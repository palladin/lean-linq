import LeanLinq.Core.Query
import LeanLinq.Eval.Expr

/-! # Query evaluation — the denotational semantics

`Query.run : Query ts s → TableEnv ts → List (Values s)` computes a query's
rows over a typed in-memory database: the same query value that compiles to
SQL executes as Lean list pipelines. Table resolution happened at
*elaboration* — `fromT`/`joinT` nodes carry their `HasTable` instances, and
evaluation reads rows through them — so there is no name lookup, no schema
check, and no failure mode at run time.

The walk mirrors the compiler's exactly — HOAS binders are instantiated with
the same `Row.ofAlias` marker rows and a deterministic alias counter, so
evaluation and compilation interpret the same instantiated trees; where the
compiler accumulates clause text, the evaluator accumulates an alias→row
scope.

A spine enumerates *branches* (one per surviving source-row combination),
each carrying its scope, the ORDER BY keys collected along the way, and the
terminal's payload — typed by the `Terminal` index, like the compiler's
`SelectK`. Grouped terminals then bucket branches by evaluated keys; a group
is simply the list of its members' scopes, which is what `SqlExpr.evalG`
consumes to fold aggregates. -/

namespace LeanLinq

/-- Lexicographic `≤` on evaluated ORDER BY keys (`desc` flips, NULL sorts
smallest, ties fall through — `mergeSort` is stable, so source order is the
final tiebreak). -/
def keyLe : List (Dir × AnyCell) → List (Dir × AnyCell) → Bool
  | [], _ => true
  | _, [] => true
  | (d, a) :: as', (_, b) :: bs =>
      match (if d == .desc then b.cmp a else a.cmp b) with
      | .lt => true
      | .gt => false
      | .eq => keyLe as' bs

/-- Stable-sort by evaluated keys, then strip the keys. -/
def sortTagged (tagged : List (List (Dir × AnyCell) × α)) : List α :=
  (tagged.mergeSort fun a b => keyLe a.1 b.1).map (·.2)

/-- First-occurrence-order bucketing of scopes by their evaluated GROUP BY
keys (NULLs compare equal — `AnyCell.cmp`-based `==`). -/
def insertGrouped (acc : List (List AnyCell × List Scope))
    (k : List AnyCell) (sc : Scope) : List (List AnyCell × List Scope) :=
  match acc with
  | [] => [(k, [sc])]
  | (k', ms) :: rest =>
      if k' == k then (k', ms ++ [sc]) :: rest
      else (k', ms) :: insertGrouped rest k sc

mutual

/-- Evaluate an expression over the scopes of the current group
(singleton = ungrouped row context). Structural subqueries evaluate by
recursion — a correlated subquery receives the evaluation site's scope,
inner alias numbering continuing from its length (the alias counter always
equals the scope length along any evaluation path). -/
def SqlExprP.evalG {c : SqlType} (ee : EvalEnv ts) : List Scope → SqlExpr ts c →
    Except EvalError (Nullable c.ty)
  | _, .intC i => pure (some i)
  | _, .longC i => pure (some i)
  | _, .doubleC f => pure (some f)
  | _, .decimalC d => pure (some (parseDecimal d))
  | _, .stringC s => pure (some s)
  | _, .boolC b => pure (some b)
  | _, .dateTimeC s => pure (some (normDateTime s))
  | _, .guidC g => pure (some g.toLower)
  | _, .nullC _ => pure none
  | _, .paramE (inst := i) _ => pure (SqlType.toNullable (i.get ee.params))
  | scs, .widen (t := t₀) e => SqlExprP.evalG (c := ⟨t₀, false⟩) ee scs e
  | scs, .field ⟨t', _⟩ row name =>
      match scs.head? with
      | none => .error (.internal s!"no row in scope for {row.alias}.{name}")
      | some sc =>
          match sc.get? row.alias name t' with
          | some cell => pure cell
          | none => .error (.internal s!"unresolved field {row.alias}.{name}")
  | scs, .arith (c := c₀) op a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) (c₀.ty.arithV op)
  | scs, .concat a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y => pure (some (x ++ y))
  | scs, .cmp (t := t₀) op a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y =>
        pure (some (op.holds (t₀.cmpV x y)))
  | scs, .and a b => do
      pure (match (← a.evalG ee scs), (← b.evalG ee scs) with
        | some false, _ => some false
        | _, some false => some false
        | some true, some true => some true
        | _, _ => none)
  | scs, .or a b => do
      pure (match (← a.evalG ee scs), (← b.evalG ee scs) with
        | some true, _ => some true
        | _, some true => some true
        | some false, some false => some false
        | _, _ => none)
  | scs, .not a => do pure ((← a.evalG ee scs).map (!·))
  | scs, .isNull e => do pure (some (← e.evalG ee scs).isNone)
  | scs, .isNotNull e => do pure (some (← e.evalG ee scs).isSome)
  | scs, .like e p => do
      strict2 (← e.evalG ee scs) (← p.evalG ee scs) fun s pat =>
        pure (some (likeMatch s pat))
  | scs, .inList (c := ⟨t₀, _⟩) e es => do
      -- `x IN ()` is FALSE without evaluating x (mirrors the compiled `(1 = 0)`)
      match es with
      | [] => pure (some false)
      | es =>
          match (← e.evalG ee scs) with
          | none => pure none
          | some v =>
              let hits := (← SqlExprP.evalGList ee scs es).map fun ⟨u, cell⟩ =>
                if h : u = t₀ then
                  (h ▸ cell).map (fun w => t₀.cmpV v w == Ordering.eq)
                else some false
              pure (if hits.any (· == some true) then some true
                    else if hits.any (·.isNone) then none
                    else some false)
  -- the subquery evaluates in the *current* scope, so correlated outer
  -- references resolve; in aggregate positions (several member scopes)
  -- the group's first member stands for the group, the same convention
  -- bare column reads use
  | scs, .inSub (t := t₀) e sq => do
      match (← e.evalG ee scs) with
      | none => pure none
      | some v =>
          let rows ← sq.evalRowsIn ee (scs.head?.getD [])
          let hits := (rows.map fun | .cons cell .nil => SqlType.toNullable cell).map
            (·.map (fun w => t₀.cmpV v w == Ordering.eq))
          pure (if hits.any (· == some true) then some true
                else if hits.any (·.isNone) then none
                else some false)
  | scs, .scalarSub sq => sq.evalCellIn ee (scs.head?.getD [])
  -- EXISTS: rows or not — never NULL, evaluated in the current scope
  -- (correlation is the construct's whole point)
  | scs, .existsSub sub => do
      pure (some !(← sub.evalRowsIn ee (scs.head?.getD [])).isEmpty)
  -- CASE is lazy in its branches (SQL semantics): only the taken branch
  -- evaluates, so a guarded division cannot error
  | scs, .caseWhen c a b => do
      if (← c.evalG ee scs) == some true then a.evalG ee scs else b.evalG ee scs
  | scs, .aggE (t := t₁) op e => do
      t₁.aggV op ((← scs.mapM fun sc => e.evalG ee [sc]).filterMap id)
  | scs, .countAll => pure (some (scs.length : Int))
  | scs, .abs (c := c₀) e => do strict1 (← e.evalG ee scs) c₀.ty.absV
  | scs, .round (c := c₀) e digits => do strict1 (← e.evalG ee scs) (c₀.ty.roundV digits)
  | scs, .ceiling (c := c₀) e => do strict1 (← e.evalG ee scs) c₀.ty.ceilV
  | scs, .floor (c := c₀) e => do strict1 (← e.evalG ee scs) c₀.ty.floorV
  | scs, .substring e start len => do
      pure ((← e.evalG ee scs).map (sqlSubstring · start len))
  | scs, .upper e => do pure ((← e.evalG ee scs).map (·.toUpper))
  | scs, .lower e => do pure ((← e.evalG ee scs).map (·.toLower))
  | scs, .trim e => do pure ((← e.evalG ee scs).map (·.trimAscii.toString))
  | scs, .length e => do pure ((← e.evalG ee scs).map (fun s => (s.length : Int)))
  | _, .now =>
      match ee.now with
      | some s => pure (some s)
      | none => .error .noClock
  | scs, .datePart u e => do
      pure ((← e.evalG ee scs).map fun s =>
        match u with
        | .year => (parseYMD s).1
        | .month => (parseYMD s).2.1
        | .day => (parseYMD s).2.2)
  | scs, .dateAdd u e n => do
      pure ((← e.evalG ee scs).map fun s =>
        match u with
        | .day => dateAddDays s n
        | .month => dateAddMonths s n
        | .year => dateAddYears s n)
  | scs, .dateDiff u a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y =>
        pure (some (match u with
          | .day => dateDiffDays x y
          | .month => dateDiffMonths x y
          | .year => dateDiffYears x y))

def SqlExprP.evalGList (ee : EvalEnv ts) (scs : List Scope) :
    List ((p : SqlType) × SqlExpr ts p) →
    Except EvalError (List ((u : SqlPrim) × Nullable u))
  | [] => pure []
  | ⟨p, e⟩ :: es => do
      pure (⟨p.ty, ← e.evalG ee scs⟩ :: (← SqlExprP.evalGList ee scs es))

/-- Evaluate every cell of a projected row — the construction boundary
where `Nullable` computation results become honest cells: a NOT NULL
column receiving `none` is a loud internal error, never a silent NULL. -/
def RowP.evalRow (ee : EvalEnv ts) (scs : List Scope) :
    {s : Schema} → Row ts s → Except EvalError (Values s)
  | _, .nil => pure .nil
  | _, .cons (name := nm) e r => do
      pure (.cons (← SqlType.ofNullable nm _ (← e.evalG ee scs)) (← r.evalRow ee scs))

/-- GROUP BY keys over one scope, as comparable cells. -/
def evalKeyCells (ee : EvalEnv ts) (sc : Scope) :
    List (KeyExpr ts) → Except EvalError (List AnyCell)
  | [] => pure []
  | ⟨c, e⟩ :: ks => do
      pure ((⟨c.ty, ← e.evalG ee [sc]⟩ : AnyCell) :: (← evalKeyCells ee sc ks))

/-- ORDER BY keys over a member-scope list (grouped keys may aggregate). -/
def evalOrderCells (ee : EvalEnv ts) (scs : List Scope) :
    List (OrderKey ts) → Except EvalError (List (Dir × AnyCell))
  | [] => pure []
  | ⟨c, e, d⟩ :: ks => do
      pure ((d, (⟨c.ty, ← e.evalG ee scs⟩ : AnyCell)) :: (← evalOrderCells ee scs ks))

/-- The spine walk, scopes flowing **down**: sources extend every incoming
scope (one recursion below, over the marker-instantiated subtree), guards
filter, ORDER BY nodes sort what returns from below (stable, so stacked
nodes compose outermost-primary), and the terminal evaluates where its
trees are structural — the whole evaluation is one structural descent.
`n` is the alias counter, equal to every incoming scope's length. -/
def SpineQP.evalScopes : SpineQ ts g s → EvalEnv ts → Nat → List Scope →
    Except EvalError (List (List Scope × Values s))
  | .yield r, ee, _, scopes =>
      scopes.mapM fun sc => do pure ([sc], ← r.evalRow ee [sc])
  | .groupYield ks hv ord r, ee, _, scopes => do
      let keyed ← scopes.mapM fun sc => do pure (← evalKeyCells ee sc ks, sc)
      let groups := keyed.foldl (init := []) fun acc (kv, sc) => insertGrouped acc kv sc
      let tagged? ← groups.mapM fun (_, ms) => do
        let ok ← match hv with
          | none => pure true
          | some h => do pure ((← h.evalG ee ms) == some true)
        if ok then
          let oks ← evalOrderCells ee ms ord
          pure (some (oks, (ms, ← r.evalRow ee ms)))
        else pure none
      pure (sortTagged (tagged?.filterMap id))
  | .guard b rest, ee, n, scopes => do
      let survivors ← scopes.mapM fun sc => do
        pure (if (← b.evalG ee [sc]) == some true then some sc else none)
      rest.evalScopes ee n (survivors.filterMap id)
  | .order ks rest, ee, n, scopes => do
      let rs ← rest.evalScopes ee n scopes
      let tagged ← rs.mapM fun r => do pure (← evalOrderCells ee r.1 ks, r)
      pure (sortTagged tagged)
  | .fromT (s := s₀) (inst := i) _ f, ee, n, scopes => do
      let alias := s!"a{n}"
      let exts := scopes.flatMap fun sc =>
        (i.rows ee.tables).map fun v => (alias, ⟨s₀, v⟩) :: sc
      (f ⟨alias⟩).evalScopes ee (n + 1) exts
  | .joinT (s := s₀) (inst := i) _ on' f, ee, n, scopes => do
      let alias := s!"a{n}"
      let exts := scopes.flatMap fun sc =>
        (i.rows ee.tables).map fun v => (alias, ⟨s₀, v⟩) :: sc
      let hits ← exts.filterM fun ext => do
        pure ((← (on' ⟨alias⟩).evalG ee [ext]) == some true)
      (f ⟨alias⟩).evalScopes ee (n + 1) hits
  -- LEFT JOIN: matched rows are marked over the NULL-lifted schema; field
  -- lookups go by name+type, so matched (strict) rows and the all-NULL pad
  -- coexist behind the same markers; the pad decision is per outer scope
  | .joinLeftT (s := s₀) (inst := i) _ on' f, ee, n, scopes => do
      let alias := s!"a{n}"
      let exts ← scopes.mapM fun sc => do
        let hits ← (i.rows ee.tables).filterM fun v => do
          pure ((← (on' ⟨alias⟩).evalG ee [(alias, ⟨s₀, v⟩) :: sc]) == some true)
        if hits.isEmpty then
          pure [(alias, ⟨s₀.asNull, Values.nulls s₀⟩) :: sc]
        else
          pure (hits.map fun v => (alias, ⟨s₀, v⟩) :: sc)
      (f ⟨alias⟩).evalScopes ee (n + 1) exts.flatten
  | .fromQ (s := s₀) q f, ee, n, scopes => do
      let exts ← scopes.mapM fun sc => do
        let rows ← q.evalRowsIn ee sc
        pure (rows.map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc)
      (f ⟨s!"a{n}"⟩).evalScopes ee (n + 1) exts.flatten

/-- Scope enumeration only — `COUNT(*)`'s walk: guards filter and sources
multiply, but no projection, sort key, or GROUP BY ever evaluates (SQL:
`COUNT(*)` counts rows; it does not evaluate the select list). -/
def SpineQP.enumScopes : {g₀ : Terminal} → SpineQ ts g₀ s → EvalEnv ts → Nat →
    List Scope → g₀ = .plain → Except EvalError (List Scope)
  | _, .yield _, _, _, scopes, _ => pure scopes
  | _, .groupYield .., _, _, _, h => nomatch h
  | _, .guard b rest, ee, n, scopes, h => do
      let survivors ← scopes.mapM fun sc => do
        pure (if (← b.evalG ee [sc]) == some true then some sc else none)
      rest.enumScopes ee n (survivors.filterMap id) h
  | _, .order _ rest, ee, n, scopes, h => rest.enumScopes ee n scopes h
  | _, .fromT (s := s₀) (inst := i) _ f, ee, n, scopes, h => do
      let alias := s!"a{n}"
      let exts := scopes.flatMap fun sc =>
        (i.rows ee.tables).map fun v => (alias, ⟨s₀, v⟩) :: sc
      (f ⟨alias⟩).enumScopes ee (n + 1) exts h
  | _, .joinT (s := s₀) (inst := i) _ on' f, ee, n, scopes, h => do
      let alias := s!"a{n}"
      let exts := scopes.flatMap fun sc =>
        (i.rows ee.tables).map fun v => (alias, ⟨s₀, v⟩) :: sc
      let hits ← exts.filterM fun ext => do
        pure ((← (on' ⟨alias⟩).evalG ee [ext]) == some true)
      (f ⟨alias⟩).enumScopes ee (n + 1) hits h
  | _, .joinLeftT (s := s₀) (inst := i) _ on' f, ee, n, scopes, h => do
      let alias := s!"a{n}"
      let exts ← scopes.mapM fun sc => do
        let hits ← (i.rows ee.tables).filterM fun v => do
          pure ((← (on' ⟨alias⟩).evalG ee [(alias, ⟨s₀, v⟩) :: sc]) == some true)
        if hits.isEmpty then
          pure [(alias, ⟨s₀.asNull, Values.nulls s₀⟩) :: sc]
        else
          pure (hits.map fun v => (alias, ⟨s₀, v⟩) :: sc)
      (f ⟨alias⟩).enumScopes ee (n + 1) exts.flatten h
  | _, .fromQ (s := s₀) q f, ee, n, scopes, h => do
      let exts ← scopes.mapM fun sc => do
        let rows ← q.evalRowsIn ee sc
        pure (rows.map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc)
      (f ⟨s!"a{n}"⟩).enumScopes ee (n + 1) exts.flatten h

/-- The total evaluation core (see `Query.run` for the public entry point).
Boundary clauses are list operations over the rows of the query underneath
(SQL set semantics: UNION, INTERSECT, and EXCEPT deduplicate); spines
evaluate by the downward scope walk. `sc` is the *outer scope*: `[]` for a
top-level query, the evaluation site's scope for a correlated subquery —
inner alias numbering continues from `sc.length`, mirroring the compiler's
shared alias counter, so outer references resolve identically in both
walks. -/
def QueryP.evalRowsIn : QueryA ts s → EvalEnv ts → Scope → Except EvalError (List (Values s))
  | .spine sp, ee, sc => do
      pure ((← sp.evalScopes ee sc.length [sc]).map (·.2))
  | .distinctC q, ee, sc => do
      pure (List.dedupBy Values.beq (← q.evalRowsIn ee sc))
  | .limitC q lim? off?, ee, sc => do
      let rows := (← q.evalRowsIn ee sc).drop (off?.getD 0)
      pure (match lim? with
        | some l => rows.take l
        | none => rows)
  | .setOpC op a b, ee, sc => do
      let ra ← a.evalRowsIn ee sc
      let rb ← b.evalRowsIn ee sc
      pure (match op with
        | .union => List.dedupBy Values.beq (ra ++ rb)
        | .intersect =>
            List.dedupBy Values.beq (ra.filter (fun r => rb.any (Values.beq r)))
        | .except =>
            List.dedupBy Values.beq (ra.filter (fun r => !rb.any (Values.beq r))))

/-- Evaluate a scalar aggregate query. `sc` is the outer scope (see
`Query.evalRowsIn`). -/
def ScalarQueryP.evalCellIn : {c : SqlType} → ScalarA ts c → EvalEnv ts → Scope →
    Except EvalError (Nullable c.ty)
  | _, .countQ sp, ee, sc => do
      pure (some (((← sp.enumScopes ee sc.length [sc] rfl)).length : Int))
  | _, .aggQ (t := t₀) op sp, ee, sc => do
      let rs ← sp.evalScopes ee sc.length [sc]
      let vals := rs.map fun r => match r.2 with
        | .cons cell .nil => SqlType.toNullable cell
      t₀.aggV op (vals.filterMap id)

end

/-- Top-level rows: no outer scope. -/
def Query.evalRows (q : Query ts s) (ee : EvalEnv ts) :
    Except EvalError (List (Values s)) :=
  (q AliasOf).evalRowsIn ee []

/-- Evaluate a query over a typed in-memory database. Everything the query
references — tables *and* named parameters — was resolved against `ts` at
elaboration time, so a `TableEnv` and a `ParamEnv` for the context are all
it takes (for a parameterless context the `ps` argument defaults away).
NULL is data (`Nullable`); exceptional conditions — division by zero,
`now` without a clock — are the explicit `Except` channel, exactly the
statement-aborting behavior of PostgreSQL/SQL Server. -/
def Query.run (q : Query ts s) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    Except EvalError (List (Values s)) :=
  q.evalRows ⟨env, ps, now⟩

/-- Scalar counterpart of `Query.evalRows`. -/
def ScalarQuery.evalCell (sq : ScalarQuery ts ⟨t, n⟩) (ee : EvalEnv ts) :
    Except EvalError (Nullable t) :=
  (sq AliasOf).evalCellIn ee []

/-- Scalar counterpart of `Query.run`; the result cell is `none` for SQL
NULL (e.g. SUM over no rows). -/
def ScalarQuery.run (sq : ScalarQuery ts ⟨t, n⟩) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    Except EvalError (Nullable t) :=
  sq.evalCell ⟨env, ps, now⟩

namespace ScalarB
export ScalarQuery (evalCell run)
end ScalarB

namespace SqlExpr
export SqlExprP (evalG evalGList)
end SqlExpr

namespace Row
export RowP (evalRow)
end Row

/-! ## Length and invariant lemmas — the soundness theorems' toolkit -/

/-- Invert a successful `Except` bind. -/
theorem Except.bind_ok {ε α β : Type _} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

/-- A flatten of uniformly bounded parts is bounded by count × bound. -/
theorem List.length_flatten_le {K : Nat} :
    (parts : List (List α)) → (h : ∀ l ∈ parts, l.length ≤ K) →
    parts.flatten.length ≤ parts.length * K
  | [], _ => by simp
  | l :: t, h => by
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        Nat.succ_mul]
      have ht := List.length_flatten_le t (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hl := h l (List.mem_cons_self ..)
      omega

/-- Every element of a successful `Except`-mapM's output is the image of
a member of the input. -/
theorem List.mem_of_mapM_except {ε α β : Type _} {f : α → Except ε β} :
    (l : List α) → {ys : List β} → l.mapM f = .ok ys →
    ∀ y ∈ ys, ∃ x ∈ l, f x = .ok y
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; intro y hy; cases hy
  | a :: l, ys, h => by
      rw [List.mapM_cons] at h
      obtain ⟨b, hfa, h⟩ := Except.bind_ok h
      obtain ⟨bs, hml, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨a, List.mem_cons_self .., hfa⟩
      · obtain ⟨x, hx, hfx⟩ := List.mem_of_mapM_except l hml y hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem List.length_mapM_except {ε α β : Type _} {f : α → Except ε β} :
    (l : List α) → {ys : List β} → l.mapM f = .ok ys → ys.length = l.length
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
  | a :: l, ys, h => by
      rw [List.mapM_cons] at h
      obtain ⟨b, hfa, h⟩ := Except.bind_ok h
      obtain ⟨bs, hml, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [List.length_mapM_except l hml]

theorem sortTagged_length (t : List (List (Dir × AnyCell) × α)) :
    (sortTagged t).length = t.length := by
  simp [sortTagged, List.length_mergeSort]

theorem insertGrouped_length_le (acc : List (List AnyCell × List Scope))
    (k : List AnyCell) (sc : Scope) :
    (insertGrouped acc k sc).length ≤ acc.length + 1 := by
  induction acc with
  | nil => simp [insertGrouped]
  | cons hd rest ih =>
      rw [insertGrouped]
      split
      · simp
      · simpa using Nat.succ_le_succ ih

theorem foldl_insertGrouped_length_le (l : List (List AnyCell × Scope))
    (acc : List (List AnyCell × List Scope)) :
    (l.foldl (init := acc) fun a kb => insertGrouped a kb.1 kb.2).length
      ≤ acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons hd t ih =>
      rw [List.foldl_cons]
      calc ((t.foldl (fun a kb => insertGrouped a kb.1 kb.2)
              (insertGrouped acc hd.1 hd.2))).length
          ≤ (insertGrouped acc hd.1 hd.2).length + t.length := ih _
        _ ≤ (acc.length + 1) + t.length :=
            Nat.add_le_add_right (insertGrouped_length_le ..) _
        _ = acc.length + (hd :: t).length := by
            simp [Nat.add_assoc, Nat.add_comm 1]

namespace Query
export QueryP (evalRowsIn)
end Query

namespace QueryB
export Query (evalRows run)
end QueryB

namespace SpineQ
export SpineQP (evalScopes enumScopes)
end SpineQ

end LeanLinq
