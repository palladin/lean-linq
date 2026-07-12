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

/-- The terminal payload a branch carries, by terminal shape: plain spines
yield a projected row; grouped spines yield keys, HAVING, and the grouped
projection. -/
@[reducible] def BranchData : Ctx → Terminal → Schema → Type
  | ts, .plain, s => Row ts s
  | ts, .grouped, s => List (KeyExpr ts) × Option (SqlExpr ts ⟨.bool, true⟩) × Row ts s

/-- One surviving source-row combination of a spine walk. All branches of a
spine share the same instantiated syntax trees (`orderKeys`, `data`) — only
`scope` varies — because binders are instantiated with alias markers, not
values. -/
structure Branch (ts : Ctx) (g : Terminal) (s : Schema) where
  scope : Scope
  orderKeys : List (OrderKey ts)
  data : BranchData ts g s

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

/-- Stable-sort rows by their evaluated keys, then strip the keys. -/
def sortTagged (tagged : List (List (Dir × AnyCell) × Values s)) : List (Values s) :=
  (tagged.mergeSort fun a b => keyLe a.1 b.1).map (·.2)

def finishPlain (ee : EvalEnv ts) (brs : List (Branch ts .plain s)) :
    Except EvalError (List (Values s)) := do
  let tagged ← brs.mapM fun br => do
    let ks ← br.orderKeys.mapM fun k => do
      pure (k.dir, (⟨k.col.ty, ← k.expr.evalG ee [br.scope]⟩ : AnyCell))
    pure (ks, ← br.data.evalRow ee [br.scope])
  pure (sortTagged tagged)

/-- A branch destined for grouping: pre-group scope plus the (shared)
key/HAVING/projection/ORDER BY trees. Both grouping surfaces — the
comprehension's `groupYield` terminal and the pipeline's `groupedC` boundary
— reduce to this. -/
structure GBranch (ts : Ctx) (s : Schema) where
  scope : Scope
  keys : List (KeyExpr ts)
  having? : Option (SqlExpr ts ⟨.bool, true⟩)
  orderKeys : List (OrderKey ts)
  row : Row ts s

private def insertGrouped (acc : List (List AnyCell × List (GBranch ts s)))
    (k : List AnyCell) (br : GBranch ts s) : List (List AnyCell × List (GBranch ts s)) :=
  match acc with
  | [] => [(k, [br])]
  | (k', ms) :: rest =>
      if k' == k then (k', ms ++ [br]) :: rest
      else (k', ms) :: insertGrouped rest k br

/-- GROUP BY: bucket branches by evaluated keys (first-occurrence order),
filter groups through HAVING, evaluate the grouped projection and ORDER BY
keys over each group's member scopes, sort. -/
def groupedCore (ee : EvalEnv ts) (brs : List (GBranch ts s)) :
    Except EvalError (List (Values s)) := do
  let keyed ← brs.mapM fun br => do
    let ks ← br.keys.mapM fun k => do
      pure (⟨k.col.ty, ← k.expr.evalG ee [br.scope]⟩ : AnyCell)
    pure (ks, br)
  let groups := keyed.foldl (init := []) fun acc (kv, br) => insertGrouped acc kv br
  let rows? ← groups.mapM fun (_, ms) => do
    match ms with
    | [] => pure none
    | tree :: _ =>
        let scopes := ms.map (·.scope)
        let ok ← match tree.having? with
          | none => pure true
          | some h => do pure ((← h.evalG ee scopes) == some true)
        if ok then
          let ks ← tree.orderKeys.mapM fun k => do
            pure (k.dir, (⟨k.col.ty, ← k.expr.evalG ee scopes⟩ : AnyCell))
          pure (some (ks, ← tree.row.evalRow ee scopes))
        else pure none
  pure (sortTagged (rows?.filterMap id))

def finishGrouped (ee : EvalEnv ts) (brs : List (Branch ts .grouped s)) :
    Except EvalError (List (Values s)) :=
  groupedCore ee <| brs.map fun br =>
    let (ks, hv, r) := br.data
    { scope := br.scope, keys := ks, having? := hv, orderKeys := br.orderKeys, row := r }

mutual

/-- The total evaluation core (see `Query.run` for the public entry point).
Boundary clauses are list operations over the rows of the query underneath
(SQL set semantics: UNION, INTERSECT, and EXCEPT deduplicate); spines
enumerate branches. `sc` is the *outer scope*: `[]` for a top-level query,
the evaluation site's scope for a correlated subquery — inner alias
numbering continues from `sc.length`, mirroring the compiler's shared
alias counter, so outer references resolve identically in both walks. -/
def Query.evalRowsIn : Query ts s → EvalEnv ts → Scope → Except EvalError (List (Values s))
  | .spine (g := .plain) sp, ee, sc => do finishPlain ee (← sp.evalSpine ee sc.length sc)
  | .spine (g := .grouped) sp, ee, sc => do finishGrouped ee (← sp.evalSpine ee sc.length sc)
  | .distinctC q, ee, sc => do
      pure (List.dedupBy Values.beq (← q.evalRowsIn ee sc))
  | .limitC q lim? off?, ee, sc => do
      let rows := (← q.evalRowsIn ee sc).drop (off?.getD 0)
      pure (match lim? with
        | some l => rows.take l
        | none => rows)
  | .groupedC sp keys hv? ord? sel, ee, sc => do
      groupedCore ee <| (← sp.evalSpine ee sc.length sc).map fun br =>
        { scope := br.scope
          keys := keys br.data
          having? := hv?.map (· br.data)
          orderKeys := ((ord?.map (· br.data)).getD []) ++ br.orderKeys
          row := sel br.data ⟨⟩ }
  | .setOpC op a b, ee, sc => do
      let ra ← a.evalRowsIn ee sc
      let rb ← b.evalRowsIn ee sc
      pure (match op with
        | .union => List.dedupBy Values.beq (ra ++ rb)
        | .intersect =>
            List.dedupBy Values.beq (ra.filter (fun r => rb.any (Values.beq r)))
        | .except =>
            List.dedupBy Values.beq (ra.filter (fun r => !rb.any (Values.beq r))))

/-- Enumerate a spine's branches: sources multiply the scope (one branch per
row, rows read through the node's stored `HasTable` instance, alias
numbering deterministic along the path), guards filter (`some true` only —
SQL three-valued WHERE), ORDER BY nodes contribute keys (outermost first:
chained `orderBy` is primary-then-secondary), the terminal seals the branch. -/
def SpineQ.evalSpine : SpineQ ts g s → EvalEnv ts → Nat → Scope →
    Except EvalError (List (Branch ts g s))
  | .yield r, _, _, sc => pure [{ scope := sc, orderKeys := [], data := r }]
  | .groupYield ks hv r, _, _, sc => pure [{ scope := sc, orderKeys := [], data := (ks, hv, r) }]
  | .guard b rest, ee, n, sc => do
      if (← b.evalG ee [sc]) == some true then rest.evalSpine ee n sc else pure []
  | .order ks rest, ee, n, sc => do
      pure ((← rest.evalSpine ee n sc).map fun br => { br with orderKeys := ks ++ br.orderKeys })
  | .fromT (s := s₀) (inst := i) _ f, ee, n, sc => do
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      let branches ← (i.rows ee.tables).mapM fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
      pure branches.flatten
  | .joinT (s := s₀) (inst := i) _ on' f, ee, n, sc => do
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      let hits ← (i.rows ee.tables).filterM fun v => do
        pure ((← (on' row).evalG ee [(alias, ⟨s₀, v⟩) :: sc]) == some true)
      let branches ← hits.mapM fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
      pure branches.flatten
  -- LEFT JOIN: the bound row is marked over the NULL-lifted schema; field
  -- lookups go by name+type, so matched (strict) rows and the all-NULL pad
  -- coexist behind the same markers
  | .joinLeftT (s := s₀) (inst := i) _ on' f, ee, n, sc => do
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀.asNull
      let hits ← (i.rows ee.tables).filterM fun v => do
        pure ((← (on' row).evalG ee [(alias, ⟨s₀, v⟩) :: sc]) == some true)
      if hits.isEmpty then
        let branches ← (f row).evalSpine ee (n + 1)
          ((alias, ⟨s₀.asNull, Values.nulls s₀⟩) :: sc)
        pure branches
      else
        let branches ← hits.mapM fun v =>
          (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
        pure branches.flatten
  | .fromQ (s := s₀) q f, ee, n, sc => do
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      let branches ← (← q.evalRowsIn ee sc).mapM fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
      pure branches.flatten

end

/-- Top-level rows: no outer scope. -/
def Query.evalRows (q : Query ts s) (ee : EvalEnv ts) :
    Except EvalError (List (Values s)) :=
  q.evalRowsIn ee []

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

/-- Evaluate a scalar aggregate query: the spine's branches are the group.
`sc` is the outer scope (see `Query.evalRowsIn`). -/
def ScalarQuery.evalCellIn (sq : ScalarQuery ts ⟨t, n⟩) (ee : EvalEnv ts)
    (sc : Scope) : Except EvalError (Nullable t) :=
  match sq with
  | .countQ sp => do pure (some (((← sp.evalSpine ee sc.length sc)).length : Int))
  | .aggQ op sp => do
      match (← sp.evalSpine ee sc.length sc) with
      | [] => pure none
      | brs@(br₀ :: _) =>
          match br₀.data with
          | .cons e .nil => SqlExpr.evalG ee (brs.map (·.scope)) (.aggE op e)

def ScalarQuery.evalCell (sq : ScalarQuery ts ⟨t, n⟩) (ee : EvalEnv ts) :
    Except EvalError (Nullable t) :=
  sq.evalCellIn ee []

/-- Scalar counterpart of `Query.run`; the result cell is `none` for SQL
NULL (e.g. SUM over no rows). -/
def ScalarQuery.run (sc : ScalarQuery ts ⟨t, n⟩) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    Except EvalError (Nullable t) :=
  sc.evalCell ⟨env, ps, now⟩

/-! ## Length and invariant lemmas — the soundness theorems' toolkit -/

/-- Invert a successful `Except` bind. -/
theorem Except.bind_ok {ε α β : Type _} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

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

theorem sortTagged_length {s : Schema}
    (t : List (List (Dir × AnyCell) × Values s)) :
    (sortTagged t).length = t.length := by
  simp [sortTagged, List.length_mergeSort]

theorem finishPlain_length {ts : Ctx} {s : Schema} {ee : EvalEnv ts}
    {brs : List (Branch ts .plain s)} {rows : List (Values s)}
    (h : finishPlain ee brs = .ok rows) : rows.length = brs.length := by
  unfold finishPlain at h
  obtain ⟨tagged, ht, h⟩ := Except.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [sortTagged_length, List.length_mapM_except _ ht]

theorem insertGrouped_length_le {ts : Ctx} {s : Schema}
    (acc : List (List AnyCell × List (GBranch ts s))) (k : List AnyCell)
    (br : GBranch ts s) :
    (insertGrouped acc k br).length ≤ acc.length + 1 := by
  induction acc with
  | nil => simp [insertGrouped]
  | cons hd rest ih =>
      rw [insertGrouped]
      split
      · simp
      · simpa using Nat.succ_le_succ ih

theorem foldl_insertGrouped_length_le {ts : Ctx} {s : Schema}
    (l : List (List AnyCell × GBranch ts s))
    (acc : List (List AnyCell × List (GBranch ts s))) :
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

theorem groupedCore_length_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts}
    {brs : List (GBranch ts s)} {rows : List (Values s)}
    (h : groupedCore ee brs = .ok rows) : rows.length ≤ brs.length := by
  unfold groupedCore at h
  obtain ⟨keyed, hk, h⟩ := Except.bind_ok h
  obtain ⟨rows?, hr, h⟩ := Except.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  calc (sortTagged (rows?.filterMap id)).length
      = (rows?.filterMap id).length := sortTagged_length _
    _ ≤ rows?.length := List.length_filterMap_le _ _
    _ = _ := List.length_mapM_except _ hr
    _ ≤ 0 + keyed.length := foldl_insertGrouped_length_le _ _
    _ = keyed.length := Nat.zero_add _
    _ = brs.length := List.length_mapM_except _ hk

theorem finishGrouped_length_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts}
    {brs : List (Branch ts .grouped s)} {rows : List (Values s)}
    (h : finishGrouped ee brs = .ok rows) : rows.length ≤ brs.length := by
  unfold finishGrouped at h
  simpa using groupedCore_length_le h

end LeanLinq
