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
  | ts, .grouped, s => List (KeyExpr ts) × Option (SqlExpr ts .bool true) × Row ts s

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
      pure (k.dir, (⟨k.type, ← k.expr.evalG ee [br.scope]⟩ : AnyCell))
    pure (ks, ← br.data.evalRow ee [br.scope])
  pure (sortTagged tagged)

/-- A branch destined for grouping: pre-group scope plus the (shared)
key/HAVING/projection/ORDER BY trees. Both grouping surfaces — the
comprehension's `groupYield` terminal and the pipeline's `groupedC` boundary
— reduce to this. -/
structure GBranch (ts : Ctx) (s : Schema) where
  scope : Scope
  keys : List (KeyExpr ts)
  having? : Option (SqlExpr ts .bool true)
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
      pure (⟨k.type, ← k.expr.evalG ee [br.scope]⟩ : AnyCell)
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
            pure (k.dir, (⟨k.type, ← k.expr.evalG ee scopes⟩ : AnyCell))
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
enumerate branches. -/
def Query.evalRows : Query ts s → EvalEnv ts → Except EvalError (List (Values s))
  | .spine (g := .plain) sp, ee => do finishPlain ee (← sp.evalSpine ee 0 [])
  | .spine (g := .grouped) sp, ee => do finishGrouped ee (← sp.evalSpine ee 0 [])
  | .distinctC q, ee => do pure (← q.evalRows ee).eraseDups
  | .limitC q lim? off?, ee => do
      let rows := (← q.evalRows ee).drop (off?.getD 0)
      pure (match lim? with
        | some l => rows.take l
        | none => rows)
  | .groupedC sp keys hv? ord? sel, ee => do
      groupedCore ee <| (← sp.evalSpine ee 0 []).map fun br =>
        { scope := br.scope
          keys := keys br.data
          having? := hv?.map (· br.data)
          orderKeys := ((ord?.map (· br.data)).getD []) ++ br.orderKeys
          row := sel br.data ⟨⟩ }
  | .setOpC op a b, ee => do
      let ra ← a.evalRows ee
      let rb ← b.evalRows ee
      pure (match op with
        | .union => (ra ++ rb).eraseDups
        | .intersect => (ra.filter (rb.contains ·)).eraseDups
        | .except => (ra.filter (fun r => !rb.contains r)).eraseDups)

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
      let branches ← (← q.evalRows ee).mapM fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
      pure branches.flatten

end

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

/-- Evaluate a scalar aggregate query: the spine's branches are the group. -/
def ScalarQuery.evalCell : ScalarQuery ts t n → EvalEnv ts → Except EvalError (Nullable t)
  | .countQ sp, ee => do pure (some (((← sp.evalSpine ee 0 [])).length : Int))
  | .aggQ op sp, ee => do
      match (← sp.evalSpine ee 0 []) with
      | [] => pure none
      | brs@(br₀ :: _) =>
          match br₀.data with
          | .cons e .nil => SqlExpr.evalG ee (brs.map (·.scope)) (.aggE op e)

/-- Scalar counterpart of `Query.run`; the result cell is `none` for SQL
NULL (e.g. SUM over no rows). -/
def ScalarQuery.run (sc : ScalarQuery ts t n) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    Except EvalError (Nullable t) :=
  sc.evalCell ⟨env, ps, now⟩

end LeanLinq
