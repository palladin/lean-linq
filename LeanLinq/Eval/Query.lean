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
  | ts, .grouped, s => List (KeyExpr ts) × Option (SqlExpr ts .bool) × Row ts s

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

def finishPlain (ee : EvalEnv ts) (brs : List (Branch ts .plain s)) : List (Values s) :=
  sortTagged (brs.map fun br =>
    (br.orderKeys.map fun k => (k.dir, (⟨k.type, k.expr.evalG ee [br.scope]⟩ : AnyCell)),
     br.data.evalRow ee [br.scope]))

/-- A branch destined for grouping: pre-group scope plus the (shared)
key/HAVING/projection/ORDER BY trees. Both grouping surfaces — the
comprehension's `groupYield` terminal and the pipeline's `groupedC` boundary
— reduce to this. -/
structure GBranch (ts : Ctx) (s : Schema) where
  scope : Scope
  keys : List (KeyExpr ts)
  having? : Option (SqlExpr ts .bool)
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
def groupedCore (ee : EvalEnv ts) (brs : List (GBranch ts s)) : List (Values s) :=
  let groups := brs.foldl (init := []) fun acc br =>
    insertGrouped acc (br.keys.map fun k => ⟨k.type, k.expr.evalG ee [br.scope]⟩) br
  sortTagged <| groups.filterMap fun (_, ms) =>
    match ms with
    | [] => none
    | tree :: _ =>
        let scopes := ms.map (·.scope)
        let ok := match tree.having? with
          | none => true
          | some h => h.evalG ee scopes == some true
        if ok then
          some (tree.orderKeys.map fun k => (k.dir, (⟨k.type, k.expr.evalG ee scopes⟩ : AnyCell)),
                tree.row.evalRow ee scopes)
        else none

def finishGrouped (ee : EvalEnv ts) (brs : List (Branch ts .grouped s)) : List (Values s) :=
  groupedCore ee <| brs.map fun br =>
    let (ks, hv, r) := br.data
    { scope := br.scope, keys := ks, having? := hv, orderKeys := br.orderKeys, row := r }

mutual

/-- The total evaluation core (see `Query.run` for the public entry point).
Boundary clauses are list operations over the rows of the query underneath
(SQL set semantics: UNION, INTERSECT, and EXCEPT deduplicate); spines
enumerate branches. -/
def Query.evalRows : Query ts s → EvalEnv ts → List (Values s)
  | .spine (g := .plain) sp, ee => finishPlain ee (sp.evalSpine ee 0 [])
  | .spine (g := .grouped) sp, ee => finishGrouped ee (sp.evalSpine ee 0 [])
  | .distinctC q, ee => (q.evalRows ee).eraseDups
  | .limitC q lim? off?, ee =>
      let rows := (q.evalRows ee).drop (off?.getD 0)
      match lim? with
      | some l => rows.take l
      | none => rows
  | .groupedC sp keys hv? ord? sel, ee =>
      groupedCore ee <| (sp.evalSpine ee 0 []).map fun br =>
        { scope := br.scope
          keys := keys br.data
          having? := hv?.map (· br.data)
          orderKeys := ((ord?.map (· br.data)).getD []) ++ br.orderKeys
          row := sel br.data ⟨⟩ }
  | .setOpC op a b, ee =>
      let ra := a.evalRows ee
      let rb := b.evalRows ee
      match op with
      | .union => (ra ++ rb).eraseDups
      | .intersect => (ra.filter (rb.contains ·)).eraseDups
      | .except => (ra.filter (fun r => !rb.contains r)).eraseDups

/-- Enumerate a spine's branches: sources multiply the scope (one branch per
row, rows read through the node's stored `HasTable` instance, alias
numbering deterministic along the path), guards filter (`some true` only —
SQL three-valued WHERE), ORDER BY nodes contribute keys (outermost first:
chained `orderBy` is primary-then-secondary), the terminal seals the branch. -/
def SpineQ.evalSpine : SpineQ ts g s → EvalEnv ts → Nat → Scope → List (Branch ts g s)
  | .yield r, _, _, sc => [{ scope := sc, orderKeys := [], data := r }]
  | .groupYield ks hv r, _, _, sc => [{ scope := sc, orderKeys := [], data := (ks, hv, r) }]
  | .guard b rest, ee, n, sc =>
      if b.evalG ee [sc] == some true then rest.evalSpine ee n sc else []
  | .order ks rest, ee, n, sc =>
      (rest.evalSpine ee n sc).map fun br => { br with orderKeys := ks ++ br.orderKeys }
  | .fromT (s := s₀) (inst := i) _ f, ee, n, sc =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      (i.rows ee.tables).flatMap fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
  | .joinT (s := s₀) (inst := i) kind _ on' f, ee, n, sc =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      let hits := (i.rows ee.tables).filter fun v =>
        (on' row).evalG ee [(alias, ⟨s₀, v⟩) :: sc] == some true
      let sources := match kind, hits with
        | .left, [] => [Values.nulls s₀]   -- LEFT JOIN: unmatched ⇒ NULL row
        | _, ms => ms
      sources.flatMap fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)
  | .fromQ (s := s₀) q f, ee, n, sc =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      (q.evalRows ee).flatMap fun v =>
        (f row).evalSpine ee (n + 1) ((alias, ⟨s₀, v⟩) :: sc)

end

/-- Evaluate a query over a typed in-memory database. Everything the query
references — tables *and* named parameters — was resolved against `ts` at
elaboration time, so a `TableEnv` and a `ParamEnv` for the context are all
it takes. For a parameterless context the `ps` argument defaults away. -/
def Query.run (q : Query ts s) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    List (Values s) :=
  q.evalRows ⟨env, ps, now⟩

/-- Evaluate a scalar aggregate query: the spine's branches are the group. -/
def ScalarQuery.evalCell : ScalarQuery ts t → EvalEnv ts → Option t.interp
  | .countQ sp, ee => some ((sp.evalSpine ee 0 []).length : Int)
  | .aggQ op sp, ee =>
      match sp.evalSpine ee 0 [] with
      | [] => none
      | brs@(br₀ :: _) =>
          match br₀.data with
          | .cons e .nil => SqlExpr.evalG ee (brs.map (·.scope)) (.aggE op e)

/-- Scalar counterpart of `Query.run`; the result cell is `none` for SQL
NULL (e.g. SUM over no rows). -/
def ScalarQuery.run (sc : ScalarQuery ts t) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params := by exact .nil) (now : Option String := none) :
    Option t.interp :=
  sc.evalCell ⟨env, ps, now⟩

end LeanLinq
