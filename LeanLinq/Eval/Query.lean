import LeanLinq.Core.Query
import LeanLinq.Eval.Expr

/-! # Query evaluation — the denotational semantics

`Query.run : Query s → Db → List (Values s)` computes a query's rows over an
in-memory database: the same query value that compiles to SQL executes as
Lean list pipelines. The walk mirrors the compiler's exactly — HOAS binders
are instantiated with the same `Row.ofAlias` marker rows and a deterministic
alias counter, so evaluation and compilation interpret the same instantiated
trees; where the compiler accumulates clause text, the evaluator accumulates
an alias→row environment.

A spine enumerates *branches* (one per surviving source-row combination),
each carrying its environment, the ORDER BY keys collected along the way,
and the terminal's payload — typed by the `Terminal` index, like the
compiler's `SelectK`. Grouped terminals then bucket branches by evaluated
keys; a group is simply the list of its members' environments, which is what
`SqlExpr.evalG` consumes to fold aggregates. -/

namespace LeanLinq

def Db.rows (db : Db) (t : Table s) : List (Values s) := db.rowsOf t.name s

/-- The terminal payload a branch carries, by terminal shape: plain spines
yield a projected row; grouped spines yield keys, HAVING, and the grouped
projection. -/
@[reducible] def BranchData : Terminal → Schema → Type
  | .plain, s => Row s
  | .grouped, s => List KeyExpr × Option (SqlExpr .bool) × Row s

/-- One surviving source-row combination of a spine walk. All branches of a
spine share the same instantiated syntax trees (`orderKeys`, `data`) — only
`env` varies — because binders are instantiated with alias markers, not
values. -/
structure Branch (g : Terminal) (s : Schema) where
  env : Env
  orderKeys : List OrderKey
  data : BranchData g s

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

def finishPlain (db : Db) (brs : List (Branch .plain s)) : List (Values s) :=
  sortTagged (brs.map fun br =>
    (br.orderKeys.map fun k => (k.dir, (⟨k.type, k.expr.evalG db [br.env]⟩ : AnyCell)),
     br.data.evalRow db [br.env]))

/-- A branch destined for grouping: pre-group environment plus the (shared)
key/HAVING/projection/ORDER BY trees. Both grouping surfaces — the
comprehension's `groupYield` terminal and the pipeline's `groupedC` boundary
— reduce to this. -/
structure GBranch (s : Schema) where
  env : Env
  keys : List KeyExpr
  having? : Option (SqlExpr .bool)
  orderKeys : List OrderKey
  row : Row s

private def insertGrouped (acc : List (List AnyCell × List (GBranch s)))
    (k : List AnyCell) (br : GBranch s) : List (List AnyCell × List (GBranch s)) :=
  match acc with
  | [] => [(k, [br])]
  | (k', ms) :: rest =>
      if k' == k then (k', ms ++ [br]) :: rest
      else (k', ms) :: insertGrouped rest k br

/-- GROUP BY: bucket branches by evaluated keys (first-occurrence order),
filter groups through HAVING, evaluate the grouped projection and ORDER BY
keys over each group's member environments, sort. -/
def groupedCore (db : Db) (brs : List (GBranch s)) : List (Values s) :=
  let groups := brs.foldl (init := []) fun acc br =>
    insertGrouped acc (br.keys.map fun k => ⟨k.type, k.expr.evalG db [br.env]⟩) br
  sortTagged <| groups.filterMap fun (_, ms) =>
    match ms with
    | [] => none
    | tree :: _ =>
        let envs := ms.map (·.env)
        let ok := match tree.having? with
          | none => true
          | some h => h.evalG db envs == some true
        if ok then
          some (tree.orderKeys.map fun k => (k.dir, (⟨k.type, k.expr.evalG db envs⟩ : AnyCell)),
                tree.row.evalRow db envs)
        else none

def finishGrouped (db : Db) (brs : List (Branch .grouped s)) : List (Values s) :=
  groupedCore db <| brs.map fun br =>
    let (ks, hv, r) := br.data
    { env := br.env, keys := ks, having? := hv, orderKeys := br.orderKeys, row := r }

mutual

/-- Evaluate a query over an in-memory database. Boundary clauses are list
operations over the rows of the query underneath (SQL set semantics: UNION,
INTERSECT, and EXCEPT deduplicate); spines enumerate branches. -/
def Query.run : Query s → Db → List (Values s)
  | .spine (g := .plain) sp, db => finishPlain db (sp.evalSpine db 0 [])
  | .spine (g := .grouped) sp, db => finishGrouped db (sp.evalSpine db 0 [])
  | .distinctC q, db => (q.run db).eraseDups
  | .limitC q lim? off?, db =>
      let rows := (q.run db).drop (off?.getD 0)
      match lim? with
      | some l => rows.take l
      | none => rows
  | .groupedC sp keys hv? ord? sel, db =>
      groupedCore db <| (sp.evalSpine db 0 []).map fun br =>
        { env := br.env
          keys := keys br.data
          having? := hv?.map (· br.data)
          orderKeys := ((ord?.map (· br.data)).getD []) ++ br.orderKeys
          row := sel br.data ⟨⟩ }
  | .setOpC op a b, db =>
      let ra := a.run db
      let rb := b.run db
      match op with
      | .union => (ra ++ rb).eraseDups
      | .intersect => (ra.filter (rb.contains ·)).eraseDups
      | .except => (ra.filter (fun r => !rb.contains r)).eraseDups

/-- Enumerate a spine's branches: sources multiply the environment (one
branch per row, alias numbering deterministic along the path), guards filter
(`some true` only — SQL three-valued WHERE), ORDER BY nodes contribute keys
(outermost first: chained `orderBy` is primary-then-secondary), the terminal
seals the branch. -/
def SpineQ.evalSpine : SpineQ g s → Db → Nat → Env → List (Branch g s)
  | .yield r, _, _, env => [{ env, orderKeys := [], data := r }]
  | .groupYield ks hv r, _, _, env => [{ env, orderKeys := [], data := (ks, hv, r) }]
  | .guard b rest, db, n, env =>
      if b.evalG db [env] == some true then rest.evalSpine db n env else []
  | .order ks rest, db, n, env =>
      (rest.evalSpine db n env).map fun br => { br with orderKeys := ks ++ br.orderKeys }
  | .fromT (s := s₀) t f, db, n, env =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      (db.rows t).flatMap fun v =>
        (f row).evalSpine db (n + 1) ((alias, ⟨s₀, v⟩) :: env)
  | .joinT (s := s₀) kind t on' f, db, n, env =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      let hits := (db.rows t).filter fun v =>
        (on' row).evalG db [(alias, ⟨s₀, v⟩) :: env] == some true
      let sources := match kind, hits with
        | .left, [] => [Values.nulls s₀]   -- LEFT JOIN: unmatched ⇒ NULL row
        | _, ms => ms
      sources.flatMap fun v =>
        (f row).evalSpine db (n + 1) ((alias, ⟨s₀, v⟩) :: env)
  | .fromQ (s := s₀) q f, db, n, env =>
      let alias := s!"a{n}"
      let row := Row.ofAlias alias s₀
      (q.run db).flatMap fun v =>
        (f row).evalSpine db (n + 1) ((alias, ⟨s₀, v⟩) :: env)

end

/-- Evaluate a scalar aggregate query: the spine's branches are the group. -/
def ScalarQuery.evalCell : ScalarQuery t → Db → Option t.interp
  | .countQ sp, db => some ((sp.evalSpine db 0 []).length : Int)
  | .aggQ op sp, db =>
      match sp.evalSpine db 0 [] with
      | [] => none
      | brs@(br₀ :: _) =>
          match br₀.data with
          | .cons e .nil => SqlExpr.evalG db (brs.map (·.env)) (.aggE op e)

end LeanLinq
