import LeanLinq.Core.Query

/-! # C#-style LINQ comprehension syntax

```
query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 18
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Id"].as "CustomerId", (a.sum o["Amount"]).as "TotalSpent"]
  distinct
  limit 5 offset 10
}
```

Clauses desugar right-to-left into a `SpineQ`-valued fold — each clause's
terminal shape (`Terminal.plain` vs `.grouped`) is known statically at
expansion, so grouping discipline is enforced by the index, not at run time:
- `from x in src` ⇒ `QuerySource.bind src (fun x => …)` (tables, or queries —
  plain-spine queries inline, others become derived tables);
- `join x in t on p` / `leftJoin x in t on p` ⇒ `SpineQ.joinT` (fuse into the
  same flat statement);
- `where p` ⇒ `SpineQ.guard p …` (a WHERE conjunct);
- `orderBy k, …` ⇒ `SpineQ.order` (spine ORDER BY — may reference aggregates
  when grouped);
- `groupBy k, … into a` + optional `having p` turn the final `select r` into
  the grouped terminal (`SpineQ.groupYield`); `into a` *binds* the aggregate
  token (C#'s `group … into g`), so `a.count`/`a.sum e`/… are in scope only
  in the clauses after the grouping;
- plain `select r` ⇒ `SpineQ.yield r`;
- the fold wraps into `Query.spine`, and trailing `distinct` /
  `limit n [offset m]` / `offset n` decorate the finished query.

Clauses are newline- (or `;`-) separated, do-notation style. Join sources and
limit/offset amounts parse at `term:max` (parenthesize anything compound).

Token choices, learned the hard way:
- the head must be a *reserved* token — non-reserved (`&"…"`) leading keywords
  are not dispatched for term parsers, so the whole block would parse as an
  application of an identifier to a structure instance;
- `query!` (like `panic!`/`assert!`) reserves nothing usable: `query` remains
  a perfectly good identifier, since `!` cannot appear in identifiers;
- clause keywords (`select`, `join`, `orderBy`, …) stay non-reserved —
  reserving them would break those names as identifiers everywhere — which is
  fine mid-category thanks to `behavior := both`, just not in term-head
  position. Rules led by non-reserved keywords cannot be matched by quotation
  patterns, so the expander dispatches on syntax kinds. -/

-- `behavior := both` makes the category dispatch rules led by a non-reserved
-- identifier keyword (`select`, `join`, …); the default behavior only
-- dispatches on reserved tokens.
declare_syntax_cat sqlClause (behavior := both)

namespace LeanLinq

syntax (name := sqlFrom) "from " ident " in " term : sqlClause
syntax (name := sqlJoin) &"join " ident " in " term:max &"on " term : sqlClause
syntax (name := sqlLeftJoin) &"leftJoin " ident " in " term:max &"on " term : sqlClause
syntax (name := sqlWhere) "where " term : sqlClause
syntax (name := sqlOrderBy) &"orderBy " term,+ : sqlClause
syntax (name := sqlGroupBy) &"groupBy " term:max,+ &"into " ident : sqlClause
syntax (name := sqlHaving) &"having " term : sqlClause
syntax (name := sqlSelect) &"select " term : sqlClause
syntax (name := sqlDistinct) &"distinct" : sqlClause
syntax (name := sqlLimit) &"limit " term:max (&"offset " term:max)? : sqlClause
syntax (name := sqlOffset) &"offset " term:max : sqlClause

/-- `query! { … }` builds a query whose context is inferred from the use
site; `query! MyDb { … }` pins the context in place (expands to a
`( … : Query MyDb _)` ascription) — the form for standalone definitions,
where nothing downstream determines the context. -/
scoped syntax (name := sqlQuery) "query! " (ident)? "{" withoutPosition(sepByIndentSemicolon(sqlClause)) "}" : term

open Lean

private def sepTerms (stx : Syntax) : Syntax.TSepArray `term "," :=
  .ofElems (stx.getSepArgs.map (⟨·⟩))

/-- Fold the leading clauses (from/join/where/orderBy) right-to-left over the
terminal. The fold is `SpineQ`-valued: each clause's terminal shape is known
statically at expansion, so no run-time grouped/plain dispatch is needed. -/
private def foldLeading (acc : Term) (c : Syntax) : MacroM Term := do
  if c.isOfKind ``sqlFrom then
    `(LeanLinq.QuerySource.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
  else if c.isOfKind ``sqlJoin then
    `(LeanLinq.SpineQP.joinT $(⟨c[3]⟩)
        (fun $(⟨c[1]⟩) => $(⟨c[5]⟩)) (fun $(⟨c[1]⟩) => $acc))
  else if c.isOfKind ``sqlLeftJoin then
    `(LeanLinq.SpineQP.joinLeftT $(⟨c[3]⟩)
        (fun $(⟨c[1]⟩) => $(⟨c[5]⟩)) (fun $(⟨c[1]⟩) => $acc))
  else if c.isOfKind ``sqlWhere then
    `(LeanLinq.SpineQP.guard $(⟨c[1]⟩) $acc)
  else if c.isOfKind ``sqlOrderBy then
    `(LeanLinq.SpineQP.order [$(sepTerms c[1]),*] $acc)
  else
    Macro.throwErrorAt c "unexpected clause before `select` (allowed: from, join, leftJoin, where, orderBy, groupBy, having)"

/-- Apply the trailing clauses (distinct / limit [offset] / offset) in
written order. -/
private def applyTrailing (acc : Term) (c : Syntax) : MacroM Term := do
  if c.isOfKind ``sqlDistinct then
    `(LeanLinq.Query.distinct $acc)
  else if c.isOfKind ``sqlLimit then
    let lim : Term := ⟨c[1]⟩
    if c[2].getNumArgs > 0 then
      `(LeanLinq.Query.limitOffset $acc (some $lim) (some $(⟨c[2][1]⟩)))
    else
      `(LeanLinq.Query.limit $acc $lim)
  else if c.isOfKind ``sqlOffset then
    `(LeanLinq.Query.offset $acc $(⟨c[1]⟩))
  else
    Macro.throwErrorAt c "only `distinct`, `limit`, and `offset` may follow `select`"

private def expandClauses (clauses : List Syntax) : MacroM Term := do
  match clauses.findIdx? (·.isOfKind ``sqlSelect) with
  | none => Macro.throwError "query! must contain a `select` clause"
  | some i =>
    let pre := clauses.take i
    -- note: `(…)!` parenthesized so the lexer doesn't munch `![` (the
    -- row-literal token) out of `clauses[i]![1]`
    let selRow : Term := ⟨(clauses[i]!)[1]⟩
    let post := clauses.drop (i + 1)
    let core ←
      match pre.findIdx? (·.isOfKind ``sqlGroupBy) with
      | none =>
        match pre.find? (·.isOfKind ``sqlHaving) with
        | some h => Macro.throwErrorAt h "`having` requires a `groupBy … into …` clause"
        | none => do
          let terminal ← `(LeanLinq.SpineQP.yield $selRow)
          pre.foldrM (fun c acc => foldLeading acc c) terminal
      | some gi => do
        let g := pre[gi]!
        let before := pre.take gi
        let after := pre.drop (gi + 1)
        if let some g' := (after.find? (·.isOfKind ``sqlGroupBy)) then
          Macro.throwErrorAt g' "duplicate `groupBy` clause"
        if let some h := before.find? (·.isOfKind ``sqlHaving) then
          Macro.throwErrorAt h "`having` must follow the `groupBy` clause"
        -- after the grouping, only `having` (at most once) and `orderBy` —
        -- the aggregate binder is not in scope for `where`/`from`/joins
        let havings := after.filter (·.isOfKind ``sqlHaving)
        let orderBys := after.filter (·.isOfKind ``sqlOrderBy)
        if havings.length > 1 then
          Macro.throwErrorAt havings[1]! "duplicate `having` clause"
        if let some c := after.find? (fun c =>
            !c.isOfKind ``sqlHaving && !c.isOfKind ``sqlOrderBy) then
          Macro.throwErrorAt c "only `having` and `orderBy` may appear between `groupBy` and `select`"
        let hv ← match havings with
          | [] => `(Option.none)
          | h :: _ => `(Option.some $(⟨h[1]⟩))
        let terminal ← `(LeanLinq.SpineQP.groupYield __gkeys $hv $selRow)
        let grouped ← orderBys.foldrM (fun c acc => foldLeading acc c) terminal
        -- `into a` binds the aggregate token over having/orderBy/select —
        -- but NOT over the keys: grouping *by* an aggregate is meaningless
        -- SQL, so the keys elaborate outside the binder (referencing `a`
        -- in a key is an unknown identifier, as it should be)
        let binder : Ident := ⟨g[3]⟩
        let withBinder ← `(let __gkeys := [$(sepTerms g[1]),*]
          (fun ($binder : LeanLinq.Agg) => $grouped) LeanLinq.Agg.mk)
        before.foldrM (fun c acc => foldLeading acc c) withBinder
    let coreQ ← `(LeanLinq.QueryP.spine $core)
    post.foldlM applyTrailing coreQ

@[macro sqlQuery] def expandQuery : Lean.Macro := fun stx => do
  let q ← expandClauses stx[3].getSepArgs.toList
  if stx[1].getNumArgs > 0 then
    `(($q : LeanLinq.Query $(⟨stx[1][0]⟩) _))
  else
    pure q

end LeanLinq
