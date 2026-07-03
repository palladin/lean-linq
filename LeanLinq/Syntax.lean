import LeanLinq.Core.Query

/-! # C#-style LINQ comprehension syntax

```
query! {
  from c in customers
  from o in orders
  where c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "Name", o["OrderId"].as "OrderId"]
}
```

desugars right-to-left into the binder-style `Query` constructors:
`from x in src …` ⇒ `QuerySource.bind src (fun x => …)` (sources are tables,
or queries — inlined by normalization), `where p …` ⇒ `Query.guard p …`, and
the final `select r` ⇒ `Query.yield r`. Nested `from`s are cross products.
Clauses are newline- (or `;`-) separated, do-notation style.

Token choices, learned the hard way:
- the head must be a *reserved* token — non-reserved (`&"…"`) leading keywords
  are not dispatched for term parsers, so the whole block would parse as an
  application of an identifier to a structure instance;
- `query!` (like `panic!`/`assert!`) reserves nothing usable: `query` remains
  a perfectly good identifier, since `!` cannot appear in identifiers;
- `select` stays non-reserved — reserving it would break `.select`/dot
  notation everywhere — which is fine mid-rule, just not in head position. -/

-- `behavior := both` makes the category dispatch rules led by a non-reserved
-- identifier keyword (our `select`); the default behavior only dispatches on
-- reserved tokens.
declare_syntax_cat sqlClause (behavior := both)

namespace LeanLinq

syntax (name := sqlFrom) "from " ident " in " term : sqlClause
syntax (name := sqlWhere) "where " term : sqlClause
syntax (name := sqlSelect) &"select " term : sqlClause

scoped syntax (name := sqlQuery) "query! " "{" withoutPosition(sepByIndentSemicolon(sqlClause)) "}" : term

open Lean in
private def expandClauses : List (TSyntax `sqlClause) → MacroM Term
  | [] => Macro.throwError "query comprehension must end with a `select` clause"
  | [c] =>
    -- `select` is non-reserved, so its rule cannot be matched by a quotation
    -- pattern (a leading ident gets antiquotation treatment); match by kind.
    if c.raw.isOfKind ``sqlSelect then
      `(LeanLinq.Query.yield $(⟨c.raw[1]⟩))
    else
      Macro.throwError "the last clause of a query comprehension must be `select`"
  | c :: rest => do
    let restE ← expandClauses rest
    match c with
    | `(sqlClause| from $x in $src) => `(LeanLinq.QuerySource.bind $src (fun $x => $restE))
    | `(sqlClause| where $p) => `(LeanLinq.Query.guard $p $restE)
    | _ =>
      if c.raw.isOfKind ``sqlSelect then
        Macro.throwError "`select` must be the last clause of a query comprehension"
      else
        Macro.throwUnsupported

@[macro sqlQuery] def expandQuery : Lean.Macro := fun stx =>
  expandClauses (stx[2].getSepArgs.toList.map (⟨·⟩))

end LeanLinq
