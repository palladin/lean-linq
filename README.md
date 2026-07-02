# lean-linq

A type-safe, deeply-embedded SQL query DSL for Lean 4 — language-integrated queries built
from intrinsically-typed GADTs and HOAS binders: schemas index the types of queries and rows,
so only well-formed SQL elaborates.

Queries are staged: bound row variables carry *SQL expressions* (not runtime values) and
compose an expression tree, MetaOCaml-style. The compiler emits parameterized SQL — literals
never appear in the SQL text.

```lean
import LeanLinq
open LeanLinq

abbrev CustomersS : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table CustomersS := ⟨"Customers"⟩
abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int)]
def orders : Table OrdersS := ⟨"Orders"⟩

def customerOrders := query! {
  from c in customers
  from o in orders
  where c["Id"] ==. o["CustomerId"]
  where c["Age"] >. 18
  select ![c["Name"].as "Name", o["OrderId"].as "OrderId"]
}

#eval customerOrders.toSql
-- { sql := "SELECT c0.Name AS Name, c1.OrderId AS OrderId
--           FROM Customers AS c0, Orders AS c1
--           WHERE (c0.Id = c1.CustomerId) AND (@p0 < c0.Age)",
--   params := #[("@p0", .int 18)] }
```

Ill-typed queries don't compile: a misspelled column name, comparing an `int` column to a
`string`, or adding two `string` columns are all elaboration errors.

## Building

```
lake build   # library
lake test    # golden tests (exact SQL text + parameters)
```

## The comprehension syntax

`query! { … }` takes newline- (or `;`-) separated clauses, desugared right-to-left onto the
core binders (exactly how C# desugars LINQ into `SelectMany`):

| Clause | Desugars to | SQL |
|---|---|---|
| `from x in src` | `QuerySource.bind src (fun x => …)` | a `FROM` source |
| `where p` | `Query.guard p …` | a `WHERE` conjunct |
| `select r` (last) | `Query.yield r` | the `SELECT` list |

Sources are tables *or* queries (subqueries) via the `QuerySource` class. Nested `from`s are
cross products — there is no product combinator; a join is two `from`s and a `where`.
Comprehensions compile to a single flat SELECT.

A pipeline API is also derived on top of the same binders (`from` and `where` are Lean
keywords, hence the primes):

```lean
def adults := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.select (fun c => ![c["Name"].as "Name"])
```

Pipeline stages wrap their input as a derived table (`(…) AS cN`), so prefer `query! {}` when
you want minimal SQL.

Row access and construction:

- `r["Name"]` — column by name, checked at compile time (typeclass `HasCol` over the schema;
  a typo fails instance synthesis).
- `r.nth ⟨0, by decide⟩` — positional.
- `![e₁.as "A", e₂.as "B"]` — row literal for projections; `r₁ ++ r₂` splices whole rows.
  (`![…]` rather than `[…]`: overloading the list brackets would break list *patterns* in any
  scope with LeanLinq notation open — Lean does not backtrack syntax choice nodes in patterns.)

Operators on `SqlExpr` (scoped in `LeanLinq`): `+` (int), `++` (string concat), and the dotted
comparison/logic family `==.` `!=.` `<.` `>.` `&&.` `||.` `!.` (the Prelude's `==`/`<`/`&&`
return `Bool`/`Prop`, so SQL needs its own).

## Rules of the road

- **Schemas must be `abbrev`**, not `def` — column lookup and instance search must see through
  the schema name.
- **Literals go on the right** of `==.`/`!=.` (`c["Name"] ==. "Alice"`): coercions only fire
  against a known expected type. For literal-first, use `SqlExpr.str`/`.int`/`.bool`.
  (Monomorphic operators like `<.`/`>.`/`+` take literals on either side.)

## Design

- `SqlType` universe; `SqlExpr : SqlType → Type` GADT — ill-typed SQL is unrepresentable.
- `Schema := List (String × SqlType)`; `Row : Schema → Type` heterogeneous tuple of expressions.
- `Query : Schema → Type` in monadic-comprehension form:
  `yield : Row s → Query s`, `guard : SqlExpr .bool → Query s → Query s`,
  `fromT : Table s → (Row s → Query s') → Query s'`, and `fromQ` likewise for subqueries.
  HOAS binders; illegal column references are type errors at the binding site.
- Compiler: a `StateM` (alias counter + parameter accumulator) walk that collects the
  comprehension spine — sources, conjuncts, projection — into one flat SELECT; `fromQ`
  recursively compiles derived tables. (`partial`: binders force recursion on applied
  continuations, which structural termination cannot see; the golden-test executable is the
  harness.)

## Roadmap

1. ~~Core: typed GADTs, comprehension + pipeline surfaces, `query!` macro, SQLite-style
   parameterized output~~ (done)
2. Ergonomics: `sql_table` command macro, `c.Name` dot access inside `query!`
3. Full type universe (long/double/decimal/dateTime/guid), NULL, user-named parameters
4. Full query surface: orderBy, distinct, limit/offset, left join, groupBy/having,
   aggregates, union/intersect/except, subqueries in expressions
5. Statements: INSERT / UPDATE / DELETE
6. Dialects: SQLite / PostgreSQL / SQL Server, WHERE-merging into pipeline-generated subqueries
