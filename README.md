# lean-linq

A type-safe, deeply-embedded SQL query DSL for Lean 4 — language-integrated queries in the
spirit of LINQ and [TypedSqlBuilder](https://github.com/palladin/typedsqlbuilder), built on the
intrinsically-typed GADT + HOAS methodology of
[SqlDsl.idr](https://github.com/palladin/idris-snippets/blob/master/src/SqlDsl.idr).

Queries are staged: lambdas in `filter`/`select` receive rows of *SQL expressions* (not runtime
values) and compose an expression tree, MetaOCaml-style. The compiler emits parameterized SQL —
literals never appear in the SQL text.

```lean
import LeanLinq
open LeanLinq

abbrev CustomersS : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table CustomersS := ⟨"Customers"⟩

def adults := Query.from' customers
  |>.filter (fun c => 18 <. c["Age"] &&. !.(c["Name"] ==. "Bob"))
  |>.select (fun c => [c["Name"].as "Name", c["Id"].as "Id"])

#eval adults.toSql
-- { sql := "SELECT c1.Name AS Name, c1.Id AS Id FROM (SELECT * FROM (SELECT * FROM Customers) AS c0
--           WHERE ((@p0 < c0.Age) AND (NOT (c0.Name = @p1)))) AS c1",
--   params := #[("@p0", .int 18), ("@p1", .string "Bob")] }
```

Ill-typed queries don't compile: a misspelled column name, comparing an `int` column to a
`string`, or adding two `string` columns are all elaboration errors.

## Building

```
lake build   # library
lake test    # golden tests (exact SQL text + parameters)
```

## API (milestone 1)

| Combinator | SQL | Notes |
|---|---|---|
| `Query.from' t` | `FROM` | `from` is a Lean keyword |
| `q.filter (fun r => p)` | `WHERE` | `where` is a Lean keyword |
| `q.select (fun r => proj)` | `SELECT` | projection = row literal of `.as`-named cells |
| `q₁.product q₂ (fun a b => proj)` | cross join | `fun a b => a ++ b` keeps all columns |
| `q.toSql` | — | returns `Compiled` (sql + params, SQLite `@pN` style) |

Row access inside lambdas:

- `r["Name"]` — by name, checked at compile time (typeclass `HasCol` over the schema).
- `r.nth ⟨0, by decide⟩` — positional.
- `[e₁.as "A", e₂.as "B"]` — projection row literal; `r₁ ++ r₂` splices whole rows.

Operators on `SqlExpr` (scoped in `LeanLinq`): `+` (int), `++` (string concat), and the dotted
comparison/logic family `==.` `!=.` `<.` `&&.` `||.` `!.` (the Prelude's `==`/`<`/`&&` return
`Bool`/`Prop`, so SQL needs its own).

## Rules of the road

- **Schemas must be `abbrev`**, not `def` — column lookup and instance search must see through
  the schema name.
- **Literals go on the right** of an operator (`c["Name"] ==. "Alice"`): coercions only fire
  against a known expected type. For literal-first, use `SqlExpr.str`/`.int`/`.bool`.
- Row literals `[…]` overload the `List` literal syntax and resolve against the expected type;
  inside `select` lambdas this is always unambiguous.

## Design

- `SqlType` universe; `SqlExpr : SqlType → Type` GADT — ill-typed SQL is unrepresentable.
- `Schema := List (String × SqlType)`; `Row : Schema → Type` heterogeneous tuple of expressions.
- `Query : Schema → Type` GADT with HOAS predicates/projections.
- Compiler: `StateM` (alias counter + parameter accumulator); every combinator wraps its child
  as a derived table `(…) AS cN` — a transparent, predictable translation (flattening is a
  later, purely cosmetic phase).

## Roadmap

1. ~~Idris-parity core~~ (this milestone)
2. Ergonomics: `sql_table` command macro, `query!` syntax (real `from`/`where` keywords, `c.Name` dot access)
3. Full type universe (long/double/decimal/dateTime/guid), NULL, user-named parameters
4. Full query surface: orderBy, distinct, limit/offset, inner/left joins, groupBy/having,
   aggregates, union/intersect/except, subqueries in expressions
5. Statements: INSERT / UPDATE / DELETE
6. Dialects: SQLite / PostgreSQL / SQL Server, subquery flattening
