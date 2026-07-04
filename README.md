# lean-linq

[![CI](https://github.com/palladin/lean-linq/actions/workflows/ci.yml/badge.svg)](https://github.com/palladin/lean-linq/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![dialects](https://img.shields.io/badge/SQL-SQLite%20%7C%20PostgreSQL%20%7C%20SQL%20Server-informational)](#integration-tests)

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

def adults := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

#eval adults.toSql .sqlite
-- { sql := "SELECT \"a0\".\"Id\" AS \"Id\", \"a0\".\"Name\" AS \"Name\"
--           FROM \"Customers\" \"a0\"
--           WHERE (:p0 < \"a0\".\"Age\") ORDER BY \"a0\".\"Name\" ASC",
--   params := #[(":p0", .int 18)] }
```

Ill-typed queries don't compile: a misspelled column name, comparing an `int` column to a
`string`, or adding two `string` columns are all elaboration errors.

**Scope**: lean-linq compiles queries to `CompiledSql` (SQL text + parameter bindings) for a
database driver to execute — it does not ship a driver. The docker-based integration harness
executes every case against live databases for testing, not production use.

## Building

```
lake build                        # library
lake test                         # golden tests: 355 cases × 3 dialects (exact SQL + parameters)
lake exe tests --update           # regenerate Tests/golden/{sqlite,sqlserver,postgres}.golden

docker compose up -d --wait       # PostgreSQL + SQL Server test databases
lake exe integration              # execute all 355 cases against live SQLite/PostgreSQL/SQL Server
lake exe integration --update     # regenerate Tests/golden/results-*.golden
```

## Integration tests

Every pipeline query case has a comprehension twin (`C<Name>`, Tests/QueriesC.lean)
expressing the same shape with `query!` clauses, so both surfaces are covered by
every layer below. `lake exe integration` executes every registered query and
statement against real databases: SQLite (local temp file), PostgreSQL and SQL Server (docker compose
services, driven through `psql`/`sqlcmd` inside the containers — no local client
installs needed). The seed dataset mirrors the classic customers/products/orders
fixture. Parameters are inlined as dialect-escaped literals *for execution only*;
the library itself always emits parameterized SQL.

- Row results are normalized (booleans, decimal trailing zeros, datetime
  precision, guid case, NULL sentinels, row order for unordered queries) and
  checked three ways: against an **in-memory oracle** (`Tests/Oracle.lean` —
  independently-derived expected rows for every deterministic case), against
  per-dialect goldens (`Tests/golden/results-{db}.golden`), and across
  engines.
- Statements run inside a transaction: execute, verify table state with a
  SELECT, roll back.
- A cross-dialect comparison then checks that all engines agree on every case,
  modulo a small allowlist (AVG division semantics differ by engine: integer on
  SQL Server, numeric on PostgreSQL, float on SQLite).
- Unreachable databases are skipped with a warning: `--db sqlite,postgres`
  selects explicitly.
- Prerequisites: the `sqlite3` CLI (ships with macOS and GitHub runners;
  `apt-get install sqlite3` on minimal Linux) and docker compose v2. The SQL
  Server image is amd64-only: on Apple Silicon it runs via Docker Desktop's
  Rosetta emulation; on ARM Linux (no Rosetta) skip it with
  `--db sqlite,postgres`.

## Feature surface

- **Types**: int, long, double, decimal, string, bool, dateTime, guid; NULL via
  `isNull`/`isNotNull`, `setNull`/`valueNull` in statements.
- **Expressions**: `+ - * /` (numeric), `++` (concat), `==. !=. <. <=. >. >=.`,
  `&&. ||. !.`, `like`, `inValues`, `inQuery` (subquery), `caseWhen`,
  named parameters (`SqlExpr.param`), `abs`/`round`/`ceiling`/`floor`,
  `substring`/`upper`/`lower`/`trim`/`length`,
  `now`/`year`/`month`/`day`/`addDays`/`addMonths`/`addYears`/`diffDays`/`diffMonths`/`diffYears`.
- **Queries**: `from'`/`where'`/`select`, `innerJoin`/`leftJoin` (fuse into one
  statement), `orderBy` (multi-key, fuses), `distinct`, `limitOffset`,
  `groupBy`/`having`/grouped `select` with aggregates (`a.count`, `a.sum`, …),
  scalar queries (`count`/`sum`/`avg`/`min`/`max`, embeddable via `.embed`),
  `union`/`intersect`/`except`.
- **Statements**: `t.insert |>.value …`, `t.update |>.set/.setWith/.setNull |>.where' …`,
  `t.delete |>.where' …`.
- **Dialects**: SQLite (`"x"`, `:p0`, `LIMIT/OFFSET`), SQL Server (`[x]`, `@p0`,
  `OFFSET…FETCH`, `GETDATE`/`DATEADD`/`DATEDIFF`/`LEN`, `+` concat), PostgreSQL
  (`"x"`, `:p0`, `EXTRACT`/`INTERVAL`/`NOW()`): `q.toSql .sqlite`,
  `.toSqlServer`, `.toPostgres`. Every SQLite golden is parse-validated against
  a real SQLite database.

## The pipeline API

The primary surface is a fluent pipeline over typed combinators (`from` and `where` are Lean
keywords, hence the primes):

```lean
abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int), ("Amount", .int)]
def orders : Table OrdersS := ⟨"Orders"⟩

def report := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "CustId", c["Name"].as "Name", o["Amount"].as "Amount"])
  |>.groupBy (fun r => [r["CustId"].key, r["Name"].key])
  |>.having (fun _ a => 1 <. a.count)
  |>.select (fun r a => ![r["Name"].as "Name", (a.sum r["Amount"]).as "Total"])
  |>.orderBy (fun r => [r["Total"].desc])
  |>.limit 10
```

Available: `from'` / `where'` / `select`, `innerJoin` / `leftJoin`, `orderBy` (multi-key),
`groupBy` / `having` / grouped `select` (the lambda receives an `Agg` token: `a.count`,
`a.sum e`, …), `distinct`, `limitOffset`/`limit`/`offset`, `union`/`intersect`/`except`,
and scalar queries (`count`/`sum`/`avg`/`min`/`max`, embeddable in expressions via
`.embed`, subqueries via `inQuery`).

Queries **normalize at construction time** (`Query.bind`, the comprehension monad):
`where'` splices a conjunct, `select` replaces the projection, joins extend the FROM clause,
`orderBy` attaches to the statement, and a query used as a source is inlined — so pipelines
compile to a single flat SELECT. Clauses that must not be spliced through — DISTINCT,
LIMIT/OFFSET, GROUP BY/HAVING, set operations — are *boundary nodes*: binding over them
wraps the query as a derived table, which is exactly SQL's semantics.

## The query! comprehension syntax

The same core also has a C#-LINQ-style comprehension surface: `query! { … }` takes newline-
(or `;`-) separated clauses, desugared right-to-left onto the spine constructors (exactly
how C# desugars LINQ into `SelectMany`):

| Clause | Desugars to | SQL |
|---|---|---|
| `from x in src` | `QuerySource.bind src (fun x => …)` | a `FROM` source |
| `join x in t on p` / `leftJoin x in t on p` | `Query.joinOn` | `INNER/LEFT JOIN … ON` |
| `where p` | `Query.guard p …` | a `WHERE` conjunct |
| `orderBy k, …` | `Query.orderWith` | `ORDER BY` (may reference aggregates when grouped) |
| `groupBy k, … into a` + `having p` | grouped terminal (`Query.groupYieldQ`) | `GROUP BY … HAVING` |
| `select r` | `Query.yield r` | the `SELECT` list |
| trailing `distinct`, `limit n [offset m]`, `offset n` | `.distinct`/`.limitOffset` | `DISTINCT`, `LIMIT/OFFSET` |

Sources are tables *or* queries via the `QuerySource` class (nested `from`s are cross
products). `groupBy … into a` *binds* the aggregate token — like C#'s `group … into g` —
so `a.count` / `a.sum e` are in scope only in the clauses after the grouping; `where` after
`groupBy` and `having` without `groupBy` are rejected. Ordering by an aggregate *expression*
is something only the comprehension can express in one statement:

```lean
query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 18
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Id"].as "CustomerId", (a.sum o["Amount"]).as "TotalSpent"]
}
```

Every pipeline test case has a comprehension twin (Tests/QueriesC.lean), so both surfaces
are exercised by the full test stack.

## Statements

INSERT / UPDATE / DELETE use the same name-checked, typed column machinery:

```lean
customers.insert
  |>.value "Id" 200 |>.value "Name" "John Doe" |>.valueNull "Age"
-- INSERT INTO "Customers" ("Id", "Name", "Age") VALUES (:p0, :p1, NULL)

customers.update
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["Id"] ==. 200)
-- UPDATE "Customers" SET "Age" = ("Age" + :p0) WHERE ("Id" = :p1)

customers.delete |>.where' (fun c => c["Age"] <. 18)
-- DELETE FROM "Customers" WHERE ("Age" < :p0)
```

## Rows and operators

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
- Two-level query algebra: `SpineQ` (the comprehension spine: `yield`/`guard`/`fromT`/
  `joinT`/`order`/`fromQ`) and `Query` (boundary nodes: `distinct`, `limit`, grouped
  selects, set ops). Separate inductives so the statement ↔ spine compiler recursion is
  structural. HOAS binders; illegal column references are type errors at the binding site.
- Subqueries inside expressions (`inQuery`, `.embed`) are stored as *staged compilation
  actions*, not ASTs — a mutual `SqlExpr`/`Query` block would violate strict positivity
  through the HOAS binders (`Row → Query` puts `Query` inside `Row`'s expression fields,
  left of an arrow).
- Compiler: a `StateM` (alias counter + parameter accumulator) walk that renders the spine as
  one flat SELECT. Everything is total — `Query` is a reflexive inductive, so structural
  recursion covers HOAS continuations applied to any row — which means the kernel itself can
  run the compiler (`#guard` tests of generated SQL at elaboration time).

## Status

Core, full query surface (joins, grouping, aggregates, set ops, subqueries),
statements, and the three dialects are implemented, with a 358-case × 3-dialect
golden suite (both surfaces), an executable in-memory oracle, and live 3-engine
integration tests.

Known limitations: no driver layer (compile-only, by design); the `double`
type is implemented but not exercised by the test models (the reference suite
has the same hole); trailing `orderBy` after `distinct`/`limit` is pipeline-only
(the comprehension fuses ordering before them). Possible next steps: a driver /
FFI execution layer, EXISTS/NOT IN, window functions, CTEs.
