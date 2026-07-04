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
abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int)]
def orders : Table OrdersS := ⟨"Orders"⟩

def customerOrders := query! {
  from c in customers
  from o in orders
  where c["Id"] ==. o["CustomerId"]
  where c["Age"] >. 18
  select ![c["Name"].as "Name", o["OrderId"].as "OrderId"]
}

#eval customerOrders.toSql .sqlite
-- { sql := "SELECT \"a0\".\"Name\" AS \"Name\", \"a1\".\"OrderId\" AS \"OrderId\"
--           FROM \"Customers\" \"a0\", \"Orders\" \"a1\"
--           WHERE (\"a0\".\"Id\" = \"a1\".\"CustomerId\") AND (:p0 < \"a0\".\"Age\")",
--   params := #[(":p0", .int 18)] }
```

Ill-typed queries don't compile: a misspelled column name, comparing an `int` column to a
`string`, or adding two `string` columns are all elaboration errors.

## Building

```
lake build                        # library
lake test                         # golden tests: 181 cases × 3 dialects (exact SQL + parameters)
lake exe tests --update           # regenerate Tests/golden/{sqlite,sqlserver,postgres}.golden

docker compose up -d --wait       # PostgreSQL + SQL Server test databases
lake exe integration              # execute all 181 cases against live SQLite/PostgreSQL/SQL Server
lake exe integration --update     # regenerate Tests/golden/results-*.golden
```

## Integration tests

`lake exe integration` executes every registered query and statement against real
databases: SQLite (local temp file), PostgreSQL and SQL Server (docker compose
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

## The comprehension syntax

`query! { … }` takes newline- (or `;`-) separated clauses, desugared right-to-left onto the
core binders (exactly how C# desugars LINQ into `SelectMany`):

| Clause | Desugars to | SQL |
|---|---|---|
| `from x in src` | `QuerySource.bind src (fun x => …)` | a `FROM` source |
| `join x in t on p` / `leftJoin x in t on p` | `Query.joinOn` | `INNER/LEFT JOIN … ON` |
| `where p` | `Query.guard p …` | a `WHERE` conjunct |
| `orderBy k, …` | `Query.orderWith` | `ORDER BY` (may reference aggregates when grouped) |
| `groupBy k, …` + `having p` | grouped terminal (`Query.groupYieldQ`) | `GROUP BY … HAVING` |
| `select r` | `Query.yield r` | the `SELECT` list |
| trailing `distinct`, `limit n [offset m]`, `offset n` | `.distinct`/`.limitOffset` | `DISTINCT`, `LIMIT/OFFSET` |

Sources are tables *or* queries via the `QuerySource` class. Nested `from`s are cross
products — there is no product combinator; a join is two `from`s and a `where` (or a `join`
clause). In grouped comprehensions, aggregates use the `agg` constant (`agg.count`,
`agg.sum e`, …) in `having`, `orderBy`, and `select` — and ordering by an aggregate
expression is something only the comprehension can express in one statement:

```lean
query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 18
  groupBy c["Id"].key, c["Name"].key
  having agg.count >. 1
  orderBy (agg.sum o["Amount"]).desc
  select ![c["Id"].as "CustomerId", (agg.sum o["Amount"]).as "TotalSpent"]
}
```

A pipeline API is derived on top of the same core (`from` and `where` are Lean keywords,
hence the primes):

```lean
def adults := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.select (fun c => ![c["Name"].as "Name"])
```

Queries **normalize at construction time** (`Query.bind`, the comprehension monad):
`where'` splices a conjunct, `select` replaces the projection, joins extend the FROM clause,
`orderBy` attaches to the statement, and a query used as a `from` source is inlined. Both
surfaces compile to the same flat SELECT. Clauses that must not be spliced through —
DISTINCT, LIMIT/OFFSET, GROUP BY/HAVING, set operations — are *boundary nodes*: binding over
them wraps the query as a derived table, which is exactly SQL's semantics.

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
statements, and the three dialects are implemented, with a 181-case × 3-dialect
golden test suite. Possible next steps: executing queries against a live
connection, richer HAVING/ORDER BY over aggregates, and window functions.
