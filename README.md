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

abbrev CustomersS : Schema :=          -- bare = NOT NULL; nullable is explicit
  [("Id", .int), ("Name", .string), ("Age", .null .int)]
def customers : Table "Customers" CustomersS := ⟨⟩

abbrev MyDb : Ctx := { tables := [("Customers", CustomersS)] }

def adults := Query.from' (ts := MyDb) customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

#eval adults.toSql .sqlite
-- { sql := "SELECT \"a0\".\"Id\" AS \"Id\", \"a0\".\"Name\" AS \"Name\"
--           FROM \"Customers\" \"a0\"
--           WHERE (:p0 < \"a0\".\"Age\") ORDER BY \"a0\".\"Name\" ASC",
--   params := #[(":p0", .int 18)] }
```

The same query in `query!` comprehension syntax — both surfaces normalize to *identical* SQL:

```lean
def adults' := query! MyDb {
  from c in customers
  where 18 <. c["Age"]
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}

#eval adults.toSql .sqlite == adults'.toSql .sqlite   -- true
```

Ill-typed queries don't compile: a misspelled column name, comparing an `int` column to a
`string`, adding two `string` columns, referencing a table outside the declared context
(`Ctx`), or referencing an unbound named parameter are all elaboration errors. A query's
type records the database context it is written against — its tables *and* its named
parameters — and each reference is resolved by instance search (`HasTable`/`HasParam`) at
elaboration time, the way columns are resolved by `HasCol`.

**Nullability lives in the universe.** A schema entry is a column type *plus* its
nullability, and **bare means NOT NULL** — `("Age", .int)` never holds NULL;
NULL-capable columns say so: `("SignupDate", .null .dateTime)` (a deliberate,
Kotlin/C#-style divergence from SQL's default). The flag flows: expressions carry it
(`SqlExpr ts t n`), a `leftJoin`'s joined row is NULL-lifted *in its type*, aggregates
are nullable (empty groups), `isNull` never is, and writing NULL into a NOT NULL
column — `setNull`, or a nullable value in `.value` — is an elaboration error. The
payoff is at the read side: fetched cells have **honest types** — `row.get "Name"` is
a `String` when the schema says NOT NULL, an `Option String` only when it says
`.null` — and the drivers reject a wire NULL in a NOT NULL column as the protocol
error it is.

**Scope**: lean-linq compiles queries to `CompiledSql` (SQL text + parameter bindings) for
any driver to execute, and ships **native drivers for all three engines** — SQLite
(C FFI over the system sqlite3), PostgreSQL (libpq, with pipeline-batched fetch
rounds), and SQL Server (FreeTDS, `sp_executesql` RPC): typed queries in, typed rows
out, parameters bound natively — see "Executing for real" below.

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
  checked three ways: against the **evaluator** (`Query.run` over the seed
  database — expected rows computed from the same query value that produced
  the SQL, for every deterministic case), against per-dialect goldens
  (`Tests/golden/results-{db}.golden`), and across engines.
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
  context-typed named parameters (`SqlExpr.param "minAge"`), `abs`/`round`/`ceiling`/`floor`,
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
def orders : Table "Orders" OrdersS := ⟨⟩

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

## Executing for real: the native drivers

`import LeanLinq.Driver.Sqlite` (a separate lib target — the core library stays
FFI-free) talks to the system sqlite3 library:

```lean
open LeanLinq.Sqlite

def demo : IO Unit := do
  let conn ← Sqlite.connect "app.db"
  let rows ← conn.query adults          -- IO (List (Values s)): typed rows out
  let _ ← conn.execInsert someInsert    -- statements too
  conn.close
```

- **Parameters are bound natively** — auto parameters from the compiled statement's
  values, user-named parameters from the same typed `ParamEnv c.params` the evaluator
  reads. Nothing is ever inlined, at compile time or execution time.
- **Rows decode schema-directed into `Values s`** using the `SqlType.interp`
  conventions, so driver output is cell-for-cell comparable with `Query.run` — and the
  test suite does exactly that: `lake exe sqlitedriver` runs all registered cases through the
  driver and compares against the evaluator **at the `Values` level** (statements
  verified inside rolled-back transactions).
- **`DbFetch` programs run over the wire**: `f.execIO conn budget` interprets the same
  round-budgeted tree `runWith` interprets in memory, with the same proof discipline.

`DbFetch` prices round trips in the type (`fetch` = 1, independent `seq` = `max`,
data-dependent `bind` = `+`, per-row `for` = body grade × collection length), and
execution demands a budget plus a proof — the philosophy being that everything is
representable and the *proof* is the gate. That gives N+1 three doors and one wall:
`fetchFor` batches a whole key set into one `IN (…)` round (grade 1);
`let ys ← for x in xs do body` loops per row with the **exact dynamic grade**
`k * xs.length` — for collections already in hand, proved at the door (`by decide`
for literals, `omega` for computed budgets); and over *just-fetched* rows the loop
is legal exactly when the fetch is bounded — `fetchLimit q n` returns a
length-refined list (`{xs // xs.length ≤ n}`, backed by the first theorem about the
executable semantics: `Query.run_limit_length_le`, `LIMIT` really limits), and
looping over its `.val` fuses into `DbFetch.forRows`, whose budget proof *is* the
refinement — grade `m + k * n`, closed, silent. The wall: over an unbounded fetch no
evidence exists, and the program never elaborates. You can write N+1 when you mean
it — priced by a bounded query — and you cannot write it by accident. (Loops are
first-class constructors with independent bodies, so the pipelining PostgreSQL
driver batches them into shared rounds — the declared grade is an upper bound.)

**PostgreSQL** works the same way (`import LeanLinq.Driver.Postgres`, `Pg.connect` with
a conninfo string; requires libpq — `brew install libpq` / `libpq-dev`): the driver
rewrites the compiled `:name` placeholders to the wire's `$N` form and sends every
parameter with an explicit type OID, which resolves `EXTRACT(YEAR FROM $1)`-style
inference properly. And on PostgreSQL the `DbFetch` grading pays off for real:
`f.execPg conn budget` interprets independence through libpq **pipeline mode** —
`seq` sides and `for` loop bodies share round trips, so the declared grade is an
actual latency bound, not just an upper estimate. `lake exe pgdriver` sweeps the full
corpus against live PostgreSQL, typed `Values`-to-`Values` against the evaluator.

**SQL Server** completes the trilogy (`import LeanLinq.Driver.Mssql`, `Ms.connect`
with host/port/credentials; requires FreeTDS — `brew install freetds` /
`freetds-dev`). It is the one engine that needs **no placeholder rewriting at all**:
the sqlServer dialect already compiles `@p0`/`@minAge`, TDS's native named-parameter
form, so execution is an `sp_executesql` RPC — the compiled SQL travels verbatim as
`@stmt`, a declaration string types every parameter, and the values ride as text
with server-side conversion (the same text-plus-typed-declaration strategy as the
PostgreSQL driver's OIDs). One DB-Library wrinkle is handled transparently: its API
cannot express an *empty string* parameter (zero length means NULL at the API
layer), so executions carrying one fall back to an equivalent `EXEC sp_executesql`
batch with the statement still verbatim. TDS allows one active request per
connection — no pipelining — so `DbFetch.execMs` is sequential and the `max` grade
stays an honest upper bound, as with in-process SQLite. `lake exe mssqldriver`
sweeps the full corpus against live SQL Server (docker compose, port 14333), typed
`Values`-to-`Values` against the evaluator — with the native drivers now covering
all three engines, the string-based CLI integration harness is a retirement
candidate once the parallel-run period ends.

## Running queries in memory

Queries are total, deeply-embedded values, so they carry a denotational
semantics: `Query.run : Query c s → TableEnv c.tables → ParamEnv c.params →
Except EvalError (List (Values s))` evaluates the exact query value that
compiles to SQL against a *typed* in-memory database — SQL semantics
included (three-valued NULL logic, LEFT JOIN padding, GROUP BY/HAVING with
aggregates, exact fixed-point decimals, civil-calendar date arithmetic).
Statements apply as `TableEnv c.tables → Except EvalError (TableEnv
c.tables)`. For a parameterless context the `ParamEnv` argument defaults
away.

NULL and errors are separate channels, never conflated: `Nullable`'s `none`
is SQL NULL and only NULL, while exceptional, statement-aborting conditions
— division by zero, `now` without a clock — are explicit `EvalError`s
(`CASE WHEN` stays lazy, as in SQL, so a guarded division doesn't abort).

Because every table and parameter reference was resolved against the context
at elaboration time (the `HasTable`/`HasParam` instance stored in the query
*is* the accessor), evaluation performs no name lookup and has no failure
mode: running a query against a database that lacks one of its tables — or
leaves one of its parameters unbound — is not an error case, it is
untypeable.

```lean
def db : TableEnv MyDb.tables := .cons [/- value rows -/] .nil

#eval adults.run db      -- Except.ok [(2, "Jane Smith"), (1, "John Doe")]
```

This is also how the test suite works: the integration runner computes every
case's expected rows with `Query.run` and differential-tests all three
engines against it — the executable semantics is the oracle, not hand-written
expectations. And it is the foundation for stating propositions about result
sets (rows of `q.where' p` satisfy `p`, `orderBy` results are sorted, …) as
theorems about `⟦q⟧ = q.run`.

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

- **Schemas and contexts must be `abbrev`**, not `def` — column lookup (`HasCol`) and table
  lookup (`HasTable`) resolve by instance search over the literal lists.
- **Pin the context** — at the query head (`Query.from' (ts := MyDb) t`) or on the
  comprehension (`query! MyDb { … }`): an unannotated standalone definition would leave
  the context as a metavariable, and instance search cannot run against an undetermined
  context. (Nested blocks — subqueries, sources — infer it from the enclosing query.)
- **Literals go on the right** of `==.`/`!=.` (`c["Name"] ==. "Alice"`): coercions only fire
  against a known expected type. For literal-first, use `SqlExpr.str`/`.int`/`.bool`.
  (Monomorphic operators like `<.`/`>.`/`+` take literals on either side.)

## Design

- `SqlType` universe; `SqlExpr : Ctx → SqlType → Type` GADT — ill-typed SQL is unrepresentable.
- `Schema := List (String × SqlCol)` where `SqlCol = {ty : SqlType, nullable : Bool}`
  (bare = NOT NULL); `Ctx := { tables : List (String × Schema), params : List (String ×
  SqlCol) }`; `SqlExpr : Ctx → SqlType → Bool → Type` carries nullability as an index;
  `Row : Ctx → Schema → Type` heterogeneous tuple of expressions; `Values` cells have
  per-column honest types (`Option` only where `.null`).
- Table names live at the type level (`Table (n : String) (s : Schema)`); queries are indexed
  by their ambient context, and `fromT`/`joinT`/`param` *store* the `HasTable`/`HasParam`
  membership instance resolved at elaboration — a query carries its referenced tables and
  parameters as capabilities, so the evaluator reads rows and bindings through them with no
  run-time resolution. A parameter's type comes from the context, not an annotation
  (`SqlExpr.param "minAge"`).
- Two-level query algebra: `SpineQ` (the comprehension spine: `yield`/`guard`/`fromT`/
  `joinT`/`order`/`fromQ`) and `Query` (boundary nodes: `distinct`, `limit`, grouped
  selects, set ops). Separate inductives so the statement ↔ spine compiler recursion is
  structural. HOAS binders; illegal column references are type errors at the binding site.
- Subqueries inside expressions (`inQuery`, `.embed`) are stored as *staged actions*
  (compilation and evaluation), not ASTs — a mutual `SqlExpr`/`Query` block would violate
  strict positivity through the HOAS binders (`Row → Query` puts `Query` inside `Row`'s
  expression fields, left of an arrow).
- Compiler: a `StateM` (alias counter + parameter accumulator) walk that renders the spine as
  one flat SELECT. The evaluator (`Query.run`) is the same walk under a different
  interpretation — binders instantiated with the same alias-marker rows, an alias→row
  environment where the compiler accumulates clause text. Everything is total — `Query` is a
  reflexive inductive, so structural recursion covers HOAS continuations applied to any row —
  which means the kernel itself can run both (`#guard` tests of generated SQL *and* of
  evaluated rows at elaboration time).

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
