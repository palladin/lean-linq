# lean-linq

[![CI](https://github.com/palladin/lean-linq/actions/workflows/ci.yml/badge.svg)](https://github.com/palladin/lean-linq/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![dialects](https://img.shields.io/badge/SQL-SQLite%20%7C%20PostgreSQL%20%7C%20MySQL%20%7C%20SQL%20Server-informational)](#integration-tests)

A type-safe, deeply-embedded SQL query DSL for Lean 4 — language-integrated queries built
from intrinsically-typed GADTs and PHOAS binders: schemas index the types of queries and rows,
so only well-formed SQL elaborates.

Queries are staged: bound row variables carry *SQL expressions* (not runtime values) and
compose an expression tree. The compiler emits parameterized SQL — literals
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
(the `SqlType` index bundles primitive and nullability), a `leftJoin`'s joined row is
NULL-lifted *in its type*, aggregates
are nullable (empty groups), `isNull` never is, and writing NULL into a NOT NULL
column — `setNull`, or a nullable value in `.value` — is an elaboration error. The
payoff is at the read side: fetched cells have **honest types** — `row["Name"]` is
a `String` when the schema says NOT NULL, an `Option String` only when it says
`.null` — and the drivers reject a wire NULL in a NOT NULL column as the protocol
error it is.

**Scope**: lean-linq compiles queries to `CompiledSql` (SQL text + parameter bindings) for
any driver to execute, and ships **native drivers for all four engines** — SQLite
(C FFI over the system sqlite3), PostgreSQL (libpq), MySQL (libmysqlclient,
`brew install mysql-client`), and SQL Server (FreeTDS, `sp_executesql` RPC): typed queries in, typed rows
out, parameters bound natively — see "Executing for real" below.

## `db!` — database programs with the round-trip bill in the type

`Db` prices round trips in the type (`fetch` = 1, data-dependent `bind` =
`+`, per-row `for` = body grade × collection length — a derived bind-chain), and
execution demands a budget plus a proof — the philosophy being that everything is
priced and the *proof* is the gate. A grade **is its collapse** — a function
from table-size valuations to `Nat` — and there is no ⊤ and no ℕ∞ anywhere: the
unknown is not "unbounded", it is a *symbol* (`customers.size` reads the size),
and evaluating at a valuation σ is application. `customers.size + 1` is a type;
`q.gcard` prices a query's rows in the same terms (a source is its table's
symbol, joins multiply, unions add, `limit` takes the pointwise `min` of the
inner bound and the limit — tighter than either); the algebra is pointwise, so
grade arithmetic is plain `Nat` arithmetic, and the doors discharge their
obligations by unfolding to it (`omega` after a definitional normalization).

That gives N+1 four doors, none accidental: `fetchFor` batches a whole key set
into one `IN (…)` round (grade 1); `let ys ← for x in xs do body` loops per row
with the **exact dynamic grade** `k * xs.length` — for collections already in
hand, proved at the door (`by decide` for literals, `omega` for computed
budgets); over *just-fetched* rows, `fetchLimit q n` returns a length-refined
list (`{xs // xs.length ≤ n}`, backed by the first theorem about the executable
semantics: `Query.run_limit_length_le`, `LIMIT` really limits), and looping over
its `.val` fuses into `DbP.forRows`, whose budget proof *is* the refinement
— grade `m + k * n`, closed, silent; and the plain spelling needs no bound at
all — `let xs ← q.execQuery` then `for p in xs do body` fuses into `forFetched`,
because `fetch` carries as its postcondition that the rows fit `q.gcard` at every
size valuation σ — and the graded spec threads σ, so the loop's budget proof
consumes the contract exactly where it was measured and transports it through
the evaluation homomorphism, grade `1 + k * q.gcard` in the
database's own terms. `exec budget` refuses a symbolic grade statically (no
number dominates a table symbol); the sized door `execWithin` collapses the
grade against the live database's own sizes and checks *before* interpreting
a single round; `execAll` runs unchecked, visibly. You can write N+1 when you
mean it — priced by a bounded query or by the database itself — and you cannot
write it by accident: a loop over a collection *derived* from fetched rows
(`filterMap` ids and the like) has no contract to consume, and no proof exists.
(Independence — fetches sharing a round — is applicative structure, not
monadic; it was deliberately removed from the core and returns with a free
applicative layered over the monad, where PostgreSQL pipeline batching lives.)

All of it in one definition, written in `db!` do-sugar:

```lean
def topSpendersDetail (n : Nat) :
    Db ShopDb (Grade.nat n + 1) (List (String × Nat)) := db! {
  let spenders ← Query.from' (ts := ShopDb) customers
    |>.where' (fun c => 18 <. c["Age"])
    |>.orderBy (fun c => [c["Name"].asc])
    |>.fetchLimit n                           -- LIMIT n, length-refined rows
  let report ← for s in spenders.val do       -- fuses into forRows: the proof is the refinement
    Query.from' (ts := ShopDb) orders
      |>.where' (fun o => o["CustomerId"] ==. s["Id"])
      |>.execQuery
      |>.map (fun os => (s["Name"], os.length))
  return report
}

#eval (topSpendersDetail 5).exec 6 db      -- 5 + 1 rounds declared; proof by decide, silent

-- and "all rows, per row" needs no bound at all — the price is symbolic:
def topSpendersAll : Db ShopDb (customers.size + 1) (List (String × Nat)) := db! {
  let spenders ← Query.from' (ts := ShopDb) customers
    |>.where' (fun c => 18 <. c["Age"]) |>.execQuery
  let report ← for s in spenders do           -- fuses into forFetched: the proof is fetch's contract
    Query.from' (ts := ShopDb) orders
      |>.where' (fun o => o["CustomerId"] ==. s["Id"])
      |>.execQuery
      |>.map (fun os => (s["Name"], os.length))
  return report
}

#eval topSpendersAll.execWithin 50 db              -- collapses |customers|+1 at db's sizes, checks, runs
#check_failure (topSpendersAll.exec 1000 db)       -- no number dominates |customers| + 1
```

Writes are effects in the same monad — `insert`, `update`, `delete`,
`INSERT … SELECT`, and batched multi-row `VALUES` each cost one operation and
return their **affected-row count** (exact in the model, engine-reported over the
wire). The grade is simply the count of database operations, reads and writes
alike — so the write-side N+1 carries its bill too:

```lean
-- one SELECT, then one INSERT per row — the type says what it costs:
def duplicateAll : Db ShopDb (customers.size + 1) Nat := db! {
  let rows ← Query.from' (ts := ShopDb) customers |>.execQuery
  let ks ← for r in rows do
    customers.insert (ts := ShopDb)
      |>.value "Id" r["Id"] |>.value "Age" r["Age"] |>.value "Name" r["Name"]
      |>.execInsert
  return ks.sum
}

-- the same copy as INSERT … SELECT: the engine moves the rows, grade 1
def duplicateAllFast : Db ShopDb 1 Nat := db! {
  let k ← customers.insertFrom (Query.from' (ts := ShopDb) customers)
    |>.execInsertSelect
  return k
}
```

On a fetched row, `s["Id"]` in an expression position embeds the cell as a typed
literal (the inner query's WHERE), and anywhere else reads the honest value —
the same brackets both ways. Over the wire the doors are per-driver:
`f.execIO conn budget` (SQLite), `f.execPg conn budget` (PostgreSQL, pipelined),
`f.execMs conn budget` (SQL Server) — each with an unchecked `…All` variant.
All interpret sequentially, one statement per round.

## Building

```
lake build                        # library
lake test                         # golden tests: 404 cases × 4 dialects (exact SQL + parameters)
lake exe tests --update           # regenerate Tests/golden/{sqlite,sqlserver,postgres}.golden

docker compose up -d --wait       # PostgreSQL + SQL Server test databases
lake exe integration              # execute all 358 cases against live SQLite/PostgreSQL/SQL Server
lake exe integration --update     # regenerate Tests/golden/results-*.golden

lake exe sqlitedriver             # native-driver sweeps: full corpus through each driver,
lake exe pgdriver                 #   compared against the evaluator at the Values level
lake exe mssqldriver
```

## Integration tests

Nearly every pipeline query case has a comprehension twin (`C<Name>`, Tests/QueriesC.lean;
the exceptions are shapes `query!` cannot spell — split limit/offset chains and
set-operation compositions)
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
  `&&. ||. !.`, `like`, `inValues`/`notInValues`, `inQuery`/`notInQuery` (subquery),
  `exists'`/`notExists` (correlated subqueries), `caseWhen`,
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
abbrev ShopDb : Ctx := { tables := [("Customers", CustomersS), ("Orders", OrdersS)] }

def report := Query.from' (ts := ShopDb) customers
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

Nearly every pipeline test case has a comprehension twin (Tests/QueriesC.lean), so both surfaces
are exercised by the full test stack.

## Statements

INSERT / UPDATE / DELETE use the same name-checked, typed column machinery:

```lean
customers.insert (ts := MyDb)
  |>.value "Id" 200 |>.value "Name" "John Doe" |>.valueNull "Age"
-- INSERT INTO "Customers" ("Id", "Name", "Age") VALUES (:p0, :p1, NULL)

customers.update (ts := MyDb)
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["Id"] ==. 200)
-- UPDATE "Customers" SET "Age" = ("Age" + :p0) WHERE ("Id" = :p1)

customers.delete (ts := MyDb) |>.where' (fun c => c["Age"] <. 18)
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

- **Parameters are bound natively**, and there are two kinds. *User parameters*
  (`Ctx.params`) are the query's typed interface — declared names whose values the
  caller supplies at execution, read from the same typed `ParamEnv c.params` by the
  evaluator and the drivers alike. *Auto parameters* (`p0, p1, …`) are a compilation
  artifact: one per literal, value shipped alongside the SQL — the evaluator never
  sees them (it evaluates literals directly), and they exist so no value ever appears
  in the SQL text (injection safety, plan-cache reuse, typed wire transfer). Nothing
  is ever inlined, at compile time or execution time; user names shaped like `p0` are
  statically refused to keep the namespaces apart.
- **Rows decode schema-directed into `Values s`** using the `SqlType.interp`
  conventions, so driver output is cell-for-cell comparable with `Query.run` — and the
  test suite does exactly that: `lake exe sqlitedriver` runs all registered cases through the
  driver and compares against the evaluator **at the `Values` level** (statements
  verified inside rolled-back transactions).
- **`Db` programs run over the wire**: `f.execIO conn budget` interprets the same
  round-budgeted tree `runWith` interprets in memory, with the same proof discipline.

**PostgreSQL** works the same way (`import LeanLinq.Driver.Postgres`, `Pg.connect` with
a conninfo string; requires libpq — `brew install libpq` / `libpq-dev`): the driver
rewrites the compiled `:name` placeholders to the wire's `$N` form and sends every
parameter with an explicit type OID, which resolves `EXTRACT(YEAR FROM $1)`-style
inference properly. `f.execPg conn budget` interprets one statement per round
(pipeline batching is applicative structure and returns with the free-applicative
layer). `lake exe pgdriver` sweeps the full corpus against live PostgreSQL, typed
`Values`-to-`Values` against the evaluator.

**MySQL** (`import LeanLinq.Driver.Mysql`, `Mysql.connect`; requires
libmysqlclient — `brew install mysql-client` / `libmysqlclient-dev`) executes over
prepared statements: the driver rewrites each `:name` *occurrence* to MySQL's
unnamed `?` and emits values in occurrence order (a repeated named reference
repeats its value — unlike PostgreSQL's `$N`), parameters bind as text (MySQL
coerces in typed contexts), and results decode through the same shared cell
parser as every other driver. `lake exe mysqldriver` sweeps the corpus against
the compose service on port 3307.

**SQL Server** (`import LeanLinq.Driver.Mssql`, `Ms.connect`
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
connection — no pipelining — so `Db.execMs` is sequential and the `max` grade
stays an honest upper bound, as with in-process SQLite. `lake exe mssqldriver`
sweeps the full corpus against live SQL Server (docker compose, port 14333), typed
`Values`-to-`Values` against the evaluator — with the native drivers now covering
all four engines, the string-based CLI integration harness is a retirement
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
case's expected rows with `Query.run` and differential-tests all four
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
- `SqlType = {ty : SqlPrim, nullable : Bool}` — the SQL type *is* its primitive plus
  its nullability, one value that travels together (bare = NOT NULL). `Schema := List
  (String × SqlType)`; `Ctx := { tables, params }` both over `SqlType`;
  `SqlExpr : Ctx → SqlType → Type` — nullability rides the single index;
  `Row : Ctx → Schema → Type` heterogeneous tuple of expressions; `Values` cells have
  per-column honest types (`Option` only where `.null`).
- Table names live at the type level (`Table (n : String) (s : Schema)`); queries are indexed
  by their ambient context, and `fromT`/`joinT`/`param` *store* the `HasTable`/`HasParam`
  membership instance resolved at elaboration — a query carries its referenced tables and
  parameters as capabilities, so the evaluator reads rows and bindings through them with no
  run-time resolution. A parameter's type comes from the context, not an annotation
  (`SqlExpr.param "minAge"`).
- One mutual query algebra (PHOAS): expressions, rows, and the two query levels —
  `SpineQP` (the comprehension spine: `yield`/`groupYield`/`guard`/`fromT`/`joinT`/`order`/
  `fromQ`) and `QueryP` (boundary nodes: `distinct`, `limit`, set ops) — form a single
  inductive family parameterized by the row representation `ρ : Schema → Type`. Binders
  take the opaque atom `ρ s` (the one slot a `∀ρ`-polymorphic term cannot inspect), which
  keeps every mutual occurrence positive; the smart constructors re-wrap with
  `RowP.ofAtom`, so surface lambdas receive rows. The public `Query ts s` is the bundle
  `∀ ρ, QueryP ρ ts s`: the compiler reads it at `AliasOf`, the evaluator walks the same
  instantiation, and `card` counts it — one term, every reading, with agreement by
  parametricity rather than by discipline.
- Subqueries inside expressions (`inQuery`, `exists'`, `.embed`) are stored
  *structurally* at the same ρ, so a correlated subquery captures the outer binder like
  any other Lean value. That capture pins it to the ambient representation: a correlated
  inner chain spells its head per-ρ (`QueryP.from' … |>.where' (fun o => o["CustomerId"]
  ==. c["Id"])`), and an inner `query!` block ascribes `: QueryP _ Ctx _`. Uncorrelated
  subqueries stay ordinary bundles and drop in unchanged.
- Compiler: a `StateM` (alias counter + parameter accumulator) walk that renders the spine as
  one flat SELECT, recursing structurally into stored subqueries (inner aliases continue the
  outer numbering). The evaluator (`Query.run`) walks the same instantiation with scopes
  flowing down — sources extend each alias→row scope, terminals evaluate where their trees
  are structural — so correlated references resolve identically in both readings.
  Everything is total — the family is a reflexive inductive, so structural recursion covers
  binder continuations applied to any atom —
  which means the kernel itself can run both (`#guard` tests of generated SQL *and* of
  evaluated rows at elaboration time).

## Status

Core, full query surface (joins, grouping, aggregates, set ops, subqueries),
statements, the four dialects, native drivers for all four engines, and the
round-budgeted `Db` layer are implemented, with a 404-case × 4-dialect
golden suite (both surfaces), an executable in-memory oracle, per-driver
corpus sweeps, and live 3-engine integration tests.

Known limitations: trailing `orderBy` after
`distinct`/`limit` is pipeline-only (the comprehension fuses ordering before
them). Possible next steps: EXISTS/NOT IN, window functions, CTEs, and
cardinality-indexed queries — row bounds, predicate satisfaction, and
sortedness as propositions the fetch returns with the rows.
