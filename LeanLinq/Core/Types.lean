namespace LeanLinq

/-- SQL column/expression types. -/
inductive SqlPrim where
  | int
  | long
  | double
  | decimal
  | string
  | bool
  | dateTime
  | guid
  deriving DecidableEq, Repr

/-- Runtime values carried by SQL parameters. Decimals are kept as exact
digit strings; date-times and guids as their textual forms. -/
inductive SqlValue where
  | int (i : Int)
  | long (i : Int)
  | double (f : Float)
  | decimal (digits : String)
  | string (s : String)
  | bool (b : Bool)
  | dateTime (iso : String)
  | guid (g : String)
  | null
  deriving Repr, BEq

/-- Compilation targets. Differ in identifier quoting, parameter prefixes,
LIMIT/OFFSET syntax, and function renderings. -/
inductive DatabaseType where
  | sqlite
  | sqlServer
  | postgres
  | mysql
  deriving DecidableEq, Repr

/-- A column type: the SQL type plus its **nullability** — and the default
is NOT NULL. `("Age", .int)` declares a NOT NULL int; a NULL-capable column
says so explicitly: `("SignupDate", .null .dateTime)`. This is a deliberate
divergence from SQL's default (nullable), in the direction application
schemas actually lean — and it is what lets fetched cells carry honest
types (`s.get "Name" : String`, no `Option`). -/
structure SqlType where
  ty : SqlPrim
  nullable : Bool := false
  deriving DecidableEq, Repr

namespace SqlType

@[reducible] def int : SqlType := ⟨.int, false⟩
@[reducible] def long : SqlType := ⟨.long, false⟩
@[reducible] def double : SqlType := ⟨.double, false⟩
@[reducible] def decimal : SqlType := ⟨.decimal, false⟩
@[reducible] def string : SqlType := ⟨.string, false⟩
@[reducible] def bool : SqlType := ⟨.bool, false⟩
@[reducible] def dateTime : SqlType := ⟨.dateTime, false⟩
@[reducible] def guid : SqlType := ⟨.guid, false⟩

/-- A NULL-capable column: `("Price", .null .decimal)`. -/
@[reducible] def null (t : SqlPrim) : SqlType := ⟨t, true⟩

end SqlType

instance : Coe SqlPrim SqlType := ⟨(⟨·, false⟩)⟩

/-- A relation schema: ordered column names with their column types
(SQL type + nullability; bare means NOT NULL).

IMPORTANT: concrete schemas must be declared with `abbrev` (not `def`) so that
elaboration — column lookup, projection typing — can see through the name:

```
abbrev Customers : Schema :=
  [("Id", .int), ("Name", .string), ("SignupDate", .null .dateTime)]
```
-/
abbrev Schema := List (String × SqlType)

/-- The schema with every column made NULL-capable — the type-level truth
of a LEFT JOIN's right side. Reducible structural recursion (not
`List.map`) so instance search unfolds it over literal schemas. -/
@[reducible] def Schema.asNull : Schema → Schema
  | [] => []
  | (n, c) :: s => (n, ⟨c.ty, true⟩) :: Schema.asNull s

/-- The context a query is typed against: the named tables (with schemas)
and the named parameters (with column types — nullability included) its
database provides. Queries carry a `Ctx` index; membership of each
referenced table/parameter is established by instance search
(`HasTable`/`HasParam`) at construction, and a `TableEnv c.tables` /
`ParamEnv c.params` supplies rows and bindings at evaluation. Like schemas,
concrete contexts must be `abbrev`.

`params` is the query's **typed interface to the caller** — the
user-declared names whose values arrive at execution time, honored
symmetrically by both interpreters (the evaluator reads the `ParamEnv`,
the drivers bind the same values by name). It is *not* where literals
live: constants are stored in the AST and evaluated directly; only
compilation turns them into auto-allocated `p0, p1, …` placeholders so
that values never enter the SQL text (see `CompiledSql`). The two kinds
share the placeholder syntax, which is why user names of the shape
`p{digits}` are reserved and statically refused (`SqlExpr.param`). -/
structure Ctx where
  tables : List (String × Schema)
  params : List (String × SqlType) := []

end LeanLinq
