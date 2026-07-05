namespace LeanLinq

/-- SQL column/expression types. -/
inductive SqlType where
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
  deriving DecidableEq, Repr

/-- A relation schema: ordered column names with their SQL types.

IMPORTANT: concrete schemas must be declared with `abbrev` (not `def`) so that
elaboration — column lookup, projection typing — can see through the name:

```
abbrev Customers : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
```
-/
abbrev Schema := List (String × SqlType)

/-- A table context: the named tables (with schemas) a query is typed
against. Queries carry a `Ctx` index; the membership of each referenced
table is established by instance search (`HasTable`) at construction, and a
`TableEnv ts` supplies the rows at evaluation. Like schemas, concrete
contexts must be `abbrev`. -/
abbrev Ctx := List (String × Schema)

end LeanLinq
