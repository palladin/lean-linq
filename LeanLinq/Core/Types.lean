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

end LeanLinq
