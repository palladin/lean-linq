namespace LeanLinq

/-- SQL column/expression types. Milestone 1 covers int/bool/string;
later phases extend this to long/double/decimal/dateTime/guid + nullability. -/
inductive SqlType where
  | int
  | bool
  | string
  deriving DecidableEq, Repr

/-- Runtime values carried by SQL parameters. -/
inductive SqlValue where
  | int (i : Int)
  | bool (b : Bool)
  | string (s : String)
  deriving Repr, BEq

end LeanLinq
