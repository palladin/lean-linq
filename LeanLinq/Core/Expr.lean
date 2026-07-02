import LeanLinq.Core.Types

namespace LeanLinq

/-- Intrinsically-typed SQL expressions: `SqlExpr t` can only be built from
operations valid for `t`, so ill-typed SQL is unrepresentable.

Construct these via the notation in `LeanLinq.Notation` (`==.`, `&&.`, `+`, …)
rather than the raw constructors: user code that stays on the notation layer is
insulated from internal refactors (e.g. the planned `mutual` merge with `Query`
for subqueries-in-expressions). -/
inductive SqlExpr : SqlType → Type where
  | intC    : Int → SqlExpr .int
  | boolC   : Bool → SqlExpr .bool
  | stringC : String → SqlExpr .string
  | plus    : SqlExpr .int → SqlExpr .int → SqlExpr .int
  | concat  : SqlExpr .string → SqlExpr .string → SqlExpr .string
  | eq      : {t : SqlType} → SqlExpr t → SqlExpr t → SqlExpr .bool
  | lt      : SqlExpr .int → SqlExpr .int → SqlExpr .bool
  | and     : SqlExpr .bool → SqlExpr .bool → SqlExpr .bool
  | or      : SqlExpr .bool → SqlExpr .bool → SqlExpr .bool
  | not     : SqlExpr .bool → SqlExpr .bool
  | field   : (t : SqlType) → (alias name : String) → SqlExpr t

/-- Explicit literal constructors, for positions where the expected type is not
yet known and coercions cannot fire (e.g. a literal on the left of `==.`). -/
def SqlExpr.int (i : Int) : SqlExpr .int := .intC i

/-- See `SqlExpr.int`. -/
def SqlExpr.str (s : String) : SqlExpr .string := .stringC s

/-- See `SqlExpr.int`. -/
def SqlExpr.bool (b : Bool) : SqlExpr .bool := .boolC b

end LeanLinq
