import LeanLinq.Core.Expr

/-! # Operator notation for `SqlExpr`

Arithmetic and concatenation reuse the standard `+`/`++` typeclasses.
Comparisons and logic cannot reuse `==`/`<`/`&&`/`||`/`!` (those return
`Bool`/`Prop`), so we mint dotted variants with matching precedences.

Coercions fire only against a known expected type, so put literals on the
*right* of an operator (`c["Name"] ==. "Alice"`); for the other order use the
explicit constructors (`SqlExpr.str "Alice" ==. c["Name"]`). -/

namespace LeanLinq

instance : Add (SqlExpr .int) := ⟨.plus⟩
instance : Append (SqlExpr .string) := ⟨.concat⟩

instance : OfNat (SqlExpr .int) n := ⟨.intC (Int.ofNat n)⟩
instance : Coe String (SqlExpr .string) := ⟨.stringC⟩
instance : Coe Bool (SqlExpr .bool) := ⟨.boolC⟩

/-- SQL equality: `a ==. b` compiles to `(a = b)`. -/
scoped infix:50  " ==. " => SqlExpr.eq
/-- SQL less-than: `a <. b` compiles to `(a < b)`. -/
scoped infix:50  " <. "  => SqlExpr.lt
/-- SQL conjunction: `a &&. b` compiles to `(a AND b)`. -/
scoped infixl:35 " &&. " => SqlExpr.and
/-- SQL disjunction: `a ||. b` compiles to `(a OR b)`. -/
scoped infixl:30 " ||. " => SqlExpr.or
/-- SQL negation: `!.a` compiles to `(NOT a)`. -/
scoped prefix:max "!."   => SqlExpr.not

/-- `a !=. b` is `NOT (a = b)`. -/
scoped notation:50 a:51 " !=. " b:51 => SqlExpr.not (SqlExpr.eq a b)

end LeanLinq
