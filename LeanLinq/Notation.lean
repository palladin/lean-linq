import LeanLinq.Core.Expr

/-! # Operator notation for `SqlExpr`

Arithmetic reuses the standard `+`/`-`/`*`/`/` typeclasses (instances only
for the numeric SQL types, so `string + string` stays a type error);
concatenation is `++`. Comparisons and logic cannot reuse `==`/`<`/`&&`
(those return `Bool`/`Prop`), so we mint dotted variants with matching
precedences.

Coercions fire only against a known expected type, so put literals on the
*right* of a polymorphic operator (`c["Name"] ==. "Alice"`); for the other
order use the explicit constructors (`SqlExpr.str`, `.int`, `.dec`, …). -/

namespace LeanLinq

instance : Add (SqlExpr .int) := ⟨.arith .add⟩
instance : Add (SqlExpr .long) := ⟨.arith .add⟩
instance : Add (SqlExpr .double) := ⟨.arith .add⟩
instance : Add (SqlExpr .decimal) := ⟨.arith .add⟩
instance : Sub (SqlExpr .int) := ⟨.arith .sub⟩
instance : Sub (SqlExpr .long) := ⟨.arith .sub⟩
instance : Sub (SqlExpr .double) := ⟨.arith .sub⟩
instance : Sub (SqlExpr .decimal) := ⟨.arith .sub⟩
instance : Mul (SqlExpr .int) := ⟨.arith .mul⟩
instance : Mul (SqlExpr .long) := ⟨.arith .mul⟩
instance : Mul (SqlExpr .double) := ⟨.arith .mul⟩
instance : Mul (SqlExpr .decimal) := ⟨.arith .mul⟩
instance : Div (SqlExpr .int) := ⟨.arith .div⟩
instance : Div (SqlExpr .long) := ⟨.arith .div⟩
instance : Div (SqlExpr .double) := ⟨.arith .div⟩
instance : Div (SqlExpr .decimal) := ⟨.arith .div⟩

instance : Append (SqlExpr .string) := ⟨.concat⟩

instance : OfNat (SqlExpr .int) n := ⟨.intC (Int.ofNat n)⟩
instance : OfNat (SqlExpr .long) n := ⟨.longC (Int.ofNat n)⟩
instance : Neg (SqlExpr .int) := ⟨fun e => .arith .sub (.intC 0) e⟩

/-- Render a scientific literal (`99.99`) as exact decimal digits. -/
private def scientificDigits (m : Nat) (sign : Bool) (e : Nat) : String :=
  if !sign || e == 0 then toString m
  else
    let s := toString m
    let s := if s.length ≤ e then String.ofList (List.replicate (e + 1 - s.length) '0') ++ s else s
    let intPart := s.dropEnd e |>.toString
    let fracPart := s.takeEnd e |>.toString
    s!"{intPart}.{fracPart}"

instance : OfScientific (SqlExpr .decimal) :=
  ⟨fun m sign e => .decimalC (scientificDigits m sign e)⟩
instance : OfScientific (SqlExpr .double) :=
  ⟨fun m sign e => .doubleC (OfScientific.ofScientific m sign e)⟩

instance : Coe String (SqlExpr .string) := ⟨.stringC⟩
instance : Coe Bool (SqlExpr .bool) := ⟨.boolC⟩

/-- SQL equality: `a ==. b` compiles to `(a = b)`. -/
scoped infix:50  " ==. " => SqlExpr.cmp CmpOp.eq
/-- SQL inequality: `a !=. b` compiles to `(a <> b)`. -/
scoped infix:50  " !=. " => SqlExpr.cmp CmpOp.ne
/-- SQL less-than: `a <. b` compiles to `(a < b)`. -/
scoped infix:50  " <. "  => SqlExpr.cmp CmpOp.lt
/-- SQL less-or-equal. -/
scoped infix:50  " <=. " => SqlExpr.cmp CmpOp.le
/-- SQL greater-than. -/
scoped infix:50  " >. "  => SqlExpr.cmp CmpOp.gt
/-- SQL greater-or-equal. -/
scoped infix:50  " >=. " => SqlExpr.cmp CmpOp.ge
/-- SQL conjunction: `a &&. b` compiles to `(a AND b)`. -/
scoped infixl:35 " &&. " => SqlExpr.and
/-- SQL disjunction: `a ||. b` compiles to `(a OR b)`. -/
scoped infixl:30 " ||. " => SqlExpr.or
/-- SQL negation: `!.a` compiles to `(NOT a)`. -/
scoped prefix:max "!."   => SqlExpr.not

end LeanLinq
