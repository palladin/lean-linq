import LeanLinq.Core.Expr

/-! # Operator notation for `SqlExpr`

Arithmetic reuses the standard `+`/`-`/`*`/`/` typeclasses via
**flag-homogeneous** instances — mixed nullability meets through the
`widen` coercion, and instances exist only for the numeric SQL types, so
`string + string` stays a type error; concatenation is `++`.
Comparisons and logic cannot reuse `==`/`<`/`&&` (those return
`Bool`/`Prop`), so we mint dotted variants with matching precedences — the
constructors carry the flag arithmetic themselves.

Literal instances are **flag-polymorphic**: a numeric or string literal
lands at whatever nullability the position expects (strict by nature,
`widen`ed on demand), so `c["MiddleName"] ==. "x"` works when the column is
nullable. Coercions fire only against a known expected type, so put
literals on the *right* of a polymorphic operator
(`c["Name"] ==. "Alice"`); for the other order use the explicit
constructors (`SqlExpr.str`, `.int`, `.dec`, …). -/

namespace LeanLinq

/-- A never-NULL expression at whatever flag the position expects. -/
@[reducible] def SqlExpr.atFlag (n : Bool) (e : SqlExpr ts ⟨t, false⟩) :
    SqlExpr ts ⟨t, n⟩ :=
  match n with
  | false => e
  | true => .widen e

instance : Add (SqlExpr ts ⟨.int, n⟩) := ⟨.arith .add⟩
instance : Add (SqlExpr ts ⟨.long, n⟩) := ⟨.arith .add⟩
instance : Add (SqlExpr ts ⟨.double, n⟩) := ⟨.arith .add⟩
instance : Add (SqlExpr ts ⟨.decimal, n⟩) := ⟨.arith .add⟩
instance : Sub (SqlExpr ts ⟨.int, n⟩) := ⟨.arith .sub⟩
instance : Sub (SqlExpr ts ⟨.long, n⟩) := ⟨.arith .sub⟩
instance : Sub (SqlExpr ts ⟨.double, n⟩) := ⟨.arith .sub⟩
instance : Sub (SqlExpr ts ⟨.decimal, n⟩) := ⟨.arith .sub⟩
instance : Mul (SqlExpr ts ⟨.int, n⟩) := ⟨.arith .mul⟩
instance : Mul (SqlExpr ts ⟨.long, n⟩) := ⟨.arith .mul⟩
instance : Mul (SqlExpr ts ⟨.double, n⟩) := ⟨.arith .mul⟩
instance : Mul (SqlExpr ts ⟨.decimal, n⟩) := ⟨.arith .mul⟩
instance : Div (SqlExpr ts ⟨.int, n⟩) := ⟨.arith .div⟩
instance : Div (SqlExpr ts ⟨.long, n⟩) := ⟨.arith .div⟩
instance : Div (SqlExpr ts ⟨.double, n⟩) := ⟨.arith .div⟩
instance : Div (SqlExpr ts ⟨.decimal, n⟩) := ⟨.arith .div⟩

instance : Append (SqlExpr ts ⟨.string, n⟩) := ⟨.concat⟩

instance : OfNat (SqlExpr ts ⟨.int, n⟩) k := ⟨.atFlag n (.intC (Int.ofNat k))⟩
instance : OfNat (SqlExpr ts ⟨.long, n⟩) k := ⟨.atFlag n (.longC (Int.ofNat k))⟩
instance : Neg (SqlExpr ts ⟨.int, n⟩) := ⟨fun e => .arith .sub (.atFlag n (.intC 0)) e⟩

/-- Render a scientific literal (`99.99`) as exact decimal digits. -/
private def scientificDigits (m : Nat) (sign : Bool) (e : Nat) : String :=
  if !sign || e == 0 then toString m
  else
    let s := toString m
    let s := if s.length ≤ e then String.ofList (List.replicate (e + 1 - s.length) '0') ++ s else s
    let intPart := s.dropEnd e |>.toString
    let fracPart := s.takeEnd e |>.toString
    s!"{intPart}.{fracPart}"

instance : OfScientific (SqlExpr ts ⟨.decimal, n⟩) :=
  ⟨fun m sign e => .atFlag n (.decimalC (scientificDigits m sign e))⟩
instance : OfScientific (SqlExpr ts ⟨.double, n⟩) :=
  ⟨fun m sign e => .atFlag n (.doubleC (OfScientific.ofScientific m sign e))⟩

/- Two mono instances per literal coercion: the strict one wins when the
position leaves the flag free (the analogue of the numeric
`default_instance`), the widened one serves positions that pin the flag
nullable. -/
instance : Coe String (SqlExpr ts ⟨.string, true⟩) := ⟨fun s => .widen (.stringC s)⟩
instance : Coe Bool (SqlExpr ts ⟨.bool, true⟩) := ⟨fun b => .widen (.boolC b)⟩
instance (priority := high) : Coe String (SqlExpr ts ⟨.string, false⟩) := ⟨.stringC⟩
instance (priority := high) : Coe Bool (SqlExpr ts ⟨.bool, false⟩) := ⟨.boolC⟩

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
