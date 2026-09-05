import LeanLinq

/-! Scalar operations reject unsupported primitive types during elaboration,
including direct AST construction. SUBSTRING keeps a signed start but requires
a natural-number length; numeric functions preserve their input nullability. -/

namespace ScalarTyping
open LeanLinq

abbrev S : Schema := [("Text", .string), ("Number", .int)]
abbrev C : Ctx := { tables := [("scalar_typing", S)] }
def rows : Table "scalar_typing" S := ⟨⟩
def source := Query.from' (ts := C) rows

-- Check the constructor interfaces directly, with a numeric capability for an
-- otherwise unknown SQL type. The negative cases below check that it is needed.
example {ρ : Schema → Type} {c : SqlType} :
    ArithOp → [SqlNumeric c.ty] → SqlExprP ρ C c → SqlExprP ρ C c → SqlExprP ρ C c :=
  SqlExprP.arith
example {ρ : Schema → Type} {c : SqlType} [SqlNumeric c.ty] :
    SqlExprP ρ C c → SqlExprP ρ C c := SqlExprP.abs
example {ρ : Schema → Type} {c : SqlType} [SqlNumeric c.ty] :
    SqlExprP ρ C c → Int → SqlExprP ρ C c := SqlExprP.round
example {ρ : Schema → Type} {c : SqlType} [SqlNumeric c.ty] :
    SqlExprP ρ C c → SqlExprP ρ C c := SqlExprP.ceiling
example {ρ : Schema → Type} {c : SqlType} [SqlNumeric c.ty] :
    SqlExprP ρ C c → SqlExprP ρ C c := SqlExprP.floor
example {ρ : Schema → Type} {n : Bool} :
    SqlExprP ρ C ⟨.string, n⟩ → Int → Nat → SqlExprP ρ C ⟨.string, n⟩ :=
  SqlExprP.substring

private def numericCalls {t : SqlPrim} {n : Bool} [SqlNumeric t]
    (e : SqlExpr C ⟨t, n⟩) : List (SqlExpr C ⟨t, n⟩) :=
  [.arith .add e e, .arith .sub e e, .arith .mul e e, .arith .div e e,
    e.abs, e.round (-1), e.ceiling, e.floor]

-- Every numeric primitive works at either nullability flag. Negative ROUND
-- digits remain valid; only SUBSTRING's length is restricted to Nat.
example (n : Bool) (e : SqlExpr C ⟨.int, n⟩) : List (SqlExpr C ⟨.int, n⟩) :=
  [e + e, e - e, e * e, e / e] ++ numericCalls e
example (n : Bool) (e : SqlExpr C ⟨.long, n⟩) : List (SqlExpr C ⟨.long, n⟩) :=
  [e + e, e - e, e * e, e / e] ++ numericCalls e
example (n : Bool) (e : SqlExpr C ⟨.double, n⟩) : List (SqlExpr C ⟨.double, n⟩) :=
  [e + e, e - e, e * e, e / e] ++ numericCalls e
example (n : Bool) (e : SqlExpr C ⟨.decimal, n⟩) : List (SqlExpr C ⟨.decimal, n⟩) :=
  [e + e, e - e, e * e, e / e] ++ numericCalls e

-- Plain method calls reject each nonnumeric primitive.
#check_failure ((SqlExpr.str "abc" : SqlExpr C .string).abs)
#check_failure ((SqlExpr.bool true : SqlExpr C .bool).round 2)
#check_failure ((SqlExpr.dt "2026-01-01" : SqlExpr C .dateTime).ceiling)
#check_failure ((SqlExpr.gd "00000000-0000-0000-0000-000000000000" : SqlExpr C .guid).floor)

-- Calling a raw constructor cannot bypass the same constraints, including for
-- nullable values and arithmetic without the overloaded notation.
#check_failure (SqlExprP.abs (SqlExprP.stringC "abc") : SqlExpr C .string)
#check_failure (SqlExprP.round (SqlExprP.stringC "abc") 2 : SqlExpr C .string)
#check_failure (SqlExprP.ceiling (SqlExprP.stringC "abc") : SqlExpr C .string)
#check_failure (SqlExprP.floor (SqlExprP.stringC "abc") : SqlExpr C .string)
#check_failure (SqlExprP.abs (SqlExprP.nullC .string) : SqlExpr C (.null .string))
#check_failure (SqlExprP.arith .add (.stringC "a") (.stringC "b") : SqlExpr C .string)
#check_failure (SqlExprP.arith .sub (.stringC "a") (.stringC "b") : SqlExpr C .string)
#check_failure (SqlExprP.arith .mul (.stringC "a") (.stringC "b") : SqlExpr C .string)
#check_failure (SqlExprP.arith .div (.stringC "a") (.stringC "b") : SqlExpr C .string)

-- The errors also occur in ordinary query callbacks, before compilation.
#check_failure (source.select (fun r => ![r["Text"].abs.as "Bad"]))
#check_failure (source.select (fun r => ![(r["Text"].round 2).as "Bad"]))
#check_failure (source.select (fun r => ![(r["Text"].substring 1 (-1)).as "Bad"]))

-- Both a negative numeral and an already signed length must fail. The latter
-- also rules out an accidental implicit Int-to-Nat conversion.
#check_failure ((SqlExpr.str "abc" : SqlExpr C .string).substring 1 (-1))
#check_failure (SqlExprP.substring (.stringC "abc") 1 (-1) : SqlExpr C .string)
#check_failure (fun length : Int =>
  (SqlExprP.substring (.stringC "abc") 1 length : SqlExpr C .string))

-- Pin the intended diagnostics so parser or lookup failures cannot satisfy
-- these central rejection checks accidentally.
/--
error: failed to synthesize instance of type class
  SqlNumeric SqlType.string.ty

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : SqlExpr C .string := SqlExprP.abs (.stringC "abc")

/--
error: Application type mismatch: The argument
  -1
has type
  Int
but is expected to have type
  Nat
in the application
  (SqlExprP.stringC "abc").substring 1 (-1)
-/
#guard_msgs in
example : SqlExpr C .string := SqlExprP.substring (.stringC "abc") 1 (-1 : Int)

def acceptedProjection := source.select (fun r =>
  ![r["Number"].abs.as "Absolute", (r["Text"].substring (-2) 5).as "Prefix",
    (r["Text"].substring 1 0).as "Empty"])
def env : TableEnv C.tables := .cons [.cons "abcdef" (.cons (-4) .nil)] .nil

#guard (acceptedProjection.run env).toOption ==
  some [.cons 4 (.cons "ab" (.cons "" .nil))]

example (start : Int) (length : Nat) : SqlExpr C (.null .string) :=
  (SqlExprP.nullC .string).substring start length

end ScalarTyping
