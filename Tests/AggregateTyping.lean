import LeanLinq

/-! Aggregate operators carry the primitive type of their input. SUM and AVG
need numeric evidence even through the raw AST; MIN and MAX retain their
existing support for nonnumeric values and SQL NULL/empty-input behavior. -/

namespace AggregateTyping
open LeanLinq

abbrev S : Schema := [("Bucket", .int), ("Text", .null .string)]
abbrev C : Ctx := { tables := [("aggregate_typing", S)] }
def rows : Table "aggregate_typing" S := ⟨⟩
def source := Query.from' (ts := C) rows

-- The operator itself cannot be built with a nonnumeric SUM/AVG input.
#check_failure (Aggregate.sum : Aggregate .string)
#check_failure (Aggregate.avg : Aggregate .string)
#check_failure (Aggregate.sum : Aggregate .bool)
#check_failure (Aggregate.avg : Aggregate .bool)
#check_failure (Aggregate.sum : Aggregate .dateTime)
#check_failure (Aggregate.avg : Aggregate .dateTime)
#check_failure (Aggregate.sum : Aggregate .guid)
#check_failure (Aggregate.avg : Aggregate .guid)

example {t : SqlPrim} [SqlNumeric t] : Aggregate t := .sum
example {t : SqlPrim} [SqlNumeric t] : Aggregate t := .avg
example {t : SqlPrim} : Aggregate t := .min
example {t : SqlPrim} : Aggregate t := .max

-- Pin both raw node signatures: their operator has exactly the operand's
-- primitive, and every aggregate result remains nullable.
example {ρ : Schema → Type} {ks : Schema} {t : SqlPrim} {n : Bool} :
    Aggregate t → SqlExprP ρ C ⟨t, n⟩ → GroupedExprP ρ C ks ⟨t, true⟩ := GroupedExprP.aggE
example {ρ : Schema → Type} {t : SqlPrim} {n : Bool} :
    Aggregate t → SpineQP ρ C .plain [("Value", ⟨t, n⟩)] → ScalarQueryP ρ C ⟨t, true⟩ :=
  ScalarQueryP.aggQ

-- Input mode also traverses intervening sources with several columns. The
-- aggregate's singleton input and primitive linkage remain in aggQ itself.
example {s : Schema} : SelSpec s := .inputSel
#check_failure (ScalarQueryP.aggQ .sum
  (.yield (RowP.nil : RowP AliasOf C [])) : ScalarQueryP AliasOf C (.null .int))
#check_failure (ScalarQueryP.aggQ .sum
  (.yield (.cons (.intC 1) (.cons (.intC 2) .nil)) :
    SpineQP AliasOf C .plain [("First", .int), ("Second", .int)]) :
  ScalarQueryP AliasOf C (.null .int))

private def numericNodes {t : SqlPrim} {n : Bool} [SqlNumeric t]
    (e : SqlExpr C ⟨t, n⟩) (sp : SpineQP AliasOf C .plain [("Value", ⟨t, n⟩)]) :
    List (GroupedExprP AliasOf C [] ⟨t, true⟩) × List (ScalarQueryP AliasOf C ⟨t, true⟩) :=
  ([.aggE .sum e, .aggE .avg e, .aggE .min e, .aggE .max e],
   [.aggQ .sum sp, .aggQ .avg sp, .aggQ .min sp, .aggQ .max sp])

-- All four numeric primitives work with either strict or nullable input.
example (n : Bool) (e : SqlExpr C ⟨.int, n⟩)
    (sp : SpineQP AliasOf C .plain [("Value", ⟨.int, n⟩)]) := numericNodes e sp
example (n : Bool) (e : SqlExpr C ⟨.long, n⟩)
    (sp : SpineQP AliasOf C .plain [("Value", ⟨.long, n⟩)]) := numericNodes e sp
example (n : Bool) (e : SqlExpr C ⟨.double, n⟩)
    (sp : SpineQP AliasOf C .plain [("Value", ⟨.double, n⟩)]) := numericNodes e sp
example (n : Bool) (e : SqlExpr C ⟨.decimal, n⟩)
    (sp : SpineQP AliasOf C .plain [("Value", ⟨.decimal, n⟩)]) := numericNodes e sp

-- Raw grouped-expression construction must reject both SUM and AVG, whether
-- the operand is a strict literal or a nullable expression.
#check_failure (GroupedExprP.aggE .sum (.stringC "abc") : GroupedExprP AliasOf C [] (.null .string))
#check_failure (GroupedExprP.aggE .avg (.stringC "abc") : GroupedExprP AliasOf C [] (.null .string))
#check_failure (GroupedExprP.aggE .sum (.nullC .string) : GroupedExprP AliasOf C [] (.null .string))
#check_failure (GroupedExprP.aggE .avg (.nullC .bool) : GroupedExprP AliasOf C [] (.null .bool))

private def rawText : SpineQP AliasOf C .plain [("Value", .string)] :=
  .yield (.cons (.stringC "abc") .nil)
private def rawNullText : SpineQP AliasOf C .plain [("Value", .null .string)] :=
  .yield (.cons (.nullC .string) .nil)

-- The scalar-query constructor enforces the same boundary independently of
-- the public Query.sum/avg helpers.
#check_failure (ScalarQueryP.aggQ .sum rawText : ScalarQueryP AliasOf C (.null .string))
#check_failure (ScalarQueryP.aggQ .avg rawText : ScalarQueryP AliasOf C (.null .string))
#check_failure (ScalarQueryP.aggQ .sum rawNullText : ScalarQueryP AliasOf C (.null .string))
#check_failure (ScalarQueryP.aggQ .avg rawNullText : ScalarQueryP AliasOf C (.null .string))

-- Empty data cannot bypass the numeric constraint at the evaluator boundary.
#check_failure (SqlPrim.aggV .string .sum [])
#check_failure (SqlPrim.aggV .string .avg [])

-- Pin the intended error for each raw AST path, rather than accepting an
-- unrelated parser or name-resolution failure.
/--
error: failed to synthesize instance of type class
  SqlNumeric SqlPrim.string

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : GroupedExprP AliasOf C [] (.null .string) := .aggE .sum (.stringC "abc")

/--
error: failed to synthesize instance of type class
  SqlNumeric SqlPrim.string

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : ScalarQueryP AliasOf C (.null .string) := .aggQ .avg rawText

def texts := source.select (fun r => ![r["Text"].as "Value"])
def nullTexts := (source.where' (fun r => r["Bucket"] ==. 2))
  |>.select (fun r => ![r["Text"].as "Value"])
def textExtrema := source.groupBy (fun r => ![r["Bucket"].as "Bucket"])
  |>.select (fun keys a => ![keys["Bucket"].as "Bucket",
    (a.min (fun r => r["Text"])).as "Minimum", (a.max (fun r => r["Text"])).as "Maximum"])

def env : TableEnv C.tables := .cons [
  .cons 1 (.cons (some "zeta") .nil), .cons 1 (.cons none .nil),
  .cons 1 (.cons (some "alpha") .nil), .cons 2 (.cons none .nil)] .nil

-- MIN/MAX ignore NULL values, return NULL when no values remain, and retain
-- text ordering. These expected results do not inspect the AST implementation.
#guard (texts.min.run env).toOption == some (some "alpha")
#guard (texts.max.run env).toOption == some (some "zeta")
#guard ((texts.limit 0).min.run env).toOption == some none
#guard ((texts.limit 0).max.run env).toOption == some none
#guard (nullTexts.min.run env).toOption == some none
#guard (nullTexts.max.run env).toOption == some none
#guard (textExtrema.run env).toOption == some [
  .cons 1 (.cons (some "alpha") (.cons (some "zeta") .nil)),
  .cons 2 (.cons none (.cons none .nil))]

end AggregateTyping
