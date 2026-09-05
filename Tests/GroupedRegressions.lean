import Tests.CompilerRegressions

/-! Invalid grouped expressions are rejected while Lean builds the query.
Named keys expose only their declared schema; aggregate operands use ordinary
row selectors, and each grouped callback has its own expression phase. -/

namespace GroupedRegressions
open LeanLinq

abbrev C := CompilerRegressions.C
def source := CompilerRegressions.source
def items := CompilerRegressions.items
def grouped := source.groupBy (fun r => ![r["Bucket"].as "Bucket"])

-- The ordinary-expression representation is not part of the grouped API.
#check_failure GroupExprP.mk
#check_failure GroupExprP.raw
#check_failure GroupRowP.mk
#check_failure GroupRowP.raw
#check_failure GroupAggP.mk
#check_failure GroupAggP.source
#check_failure GroupAggregateP.mk
#check_failure (fun e : SqlExpr C .int => (⟨e⟩ : GroupExprP Unit AliasOf C [] .int))
#check_failure (fun e : SqlExpr C .int => ({ raw := e } : GroupExprP Unit AliasOf C [] .int))

-- SELECT, HAVING, and ORDER BY cannot look up a field absent from the key row.
#check_failure (grouped.select (fun keys _ => ![keys["Id"].as "Id"]))
#check_failure (grouped.having (fun keys _ => keys["Id"] >. 0))
#check_failure (grouped.orderBy (fun keys _ => [keys["Id"].asc]))
#check_failure (grouped.select (fun keys _ => ![(keys["Id"].abs + 1).as "Id"]))

-- A computed key provides its result under a name, not its input columns.
#check_failure ((source.groupBy (fun r => ![(r["Id"] + r["Bucket"]).as "Combined"]))
  |>.select (fun keys _ => ![keys["Id"].as "Id"]))

-- Ordinary SQL expressions/rows do not implicitly become grouped expressions.
#check_failure (grouped.select (fun _ _ => ![(SqlExpr.int 1).as "Raw"]))
#check_failure (grouped.select (fun _ _ =>
  (RowP.cons (SqlExpr.int 1) RowP.nil : RowP _ C [("Raw", .int)])))

-- Aggregate input is a selector over ordinary rows. A grouped key or aggregate
-- cannot be smuggled into its operand, and aggregate calls cannot be nested.
#check_failure (grouped.select (fun keys a => ![(a.sum keys["Bucket"]).as "Sum"]))
#check_failure (grouped.select (fun keys a => ![(a.sum (fun _ => keys["Bucket"])).as "Sum"]))
#check_failure (grouped.select (fun _ a =>
  ![(a.sum (fun _ => a.sum (fun r => r["Id"]))).as "Sum"]))

-- Grouped SUBSTRING requires a natural-number length at construction time.
#check_failure (grouped.select (fun _ _ =>
  ![((GroupExprP.str "abc" : GroupExprP _ _ C _ .string).substring 1 (-1)).as "Text"]))

-- Pin the intended type errors as well as merely requiring failure: a parser
-- error or a renamed API must not make these central safety tests pass.
/--
error: failed to synthesize instance of type class
  HasCol [("Bucket", SqlType.int)] "Id" SqlType.int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Query C [("Id", .int)] :=
  grouped.select (fun keys _ => ![(keys.col (c := .int) "Id").as "Id"])

/--
error: Type mismatch
  a.sum fun r => r.col "Id"
has type
  GroupExprP κ✝ ρ✝ CompilerRegressions.C [("Bucket", SqlType.int)] { ty := SqlPrim.int, nullable := true }
but is expected to have type
  SqlExprP ρ✝ CompilerRegressions.C { ty := SqlPrim.int, nullable := true }
-/
#guard_msgs in
example : Query C [("Sum", .null .int)] := grouped.select (fun _ a =>
  ![(a.sum (n := true) (fun _ => a.sum (fun r => r["Id"]))).as "Sum"])

-- A grouped expression cannot be used in an ordinary WHERE predicate.
#check_failure (grouped.select (fun _ a =>
  let _ := source.where' (fun _ => a.count >. 0)
  ![a.count.as "Count"]))

-- The phase variable also distinguishes two grouped callbacks on the same
-- source: an inner projection cannot combine its aggregate with an outer one.
#check_failure (grouped.select (fun _ outer =>
  let _ := grouped.select (fun _ inner => ![(outer.count + inner.count).as "Count"])
  ![outer.count.as "Count"]))

-- Comprehensions retain ordinary row variables for aggregate operands only.
#check_failure (query! {
  from r in items
  groupBy ![r["Bucket"].as "Bucket"] into keys, a
  select ![r["Id"].as "Id"]
} : Query C _)
#check_failure (query! {
  from r in items
  groupBy ![r["Bucket"].as "Bucket"] into keys, a
  having r["Id"] >. 0
  select ![keys["Bucket"].as "Bucket"]
} : Query C _)
#check_failure (query! {
  from r in items
  groupBy ![r["Bucket"].as "Bucket"] into keys, a
  orderBy r["Id"].asc
  select ![keys["Bucket"].as "Bucket"]
} : Query C _)

def keyExpressions := grouped
  |>.having (fun keys _ => keys["Bucket"] >. 0)
  |>.orderBy (fun keys a => [(a.sum (fun r => r["Id"])).desc, keys["Bucket"].asc])
  |>.select (fun keys a => ![(keys["Bucket"] + 1).as "Next", (a.sum (fun r => r["Id"])).as "Sum"])

def computedKey := source.groupBy (fun r => ![(r["Id"] + r["Bucket"]).as "Combined"])
  |>.select (fun keys _ => ![keys["Combined"].as "Combined"])

-- Literals in the key are compiled once; subsequent key references must reuse
-- their parameter identity as well as their value (notably on PostgreSQL).
def computedLiteralKey := source.groupBy (fun r => ![(r["Bucket"] + 1).as "Next"])
  |>.select (fun keys _ => ![keys["Next"].as "Next"])

def computedKeyAggregate := source.groupBy (fun r => ![(r["Bucket"] + 1).as "Next"])
  |>.having (fun keys a => a.sum (fun r => r["Id"]) >. 1 &&. keys["Next"] >=. 2)
  |>.orderBy (fun keys a => [(a.sum (fun r => r["Id"])).desc, keys["Next"].asc])
  |>.select (fun keys a => ![keys["Next"].as "Next", (a.sum (fun r => r["Id"])).as "Sum"])

def computedKeyCountOnly := source.groupBy (fun r => ![(r["Bucket"] + 1).as "Next"])
  |>.select (fun _ a => ![a.count.as "Count"])

def computedKeyCase := source.groupBy (fun r => ![(r["Bucket"] + 1).as "Next"])
  |>.select (fun keys _ =>
    ![(GroupExprP.caseWhen (keys["Next"] >. 2)
        (keys["Next"] * 2).anyNull (keys["Next"] + 1).anyNull).as "Adjusted",
      (keys["Next"] + 10).as "PlusTen"])

def constantKey := source.groupBy (fun _ => ![(SqlExpr.int 1).as "One"])
  |>.select (fun keys a => ![keys["One"].as "One", a.count.as "Count"])

def emptyConstantKey := (source.limit 0).groupBy (fun _ => ![(SqlExpr.int 1).as "One"])
  |>.select (fun keys a => ![keys["One"].as "One", a.count.as "Count"])

def predicateKey := source.groupBy (fun r => ![(r["Value"] >. 1).as "Positive"])
  |>.select (fun keys a => ![keys["Positive"].as "Positive", a.count.as "Count"])

def nonkeyAggregates := grouped
  |>.select (fun keys a => ![keys["Bucket"].as "Bucket",
    (a.sum (fun r => r["Id"])).as "Sum", (a.max (fun r => r["Value"])).as "Maximum"])

def groupedLiterals := grouped.select (fun _ _ =>
  ![(GroupExprP.int 7).as "Integer", (GroupExprP.str "fixed").as "Text"])

def groupedSubstring := grouped.select (fun _ _ =>
  ![((GroupExprP.str "abc" : GroupExprP _ _ C _ .string).substring 1 2).as "Text"])

abbrev ParamC : Ctx := { tables := C.tables, params := [("offset", .int)] }
def parameterExpression := (Query.from' (ts := ParamC) items)
  |>.groupBy (fun r => ![r["Bucket"].as "Bucket"])
  |>.select (fun keys _ =>
    ![(keys["Bucket"] + GroupExprP.param (ts := ParamC) "offset").as "Shifted"])

def comprehension := (query! {
  from r in items
  groupBy ![r["Bucket"].as "Bucket"] into keys, a
  having a.count >. 0
  orderBy keys["Bucket"].asc
  select ![keys["Bucket"].as "Bucket", (a.sum r["Id"]).as "Sum"]
} : Query C _)

-- Successful construction and independently specified in-memory results pin
-- the accepted API; server runners can execute these exported fixtures too.
#guard (keyExpressions.run CompilerRegressions.env).toOption == some [
  .cons 2 (.cons (some 3) .nil), .cons 3 (.cons (some 3) .nil)]
#guard (computedKey.run CompilerRegressions.env).toOption ==
  some [.cons 2 .nil, .cons 3 .nil, .cons 5 .nil]
#guard (computedLiteralKey.run CompilerRegressions.env).toOption == some [.cons 2 .nil, .cons 3 .nil]
#guard (computedKeyAggregate.run CompilerRegressions.env).toOption == some [
  .cons 2 (.cons (some 3) .nil), .cons 3 (.cons (some 3) .nil)]
#guard (computedKeyCountOnly.run CompilerRegressions.env).toOption ==
  some [.cons (some 2) .nil, .cons (some 1) .nil]
#guard (computedKeyCase.run CompilerRegressions.env).toOption == some [
  .cons (some 3) (.cons 12 .nil), .cons (some 6) (.cons 13 .nil)]
#guard (constantKey.run CompilerRegressions.env).toOption == some [.cons 1 (.cons (some 3) .nil)]
#guard (emptyConstantKey.run CompilerRegressions.env).toOption == some []
#guard (predicateKey.run CompilerRegressions.env).toOption == some [
  .cons none (.cons (some 1) .nil), .cons (some false) (.cons (some 1) .nil),
  .cons (some true) (.cons (some 1) .nil)]
#guard (nonkeyAggregates.run CompilerRegressions.env).toOption == some [
  .cons 1 (.cons (some 3) (.cons (some 0) .nil)),
  .cons 2 (.cons (some 3) (.cons (some 2) .nil))]
#guard (groupedLiterals.run CompilerRegressions.env).toOption == some [
  .cons 7 (.cons "fixed" .nil), .cons 7 (.cons "fixed" .nil)]
#guard (groupedSubstring.run CompilerRegressions.env).toOption ==
  some [.cons "ab" .nil, .cons "ab" .nil]
#guard (parameterExpression.run CompilerRegressions.env (.cons 10 .nil)).toOption ==
  some [.cons 11 .nil, .cons 12 .nil]
#guard (comprehension.run CompilerRegressions.env).toOption == some [
  .cons 1 (.cons (some 3) .nil), .cons 2 (.cons (some 3) .nil)]

end GroupedRegressions
