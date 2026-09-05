import LeanLinq

/-! Independently specified evaluator edge cases: NULL membership,
EXISTS demand, string boundaries, and normalized date arithmetic. -/

open LeanLinq

namespace EvalRegressions

local instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

abbrev S : Schema := [("k", .int), ("v", .null .int)]
abbrev C : Ctx := { tables := [("eval_rows", S)] }
def rowsTable : Table "eval_rows" S := ⟨⟩
def env : TableEnv C.tables := .cons
  [.cons 1 (.cons none .nil), .cons 2 (.cons (some 2) .nil),
   .cons 2 (.cons (some 2) .nil)] .nil
def ee : EvalEnv C := ⟨env, .nil, none⟩
def base := Query.from' (ts := C) rowsTable
def valuesQ := base.select (fun r => ![r["v"].as "v"])

private def boolResult (e : SqlExpr C ⟨.bool, n⟩) := e.evalG ee [[]]

#guard boolResult ((SqlExprP.nullC .int).inQuery (valuesQ.limit 0)) == .ok (some false)
#guard boolResult ((SqlExprP.nullC .int).notInQuery (valuesQ.limit 0)) == .ok (some true)
#guard boolResult ((SqlExprP.nullC .int).inQuery valuesQ) == .ok none
#guard boolResult ((SqlExpr.int 2).inQuery valuesQ) == .ok (some true)
#guard boolResult ((SqlExpr.int 3).inQuery valuesQ) == .ok none

def badProjection : Query C [("bad", .int)] := base.select fun _ =>
  ![((SqlExpr.int 1 : SqlExprP _ C .int) / SqlExpr.int 0).as "bad"]
def duplicateValues : Query C [("value", .int)] := base.select fun _ =>
  ![(SqlExpr.int 1).as "value"]
def otherValues : Query C [("value", .int)] := base.select fun _ =>
  ![(SqlExpr.int 2).as "value"]
def badOrdering := base.orderBy fun _ =>
  [((SqlExpr.int 1 : SqlExprP _ C .int) / SqlExpr.int 0).asc]

#guard boolResult (SqlExpr.exists' badProjection) == .ok (some true)
#guard boolResult (SqlExpr.notExists badProjection) == .ok (some false)
#guard boolResult (SqlExpr.exists' badOrdering) == .ok (some true)
#guard boolResult (SqlExpr.exists' (badProjection.limit 0)) == .ok (some false)
#guard boolResult (SqlExpr.exists' (badProjection.limit 1)) == .ok (some true)
#guard boolResult (SqlExpr.exists' (badProjection.offset 3)) == .ok (some false)
#guard boolResult (SqlExpr.exists' (badProjection.offset 2)) == .ok (some true)
#guard boolResult (SqlExpr.exists' badProjection.distinct) == .ok (some true)
#guard boolResult (SqlExpr.exists' (duplicateValues.distinct.offset 1)) == .ok (some false)
#guard boolResult (SqlExpr.exists' ((duplicateValues.union otherValues).offset 1)) == .ok (some true)
#guard boolResult (SqlExpr.exists' ((duplicateValues.union otherValues).offset 2)) == .ok (some false)
#guard boolResult (SqlExpr.exists' (duplicateValues.intersect otherValues)) == .ok (some false)
#guard boolResult (SqlExpr.exists' (duplicateValues.except duplicateValues)) == .ok (some false)
#guard boolResult (SqlExpr.exists' (duplicateValues.except otherValues)) == .ok (some true)
#guard (badProjection.limit 0).run env == .ok []

def groupedBad := base.groupBy (fun r => ![r["k"].as "k"])
  |>.select (fun _ _ => ![(GroupExprP.int 1 / GroupExprP.int 0).as "bad"])
def noGroups := base.groupBy (fun r => ![r["k"].as "k"])
  |>.having (fun _ a => a.count >. 99)
  |>.select (fun _ _ => ![(GroupExprP.int 1 / GroupExprP.int 0).as "bad"])

#guard boolResult (SqlExpr.exists' groupedBad) == .ok (some true)
#guard boolResult (SqlExpr.exists' noGroups) == .ok (some false)
#guard boolResult (SqlExpr.exists' (groupedBad.offset 2)) == .ok (some false)

#guard (SqlExpr.str "  \t foo \n  " : SqlExpr C .string).trim.evalG ee [[]] ==
  .ok (some "\t foo \n")
#guard sqlTrim "   " == ""
#guard sqlSubstring "abcdef" 0 3 == "ab"
#guard sqlSubstring "abcdef" (-2) 3 == ""
#guard sqlSubstring "abcdef" (-2) 5 == "ab"
#guard sqlSubstring "abcdef" 2 3 == "bcd"
#guard ((SqlExpr.str "abcdef" : SqlExpr C .string).substring 1 (-1)).evalG ee [[]] ==
  .error (.invalidStatement "negative SUBSTRING length")
#guard dateAddDays "0001-01-01 00:00:00" 0 == "0001-01-01 00:00:00"
#guard dateAddYears "1000-01-01 12:34:56" (-1) == "0999-01-01 12:34:56"
#guard dateAddMonths "0999-12-31 12:34:56" 1 == "1000-01-31 12:34:56"

end EvalRegressions
