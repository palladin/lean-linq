import LeanLinq

/-! Aggregate inputs may refer to the row being updated or deleted. The target
and inner source deliberately share `Id`; native compilation must preserve the
target binding through every projection and nested query. -/

namespace AggregateDml
open LeanLinq

abbrev TargetS : Schema := [("Id", .int), ("Value", .null .int)]
abbrev InnerS : Schema := [("Id", .int)]
abbrev C : Ctx := { tables := [
  ("aggregate_dml_target", TargetS), ("aggregate_dml_inner", InnerS)] }

def target : Table "aggregate_dml_target" TargetS := ⟨⟩
def inner : Table "aggregate_dml_inner" InnerS := ⟨⟩
def targetRows : List (Values TargetS) := [
  .cons 10 (.cons (some 0) .nil), .cons 20 (.cons (some 0) .nil)]
def innerRows : List (Values InnerS) := [.cons 1 .nil, .cons 2 .nil]
def seed : TableEnv C.tables := .cons targetRows (.cons innerRows .nil)

def expectedUpdated : List (Values TargetS) := [
  .cons 10 (.cons (some 20) .nil), .cons 20 (.cons (some 40) .nil)]
def expectedRemaining : List (Values TargetS) := [.cons 10 (.cons (some 0) .nil)]
def expectedNulls : List (Values TargetS) := [
  .cons 10 (.cons none .nil), .cons 20 (.cons none .nil)]

def targetQuery : Query C TargetS :=
  Query.from' (ts := C) target |>.orderBy (fun row => [row["Id"].asc])

private def capturedSum (row : Row C TargetS) : SqlExpr C (.null .int) :=
  ((QueryP.from' (ts := C) inner
    |>.select (fun _ => ![row["Id"].as "Input"])).sum).embed

private def hiddenSum (row : Row C TargetS) : SqlExpr C (.null .int) :=
  ((QueryP.from' (ts := C) inner |>.select (fun input =>
    ![(SqlExpr.caseWhen (SqlExpr.exists' (QueryP.from' (ts := C) inner
      |>.where' (fun nested => nested["Id"] ==. input["Id"] &&. nested["Id"] <. row["Id"])))
      row["Id"].anyNull (SqlExpr.int 0)).as "Input"])).sum).embed

private def groupedSum (row : Row C TargetS) : SqlExpr C (.null .int) :=
  ((QueryP.from' (ts := C) inner
    |>.groupBy (fun _ => ![(SqlExpr.int 1).as "Bucket"])
    |>.select (fun _ a => ![(a.sum (fun _ => row["Id"])).as "Input"])).sum).embed

def updateScalar : UpdateStmt C "aggregate_dml_target" TargetS :=
  target.update |>.setWith "Value" capturedSum |>.where' (fun row => row["Id"] >. 0)
def updateGrouped : UpdateStmt C "aggregate_dml_target" TargetS :=
  target.update |>.setWith "Value" groupedSum
def updateHidden : UpdateStmt C "aggregate_dml_target" TargetS :=
  target.update |>.setWith "Value" hiddenSum
def updateEmptyInput : UpdateStmt C "aggregate_dml_target" TargetS :=
  target.update |>.setWith "Value" (fun row =>
    ((QueryP.from' (ts := C) inner |>.limit 0
      |>.select (fun _ => ![row["Id"].as "Input"])).sum).embed)

-- Statement callbacks have a concrete AliasOf representation and can inspect
-- their target marker. The evaluator must supply the compiler's same binding.
def updateObservesAlias : UpdateStmt C "aggregate_dml_target" TargetS :=
  target.update |>.setWith "Value" (fun row =>
    (match row["Id"] with
      | .field _ atom _ => if atom.alias == "a0" then row["Id"] * 2 else row["Id"]
      | _ => SqlExpr.int (-1) : SqlExpr C .int))

def deleteScalar : DeleteStmt C "aggregate_dml_target" TargetS :=
  target.delete |>.where' (fun row => capturedSum row >. 30)
def deleteHidden : DeleteStmt C "aggregate_dml_target" TargetS :=
  target.delete |>.where' (fun row => hiddenSum row >. 30)
def deleteGrouped : DeleteStmt C "aggregate_dml_target" TargetS :=
  target.delete |>.where' (fun row => SqlExpr.exists' (
    QueryP.from' (ts := C) inner
      |>.groupBy (fun _ => ![(SqlExpr.int 1).as "Bucket"])
      |>.having (fun _ a => a.sum (fun _ => row["Id"]) >. 30)
      |>.select (fun _ a => ![a.count.as "Count"])))
def deleteObservesAlias : DeleteStmt C "aggregate_dml_target" TargetS :=
  target.delete |>.where' (fun row =>
    match row["Id"] with
    | .field _ atom _ => if atom.alias == "a0" then row["Id"] >. 15 else row["Id"] >. 5
    | _ => row["Id"] >. 0)

def updateCases : List (String × UpdateStmt C "aggregate_dml_target" TargetS × List (Values TargetS)) := [
  ("scalar", updateScalar, expectedUpdated),
  ("grouped", updateGrouped, expectedUpdated),
  ("hidden", updateHidden, expectedUpdated),
  ("empty input", updateEmptyInput, expectedNulls),
  ("observed target alias", updateObservesAlias, expectedUpdated)]
def deleteCases : List (String × DeleteStmt C "aggregate_dml_target" TargetS × List (Values TargetS)) := [
  ("scalar", deleteScalar, expectedRemaining),
  ("grouped", deleteGrouped, expectedRemaining),
  ("hidden", deleteHidden, expectedRemaining),
  ("observed target alias", deleteObservesAlias, expectedRemaining)]

private def targetState (env : TableEnv C.tables) : List (Values TargetS) :=
  match env with | .cons rows _ => rows

-- Both interpretations rebuild callbacks with the same target marker, including
-- callbacks that inspect its alias rather than only using it in expressions.
#guard updateCases.all fun (_, statement, expected) =>
  match statement.applyCount seed with
  | .ok (env, affected) => affected == 2 && targetState env == expected
  | .error _ => false
#guard deleteCases.all fun (_, statement, expected) =>
  match statement.applyCount seed with
  | .ok (env, affected) => affected == 1 && targetState env == expected
  | .error _ => false

#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  updateCases.all (fun (_, statement, _) => (statement.toSqlChecked db).isOk) &&
  deleteCases.all (fun (_, statement, _) => (statement.toSqlChecked db).isOk)

-- A table whose name resembles generated aliases must not become the binding
-- used for a nested source. The target reserves a0; source aliases start at a1.
abbrev AliasC : Ctx := { tables := [("a0", TargetS), ("aggregate_dml_inner", InnerS)] }
def aliasNamedTarget : Table "a0" TargetS := ⟨⟩
def updateAliasNamedTarget : UpdateStmt AliasC "a0" TargetS :=
  aliasNamedTarget.update |>.setWith "Value" (fun row =>
    ((QueryP.from' (ts := AliasC) inner
      |>.select (fun _ => ![row["Id"].as "Input"])).sum).embed)
#guard (updateAliasNamedTarget.applyCount (.cons targetRows (.cons innerRows .nil))).toOption.map
  (fun (env, affected) => match env with | .cons rows _ => (rows, affected)) ==
    some (expectedUpdated, 2)
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  (updateAliasNamedTarget.toSqlChecked db).isOk

end AggregateDml
