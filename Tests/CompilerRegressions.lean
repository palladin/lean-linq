import LeanLinq

/-! Regression queries with independently specified SQL and validation results.
The SQLite driver tests also execute the exported query values. -/

namespace CompilerRegressions
open LeanLinq

abbrev S : Schema := [("Id", .int), ("Bucket", .int), ("Value", .null .int)]
abbrev C : Ctx := { tables := [("compiler_items", S)] }
def items : Table "compiler_items" S := ⟨⟩
def source := Query.from' (ts := C) items
def env : TableEnv C.tables := .cons [
  .cons 1 (.cons 1 (.cons none .nil)),
  .cons 2 (.cons 1 (.cons (some 0) .nil)),
  .cons 3 (.cons 2 (.cons (some 2) .nil))] .nil

def grouped := source.groupBy (fun r => ![r["Bucket"].as "Bucket"])
  |>.orderBy (fun r _ => [r["Bucket"].asc])
  |>.select (fun r a => ![r["Bucket"].as "Bucket", a.count.as "Count"])
def groupedUnion := grouped.union grouped
def emptyOrder := source.orderBy (fun _ => [])

#guard (groupedUnion.toSqlChecked).isOk
#guard (groupedUnion.toSql.sql.splitOn "ORDER BY").length == 1
#guard (groupedUnion.run env).toOption == some [
  .cons 1 (.cons (some 2) .nil), .cons 2 (.cons (some 1) .nil)]
#guard emptyOrder.toSql == source.toSql
#guard (emptyOrder.limit 1).toSqlServer.sql ==
  "SELECT [a0].[Id] AS [Id], [a0].[Bucket] AS [Bucket], [a0].[Value] AS [Value] FROM [compiler_items] [a0] ORDER BY (SELECT NULL) OFFSET 0 ROWS FETCH NEXT 1 ROWS ONLY"
#guard (source.orderBy (fun r => [r["Id"].asc]) |>.count |>.toSql .sqlServer).sql ==
  "SELECT COUNT(*) FROM [compiler_items] [a0]"
#guard (source.limit 0).toSqlServer.sql ==
  "SELECT TOP (0) [a1].[Id] AS [Id], [a1].[Bucket] AS [Bucket], [a1].[Value] AS [Value] FROM (SELECT [a0].[Id] AS [Id], [a0].[Bucket] AS [Bucket], [a0].[Value] AS [Value] FROM [compiler_items] [a0] ORDER BY (SELECT NULL) OFFSET 0 ROWS FETCH NEXT 1 ROWS ONLY) [a1]"
#guard (source.limit 0).toSqlChecked .sqlServer |>.isOk

def correlatedSource := source.bind (fun outer =>
  QueryP.from' (ts := C) items
    |>.where' (fun inner => inner["Bucket"] ==. outer["Bucket"])
    |>.limit 1)

-- Every current dialect rejects unsupported sibling captures explicitly.
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  match correlatedSource.toSqlChecked db with
  | .error (.correlatedDerivedTable "a0" "Bucket") => true
  | _ => false
#guard !(correlatedSource.count.toSqlChecked).isOk
#guard !((items.insertFrom correlatedSource).toSqlChecked).isOk

-- Correlation inside an expression subquery remains valid, including a
-- derived table that captures the enclosing expression-query scope.
def correlatedExpression := source.where' (fun outer => SqlExpr.exists' (
  QueryP.from' (ts := C) items
    |>.where' (fun inner => inner["Bucket"] ==. outer["Bucket"])
    |>.limit 1))
def correlatedNestedExpression := source.where' (fun outer => SqlExpr.exists' (
  QueryP.from' (ts := C) items
    |>.where' (fun inner => inner["Bucket"] ==. outer["Bucket"])
    |>.limit 1 |>.select (fun r => r)))
def correlatedProjection := source.where' (fun outer => SqlExpr.exists' (
  QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Id"].as "Id"])))
#guard correlatedExpression.toSqlChecked.isOk
#guard correlatedNestedExpression.toSqlChecked.isOk
#guard correlatedProjection.toSqlChecked.isOk

-- Some SQL engines hoist an outer-only aggregate out of a scalar subquery,
-- producing one row even when the outer source has LIMIT 0. Reject captures
-- in aggregate arguments so query-derived round budgets stay sound.
def outerAggregate := (source.limit 0).select (fun outer =>
  ![((QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Id"].as "Id"])
    |>.sum).embed).as "Sum"])
def correlatedLocalAggregate := source.select (fun outer =>
  ![((QueryP.from' (ts := C) items
    |>.where' (fun inner => inner["Bucket"] ==. outer["Bucket"])
    |>.select (fun inner => ![inner["Id"].as "Id"])
    |>.sum).embed).as "Sum"])
#guard outerAggregate.gcard.eval (fun _ => 99) == 0
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  match outerAggregate.toSqlChecked db with
  | .error (.invalidAggregate "aggregate arguments cannot capture an outer query row") => true
  | _ => false
#guard correlatedLocalAggregate.toSqlChecked.isOk

-- The intrinsically grouped aggregate path retains the same outer-capture
-- check. Its aggregate is in HAVING, so EXISTS must demand it.
def groupedOuterAggregate := (source.limit 0).where' (fun outer => SqlExpr.exists' (
  QueryP.from' (ts := C) items
    |>.groupBy (fun inner => ![inner["Bucket"].as "Bucket"])
    |>.having (fun _ a => a.sum (fun _ => outer["Id"]) >. 0)
    |>.select (fun keys _ => ![keys["Bucket"].as "Bucket"])))
#guard groupedOuterAggregate.gcard.eval (fun _ => 99) == 0
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  match groupedOuterAggregate.toSqlChecked db with
  | .error (.invalidAggregate "aggregate arguments cannot capture an outer query row") => true
  | _ => false

-- A nested expression subquery must not hide the aggregate's outer capture.
def hiddenOuterAggregate := (source.limit 0).select (fun outer =>
  ![((QueryP.from' (ts := C) items |>.select (fun _ =>
    ![(SqlExpr.caseWhen (SqlExpr.exists' (QueryP.from' (ts := C) items
      |>.where' (fun _ => outer["Id"] >. 0)))
      (SqlExpr.int 1) (SqlExpr.int 0)).as "Id"])
      |>.sum).embed).as "Sum"])
def hiddenLocalAggregate := source.select (fun _ =>
  ![((QueryP.from' (ts := C) items |>.select (fun inner =>
    ![(SqlExpr.caseWhen (SqlExpr.exists' (QueryP.from' (ts := C) items
      |>.where' (fun _ => inner["Id"] >. 0)))
      (SqlExpr.int 1) (SqlExpr.int 0)).as "Id"])
      |>.sum).embed).as "Sum"])
#guard hiddenOuterAggregate.gcard.eval (fun _ => 99) == 0
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  match hiddenOuterAggregate.toSqlChecked db with
  | .error (.invalidAggregate "aggregate arguments cannot capture an outer query row") => true
  | _ => false
#guard hiddenLocalAggregate.toSqlChecked.isOk

abbrev QuotedS : Schema := [("a\"b", .int)]
abbrev QuotedC : Ctx := { tables := [("compiler_quoted", QuotedS)] }
def quotedTable : Table "compiler_quoted" QuotedS := ⟨⟩
def quoted := Query.from' (ts := QuotedC) quotedTable
#guard quoted.toSql.sql ==
  "SELECT \"a0\".\"a\"\"b\" AS \"a\"\"b\" FROM \"compiler_quoted\" \"a0\""
#guard DatabaseType.sqlServer.quoteIdent "a]b" == "[a]]b]"
#guard DatabaseType.mysql.quoteIdent "a`b" == "`a``b`"
#guard DatabaseType.postgres.quoteIdent "a\"b" == "\"a\"\"b\""

def predicateProjection := source.select (fun r => ![(r["Value"] >. 1).as "Big"])
#guard predicateProjection.toSqlServer.sql ==
  "SELECT CASE WHEN ([a0].[Value] > @p0) THEN 1 WHEN NOT (([a0].[Value] > @p0)) THEN 0 ELSE NULL END AS [Big] FROM [compiler_items] [a0]"
#guard predicateProjection.toSqlServer.params == #[ ("@p0", .int 1) ]
#guard (predicateProjection.run env).toOption == some [
  .cons none .nil, .cons (some false) .nil, .cons (some true) .nil]

-- Predicates used as comparison operands and CASE branches retain UNKNOWN.
def comparedPredicate := source.where' (fun r => (r["Value"] >. 1) ==. false)
def conditionalPredicate := source.select (fun r =>
  ![(SqlExpr.caseWhen (r["Id"] >. 0) (r["Value"] >. 1) (r["Value"] <. 1)).as "Flag"])
#guard (comparedPredicate.toSqlServer.sql.splitOn "THEN 0 ELSE NULL END = @p1").length == 2
#guard (conditionalPredicate.toSqlServer.sql.splitOn "THEN 0 ELSE NULL END").length == 3

abbrev FlagS : Schema := [("Flag", .null .bool)]
abbrev FlagC : Ctx := { tables := [("compiler_flags", FlagS)] }
def flags : Table "compiler_flags" FlagS := ⟨⟩
def updateFlag : UpdateStmt FlagC "compiler_flags" FlagS :=
  flags.update |>.setWith "Flag" (fun r => r["Flag"].isNull) |>.where' (fun r => r["Flag"])
def insertFlag : InsertStmt FlagC "compiler_flags" FlagS :=
  flags.insert |>.value "Flag" ((SqlExpr.int 1) >. 0)
#guard (updateFlag.toSql .sqlServer).sql ==
  "UPDATE [compiler_flags] SET [Flag] = CASE WHEN [Flag] IS NULL THEN 1 WHEN NOT ([Flag] IS NULL) THEN 0 ELSE NULL END WHERE ([Flag] = 1)"
#guard ((insertFlag.toSql .sqlServer).sql.splitOn "THEN 0 ELSE NULL END").length == 2
#guard updateFlag.toSqlChecked.isOk
#guard insertFlag.toSqlChecked.isOk

#check_failure (source.groupBy (fun r => ![r["Bucket"].as "Bucket"])
  |>.select (fun _ a => ![(a.sum (fun _ => a.sum (fun r => r["Id"]))).as "Sum"]))
-- Raw grouped aggregates also reject nesting and ordinary WHERE placement.
#check_failure (GroupedExprP.aggE .sum
  (GroupedExprP.aggE .sum (.intC 1) : GroupedExprP AliasOf C [] (.null .int)))
#check_failure (source.where' (fun _ =>
  (GroupedExprP.cmp .gt (.widen .countAll) (.widen (.intC 0)) :
    GroupedExprP _ C [] (.null .bool))))
#guard grouped.toSqlChecked.isOk

def substringZero := source.select (fun _ => ![(SqlExpr.str "abcd" |>.substring 0 2).as "Text"])
def substringNegative := source.select (fun _ => ![(SqlExpr.str "abcd" |>.substring (-1) 3).as "Text"])
#guard substringZero.toSql.params == #[ (":p0", .int 1), (":p1", .int 1), (":p2", .string "abcd") ]
#guard substringNegative.toSql.params == substringZero.toSql.params

end CompilerRegressions
