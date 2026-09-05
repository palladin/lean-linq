import Tests.CompilerRegressions

/-! Aggregation consumes projected input rows, including outer captures and
subqueries. The evaluator and all four native drivers use the same fixtures
with independently specified result bags. -/

namespace AggregateProjection
open LeanLinq

abbrev C := CompilerRegressions.C
abbrev Result : Schema := [("Id", .int), ("Total", .null .int)]
def items := CompilerRegressions.items
def source := CompilerRegressions.source

def outerOnly : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.sum).embed).as "Total"])

def mixed : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun inner => ![(inner["Id"] + outer["Id"]).as "Value"])
    |>.sum).embed).as "Total"])

def filteredOuter : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.where' (fun inner => inner["Bucket"] ==. outer["Bucket"])
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.sum).embed).as "Total"])

def hiddenExists : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun _ => ![(SqlExpr.caseWhen
      (SqlExpr.exists' (QueryP.from' (ts := C) items
        |>.where' (fun _ => outer["Id"] >. 1)))
      (SqlExpr.int 1) (SqlExpr.int 0)).as "Value"])
    |>.sum).embed).as "Total"])

-- A scalar subquery inside an aggregate operand captures both the outer row
-- and the current input row. Each nested sum has its own input projection.
def nestedScalar : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun middle => ![((QueryP.from' (ts := C) items
      |>.where' (fun inner => inner["Bucket"] ==. middle["Bucket"])
      |>.select (fun inner => ![(inner["Id"] + outer["Id"]).as "Value"])
      |>.sum).embed).as "Value"])
    |>.sum).embed).as "Total"])

def nullableOuter : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Value"].as "Value"]) |>.sum).embed).as "Total"])

def countNullable : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Value"].as "Value"]) |>.count).embed).as "Total"])

def emptyInnerSum : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items |>.limit 0
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.sum).embed).as "Total"])

def emptyInnerCount : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items |>.limit 0
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.count).embed).as "Total"])

def limited : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.orderBy (fun inner => [inner["Id"].asc]) |>.limit 2
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.sum).embed).as "Total"])

def distinctInput : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun _ => ![outer["Id"].as "Value"]) |>.distinct |>.sum).embed).as "Total"])

def orderedDistinct : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun inner => ![(inner["Bucket"] + outer["Id"]).as "Value"])
    |>.orderBy (fun value => [value["Value"].desc]) |>.distinct |>.sum).embed).as "Total"])

def orderedGrouped : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.groupBy (fun inner => ![inner["Bucket"].as "Bucket"])
    |>.orderBy (fun _ a => [(a.sum (fun inner => inner["Id"] + outer["Id"])).desc])
    |>.select (fun _ a => ![(a.sum (fun inner => inner["Id"] + outer["Id"])).as "Value"])
    |>.sum).embed).as "Total"])

-- Unlike dead ordering above, this descending order determines which row is
-- summed. Dropping it changes every result by selecting Id 1 instead of Id 3.
def descendingLimited : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.orderBy (fun inner => [inner["Id"].desc]) |>.limit 1
    |>.select (fun inner => ![(inner["Id"] + outer["Id"]).as "Value"])
    |>.sum).embed).as "Total"])

-- HAVING, ORDER BY and SELECT use different captured aggregate expressions.
-- LIMIT makes ordering observable; the final sum consumes a grouped boundary.
def groupedClauses : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.groupBy (fun inner => ![inner["Bucket"].as "Bucket"])
    |>.having (fun _ a => a.sum (fun _ => outer["Id"]) >. 1)
    |>.orderBy (fun keys a =>
      [(a.sum (fun inner => inner["Id"] + outer["Id"])).desc, keys["Bucket"].asc])
    |>.select (fun _ a => ![(a.sum (fun inner => inner["Id"] + outer["Id"])).as "Value"])
    |>.limit 1 |>.sum).embed).as "Total"])

def groupedCount : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.groupBy (fun inner => ![inner["Bucket"].as "Bucket"])
    |>.having (fun _ a => a.sum (fun _ => outer["Id"]) >. 2)
    |>.select (fun _ a => ![a.count.as "Value"])
    |>.count).embed).as "Total"])

def groupedBoundary : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.groupBy (fun inner => ![inner["Bucket"].as "Bucket"])
    |>.select (fun _ a => ![(a.sum (fun inner => inner["Value"])).as "Subtotal"])
    |>.select (fun group => ![(group["Subtotal"] + outer["Id"]).as "Value"])
    |>.sum).embed).as "Total"])

def localInput : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun inner => ![inner["Id"].as "Value"]) |>.sum).embed).as "Total"])

-- A plain scalar aggregate does not expose its input's user-facing column
-- label. Its private projection alias must work even for an empty label.
def emptyLabelScalar := source.select (fun row => ![row["Id"].as ""]) |>.sum
def quotedLabelScalar := source.select (fun row => ![row["Id"].as "a\"b]`c"]) |>.sum
#guard (emptyLabelScalar.run CompilerRegressions.env).toOption == some (some 6)
#guard (quotedLabelScalar.run CompilerRegressions.env).toOption == some (some 6)

def emptyLabel : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun inner => ![inner["Id"].as ""]) |>.sum).embed).as "Total"])
def quotedLabel : Query C Result := source.select (fun outer =>
  ![outer["Id"].as "Id", ((QueryP.from' (ts := C) items
    |>.select (fun inner => ![inner["Id"].as "a\"b]`c"]) |>.sum).embed).as "Total"])

structure Case where
  name : String
  query : Query C Result
  expected : List (Values Result)

private def totals (a b c : Option Int) : List (Values Result) :=
  [.cons 1 (.cons a .nil), .cons 2 (.cons b .nil), .cons 3 (.cons c .nil)]

def cases : List Case := [
  ⟨"outer-only", outerOnly, totals (some 3) (some 6) (some 9)⟩,
  ⟨"mixed local/outer", mixed, totals (some 9) (some 12) (some 15)⟩,
  ⟨"filtered outer-only", filteredOuter, totals (some 2) (some 4) (some 3)⟩,
  ⟨"hidden EXISTS", hiddenExists, totals (some 0) (some 3) (some 3)⟩,
  ⟨"nested scalar", nestedScalar, totals (some 14) (some 19) (some 24)⟩,
  ⟨"nullable outer", nullableOuter, totals none (some 0) (some 6)⟩,
  ⟨"COUNT over nullable projection", countNullable, totals (some 3) (some 3) (some 3)⟩,
  ⟨"empty inner SUM", emptyInnerSum, totals none none none⟩,
  ⟨"empty inner COUNT", emptyInnerCount, totals (some 0) (some 0) (some 0)⟩,
  ⟨"empty outer", outerOnly.limit 0, []⟩,
  ⟨"limited input", limited, totals (some 2) (some 4) (some 6)⟩,
  ⟨"distinct input", distinctInput, totals (some 1) (some 2) (some 3)⟩,
  ⟨"ordered DISTINCT input", orderedDistinct, totals (some 5) (some 7) (some 9)⟩,
  ⟨"ordered grouped input", orderedGrouped, totals (some 9) (some 12) (some 15)⟩,
  ⟨"descending LIMIT input", descendingLimited, totals (some 4) (some 5) (some 6)⟩,
  ⟨"grouped HAVING/ORDER", groupedClauses, totals (some 5) (some 7) (some 9)⟩,
  ⟨"grouped COUNT", groupedCount, totals (some 0) (some 1) (some 2)⟩,
  ⟨"grouped boundary", groupedBoundary, totals (some 4) (some 6) (some 8)⟩,
  ⟨"local input", localInput, totals (some 6) (some 6) (some 6)⟩,
  ⟨"empty input label", emptyLabel, totals (some 6) (some 6) (some 6)⟩,
  ⟨"quoted input label", quotedLabel, totals (some 6) (some 6) (some 6)⟩]

#guard cases.all fun c => (c.query.run CompilerRegressions.env).toOption == some c.expected
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  cases.all (fun c => (c.query.toSqlChecked db).isOk)

end AggregateProjection
