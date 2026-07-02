import Tests.Basic

/-! # Golden tests: exact SQL text + parameters for every M1 feature. -/

open LeanLinq

def check (label : String) (actual : Compiled) (sql : String)
    (params : Array (String × SqlValue) := #[]) : IO Bool := do
  let expected : Compiled := { sql, params }
  if actual == expected then
    IO.println s!"ok   {label}"
    pure true
  else
    IO.eprintln s!"FAIL {label}"
    IO.eprintln s!"  expected sql: {expected.sql}"
    IO.eprintln s!"       got sql: {actual.sql}"
    IO.eprintln s!"  expected params: {repr expected.params}"
    IO.eprintln s!"       got params: {repr actual.params}"
    pure false

def main : IO UInt32 := do
  let results ← List.mapM id [
    check "from" exFrom.toSql
      "SELECT * FROM Customers",
    check "select named column" exSelectName.toSql
      "SELECT c0.Name AS Name FROM (SELECT * FROM Customers) AS c0",
    check "select positional" exSelectPositional.toSql
      "SELECT c0.Id AS Id FROM (SELECT * FROM Customers) AS c0",
    check "where + select" exWhereSelect.toSql
      "SELECT c1.Id AS Id, c1.Age AS Age FROM (SELECT * FROM (SELECT * FROM Customers) AS c0 WHERE (c0.Name = @p0)) AS c1"
      #[("@p0", .string "Nick")],
    check "operators" exOperators.toSql
      "SELECT * FROM (SELECT * FROM Customers) AS c0 WHERE ((@p0 < c0.Age) AND (NOT (c0.Name = @p1)))"
      #[("@p0", .int 18), ("@p1", .string "Bob")],
    check "arithmetic + concat" exCompute.toSql
      "SELECT (c0.Age + @p0) AS AgePlus, (c0.Name || @p1) AS Loud FROM (SELECT * FROM Customers) AS c0"
      #[("@p0", .int 1), ("@p1", .string "!")],
    check "product with projection" exProduct.toSql
      "SELECT c0.Name AS Name, c1.OrderId AS OrderId FROM (SELECT * FROM Customers) AS c0, (SELECT * FROM Orders) AS c1",
    check "product + filter (join)" exJoin.toSql
      "SELECT * FROM (SELECT c0.Id AS CustId, c0.Name AS Name, c1.CustomerId AS OrderCustId, c1.OrderId AS OrderId FROM (SELECT * FROM Customers) AS c0, (SELECT * FROM Orders) AS c1) AS c2 WHERE (c2.CustId = c2.OrderCustId)",
    check "product append" exProductAppend.toSql
      "SELECT c0.Id AS Id, c0.Name AS Name, c0.Age AS Age, c1.OrderId AS OrderId, c1.CustomerId AS CustomerId FROM (SELECT * FROM Customers) AS c0, (SELECT * FROM Orders) AS c1",
    check "select all (identity)" exSelectAll.toSql
      "SELECT c0.Id AS Id, c0.Name AS Name, c0.Age AS Age FROM (SELECT * FROM Customers) AS c0",
    check "stacked filters" exFilterTwice.toSql
      "SELECT * FROM (SELECT * FROM (SELECT * FROM Customers) AS c0 WHERE (c0.Age < @p0)) AS c1 WHERE (@p1 < c1.Age)"
      #[("@p0", .int 65), ("@p1", .int 18)],
    check "not equal" exNotEqual.toSql
      "SELECT * FROM (SELECT * FROM Customers) AS c0 WHERE (NOT (c0.Id = @p0))"
      #[("@p0", .int 0)]
  ]
  if results.all id then
    IO.println s!"all {results.length} tests passed"
    pure 0
  else
    IO.eprintln s!"{results.filter (!·)|>.length} of {results.length} tests FAILED"
    pure 1
