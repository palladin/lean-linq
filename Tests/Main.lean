import Tests.Basic

/-! # Golden tests: exact SQL text + parameters for every feature. -/

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

def allCustomerCols (a : String) : String :=
  s!"{a}.Id AS Id, {a}.Name AS Name, {a}.Age AS Age"

def baseCustomers : String :=
  s!"SELECT {allCustomerCols "c0"} FROM Customers AS c0"

def main : IO UInt32 := do
  let results ← List.mapM id [
    -- pipeline style
    check "from" exFrom.toSql
      baseCustomers,
    check "select named column" exSelectName.toSql
      s!"SELECT c1.Name AS Name FROM ({baseCustomers}) AS c1",
    check "select positional" exSelectPositional.toSql
      s!"SELECT c1.Id AS Id FROM ({baseCustomers}) AS c1",
    check "where + select" exWhereSelect.toSql
      s!"SELECT c2.Id AS Id, c2.Age AS Age FROM (SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1 WHERE (c1.Name = @p0)) AS c2"
      #[("@p0", .string "Nick")],
    check "operators" exOperators.toSql
      s!"SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1 WHERE ((@p0 < c1.Age) AND (NOT (c1.Name = @p1)))"
      #[("@p0", .int 18), ("@p1", .string "Bob")],
    check "arithmetic + concat" exCompute.toSql
      s!"SELECT (c1.Age + @p0) AS AgePlus, (c1.Name || @p1) AS Loud FROM ({baseCustomers}) AS c1"
      #[("@p0", .int 1), ("@p1", .string "!")],
    check "select all (identity)" exSelectAll.toSql
      s!"SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1",
    check "stacked wheres" exFilterTwice.toSql
      s!"SELECT {allCustomerCols "c2"} FROM (SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1 WHERE (c1.Age < @p0)) AS c2 WHERE (@p1 < c2.Age)"
      #[("@p0", .int 65), ("@p1", .int 18)],
    check "not equal" exNotEqual.toSql
      s!"SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1 WHERE (NOT (c1.Id = @p0))"
      #[("@p0", .int 0)],
    -- LINQ comprehension style: flat SELECTs
    check "linq where" exLinqWhere.toSql
      "SELECT c0.Name AS Name FROM Customers AS c0 WHERE (@p0 < c0.Age)"
      #[("@p0", .int 10)],
    check "linq join (nested from)" exLinqJoin.toSql
      "SELECT c0.Name AS Name, c1.OrderId AS OrderId FROM Customers AS c0, Orders AS c1 WHERE (c0.Id = c1.CustomerId)",
    check "linq append" exLinqAppend.toSql
      "SELECT c0.Id AS Id, c0.Name AS Name, c0.Age AS Age, c1.OrderId AS OrderId, c1.CustomerId AS CustomerId FROM Customers AS c0, Orders AS c1",
    check "linq two wheres" exLinqTwoWhere.toSql
      "SELECT c0.Id AS Id FROM Customers AS c0 WHERE (@p0 < c0.Age) AND (c0.Name = @p1)"
      #[("@p0", .int 10), ("@p1", .string "Nick")],
    check "linq subquery source" exLinqSub.toSql
      s!"SELECT c2.Name AS Name FROM (SELECT {allCustomerCols "c1"} FROM ({baseCustomers}) AS c1 WHERE (@p0 < c1.Age)) AS c2"
      #[("@p0", .int 18)]
  ]
  if results.all id then
    IO.println s!"all {results.length} tests passed"
    pure 0
  else
    IO.eprintln s!"{results.filter (!·) |>.length} of {results.length} tests FAILED"
    pure 1
