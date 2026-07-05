import Tests.Tables

/-! Ported statement shapes: INSERT / UPDATE / DELETE, including NULL
assignments and the wider column types. -/

open LeanLinq

namespace TQ

def InsertBasic := customers.insert
  |>.value "Id" 200 |>.value "Age" 25 |>.value "Name" "John Doe"
def UpdateBasic := customers.update
  |>.set "Age" 26 |>.where' (fun c => c["Id"] ==. 200)
def UpdateMultiple := customers.update
  |>.set "Age" 27 |>.set "Name" "John Smith" |>.where' (fun c => c["Id"] ==. 200)
def UpdateConditional := customers.update
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["Age"] >=. 18 &&. c["Name"] !=. "Admin")
def DeleteBasic := customers.delete |>.where' (fun c => c["Id"] ==. 200)
def DeleteConditional := customers.delete
  |>.where' (fun c => c["Age"] <. 18 ||. c["Name"] ==. "Temp")
def DeleteAll := customers.delete
def UpdateSetNull := customers.update |>.setNull "Name"
def UpdateSetNullInt := customers.update |>.setNull "Age"
def UpdateSetNullMixed := customers.update |>.set "Name" "John" |>.setNull "Age"
def UpdateSetNullWhere := customers.update
  |>.setNull "Name" |>.where' (fun c => c["Id"] ==. 200)
def InsertWithNull := customers.insert
  |>.value "Id" 202 |>.valueNull "Name" |>.value "Age" 25
def InsertWithNullInt := customers.insert
  |>.value "Id" 203 |>.value "Name" "John" |>.valueNull "Age"
def InsertWithNewColumns := products.insert
  |>.value "Id" 200 |>.value "ProductName" "Test Product"
  |>.value "Price" 99.99
  |>.value "CreatedDate" (SqlExpr.dt "2024-08-18 00:00:00")
  |>.value "UniqueId" (SqlExpr.gd "12345678-1234-1234-1234-123456789012")
def UpdateWithNewColumns := products.update
  |>.set "Price" 119.99
  |>.set "CreatedDate" (SqlExpr.dt "2024-12-25 00:00:00")
  |>.set "UniqueId" (SqlExpr.gd "87654321-4321-4321-4321-210987654321")
  |>.where' (fun p => p["Id"] ==. 100)
def InsertWithNewColumnsNull := products.insert
  |>.value "Id" 201 |>.value "ProductName" "Null Test"
  |>.valueNull "Price" |>.valueNull "CreatedDate" |>.valueNull "UniqueId"
def UpdateSetNewColumnsNull := products.update
  |>.setNull "Price" |>.setNull "CreatedDate" |>.setNull "UniqueId"
  |>.where' (fun p => p["Id"] ==. 101)

/-- Register a statement: expected = the statement's table after applying it
to the seed, ordered by `Id` — mirroring the harness's rolled-back
transaction plus verification SELECT. -/
def si (i : InsertStmt s) : Case :=
  { compile := fun db => i.toSql db
    expected := fun db => renderTable (i.apply db) i.table.name s
    ordered := true }
def su (u : UpdateStmt s) : Case :=
  { compile := fun db => u.toSql db
    expected := fun db => renderTable (u.apply db) u.table.name s
    ordered := true }
def sd (d : DeleteStmt s) : Case :=
  { compile := fun db => d.toSql db
    expected := fun db => renderTable (d.apply db) d.table.name s
    ordered := true }

/-- The statement registry: name ↦ per-dialect compilation + expected state. -/
def statementCases : List (String × Case) := [
  ("InsertBasic", si InsertBasic), ("UpdateBasic", su UpdateBasic),
  ("UpdateMultiple", su UpdateMultiple), ("UpdateConditional", su UpdateConditional),
  ("DeleteBasic", sd DeleteBasic), ("DeleteConditional", sd DeleteConditional),
  ("DeleteAll", sd DeleteAll), ("UpdateSetNull", su UpdateSetNull),
  ("UpdateSetNullInt", su UpdateSetNullInt), ("UpdateSetNullMixed", su UpdateSetNullMixed),
  ("UpdateSetNullWhere", su UpdateSetNullWhere), ("InsertWithNull", si InsertWithNull),
  ("InsertWithNullInt", si InsertWithNullInt),
  ("InsertWithNewColumns", si InsertWithNewColumns),
  ("UpdateWithNewColumns", su UpdateWithNewColumns),
  ("InsertWithNewColumnsNull", si InsertWithNewColumnsNull),
  ("UpdateSetNewColumnsNull", su UpdateSetNewColumnsNull)
]

end TQ
