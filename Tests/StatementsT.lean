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
  |>.value "CreatedDate" (SqlExpr.dt "2024-08-18")
  |>.value "UniqueId" (SqlExpr.gd "12345678-1234-1234-1234-123456789012")
def UpdateWithNewColumns := products.update
  |>.set "Price" 119.99
  |>.set "CreatedDate" (SqlExpr.dt "2024-12-25")
  |>.set "UniqueId" (SqlExpr.gd "87654321-4321-4321-4321-210987654321")
  |>.where' (fun p => p["Id"] ==. 100)
def InsertWithNewColumnsNull := products.insert
  |>.value "Id" 201 |>.value "ProductName" "Null Test"
  |>.valueNull "Price" |>.valueNull "CreatedDate" |>.valueNull "UniqueId"
def UpdateSetNewColumnsNull := products.update
  |>.setNull "Price" |>.setNull "CreatedDate" |>.setNull "UniqueId"
  |>.where' (fun p => p["Id"] ==. 101)

def si (i : InsertStmt s) : DatabaseType → Compiled := fun db => i.toSql db
def su (u : UpdateStmt s) : DatabaseType → Compiled := fun db => u.toSql db
def sd (d : DeleteStmt s) : DatabaseType → Compiled := fun db => d.toSql db

/-- The statement registry: name ↦ per-dialect compilation. -/
def statementCases : List (String × (DatabaseType → Compiled)) := [
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
