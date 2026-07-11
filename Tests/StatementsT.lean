import Tests.Tables

/-! Ported statement shapes: INSERT / UPDATE / DELETE, including NULL
assignments and the wider column types. -/

open LeanLinq

namespace TQ

/- Statements are pinned to `TestCtx` (their context is not constrained by
construction — only `apply` needs the table instance). -/

def InsertBasic := customers.insert (ts := TestCtx)
  |>.value "Id" 200 |>.value "Age" 25 |>.value "Name" "John Doe"
def UpdateBasic := customers.update (ts := TestCtx)
  |>.set "Age" 26 |>.where' (fun c => c["Id"] ==. 200)
def UpdateMultiple := customers.update (ts := TestCtx)
  |>.set "Age" 27 |>.set "Name" "John Smith" |>.where' (fun c => c["Id"] ==. 200)
def UpdateConditional := customers.update (ts := TestCtx)
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["Age"] >=. 18 &&. c["Name"] !=. "Admin")
def DeleteBasic := customers.delete (ts := TestCtx) |>.where' (fun c => c["Id"] ==. 200)
def DeleteConditional := customers.delete (ts := TestCtx)
  |>.where' (fun c => c["Age"] <. 18 ||. c["Name"] ==. "Temp")
def DeleteAll := customers.delete (ts := TestCtx)
def UpdateSetNull := customers.update (ts := TestCtx) |>.setNull "Name"
def UpdateSetNullInt := customers.update (ts := TestCtx) |>.setNull "Age"
def UpdateSetNullMixed := customers.update (ts := TestCtx) |>.set "Name" "John" |>.setNull "Age"
def UpdateSetNullWhere := customers.update (ts := TestCtx)
  |>.setNull "Name" |>.where' (fun c => c["Id"] ==. 200)
def InsertWithNull := customers.insert (ts := TestCtx)
  |>.value "Id" 202 |>.valueNull "Name" |>.value "Age" 25
def InsertWithNullInt := customers.insert (ts := TestCtx)
  |>.value "Id" 203 |>.value "Name" "John" |>.valueNull "Age"
def InsertWithNewColumns := products.insert (ts := TestCtx)
  |>.value "Id" 200 |>.value "ProductName" "Test Product"
  |>.value "Price" 99.99
  |>.value "CreatedDate" (SqlExpr.dt "2024-08-18 00:00:00")
  |>.value "UniqueId" (SqlExpr.gd "12345678-1234-1234-1234-123456789012")
def UpdateWithNewColumns := products.update (ts := TestCtx)
  |>.set "Price" 119.99
  |>.set "CreatedDate" (SqlExpr.dt "2024-12-25 00:00:00")
  |>.set "UniqueId" (SqlExpr.gd "87654321-4321-4321-4321-210987654321")
  |>.where' (fun p => p["Id"] ==. 100)
def InsertWithNewColumnsNull := products.insert (ts := TestCtx)
  |>.value "Id" 201 |>.value "ProductName" "Null Test"
  |>.valueNull "Price" |>.valueNull "CreatedDate" |>.valueNull "UniqueId"
def UpdateSetNewColumnsNull := products.update (ts := TestCtx)
  |>.setNull "Price" |>.setNull "CreatedDate" |>.setNull "UniqueId"
  |>.where' (fun p => p["Id"] ==. 101)

/-- Register a statement: expected = the statement's table after applying it
to the seed, ordered by `Id` — mirroring the harness's rolled-back
transaction plus verification SELECT. The table is read back through the
same `HasTable` instance `apply` writes through. -/
def si (i : InsertStmt TestCtx n s) [inst : HasTable TestCtx.tables n s] : Case :=
  { compile := fun db => i.toSql db
    expected := fun env =>
      match i.apply env seedParams with
      | .ok env' => renderTableRows (inst.rows env')
      | .error e => evalFailure e
    ordered := true
    payload := .ins i }
def su (u : UpdateStmt TestCtx n s) [inst : HasTable TestCtx.tables n s] : Case :=
  { compile := fun db => u.toSql db
    expected := fun env =>
      match u.apply env seedParams with
      | .ok env' => renderTableRows (inst.rows env')
      | .error e => evalFailure e
    ordered := true
    payload := .upd u }
def sd (d : DeleteStmt TestCtx n s) [inst : HasTable TestCtx.tables n s] : Case :=
  { compile := fun db => d.toSql db
    expected := fun env =>
      match d.apply env seedParams with
      | .ok env' => renderTableRows (inst.rows env')
      | .error e => evalFailure e
    ordered := true
    payload := .del d }

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
