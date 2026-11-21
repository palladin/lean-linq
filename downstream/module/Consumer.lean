module

public import LeanLinq

/-! A downstream module that defines a public query with `query!` and a
public program with `db!`. -/

open LeanLinq

public section

abbrev PeopleS : Schema :=
  [("Id", .long), ("Age", .null .int), ("Name", .null .string)]
def people : Table "People" PeopleS := ⟨⟩

abbrev AppCtx : Ctx := { tables := [("People", PeopleS)], params := [] }

def adults := (query! {
  from p in people
  where p["Age"] >. 17
  select ![p["Id"].as "Id", p["Name"].as "Name"]
} : Query AppCtx _)

def countAdults : Db AppCtx 1 Nat := db! {
  let rows ← adults.execQuery
  return rows.length
}
