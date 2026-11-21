module

import LeanLinq
-- `#guard` runs the compiler while this file compiles, which a module asks for
-- with `meta import`. Writing and type-checking the query needs only `import`.
meta import LeanLinq

/-! A file in Lean's module system that imports lean-linq and writes a query
with `query!`, as a downstream project does. Compiling it checks the import,
the comprehension syntax and the compiler from inside a module. -/

open LeanLinq

namespace ModuleImport

abbrev PeopleS : Schema :=
  [("Id", .long), ("Age", .null .int), ("Name", .null .string)]
def people : Table "People" PeopleS := ⟨⟩

abbrev Ctx : Ctx := { tables := [("People", PeopleS)], params := [] }

def adults := (query! {
  from p in people
  where p["Age"] >. 17
  select ![p["Name"].as "Name"]
} : Query Ctx _)

#guard adults.toSql.sql ==
  "SELECT \"a0\".\"Name\" AS \"Name\" FROM \"People\" \"a0\" WHERE (\"a0\".\"Age\" > :p0)"

end ModuleImport
