import LeanLinq

/-! Test models: the classic customers / products / orders trio. -/

open LeanLinq

namespace TQ

abbrev CustomersS : Schema :=
  [("Id", .long), ("Age", .int), ("Name", .string), ("IsActive", .bool)]
def customers : Table CustomersS := ⟨"customers"⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .decimal),
   ("CreatedDate", .dateTime), ("UniqueId", .guid)]
def products : Table ProductsS := ⟨"products"⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table OrdersS := ⟨"orders"⟩

/-- Registry helpers: compile a query/scalar/statement per dialect. -/
def q (query : Query s) : DatabaseType → CompiledSql := fun db => query.toSql db
def sq (s : ScalarQuery t) : DatabaseType → CompiledSql := fun db => s.toSql db

end TQ
