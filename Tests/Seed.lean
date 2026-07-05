import Tests.Tables

/-! # The seed database, as an in-memory `Db`

The same rows the integration runner installs in every engine (`setupSql`),
as evaluator input: expected results for all registered cases are computed
over this value. Decimals are milli-units, date-times normalized, guids
lower-case — the `SqlType.interp` conventions. -/

open LeanLinq

namespace TQ

/-- Test values for user-named parameters, aligned with the seed data. -/
def bindings : List (String × SqlValue) := [
  ("minAge", .int 18), ("maxAge", .int 65),
  ("customerName", .string "John Doe"),
  ("isAdult", .bool true), ("isActive", .bool true),
  ("minPrice", .decimal "100.00"),
  ("startDate", .dateTime "2023-01-01"),
  ("targetId", .guid "11111111-1111-1111-1111-111111111111")
]

private def cust (id age : Int) (name : String) (act : Bool) : Values CustomersS :=
  .cons (some id) (.cons (some age) (.cons (some name) (.cons (some act) .nil)))

private def prod (id : Int) (name : String) (priceM : Option Int)
    (created uid : Option String) : Values ProductsS :=
  .cons (some id) (.cons (some name) (.cons priceM (.cons created (.cons uid .nil))))

private def ord (id cid pid amt : Int) : Values OrdersS :=
  .cons (some id) (.cons (some cid) (.cons (some pid) (.cons (some amt) .nil)))

def seedDb : Db := {
  tables := [
    ("customers", ⟨CustomersS,
      [cust 1 25 "John Doe" true, cust 2 30 "Jane Smith" true,
       cust 3 16 "Minor User" false, cust 4 65 "Senior User" true]⟩),
    ("products", ⟨ProductsS,
      [prod 1 "Laptop" (some 999990) (some "2023-01-15 00:00:00")
         (some "11111111-1111-1111-1111-111111111111"),
       prod 2 "Mouse" (some 25500) (some "2023-06-10 00:00:00")
         (some "22222222-2222-2222-2222-222222222222"),
       prod 3 "Discontinued" none none none]⟩),
    ("orders", ⟨OrdersS,
      [ord 1 1 1 500, ord 2 1 2 150, ord 3 2 1 300, ord 4 4 2 75]⟩)],
  params := bindings }

end TQ
