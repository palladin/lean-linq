import LeanLinq

/-! # lean-linq playground

Open this file in your editor and put the cursor on any `#eval` to see the
compiled SQL in the infoview. Everything here is safe to edit — the file is
not part of the library or the test suites (`lake build Playground` builds
just this file).

Try breaking things: misspell a column, compare an `int` to a `string`,
reference the aggregate binder before its `groupBy` — all elaboration errors. -/

open LeanLinq

/-! ## Schemas

Schemas must be `abbrev` (instance search needs to see through the name). -/

abbrev CustomersS : Schema :=
  [("Id", .long), ("Age", .int), ("Name", .string), ("IsActive", .bool)]
def customers : Table CustomersS := ⟨"customers"⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table OrdersS := ⟨"orders"⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .decimal),
   ("CreatedDate", .dateTime), ("UniqueId", .guid)]
def products : Table ProductsS := ⟨"products"⟩

/-! ## Pipeline style -/

def adults := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"] &&. c["IsActive"] ==. true)
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

#eval adults.toSql .sqlite
#eval adults.toSql .sqlServer      -- [brackets], @p0, OFFSET/FETCH pagination
#eval adults.toSql .postgres

/-! ## query! comprehension style — same core, identical SQL -/

def adults' := query! {
  from c in customers
  where 18 <. c["Age"] &&. c["IsActive"] ==. true
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}

#eval adults.toSql .sqlite == adults'.toSql .sqlite   -- true

def spending := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "CustId", c["Name"].as "Name", o["Amount"].as "Amount"])
  |>.groupBy (fun r => [r["CustId"].key, r["Name"].key])
  |>.having (fun _ a => 1 <. a.count)
  |>.orderBy (fun r a => [(a.sum r["Amount"]).desc])
  |>.select (fun r a => ![r["Name"].as "Name", (a.sum r["Amount"]).as "Total"])
  |>.limit 10

#eval (spending.toSql .sqlite).sql

def spending' := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Name"].as "Name", (a.sum o["Amount"]).as "Total"]
  limit 10
}

#eval (spending'.toSql .sqlite).sql

def cheapProducts := query! {
  from p in products
  where p["Price"] <. 100.00 ||. p["Price"].isNull
  orderBy p["Price"].asc
  select ![p["ProductName"].as "Name", p["Price"].as "Price"]
}

#eval cheapProducts.toSql .postgres

/-! ## Subqueries and scalar aggregates -/

def avgAmount := Query.from' orders
  |>.select (fun o => ![o["Amount"].as "Amount"]) |>.avg

#eval avgAmount.toSql .sqlite

def bigSpenders := Query.from' customers
  |>.where' (fun c => c["Id"].inQuery (query! {
      from o in orders
      where o["Amount"] >. avgAmount.embed
      select ![o["CustomerId"].as "CustomerId"]
    }))
  |>.select (fun c => ![c["Name"].as "Name"])

#eval (bigSpenders.toSql .sqlite).sql

/-! ## Statements -/

#eval (customers.insert
  |>.value "Id" 100 |>.value "Age" 30
  |>.value "Name" "Ada" |>.value "IsActive" true).toSql .sqlite

#eval (customers.update
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["IsActive"] ==. true)).toSql .sqlServer

#eval (customers.delete |>.where' (fun c => c["Age"].isNull)).toSql .postgres

/-! ## The type system at work — uncomment any line for the error

#eval (Query.from' customers |>.where' (fun c => c["Nmae"] ==. "Ada")).toSql .sqlite
--                                          typo ^^^^^^ : no HasCol instance

#eval (Query.from' customers |>.where' (fun c => c["Id"] ==. c["Name"])).toSql .sqlite
--                                     long vs string ^^^^^^^^^^^^^^^^ : type mismatch

#eval (query! { from o in orders
                where a.count >. 1     -- binder `a` not in scope before groupBy
                groupBy o["CustomerId"].key into a
                select ![o["CustomerId"].as "Cid"] }).toSql .sqlite
-/
