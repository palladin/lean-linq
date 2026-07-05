import LeanLinq

/-! # lean-linq playground

Open this file in your editor and put the cursor on any `#eval` to see the
compiled SQL in the infoview. Everything here is safe to edit — the file is
not part of the library or the test suites (`lake build Playground` builds
just this file).

Try breaking things: misspell a column, compare an `int` to a `string`,
reference a table outside the context, reference the aggregate binder before
its `groupBy` — all elaboration errors. -/

open LeanLinq

/-! ## Schemas, tables, and the context

Schemas and contexts must be `abbrev` (instance search needs to see through
the name). A table carries its name and schema in its *type*; the context
lists what the database provides, and every table reference is resolved
against it by instance search (`HasTable`) at elaboration time. -/

abbrev CustomersS : Schema :=
  [("Id", .long), ("Age", .int), ("Name", .string), ("IsActive", .bool)]
def customers : Table "customers" CustomersS := ⟨⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table "orders" OrdersS := ⟨⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .decimal),
   ("CreatedDate", .dateTime), ("UniqueId", .guid)]
def products : Table "products" ProductsS := ⟨⟩

abbrev PlayCtx : Ctx :=
  { tables := [("customers", CustomersS), ("orders", OrdersS), ("products", ProductsS)] }

/-! ## Pipeline style -/

def adults := Query.from' (ts := PlayCtx) customers
  |>.where' (fun c => 18 <. c["Age"] &&. c["IsActive"] ==. true)
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

#eval adults.toSql .sqlite
#eval adults.toSql .sqlServer      -- [brackets], @p0, OFFSET/FETCH pagination
#eval adults.toSql .postgres

/-! ## query! comprehension style — same core, identical SQL -/

def adults' := (query! {
  from c in customers
  where 18 <. c["Age"] &&. c["IsActive"] ==. true
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
} : Query PlayCtx _)

#eval adults.toSql .sqlite == adults'.toSql .sqlite   -- true

def spending := Query.from' (ts := PlayCtx) customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "CustId", c["Name"].as "Name", o["Amount"].as "Amount"])
  |>.groupBy (fun r => [r["CustId"].key, r["Name"].key])
  |>.having (fun _ a => 1 <. a.count)
  |>.orderBy (fun r a => [(a.sum r["Amount"]).desc])
  |>.select (fun r a => ![r["Name"].as "Name", (a.sum r["Amount"]).as "Total"])
  |>.limit 10

#eval (spending.toSql .sqlite).sql

def spending' := (query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Name"].as "Name", (a.sum o["Amount"]).as "Total"]
  limit 10
} : Query PlayCtx _)

#eval (spending'.toSql .sqlite).sql

def cheapProducts := (query! {
  from p in products
  where p["Price"] <. 100.00 ||. p["Price"].isNull
  orderBy p["Price"].asc
  select ![p["ProductName"].as "Name", p["Price"].as "Price"]
} : Query PlayCtx _)

#eval cheapProducts.toSql .postgres

/-! ## Subqueries and scalar aggregates -/

def avgAmount := Query.from' (ts := PlayCtx) orders
  |>.select (fun o => ![o["Amount"].as "Amount"]) |>.avg

#eval avgAmount.toSql .sqlite

def bigSpenders := Query.from' (ts := PlayCtx) customers
  |>.where' (fun c => c["Id"].inQuery (query! {
      from o in orders
      where o["Amount"] >. avgAmount.embed
      select ![o["CustomerId"].as "CustomerId"]
    }))
  |>.select (fun c => ![c["Name"].as "Name"])

#eval (bigSpenders.toSql .sqlite).sql

/-! ## Executable semantics — the same query value *runs* in pure Lean

`Query.run : Query ts s → TableEnv ts → List (Values s)` is the library's
denotational semantics: a typed in-memory evaluator over the exact query
value that compiles to SQL (the integration suite differential-tests all
three engines against it). Table resolution happened at elaboration, so a
`TableEnv PlayCtx` is all it takes — no names, no failure modes. -/

def demoEnv : TableEnv PlayCtx.tables :=
  .cons  -- customers
    [.cons (some 1) (.cons (some 25) (.cons (some "John Doe") (.cons (some true) .nil))),
     .cons (some 2) (.cons (some 30) (.cons (some "Jane Smith") (.cons (some true) .nil))),
     .cons (some 3) (.cons (some 16) (.cons (some "Minor User") (.cons (some false) .nil)))] <|
  .cons  -- orders
    [.cons (some 1) (.cons (some 1) (.cons (some 1) (.cons (some 500) .nil))),
     .cons (some 2) (.cons (some 2) (.cons (some 1) (.cons (some 300) .nil)))] <|
  .cons [] .nil  -- products

#eval adults.run demoEnv    -- Except.ok [(2, "Jane Smith"), (1, "John Doe")]
#eval (adults'.run demoEnv).toOption == (adults.run demoEnv).toOption   -- twins agree
#eval spending.run demoEnv  -- joins/grouping run in memory as well

-- NULL is data; exceptional conditions are the explicit error channel:
#eval (Query.from' (ts := PlayCtx) customers
  |>.select (fun c => ![(c["Age"] / 0).as "Boom"])).run demoEnv
-- Except.error LeanLinq.EvalError.divByZero

/-! ## Statements -/

#eval (customers.insert (ts := PlayCtx)
  |>.value "Id" 100 |>.value "Age" 30
  |>.value "Name" "Ada" |>.value "IsActive" true).toSql .sqlite

#eval (customers.update (ts := PlayCtx)
  |>.setWith "Age" (fun c => c["Age"] + 1)
  |>.where' (fun c => c["IsActive"] ==. true)).toSql .sqlServer

#eval (customers.delete (ts := PlayCtx) |>.where' (fun c => c["Age"].isNull)).toSql .postgres

-- statements also apply in memory, through the same `HasTable` instance:
#eval ((customers.update (ts := PlayCtx)
  |>.setWith "Age" (fun c => c["Age"] + 1)).apply demoEnv) |> fun r => if r matches .ok _ then "applied" else "error"

/-! ## The type system at work — uncomment any line for the error

#eval (Query.from' (ts := PlayCtx) customers |>.where' (fun c => c["Nmae"] ==. "Ada")).toSql .sqlite
--                                                typo ^^^^^^ : no HasCol instance

#eval (Query.from' (ts := PlayCtx) customers |>.where' (fun c => c["Id"] ==. c["Name"])).toSql .sqlite
--                                           long vs string ^^^^^^^^^^^^^^^^ : type mismatch

#eval (Query.from' (ts := PlayCtx) (⟨⟩ : Table "ghost" CustomersS)).toSql .sqlite
--     table not in the context ^^^^^^^^^^^^^^^^^^^^^^ : no HasTable instance

#eval ((query! { from o in orders
                 where a.count >. 1     -- binder `a` not in scope before groupBy
                 groupBy o["CustomerId"].key into a
                 select ![o["CustomerId"].as "Cid"] } : Query PlayCtx _)).toSql .sqlite
-/
