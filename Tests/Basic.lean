import LeanLinq

/-! # Example schemas and queries

The golden assertions live in `Tests.Main` (the `lake test` executable);
a couple of `#guard`s at the bottom kernel-evaluate the compiler at
elaboration time as a smoke layer (possible because the whole pipeline,
HOAS binders included, is total). -/

open LeanLinq

abbrev CustomersS : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table CustomersS := ⟨"Customers"⟩

abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int)]
def orders : Table OrdersS := ⟨"Orders"⟩

/-! ## Pipeline style -/

/-- Bare FROM. -/
def exFrom := Query.from' customers

/-- Project one named column. -/
def exSelectName := Query.from' customers
  |>.select (fun c => ![c["Name"].as "Name"])

/-- Positional projection. -/
def exSelectPositional := Query.from' customers
  |>.select (fun c => ![(c.nth ⟨0, by decide⟩).as "Id"])

/-- WHERE on a string column, then project two columns. -/
def exWhereSelect := Query.from' customers
  |>.where' (fun c => c["Name"] ==. "Nick")
  |>.select (fun c => ![c["Id"].as "Id", c["Age"].as "Age"])

/-- Operator coverage: literals via `OfNat`/`Coe`, `&&.`, `!.`, `<.`. -/
def exOperators := Query.from' customers
  |>.where' (fun c => 18 <. c["Age"] &&. !.(c["Name"] ==. "Bob"))

/-- Arithmetic and concatenation in projections. -/
def exCompute := Query.from' customers
  |>.select (fun c => ![(c["Age"] + 1).as "AgePlus", (c["Name"] ++ "!").as "Loud"])

/-- Identity projection. -/
def exSelectAll := Query.from' customers |>.select (fun c => c)

/-- Stacked WHEREs merge into AND-ed conjuncts of one flat SELECT. -/
def exFilterTwice := Query.from' customers
  |>.where' (fun c => c["Age"] <. 65)
  |>.where' (fun c => 18 <. c["Age"])

/-- `!=.` desugars to NOT (=). -/
def exNotEqual := Query.from' customers
  |>.where' (fun c => c["Id"] !=. 0)

/-! ## LINQ comprehension style -/

/-- Single-table comprehension — compiles to one flat SELECT. -/
def exLinqWhere := query! {
  from c in customers
  where c["Age"] >. 10
  select ![c["Name"].as "Name"]
}

/-- Nested `from`s are the cross product; with a join condition this is the
classic LINQ join, still one flat SELECT. -/
def exLinqJoin := query! {
  from c in customers
  from o in orders
  where c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "Name", o["OrderId"].as "OrderId"]
}

/-- Row append keeps all columns of both sides. -/
def exLinqAppend := query! {
  from c in customers
  from o in orders
  select c ++ o
}

/-- Multiple `where` clauses become AND-ed conjuncts. -/
def exLinqTwoWhere := query! {
  from c in customers
  where c["Age"] >. 10
  where c["Name"] ==. "Nick"
  select ![c["Id"].as "Id"]
}

/-- A pipeline query as a `from` source — inlined into the enclosing
comprehension by normalization. -/
def exLinqSub := query! {
  from c in (Query.from' customers |>.where' (fun r => 18 <. r["Age"]))
  select ![c["Name"].as "Name"]
}

/-! ## Elaboration-time smoke checks (kernel-evaluate the compiler). -/

#guard exFrom.toSql.sql == "SELECT c0.Id AS Id, c0.Name AS Name, c0.Age AS Age FROM Customers AS c0"
#guard exLinqJoin.toSql ==
  { sql := "SELECT c0.Name AS Name, c1.OrderId AS OrderId FROM Customers AS c0, Orders AS c1 WHERE (c0.Id = c1.CustomerId)",
    params := #[] }

/-! ## Negative tests: these must NOT elaborate. -/

#check_failure fun (c : Row CustomersS) => c["Nmae"]               -- misspelled column
#check_failure fun (c : Row CustomersS) => c["Id"] ==. c["Name"]   -- int vs string
#check_failure fun (c : Row CustomersS) => c["Name"] + c["Name"]   -- + on strings
