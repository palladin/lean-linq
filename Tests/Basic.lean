import LeanLinq

/-! # Example schemas, queries, and elaboration-time smoke tests

The golden assertions live in `Tests.Main` (the `lake test` executable); the
`#guard`s here are an elaboration-time smoke layer over the same queries. -/

open LeanLinq

abbrev CustomersS : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table CustomersS := ⟨"Customers"⟩

abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int)]
def orders : Table OrdersS := ⟨"Orders"⟩

/-- Idris `example0`: bare FROM. -/
def exFrom := Query.from' customers

/-- Idris `example1`: project one named column. -/
def exSelectName := Query.from' customers
  |>.select (fun c => [c["Name"].as "Name"])

/-- Idris `example2`: positional projection. -/
def exSelectPositional := Query.from' customers
  |>.select (fun c => [(c.nth ⟨0, by decide⟩).as "Id"])

/-- Idris `example3`: WHERE on a string column, then project two columns. -/
def exWhereSelect := Query.from' customers
  |>.filter (fun c => c["Name"] ==. "Nick")
  |>.select (fun c => [c["Id"].as "Id", c["Age"].as "Age"])

/-- Operator coverage: literals via `OfNat`/`Coe`, `&&.`, `!.`, `<.`. -/
def exOperators := Query.from' customers
  |>.filter (fun c => 18 <. c["Age"] &&. !.(c["Name"] ==. "Bob"))

/-- Arithmetic and concatenation in projections. -/
def exCompute := Query.from' customers
  |>.select (fun c => [(c["Age"] + 1).as "AgePlus", (c["Name"] ++ "!").as "Loud"])

/-- Product with an explicit projection over both sides. -/
def exProduct := (Query.from' customers).product (Query.from' orders)
  (fun c o => [c["Name"].as "Name", o["OrderId"].as "OrderId"])

/-- Join-style: product, rename into a flat schema, then filter on it. -/
def exJoin := (Query.from' customers).product (Query.from' orders)
    (fun c o => [c["Id"].as "CustId", c["Name"].as "Name",
                 o["CustomerId"].as "OrderCustId", o["OrderId"].as "OrderId"])
  |>.filter (fun r => r["CustId"] ==. r["OrderCustId"])

/-- Product keeping all columns of both sides via row append. -/
def exProductAppend := (Query.from' customers).product (Query.from' orders)
  (fun c o => c ++ o)

/-- Identity projection. -/
def exSelectAll := Query.from' customers |>.select (fun c => c)

/-- Stacked WHEREs nest as derived tables. -/
def exFilterTwice := Query.from' customers
  |>.filter (fun c => c["Age"] <. 65)
  |>.filter (fun c => 18 <. c["Age"])

/-- `!=.` desugars to NOT (=). -/
def exNotEqual := Query.from' customers
  |>.filter (fun c => c["Id"] !=. 0)

-- Elaboration-time smoke checks (kernel-evaluates the whole compiler).
#guard exFrom.toSql.sql == "SELECT * FROM Customers"
#guard exWhereSelect.toSql ==
  { sql := "SELECT c1.Id AS Id, c1.Age AS Age FROM (SELECT * FROM (SELECT * FROM Customers) AS c0 WHERE (c0.Name = @p0)) AS c1",
    params := #[("@p0", .string "Nick")] }

-- Negative tests: these must NOT elaborate.
#check_failure fun (c : Row CustomersS) => c["Nmae"]                -- misspelled column
#check_failure fun (c : Row CustomersS) => c["Id"] ==. c["Name"]   -- int vs string
#check_failure fun (c : Row CustomersS) => c["Name"] + c["Name"]   -- + on strings
