import LeanLinq

/-! # Example schemas and queries

The golden assertions live in `Tests.Main` (the `lake test` executable);
a couple of `#guard`s at the bottom kernel-evaluate the compiler and the
evaluator at elaboration time as a smoke layer (possible because the whole
pipeline, HOAS binders included, is total).

Queries here are pinned to a concrete context (`BasicCtx`) because they feed
`#guard`s directly; the main test corpus stays context-polymorphic. -/

open LeanLinq

abbrev CustomersS : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table "Customers" CustomersS := ⟨⟩

abbrev OrdersS : Schema := [("OrderId", .int), ("CustomerId", .int)]
def orders : Table "Orders" OrdersS := ⟨⟩

abbrev BasicCtx : Ctx := { tables := [("Customers", CustomersS), ("Orders", OrdersS)] }

/-! ## Pipeline style -/

/-- Bare FROM. -/
def exFrom := Query.from' (ts := BasicCtx) customers

/-- Project one named column. -/
def exSelectName := Query.from' (ts := BasicCtx) customers
  |>.select (fun c => ![c["Name"].as "Name"])

/-- Positional projection. -/
def exSelectPositional := Query.from' (ts := BasicCtx) customers
  |>.select (fun c => ![(c.nth ⟨0, by decide⟩).as "Id"])

/-- WHERE on a string column, then project two columns. -/
def exWhereSelect := Query.from' (ts := BasicCtx) customers
  |>.where' (fun c => c["Name"] ==. "Nick")
  |>.select (fun c => ![c["Id"].as "Id", c["Age"].as "Age"])

/-- Operator coverage: literals via `OfNat`/`Coe`, `&&.`, `!.`, `<.`. -/
def exOperators := Query.from' (ts := BasicCtx) customers
  |>.where' (fun c => 18 <. c["Age"] &&. !.(c["Name"] ==. "Bob"))

/-- Arithmetic and concatenation in projections. -/
def exCompute := Query.from' (ts := BasicCtx) customers
  |>.select (fun c => ![(c["Age"] + 1).as "AgePlus", (c["Name"] ++ "!").as "Loud"])

/-- Identity projection. -/
def exSelectAll := Query.from' (ts := BasicCtx) customers |>.select (fun c => c)

/-- Stacked WHEREs merge into AND-ed conjuncts of one flat SELECT. -/
def exFilterTwice := Query.from' (ts := BasicCtx) customers
  |>.where' (fun c => c["Age"] <. 65)
  |>.where' (fun c => 18 <. c["Age"])

/-- `!=.` desugars to NOT (=). -/
def exNotEqual := Query.from' (ts := BasicCtx) customers
  |>.where' (fun c => c["Id"] !=. 0)

/-! ## LINQ comprehension style -/

/-- Single-table comprehension — compiles to one flat SELECT. -/
def exLinqWhere := (query! {
  from c in customers
  where c["Age"] >. 10
  select ![c["Name"].as "Name"]
} : Query BasicCtx _)

/-- Nested `from`s are the cross product; with a join condition this is the
classic LINQ join, still one flat SELECT. -/
def exLinqJoin := (query! {
  from c in customers
  from o in orders
  where c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "Name", o["OrderId"].as "OrderId"]
} : Query BasicCtx _)

/-- Row append keeps all columns of both sides. -/
def exLinqAppend := (query! {
  from c in customers
  from o in orders
  select c ++ o
} : Query BasicCtx _)

/-- Multiple `where` clauses become AND-ed conjuncts. -/
def exLinqTwoWhere := (query! {
  from c in customers
  where c["Age"] >. 10
  where c["Name"] ==. "Nick"
  select ![c["Id"].as "Id"]
} : Query BasicCtx _)

/-- A pipeline query as a `from` source — inlined into the enclosing
comprehension by normalization. -/
def exLinqSub := (query! {
  from c in (Query.from' (ts := BasicCtx) customers |>.where' (fun r => 18 <. r["Age"]))
  select ![c["Name"].as "Name"]
} : Query BasicCtx _)

/-! ## Elaboration-time smoke checks (kernel-evaluate the compiler). -/

#guard exFrom.toSql.sql ==
  "SELECT \"a0\".\"Id\" AS \"Id\", \"a0\".\"Name\" AS \"Name\", \"a0\".\"Age\" AS \"Age\" FROM \"Customers\" \"a0\""
#guard exLinqJoin.toSql ==
  { sql := "SELECT \"a0\".\"Name\" AS \"Name\", \"a1\".\"OrderId\" AS \"OrderId\" FROM \"Customers\" \"a0\", \"Orders\" \"a1\" WHERE (\"a0\".\"Id\" = \"a1\".\"CustomerId\")",
    params := #[] }

/-! ## Executable semantics: `Query.run` kernel-evaluates too. -/

def demoEnv : TableEnv BasicCtx.tables :=
  .cons [.cons (some 1) (.cons (some "Nick") (.cons (some 30) .nil)),
         .cons (some 2) (.cons (some "Ada") (.cons (some 17) .nil))] <|
  .cons [] .nil

#guard ((Query.from' (ts := BasicCtx) customers
  |>.where' (fun c => 18 <. c["Age"])
  |>.select (fun c => ![c["Name"].as "Name"])).run demoEnv).length == 1

/-! ## Negative tests: these must NOT elaborate. -/

#check_failure fun (c : Row BasicCtx CustomersS) => c["Nmae"]             -- misspelled column
#check_failure fun (c : Row BasicCtx CustomersS) => c["Id"] ==. c["Name"] -- int vs string
#check_failure fun (c : Row BasicCtx CustomersS) => c["Name"] + c["Name"] -- + on strings
-- a table outside the context: no HasTable instance, so the query is untypeable
#check_failure (Query.from' (⟨⟩ : Table "Ghost" CustomersS) : Query BasicCtx CustomersS)
-- a parameter outside the context: no HasParam instance — unbound is untypeable,
-- not silently NULL
#check_failure (SqlExpr.param (ts := BasicCtx) "ghost")
