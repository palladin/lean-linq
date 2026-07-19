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
  [("Id", .long), ("ProductName", .string), ("Price", .null .decimal),
   ("CreatedDate", .null .dateTime), ("UniqueId", .null .guid)]
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

def adults' := query! PlayCtx {
  from c in customers
  where 18 <. c["Age"] &&. c["IsActive"] ==. true
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}

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

def spending' := query! PlayCtx {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Name"].as "Name", (a.sum o["Amount"]).as "Total"]
  limit 10
}

#eval (spending'.toSql .sqlite).sql

def cheapProducts := query! PlayCtx {
  from p in products
  where p["Price"] <. 100.00 ||. p["Price"].isNull
  orderBy p["Price"].asc
  select ![p["ProductName"].as "Name", p["Price"].as "Price"]
}

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

`Query.run : Query ts s → TableEnv ts.tables → ParamEnv ts.params →
Except EvalError (List (Values s))` is the library's
denotational semantics: a typed in-memory evaluator over the exact query
value that compiles to SQL (the integration suite differential-tests all
three engines against it). Table resolution happened at elaboration, so a
`TableEnv PlayCtx` is all it takes — no names, no failure modes. -/

def demoEnv : TableEnv PlayCtx.tables :=
  .cons  -- customers
    [.cons 1 (.cons 25 (.cons "John Doe" (.cons true .nil))),
     .cons 2 (.cons 30 (.cons "Jane Smith" (.cons true .nil))),
     .cons 3 (.cons 16 (.cons "Minor User" (.cons false .nil)))] <|
  .cons  -- orders
    [.cons 1 (.cons 1 (.cons 1 (.cons 500 .nil))),
     .cons 2 (.cons 2 (.cons 1 (.cons 300 .nil)))] <|
  .cons [] .nil  -- products

#eval adults.run demoEnv    -- Except.ok [(2, "Jane Smith"), (1, "John Doe")]
#eval (adults'.run demoEnv).toOption == (adults.run demoEnv).toOption   -- twins agree
#eval spending.run demoEnv  -- joins/grouping run in memory as well

-- NULL is data; exceptional conditions are the explicit error channel:
#eval (Query.from' (ts := PlayCtx) customers
  |>.select (fun c => ![(c["Age"] / 0).as "Boom"])).run demoEnv
-- Except.error LeanLinq.EvalError.divByZero

/-! ## Db — round-budgeted database programs

The round-trip bill is a type index: `fetch` costs 1, independent `seq`s
share rounds (`max`), data-dependent `bind`s add, and the per-row loop
`for x in xs do …` costs exactly `xs.length` bodies' worth. `exec`
demands a budget and a proof `r ≤ budget` — `by decide` for closed
grades, `omega` for computed budgets. The one thing with no proof is a
loop over rows a fetch *inside the same program* returned — classic
N+1 — which never elaborates; the batched door (`fetchFor`, one
`IN (…)` statement) costs 1 for any collection size. -/

def spendersReport : Db PlayCtx 2 (Nat × Nat) := db! {
  let parents ← adults.execQuery
  let ids := parents.filterMap fun v => (v.get? "Id" .long).bind id
  let children ← .fetchFor ids fun ks =>
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"].inValues ks)
  return (parents.length, children.length)
}

#eval spendersReport.exec 2 demoEnv   -- Except.ok (2, 2) — 1+1 rounds, any N

/- The per-row loop *is* expressible — explicitly, over data you already
hold (a parameter, a literal, a previous result). `for x in xs do …`
carries the *exact* dynamic round count in the type, and the door takes
a proof — `by decide` once the list is a literal, `by omega` for a
computed budget. -/
def ordersFor (ids : List Int) :
    Db PlayCtx (Grade.nat ids.length) (List Nat) := db! {
  let waves ← for k in ids do
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. SqlExpr.long k)
      |>.execQuery
  return waves.map (·.length)
}
-- the annotation states `ids.length` even though the loop's raw index
-- is `1 * ids.length` (the combinator's exact arithmetic): `db!`
-- wraps its expansion in `withBill`, and the pointwise tactic closes
-- the gap

#eval (ordersFor [1, 2]).exec 2 demoEnv   -- Except.ok [1, 1] — grade 2

/- And the per-row loop over *just-fetched* rows — with the fetch bounded.
`fetchLimit q n` puts the bound in the type (`{xs // xs.length ≤ n}`,
realized by `LIMIT n` — a theorem about the semantics,
`Query.run_limit_length_le`), and looping over `parents.val` fuses into
`Db.forRows`, whose budget proof comes from the refinement. The
bound can itself be a parameter: the grade is `n + 1` — one round for
the parents, at most `n` for the fan-out — and `p["Id"]` embeds the
fetched cell as a typed literal. N+1 written deliberately: the bounded
query pays for the fan-out. -/
def topSpendersDetail (n : Nat) :
    Db PlayCtx (Grade.nat n + 1) (List (String × Nat)) := db! {
  let spenders ← adults.fetchLimit n
  let report ← for s in spenders.val do
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. s["Id"])
      |>.execQuery
      |>.map (fun orders => (s["Name"], orders.length))
  return report
}

#eval (topSpendersDetail 5).exec 6 demoEnv
-- Except.ok [("Jane Smith", 1), ("John Doe", 1)] — grade 5+1, by decide

-- and under a *symbolic* budget the door takes a proof, for every n:
example (n : Nat) : Except EvalError (List (String × Nat)) :=
  (topSpendersDetail n).exec (n + 1) demoEnv .nil none
    (by simpa only [Grade.ofNat_eq_nat, Grade.nat_add]
      using Grade.le_refl (Grade.nat (n + 1)))

/- The same report in **two rounds flat**, any number of spenders: the
batched door replaces the per-row loop — every order arrives in one
`IN (…)` statement and the counting happens in Lean. Note the brackets
playing both roles: `o["CustomerId"].inValues ks` embeds into SQL,
`o["CustomerId"] == s["Id"]` compares fetched values. -/
def topSpendersDetail2 (n : Nat) :
    Db PlayCtx 2 (List (String × Nat)) := db! {
  let spenders ← adults.fetchLimit n
  let allOrders ← .fetchFor (spenders.val.map (·["Id"])) fun ks =>
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"].inValues ks)
  return spenders.val.map fun s =>
    (s["Name"], (allOrders.filter (fun o => o["CustomerId"] == s["Id"])).length)
}

#eval (topSpendersDetail2 5).exec 2 demoEnv
-- Except.ok [("Jane Smith", 1), ("John Doe", 1)] — grade 1 + 1, any n

/- "All the records" used to be two phases in `Except` — you could not
know the fan-out before asking, so no single program could promise a
round count. **Now it can**: `fetchCount`'s spec says the answer fits
`gcard`, and that spec pays the loop's budget — the fully dynamic
"count, then loop that many times" is ONE program, priced statically
in the database's own terms: one round to ask, one for the page, at
most `|customers|` for the fan-out. -/
def allSpendersDetail :
    Db PlayCtx (customers.size + 2) (List (String × Nat)) :=
  DbP.withBound
    (FreerD.weaken (Query.countWp_bill_bind (q := adults))
      (FreerD.bindS (Query.fetchCountP adults) (fun n => topSpendersDetail n)))

-- collapsed at demoEnv (3 customers): budget 5 suffices, 4 does not…
#guard (allSpendersDetail.execWithin 5 demoEnv).toOption
    == some [("Jane Smith", 1), ("John Doe", 1)]
-- …and no closed budget dominates |customers| + 2:
#check_failure (allSpendersDetail.exec 1000 demoEnv)

/- Under-budgeting the loop is caught at elaboration —
`(ordersFor [1, 2]).exec 1 demoEnv` fails `by decide` (grade 2 > 1). An
*unbounded* fetch gives the loop no proof to fuse with, so it still never
elaborates; and the fully implicit N+1 is rejected too:
`mapM` needs a `Monad` instance, and `Db` cannot have one, because
hiding the grade inside a fixed `m : Type → Type` would blind the budget
check. The checker below verifies this fails to elaborate. -/
#check_failure fun (ids : List Int) => db! {
  let parents ← .fetch adults
  let children ← ids.mapM fun k => Db.fetch
    (Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. SqlExpr.long k))
  return (parents.length, children.length)
}

/-! ## Symbolic grades — round budgets in the database's own terms

`topSpendersDetail n` needs its `n` because a closed bound must be a
numeral: to price the per-parent loop you must cap the parents. Grades
remove the dilemma — they are max-plus polynomials over table sizes,
so the natural unlimited program carries the honest price **in its
type**: `customers.size + 1` — one round for the parents, one per
actual customer. `exec` still refuses it (no number dominates
`|customers| + 1`); `execWithin` collapses the grade against the
model's own sizes and checks there; `execAll` runs unchecked. -/

/-- The unlimited report, priced symbolically — no budget argument, no
LIMIT, the type says exactly what it costs: `for s in adults do` loops
over the *query*, and the loop's grade is the query's own symbolic
card. -/
def topSpendersDetailAll :
    Db PlayCtx (customers.size + 1) (List (String × Nat)) := db! {
  let report ← for s in adults do
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. s["Id"])
      |>.execQuery
      |>.map (fun orders => (s["Name"], orders.length))
  return report
}

-- the grade collapses against the model's sizes: demoEnv holds 3
-- customers, so the price is 4 — an upper bound (guards only remove:
-- just 2 of the 3 are adults, so the program performs 1 + 2 = 3 rounds)
#guard (customers.size + 1).eval (TableEnv.sizes demoEnv) == 4
#guard ((topSpendersDetailAll.runCount ⟨demoEnv, .nil, none⟩).toOption.map (·.2))
    == some 3
-- the sized door checks the collapsed grade, then runs …
#guard (topSpendersDetailAll.execWithin 4 demoEnv).toOption
    == some [("Jane Smith", 1), ("John Doe", 1)]
-- … and refuses an insufficient budget at this database's sizes
#guard (topSpendersDetailAll.execWithin 3 demoEnv).toOption == none
-- the closed door refuses the symbolic grade statically — no number
-- bounds |customers| + 1:
#check_failure (topSpendersDetailAll.exec 1000 demoEnv)

/-- The same program, spelled **fetch first, then loop over the rows**:
`spenders` is a plain `List` — no subtype, no restated bound — and the
loop is still priced, because `fetch`'s postcondition (rows fit
`adults.gcard` at every σ) rides into the loop's budget evidence
(`forFetched`, fused from the adjacent bind + `for`). The two spellings
carry the same type: the price is the program's, not the sugar's. -/
def topSpendersDetailAll' :
    Db PlayCtx (customers.size + 1) (List (String × Nat)) := db! {
  let spenders ← adults.execQuery
  let report ← for s in spenders do
    Query.from' (ts := PlayCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. s["Id"])
      |>.execQuery
      |>.map (fun orders => (s["Name"], orders.length))
  return report
}

-- same rounds, same rows, same doors as the loop-over-query spelling:
#guard ((topSpendersDetailAll'.runCount ⟨demoEnv, .nil, none⟩).toOption.map (·.2))
    == some 3
#guard (topSpendersDetailAll'.execWithin 4 demoEnv).toOption
    == some [("Jane Smith", 1), ("John Doe", 1)]
#check_failure (topSpendersDetailAll'.exec 1000 demoEnv)

/-- Program-level reasoning, absorbed into the door: the refined `fetch`
carries in its *type* what used to need a run-hypothesis — the ten-slot
page fits by projection, zero proof work, over every environment and
every engine that survives the clamp. -/
example {σ : String → Nat}
    {xs : List (Values [("Id", SqlType.long), ("Name", SqlType.string)])}
    (hxs : xs.length ≤ (Query.gcard (adults.limit 10)).eval σ) :
    xs.length ≤ 10 :=
  fetchPage_fits adults 10 hxs

/- And the hypothesis is *handed over* by the verified model door:
`runWithP` runs the same tree `runWith` runs, but its `fetch` arm
constructs the contract via `run_gcard` instead of promising it — the
result arrives with the spec's strongest-post reading (`Wp.sp`) at this
run's sizes and op count, `sp_fetch` turns it back into the pointwise
contract, and the page bound is a theorem of the run, no check
anywhere. -/
#guard ((((adults.limit 10).execQuery).runWithP .nil none demoEnv).toOption.map
    (·.val.1.length)) == some 2

example {res : {p : List (Values [("Id", SqlType.long), ("Name", SqlType.string)])
        × TableEnv PlayCtx.tables × Nat //
      ∀ k₀, Wp.sp (dbWp (DbE.fetch (adults.limit 10)))
        p.1 (TableEnv.sizes demoEnv) k₀ (TableEnv.sizes p.2.1) (k₀ + p.2.2)}}
    (_h : ((adults.limit 10).execQuery).runWithP .nil none demoEnv = .ok res) :
    res.val.1.length ≤ 10 :=
  fetchPage_fits adults 10
    (res.property 0 (fun ys _ _ => ys.length ≤ _) (fun _ hb => hb))

-- **count adequacy** — the bill in the type is a theorem of the run:
-- the certified door hands back the op count, provably ≤ the bill at
-- the model's own sizes (`customers.size + 1` collapses to 4 here)
#guard ((topSpendersDetailAll.runWithP .nil none demoEnv).toOption.map
    (·.val.2.2)) == some 3
example {res} (h : topSpendersDetailAll.runWithP .nil none demoEnv = .ok res) :
    res.val.2.2 ≤ (customers.size + 1).eval (TableEnv.sizes demoEnv) :=
  DbP.runWithP_count_le h

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

/-- Writes are monadic now — one program, reads and writes, one bill:
insert a customer, then ask how many there are. Grade 2 = two database
operations; the count comes back through `fetchCount`. -/
def growThenCount : Db PlayCtx 2 Nat := db! {
  let _ins ← customers.insert (ts := PlayCtx)
    |>.value "Id" 100 |>.value "Age" 30
    |>.value "Name" "Ada" |>.value "IsActive" true
    |>.execInsert
  let n ← Query.fetchCount (Query.from' (ts := PlayCtx) customers)
  return n
}

#guard (growThenCount.exec 2 demoEnv).toOption == some 4  -- 3 seeded + 1

-- writes report their affected counts — engine-truthful over the wire
-- (sqlite3_changes / PQcmdTuples / DBCOUNT), exact in the model:
#guard ((db! {
  let k ← customers.delete (ts := PlayCtx) |>.execDelete
  return k
}).exec 1 demoEnv).toOption == some 3   -- unconditional DELETE clears all 3

/-- **The write-side N+1, written deliberately** — one SELECT, then one
INSERT per row. The loop over just-fetched rows fuses through
`forFetched`, its body is a write, and the type bills the truth:
`customers.size + 1` database operations. `exec` refuses it statically
(no number dominates a table symbol); the sized door collapses and
checks. This is the program `INSERT … SELECT` will collapse to
**one** operation — the write-side `fetchFor`. -/
def duplicateAll : Db PlayCtx (customers.size + 1) Nat := db! {
  let rows ← Query.from' (ts := PlayCtx) customers |>.execQuery
  let ks ← for r in rows do
    customers.insert (ts := PlayCtx)
      |>.value "Id" r["Id"] |>.value "Age" r["Age"]
      |>.value "Name" r["Name"] |>.value "IsActive" r["IsActive"]
      |>.execInsert
  return ks.sum
}

-- 3 rows fetched, 3 single-row inserts, each affecting 1: Σ = 3 —
-- at demoEnv's sizes the bill is 1 + 3 = 4, and 3 rounds is refused
#guard (duplicateAll.execWithin 4 demoEnv).toOption == some 3
#check_failure (duplicateAll.exec 1000 demoEnv)

/-- **The collapse**: the same copy as ONE operation — the engine moves
the rows. `INSERT … SELECT` is the write-side `fetchFor`: grade 1 for
any table size, affected = the source's row count, and the spec bounds
both the count and the growth by the source query's own symbolic card
(`run_gcard` at the door). `duplicateAll` above: `customers.size + 1`.
This: 1. -/
def duplicateAllFast : Db PlayCtx 1 Nat := db! {
  let k ← customers.insertFrom (Query.from' (ts := PlayCtx) customers)
    |>.execInsertSelect
  return k
}

#guard (duplicateAllFast.exec 1 demoEnv).toOption == some 3
#eval (customers.insertFrom (Query.from' (ts := PlayCtx) customers)
  |>.toSql .postgres).sql
-- "INSERT INTO \"customers\" (\"Id\", \"Age\", \"Name\", \"IsActive\") SELECT …"

/-- And the write's spec *pays*: through insert's interval spec composed
with the count's bound (the state-wp threading them), the count comes
back **provably ≤ old size + 1** — a theorem of this run, before
looking at the number. -/
example {res : {p : Nat × TableEnv PlayCtx.tables × Nat //
      ∀ k₀, Wp.sp _ p.1 (TableEnv.sizes demoEnv) k₀ (TableEnv.sizes p.2.1)
        (k₀ + p.2.2)}}
    (_h : DbP.runWithP .nil none
        (FreerD.bindS (DbP.insert (customers.insert (ts := PlayCtx)
          |>.value "Id" 100 |>.value "Age" 30
          |>.value "Name" "Ada" |>.value "IsActive" true))
          (fun _ => Query.fetchCountP (Query.from' (ts := PlayCtx) customers)))
        demoEnv = .ok res) :
    res.val.1 ≤ TableEnv.sizes demoEnv "customers" + 1 := by
  refine res.property 0
    (fun n _ _ => n ≤ TableEnv.sizes demoEnv "customers" + 1) ?_
  intro σ' _ _ hhi n hn
  have hg : (Query.gcard (Query.from' (ts := PlayCtx) customers)).eval σ'
      = σ' "customers" := by
    simp only [gradeEvalNorm, Nat.mul_one]
  rw [hg] at hn
  omega

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
