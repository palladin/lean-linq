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
  |>.select (fun c => ![c["Name"].as "Name"])).run demoEnv
    |>.toOption.map (·.length)) == some 1

/-! ## DbFetch: the round budget is in the type — N+1 is unprovable.

The per-row loop *is* writable (Lean is dependently typed: its grade is
`ks.length`), but `exec`'s budget obligation is only auto-dischargeable
for closed grades. A runtime length is provable exactly when the
collection is in scope at the door — bound it, or compute the budget
from it; rows fetched *inside* the program admit no proof at all. -/

def ordersOf (k : Int) := Query.from' (ts := BasicCtx) orders
  |>.where' (fun o => o["CustomerId"] ==. SqlExpr.int k)

def perRow : (ks : List Int) → DbFetch BasicCtx ks.length (List (List (Values OrdersS)))
  | [] => .pure []
  | k :: ks => (perRow ks).bind fun acc =>
      (DbFetch.fetch (ordersOf k)).map (· :: acc)

/-- Batched programs have closed grades: `1 + 1`, discharged silently
(`fetch!` is do-sugar over the graded combinators — grades stay visible). -/
def batched : DbFetch BasicCtx 2 (Nat × Nat) := fetch! {
  let cs ← .fetch (Query.from' (ts := BasicCtx) customers)
  let os ← .fetch (Query.from' (ts := BasicCtx) orders)
  return (cs.length, os.length)
}

#guard (batched.exec 2 demoEnv |>.toOption) == some (2, 0)

/-- A program whose grade is itself a parameter: `n` sampling rounds. -/
def sampleRounds : (n : Nat) → DbFetch BasicCtx n (List Nat)
  | 0 => .pure []
  | n + 1 => (sampleRounds n).bind fun acc =>
      (DbFetch.fetch (Query.from' (ts := BasicCtx) customers)).map
        fun cs => cs.length :: acc

/-- Symbolic grade under a symbolic budget: `n ≤ 2 * n + 1` is a theorem,
so `omega` discharges it for *every* `n` — the door demands proof, not
literals. Contrast N+1's `ids.length ≤ 8`, which is simply not provable. -/
example (n : Nat) : Except EvalError (List Nat) :=
  (sampleRounds n).exec (2 * n + 1) demoEnv .nil none (by omega)

/-- Bounded fan-out is allowed — proof-carrying: `take 3` makes
`(ids.take 3).length ≤ 8` provable, and the caller supplies the proof. -/
example (ids : List Int) : Except EvalError (List (List (Values OrdersS))) :=
  (perRow (ids.take 3)).exec 8 demoEnv .nil none
    (by rw [List.length_take]; omega)

/-- `for x in xs do` is that idiom as sugar — the per-row loop with the
exact grade `1 * ks.length` in the type: closed lists close it
(`by decide` sees `1 * 2 = 2`), parameter lists leave a symbolic grade
the caller proves at the door (see below). -/
def perRowAll (ks : List Int) := fetch! {
  let waves ← for k in ks do .fetch (ordersOf k)
  return waves.map (·.length)
}

#guard ((perRowAll [1, 2]).exec 2 demoEnv |>.toOption) == some [0, 0]

/-- Symbolic dynamic grade under a computed budget: the obligation
`1 * ks.length + 0 ≤ ks.length` is a theorem, so `omega` closes it for
every `ks` — the rounds are visible, priced, and proved, not hidden. -/
example (ks : List Int) : Except EvalError (List Nat) :=
  (perRowAll ks).exec ks.length demoEnv .nil none (by omega)

/-- The bounded post-fetch loop: `fetchLimit` puts the row bound in the
type (`{xs // xs.length ≤ 3}` — `LIMIT` really limits, by
`Query.run_limit_length_le`), and looping over `.val` fuses into
`DbFetch.forRows`, whose budget proof is the refinement itself. Grade
`1 + 1 * 3 = 4`, closed, silent — and the two-row table exercises the
loop-shorter-than-bound path. -/
def perRowBounded : DbFetch BasicCtx 4 (List Nat) := fetch! {
  let parents ← Query.from' (ts := BasicCtx) customers |>.fetchLimit 3
  let waves ← for p in parents.val do
    Query.from' (ts := BasicCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. p["Id"])
      |>.fetch
  return waves.map (·.length)
}

#guard (perRowBounded.exec 4 demoEnv |>.toOption) == some [0, 0]

/-! ## Negative tests: these must NOT elaborate. -/

#check_failure fun (c : Row BasicCtx CustomersS) => c["Nmae"]             -- misspelled column
#check_failure fun (c : Row BasicCtx CustomersS) => c["Id"] ==. c["Name"] -- int vs string
#check_failure fun (c : Row BasicCtx CustomersS) => c["Name"] + c["Name"] -- + on strings
-- a table outside the context: no HasTable instance, so the query is untypeable
#check_failure (Query.from' (⟨⟩ : Table "Ghost" CustomersS) : Query BasicCtx CustomersS)
-- a parameter outside the context: no HasParam instance — unbound is untypeable,
-- not silently NULL
#check_failure (SqlExpr.param (ts := BasicCtx) "ghost")
-- classic N+1: one fetch per row of a runtime collection — the grade is
-- `ids.length`, the budget obligation is undischargeable, no proof exists
#check_failure fun (ids : List Int) => (perRow ids).exec 8 demoEnv
-- the fetch! sugar changes nothing: a dependent-grade sub-program still
-- leaves an obligation with free variables at the door
#check_failure fun (ids : List Int) => (fetch! {
  let rows ← perRow ids
  return rows.length
}).exec 8 demoEnv
-- a symbolic loop under a *fixed* budget leaves a free variable in the
-- obligation (`1 * ids.length + 0 ≤ 8`) — no proof, no run
#check_failure fun (ids : List Int) => (perRowAll ids).exec 8 demoEnv
-- under-budgeting a closed loop is caught the same way: grade 2 > 1
#check_failure ((perRowAll [1, 2]).exec 1 demoEnv)
-- an *unbounded* fetch gives the loop no refinement to fuse with — no
-- `.val`, no bound, and the raw loop's grade would mention the fetched
-- value, which `bind` cannot type
#check_failure (fetch! {
  let parents ← Query.from' (ts := BasicCtx) customers |>.fetch
  let waves ← for p in parents.val do
    Query.from' (ts := BasicCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. p["Id"])
      |>.fetch
  return waves.map (·.length)
} : DbFetch BasicCtx 4 (List Nat))
-- under-budgeting the bounded fan-out: grade 4 > 3
#check_failure (perRowBounded.exec 3 demoEnv)
-- and `for … do` cannot follow a fetch inside one program:
-- the loop's grade would mention the fetched rows, which `bind` cannot
-- type — the N+1 rejection is structural, not a lint
#check_failure (fetch! {
  let cs ← .fetch (Query.from' (ts := BasicCtx) customers)
  let ids := cs.filterMap fun v => (v.get? "Id" .int).bind id
  let waves ← for k in ids do .fetch (ordersOf k)
  return waves.length
}).exec 8 demoEnv
