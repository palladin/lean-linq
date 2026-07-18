import LeanLinq
import Tests.QueriesC
import Tests.StatementsT
import Tests.Seed
import Tests.SeedSql

/-! # Engine-agnostic native-driver sweep

Runs every registered case through a native driver (`DriverOps`) and
compares against the evaluator **at the `Values s` level, cell for cell** —
strings appear only in failure messages. Statements run inside rolled-back
transactions and are verified with a typed read-back query against
`apply`'s in-memory result. Instantiated by `Tests/SqliteDriverT.lean`,
`Tests/PgDriverT.lean`, and `Tests/MssqlDriverT.lean`. -/

open LeanLinq

namespace TQ

/-- What a native driver must provide to be swept. -/
structure DriverOps where
  query : {s : Schema} → Query TestCtx s → IO (List (Values s))
  queryCell : {t : SqlPrim} → {n : Bool} → ScalarQuery TestCtx ⟨t, n⟩ → IO (Nullable t)
  execIns : {n : String} → {s : Schema} → InsertStmt TestCtx n s → IO Unit
  execUpd : {n : String} → {s : Schema} → UpdateStmt TestCtx n s → IO Unit
  execDel : {n : String} → {s : Schema} → DeleteStmt TestCtx n s → IO Unit
  execRaw : String → IO Unit
  /-- Transaction bracket for statement cases; T-SQL spells these
  `BEGIN TRAN`/`ROLLBACK TRAN`. -/
  begin : String := "BEGIN"
  rollback : String := "ROLLBACK"

/-- Rendering is for *messages only*; comparison is typed. -/
def showRows (rows : List (Values s)) : String :=
  String.intercalate " | " (rows.map fun v => String.intercalate ", " (cellsOf v))

def checkRows (name what : String) (ordered : Bool)
    (driver expected : List (Values s)) : IO Bool := do
  let (d, e) :=
    if ordered then (driver, expected)
    else (driver.mergeSort rowLe, expected.mergeSort rowLe)
  if d == e then
    pure true
  else do
    IO.eprintln s!"DRIVER MISMATCH {name} ({what})"
    IO.eprintln s!"  driver:    {showRows d}"
    IO.eprintln s!"  evaluator: {showRows e}"
    pure false

/-- Verify a statement: typed read-back of the whole table (inside the
caller's transaction) against `apply`'s in-memory table. -/
def checkTable {n : String} {s : Schema} (ops : DriverOps) (name : String)
    (inst : HasTable TestCtx.tables n s)
    (applied : Except EvalError (TableEnv TestCtx.tables)) : IO Bool := do
  have : HasTable TestCtx.tables n s := inst
  let got ← ops.query (Query.from' (ts := TestCtx) (⟨⟩ : Table n s))
  match applied with
  | .error e =>
      IO.eprintln s!"EVAL ERROR {name}: {repr e}"
      pure false
  | .ok env' => checkRows name "statement" false got (inst.rows env')

def runCase (ops : DriverOps) (name : String) (c : Case) : IO Bool := do
  match c.payload with
  | .query q => do
      let driver ← ops.query q
      match q.run seedEnv seedParams with
      | .error e =>
          IO.eprintln s!"EVAL ERROR {name}: {repr e}"
          pure false
      | .ok expected => checkRows name "query" c.ordered driver expected
  | .scalar (t := t) sc => do
      let driver ← ops.queryCell sc
      match sc.run seedEnv seedParams with
      | .error e =>
          IO.eprintln s!"EVAL ERROR {name}: {repr e}"
          pure false
      | .ok expected =>
          if cellBeq t driver expected then pure true
          else do
            IO.eprintln s!"DRIVER MISMATCH {name} (scalar)"
            IO.eprintln s!"  driver:    {renderCell t driver}"
            IO.eprintln s!"  evaluator: {renderCell t expected}"
            pure false
  | .ins (inst := inst) i => do
      ops.execRaw ops.begin
      try
        ops.execIns i
        let ok ← checkTable ops name inst (i.apply (inst := inst) seedEnv seedParams)
        pure ok
      finally
        ops.execRaw ops.rollback
  | .upd (inst := inst) u => do
      ops.execRaw ops.begin
      try
        ops.execUpd u
        let ok ← checkTable ops name inst (u.apply (inst := inst) seedEnv seedParams)
        pure ok
      finally
        ops.execRaw ops.rollback
  | .del (inst := inst) d => do
      ops.execRaw ops.begin
      try
        ops.execDel d
        let ok ← checkTable ops name inst (d.apply (inst := inst) seedEnv seedParams)
        pure ok
      finally
        ops.execRaw ops.rollback

/-- Sweep every registered case; returns (passed, failed, skipped). -/
def runSweep (ops : DriverOps) : IO (Nat × Nat × Nat) := do
  let mut failures := 0
  let mut passed := 0
  let mut skipped := 0
  for (name, c) in queryCases ++ twinCases ++ statementCases do
    if skipResults.contains name || crossDialectAllowlist.contains name then
      skipped := skipped + 1
      continue
    if ← runCase ops name c then passed := passed + 1
    else failures := failures + 1
  pure (passed, failures, skipped)

/-- The shared `db!` smoke: a data-dependent two-round program. -/
def spenders : Db TestCtx 2 (Nat × List (Values OrdersS)) := db! {
  let adults ← .fetch (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] >=. SqlExpr.param "minAge"))
  let ids := adults.filterMap fun v => (v.get? "Id" .long).bind id
  let children ← .fetchFor ids fun ks =>
    Query.from' (ts := TestCtx) orders |>.where' (fun o => o["CustomerId"].inValues ks)
  return (adults.length, children)
}

/-- The two-fetch smoke, sequential by design: independence is
applicative structure — retired with `seq`, returning with the free
applicative — so two fetches cost `1 + 1 = 2` in the monad. -/
def bothTables : Db TestCtx 2 (List (Values CustomersS) × List (Values OrdersS)) := db! {
  let cs ← .fetch (Query.from' (ts := TestCtx) customers)
  let os ← .fetch (Query.from' (ts := TestCtx) orders)
  return (cs, os)
}

/-- The shared `for … do` smoke: the per-row loop over an in-hand key
list — exact grade `1 * 3 + 0 = 3`, one sequential fetch per key. -/
def perRowLoop : Db TestCtx 3 (List Nat) := db! {
  let waves ← for k in ([1, 2, 3] : List Int) do
    Query.from' (ts := TestCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. SqlExpr.long k)
      |>.execQuery
  return waves.map (·.length)
}

/-- The bounded post-fetch loop smoke: `fetchLimit` + the `for … .val`
fusion (`Db.forRows`) — grade `1 + 1 * 3 = 4`; parents ordered so
every engine visits the same rows. -/
def boundedFanOut : Db TestCtx 4 (List Nat) := db! {
  let parents ← Query.from' (ts := TestCtx) customers
    |>.orderBy (fun c => [c["Id"].asc])
    |>.fetchLimit 3
  let waves ← for p in parents.val do
    Query.from' (ts := TestCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. p["Id"])
      |>.execQuery
  return waves.map (·.length)
}

/-- The contract-priced fan-out smoke: the LIMIT lives in the query, and
the loop's budget is the fetch's own contract — the closed `gcard` of a
limited query. Plain rows, plain `for`, grade `1 + 1 * 3 = 4` with no
bound restated. -/
def cardFanOut : Db TestCtx 4 (List Nat) := db! {
  let parents ← Query.from' (ts := TestCtx) customers
    |>.orderBy (fun c => [c["Id"].asc])
    |>.limit 3
    |>.execQuery
  let waves ← for p in parents do
    Query.from' (ts := TestCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. p["Id"])
      |>.execQuery
  return waves.map (·.length)
}

/-- The whole-table fan-out smoke: no LIMIT anywhere, and the price is
symbolic — `|customers| + 1`. No closed budget dominates a table symbol,
so every budgeted door refuses it statically; the per-driver All doors
run it unchecked. -/
def wholeTableFanOut : Db TestCtx (customers.size + 1) (List Nat) := db! {
  let parents ← Query.from' (ts := TestCtx) customers
    |>.orderBy (fun c => [c["Id"].asc])
    |>.execQuery
  let waves ← for p in parents do
    Query.from' (ts := TestCtx) orders
      |>.where' (fun o => o["CustomerId"] ==. p["Id"])
      |>.execQuery
  return waves.map (·.length)
}

/-- Compare a `Db` smoke result against its in-memory interpretation. -/
def checkSpenders (live : Nat × List (Values OrdersS)) : IO Bool := do
  match spenders.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR spenders (Db): {repr e}"
      pure false
  | .ok mem =>
      if live.1 == mem.1 && live.2.mergeSort rowLe == mem.2.mergeSort rowLe then
        pure true
      else do
        IO.eprintln "DRIVER MISMATCH spenders (Db)"
        pure false

def checkBothTables (live : List (Values CustomersS) × List (Values OrdersS)) : IO Bool := do
  match bothTables.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR bothTables (Db two-fetch): {repr e}"
      pure false
  | .ok mem =>
      if live.1.mergeSort rowLe == mem.1.mergeSort rowLe &&
         live.2.mergeSort rowLe == mem.2.mergeSort rowLe then
        pure true
      else do
        IO.eprintln "DRIVER MISMATCH bothTables (Db two-fetch)"
        pure false

def checkPerRowLoop (live : List Nat) : IO Bool := do
  match perRowLoop.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR perRowLoop (Db for/do): {repr e}"
      pure false
  | .ok mem =>
      if live == mem then pure true
      else do
        IO.eprintln s!"DRIVER MISMATCH perRowLoop (Db for/do): {live} vs {mem}"
        pure false

def checkBoundedFanOut (live : List Nat) : IO Bool := do
  match boundedFanOut.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR boundedFanOut (Db forRows): {repr e}"
      pure false
  | .ok mem =>
      if live == mem then pure true
      else do
        IO.eprintln s!"DRIVER MISMATCH boundedFanOut (Db forRows): {live} vs {mem}"
        pure false

def checkCardFanOut (live : List Nat) : IO Bool := do
  match cardFanOut.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR cardFanOut (Db contract-priced): {repr e}"
      pure false
  | .ok mem =>
      if live == mem then pure true
      else do
        IO.eprintln s!"DRIVER MISMATCH cardFanOut (Db contract-priced): {live} vs {mem}"
        pure false

def checkWholeTableFanOut (live : List Nat) : IO Bool := do
  match wholeTableFanOut.execAll seedEnv seedParams with
  | .error e =>
      IO.eprintln s!"EVAL ERROR wholeTableFanOut (Db symbolic): {repr e}"
      pure false
  | .ok mem =>
      if live == mem then pure true
      else do
        IO.eprintln s!"DRIVER MISMATCH wholeTableFanOut (Db symbolic): {live} vs {mem}"
        pure false

end TQ
