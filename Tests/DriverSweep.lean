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
`apply`'s in-memory result. Instantiated by `Tests/DriverT.lean` (SQLite)
and `Tests/PgDriverT.lean` (PostgreSQL). -/

open LeanLinq

namespace TQ

/-- What a native driver must provide to be swept. -/
structure DriverOps where
  query : {s : Schema} → Query TestCtx s → IO (List (Values s))
  queryCell : {t : SqlType} → ScalarQuery TestCtx t → IO (Nullable t)
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
      ops.execIns i
      let ok ← checkTable ops name inst (i.apply (inst := inst) seedEnv seedParams)
      ops.execRaw ops.rollback
      pure ok
  | .upd (inst := inst) u => do
      ops.execRaw ops.begin
      ops.execUpd u
      let ok ← checkTable ops name inst (u.apply (inst := inst) seedEnv seedParams)
      ops.execRaw ops.rollback
      pure ok
  | .del (inst := inst) d => do
      ops.execRaw ops.begin
      ops.execDel d
      let ok ← checkTable ops name inst (d.apply (inst := inst) seedEnv seedParams)
      ops.execRaw ops.rollback
      pure ok

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

/-- The shared `fetch!` smoke: a data-dependent two-round program. -/
def spenders : DbFetch TestCtx 2 (Nat × List (Values OrdersS)) := fetch! {
  let adults ← .fetch (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] >=. SqlExpr.param "minAge"))
  let ids := adults.filterMap fun v => (v.get? "Id" .long).bind id
  let children ← .fetchFor ids fun ks =>
    Query.from' (ts := TestCtx) orders |>.where' (fun o => o["CustomerId"].inValues ks)
  return (adults.length, children)
}

/-- The shared `seq` smoke: two *independent* fetches, grade `max 1 1 = 1` —
on a pipelining driver this is one round carrying two statements. -/
def bothTables : DbFetch TestCtx 1 (List (Values CustomersS) × List (Values OrdersS)) :=
  .seq (.map Prod.mk (.fetch (Query.from' (ts := TestCtx) customers)))
       (.fetch (Query.from' (ts := TestCtx) orders))

/-- Compare a `DbFetch` smoke result against its in-memory interpretation. -/
def checkSpenders (live : Nat × List (Values OrdersS)) : IO Bool := do
  match spenders.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR spenders (DbFetch): {repr e}"
      pure false
  | .ok mem =>
      if live.1 == mem.1 && live.2.mergeSort rowLe == mem.2.mergeSort rowLe then
        pure true
      else do
        IO.eprintln "DRIVER MISMATCH spenders (DbFetch)"
        pure false

def checkBothTables (live : List (Values CustomersS) × List (Values OrdersS)) : IO Bool := do
  match bothTables.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR bothTables (DbFetch seq): {repr e}"
      pure false
  | .ok mem =>
      if live.1.mergeSort rowLe == mem.1.mergeSort rowLe &&
         live.2.mergeSort rowLe == mem.2.mergeSort rowLe then
        pure true
      else do
        IO.eprintln "DRIVER MISMATCH bothTables (DbFetch seq)"
        pure false

end TQ
