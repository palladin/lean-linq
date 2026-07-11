import LeanLinq.Driver.Sqlite
import Tests.QueriesC
import Tests.StatementsT
import Tests.Seed
import Tests.SeedSql

/-! # Native-driver differential test

Runs every registered case through the real SQLite driver — typed queries,
**natively bound** parameters (no inlining anywhere on this path) — and
compares the decoded rows against the evaluator **at the `Values s` level,
cell for cell**; strings appear only in failure messages. Statements run
inside rolled-back transactions and are verified with a typed read-back
query against `apply`'s in-memory result. Finally, a `fetch!` program is
interpreted over the wire (`DbFetch.execIO`) and must agree with its
in-memory interpretation (`runWith`).

The golden text files remain the CLI harness's concern
(`lake exe integration`): two independent referees, no shared bridge. -/

open LeanLinq LeanLinq.Sqlite TQ

/-- Rendering is for *messages only*; comparison is typed. -/
private def showRows (rows : List (Values s)) : String :=
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
def checkTable {n : String} {s : Schema} (conn : Conn) (name : String)
    (inst : HasTable TestCtx.tables n s)
    (applied : Except EvalError (TableEnv TestCtx.tables)) : IO Bool := do
  have : HasTable TestCtx.tables n s := inst
  let got ← conn.query (Query.from' (ts := TestCtx) (⟨⟩ : Table n s)) seedParams
  match applied with
  | .error e =>
      IO.eprintln s!"EVAL ERROR {name}: {repr e}"
      pure false
  | .ok env' => checkRows name "statement" false got (inst.rows env')

def runCase (conn : Conn) (name : String) (c : Case) : IO Bool := do
  match c.payload with
  | .query q => do
      let driver ← conn.query q seedParams
      match q.run seedEnv seedParams with
      | .error e =>
          IO.eprintln s!"EVAL ERROR {name}: {repr e}"
          pure false
      | .ok expected => checkRows name "query" c.ordered driver expected
  | .scalar (t := t) sc => do
      let driver ← conn.queryCell sc seedParams
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
      conn.execRaw "BEGIN"
      conn.execInsert i seedParams
      let ok ← checkTable conn name inst (i.apply (inst := inst) seedEnv seedParams)
      conn.execRaw "ROLLBACK"
      pure ok
  | .upd (inst := inst) u => do
      conn.execRaw "BEGIN"
      conn.execUpdate u seedParams
      let ok ← checkTable conn name inst (u.apply (inst := inst) seedEnv seedParams)
      conn.execRaw "ROLLBACK"
      pure ok
  | .del (inst := inst) d => do
      conn.execRaw "BEGIN"
      conn.execDelete d seedParams
      let ok ← checkTable conn name inst (d.apply (inst := inst) seedEnv seedParams)
      conn.execRaw "ROLLBACK"
      pure ok

/-- A round-budgeted program interpreted over the wire and in memory. -/
def spenders : DbFetch TestCtx 2 (Nat × List (Values OrdersS)) := fetch! {
  let adults ← .fetch (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] >=. SqlExpr.param "minAge"))
  let ids := adults.filterMap fun v => (v.get? "Id" .long).bind id
  let children ← .fetchFor ids fun ks =>
    Query.from' (ts := TestCtx) orders |>.where' (fun o => o["CustomerId"].inValues ks)
  return (adults.length, children)
}

def main : IO UInt32 := do
  let path := "/tmp/leanlinq-driver.db"
  if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let conn ← Sqlite.connect path
  conn.execRaw (setupSql .sqlite)
  let mut failures := 0
  let mut passed := 0
  let mut skipped := 0
  for (name, c) in queryCases ++ twinCases ++ statementCases do
    if skipResults.contains name || crossDialectAllowlist.contains name then
      skipped := skipped + 1
      continue
    if ← runCase conn name c then passed := passed + 1
    else failures := failures + 1
  -- DbFetch: over the wire == in memory
  let live ← spenders.execIO conn 2 seedParams
  match spenders.runWith ⟨seedEnv, seedParams, none⟩ with
  | .error e =>
      IO.eprintln s!"EVAL ERROR spenders (DbFetch): {repr e}"
      failures := failures + 1
  | .ok mem =>
      if live.1 == mem.1 && live.2.mergeSort rowLe == mem.2.mergeSort rowLe then
        IO.println s!"DbFetch execIO == runWith ({live.1} adults, {live.2.length} orders)"
      else do
        IO.eprintln "DRIVER MISMATCH spenders (DbFetch)"
        failures := failures + 1
  conn.close
  if failures == 0 then
    IO.println s!"driver: {passed} cases match the evaluator (typed), {skipped} skipped — all green"
    return 0
  else
    IO.eprintln s!"driver: {failures} failures ({passed} passed, {skipped} skipped)"
    return 1
