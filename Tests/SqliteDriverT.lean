import LeanLinq.Driver.Sqlite
import Tests.DriverSweep

/-! # Native SQLite driver — differential test (`lake exe sqlitedriver`)

The shared sweep (`Tests/DriverSweep.lean`) over the in-process SQLite
driver, plus the `DbFetch` smokes through `execIO`. -/

open LeanLinq LeanLinq.Sqlite TQ

-- ⊤ never fits a finite door — over the wire either: only execIOAll runs it
#check_failure fun (conn : LeanLinq.Sqlite.Conn) =>
  TQ.unboundedFanOut.execIO conn 1000 seedParams

def main : IO UInt32 := do
  let path := "/tmp/leanlinq-driver.db"
  if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let conn ← Sqlite.connect path
  conn.execRaw (setupSql .sqlite)
  let ops : DriverOps := {
    query := fun q => conn.query q seedParams
    queryCell := fun sc => conn.queryCell sc seedParams
    execIns := fun i => conn.execInsert i seedParams
    execUpd := fun u => conn.execUpdate u seedParams
    execDel := fun d => conn.execDelete d seedParams
    execRaw := conn.execRaw }
  let (passed, failures, skipped) ← runSweep ops
  let mut failures := failures
  -- DbFetch smokes: over the wire == in memory
  unless ← checkSpenders (← spenders.execIO conn 2 seedParams) do
    failures := failures + 1
  unless ← checkBothTables (← bothTables.execIO conn 1 seedParams) do
    failures := failures + 1
  unless ← checkPerRowLoop (← perRowLoop.execIO conn 3 seedParams) do
    failures := failures + 1
  unless ← checkBoundedFanOut (← boundedFanOut.execIO conn 4 seedParams) do
    failures := failures + 1
  unless ← checkUnboundedFanOut (← unboundedFanOut.execIOAll conn seedParams) do
    failures := failures + 1
  conn.close
  if failures == 0 then
    IO.println s!"driver(sqlite): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
    return 0
  else
    IO.eprintln s!"driver(sqlite): {failures} failures ({passed} passed, {skipped} skipped)"
    return 1
