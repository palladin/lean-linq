import LeanLinq.Driver.Sqlite
import Tests.DriverSweep

/-! # Native SQLite driver — differential test (`lake exe sqlitedriver`)

The shared sweep (`Tests/DriverSweep.lean`) over the in-process SQLite
driver, plus the `Db` smokes through `execIO`. -/

open LeanLinq LeanLinq.Sqlite TQ

/-! Wire-decoder pins: parse failures are loud, never silent zeros. -/
#guard (LeanLinq.Driver.parseFloat? "1.5e3") == some 1500.0
#guard (LeanLinq.Driver.parseFloat? "-2.5E-2") == some (-0.025)
#guard (LeanLinq.Driver.parseFloat? "Infinity").isSome
#guard (LeanLinq.Driver.parseFloat? "abc") == none
#guard (LeanLinq.Driver.parseFloat? "") == none
#guard (LeanLinq.Driver.parseIntText? "325.0000000000000000") == some 325
#guard (LeanLinq.Driver.parseIntText? "xyz") == none
#guard (LeanLinq.Driver.parseDecimal? "-12.345") == some (-12345)
#guard (LeanLinq.Driver.parseDecimal? "1,000") == none

-- a symbolic grade never fits a closed budget — over the wire either:
-- no number dominates |customers| + 1; only execIOAll runs it
#check_failure fun (conn : LeanLinq.Sqlite.Conn) =>
  TQ.wholeTableFanOut.execIO conn 1000 seedParams

def main : IO UInt32 := do
  let path := "/tmp/leanlinq-driver.db"
  if ← System.FilePath.pathExists path then IO.FS.removeFile path
  let conn ← Sqlite.connect path
  conn.execRaw (setupSql .sqlite)
  let ops : DriverOps := {
    query := fun q => conn.query q seedParams
    queryCell := fun sc => conn.queryCell sc seedParams
    execIns := fun i => discard (conn.execInsert i seedParams)
    execUpd := fun u => discard (conn.execUpdate u seedParams)
    execDel := fun d => discard (conn.execDelete d seedParams)
    execRaw := conn.execRaw }
  let (passed, failures, skipped) ← runSweep ops
  let mut failures := failures
  -- Db smokes: over the wire == in memory
  unless ← checkSpenders (← spenders.execIO conn 2 seedParams) do
    failures := failures + 1
  unless ← checkBothTables (← bothTables.execIO conn 2 seedParams) do
    failures := failures + 1
  unless ← checkPerRowLoop (← perRowLoop.execIO conn 3 seedParams) do
    failures := failures + 1
  unless ← checkBoundedFanOut (← boundedFanOut.execIO conn 4 seedParams) do
    failures := failures + 1
  unless ← checkCardFanOut (← cardFanOut.execIO conn 4 seedParams) do
    failures := failures + 1
  unless ← checkWholeTableFanOut (← wholeTableFanOut.execIOAll conn seedParams) do
    failures := failures + 1
  conn.close
  if failures == 0 then
    IO.println s!"driver(sqlite): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
    return 0
  else
    IO.eprintln s!"driver(sqlite): {failures} failures ({passed} passed, {skipped} skipped)"
    return 1
