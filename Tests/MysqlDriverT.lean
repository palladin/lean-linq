import LeanLinq.Driver.Mysql
import Tests.DriverSweep

/-! # Native MySQL driver — differential test (`lake exe mysqldriver`)

The shared sweep (`Tests/DriverSweep.lean`) over the libmysqlclient
driver, plus the `Db` smokes through `execMy`. Requires the compose
service: `docker compose up -d --wait mysql` (port 3307). -/

open LeanLinq LeanLinq.Mysql TQ

-- a symbolic grade never fits a closed budget — over the wire either
#check_failure fun (conn : LeanLinq.Mysql.Conn) =>
  TQ.wholeTableFanOut.execMy conn 1000 seedParams

def main : IO UInt32 := do
  let conn? ← try some <$> Mysql.connect catch _ => pure none
  match conn? with
  | none =>
      IO.eprintln "[mysqldriver] MySQL unreachable — skipped (is `docker compose up -d --wait` running?)"
      return 0
  | some conn =>
  conn.execRaw (setupSql .mysql)
  let ops : DriverOps := {
    query := fun q => conn.query q seedParams
    queryCell := fun sc => conn.queryCell sc seedParams
    execIns := fun i => discard (conn.execInsert i seedParams)
    execUpd := fun u => discard (conn.execUpdate u seedParams)
    execDel := fun d => discard (conn.execDelete d seedParams)
    execInsSel := fun st => discard (conn.execInsertSelect st seedParams)
    execRaw := conn.execRaw
    begin := "START TRANSACTION"
    rollback := "ROLLBACK" }
  let (passed, failures, skipped) ← runSweep ops
  let mut failures := failures
  -- Db smokes: over the wire == in memory
  unless ← checkSpenders (← spenders.execMy conn 2 seedParams) do
    failures := failures + 1
  unless ← checkBothTables (← bothTables.execMy conn 2 seedParams) do
    failures := failures + 1
  unless ← checkPerRowLoop (← perRowLoop.execMy conn 3 seedParams) do
    failures := failures + 1
  unless ← checkBoundedFanOut (← boundedFanOut.execMy conn 4 seedParams) do
    failures := failures + 1
  unless ← checkCardFanOut (← cardFanOut.execMy conn 4 seedParams) do
    failures := failures + 1
  unless ← checkWholeTableFanOut (← wholeTableFanOut.execMyAll conn seedParams) do
    failures := failures + 1
  conn.close
  if failures == 0 then
    IO.println s!"driver(mysql): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
    return 0
  else
    IO.eprintln s!"driver(mysql): {failures} failures ({passed} passed, {skipped} skipped)"
    return 1
