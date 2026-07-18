import LeanLinq.Driver.Mssql
import Tests.DriverSweep

/-! # Native SQL Server driver — differential test (`lake exe mssqldriver`)

The shared sweep over live SQL Server (docker compose, port 14333): typed
`Values`-to-`Values` against the evaluator, through native TDS
`sp_executesql` RPC with true `@name` parameters — the first non-inlined
MSSQL execution in the suite, and the third engine independently confirming
the semantics. `Db` smokes run through `execMs` (sequential — TDS has
no pipelining). -/

open LeanLinq LeanLinq.Ms TQ

def msHost := "127.0.0.1"
def msPort := 14333
def msUser := "sa"
def msPass := "Test123!Strong"

def main : IO UInt32 := do
  -- probe against master (also creates testdb on first contact, like the
  -- CLI harness's probe)
  let probe? ← try
    let m ← Ms.connect msHost msPort msUser msPass
    m.execRaw "IF DB_ID('testdb') IS NULL CREATE DATABASE testdb"
    m.close
    pure true
  catch _ => pure false
  unless probe? do
    IO.eprintln "[mssqldriver] SQL Server unreachable — skipped (is `docker compose up -d --wait` running?)"
    return 0
  let conn ← Ms.connect msHost msPort msUser msPass (db := "testdb")
  conn.execRaw (setupSql .sqlServer)
  let ops : DriverOps := {
    query := fun q => conn.query q seedParams
    queryCell := fun sc => conn.queryCell sc seedParams
    execIns := fun i => discard (conn.execInsert i seedParams)
    execUpd := fun u => discard (conn.execUpdate u seedParams)
    execDel := fun d => discard (conn.execDelete d seedParams)
    execInsSel := fun st => discard (conn.execInsertSelect st seedParams)
    execInsVals := fun st => discard (conn.execInsertValues st seedParams)
    execRaw := conn.execRaw
    begin := "BEGIN TRAN"
    rollback := "ROLLBACK TRAN" }
  let (passed, failures, skipped) ← runSweep ops
  let mut failures := failures
  -- Db smokes: over the wire == in memory (sequential on TDS)
  unless ← checkSpenders (← spenders.execMs conn 2 seedParams) do
    failures := failures + 1
  unless ← checkBothTables (← bothTables.execMs conn 2 seedParams) do
    failures := failures + 1
  unless ← checkPerRowLoop (← perRowLoop.execMs conn 3 seedParams) do
    failures := failures + 1
  unless ← checkBoundedFanOut (← boundedFanOut.execMs conn 4 seedParams) do
    failures := failures + 1
  unless ← checkCardFanOut (← cardFanOut.execMs conn 4 seedParams) do
    failures := failures + 1
  unless ← checkWholeTableFanOut (← wholeTableFanOut.execMsAll conn seedParams) do
    failures := failures + 1
  -- error routing: a server error must surface as an IO error carrying the
  -- server's message text (per-connection buffers in native/freetds_shim.c)
  let errText ← try
    conn.execRaw "SELECT 1 +"
    pure ""
  catch e => pure (toString e)
  unless errText.startsWith "freetds" && errText.length > 20 do
    IO.eprintln s!"ERROR-ROUTING CHECK failed: got {repr errText}"
    failures := failures + 1
  conn.close
  if failures == 0 then
    IO.println s!"driver(mssql): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
    return 0
  else
    IO.eprintln s!"driver(mssql): {failures} failures ({passed} passed, {skipped} skipped)"
    return 1
