import LeanLinq.Driver.Postgres
import Tests.DriverSweep
import Tests.DriverRegressions
import Tests.TransactionDriver

/-! # Native PostgreSQL driver — differential test (`lake exe pgdriver`)

The shared sweep over live PostgreSQL (docker compose, port 5433): typed
`Values`-to-`Values` against the evaluator, through the wire protocol with
`$N` placeholders and OID-typed parameters — a second engine independently
confirming the semantics. The `Db` smokes run sequentially through `execPg`,
with one statement per effect. -/

open LeanLinq LeanLinq.Pg TQ

def conninfo : String :=
  "host=127.0.0.1 port=5433 user=testuser password=testpass dbname=testdb"

def main : IO UInt32 := do
  let conn? ← try some <$> Pg.connect conninfo catch _ => pure none
  match conn? with
  | none =>
      IO.eprintln "[pgdriver] PostgreSQL unreachable — skipped (is `docker compose up -d --wait` running?)"
      return 0
  | some conn =>
      TransactionDriver.run .postgres {
        withTransaction := fun action => conn.withTransaction action
        execRaw := conn.execRaw
        query := fun q => conn.query q
        update := fun u => conn.execUpdate u
        runDb := fun p => p.execPgAll conn }
      DriverRegressions.checkDoubleQueries (fun q ps => conn.query q ps)
      DriverRegressions.checkCompilerQueries .postgres (fun q => conn.query q) conn.execRaw
      DriverRegressions.checkAggregateDml .postgres {
        query := fun q => conn.query q
        update := fun q => conn.execUpdate q
        delete := fun q => conn.execDelete q
        queryAlias := fun q => conn.query q
        updateAlias := fun q => conn.execUpdate q
        execRaw := conn.execRaw }
      conn.execRaw (setupSql .postgres)
      let ops : DriverOps := {
        query := fun q => conn.query q seedParams
        queryCell := fun sc => conn.queryCell sc seedParams
        execIns := fun i => discard (conn.execInsert i seedParams)
        execUpd := fun u => discard (conn.execUpdate u seedParams)
        execDel := fun d => discard (conn.execDelete d seedParams)
        execInsSel := fun st => discard (conn.execInsertSelect st seedParams)
        execInsVals := fun st => discard (conn.execInsertValues st seedParams)
        execRaw := conn.execRaw }
      let (passed, failures, skipped) ← runSweep ops
      let mut failures := failures
      -- Db smokes: sequential wire execution == in memory
      unless ← checkSpenders (← spenders.execPg conn 2 seedParams) do
        failures := failures + 1
      unless ← checkBothTables (← bothTables.execPg conn 2 seedParams) do
        failures := failures + 1
      unless ← checkPerRowLoop (← perRowLoop.execPg conn 3 seedParams) do
        failures := failures + 1
      unless ← checkBoundedFanOut (← boundedFanOut.execPg conn 4 seedParams) do
        failures := failures + 1
      unless ← checkCardFanOut (← cardFanOut.execPg conn 4 seedParams) do
        failures := failures + 1
      unless ← checkWholeTableFanOut (← wholeTableFanOut.execPgAll conn seedParams) do
        failures := failures + 1
      -- Connection recovery: a server error (division by zero
      -- evaluated by the engine) must not wedge the connection — the next
      -- query on the same connection has to succeed
      let recovered ← do
        let bad := Query.from' (ts := TestCtx) customers
          |>.select (fun _ => ![(SqlExpr.int 10 / SqlExpr.int 0).as "X"])
        try
          let _ ← (Db.fetch bad).execPg conn 1 seedParams
          pure false  -- engine unexpectedly accepted 1/0
        catch _ =>
          let _ ← conn.query (Query.from' (ts := TestCtx) customers) seedParams
          pure true
      unless recovered do
        IO.eprintln "CONNECTION RECOVERY failed: connection wedged after error"
        failures := failures + 1
      conn.close
      TransactionDriver.checkClosed (fun action => conn.withTransaction action)
        (conn.execRaw "SELECT 1") (discard (conn.query TransactionDriver.rows))
        (discard (conn.execUpdate (TransactionDriver.bump 1)))
      if failures == 0 then
        IO.println s!"driver(postgres): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
        return 0
      else
        IO.eprintln s!"driver(postgres): {failures} failures ({passed} passed, {skipped} skipped)"
        return 1
