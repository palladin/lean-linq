import LeanLinq.Driver.Postgres
import Tests.DriverSweep

/-! # Native PostgreSQL driver — differential test (`lake exe pgdriver`)

The shared sweep over live PostgreSQL (docker compose, port 5433): typed
`Values`-to-`Values` against the evaluator, through the wire protocol with
`$N` placeholders and OID-typed parameters — a second engine independently
confirming the semantics. The `DbFetch` smokes run through `execPg`; the
`seq` one exercises a real pipeline round carrying two statements. -/

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
      conn.execRaw (setupSql .postgres)
      let ops : DriverOps := {
        query := fun q => conn.query q seedParams
        queryCell := fun sc => conn.queryCell sc seedParams
        execIns := fun i => conn.execInsert i seedParams
        execUpd := fun u => conn.execUpdate u seedParams
        execDel := fun d => conn.execDelete d seedParams
        execRaw := conn.execRaw }
      let (passed, failures, skipped) ← runSweep ops
      let mut failures := failures
      -- DbFetch smokes: over the wire (pipelined) == in memory
      unless ← checkSpenders (← spenders.execPg conn 2 seedParams) do
        failures := failures + 1
      unless ← checkBothTables (← bothTables.execPg conn 1 seedParams) do
        failures := failures + 1
      unless ← checkPerRowLoop (← perRowLoop.execPg conn 3 seedParams) do
        failures := failures + 1
      unless ← checkBoundedFanOut (← boundedFanOut.execPg conn 4 seedParams) do
        failures := failures + 1
      unless ← checkUnboundedFanOut (← unboundedFanOut.execPgAll conn seedParams) do
        failures := failures + 1
      conn.close
      if failures == 0 then
        IO.println s!"driver(postgres): {passed} cases match the evaluator (typed), {skipped} skipped — all green"
        return 0
      else
        IO.eprintln s!"driver(postgres): {failures} failures ({passed} passed, {skipped} skipped)"
        return 1
