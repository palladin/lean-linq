import LeanLinq.Driver.Postgres

/-! Calls the PostgreSQL driver, so the program links the libpq shim and libpq.
It needs no database: it connects to a port nothing listens on and expects the
driver to report the failure. -/

open LeanLinq

def main : IO UInt32 := do
  let refused ←
    try
      let conn ← Pg.connect "host=127.0.0.1 port=1 connect_timeout=2"
      conn.close
      pure false
    catch _ =>
      pure true
  if refused then
    IO.println "downstream(postgres): linked, and the driver reported the refused connection"
    return 0
  IO.eprintln "downstream(postgres): a connection to port 1 succeeded"
  return 1
