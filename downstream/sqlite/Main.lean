import LeanLinq.Driver.Sqlite

/-! Calls the SQLite driver against an in-memory database, so the program
links the sqlite3 shim and SQLite and runs a statement through them. -/

open LeanLinq

def main : IO UInt32 := do
  let db ← Sqlite.connect ":memory:"
  try
    db.execRaw "CREATE TABLE review (id INTEGER)"
  finally
    db.close
  IO.println "downstream(sqlite): linked, and created a table in memory"
  return 0
