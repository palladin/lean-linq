import LeanLinq

/-! Shared native transaction regressions. Expected table contents are explicit;
the fixture uses a primary key so a duplicate INSERT fails on every engine. -/

namespace TransactionDriver
open LeanLinq

abbrev S : Schema := [("Id", .int), ("Balance", .int)]
abbrev DecodeS : Schema := [("Value", .int)]
abbrev C : Ctx := { tables := [("transaction_items", S), ("transaction_decode", DecodeS)] }
def items : Table "transaction_items" S := ⟨⟩
def decodeTable : Table "transaction_decode" DecodeS := ⟨⟩
def rows : Query C S := Query.from' (ts := C) items |>.orderBy (fun r => [r["Id"].asc])
def badDecode : Query C DecodeS := Query.from' decodeTable
def bump (id : Int) : UpdateStmt C "transaction_items" S :=
  items.update |>.setWith "Balance" (fun r => r["Balance"] + 1)
    |>.where' (fun r => r["Id"] ==. SqlExpr.int id)
def duplicate : InsertStmt C "transaction_items" S :=
  items.insert |>.value "Id" 1 |>.value "Balance" 99

private def expected (a b : Int) : List (Values S) :=
  [.cons 1 (.cons a .nil), .cons 2 (.cons b .nil)]

def commitProgram : Db C 3 ((Nat × Nat) × List (Values S)) := db! {
  let changed ← transaction {
    let first ← (bump 1).execUpdate
    let second ← (bump 2).execUpdate
    return (first, second)
  }
  let after ← rows.execQuery
  return (changed, after)
}

-- The first write is outside the failed region. The last write must not run.
def rollbackProgram : Db C 4 Unit := db! {
  let before ← (bump 1).execUpdate
  let failed ← transaction {
    let changed ← (bump 2).execUpdate
    let inserted ← duplicate.execInsert
    return (changed, inserted)
  }
  let after ← (bump 1).execUpdate
  return ()
}

-- A later failure cannot roll back a transaction that has already committed.
def afterCommitFailure : Db C 2 Nat := db! {
  let committed ← transaction {
    let changed ← (bump 1).execUpdate
    return changed
  }
  let failed ← duplicate.execInsert
  return failed
}

-- Each raise has zero statement cost. The following writes are retained in
-- the program and its budget, but execution must stop at the original message.
def raiseOutsideProgram (message : String) : Db C 2 Unit := db! {
  let before ← (bump 1).execUpdate
  let failed ← Db.raise message
  let marker ← (bump 2).execUpdate
  return ()
}

def raiseInsideProgram (message : String) : Db C 4 Unit := db! {
  let before ← (bump 1).execUpdate
  let failed ← transaction {
    let changed ← (bump 2).execUpdate
    let raised ← Db.raise message
    let marker ← (bump 1).execUpdate
    return marker
  }
  let after ← (bump 1).execUpdate
  return ()
}

def raiseAfterCommitProgram (message : String) : Db C 2 Unit := db! {
  let committed ← transaction {
    let changed ← (bump 1).execUpdate
    return changed
  }
  let failed ← Db.raise message
  let marker ← (bump 2).execUpdate
  return ()
}

structure Ops where
  withTransaction : {α : Type} → IO α → IO α
  execRaw : String → IO Unit
  query : {s : Schema} → Query C s → IO (List (Values s))
  update : UpdateStmt C "transaction_items" S → IO Nat
  runDb : {α : Type} → {w : Wp α} → DbP C α w → IO α

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"transaction regression: {message}")

private def errorOf (action : IO α) : IO String := do
  try
    let _ ← action
    pure ""
  catch e => pure (toString e)

/-- Failed cleanup may retire a connection. Reusing any captured reference
must report an IO error instead of dereferencing a closed native handle. -/
def checkClosed (withTransaction : IO Unit → IO Unit)
    (raw query update : IO Unit) : IO Unit := do
  let entered ← IO.mkRef false
  check (!(← errorOf (withTransaction (entered.set true))).isEmpty)
    "closed connection rejects transaction"
  check (!(← entered.get)) "closed connection never enters transaction body"
  for action in [raw, query, update] do
    check (!(← errorOf action).isEmpty) "closed connection operation raises IO error"

def run (db : DatabaseType) (ops : Ops) : IO Unit := do
  let table := db.quoteIdent "transaction_items"
  let decodeTable := db.quoteIdent "transaction_decode"
  let id := db.quoteIdent "Id"
  let balance := db.quoteIdent "Balance"
  let engine := if db == .mysql then " ENGINE=InnoDB" else ""
  let beginSql := if db == .sqlServer then "BEGIN TRAN" else "BEGIN"
  let rollbackSql := if db == .sqlServer then "ROLLBACK TRAN" else "ROLLBACK"
  ops.execRaw s!"DROP TABLE IF EXISTS {table}; CREATE TABLE {table} ({id} INTEGER PRIMARY KEY, {balance} INTEGER NOT NULL){engine}"
  -- Deliberately violate the declared non-null schema to fail in row decoding.
  ops.execRaw s!"DROP TABLE IF EXISTS {decodeTable}; CREATE TABLE {decodeTable} ({db.quoteIdent "Value"} INTEGER){engine}; INSERT INTO {decodeTable} VALUES (NULL)"
  let reset : IO Unit := ops.execRaw s!"DELETE FROM {table}; INSERT INTO {table} VALUES (1,10),(2,20)"
  let verify (a b : Int) (message : String) : IO Unit := do
    check ((← ops.query rows) == expected a b) message
  try
    reset
    let result ← ops.withTransaction do
      check ((← ops.update (bump 1)) == 1) "first affected-row count"
      verify 11 20 "read own uncommitted write"
      check ((← ops.update (bump 2)) == 1) "second affected-row count"
      pure 42
    check (result == 42) "committed callback result"
    verify 11 21 "commit persists both writes"

    reset
    let failure ← errorOf (ops.withTransaction (α := Unit) do
      discard (ops.update (bump 1))
      throw (IO.userError "transaction application failure"))
    check (failure.startsWith "transaction application failure") "original application error retained"
    verify 10 20 "application error rolls back and leaves connection reusable"

    reset
    let failure ← errorOf (ops.withTransaction do
      discard (ops.update (bump 1))
      ops.execRaw s!"INSERT INTO {table} VALUES (1,99)")
    check (!failure.isEmpty) "SQL constraint error propagated"
    verify 10 20 "SQL error rolls back and leaves connection reusable"

    reset
    let failure ← errorOf (ops.withTransaction do
      discard (ops.update (bump 1))
      discard (ops.query badDecode))
    check (!failure.isEmpty) "row-decoding error propagated"
    verify 10 20 "row-decoding error rolls back and leaves connection reusable"

    reset
    let entered ← IO.mkRef false
    ops.withTransaction do
      discard (ops.update (bump 1))
      let failure ← errorOf (ops.withTransaction (entered.set true))
      check (!failure.isEmpty) "nested transaction rejected"
      check (!(← entered.get)) "nested body never entered"
      discard (ops.update (bump 2))
    verify 11 21 "rejecting nested helper preserves outer transaction"

    reset
    ops.execRaw beginSql
    try
      discard (ops.update (bump 1))
      let failure ← errorOf (ops.withTransaction (entered.set true))
      check (!failure.isEmpty) "manually active transaction rejected"
      verify 11 20 "manual transaction still owned by caller"
    finally
      ops.execRaw rollbackSql
    verify 10 20 "rejected helper did not commit caller's transaction"

    reset
    let result ← ops.runDb commitProgram
    check (result == ((1, 1), expected 11 21)) "scoped program commits before continuation"
    verify 11 21 "scoped program persisted writes"

    reset
    let failure ← errorOf (ops.runDb rollbackProgram)
    check (!failure.isEmpty) "scoped program propagates SQL failure"
    verify 11 20 "failed scope preserves earlier writes and skips continuation"

    reset
    let failure ← errorOf (ops.runDb afterCommitFailure)
    check (!failure.isEmpty) "failure after commit propagated"
    verify 11 20 "completed transaction survives later failure"

    let outsideMessage := "Db.raise outside: retain earlier write"
    reset
    check ((← errorOf (ops.runDb (raiseOutsideProgram outsideMessage))) == outsideMessage)
      "outside raise preserves the original message"
    verify 11 20 "outside raise preserves earlier write and skips marker"

    let insideMessage := "Db.raise inside: user's message\nrollback this scope"
    reset
    check ((← errorOf (ops.runDb (raiseInsideProgram insideMessage))) == insideMessage)
      "inside raise preserves the original message"
    verify 11 20 "inside raise rolls back its write, retains earlier write and skips continuation"
    discard (ops.withTransaction (ops.update (bump 2)))
    verify 11 21 "inside raise releases transaction ownership and permits reuse"

    let afterMessage := "Db.raise after commit: keep committed write"
    reset
    check ((← errorOf (ops.runDb (raiseAfterCommitProgram afterMessage))) == afterMessage)
      "raise after commit preserves the original message"
    verify 11 20 "raise after commit retains commit and skips marker"
    discard (ops.withTransaction (ops.update (bump 2)))
    verify 11 21 "raise after commit leaves connection reusable"

    -- PostgreSQL keeps a failed transaction after a caught statement error.
    -- COMMIT must not be mistaken for success when the server would roll back.
    if db == .postgres then
      reset
      let failure ← errorOf (ops.withTransaction do
        discard (ops.update (bump 1))
        let sqlError ← errorOf (ops.execRaw s!"INSERT INTO {table} VALUES (1,99)")
        check (!sqlError.isEmpty) "caught SQL error fixture")
      check (!failure.isEmpty) "aborted transaction cannot report successful commit"
      verify 10 20 "caught SQL error rolls back aborted transaction"

    -- Session defaults must not make a managed COMMIT start a new transaction
    -- or close the connection. Managed controls override CHAIN and RELEASE.
    if db == .mysql then
      ops.execRaw "SET @lean_linq_saved_completion_type = @@session.completion_type"
      try
        for completion in [1, 2] do
          ops.execRaw s!"SET SESSION completion_type = {completion}"
          reset
          discard (ops.withTransaction (ops.update (bump 1)))
          verify 11 20 "MySQL commit overrides completion_type"
          let failure ← errorOf (ops.withTransaction (α := Unit) do
            discard (ops.update (bump 2))
            throw (IO.userError "completion_type rollback"))
          check (failure.startsWith "completion_type rollback")
            "MySQL rollback retains original failure"
          verify 11 20 "MySQL rollback overrides completion_type and permits reuse"
      finally
        ops.execRaw "SET SESSION completion_type = @lean_linq_saved_completion_type"

    IO.println s!"transactions({repr db}): native regressions passed"
  finally
    ops.execRaw s!"DROP TABLE {table}; DROP TABLE {decodeTable}"

end TransactionDriver
