/-! Exception-safe native transaction lifecycle. Transaction controls and state
checks are outside the `Db` body's operation bill. Connections must be used
exclusively for the entire scope; the managed guard rejects nesting but does
not make concurrent ordinary queries on one connection safe. -/

namespace LeanLinq.Driver

inductive TransactionState where
  | idle
  | active
  | aborted
  | unusable
  deriving BEq, Repr

/-- Native adapters own the connection guard and validate control responses.
`commit` must reject a response that reports rollback instead of commit. -/
structure TransactionOps where
  claim : IO Unit
  release : IO Unit
  state : IO TransactionState
  begin : IO Unit
  commit : IO Unit
  rollback : IO Unit
  close : IO Unit

private def attempt (action : IO α) : IO (Except IO.Error α) := do
  try return .ok (← action)
  catch e => return .error e

private def closeWithDetail (ops : TransactionOps) (detail : String) : IO String := do
  match ← attempt ops.close with
  | .ok _ => return detail
  | .error e => return s!"{detail}; closing connection also failed: {e}"

private def rethrowWithDetail (original : IO.Error) (detail : Option String) : IO α :=
  match detail with
  | none => throw original
  | some detail => throw (IO.userError s!"{original}\ntransaction cleanup: {detail}")

private def closeAndThrow (ops : TransactionOps) (original : IO.Error)
    (detail : String) : IO α := do
  rethrowWithDetail original (some (← closeWithDetail ops detail))

/-- Recover only a transaction this scope successfully began. A failed
rollback or unverifiable state makes the connection unsuitable for reuse. -/
private def rollbackOwned (ops : TransactionOps) : IO (Option String) := do
  match ← attempt ops.state with
  | .error e =>
      return some (← closeWithDetail ops s!"could not inspect transaction state: {e}")
  | .ok .unusable =>
      return some (← closeWithDetail ops "connection is unusable")
  | .ok .idle => return none
  | .ok .active | .ok .aborted =>
      match ← attempt ops.rollback with
      | .error e =>
          return some (← closeWithDetail ops s!"rollback failed: {e}")
      | .ok _ =>
          match ← attempt ops.state with
          | .ok .idle => return none
          | .ok _ =>
              return some (← closeWithDetail ops "rollback did not leave an idle connection")
          | .error e =>
              return some (← closeWithDetail ops s!"could not verify rollback: {e}")

private def runTransaction (ops : TransactionOps) (action : IO α) : IO α := do
  match ← ops.state with
  | .active | .aborted => throw (IO.userError "transaction: connection already has an active transaction")
  | .unusable => throw (IO.userError "transaction: connection is closed or unusable")
  | .idle => pure ()
  match ← attempt ops.begin with
  | .error e =>
      -- BEGIN was not confirmed. Never roll back another owner's work.
      match ← attempt ops.state with
      | .ok .idle => throw e
      | _ => closeAndThrow ops e "BEGIN failed and connection state is uncertain"
  | .ok _ => pure ()
  match ← attempt ops.state with
  | .ok .active => pure ()
  | .error e => closeAndThrow ops e "could not verify BEGIN"
  | .ok _ =>
      closeAndThrow ops (IO.userError "transaction: BEGIN did not establish an active transaction")
        "connection closed before running the transaction body"
  let value ← match ← attempt action with
    | .ok value => pure value
    | .error e => rethrowWithDetail e (← rollbackOwned ops)
  match ← attempt ops.state with
  | .ok .active => pure ()
  | .ok .aborted =>
      rethrowWithDetail (IO.userError "transaction: transaction is aborted; commit refused")
        (← rollbackOwned ops)
  | .ok .idle =>
      closeAndThrow ops (IO.userError "transaction: transaction ended before commit; outcome is unknown")
        "connection closed; transaction control inside the body is unsupported"
  | .ok .unusable =>
      closeAndThrow ops (IO.userError "transaction: connection became unusable; outcome is unknown")
        "connection closed"
  | .error e =>
      closeAndThrow ops e "could not inspect state before commit; outcome is unknown"
  match ← attempt ops.commit with
  | .error e =>
      match ← attempt ops.state with
      | .ok .active | .ok .aborted => rethrowWithDetail e (← rollbackOwned ops)
      | _ => closeAndThrow ops e "commit outcome is unknown; connection closed; do not retry automatically"
  | .ok _ =>
      match ← attempt ops.state with
      | .ok .idle => return value
      | _ =>
          closeAndThrow ops (IO.userError "transaction: could not verify commit; outcome is unknown")
            "connection closed; do not retry automatically"

/-- Run one top-level transaction using the engine's default isolation mode.
Commit on success; roll back on an exception. An existing transaction is never
adopted. Raw transaction control, implicitly committing DDL, and concurrent use
of the same connection are outside this scope's contract. -/
def withTransaction (ops : TransactionOps) (action : IO α) : IO α := do
  ops.claim
  let result ← attempt (runTransaction ops action)
  let released ← attempt ops.release
  match result, released with
  | .ok value, .ok _ => return value
  | .error e, .ok _ => throw e
  | .error e, .error releaseError =>
      closeAndThrow ops e s!"releasing transaction guard failed: {releaseError}"
  | .ok _, .error e =>
      closeAndThrow ops e "transaction completed but releasing its guard failed"

end LeanLinq.Driver
