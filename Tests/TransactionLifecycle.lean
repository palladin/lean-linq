import LeanLinq.Driver.Transaction

/-! Deterministic failure injection for transaction control. Native suites cover
real engine rollback; these cases exercise failures that are hard to trigger
reliably, especially a lost commit acknowledgement and failed cleanup. -/

namespace TransactionLifecycle
open LeanLinq.Driver

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"transaction lifecycle: {message}")

private def errorOf (action : IO α) : IO String := do
  try
    let _ ← action
    pure ""
  catch e => pure (toString e)

private structure Fixture where
  ops : TransactionOps
  state : IO.Ref TransactionState
  events : IO.Ref (Array String)
  claimed : IO.Ref Bool

private def fixture (initial : TransactionState := .idle) : IO Fixture := do
  let state ← IO.mkRef initial
  let events ← IO.mkRef (#[] : Array String)
  let claimed ← IO.mkRef false
  let note (event : String) := events.modify (·.push event)
  let ops : TransactionOps := {
    claim := do
      note "claim"
      if ← claimed.get then throw (IO.userError "already claimed")
      claimed.set true
    release := do note "release"; claimed.set false
    state := do note "state"; state.get
    begin := do note "begin"; state.set .active
    commit := do note "commit"; state.set .idle
    rollback := do note "rollback"; state.set .idle
    close := do note "close"; state.set .unusable }
  return { ops, state, events, claimed }

private def has (f : Fixture) (event : String) : IO Bool := do
  return (← f.events.get).contains event

def run : IO Unit := do
  let f ← fixture
  let value ← withTransaction f.ops do
    check ((← f.state.get) == .active) "body runs after BEGIN"
    f.events.modify (·.push "body")
    pure 42
  check (value == 42 && (← f.state.get) == .idle) "successful transaction result"
  check (!(← f.claimed.get) && !(← has f "rollback")) "success releases ownership"

  let f ← fixture .active
  let failure ← errorOf (withTransaction f.ops (f.events.modify (·.push "body")))
  check (!failure.isEmpty) "existing transaction is rejected"
  check (!(← has f "begin") && !(← has f "body") && !(← has f "rollback"))
    "existing transaction remains untouched"
  check ((← f.state.get) == .active && !(← f.claimed.get)) "caller retains transaction"

  let f ← fixture
  f.claimed.set true
  let failure ← errorOf (withTransaction f.ops (f.events.modify (·.push "body")))
  check (!failure.isEmpty && (← f.claimed.get)) "failed claim preserves existing owner"
  check (!(← has f "release") && !(← has f "body")) "failed claim does not release another owner"

  let f ← fixture
  let ops := { f.ops with begin := do
    f.events.modify (·.push "begin")
    throw (IO.userError "begin failed") }
  let failure ← errorOf (withTransaction ops (f.events.modify (·.push "body")))
  check (!failure.isEmpty && !(← has f "body") && !(← has f "commit"))
    "failed BEGIN never enters the body"
  check (!(← f.claimed.get)) "failed BEGIN releases ownership"

  let f ← fixture
  let failure ← errorOf (withTransaction f.ops (α := Unit) do
    throw (IO.userError "original body failure"))
  check (failure.startsWith "original body failure") "body error is preserved"
  check ((← has f "rollback") && (← f.state.get) == .idle && !(← f.claimed.get))
    "body failure rolls back and releases ownership"

  let f ← fixture
  let failure ← errorOf (withTransaction f.ops (f.state.set .aborted))
  check (!failure.isEmpty && !(← has f "commit") && (← has f "rollback"))
    "aborted body cannot commit successfully"
  check ((← f.state.get) == .idle) "aborted transaction is rolled back"

  let f ← fixture
  let ops := { f.ops with commit := do
    f.events.modify (·.push "commit")
    throw (IO.userError "commit rejected") }
  let failure ← errorOf (withTransaction ops (pure ()))
  check (!failure.isEmpty && (← has f "rollback")) "failed active COMMIT rolls back"
  check ((← f.state.get) == .idle && !(← f.claimed.get)) "rejected commit leaves clean state"
  check (((← f.events.get).toList.count "commit") == 1) "COMMIT is never retried"

  let f ← fixture
  let ops := { f.ops with commit := do
    f.events.modify (·.push "commit")
    f.state.set .idle
    throw (IO.userError "commit acknowledgement lost") }
  let failure ← errorOf (withTransaction ops (pure ()))
  check (!failure.isEmpty && (← has f "close")) "uncertain commit closes connection"
  check (!(← has f "rollback") && (← f.state.get) == .unusable)
    "uncertain commit cannot claim that rollback succeeded"

  let f ← fixture
  let ops := { f.ops with rollback := do
    f.events.modify (·.push "rollback")
    throw (IO.userError "rollback failed") }
  let failure ← errorOf (withTransaction ops (α := Unit) do
    throw (IO.userError "original body failure"))
  check (failure.startsWith "original body failure") "cleanup error retains original cause"
  check ((failure.splitOn "rollback failed").length > 1) "cleanup failure is reported"
  check ((← has f "close") && !(← f.claimed.get)) "failed cleanup closes and releases"

  let f ← fixture
  let ops := { f.ops with rollback := f.events.modify (·.push "rollback") }
  let failure ← errorOf (withTransaction ops (α := Unit) do
    throw (IO.userError "original body failure"))
  check (failure.startsWith "original body failure" && (← has f "close"))
    "a rollback acknowledgement without idle state retires the connection"
  check (!(← f.claimed.get)) "unverified rollback releases ownership"

  IO.println "transactions: injected lifecycle failures passed"

end TransactionLifecycle
