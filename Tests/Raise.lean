import Tests.Transactions

/-! Explicit errors are available in ordinary programs and transaction bodies.
Raising contributes no database operation. Its conservative success spec keeps
preceding operations in the bill; the existing adequacy theorem still describes
successful runs, rather than asserting a general bound for failure outcomes. -/

namespace Raise
open LeanLinq Transactions

private def snapshot (env : TableEnv C.tables) :
    List (Values AccountS) × List (Values AuditS) :=
  match env with | .cons rows (.cons events .nil) => (rows, events)

private def errorMessage {α : Type} : Except EvalError α → Option String
  | .error (.userError message) => some message
  | _ => none

def dynamicReason (label : String) (code : Nat) : String := s!"{label}: {code}"

-- One helper is usable both outside and inside a transaction.
def requireFlag {mode : ScopeMode} (allowed : Bool) (reason : String) :
    DbM mode C 0 Unit :=
  DbP.relax (mode := mode) (if allowed then Db.pure () else Db.raise reason)

def outsideCheck (allowed : Bool) (code : Nat) : Db C 0 Unit :=
  requireFlag allowed (dynamicReason "outside" code)
def insideCheck (allowed : Bool) (code : Nat) : TxDb C 0 Unit :=
  requireFlag allowed (dynamicReason "inside" code)

#guard (outsideCheck true 7 |>.exec 0 seed).toOption == some ()
#guard errorMessage (outsideCheck false 7 |>.exec 0 seed) == some "outside: 7"
#guard (outsideCheck false 7 |>.runOutcomeSt .nil none seed).count == 0
#guard snapshot (outsideCheck false 7 |>.runOutcomeSt .nil none seed).state ==
  (initialAccounts, initialAudit)
#guard errorMessage ((Db.transaction (insideCheck false 8)).exec 0 seed) == some "inside: 8"
#guard (DbP.runOutcomeSt (mode := .outside) .nil none
  (Db.transaction (insideCheck false 8)) seed).count == 0

def bareOutside : Db C 0 Unit := db! {
  raise (dynamicReason "bare outside" 9)
  return ()
}
def bareInside : Db C 0 Unit := transaction {
  raise (dynamicReason "bare inside" 10)
  return ()
}
def dottedRaise : Db C 0 Unit := db! {
  let _ ← .raise "dotted raise"
  return ()
}
#guard errorMessage (bareOutside.exec 0 seed) == some "bare outside: 9"
#guard errorMessage (bareInside.exec 0 seed) == some "bare inside: 10"
#guard errorMessage (dottedRaise.exec 0 seed) == some "dotted raise"

-- The reason can depend on an earlier database result.
def raiseFetchedCount : Db C 1 Unit := db! {
  let rows ← accountQuery.execQuery
  let _raised ← Db.raise (dynamicReason "account count" rows.length)
  return ()
}
#guard errorMessage (raiseFetchedCount.exec 1 seed) == some "account count: 2"
#guard (raiseFetchedCount.runOutcomeSt .nil none seed).count == 1

-- Outside a transaction, earlier writes remain and later effects are skipped.
-- The unreachable final INSERT is still conservatively included in the bill.
def outsideRaised : Db C 3 Unit := db! {
  let _updated ← (addBalance 100).execUpdate
  let _inserted ← (addAudit 5).execInsert
  let _raised ← requireFlag false (dynamicReason "outside writes" 2)
  let _continuation ← (addAudit 99).execInsert
  return ()
}
#guard errorMessage (outsideRaised.runOutcomeSt .nil none seed).result ==
  some "outside writes: 2"
#guard (outsideRaised.runOutcomeSt .nil none seed).count == 2
#guard snapshot (outsideRaised.runOutcomeSt .nil none seed).state ==
  (priorAccounts, [.cons 0 .nil, .cons 5 .nil])

def raisingBody : TxDb C 3 Unit := db! {
  let _updated ← (addBalance 10).execUpdate
  let _inserted ← (addAudit 7).execInsert
  let _raised ← requireFlag false (dynamicReason "transaction writes" 2)
  let _bodyContinuation ← (addAudit 88).execInsert
  return ()
}
def raisedAfterPriorWrites : Db C 6 Unit := db! {
  let _updated ← (addBalance 100).execUpdate
  let _inserted ← (addAudit 5).execInsert
  let _transaction ← Db.transaction raisingBody
  let _outerContinuation ← (addAudit 99).execInsert
  return ()
}
-- Rollback restores both tables to the scope entry, retaining outside writes.
-- Neither the body's marker 88 nor the outside marker 99 can execute.
#guard errorMessage (raisedAfterPriorWrites.runOutcomeSt .nil none seed).result ==
  some "transaction writes: 2"
#guard (raisedAfterPriorWrites.runOutcomeSt .nil none seed).count == 4
#guard snapshot (raisedAfterPriorWrites.runOutcomeSt .nil none seed).state ==
  (priorAccounts, [.cons 0 .nil, .cons 5 .nil])
#guard errorMessage (raisedAfterPriorWrites.runWithP .nil none seed) ==
  some "transaction writes: 2"

def raiseAfterCommit : Db C 3 Unit := db! {
  let _committed ← committed
  let _raised ← Db.raise "after commit"
  let _continuation ← (addAudit 99).execInsert
  return ()
}
#guard errorMessage (raiseAfterCommit.runOutcomeSt .nil none seed).result ==
  some "after commit"
#guard (raiseAfterCommit.runOutcomeSt .nil none seed).count == 2
#guard snapshot (raiseAfterCommit.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, [.cons 0 .nil, .cons 7 .nil])

def conditionalBody (allowed : Bool) : TxDb C 2 Unit := db! {
  let _updated ← (addBalance 10).execUpdate
  let _checked ← requireFlag allowed "conditional refusal"
  let _inserted ← (addAudit 7).execInsert
  return ()
}
def conditionalTransaction (allowed : Bool) : Db C 2 Unit :=
  Db.transaction (conditionalBody allowed)
#guard (conditionalTransaction true |>.exec 2 seed).toOption == some ()
#guard (conditionalTransaction true |>.runOutcomeSt .nil none seed).count == 2
#guard (conditionalTransaction true |>.runWithP .nil none seed).toOption.map
  (fun result => result.val.2.2) == some 2
#guard snapshot (conditionalTransaction true |>.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, [.cons 0 .nil, .cons 7 .nil])
#guard errorMessage (conditionalTransaction false |>.exec 2 seed) == some "conditional refusal"
#guard (conditionalTransaction false |>.runOutcomeSt .nil none seed).count == 1
#guard snapshot (conditionalTransaction false |>.runOutcomeSt .nil none seed).state ==
  (initialAccounts, initialAudit)

-- Raw effects inherit the same zero bill; the generic Freer tree is unchanged.
def rawInsideRaise : TxDb C 0 Unit :=
  DbP.relax (mode := .inside)
    (FreerD.liftE (spec := dbOpWp) (DbOp.raise (c := C) "raw inside"))
def rawOutsideRaise : Db C 0 Unit :=
  DbP.relax (mode := .outside)
    (FreerD.liftE (spec := dbWp) (DbE.op (DbOp.raise (c := C) "raw outside")))
#guard errorMessage (rawInsideRaise.runOutcomeSt .nil none seed).result == some "raw inside"
#guard (rawInsideRaise.runOutcomeSt .nil none seed).count == 0
#guard errorMessage (rawOutsideRaise.exec 0 seed) == some "raw outside"
#guard (rawOutsideRaise.runOutcomeSt .nil none seed).count == 0

def writeThenRaise : Db C 1 Unit := db! {
  let _updated ← (addBalance 10).execUpdate
  let _raised ← Db.raise "after one write"
  return ()
}
#guard errorMessage (writeThenRaise.exec 1 seed) == some "after one write"
#guard (writeThenRaise.runOutcomeSt .nil none seed).count == 1
#guard snapshot (writeThenRaise.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, initialAudit)
#check_failure writeThenRaise.exec 0 seed
#check_failure (DbP.relax (mode := .outside) writeThenRaise : Db C 0 Unit)

-- Even at the raw success specification, raising does not make the preceding
-- write disappear. A zero bill would require its hypothetical success at cost
-- one to satisfy a postcondition demanding cost zero, which is impossible.
def writeThenRaiseWp : Wp Unit :=
  (dbOpWp (DbOp.update (addBalance 10))).bind
    (fun _ => dbOpWp (DbOp.raise (c := C) "after one write"))

def rawWriteThenRaise : DbP C Unit writeThenRaiseWp :=
  FreerD.bindS (DbP.update (mode := .outside) (addBalance 10)) (fun _ =>
    FreerD.liftE (spec := dbWp) (DbE.op (DbOp.raise (c := C) "after one write")))
#guard errorMessage (DbP.runOutcomeSt (mode := .outside) .nil none rawWriteThenRaise seed).result ==
  some "after one write"
#guard (DbP.runOutcomeSt (mode := .outside) .nil none rawWriteThenRaise seed).count == 1

theorem writeThenRaiseWp_not_zero : ¬ writeThenRaiseWp.le (Wp.bill 0) := by
  intro h
  have impossible := h (fun _ _ cost => cost ≤ 0) (fun _ => 0) 0
    (by intro result sizes cost bound; simpa using bound)
  change ∀ affected : Nat, affected ≤ 0 → 1 ≤ 0 at impossible
  exact Nat.not_succ_le_zero 0 (impossible 0 (Nat.le_refl 0))

end Raise
