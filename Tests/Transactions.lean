import LeanLinq

/-! Transactions retain the bill of every body operation. Their effect signature
prevents nesting; their model commits on success and restores the complete
entry environment on failure, while preserving earlier outside writes. -/

namespace Transactions
open LeanLinq

abbrev AccountS : Schema := [("Id", .int), ("Balance", .int)]
abbrev AuditS : Schema := [("Id", .int)]
abbrev C : Ctx := { tables := [
  ("transaction_accounts", AccountS), ("transaction_audit", AuditS)] }

def accounts : Table "transaction_accounts" AccountS := ⟨⟩
def audit : Table "transaction_audit" AuditS := ⟨⟩
def initialAccounts : List (Values AccountS) := [
  .cons 1 (.cons 10 .nil), .cons 2 (.cons 20 .nil)]
def initialAudit : List (Values AuditS) := [.cons 0 .nil]
def seed : TableEnv C.tables := .cons initialAccounts (.cons initialAudit .nil)
def ee : EvalEnv C := ⟨seed, .nil, none⟩

def accountQuery : Query C AccountS := Query.from' (ts := C) accounts
def addBalance (amount : Int) : UpdateStmt C "transaction_accounts" AccountS :=
  accounts.update |>.setWith "Balance" (fun row => row["Balance"] + SqlExpr.int amount)
def addAudit (id : Int) : InsertStmt C "transaction_audit" AuditS :=
  audit.insert |>.value "Id" (SqlExpr.int id)
def addAccount : InsertStmt C "transaction_accounts" AccountS :=
  accounts.insert |>.value "Id" 3 |>.value "Balance" 30

-- This is an evaluator error, distinct from a successful SQL NULL result.
def failingQuery : Query C [("Bad", .int)] := accountQuery.select fun _ =>
  ![((SqlExpr.int 1 : SqlExprP _ C .int) / SqlExpr.int 0).as "Bad"]

private def snapshot (env : TableEnv C.tables) :
    List (Values AccountS) × List (Values AuditS) :=
  match env with | .cons rows (.cons events .nil) => (rows, events)

def creditedAccounts : List (Values AccountS) := [
  .cons 1 (.cons 20 .nil), .cons 2 (.cons 30 .nil)]
def priorAccounts : List (Values AccountS) := [
  .cons 1 (.cons 110 .nil), .cons 2 (.cons 120 .nil)]

def twoWrites : TxDb C 2 (Nat × Nat) := db! {
  let updated ← (addBalance 10).execUpdate
  let inserted ← (addAudit 7).execInsert
  return (updated, inserted)
}

def committed : Db C 2 (Nat × Nat) := Db.transaction twoWrites
def syntaxCommitted : Db C 2 (Nat × Nat) := transaction {
  let updated ← (addBalance 10).execUpdate
  let inserted ← (addAudit 7).execInsert
  return (updated, inserted)
}

-- BEGIN/COMMIT are lifecycle operations; the grade counts body effects.
example : Db C 2 (Nat × Nat) := committed
#guard (committed.exec 2 seed).toOption == some (2, 1)
#check_failure committed.exec 1 seed
#guard (committed.runCount ee).toOption == some ((2, 1), 2)
#guard (syntaxCommitted.runCount ee).toOption == some ((2, 1), 2)
#check_failure twoWrites.exec 2 seed
#guard (committed.runOutcomeSt .nil none seed).result.toOption == some (2, 1)
#guard snapshot (committed.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, [.cons 0 .nil, .cons 7 .nil])
#guard (committed.runOutcomeSt .nil none seed).count == 2

-- The ordinary success adequacy theorem still observes the body's full bill.
#guard (committed.runWithP .nil none seed).toOption.map
  (fun result => (result.val.1, result.val.2.2)) == some ((2, 1), 2)

def emptyBody : TxDb C 0 Nat := db! { return 42 }
def emptyTransaction : Db C 0 Nat := Db.transaction emptyBody
#guard (emptyTransaction.exec 0 seed).toOption == some 42
#guard (emptyTransaction.runOutcomeSt .nil none seed).count == 0
#guard snapshot (emptyTransaction.runOutcomeSt .nil none seed).state ==
  (initialAccounts, initialAudit)

-- The outside mode cannot be hidden in a helper and then used inside a body.
def outsideHelper : Db C 2 (Nat × Nat) := committed
#check_failure Db.transaction committed
#check_failure (outsideHelper : TxDb C 2 (Nat × Nat))
#check_failure (db! {
  let result ← outsideHelper
  return result
} : TxDb C 2 (Nat × Nat))
#check_failure (DbP.map id outsideHelper : TxDb C 2 (Nat × Nat))
#check_failure FreerD.bindS twoWrites (fun _ => outsideHelper)
#check_failure (transaction {
  let result ← transaction { return 42 }
  return result
} : Db C 0 Nat)

-- The body uses the original Freer monad over ordinary database operations.
-- Only the outside signature has a transaction effect; no new Freer node is
-- required, and a raw constructor cannot nest that effect inside its body.
def rawCommitted : Db C 2 (Nat × Nat) :=
  FreerD.liftE (spec := dbWp) (DbE.transaction twoWrites)
#guard (rawCommitted.runCount ee).toOption == some ((2, 1), 2)
example : Db C 2 (Nat × Nat) :=
  DbP.relax (mode := .outside) (FreerD.liftE (spec := dbWp) (DbE.transaction twoWrites))
#check_failure (DbP.relax (mode := .outside)
  (FreerD.liftE (spec := dbWp) (DbE.transaction twoWrites)) :
  Db C 1 (Nat × Nat))
#check_failure (DbE.transaction twoWrites : DbOp C (Nat × Nat))
#check_failure DbE.transaction rawCommitted
#check_failure FreerD.bindE (E := DbOp C) (spec := dbOpWp)
  (DbE.transaction twoWrites) (fun result => FreerD.pure result)
#check_failure (FreerD.weaken (Wp.le_refl _) rawCommitted : TxDb C 2 (Nat × Nat))

-- The unchanged generic fold accepts either signature. An outside handler sees
-- the transaction explicitly; normal model handlers interpret its whole body.
#guard (FreerD.foldM (fun {β} (_ : DbOp C β) => (none : Option β)) twoWrites).isNone
private def observeEffect {β : Type} (effect : DbE C β) : Except String β :=
  match effect with
  | .op _ => .error "ordinary operation"
  | .transaction _ => .error "transaction block"
#guard match FreerD.foldM observeEffect committed with
  | .error message => message == "transaction block"
  | .ok _ => false

-- Continuations run against committed state and contribute their own bill.
def afterCommit : Db C 3 (List (Values AccountS)) := db! {
  let _committed ← committed
  let rows ← accountQuery.execQuery
  return rows
}
#guard (afterCommit.runCount ee).toOption == some (creditedAccounts, 3)

def failureAfterCommit : Db C 3 Unit := db! {
  let _committed ← committed
  let _failed ← failingQuery.execQuery
  return ()
}
-- A later outside failure cannot roll back an already committed body.
#guard match (failureAfterCommit.runOutcomeSt .nil none seed).result with
  | .error .divByZero => true
  | _ => false
#guard snapshot (failureAfterCommit.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, [.cons 0 .nil, .cons 7 .nil])
#guard (failureAfterCommit.runOutcomeSt .nil none seed).count == 3

def failedBody : TxDb C 3 Unit := db! {
  let _updated ← (addBalance 10).execUpdate
  let _inserted ← (addAudit 7).execInsert
  let _failed ← failingQuery.execQuery
  return ()
}
def rolledBack : Db C 3 Unit := Db.transaction failedBody

-- The attempted failing fetch counts; neither table retains body changes.
#guard match (rolledBack.runOutcomeSt .nil none seed).result with
  | .error .divByZero => true
  | _ => false
#guard snapshot (rolledBack.runOutcomeSt .nil none seed).state ==
  (initialAccounts, initialAudit)
#guard (rolledBack.runOutcomeSt .nil none seed).count == 3
#guard match rolledBack.runWith ee with
  | .error .divByZero => true
  | _ => false

def failedAfterPriorWrites : Db C 6 Unit := db! {
  let _updated ← (addBalance 100).execUpdate
  let _inserted ← (addAudit 5).execInsert
  let _rolledBack ← rolledBack
  let _continuation ← (addAudit 99).execInsert
  return ()
}

-- Restore the transaction's entry snapshot, not the program's initial state.
-- No continuation marker appears, and its operation is not counted.
#guard match (failedAfterPriorWrites.runOutcomeSt .nil none seed).result with
  | .error .divByZero => true
  | _ => false
#guard snapshot (failedAfterPriorWrites.runOutcomeSt .nil none seed).state ==
  (priorAccounts, [.cons 0 .nil, .cons 5 .nil])
#guard (failedAfterPriorWrites.runOutcomeSt .nil none seed).count == 5

-- Exercise every member of the database effect signature inside one scope.
def allEffectsBody : TxDb C 7 (List Nat) := db! {
  let inserted ← addAccount.execInsert
  let updated ← (addBalance 10).execUpdate
  let rows ← accountQuery.execQuery
  let count ← accountQuery.count.fetch
  let selected ← (audit.insertFrom (accountQuery.select fun row =>
    ![row["Id"].as "Id"])).execInsertSelect
  let batch ← (audit.insertAll (ts := C) [.cons 7 .nil, .cons 8 .nil]).execInsertValues
  let deleted ← (accounts.delete (ts := C) |>.where' (fun row => row["Id"] ==. 3)).execDelete
  return [inserted, updated, rows.length, (count.getD 0).toNat, selected, batch, deleted]
}
def allEffects : Db C 7 (List Nat) := Db.transaction allEffectsBody
#guard (allEffects.exec 7 seed).toOption == some [1, 3, 3, 3, 3, 2, 1]
#guard (allEffects.runOutcomeSt .nil none seed).count == 7
#guard snapshot (allEffects.runOutcomeSt .nil none seed).state ==
  (creditedAccounts, [.cons 0 .nil, .cons 1 .nil, .cons 2 .nil,
    .cons 3 .nil, .cons 7 .nil, .cons 8 .nil])
#check_failure allEffects.exec 6 seed

-- A helper that performs ordinary effects can be shared across both modes.
def sharedCount {mode : ScopeMode} : DbM mode C 1 Nat :=
  accountQuery.fetchCount
def outsideCount : Db C 1 Nat := sharedCount
def insideCount : TxDb C 1 Nat := sharedCount
#guard (outsideCount.exec 1 seed).toOption == some 2
#guard ((Db.transaction insideCount).exec 1 seed).toOption == some 2

-- The fetched length refinement keeps its dependent bound inside a body.
def boundedBody : TxDb C 3 (List Nat) := db! {
  let limited ← accountQuery.fetchLimit 2
  let counts ← for _row in limited.val do sharedCount
  return counts
}
def boundedTransaction : Db C 3 (List Nat) := Db.transaction boundedBody
#guard (boundedTransaction.exec 3 seed).toOption == some [2, 2]
#guard (boundedTransaction.runCount ee).toOption == some ([2, 2], 3)
#check_failure boundedTransaction.exec 2 seed

end Transactions
