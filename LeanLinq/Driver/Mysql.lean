import LeanLinq
import LeanLinq.Driver.TextCell
import LeanLinq.Driver.Transaction
import LeanLinq.Driver.Wire

/-! # Native MySQL driver (libmysqlclient)

Typed queries in, typed rows out, over prepared statements (via
`native/mysql_shim.c`):

- **Placeholders**: MySQL's wire form is positional `?`. The compiled SQL
  keeps `:name` as its stable logical form; this driver rewrites each
  *occurrence* to `?` and emits the value list in occurrence order —
  MySQL's placeholders are unnamed, so a repeated `:name` reference
  repeats its value (unlike PostgreSQL's `$N`). Longest-name-first
  matching, so `:p1` never clobbers `:p10`.
- **Values**: text both directions. Parameters bind as strings (MySQL
  coerces text in typed contexts — the PostgreSQL text-format
  philosophy); result cells arrive as strings and decode through the
  shared `Driver.parseCell`. -/

namespace LeanLinq.Mysql

private opaque ConnP : NonemptyType
/-- An open MySQL connection. -/
def Conn : Type := ConnP.type
instance : Nonempty Conn := ConnP.property

@[extern "ll_my_connect"]
opaque connectRaw (host : @&String) (port : UInt32) (user pass db : @&String) :
  IO Conn

/-- Connect — defaults match the repo's docker-compose service. -/
def connect (host : String := "127.0.0.1") (port : UInt32 := 3307)
    (user : String := "root") (pass : String := "testpass")
    (db : String := "testdb") : IO Conn :=
  connectRaw host port user pass db

@[extern "ll_my_close"]
opaque Conn.close (conn : @&Conn) : IO Unit

/-- Execute a raw SQL batch (DDL / seed / BEGIN / ROLLBACK). -/
@[extern "ll_my_exec_raw"]
opaque Conn.execRaw (conn : @&Conn) (sql : @&String) : IO Unit

@[extern "ll_my_tx_claim"]
private opaque claimTransaction (conn : @&Conn) : IO Unit

@[extern "ll_my_tx_release"]
private opaque releaseTransaction (conn : @&Conn) : IO Unit

@[extern "ll_my_tx_state"]
private opaque transactionStateRaw (conn : @&Conn) : IO UInt32

@[extern "ll_my_tx_control"]
private opaque transactionControl (conn : @&Conn) (operation : UInt32) : IO Unit

/-- Run a top-level transaction at the engine's default isolation level.
The connection must be used exclusively throughout the action. Existing
transactions and nested managed scopes are rejected. Transaction controls
and state checks are separate from a `Db` body's operation bill. -/
def Conn.withTransaction (conn : Conn) (action : IO α) : IO α :=
  Driver.withTransaction {
    claim := claimTransaction conn
    release := releaseTransaction conn
    state := do
      match ← transactionStateRaw conn with
      | 0 => return .idle
      | 1 => return .active
      | 2 => return .aborted
      | _ => return .unusable
    begin := transactionControl conn 0
    commit := transactionControl conn 1
    rollback := transactionControl conn 2
    close := conn.close } action

@[extern "ll_my_query"]
private opaque queryRaw (conn : @&Conn) (sql : @&String)
    (vals : @&Array (Option String)) : IO (Array (Array (Option String)))

@[extern "ll_my_exec_params"]
private opaque execParamsRaw (conn : @&Conn) (sql : @&String)
    (vals : @&Array (Option String)) : IO UInt32

/-! ## Wire form: occurrence-order `?` placeholders, text values -/

/-- The text value for one compiled parameter: auto parameters carry their
values; user-named ones resolve from the typed cells. -/
private def paramText (cells : List (String × ((t : SqlPrim) × Nullable t)))
    (name : String) (v : SqlValue) : IO (Option String) := do
  match v with
  | .null =>
      let bare := String.ofList (name.toList.drop 1)
      match cells.find? (·.1 == bare) with
      | some (_, ⟨t, cell⟩) => pure (cell.map (Driver.cellText t))
      | none => throw (IO.userError s!"mysql bind: no typed value for {name}")
  | v => pure (Driver.valueText v)

/-- Prepare positional SQL and values without connecting. Quoted SQL text is
preserved, and only real placeholder occurrences contribute bound values. -/
def toWire (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) :
    IO (String × Array (Option String)) := do
  let entries := compiled.params.toList.map (fun (name, _) => (name, "?"))
  let (sql, names) := Driver.rewriteParams compiled.sql entries
  let lookup := fun (n : String) => do
    match compiled.params.toList.find? (·.1 == n) with
    | some (_, v) => paramText cells n v
    | none => throw (IO.userError "mysql toWire: unknown param")
  return (sql, ← names.mapM lookup)

/-! ## Text decode → `Values` -/

private def readCell (t : SqlPrim) : Option String → IO (Nullable t)
  | none => pure none
  | some s => IO.ofExcept ((Driver.parseCell t s).mapError IO.userError)

private def readRow : (s : Schema) → List (Option String) → IO (Values s)
  | [], [] => pure .nil
  | (nm, c) :: rest, cell :: cells => do
      pure (.cons (← Driver.cellFromWire nm c (← readCell c.ty cell))
        (← readRow rest cells))
  | _, _ => throw (IO.userError "mysql: column count mismatch")

/-! ## Typed execution -/

def Conn.query (conn : Conn) (q : Query c s)
    (ps : ParamEnv c.params := by exact .nil) : IO (List (Values s)) := do
  let compiled ← Driver.checkedSql (q.toSqlChecked .mysql)
  let (sql, vals) ← toWire compiled ps.toCells
  let rows ← queryRaw conn sql vals
  rows.toList.mapM fun r => readRow s r.toList

def Conn.queryCell (conn : Conn) (sc : ScalarQuery c ⟨t, n⟩)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  let compiled ← Driver.checkedSql (sc.toSqlChecked .mysql)
  let (sql, vals) ← toWire compiled ps.toCells
  let rows ← queryRaw conn sql vals
  match rows[0]? with
  | some row =>
      match row[0]? with
      | some cell => readCell t cell
      | none => pure none
  | none => pure none

/-- Execute a statement and report the affected-row count. -/
private def execCompiled (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Nat := do
  let (sql, vals) ← toWire compiled cells
  return (← execParamsRaw conn sql vals).toNat

def Conn.execInsert (conn : Conn) (i : InsertStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat := do
  execCompiled conn (← Driver.checkedSql (i.toSqlChecked .mysql)) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat := do
  execCompiled conn (← Driver.checkedSql (u.toSqlChecked .mysql)) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat := do
  execCompiled conn (← Driver.checkedSql (d.toSqlChecked .mysql)) ps.toCells

def Conn.execInsertSelect (conn : Conn) (st : InsertSelectStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat := do
  execCompiled conn (← Driver.checkedSql (st.toSqlChecked .mysql)) ps.toCells

def Conn.execInsertValues (conn : Conn) (st : InsertValuesStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat := do
  execCompiled conn (← Driver.checkedSql (st.toSqlChecked .mysql)) ps.toCells

/-! ## `Db` interpretation (sequential, one statement per round) -/

private def ops (conn : Conn) (ps : ParamEnv c.params) :
    {β : Type} → DbOp c β → IO β
  | _, .fetch q => conn.query q ps
  | _, .fetchCell sc => conn.queryCell sc ps
  | _, .insert (inst := _) i => conn.execInsert i ps
  | _, .update (inst := _) u => conn.execUpdate u ps
  | _, .delete (inst := _) d => conn.execDelete d ps
  | _, .insertSelect (inst := _) st => conn.execInsertSelect st ps
  | _, .insertValues (inst := _) st => conn.execInsertValues st ps
  | _, .raise message => throw (IO.userError message)

private def scopedOps (conn : Conn) (ps : ParamEnv c.params) :
    {β : Type} → DbE c β → IO β
  | _, .op e => ops conn ps e
  | _, .transaction body =>
      conn.withTransaction (FreerD.foldM (E := DbOp c) (m := IO)
        (fun e => ops conn ps e) body)

end Mysql

/-- Interpret a `Db` program against live MySQL, one statement per round,
gated by the usual budget obligation. -/
def DbP.execMy {w : Wp α} (f : DbP c α w) (conn : Mysql.Conn) (budget : Nat)
    (ps : ParamEnv c.params := by exact .nil)
    {r : Grade} [HasBill w r]
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : IO α :=
  FreerD.foldM (E := DbE c) (m := IO) (fun e => Mysql.scopedOps conn ps e) f

/-- The unchecked door over the wire: no budget, no obligation. -/
def DbP.execMyAll {w : Wp α} (f : DbP c α w) (conn : Mysql.Conn)
    (ps : ParamEnv c.params := by exact .nil) : IO α :=
  FreerD.foldM (E := DbE c) (m := IO) (fun e => Mysql.scopedOps conn ps e) f

namespace FreerD
export DbP (execMy execMyAll)
end FreerD

end LeanLinq
