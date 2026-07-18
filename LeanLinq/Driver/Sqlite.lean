import LeanLinq
import LeanLinq.Driver.TextCell

/-! # Native SQLite driver

Real execution over the system sqlite3 library (via `native/sqlite3_shim.c`):
typed queries in, typed rows out. Parameters are **bound natively** — the
compile side never inlined a literal, and now the execution side doesn't
either: auto parameters carry their `SqlValue`s in `CompiledSql.params`, and
user-named parameters come from the same typed `ParamEnv c.params` the
evaluator reads. Rows are decoded schema-directed into `Values s` using the
`SqlPrim.interp` conventions (milli-unit decimals, normalized date-times,
lower-case guids), so driver output is cell-for-cell comparable with
`Query.run`.

Errors surface as `IO.userError` carrying `sqlite3_errmsg`. Connections and
statements are external objects with finalizers; a statement keeps its
connection alive. -/

namespace LeanLinq.Sqlite

private opaque ConnP : NonemptyType
/-- An open SQLite database connection. -/
def Conn : Type := ConnP.type
instance : Nonempty Conn := ConnP.property

private opaque StmtP : NonemptyType
private def Stmt : Type := StmtP.type
instance : Nonempty Stmt := StmtP.property

/-- Open (or create) a database file. `":memory:"` works as in sqlite. -/
@[extern "ll_sqlite3_open"]
opaque connect (path : @&String) : IO Conn

/-- Close the connection (idempotent; the finalizer is the safety net). -/
@[extern "ll_sqlite3_close"]
opaque Conn.close (conn : @&Conn) : IO Unit

/-- Execute a raw SQL batch (DDL, seeds, `BEGIN`/`ROLLBACK`). Not for
queries — results are discarded. -/
@[extern "ll_sqlite3_exec_raw"]
opaque Conn.execRaw (conn : @&Conn) (sql : @&String) : IO Unit

@[extern "ll_sqlite3_prepare"]
private opaque prepareRaw (conn : Conn) (sql : @&String) : IO Stmt

@[extern "ll_sqlite3_bind_parameter_index"]
private opaque bindParameterIndex (stmt : @&Stmt) (name : @&String) : IO UInt32

@[extern "ll_sqlite3_bind_int64"]
private opaque bindInt64 (stmt : @&Stmt) (idx : UInt32) (v : Int64) : IO Unit

@[extern "ll_sqlite3_bind_double"]
private opaque bindDouble (stmt : @&Stmt) (idx : UInt32) (v : Float) : IO Unit

@[extern "ll_sqlite3_bind_text"]
private opaque bindText (stmt : @&Stmt) (idx : UInt32) (v : @&String) : IO Unit

@[extern "ll_sqlite3_bind_null"]
private opaque bindNull (stmt : @&Stmt) (idx : UInt32) : IO Unit

/-- `100` = row available, `101` = done; other codes raise. -/
@[extern "ll_sqlite3_step"]
private opaque step (stmt : @&Stmt) : IO UInt32

/-- sqlite fundamental type codes; `5` = NULL. -/
@[extern "ll_sqlite3_column_type"]
private opaque columnType (stmt : @&Stmt) (i : UInt32) : IO UInt32

@[extern "ll_sqlite3_column_int64"]
private opaque columnInt64 (stmt : @&Stmt) (i : UInt32) : IO Int64

@[extern "ll_sqlite3_column_double"]
private opaque columnDouble (stmt : @&Stmt) (i : UInt32) : IO Float

@[extern "ll_sqlite3_column_text"]
private opaque columnText (stmt : @&Stmt) (i : UInt32) : IO String

/-! ## Parameter binding -/

/-- Bind an auto parameter (a staged literal's value). Decimal digit strings
bind as text — SQLite's numeric affinity converts, matching the semantics
the inlined-literal test harness always had. -/
private def bindValue (st : Stmt) (idx : UInt32) : SqlValue → IO Unit
  | .int i => bindInt64 st idx (.ofInt i)
  | .long i => bindInt64 st idx (.ofInt i)
  | .double f => bindDouble st idx f
  | .decimal d => bindText st idx d
  | .string s => bindText st idx s
  | .bool b => bindInt64 st idx (if b then 1 else 0)
  | .dateTime s => bindText st idx s
  | .guid g => bindText st idx g
  | .null => bindNull st idx

/-- Bind a typed parameter cell (`ParamEnv` conventions: milli-unit
decimals rendered back to digit text, NULL cell → SQL NULL). -/
private def bindCell (st : Stmt) (idx : UInt32) : (t : SqlPrim) → Nullable t → IO Unit
  | _, none => bindNull st idx
  | .int, some i => bindInt64 st idx (.ofInt i)
  | .long, some i => bindInt64 st idx (.ofInt i)
  | .double, some f => bindDouble st idx f
  | .decimal, some m => bindText st idx (renderDecimal m)
  | .string, some s => bindText st idx s
  | .bool, some b => bindInt64 st idx (if b then 1 else 0)
  | .dateTime, some s => bindText st idx s
  | .guid, some g => bindText st idx g

/-- Bind every placeholder of a compiled statement: auto parameters carry
their values; user-named ones (recorded with a `.null` placeholder — see
`refParam`) resolve from the typed cells. -/
private def bindParams (st : Stmt) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Unit := do
  for (name, v) in compiled.params do
    let idx ← bindParameterIndex st name
    if idx == 0 then
      throw (IO.userError s!"sqlite3 bind: placeholder {name} not found")
    match v with
    | .null =>
        -- strip the dialect prefix (":minAge" → "minAge")
        let bare := String.ofList (name.toList.drop 1)
        match cells.find? (·.1 == bare) with
        | some (_, ⟨t, cell⟩) => bindCell st idx t cell
        | none => throw (IO.userError s!"sqlite3 bind: no typed value for {name}")
    | v => bindValue st idx v

/-! ## Row decoding -/

private def readCell (st : Stmt) (i : UInt32) : (t : SqlPrim) → IO (Nullable t) := fun t => do
  if (← columnType st i) == 5 then
    pure none
  else
    match t with
    | .int => pure (some (← columnInt64 st i).toInt)
    | .long => pure (some (← columnInt64 st i).toInt)
    | .double => pure (some (← columnDouble st i))
    | .decimal => do
        let txt ← columnText st i
        match Driver.parseDecimal? txt with
        | some m => pure (some m)
        | none => throw (IO.userError s!"unreadable decimal cell text: '{txt}'")
    | .string => pure (some (← columnText st i))
    | .bool => pure (some ((← columnInt64 st i) != 0))
    | .dateTime => pure (some (normDateTime (← columnText st i)))
    | .guid => pure (some (← columnText st i).toLower)

private def readRow (st : Stmt) : (s : Schema) → (i : UInt32) → IO (Values s)
  | [], _ => pure .nil
  | (nm, c) :: rest, i => do
      pure (.cons (← Driver.cellFromWire nm c (← readCell st i c.ty))
        (← readRow st rest (i + 1)))

private def collectRows (st : Stmt) (s : Schema) : IO (List (Values s)) := do
  let mut rows := #[]
  repeat
    let rc ← step st
    if rc == 101 then break
    rows := rows.push (← readRow st s 0)
  pure rows.toList

/-! ## Typed execution -/

/-- Execute a query: compile for SQLite, bind natively, decode
schema-directed. Output is cell-for-cell comparable with `Query.run`. -/
def Conn.query (conn : Conn) (q : Query c s)
    (ps : ParamEnv c.params := by exact .nil) : IO (List (Values s)) := do
  let compiled := q.toSql .sqlite
  let st ← prepareRaw conn compiled.sql
  bindParams st compiled ps.toCells
  collectRows st s

/-- Execute a scalar aggregate query: one row, one cell (no row = NULL). -/
def Conn.queryCell (conn : Conn) (sc : ScalarQuery c ⟨t, n⟩)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  let compiled := sc.toSql .sqlite
  let st ← prepareRaw conn compiled.sql
  bindParams st compiled ps.toCells
  if (← step st) == 101 then pure none
  else readCell st 0 t

@[extern "ll_sqlite3_changes"]
private opaque changesRaw (conn : @&Conn) : IO UInt32

/-- Execute a statement and report the engine's affected-row count. -/
private def execCompiled (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Nat := do
  let st ← prepareRaw conn compiled.sql
  bindParams st compiled cells
  let _ ← step st   -- statements step straight to DONE
  return (← changesRaw conn).toNat

def Conn.execInsert (conn : Conn) (i : InsertStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (i.toSql .sqlite) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (u.toSql .sqlite) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (d.toSql .sqlite) ps.toCells

def Conn.execInsertSelect (conn : Conn) (st : InsertSelectStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (st.toSql .sqlite) ps.toCells

def Conn.execInsertValues (conn : Conn) (st : InsertValuesStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (st.toSql .sqlite) ps.toCells

end Sqlite

/-- Interpret a `Db` program against a live connection — the same tree
`runWith` interprets in memory. The budget discipline is identical (`by
decide` for closed grades, caller-supplied proofs otherwise). `seq`
executes sequentially here: SQLite is in-process, so a "round" costs a
statement, not a network wait — the `max` grade is the contract for future
networked drivers, which batch `seq`'s sides into shared rounds. -/
private def Sqlite.interp (conn : Sqlite.Conn) (ps : ParamEnv c.params) :
    {r' : Grade} → {β : Type} → {w : Wp β} → DbP c r' β w → IO β
  | _, _, _, .pure a => Pure.pure a
  | _, _, _, .fetch q => conn.query q ps
  | _, _, _, .fetchCell sc => conn.queryCell sc ps
  | _, _, _, .weakenP _ x => interp conn ps x
  | _, _, _, .insert (inst := _) i => conn.execInsert i ps
  | _, _, _, .update (inst := _) u => conn.execUpdate u ps
  | _, _, _, .delete (inst := _) d => conn.execDelete d ps
  | _, _, _, .insertSelect (inst := _) st => conn.execInsertSelect st ps
  | _, _, _, .insertValues (inst := _) st => conn.execInsertValues st ps
  | _, _, _, .bindD x f _ _ => do interp conn ps (f (← interp conn ps x))

def DbP.execIO {w : Wp α} (f : DbP c r α w) (conn : Sqlite.Conn) (budget : Nat)
    (ps : ParamEnv c.params := by exact .nil)
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : IO α :=
  Sqlite.interp conn ps f

/-- The unbounded door over the wire: no budget, obligation-free — the
explicit opt-out, same as the in-memory `execAll`. -/
def DbP.execIOAll {w : Wp α} (f : DbP c r α w) (conn : Sqlite.Conn)
    (ps : ParamEnv c.params := by exact .nil) : IO α :=
  Sqlite.interp conn ps f

end LeanLinq
