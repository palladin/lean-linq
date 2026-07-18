import LeanLinq
import LeanLinq.Driver.TextCell

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

@[extern "ll_my_query"]
private opaque queryRaw (conn : @&Conn) (sql : @&String)
    (vals : @&Array (Option String)) : IO (Array (Array (Option String)))

@[extern "ll_my_exec_params"]
private opaque execParamsRaw (conn : @&Conn) (sql : @&String)
    (vals : @&Array (Option String)) : IO UInt32

/-! ## Wire form: occurrence-order `?` placeholders, text values -/

private def valueText : SqlValue → Option String
  | .int i => some (toString i)
  | .long i => some (toString i)
  | .double f => some (toString f)
  | .decimal d => some d
  | .string s => some s
  | .bool b => some (if b then "1" else "0")
  | .dateTime s => some s
  | .guid g => some g
  | .null => none   -- unreachable: `.null` marks user-named params

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
  | v => pure (valueText v)

/-- Scan the SQL replacing each `:name` occurrence with `?`, emitting the
value list in occurrence order. Literals never contain `:` (values always
travel as parameters), so the scan is safe. -/
private partial def scanParams (names : List String)
    (lookup : String → IO (Option String)) :
    List Char → String → Array (Option String) →
    IO (String × Array (Option String))
  | [], acc, vals => pure (acc, vals)
  | ':' :: cs, acc, vals => do
      let tail := String.mk (':' :: cs)
      match names.find? (fun n => tail.startsWith n) with
      | some n => do
          let v ← lookup n
          scanParams names lookup (cs.drop (n.length - 1))
            (acc ++ "?") (vals.push v)
      | none => scanParams names lookup cs (acc.push ':') vals
  | c :: cs, acc, vals => scanParams names lookup cs (acc.push c) vals

private def toWire (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) :
    IO (String × Array (Option String)) := do
  let names := (compiled.params.toList.map (·.1)).mergeSort
    (fun a b => a.length ≥ b.length)
  let lookup := fun (n : String) => do
    match compiled.params.toList.find? (·.1 == n) with
    | some (_, v) => paramText cells n v
    | none => throw (IO.userError "mysql toWire: unknown param")
  scanParams names lookup compiled.sql.toList "" #[]

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
  let compiled := q.toSql .mysql
  let (sql, vals) ← toWire compiled ps.toCells
  let rows ← queryRaw conn sql vals
  rows.toList.mapM fun r => readRow s r.toList

def Conn.queryCell (conn : Conn) (sc : ScalarQuery c ⟨t, n⟩)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  let compiled := sc.toSql .mysql
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
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (i.toSql .mysql) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (u.toSql .mysql) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (d.toSql .mysql) ps.toCells

def Conn.execInsertSelect (conn : Conn) (st : InsertSelectStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (st.toSql .mysql) ps.toCells

/-! ## `Db` interpretation (sequential, one statement per round) -/

private def interp (conn : Conn) (ps : ParamEnv c.params) :
    {r' : Grade} → {β : Type} → {w : Wp β} → DbP c r' β w → IO β
  | _, _, _, .pure a => Pure.pure a
  | _, _, _, .fetch q => conn.query q ps
  | _, _, _, .fetchCell sc => conn.queryCell sc ps
  | _, _, _, .insert (inst := _) i => conn.execInsert i ps
  | _, _, _, .update (inst := _) u => conn.execUpdate u ps
  | _, _, _, .delete (inst := _) d => conn.execDelete d ps
  | _, _, _, .insertSelect (inst := _) st => conn.execInsertSelect st ps
  | _, _, _, .bindD x f _ _ => do interp conn ps (f (← interp conn ps x))
  | _, _, _, .weakenP _ x => interp conn ps x

end Mysql

/-- Interpret a `Db` program against live MySQL, one statement per round,
gated by the usual budget obligation. -/
def DbP.execMy {w : Wp α} (f : DbP c r α w) (conn : Mysql.Conn) (budget : Nat)
    (ps : ParamEnv c.params := by exact .nil)
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : IO α :=
  Mysql.interp conn ps f

/-- The unchecked door over the wire: no budget, no obligation. -/
def DbP.execMyAll {w : Wp α} (f : DbP c r α w) (conn : Mysql.Conn)
    (ps : ParamEnv c.params := by exact .nil) : IO α :=
  Mysql.interp conn ps f

end LeanLinq
