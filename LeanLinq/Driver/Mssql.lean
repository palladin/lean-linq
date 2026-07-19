import LeanLinq
import LeanLinq.Driver.TextCell

/-! # Native SQL Server driver (FreeTDS DB-Library)

Typed queries in, typed rows out, over TDS (via `native/freetds_shim.c`):

- **No placeholder rewriting**: the sqlServer dialect already compiles
  `@p0`/`@minAge` — TDS's *native* named-parameter form. Execution is an
  `sp_executesql` RPC: `@stmt` is the compiled SQL verbatim, `@params`
  declares each parameter's SQL type (built from the compiled parameter
  list), and the values travel as nvarchar text with server-side
  conversion to the declared types — the strategy that worked on
  PostgreSQL (text values + typed OIDs), in TDS clothes. One dblib API
  limitation is worked around: an empty-string value cannot ride an RPC
  parameter (zero datalen means NULL), so those executions go as an
  equivalent `EXEC sp_executesql` batch, `@stmt` still verbatim.
- **TDS 7.1 on the login**: the server downgrades `datetime2` columns to
  nvarchar text on the wire; every result cell is read via
  `dbconvert(coltype → SYBCHAR)` and decoded by the shared text codecs
  (`LeanLinq.Driver.TextCell`).
- TDS allows one active request per connection — no pipelining — so
  `Db.execMs` interprets sequentially and the `max` grade stays an
  honest upper bound (as with in-process SQLite). -/

namespace LeanLinq.Ms

private opaque ConnP : NonemptyType
/-- An open SQL Server connection. -/
def Conn : Type := ConnP.type
instance : Nonempty Conn := ConnP.property

@[extern "ll_tds_connect"]
private opaque connectRaw (server user pass db : @&String) : IO Conn

@[extern "ll_tds_close"]
opaque Conn.close (conn : @&Conn) : IO Unit

/-- Execute a raw T-SQL batch (DDL / seed / BEGIN TRAN / ROLLBACK TRAN);
all result sets are drained. -/
@[extern "ll_tds_exec_raw"]
opaque Conn.execRaw (conn : @&Conn) (sql : @&String) : IO Unit

/-- Connect to SQL Server; empty `db` skips the initial `USE`. DB-Library
sessions do not get the ANSI defaults that ODBC/sqlcmd set implicitly
(without `ANSI_NULL_DFLT_ON`, created columns default to NOT NULL, etc.),
so the standard options are established per connection. -/
def connect (host : String) (port : Nat) (user pass : String)
    (db : String := "") : IO Conn := do
  let conn ← connectRaw s!"{host}:{port}" user pass db
  conn.execRaw "SET ANSI_NULLS ON; SET ANSI_NULL_DFLT_ON ON; SET ANSI_PADDING ON; SET ANSI_WARNINGS ON; SET QUOTED_IDENTIFIER ON; SET CONCAT_NULL_YIELDS_NULL ON; SET IMPLICIT_TRANSACTIONS OFF;"
  pure conn

/-- Send a batch, leaving its result sets readable (`execRaw` drains). -/
@[extern "ll_tds_send_batch"]
private opaque sendBatch (conn : @&Conn) (sql : @&String) : IO Unit

@[extern "ll_tds_rpc_begin"]
private opaque rpcBegin (conn : @&Conn) (proc : @&String) : IO Unit

@[extern "ll_tds_rpc_param_text"]
private opaque rpcParamText (conn : @&Conn) (name : @&String)
    (wide isNull : Bool) (value : @&String) : IO Unit

@[extern "ll_tds_rpc_send"]
private opaque rpcSend (conn : @&Conn) : IO Unit

@[extern "ll_tds_results_next"]
private opaque resultsNext (conn : @&Conn) : IO UInt32

@[extern "ll_tds_row_next"]
private opaque rowNext (conn : @&Conn) : IO UInt32

@[extern "ll_tds_col_is_null"]
private opaque colIsNull (conn : @&Conn) (i : UInt32) : IO Bool

@[extern "ll_tds_col_text"]
private opaque colText (conn : @&Conn) (i : UInt32) : IO String

/-! ## sp_executesql marshaling -/

private def declType : SqlPrim → String
  | .int => "int"
  | .long => "bigint"
  | .double => "float"
  | .decimal => "decimal(38,10)"
  | .string => "nvarchar(max)"
  | .bool => "bit"
  | .dateTime => "datetime2"
  | .guid => "uniqueidentifier"

private def valueTypeOf : SqlValue → SqlPrim
  | .int _ => .int
  | .long _ => .long
  | .double _ => .double
  | .decimal _ => .decimal
  | .string _ => .string
  | .bool _ => .bool
  | .dateTime _ => .dateTime
  | .guid _ => .guid
  | .null => .string   -- unreachable: `.null` marks user-named params

private def valueText : SqlValue → String
  | .int i => toString i
  | .long i => toString i
  | .double f => toString f
  | .decimal d => d
  | .string s => s
  | .bool b => if b then "1" else "0"
  | .dateTime s => s
  | .guid g => g
  | .null => ""        -- unreachable

/-- The `@params` declaration string plus the ordered value list
(`name`, isNull, text): auto parameters carry their values; user-named
ones resolve from the typed cells. Names already carry the `@` prefix
(the sqlServer dialect's `paramPrefix`). -/
private def rpcArgs (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) :
    IO (String × Array (String × Bool × String)) := do
  let mut decls := #[]
  let mut args := #[]
  for (name, v) in compiled.params do
    match v with
    | .null =>
        let bare := String.ofList (name.toList.drop 1)
        match cells.find? (·.1 == bare) with
        | some (_, ⟨t, cell⟩) =>
            decls := decls.push s!"{name} {declType t}"
            match cell with
            | some x => args := args.push (name, false, Driver.cellText t x)
            | none => args := args.push (name, true, "")
        | none => throw (IO.userError s!"freetds bind: no typed value for {name}")
    | v =>
        decls := decls.push s!"{name} {declType (valueTypeOf v)}"
        args := args.push (name, false, valueText v)
  pure (String.intercalate ", " decls.toList, args)

private def escapeStr (s : String) : String :=
  s.replace "'" "''"

/-- Execute a compiled statement as an `sp_executesql` RPC — or, when a
value is the empty string, as an `EXEC sp_executesql` batch: `dbrpcparam`
erases the value pointer at datalen 0 (rpc.c), so an empty string cannot
travel as an RPC parameter (it arrives NULL). The batch keeps `@stmt`
verbatim and the same server-side conversion discipline; only the argument
tail carries `N'...'` literals (one escaping rule: `'` doubles). -/
private def execRpc (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Unit := do
  let (decl, args) ← rpcArgs compiled cells
  if args.any (fun (_, isNull, txt) => !isNull && txt.isEmpty) then
    let assigns := args.map fun (name, isNull, txt) =>
      if isNull then s!", {name} = NULL" else s!", {name} = N'{escapeStr txt}'"
    sendBatch conn
      s!"EXEC sp_executesql N'{escapeStr compiled.sql}', N'{escapeStr decl}'{String.join assigns.toList}"
  else
    rpcBegin conn "sp_executesql"
    rpcParamText conn "@stmt" (wide := true) (isNull := false) compiled.sql
    if !args.isEmpty then
      rpcParamText conn "@params" (wide := true) (isNull := false) decl
      for (name, isNull, txt) in args do
        rpcParamText conn name (wide := false) isNull txt
    rpcSend conn

/-! ## Reading results -/

private def readRow (conn : Conn) : (s : Schema) → (col : UInt32) → IO (Values s)
  | [], _ => pure .nil
  | (nm, c) :: rest, col => do
      let cell : Nullable c.ty ←
        if ← colIsNull conn col then pure none
        else IO.ofExcept ((Driver.parseCell c.ty (← colText conn col)).mapError IO.userError)
      pure (.cons (← Driver.cellFromWire nm c cell) (← readRow conn rest (col + 1)))

/-- Drain any remaining rows/result sets after the interesting one. -/
private partial def drain (conn : Conn) : IO Unit := do
  if (← rowNext conn) == 1 then drain conn
  else if (← resultsNext conn) == 1 then drain conn
  else pure ()

private def collectRows (conn : Conn) (s : Schema) : IO (List (Values s)) := do
  if (← resultsNext conn) == 0 then pure []
  else do
    let mut rows := #[]
    repeat
      if (← rowNext conn) == 0 then break
      rows := rows.push (← readRow conn s 0)
    drain conn
    pure rows.toList

/-! ## Typed execution -/

def Conn.query (conn : Conn) (q : Query c s)
    (ps : ParamEnv c.params := by exact .nil) : IO (List (Values s)) := do
  execRpc conn (q.toSql .sqlServer) ps.toCells
  collectRows conn s

def Conn.queryCell (conn : Conn) (sc : ScalarQuery c ⟨t, n⟩)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  execRpc conn (sc.toSql .sqlServer) ps.toCells
  if (← resultsNext conn) == 0 then pure none
  else do
    if (← rowNext conn) == 0 then
      drain conn
      pure none
    else do
      let cell : Nullable t ←
        if ← colIsNull conn 0 then pure none
        else IO.ofExcept ((Driver.parseCell t (← colText conn 0)).mapError IO.userError)
      drain conn
      pure cell

@[extern "ll_tds_count"]
private opaque countRaw (conn : @&Conn) : IO UInt32

/-- Execute a statement and report the affected-row count (`DBCOUNT`,
read after the results are drained). -/
private def execStmt (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Nat := do
  execRpc conn compiled cells
  drain conn
  return (← countRaw conn).toNat

def Conn.execInsert (conn : Conn) (i : InsertStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execStmt conn (i.toSql .sqlServer) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execStmt conn (u.toSql .sqlServer) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execStmt conn (d.toSql .sqlServer) ps.toCells

def Conn.execInsertSelect (conn : Conn) (st : InsertSelectStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execStmt conn (st.toSql .sqlServer) ps.toCells

def Conn.execInsertValues (conn : Conn) (st : InsertValuesStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execStmt conn (st.toSql .sqlServer) ps.toCells

end Ms

/-- Interpret a `Db` program against live SQL Server. TDS permits one
active request per connection (no pipelining), so interpretation is
sequential and the `max` grade is an upper bound — same budget discipline
as everywhere. -/
private def Ms.ops (conn : Ms.Conn) (ps : ParamEnv c.params) :
    {β : Type} → DbE c β → IO β
  | _, .fetch q => conn.query q ps
  | _, .fetchCell sc => conn.queryCell sc ps
  | _, .insert (inst := _) i => conn.execInsert i ps
  | _, .update (inst := _) u => conn.execUpdate u ps
  | _, .delete (inst := _) d => conn.execDelete d ps
  | _, .insertSelect (inst := _) st => conn.execInsertSelect st ps
  | _, .insertValues (inst := _) st => conn.execInsertValues st ps

def DbP.execMs {w : Wp α} (f : DbP c α w) (conn : Ms.Conn) (budget : Nat)
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
  FreerD.foldM (E := DbE c) (fun e => Ms.ops conn ps e) f

/-- The unbounded door over the wire: no budget, obligation-free — the
explicit opt-out, same as the in-memory `execAll`. -/
def DbP.execMsAll {w : Wp α} (f : DbP c α w) (conn : Ms.Conn)
    (ps : ParamEnv c.params := by exact .nil) : IO α :=
  FreerD.foldM (E := DbE c) (fun e => Ms.ops conn ps e) f

end LeanLinq
