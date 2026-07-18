import LeanLinq
import LeanLinq.Driver.TextCell

/-! # Native PostgreSQL driver (libpq)

Typed queries in, typed rows out, over the wire protocol (via
`native/libpq_shim.c`):

- **Placeholders**: PostgreSQL's wire form is `$1..$n` (`:name` is a psql
  client feature). The compiled SQL keeps `:name` as its stable logical
  form; this driver rewrites each `CompiledSql.params` entry at position
  `k` to `$k+1` (longest-name-first, so `:p1` never clobbers `:p10`).
  Repeated references work because `refParam` dedupes names.
- **Types**: every parameter carries an explicit OID, which solves
  `EXTRACT(YEAR FROM $1)`-style inference properly (the CLI harness had to
  paper over it with `TIMESTAMP '…'` literals). Text format both ways.
- **`Db` interprets sequentially** (one statement per round):
  independence is applicative structure, retired with the `seq`
  constructor; libpq pipeline batching returns with the free-applicative
  layer over the monad. -/

namespace LeanLinq.Pg

private opaque ConnP : NonemptyType
/-- An open PostgreSQL connection. -/
def Conn : Type := ConnP.type
instance : Nonempty Conn := ConnP.property

private opaque ResP : NonemptyType
private def PgResult : Type := ResP.type
instance : Nonempty PgResult := ResP.property

/-- Connect with a libpq conninfo string, e.g.
`"host=127.0.0.1 port=5433 user=testuser password=testpass dbname=testdb"`. -/
@[extern "ll_pq_connect"]
opaque connect (conninfo : @&String) : IO Conn

@[extern "ll_pq_finish"]
opaque Conn.close (conn : @&Conn) : IO Unit

/-- Execute a raw SQL batch (DDL / seed / BEGIN / ROLLBACK). -/
@[extern "ll_pq_exec_raw"]
opaque Conn.execRaw (conn : @&Conn) (sql : @&String) : IO Unit

@[extern "ll_pq_exec_params"]
private opaque execParamsRaw (conn : @&Conn) (sql : @&String)
    (oids : @&Array UInt32) (vals : @&Array (Option String)) : IO PgResult

@[extern "ll_pq_ntuples"]
private opaque ntuples (res : @&PgResult) : IO UInt32

@[extern "ll_pq_getisnull"]
private opaque getisnull (res : @&PgResult) (row col : UInt32) : IO Bool

@[extern "ll_pq_getvalue"]
private opaque getvalue (res : @&PgResult) (row col : UInt32) : IO String

@[extern "ll_pq_enter_pipeline"]
private opaque enterPipeline (conn : @&Conn) : IO Unit

@[extern "ll_pq_send_query_params"]
private opaque sendQueryParams (conn : @&Conn) (sql : @&String)
    (oids : @&Array UInt32) (vals : @&Array (Option String)) : IO Unit

@[extern "ll_pq_pipeline_sync"]
private opaque pipelineSync (conn : @&Conn) : IO Unit

@[extern "ll_pq_pipeline_read_result"]
private opaque pipelineReadResult (conn : @&Conn) : IO PgResult

@[extern "ll_pq_pipeline_consume_sync"]
private opaque pipelineConsumeSync (conn : @&Conn) : IO Unit

@[extern "ll_pq_exit_pipeline"]
private opaque exitPipeline (conn : @&Conn) : IO Unit

@[extern "ll_pq_pipeline_abort"]
private opaque pipelineAbort (conn : @&Conn) : IO Unit

/-! ## Wire form: `$N` placeholders, OID-typed text values -/

/-- Rewrite `:name` placeholders to positional `$k+1`, longest name first. -/
private def toWire (compiled : CompiledSql) : String :=
  let entries := compiled.params.toList.zipIdx.map fun ((name, _), k) =>
    (name, s!"${k + 1}")
  let entries := entries.mergeSort (fun a b => a.1.length ≥ b.1.length)
  entries.foldl (fun sql (n, ph) => sql.replace n ph) compiled.sql

private def oidOf : SqlPrim → UInt32
  | .int => 23      -- int4 (function overloads resolve against int4, e.g. SUBSTRING)
  | .long => 20     -- int8
  | .double => 701  -- float8
  | .decimal => 1700 -- numeric
  | .string => 25   -- text
  | .bool => 16
  | .dateTime => 1114 -- timestamp
  | .guid => 2950   -- uuid

private def valueWire : SqlValue → UInt32 × Option String
  | .int i => (23, some (toString i))
  | .long i => (20, some (toString i))
  | .double f => (701, some (toString f))
  | .decimal d => (1700, some d)
  | .string s => (25, some s)
  | .bool b => (16, some (if b then "t" else "f"))
  | .dateTime s => (1114, some s)
  | .guid g => (2950, some g)
  | .null => (25, none)   -- unreachable: `.null` marks user-named params

/-- One wire entry per compiled parameter, in array order (`$k+1` order):
auto parameters carry their values; user-named ones resolve from the typed
cells. -/
private def wireParams (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) :
    IO (Array UInt32 × Array (Option String)) := do
  let mut oids := #[]
  let mut vals := #[]
  for (name, v) in compiled.params do
    match v with
    | .null =>
        let bare := String.ofList (name.toList.drop 1)
        match cells.find? (·.1 == bare) with
        | some (_, ⟨t, cell⟩) =>
            oids := oids.push (oidOf t)
            vals := vals.push (cell.map (Driver.cellText t))
        | none => throw (IO.userError s!"libpq bind: no typed value for {name}")
    | v =>
        let (oid, txt) := valueWire v
        oids := oids.push oid
        vals := vals.push txt
  pure (oids, vals)

/-! ## Text decode → `Values` -/

private def readCell (res : PgResult) (row col : UInt32) (t : SqlPrim) :
    IO (Nullable t) := do
  if ← getisnull res row col then pure none
  else IO.ofExcept ((Driver.parseCell t (← getvalue res row col)).mapError IO.userError)

private def readRow (res : PgResult) (row : UInt32) :
    (s : Schema) → (col : UInt32) → IO (Values s)
  | [], _ => pure .nil
  | (nm, c) :: rest, col => do
      pure (.cons (← Driver.cellFromWire nm c (← readCell res row col c.ty))
        (← readRow res row rest (col + 1)))

private def readRows (res : PgResult) (s : Schema) : IO (List (Values s)) := do
  let n ← ntuples res
  let mut rows := #[]
  for r in [0:n.toNat] do
    rows := rows.push (← readRow res r.toUInt32 s 0)
  pure rows.toList

/-! ## Typed execution -/

def Conn.query (conn : Conn) (q : Query c s)
    (ps : ParamEnv c.params := by exact .nil) : IO (List (Values s)) := do
  let compiled := q.toSql .postgres
  let (oids, vals) ← wireParams compiled ps.toCells
  let res ← execParamsRaw conn (toWire compiled) oids vals
  readRows res s

def Conn.queryCell (conn : Conn) (sc : ScalarQuery c ⟨t, n⟩)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  let compiled := sc.toSql .postgres
  let (oids, vals) ← wireParams compiled ps.toCells
  let res ← execParamsRaw conn (toWire compiled) oids vals
  if (← ntuples res) == 0 then pure none
  else readCell res 0 0 t

@[extern "ll_pq_cmd_tuples"]
private opaque cmdTuplesRaw (res : @&PgResult) : IO String

/-- Execute a statement and report the engine's affected-row count
(`PQcmdTuples`; empty for non-DML). -/
private def execCompiled (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlPrim) × Nullable t))) : IO Nat := do
  let (oids, vals) ← wireParams compiled cells
  let res ← execParamsRaw conn (toWire compiled) oids vals
  return ((← cmdTuplesRaw res).toNat?).getD 0

def Conn.execInsert (conn : Conn) (i : InsertStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (i.toSql .postgres) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (u.toSql .postgres) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Nat :=
  execCompiled conn (d.toSql .postgres) ps.toCells

/-! ## `Db` interpretation

The monad is sequential by design — dependence is monadic structure,
and `bindD` cannot know what to ask until the previous answer arrives —
so the interpreter is one statement per round. Pipelining (independent
fetches sharing rounds via libpq pipeline mode) is *applicative*
structure, retired with the `seq` constructor; it returns with the
free-applicative layer over this monad. -/

private def interp (conn : Pg.Conn) (ps : ParamEnv c.params) :
    {r' : Grade} → {β : Type} → {w : Wp β} → DbP c r' β w → IO β
  | _, _, _, .pure a => Pure.pure a
  | _, _, _, .fetch q => conn.query q ps
  | _, _, _, .fetchCell sc => conn.queryCell sc ps
  | _, _, _, .insert (inst := _) i => conn.execInsert i ps
  | _, _, _, .update (inst := _) u => conn.execUpdate u ps
  | _, _, _, .delete (inst := _) d => conn.execDelete d ps
  | _, _, _, .bindD x f _ _ => do interp conn ps (f (← interp conn ps x))
  | _, _, _, .weakenP _ x => interp conn ps x

end Pg

/-- Interpret a `Db` program against live PostgreSQL, one statement
per round, gated by the usual budget obligation: `by decide` for closed
grades, a caller-supplied proof otherwise. -/
def DbP.execPg {w : Wp α} (f : DbP c r α w) (conn : Pg.Conn) (budget : Nat)
    (ps : ParamEnv c.params := by exact .nil)
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : IO α :=
  Pg.interp conn ps f

/-- The unchecked door over the wire: no budget, no obligation — the
explicit opt-out, same as the in-memory `execAll`. -/
def DbP.execPgAll {w : Wp α} (f : DbP c r α w) (conn : Pg.Conn)
    (ps : ParamEnv c.params := by exact .nil) : IO α :=
  Pg.interp conn ps f

end LeanLinq
