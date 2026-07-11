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
- **`DbFetch.execIO` batches for real**: independent (`seq`) fetches are
  sent in one libpq *pipeline* round — the `max` grade finally buys shared
  round trips. The interpreter is level-synchronous with the budget as
  fuel: the grade bounds the number of rounds, so the type-level bill
  doubles as the termination argument. -/

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

/-! ## Wire form: `$N` placeholders, OID-typed text values -/

/-- Rewrite `:name` placeholders to positional `$k+1`, longest name first. -/
private def toWire (compiled : CompiledSql) : String :=
  let entries := compiled.params.toList.zipIdx.map fun ((name, _), k) =>
    (name, s!"${k + 1}")
  let entries := entries.mergeSort (fun a b => a.1.length ≥ b.1.length)
  entries.foldl (fun sql (n, ph) => sql.replace n ph) compiled.sql

private def oidOf : SqlType → UInt32
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
    (cells : List (String × ((t : SqlType) × Nullable t))) :
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

private def readCell (res : PgResult) (row col : UInt32) (t : SqlType) :
    IO (Nullable t) := do
  if ← getisnull res row col then pure none
  else pure (Driver.parseCell t (← getvalue res row col))

private def readRow (res : PgResult) (row : UInt32) :
    (s : Schema) → (col : UInt32) → IO (Values s)
  | [], _ => pure .nil
  | (_, t) :: rest, col => do
      pure (.cons (← readCell res row col t) (← readRow res row rest (col + 1)))

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

def Conn.queryCell (conn : Conn) (sc : ScalarQuery c t)
    (ps : ParamEnv c.params := by exact .nil) : IO (Nullable t) := do
  let compiled := sc.toSql .postgres
  let (oids, vals) ← wireParams compiled ps.toCells
  let res ← execParamsRaw conn (toWire compiled) oids vals
  if (← ntuples res) == 0 then pure none
  else readCell res 0 0 t

private def execCompiled (conn : Conn) (compiled : CompiledSql)
    (cells : List (String × ((t : SqlType) × Nullable t))) : IO Unit := do
  let (oids, vals) ← wireParams compiled cells
  let _ ← execParamsRaw conn (toWire compiled) oids vals

def Conn.execInsert (conn : Conn) (i : InsertStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Unit :=
  execCompiled conn (i.toSql .postgres) ps.toCells

def Conn.execUpdate (conn : Conn) (u : UpdateStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Unit :=
  execCompiled conn (u.toSql .postgres) ps.toCells

def Conn.execDelete (conn : Conn) (d : DeleteStmt c n s)
    (ps : ParamEnv c.params := by exact .nil) : IO Unit :=
  execCompiled conn (d.toSql .postgres) ps.toCells

/-! ## Level-synchronous `DbFetch` interpretation

Independent (`seq`) fetches share pipeline rounds. The interpreter is a
fuel-indexed *stage* machine, all in `Type 0` (a residual-tree encoding
would live in `Type 1`, which `IO` cannot carry):

    Stage c α 0     = α                              -- no rounds left ⇒ done
    Stage c α (n+1) = α ⊕ (read this round's refs, send next round's
                           fetches, yield a Stage at n)

`sendPhase` walks the graded tree: each ready fetch is *sent* into the
pipeline (walk order = send order = read order) and becomes a blocked
stage reading its ref; `bind` continues in the same round when its left
side is already done (Haxl semantics); `seq` merges both sides' next-round
actions into one `StateT` batch — that is the batching. The budget is the
fuel: rounds ≤ grade ≤ budget by construction, so exhaustion is
unreachable. -/

/-- A pipelined request together with the ref its result will fill. -/
private inductive Req (c : Ctx) : Type where
  | q : (s : Schema) → IO.Ref (Option (List (Values s))) → Req c
  | sc : (t : SqlType) → IO.Ref (Option (Nullable t)) → Req c

private abbrev SendM (c : Ctx) := StateT (Array (Req c)) IO

/-- A program that has run for some rounds: done, or blocked on the round
in flight with an action that reads its results and stages the next. -/
private def Stage (c : Ctx) (α : Type) : Nat → Type
  | 0 => α
  | n + 1 => α ⊕ SendM c (Stage c α n)

private def stageDone (a : α) : (n : Nat) → Stage c α n
  | 0 => a
  | _ + 1 => .inl a

/-- Sequential composition; when the left side is already done, the
continuation sends into the *current* round. -/
private def bindStage
    (k : (fuel : Nat) → β → SendM c (Stage c α fuel)) :
    (n : Nat) → Stage c β n → SendM c (Stage c α n)
  | 0, b => k 0 b
  | _ + 1, .inl b => k _ b
  | n + 1, .inr m => pure (.inr (do bindStage k n (← m)))

/-- Parallel composition: both sides' next-round actions run in the same
`SendM` batch — shared rounds, the `max` grade made real. -/
private def parStage (f : β → γ → α) :
    (n : Nat) → Stage c β n → Stage c γ n → Stage c α n
  | 0, b, g => f b g
  | _ + 1, .inl b, .inl g => .inl (f b g)
  | n + 1, .inl b, .inr mg => .inr (do pure (parStage f n (stageDone b n) (← mg)))
  | n + 1, .inr mb, .inl g => .inr (do pure (parStage f n (← mb) (stageDone g n)))
  | n + 1, .inr mb, .inr mg => .inr (do pure (parStage f n (← mb) (← mg)))

private def awaitRef (ref : IO.Ref (Option δ)) : IO δ := do
  match ← ref.get with
  | some v => pure v
  | none => throw (IO.userError "libpq pipeline: unfilled ref")

/-- Walk the tree for one round: send every ready fetch, produce its
blocked stage; `bind` may continue within the round; `seq` batches. -/
private def sendPhase (conn : Conn)
    (cells : List (String × ((t : SqlType) × Nullable t))) :
    DbFetch c r α → (fuel : Nat) → SendM c (Stage c α fuel)
  | .pure a, fuel => pure (stageDone a fuel)
  | .fetch (s := s) q, fuel => do
      let compiled := q.toSql .postgres
      let (oids, vals) ← wireParams compiled cells
      sendQueryParams conn (toWire compiled) oids vals
      let ref ← IO.mkRef (none : Option (List (Values s)))
      modify (·.push (.q s ref))
      match fuel with
      | 0 => throw (IO.userError "unreachable: fetch with zero round budget")
      | n + 1 => pure (.inr (do pure (stageDone (← awaitRef ref) n)))
  | .fetchCell (t := t) sc, fuel => do
      let compiled := sc.toSql .postgres
      let (oids, vals) ← wireParams compiled cells
      sendQueryParams conn (toWire compiled) oids vals
      let ref ← IO.mkRef (none : Option (Nullable t))
      modify (·.push (.sc t ref))
      match fuel with
      | 0 => throw (IO.userError "unreachable: fetch with zero round budget")
      | n + 1 => pure (.inr (do pure (stageDone (← awaitRef ref) n)))
  | .seq f x, fuel => do
      let sf ← sendPhase conn cells f fuel
      let sx ← sendPhase conn cells x fuel
      pure (parStage (fun g b => g b) fuel sf sx)
  | .bind x k, fuel => do
      let sx ← sendPhase conn cells x fuel
      bindStage (fun fuel' a => sendPhase conn cells (k a) fuel') fuel sx

/-- Read this round's results in send order and fill the refs. -/
private def fill (conn : Conn) (reqs : Array (Req c)) : IO Unit := do
  for req in reqs do
    match req with
    | .q s ref =>
        let res ← pipelineReadResult conn
        ref.set (some (← readRows res s))
    | .sc t ref =>
        let res ← pipelineReadResult conn
        if (← ntuples res) == 0 then ref.set (some none)
        else ref.set (some (← readCell res 0 0 t))

/-- Execute one pipeline round: run the send action, sync, fill. -/
private def runRound (conn : Conn) (act : SendM c σ) : IO σ := do
  enterPipeline conn
  let (stage, reqs) ← act.run #[]
  pipelineSync conn
  fill conn reqs
  pipelineConsumeSync conn
  exitPipeline conn
  pure stage

private def runStages (conn : Conn) : (n : Nat) → Stage c α n → IO α
  | 0, a => pure a
  | _ + 1, .inl a => pure a
  | n + 1, .inr next => do runStages conn n (← runRound conn next)

end Pg

/-- Interpret a `DbFetch` program against live PostgreSQL. Independent
(`seq`) fetches share pipeline rounds — the `max` grade is real here. Same
budget discipline as everywhere: `by decide` for closed grades, a
caller-supplied proof otherwise; the budget also serves as the (provably
sufficient) round fuel. -/
def DbFetch.execPg (f : DbFetch c r α) (conn : Pg.Conn) (budget : Nat)
    (ps : ParamEnv c.params := by exact .nil)
    (_h : r ≤ budget := by decide) : IO α := do
  Pg.runStages conn budget
    (← Pg.runRound conn (Pg.sendPhase conn ps.toCells f budget))

end LeanLinq
