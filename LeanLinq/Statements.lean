import LeanLinq.Compiler.Query

/-! # Data-modification statements: INSERT / UPDATE / DELETE

Column references are name-checked at compile time via `HasCol` (same
machinery as `row["Name"]`), and values are typed against the column's type.
`NULL` assignments go through `setNull`/`valueNull`. The target table's name
and schema are type indices (from `Table n s`), so a statement — like a
query — is fully static about what it touches. -/

namespace LeanLinq

structure InsertStmt (ts : Ctx) (n : String) (s : Schema) where
  values : List (String × ((p : SqlType) × SqlExpr ts p)) := []

/-- `INSERT INTO t …` — add columns with `.value`/`.valueNull`. -/
def Table.insert (_ : Table n s) : InsertStmt ts n s := ⟨[]⟩

/-- Set a column's value. The expression's nullability must fit the
column's declared flag: a NULL-capable expression into a NOT NULL column
is a type error (strict values widen into nullable columns silently). -/
def InsertStmt.value (i : InsertStmt ts n s) (name : String) {t : SqlPrim}
    {ne nl : Bool} [HasCol s name ⟨t, nl⟩] [fits : FlagFits ne nl]
    (e : SqlExpr ts ⟨t, ne⟩) : InsertStmt ts n s :=
  { i with values := i.values ++ [(name, ⟨⟨t, nl⟩, fits.fit e⟩)] }

/-- Insert NULL — only into a column the schema declares NULL-capable. -/
def InsertStmt.valueNull (i : InsertStmt ts n s) (name : String) {t : SqlPrim}
    {nl : Bool} [HasCol s name ⟨t, nl⟩] (h : nl = true := by rfl) :
    InsertStmt ts n s :=
  { i with values := i.values ++ [(name, ⟨⟨t, true⟩, .nullC t⟩)] }

structure UpdateStmt (ts : Ctx) (n : String) (s : Schema) where
  sets : List (String × (Row ts s → (p : SqlType) × SqlExpr ts p)) := []
  where? : Option (Row ts s → SqlExpr ts ⟨.bool, true⟩) := none

/-- `UPDATE t SET …` — add assignments with `.set`/`.setWith`/`.setNull`,
restrict with `.where'`. -/
def Table.update (_ : Table n s) : UpdateStmt ts n s := ⟨[], none⟩

def UpdateStmt.set (u : UpdateStmt ts n s) (name : String) {t : SqlPrim}
    {ne nl : Bool} [HasCol s name ⟨t, nl⟩] [fits : FlagFits ne nl]
    (e : SqlExpr ts ⟨t, ne⟩) : UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨⟨t, nl⟩, fits.fit e⟩)] }

/-- Row-dependent assignment: `.setWith "Age" (fun r => r["Age"] + 1)`. -/
def UpdateStmt.setWith (u : UpdateStmt ts n s) (name : String) {t : SqlPrim}
    {ne nl : Bool} [HasCol s name ⟨t, nl⟩] [fits : FlagFits ne nl]
    (f : Row ts s → SqlExpr ts ⟨t, ne⟩) : UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun r => ⟨⟨t, nl⟩, fits.fit (f r)⟩)] }

/-- Set NULL — only on a column the schema declares NULL-capable. -/
def UpdateStmt.setNull (u : UpdateStmt ts n s) (name : String) {t : SqlPrim}
    {nl : Bool} [HasCol s name ⟨t, nl⟩] (h : nl = true := by rfl) :
    UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨⟨t, true⟩, .nullC t⟩)] }

def UpdateStmt.where' (u : UpdateStmt ts n s)
    (p : Row ts s → SqlExpr ts ⟨.bool, nb⟩) : UpdateStmt ts n s :=
  { u with where? := some (fun r => (p r).anyNull) }

structure DeleteStmt (ts : Ctx) (n : String) (s : Schema) where
  where? : Option (Row ts s → SqlExpr ts ⟨.bool, true⟩) := none

/-- `DELETE FROM t` — restrict with `.where'`. -/
def Table.delete (_ : Table n s) : DeleteStmt ts n s := ⟨none⟩

def DeleteStmt.where' (d : DeleteStmt ts n s)
    (p : Row ts s → SqlExpr ts ⟨.bool, nb⟩) : DeleteStmt ts n s :=
  { d with where? := some (fun r => (p r).anyNull) }

private def whereClause {s : Schema} (p? : Option (Row ts s → SqlExpr ts ⟨.bool, true⟩)) :
    CompileM String :=
  match p? with
  | none => pure ""
  | some p => do return s!" WHERE {← (p (Row.ofAlias "" s)).compile}"

def InsertStmt.compile (i : InsertStmt ts n s) : CompileM String := do
  let cols ← i.values.mapM fun (nm, _) => quote nm
  let vals ← i.values.mapM fun (_, ⟨_, e⟩) => e.compile
  return s!"INSERT INTO {← quote n} ({String.intercalate ", " cols}) VALUES ({String.intercalate ", " vals})"

def UpdateStmt.compile (u : UpdateStmt ts n s) : CompileM String := do
  let row := Row.ofAlias "" s
  let sets ← u.sets.mapM fun (nm, f) => do
    let ⟨_, e⟩ := f row
    return s!"{← quote nm} = {← e.compile}"
  return s!"UPDATE {← quote n} SET {String.intercalate ", " sets}{← whereClause u.where?}"

def DeleteStmt.compile (d : DeleteStmt ts n s) : CompileM String := do
  return s!"DELETE FROM {← quote n}{← whereClause d.where?}"

def InsertStmt.toSql (i : InsertStmt ts n s) (db : DatabaseType := .sqlite) : CompiledSql :=
  let (sql, st) := Id.run ((i.compile.run db).run {})
  { sql, params := st.params }

def UpdateStmt.toSql (u : UpdateStmt ts n s) (db : DatabaseType := .sqlite) : CompiledSql :=
  let (sql, st) := Id.run ((u.compile.run db).run {})
  { sql, params := st.params }

def DeleteStmt.toSql (d : DeleteStmt ts n s) (db : DatabaseType := .sqlite) : CompiledSql :=
  let (sql, st) := Id.run ((d.compile.run db).run {})
  { sql, params := st.params }

/-- A typed cell as a parameter value — the encoder the batched VALUES
insert rides (data already in hand travels as parameters, never as
text). -/
def SqlValue.ofCell : (t : SqlPrim) → t.interp → SqlValue
  | .int, i => .int i
  | .long, i => .long i
  | .double, f => .double f
  | .decimal, d => .decimal (renderDecimal d)
  | .string, s => .string s
  | .bool, b => .bool b
  | .dateTime, s => .dateTime s
  | .guid, g => .guid g

/-- `INSERT INTO t VALUES (…), (…), …` — the batched multi-row write:
rows already in hand (typed `Values`), one statement, grade 1,
affected = the list's length exactly. -/
structure InsertValuesStmt (ts : Ctx) (n : String) (s : Schema) where
  rows : List (Values s)

/-- `t.insertAll rows` — aim an in-hand list at the table. -/
def Table.insertAll (_ : Table n s) (rows : List (Values s)) :
    InsertValuesStmt ts n s :=
  ⟨rows⟩

private def compileValuesRow : (s : Schema) → Values s → CompileM (List String)
  | [], .nil => pure []
  | (_, c) :: rest, .cons cell r => do
      let item ← match c, cell with
        | ⟨t, true⟩, cell =>
            match cell with
            | none => pure "NULL"
            | some v => pushParam (SqlValue.ofCell t v)
        | ⟨t, false⟩, cell => pushParam (SqlValue.ofCell t cell)
      return item :: (← compileValuesRow rest r)

def InsertValuesStmt.compile (st : InsertValuesStmt ts n s) : CompileM String := do
  let cols ← s.mapM fun (nm, _) => quote nm
  let rows ← st.rows.mapM fun r => do
    return s!"({String.intercalate ", " (← compileValuesRow s r)})"
  return s!"INSERT INTO {← quote n} ({String.intercalate ", " cols}) VALUES {String.intercalate ", " rows}"

def InsertValuesStmt.toSql (st : InsertValuesStmt ts n s)
    (db : DatabaseType := .sqlite) : CompiledSql :=
  let (sql, stt) := Id.run ((st.compile.run db).run {})
  { sql, params := stt.params }

/-- `INSERT INTO t (cols) SELECT …` — the batched write: the engine
moves the rows, one statement, grade 1. The source query's schema must
match the target's — enforced by the type. -/
structure InsertSelectStmt (ts : Ctx) (n : String) (s : Schema) where
  source : Query ts s

/-- `t.insertFrom q` — flowing: build the source query, aim it at the
table. -/
def Table.insertFrom (_ : Table n s) (q : Query ts s) :
    InsertSelectStmt ts n s :=
  ⟨q⟩

def InsertSelectStmt.compile (st : InsertSelectStmt ts n s) : CompileM String := do
  let cols ← s.mapM fun (nm, _) => quote nm
  let sub ← (st.source AliasOf).compileStmt
  return s!"INSERT INTO {← quote n} ({String.intercalate ", " cols}) {sub}"

def InsertSelectStmt.toSql (st : InsertSelectStmt ts n s)
    (db : DatabaseType := .sqlite) : CompiledSql :=
  let (sql, stt) := Id.run ((st.compile.run db).run {})
  { sql, params := stt.params }

end LeanLinq
