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

end LeanLinq
