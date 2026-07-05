import LeanLinq.Compiler.Query

/-! # Data-modification statements: INSERT / UPDATE / DELETE

Column references are name-checked at compile time via `HasCol` (same
machinery as `row["Name"]`), and values are typed against the column's type.
`NULL` assignments go through `setNull`/`valueNull`. The target table's name
and schema are type indices (from `Table n s`), so a statement — like a
query — is fully static about what it touches. -/

namespace LeanLinq

structure InsertStmt (ts : Ctx) (n : String) (s : Schema) where
  values : List (String × ((u : SqlType) × SqlExpr ts u)) := []

/-- `INSERT INTO t …` — add columns with `.value`/`.valueNull`. -/
def Table.insert (_ : Table n s) : InsertStmt ts n s := ⟨[]⟩

def InsertStmt.value (i : InsertStmt ts n s) (name : String) {t : SqlType}
    [HasCol s name t] (e : SqlExpr ts t) : InsertStmt ts n s :=
  { i with values := i.values ++ [(name, ⟨t, e⟩)] }

def InsertStmt.valueNull (i : InsertStmt ts n s) (name : String) {t : SqlType}
    [HasCol s name t] : InsertStmt ts n s :=
  { i with values := i.values ++ [(name, ⟨t, .nullC t⟩)] }

structure UpdateStmt (ts : Ctx) (n : String) (s : Schema) where
  sets : List (String × (Row ts s → (u : SqlType) × SqlExpr ts u)) := []
  where? : Option (Row ts s → SqlExpr ts .bool) := none

/-- `UPDATE t SET …` — add assignments with `.set`/`.setWith`/`.setNull`,
restrict with `.where'`. -/
def Table.update (_ : Table n s) : UpdateStmt ts n s := ⟨[], none⟩

def UpdateStmt.set (u : UpdateStmt ts n s) (name : String) {t : SqlType}
    [HasCol s name t] (e : SqlExpr ts t) : UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨t, e⟩)] }

/-- Row-dependent assignment: `.setWith "Age" (fun r => r["Age"] + 1)`. -/
def UpdateStmt.setWith (u : UpdateStmt ts n s) (name : String) {t : SqlType}
    [HasCol s name t] (f : Row ts s → SqlExpr ts t) : UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun r => ⟨t, f r⟩)] }

def UpdateStmt.setNull (u : UpdateStmt ts n s) (name : String) {t : SqlType}
    [HasCol s name t] : UpdateStmt ts n s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨t, .nullC t⟩)] }

def UpdateStmt.where' (u : UpdateStmt ts n s) (p : Row ts s → SqlExpr ts .bool) :
    UpdateStmt ts n s :=
  { u with where? := some p }

structure DeleteStmt (ts : Ctx) (n : String) (s : Schema) where
  where? : Option (Row ts s → SqlExpr ts .bool) := none

/-- `DELETE FROM t` — restrict with `.where'`. -/
def Table.delete (_ : Table n s) : DeleteStmt ts n s := ⟨none⟩

def DeleteStmt.where' (d : DeleteStmt ts n s) (p : Row ts s → SqlExpr ts .bool) :
    DeleteStmt ts n s :=
  { d with where? := some p }

private def whereClause {s : Schema} (p? : Option (Row ts s → SqlExpr ts .bool)) :
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
