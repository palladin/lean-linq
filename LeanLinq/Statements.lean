import LeanLinq.Compiler.Query

/-! # Data-modification statements: INSERT / UPDATE / DELETE

Column references are name-checked at compile time via `HasCol` (same
machinery as `row["Name"]`), and values are typed against the column's type.
`NULL` assignments go through `setNull`/`valueNull`. -/

namespace LeanLinq

structure InsertStmt (s : Schema) where
  table : Table s
  values : List (String × ((u : SqlType) × SqlExpr u)) := []

/-- `INSERT INTO t …` — add columns with `.value`/`.valueNull`. -/
def Table.insert (t : Table s) : InsertStmt s := ⟨t, []⟩

def InsertStmt.value (i : InsertStmt s) (name : String) {t : SqlType}
    [HasCol s name t] (e : SqlExpr t) : InsertStmt s :=
  { i with values := i.values ++ [(name, ⟨t, e⟩)] }

def InsertStmt.valueNull (i : InsertStmt s) (name : String) {t : SqlType}
    [HasCol s name t] : InsertStmt s :=
  { i with values := i.values ++ [(name, ⟨t, .nullC t⟩)] }

structure UpdateStmt (s : Schema) where
  table : Table s
  sets : List (String × (Row s → (u : SqlType) × SqlExpr u)) := []
  where? : Option (Row s → SqlExpr .bool) := none

/-- `UPDATE t SET …` — add assignments with `.set`/`.setWith`/`.setNull`,
restrict with `.where'`. -/
def Table.update (t : Table s) : UpdateStmt s := ⟨t, [], none⟩

def UpdateStmt.set (u : UpdateStmt s) (name : String) {t : SqlType}
    [HasCol s name t] (e : SqlExpr t) : UpdateStmt s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨t, e⟩)] }

/-- Row-dependent assignment: `.setWith "Age" (fun r => r["Age"] + 1)`. -/
def UpdateStmt.setWith (u : UpdateStmt s) (name : String) {t : SqlType}
    [HasCol s name t] (f : Row s → SqlExpr t) : UpdateStmt s :=
  { u with sets := u.sets ++ [(name, fun r => ⟨t, f r⟩)] }

def UpdateStmt.setNull (u : UpdateStmt s) (name : String) {t : SqlType}
    [HasCol s name t] : UpdateStmt s :=
  { u with sets := u.sets ++ [(name, fun _ => ⟨t, .nullC t⟩)] }

def UpdateStmt.where' (u : UpdateStmt s) (p : Row s → SqlExpr .bool) : UpdateStmt s :=
  { u with where? := some p }

structure DeleteStmt (s : Schema) where
  table : Table s
  where? : Option (Row s → SqlExpr .bool) := none

/-- `DELETE FROM t` — restrict with `.where'`. -/
def Table.delete (t : Table s) : DeleteStmt s := ⟨t, none⟩

def DeleteStmt.where' (d : DeleteStmt s) (p : Row s → SqlExpr .bool) : DeleteStmt s :=
  { d with where? := some p }

private def whereClause {s : Schema} (p? : Option (Row s → SqlExpr .bool)) :
    CompileM String :=
  match p? with
  | none => pure ""
  | some p => do return s!" WHERE {← (p (Row.ofAlias "" s)).compile}"

def InsertStmt.compile (i : InsertStmt s) : CompileM String := do
  let cols ← i.values.mapM fun (n, _) => quote n
  let vals ← i.values.mapM fun (_, ⟨_, e⟩) => e.compile
  return s!"INSERT INTO {← quote i.table.name} ({String.intercalate ", " cols}) VALUES ({String.intercalate ", " vals})"

def UpdateStmt.compile (u : UpdateStmt s) : CompileM String := do
  let row := Row.ofAlias "" s
  let sets ← u.sets.mapM fun (n, f) => do
    let ⟨_, e⟩ := f row
    return s!"{← quote n} = {← e.compile}"
  return s!"UPDATE {← quote u.table.name} SET {String.intercalate ", " sets}{← whereClause u.where?}"

def DeleteStmt.compile (d : DeleteStmt s) : CompileM String := do
  return s!"DELETE FROM {← quote d.table.name}{← whereClause d.where?}"

def InsertStmt.toSql (i : InsertStmt s) (db : DatabaseType := .sqlite) : Compiled :=
  let (sql, st) := Id.run ((i.compile.run db).run {})
  { sql, params := st.params }

def UpdateStmt.toSql (u : UpdateStmt s) (db : DatabaseType := .sqlite) : Compiled :=
  let (sql, st) := Id.run ((u.compile.run db).run {})
  { sql, params := st.params }

def DeleteStmt.toSql (d : DeleteStmt s) (db : DatabaseType := .sqlite) : Compiled :=
  let (sql, st) := Id.run ((d.compile.run db).run {})
  { sql, params := st.params }

end LeanLinq
