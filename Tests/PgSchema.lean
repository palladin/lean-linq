import LeanLinq.Driver.Postgres
import Tests.SchemaDriver

namespace PgSchemaTests
open LeanLinq

def run (conn : Pg.Conn) : IO Unit := do
  conn.createTable (⟨⟩ : Table "ddl_string_convenience" [("id", .string)])
    (primaryKey := [.column "id"]) (stringLengths := [.column "id" 16])
  SchemaDriver.run .postgres {
    create := fun statement valid => conn.execCreateTable statement valid
    query := fun q => conn.query q
    insert := fun statement => conn.execInsertValues statement
    execRaw := conn.execRaw }

end PgSchemaTests
