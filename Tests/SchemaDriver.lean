import LeanLinq
import Tests.DDL

/-! The same typed DDL scenarios run through all four native drivers. -/

namespace SchemaDriver
open LeanLinq

structure Ops (db : DatabaseType) where
  create : {name : String} → {schema : Schema} → (statement : CreateTable name schema) →
    statement.validFor db = true → IO Unit
  query : {tables : List (String × Schema)} → {schema : Schema} →
    Query { tables } schema → IO (List (Values schema))
  insert : {tables : List (String × Schema)} → {name : String} → {schema : Schema} →
    InsertValuesStmt { tables } name schema → IO Nat
  execRaw : String → IO Unit

private def rejects (label : String) (action : IO α) : IO Unit := do
  let rejected ← try
    discard action
    pure false
  catch _ => pure true
  unless rejected do throw (IO.userError s!"DDL: {label} was not rejected")

private abbrev Records : Schema :=
  [("part", .string), ("select", .long), ("value", .null .string)]
private def records : Table "ddl '\"records`]" Records := ⟨⟩
private abbrev C : Ctx := { tables := [("ddl '\"records`]", Records)] }
private def statement := records.create [.column "part", .column "select"]
  (stringLengths := [.column "part" 8, .column "value" 32])

private def row (part : String) (key : Int) (value : Option String) : Values Records :=
  .cons part (.cons key (.cons value .nil))

private abbrev Types : Schema :=
  [("i", .int), ("l", .long), ("f", .double), ("d", .decimal),
   ("s", .string), ("b", .bool), ("t", .dateTime), ("g", .guid)]
private def types : Table "ddl_types" Types := ⟨⟩
private def nullableTypes : Table "ddl_nullable_types" Types.asNull := ⟨⟩
private abbrev TC : Ctx := { tables := [("ddl_types", Types), ("ddl_nullable_types", Types.asNull)] }

private def typedRow : Values Types :=
  .cons (-7) (.cons 5000000000 (.cons 1.25 (.cons (-12345)
    (.cons "Καλημέρα 😀" (.cons true (.cons "2024-02-29 12:34:56"
      (.cons "12345678-1234-5678-9abc-def012345678" .nil)))))))

private def nullRow : Values Types.asNull :=
  .cons none (.cons none (.cons none (.cons none
    (.cons none (.cons none (.cons none (.cons none .nil)))))))

private def nullableRow : Values Types.asNull :=
  .cons (some (-7)) (.cons (some 5000000000) (.cons (some 1.25) (.cons (some (-12345))
    (.cons (some "Καλημέρα 😀") (.cons (some true) (.cons (some "2024-02-29 12:34:56")
      (.cons (some "12345678-1234-5678-9abc-def012345678") .nil)))))))

def run (db : DatabaseType) (ops : Ops db) : IO Unit := do
  let quote := db.quoteIdent
  -- Start with a fresh, test-owned schema; the second create must preserve data.
  ops.execRaw s!"DROP TABLE IF EXISTS {quote "ddl '\"records`]"}"
  ops.create statement (by cases db <;> decide)
  let expected := [row "α" 7 (some ""), row "b" 7 none, row "α" 8 (some "payload")]
  discard <| ops.insert (records.insertAll (ts := C) expected)
  ops.create statement (by cases db <;> decide)
  let actual ← ops.query (Query.from' (ts := C) records)
  unless actual.length == expected.length && expected.all actual.contains do
    throw (IO.userError s!"DDL: composite keys / NULL / Unicode / empty strings did not round-trip: {repr actual}")
  rejects "duplicate composite key" (ops.insert (records.insertAll (ts := C) [row "α" 7 none]))
  rejects "oversized key value" (ops.insert (records.insertAll (ts := C) [row "123456789" 9 none]))
  rejects "oversized nullable string" (ops.insert
    (records.insertAll (ts := C) [row "c" 9 (some (String.ofList (List.replicate 33 'x')))]))
  rejects "NULL in NOT NULL column" <| ops.execRaw
    s!"INSERT INTO {quote "ddl '\"records`]"} ({quote "part"}, {quote "select"}, {quote "value"}) VALUES (NULL, 1, NULL)"
  rejects "create without ifNotExists" <| ops.create
    { statement with ifNotExists := false } (by cases db <;> decide)

  ops.execRaw "DROP TABLE IF EXISTS ddl_types; DROP TABLE IF EXISTS ddl_nullable_types"
  ops.create types.create (by cases db <;> decide)
  ops.create nullableTypes.create (by cases db <;> decide)
  discard <| ops.insert (types.insertAll (ts := TC) [typedRow])
  discard <| ops.insert (nullableTypes.insertAll (ts := TC) [nullRow, nullableRow])
  let actual ← ops.query (Query.from' (ts := TC) types)
  unless actual == [typedRow] do throw (IO.userError s!"DDL: primitive type round-trip failed: {repr actual}")
  let actual ← ops.query (Query.from' (ts := TC) nullableTypes)
  unless actual.length == 2 && actual.contains nullRow && actual.contains nullableRow do
    throw (IO.userError "DDL: nullable primitive type round-trip failed")

  -- A one-column integer PK must still reject NULL (SQLite INTEGER PRIMARY KEY
  -- would silently generate an ID, so this compiler uses INT).
  let ids : Table "ddl_ids" [("id", .int)] := ⟨⟩
  ops.execRaw "DROP TABLE IF EXISTS ddl_ids"
  ops.create (ids.create [.column "id"]) (by cases db <;> decide)
  rejects "NULL integer primary key" (ops.execRaw "INSERT INTO ddl_ids VALUES (NULL)")
  -- SQL Server's emulation only catches an existing table. The native
  -- IF NOT EXISTS dialects also accept an existing view without changing it.
  ops.execRaw "DROP VIEW IF EXISTS ddl_view_collision"
  ops.execRaw "CREATE VIEW ddl_view_collision AS SELECT 1 AS id"
  let collision : Table "ddl_view_collision" [("id", .int)] := ⟨⟩
  if db == .sqlServer then
    rejects "existing view" <| ops.create collision.create (by cases db <;> decide)
  else
    ops.create collision.create (by cases db <;> decide)
  ops.execRaw "DROP VIEW ddl_view_collision"
  IO.println s!"DDL({repr db}): typed creation, constraints, idempotence, and all primitive codecs passed"

end SchemaDriver
