import LeanLinq.Core.Schema

/-! Typed table creation. Column names, primitive types, and nullability come
from the same schema used by queries. Constraints refer to that schema.
All four query dialects are supported; this is creation, not schema migration. -/

namespace LeanLinq

namespace DDL

def validName (name : String) : Bool :=
  !name.toList.isEmpty && !name.toList.contains (Char.ofNat 0)

def validSchema (name : String) (schema : Schema) : Bool :=
  validName name && !schema.isEmpty && decide (schema.map Prod.fst).Nodup &&
    schema.all (fun column => validName column.1)

private def utf16Length (s : String) : Nat :=
  s.toList.foldl (fun n c => n + if c.toNat > 0xffff then 2 else 1) 0

/-- Dialect identifier limits. Temporary SQL Server tables are outside this
API; MySQL metadata identifiers only support BMP characters. -/
def nameFits (db : DatabaseType) (name : String) : Bool :=
  match db with
  | .sqlite => true
  | .postgres => name.toUTF8.size ≤ 63
  | .sqlServer => utf16Length name ≤ 128
  | .mysql => name.length ≤ 64 && name.toList.getLast? != some ' ' &&
      name.toList.all (fun c => c.toNat ≤ 0xffff)

def namesFit (db : DatabaseType) (name : String) (schema : Schema) : Bool :=
  nameFits db name && schema.all (fun column => nameFits db column.1) &&
    (db != .sqlServer || name.toList.head? != some '#')

private def columnType (db : DatabaseType) (type : SqlPrim) (length : Option Nat) : String :=
  match db, type with
  | .sqlite, .int | .sqlite, .long => "INT"
  | .sqlite, .double => "REAL"
  | .sqlite, .decimal => "NUMERIC"
  | .sqlite, .bool => "INTEGER"
  | .sqlite, _ => "TEXT"
  | _, .int => "INTEGER"
  | _, .long => "BIGINT"
  | .postgres, .double => "DOUBLE PRECISION"
  | .mysql, .double => "DOUBLE"
  | .sqlServer, .double => "FLOAT(53)"
  | .postgres, .decimal => "NUMERIC"
  | _, .decimal => "DECIMAL(38,3)"
  | .postgres, .string => length.elim "TEXT" (fun n => s!"VARCHAR({n})")
  | .mysql, .string => length.elim "LONGTEXT" (fun n => s!"VARCHAR({n})")
  | .sqlServer, .string => length.elim "NVARCHAR(MAX)" (fun n => s!"NVARCHAR({n})")
  | .sqlServer, .bool => "BIT"
  | _, .bool => "BOOLEAN"
  | .postgres, .dateTime => "TIMESTAMP WITHOUT TIME ZONE"
  | .mysql, .dateTime => "DATETIME(6)"
  | .sqlServer, .dateTime => "DATETIME2(6)"
  | .postgres, .guid => "UUID"
  | .mysql, .guid => "CHAR(36)"
  | .sqlServer, .guid => "UNIQUEIDENTIFIER"

end DDL

/-- The column name at a typed position in a schema. -/
def KeyRef.name : {schema : Schema} → KeyRef schema type → String
  | (name, _) :: _, .here => name
  | _ :: _, .there ref => ref.name

/-- A non-nullable column belonging to this schema. The primitive type is
stored with its reference so composite keys can mix column types. -/
structure PrimaryKeyColumn (schema : Schema) where
  type : SqlPrim
  ref : KeyRef schema ⟨type, false⟩

/-- Resolve a primary-key column using the same schema lookup as queries. -/
def PrimaryKeyColumn.column (name : String) {type : SqlPrim}
    [column : HasCol schema name ⟨type, false⟩] : PrimaryKeyColumn schema :=
  ⟨type, column.ref⟩

/-- Names are derived from typed references, never stored independently. -/
def PrimaryKeyColumn.name (column : PrimaryKeyColumn schema) : String :=
  column.ref.name

/-- An explicit storage bound for a string column of this schema. SQL Server
counts UTF-16 code units; the other dialects count characters. -/
structure StringLength (schema : Schema) where
  nullable : Bool
  ref : KeyRef schema ⟨.string, nullable⟩
  length : Nat
  positive : 0 < length := by decide

def StringLength.column (name : String) (length : Nat) {nullable : Bool}
    [column : HasCol schema name ⟨.string, nullable⟩]
    (positive : 0 < length := by decide) : StringLength schema :=
  ⟨nullable, column.ref, length, positive⟩

def StringLength.name (column : StringLength schema) : String := column.ref.name

/-- A table-creation statement indexed by its table name and row schema.
The invariants also apply when constructing this structure directly. -/
structure CreateTable (name : String) (schema : Schema) where
  primaryKey : List (PrimaryKeyColumn schema) := []
  ifNotExists : Bool := true
  stringLengths : List (StringLength schema) := []
  schemaValid : DDL.validSchema name schema = true := by decide
  primaryKeyDistinct : (primaryKey.map PrimaryKeyColumn.name).Nodup := by decide
  stringLengthsDistinct : (stringLengths.map StringLength.name).Nodup := by decide

/-- Construct DDL from a query table. Literal schemas and keys discharge the
validity obligations at elaboration; misspelled/nullable/repeated keys fail. -/
def Table.create (_ : Table name schema) (primaryKey : List (PrimaryKeyColumn schema) := [])
    (ifNotExists := true)
    (stringLengths : List (StringLength schema) := [])
    (schemaValid : DDL.validSchema name schema = true := by decide)
    (primaryKeyDistinct : (primaryKey.map PrimaryKeyColumn.name).Nodup := by decide)
    (stringLengthsDistinct : (stringLengths.map StringLength.name).Nodup := by decide) :
    CreateTable name schema :=
  { primaryKey, ifNotExists, stringLengths, schemaValid, primaryKeyDistinct, stringLengthsDistinct }

/-- Look up a string's declared storage bound. -/
def CreateTable.stringLength (statement : CreateTable name schema) (column : String) : Option Nat :=
  (statement.stringLengths.find? (·.name == column)).map (·.length)

private def keyBytes (db : DatabaseType) (statement : CreateTable name schema)
    (column : PrimaryKeyColumn schema) : Nat :=
  match column.type with
  | .int => 4
  | .long | .double | .dateTime => 8
  | .bool => 1
  | .decimal => if db == .mysql then 18 else 17
  | .guid => if db == .mysql then 144 else 16
  | .string => (statement.stringLength column.name).getD 0 * (if db == .mysql then 4 else 2)

/-- Static dialect checks. MySQL targets InnoDB/DYNAMIC with utf8mb4 and
the standard 16 KiB (or larger) page size. SQL Server uses a clustered PK.
Server permissions, collations, row limits and existing objects still apply. -/
def CreateTable.validFor (statement : CreateTable name schema) (db : DatabaseType) : Bool :=
  DDL.namesFit db name schema &&
  statement.stringLengths.all (fun column => column.length ≤ match db with
    | .sqlite => 1000000000
    | .postgres => 10485760
    | .mysql => 16383
    | .sqlServer => 4000) &&
  match db with
  | .postgres | .sqlite => true
  | .mysql | .sqlServer =>
      statement.primaryKey.all (fun column =>
        column.type != .string || (statement.stringLength column.name).isSome) &&
      statement.primaryKey.length ≤ (if db == .mysql then 16 else 32) &&
      (statement.primaryKey.map (keyBytes db statement)).sum ≤ (if db == .mysql then 3072 else 900)

/-- Render typed DDL for a supported dialect. Names and physical key limits
are checked before SQL can be generated. Creation never validates or migrates
an existing table. SQL Server catches only the existing-table error, including
when another initializer creates the same table concurrently. -/
def CreateTable.toSql (statement : CreateTable name schema) (db : DatabaseType)
    (_valid : statement.validFor db = true := by decide) : String :=
  let quote := db.quoteIdent
  let columns := schema.map fun (name, type) =>
    quote name ++ " " ++ DDL.columnType db type.ty (statement.stringLength name) ++
      (if type.nullable then " NULL" else " NOT NULL") ++
      (if db == .sqlite then (statement.stringLength name).elim ""
        (fun n => s!" CHECK (length({quote name}) <= {n})") else "")
  let clauses := if statement.primaryKey.isEmpty then columns else
    columns ++ ["PRIMARY KEY (" ++ String.intercalate ", "
      (statement.primaryKey.map (quote ∘ PrimaryKeyColumn.name)) ++ ")"]
  let sql := "CREATE TABLE " ++
    (if statement.ifNotExists && db != .sqlServer then "IF NOT EXISTS " else "") ++
    quote name ++ " (" ++ String.intercalate ", " clauses ++ ")" ++
    (if db == .mysql then " ENGINE=InnoDB ROW_FORMAT=DYNAMIC DEFAULT CHARSET=utf8mb4" else "")
  if db == .sqlServer && statement.ifNotExists then
    let object := "N'" ++ (quote name).replace "'" "''" ++ "'"
    s!"BEGIN TRY {sql}; END TRY BEGIN CATCH IF ERROR_NUMBER() <> 2714 OR OBJECT_ID({object}, N'U') IS NULL THROW; END CATCH"
  else sql

def CreateTable.toPostgres (statement : CreateTable name schema)
    (valid : statement.validFor .postgres = true := by decide) : String :=
  statement.toSql .postgres valid

def CreateTable.toSqlite (statement : CreateTable name schema)
    (valid : statement.validFor .sqlite = true := by decide) : String :=
  statement.toSql .sqlite valid

def CreateTable.toMysql (statement : CreateTable name schema)
    (valid : statement.validFor .mysql = true := by decide) : String :=
  statement.toSql .mysql valid

def CreateTable.toMssql (statement : CreateTable name schema)
    (valid : statement.validFor .sqlServer = true := by decide) : String :=
  statement.toSql .sqlServer valid

end LeanLinq
