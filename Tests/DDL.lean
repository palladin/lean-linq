import LeanLinq

namespace DDLTests
open LeanLinq

set_option maxRecDepth 4096

abbrev Records : Schema := [("run", .string), ("key", .string), ("value", .null .string)]
def records : Table "cloud_records" Records := ⟨⟩

#guard (records.create [.column "run", .column "key"]).toPostgres ==
  "CREATE TABLE IF NOT EXISTS \"cloud_records\" (\"run\" TEXT NOT NULL, \"key\" TEXT NOT NULL, \"value\" TEXT NULL, PRIMARY KEY (\"run\", \"key\"))"

def quoted : Table "a\"b" [("select", .int), ("x\"y", .null .bool)] := ⟨⟩
#guard (quoted.create (ifNotExists := false)).toPostgres ==
  "CREATE TABLE \"a\"\"b\" (\"select\" INTEGER NOT NULL, \"x\"\"y\" BOOLEAN NULL)"

abbrev AllTypes : Schema := [("i", .int), ("l", .long), ("f", .double), ("d", .decimal),
  ("s", .string), ("b", .bool), ("t", .dateTime), ("g", .guid)]
def allTypes : Table "types" AllTypes := ⟨⟩
#guard allTypes.create.toPostgres ==
  "CREATE TABLE IF NOT EXISTS \"types\" (\"i\" INTEGER NOT NULL, \"l\" BIGINT NOT NULL, \"f\" DOUBLE PRECISION NOT NULL, \"d\" NUMERIC NOT NULL, \"s\" TEXT NOT NULL, \"b\" BOOLEAN NOT NULL, \"t\" TIMESTAMP WITHOUT TIME ZONE NOT NULL, \"g\" UUID NOT NULL)"

-- Heterogeneous keys retain their primitive types and caller-specified order.
def mixedKey : List (PrimaryKeyColumn AllTypes) := [.column "s", .column "l"]
#guard mixedKey.map PrimaryKeyColumn.type == [.string, .long]
#guard (allTypes.create mixedKey).toPostgres.endsWith "PRIMARY KEY (\"s\", \"l\"))"

-- The raw reference carries membership and non-nullability too.
def runColumn : PrimaryKeyColumn Records := ⟨.string, .here⟩
def keyColumn : PrimaryKeyColumn Records := ⟨.string, .there .here⟩
#guard (records.create [keyColumn, runColumn]).toPostgres.endsWith
  "PRIMARY KEY (\"key\", \"run\"))"
#check_failure (⟨.long, .here⟩ : PrimaryKeyColumn Records)
#check_failure (⟨.string, .there (.there .here)⟩ : PrimaryKeyColumn Records)
#check_failure (⟨.string, .here⟩ : PrimaryKeyColumn [])
#check_failure allTypes.create [runColumn]
#check_failure records.create [runColumn, .column "run"]

-- Ordinary calls reject invalid constraints before any SQL is sent.
#check_failure records.create [.column "missing"]
#check_failure records.create [.column "value"]
#check_failure records.create [.column "run", .column "run"]
#check_failure (records.create [.column "run"]).toPostgres (name := "other")
#check_failure ((⟨⟩ : Table "bad" [("x", .int), ("x", .string)]).create)
#check_failure ((⟨⟩ : Table "empty" []).create)
#check_failure ((⟨⟩ : Table "" Records).create)
#check_failure ((⟨⟩ : Table "bad" [("", .int)]).create)
#check_failure ((⟨⟩ : Table (String.singleton (Char.ofNat 0)) Records).create)
#check_failure ((⟨⟩ : Table "bad" [(String.singleton (Char.ofNat 0), .int)]).create)

-- The raw statement cannot bypass the same invariants.
#check_failure ({ primaryKey := [.column "missing"] } : CreateTable "cloud_records" Records)
#check_failure ({ primaryKey := [.column "value"] } : CreateTable "cloud_records" Records)
#check_failure ({ primaryKey := [.column "run", .column "run"] } : CreateTable "cloud_records" Records)

-- Byte length matters: quoted Unicode names must not be silently truncated.
def boundary : Table (String.ofList (List.replicate 63 'x')) Records := ⟨⟩
#check boundary.create.toPostgres
#check_failure ((⟨⟩ : Table (String.ofList (List.replicate 64 'x')) Records).create.toPostgres)
#check_failure ((⟨⟩ : Table (String.ofList (List.replicate 32 'λ')) Records).create.toPostgres)
#check_failure ((⟨⟩ : Table "bad" [(String.ofList (List.replicate 64 'x'), .int)]).create.toPostgres)

-- Every supported primitive, including nullable data, has a dialect mapping.
#guard allTypes.create.toSqlite ==
  "CREATE TABLE IF NOT EXISTS \"types\" (\"i\" INT NOT NULL, \"l\" INT NOT NULL, \"f\" REAL NOT NULL, \"d\" NUMERIC NOT NULL, \"s\" TEXT NOT NULL, \"b\" INTEGER NOT NULL, \"t\" TEXT NOT NULL, \"g\" TEXT NOT NULL)"
#guard allTypes.create.toMysql ==
  "CREATE TABLE IF NOT EXISTS `types` (`i` INTEGER NOT NULL, `l` BIGINT NOT NULL, `f` DOUBLE NOT NULL, `d` DECIMAL(38,3) NOT NULL, `s` LONGTEXT NOT NULL, `b` BOOLEAN NOT NULL, `t` DATETIME(6) NOT NULL, `g` CHAR(36) NOT NULL) ENGINE=InnoDB ROW_FORMAT=DYNAMIC DEFAULT CHARSET=utf8mb4"
#guard (allTypes.create (ifNotExists := false)).toMssql ==
  "CREATE TABLE [types] ([i] INTEGER NOT NULL, [l] BIGINT NOT NULL, [f] FLOAT(53) NOT NULL, [d] DECIMAL(38,3) NOT NULL, [s] NVARCHAR(MAX) NOT NULL, [b] BIT NOT NULL, [t] DATETIME2(6) NOT NULL, [g] UNIQUEIDENTIFIER NOT NULL)"

def bounded := records.create [.column "run", .column "key"]
  (stringLengths := [.column "run" 64, .column "key" 128, .column "value" 500])
#guard bounded.toPostgres ==
  "CREATE TABLE IF NOT EXISTS \"cloud_records\" (\"run\" VARCHAR(64) NOT NULL, \"key\" VARCHAR(128) NOT NULL, \"value\" VARCHAR(500) NULL, PRIMARY KEY (\"run\", \"key\"))"
#guard bounded.toSqlite ==
  "CREATE TABLE IF NOT EXISTS \"cloud_records\" (\"run\" TEXT NOT NULL CHECK (length(\"run\") <= 64), \"key\" TEXT NOT NULL CHECK (length(\"key\") <= 128), \"value\" TEXT NULL CHECK (length(\"value\") <= 500), PRIMARY KEY (\"run\", \"key\"))"
#guard bounded.toMysql ==
  "CREATE TABLE IF NOT EXISTS `cloud_records` (`run` VARCHAR(64) NOT NULL, `key` VARCHAR(128) NOT NULL, `value` VARCHAR(500) NULL, PRIMARY KEY (`run`, `key`)) ENGINE=InnoDB ROW_FORMAT=DYNAMIC DEFAULT CHARSET=utf8mb4"
#guard bounded.toMssql ==
  "BEGIN TRY CREATE TABLE [cloud_records] ([run] NVARCHAR(64) NOT NULL, [key] NVARCHAR(128) NOT NULL, [value] NVARCHAR(500) NULL, PRIMARY KEY ([run], [key])); END TRY BEGIN CATCH IF ERROR_NUMBER() <> 2714 OR OBJECT_ID(N'[cloud_records]', N'U') IS NULL THROW; END CATCH"

def escaped : Table "a'\"b`]" [("select", .int), ("x`]", .null .bool)] := ⟨⟩
#guard escaped.create.toMysql ==
  "CREATE TABLE IF NOT EXISTS `a'\"b``]` (`select` INTEGER NOT NULL, `x``]` BOOLEAN NULL) ENGINE=InnoDB ROW_FORMAT=DYNAMIC DEFAULT CHARSET=utf8mb4"
#guard escaped.create.toMssql ==
  "BEGIN TRY CREATE TABLE [a'\"b`]]] ([select] INTEGER NOT NULL, [x`]]] BIT NULL); END TRY BEGIN CATCH IF ERROR_NUMBER() <> 2714 OR OBJECT_ID(N'[a''\"b`]]]', N'U') IS NULL THROW; END CATCH"

-- Storage annotations carry column membership and the string type.
#check_failure records.create (stringLengths := [.column "missing" 10])
#check_failure allTypes.create (stringLengths := [.column "i" 10])
#check_failure records.create (stringLengths := [.column "run" 0])
#check_failure records.create (stringLengths := [.column "run" 10, .column "run" 20])
#check_failure (⟨false, .here, 10, by decide⟩ : StringLength AllTypes)
#check_failure ({ stringLengths := [.column "run" 10, .column "run" 20] } :
  CreateTable "cloud_records" Records)
#check_failure (records.create [.column "run"]).toMysql
#check_failure (records.create [.column "run"]).toMssql
#check_failure (records.create (stringLengths := [.column "value" 4001])).toMssql
#check_failure (records.create (stringLengths := [.column "value" 16384])).toMysql

-- Whole composite keys, not just individual string columns, must fit.
#check (records.create [.column "run"] (stringLengths := [.column "run" 450])).toMssql
#check_failure (records.create [.column "run", .column "key"]
  (stringLengths := [.column "run" 300, .column "key" 151])).toMssql
#check (records.create [.column "run"] (stringLengths := [.column "run" 768])).toMysql
#check_failure (records.create [.column "run", .column "key"]
  (stringLengths := [.column "run" 384, .column "key" 385])).toMysql

-- MySQL counts characters; SQL Server stores identifiers in UTF-16.
#check ((⟨⟩ : Table (String.ofList (List.replicate 64 'λ')) Records).create.toMysql)
#check_failure ((⟨⟩ : Table (String.ofList (List.replicate 65 'λ')) Records).create.toMysql)
#check ((⟨⟩ : Table (String.ofList (List.replicate 128 'x')) Records).create.toMssql)
#check_failure ((⟨⟩ : Table (String.ofList (List.replicate 129 'x')) Records).create.toMssql)
#check_failure ((⟨⟩ : Table "😀" Records).create.toMysql)
#check_failure ((⟨⟩ : Table "#temporary" Records).create.toMssql)
#check_failure ((⟨⟩ : Table "trailing " Records).create.toMysql)

end DDLTests
