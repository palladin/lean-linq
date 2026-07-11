import LeanLinq

/-! # Shared harness policy: seed DDL/SQL and skip sets

Used by both the CLI integration runner (`Tests/Integration.lean`) and the
native-driver sweep (`Tests/DriverT.lean`). -/

namespace TQ

def seedCustomers (boolLit : Bool → String) : String :=
  s!"INSERT INTO {"customers"} VALUES " ++
  s!"(1, 25, 'John Doe', {boolLit true}), (2, 30, 'Jane Smith', {boolLit true}), " ++
  s!"(3, 16, 'Minor User', {boolLit false}), (4, 65, 'Senior User', {boolLit true});"

def seedProducts : String :=
  "INSERT INTO products VALUES " ++
  "(1, 'Laptop', 999.99, '2023-01-15 00:00:00', '11111111-1111-1111-1111-111111111111'), " ++
  "(2, 'Mouse', 25.50, '2023-06-10 00:00:00', '22222222-2222-2222-2222-222222222222'), " ++
  "(3, 'Discontinued', NULL, NULL, NULL);"

def seedOrders : String :=
  "INSERT INTO orders VALUES (1, 1, 1, 500), (2, 1, 2, 150), (3, 2, 1, 300), (4, 4, 2, 75);"

def setupSql : LeanLinq.DatabaseType → String
  | .sqlite =>
      "DROP TABLE IF EXISTS orders; DROP TABLE IF EXISTS products; DROP TABLE IF EXISTS customers;
CREATE TABLE customers (\"Id\" INTEGER PRIMARY KEY, \"Age\" INTEGER, \"Name\" TEXT, \"IsActive\" INTEGER);
CREATE TABLE products (\"Id\" INTEGER PRIMARY KEY, \"ProductName\" TEXT, \"Price\" REAL, \"CreatedDate\" TEXT, \"UniqueId\" TEXT);
CREATE TABLE orders (\"Id\" INTEGER PRIMARY KEY, \"CustomerId\" INTEGER, \"ProductId\" INTEGER, \"Amount\" INTEGER);
" ++ seedCustomers (fun b => if b then "1" else "0") ++ seedProducts ++ seedOrders
  | .postgres =>
      "DROP TABLE IF EXISTS orders; DROP TABLE IF EXISTS products; DROP TABLE IF EXISTS customers;
CREATE TABLE customers (\"Id\" INT PRIMARY KEY, \"Age\" INT, \"Name\" VARCHAR(255), \"IsActive\" BOOLEAN);
CREATE TABLE products (\"Id\" INT PRIMARY KEY, \"ProductName\" VARCHAR(255), \"Price\" DECIMAL(18,2), \"CreatedDate\" TIMESTAMP, \"UniqueId\" UUID);
CREATE TABLE orders (\"Id\" INT PRIMARY KEY, \"CustomerId\" INT, \"ProductId\" INT, \"Amount\" INT);
" ++ seedCustomers (fun b => if b then "true" else "false") ++ seedProducts ++ seedOrders
  | .sqlServer =>
      "DROP TABLE IF EXISTS [orders]; DROP TABLE IF EXISTS [products]; DROP TABLE IF EXISTS [customers];
CREATE TABLE [customers] ([Id] INT PRIMARY KEY, [Age] INT, [Name] NVARCHAR(255), [IsActive] BIT);
CREATE TABLE [products] ([Id] INT PRIMARY KEY, [ProductName] NVARCHAR(255), [Price] DECIMAL(18,2), [CreatedDate] DATETIME2, [UniqueId] UNIQUEIDENTIFIER);
CREATE TABLE [orders] ([Id] INT PRIMARY KEY, [CustomerId] INT, [ProductId] INT, [Amount] INT);
" ++ seedCustomers (fun b => if b then "1" else "0") ++ seedProducts ++ seedOrders

/-- Cases whose output depends on the current time: execute-only. -/
def skipResults : List String :=
  ["DateTimeNow", "DateTimeFunctionsInSelect",
   "CDateTimeNow", "CDateTimeFunctionsInSelect"]

/-- Cases where engines legitimately disagree; excluded from cross-dialect
and evaluator comparison, still checked against their per-dialect golden.
`FromSelectAvg`: AVG over integers is integer division on SQL Server (256)
but exact on PostgreSQL/SQLite (256.25). `FromGroupByMultipleOrderBySelect`:
ORDER BY COUNT(*) DESC where every count ties, so order is engine-specific. -/
def crossDialectAllowlist : List String := [
  "FromSelectAvg", "FromGroupByMultipleOrderBySelect",
  "CFromSelectAvg", "CFromGroupByMultipleOrderBySelect"
]

end TQ
