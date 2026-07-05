import LeanLinq

/-! Test models — the classic customers / products / orders trio — and the
`Case` registry entry: per-dialect compilation *plus* expected result rows
computed by the evaluator (`Query.run`) over the typed seed database. The
expected side is derived from the same query value that compiles to SQL, so
every registered case is checked against the executable semantics with no
hand-written expectations. -/

open LeanLinq

namespace TQ

abbrev CustomersS : Schema :=
  [("Id", .long), ("Age", .int), ("Name", .string), ("IsActive", .bool)]
def customers : Table "customers" CustomersS := ⟨⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .decimal),
   ("CreatedDate", .dateTime), ("UniqueId", .guid)]
def products : Table "products" ProductsS := ⟨⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table "orders" OrdersS := ⟨⟩

/-- The test context: what the seed database provides. Queries are defined
polymorphically over any context with the tables they use; the registry
instantiates them here. -/
abbrev TestCtx : Ctx := {
  tables := [("customers", CustomersS), ("products", ProductsS), ("orders", OrdersS)]
  params := [("minAge", .int), ("maxAge", .int), ("customerName", .string),
             ("isAdult", .bool), ("isActive", .bool), ("minPrice", .decimal),
             ("startDate", .dateTime), ("targetId", .guid)] }

/-- Test values for user-named parameters, aligned with the seed data —
the typed bindings the evaluator reads (`SqlType.interp` conventions:
milli-unit decimals, normalized date-times, lower-case guids). -/
def seedParams : ParamEnv TestCtx.params :=
  .cons (some 18) <| .cons (some 65) <| .cons (some "John Doe") <|
  .cons (some true) <| .cons (some true) <| .cons (some 100000) <|
  .cons (some "2023-01-01 00:00:00") <|
  .cons (some "11111111-1111-1111-1111-111111111111") .nil

/-- The same values as SQL literal sources, for the integration runner's
execution-only parameter inlining. -/
def bindings : List (String × SqlValue) := [
  ("minAge", .int 18), ("maxAge", .int 65),
  ("customerName", .string "John Doe"),
  ("isAdult", .bool true), ("isActive", .bool true),
  ("minPrice", .decimal "100.00"),
  ("startDate", .dateTime "2023-01-01"),
  ("targetId", .guid "11111111-1111-1111-1111-111111111111")
]

/-! ## Rendering evaluated rows (the harness's normalized cell format) -/

def renderCell : (t : SqlType) → Option t.interp → String
  | _, none => "NULL"
  | .int, some i => toString i
  | .long, some i => toString i
  | .double, some f => toString f
  | .decimal, some m => renderDecimal m
  | .string, some s => s
  | .bool, some b => if b then "1" else "0"
  | .dateTime, some s => s
  | .guid, some g => g

def cellsOf : {s : Schema} → Values s → List String
  | _, .nil => []
  | _, .cons (t := t) c r => renderCell t c :: cellsOf r

/-- Rows to one comparable line: cells comma-joined, rows pipe-joined;
unordered results are compared after a lexicographic sort, mirroring the
harness's engine-output normalization. -/
def renderRows (ordered : Bool) (rows : List (List String)) : String :=
  let rows := rows.map (String.intercalate ",")
  let rows := if ordered then rows else rows.mergeSort (fun a b => a ≤ b)
  String.intercalate "|" rows

/-- `≤` on the first cell (the tests' `Id` column) — statement verification
order. -/
def firstCellLe : {s : Schema} → Values s → Values s → Bool
  | _, .nil, .nil => true
  | _, .cons (t := t) a _, .cons b _ => cellCmp t a b != .gt

/-- A table's rows ordered by first column — mirrors the harness's
statement-verification `SELECT * FROM t ORDER BY Id`. -/
def renderTableRows (rows : List (Values s)) : String :=
  renderRows true ((rows.mergeSort firstCellLe).map cellsOf)

/-- Does the compiled statement carry an ORDER BY clause? Same sniff the
integration harness applies to engine output. -/
def sniffOrdered (c : CompiledSql) : Bool := (c.sql.splitOn " ORDER BY ").length > 1

/-! ## Registry entries -/

/-- A registered test case: how it compiles, and what rows it must produce —
the latter computed by the evaluator over the typed seed database. -/
structure Case where
  compile : DatabaseType → CompiledSql
  expected : TableEnv TestCtx.tables → String
  ordered : Bool

/-- Register a query. -/
def q (query : Query TestCtx s) : Case :=
  let ordered := sniffOrdered (query.toSql .sqlite)
  { compile := fun db => query.toSql db
    expected := fun env => renderRows ordered ((query.run env seedParams).map cellsOf)
    ordered }

/-- Register a scalar aggregate query: one row, one cell. -/
def sq (sc : ScalarQuery TestCtx t) : Case :=
  { compile := fun db => sc.toSql db
    expected := fun env => renderCell t (sc.run env seedParams)
    ordered := false }

end TQ
