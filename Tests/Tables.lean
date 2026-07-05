import LeanLinq

/-! Test models — the classic customers / products / orders trio — and the
`Case` registry entry: per-dialect compilation *plus* expected result rows
computed by the evaluator (`Query.run`) over a seed database. The expected
side is derived from the same query value that compiles to SQL, so every
registered case is checked against the executable semantics with no
hand-written expectations. -/

open LeanLinq

namespace TQ

abbrev CustomersS : Schema :=
  [("Id", .long), ("Age", .int), ("Name", .string), ("IsActive", .bool)]
def customers : Table CustomersS := ⟨"customers"⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .decimal),
   ("CreatedDate", .dateTime), ("UniqueId", .guid)]
def products : Table ProductsS := ⟨"products"⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table OrdersS := ⟨"orders"⟩

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

/-- A table's current rows, ordered by first column — mirrors the harness's
statement-verification `SELECT * FROM t ORDER BY Id`. -/
def renderTable (db : Db) (tname : String) (s : Schema) : String :=
  renderRows true (((db.rowsOf tname s).mergeSort firstCellLe).map cellsOf)

/-- Does the compiled statement carry an ORDER BY clause? Same sniff the
integration harness applies to engine output. -/
def sniffOrdered (c : CompiledSql) : Bool := (c.sql.splitOn " ORDER BY ").length > 1

/-! ## Registry entries -/

/-- A registered test case: how it compiles, and what rows it must produce —
the latter computed by the evaluator over a seed `Db`. -/
structure Case where
  compile : DatabaseType → CompiledSql
  expected : Db → String
  ordered : Bool

/-- Register a query. -/
def q (query : Query s) : Case :=
  let ordered := sniffOrdered (query.toSql .sqlite)
  { compile := fun db => query.toSql db
    expected := fun db => renderRows ordered ((query.run db).map cellsOf)
    ordered }

/-- Register a scalar aggregate query: one row, one cell. -/
def sq (sc : ScalarQuery t) : Case :=
  { compile := fun db => sc.toSql db
    expected := fun db => renderCell t (sc.evalCell db)
    ordered := false }

end TQ
