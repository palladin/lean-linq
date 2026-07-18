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
  [("Id", .long), ("Age", .null .int), ("Name", .null .string),
   ("IsActive", .null .bool)]
def customers : Table "customers" CustomersS := ⟨⟩

abbrev ProductsS : Schema :=
  [("Id", .long), ("ProductName", .string), ("Price", .null .decimal),
   ("CreatedDate", .null .dateTime), ("UniqueId", .null .guid)]
def products : Table "products" ProductsS := ⟨⟩

abbrev OrdersS : Schema :=
  [("Id", .long), ("CustomerId", .long), ("ProductId", .long), ("Amount", .int)]
def orders : Table "orders" OrdersS := ⟨⟩

abbrev MeasurementsS : Schema :=
  [("Id", .long), ("Value", .double), ("Factor", .null .double)]
def measurements : Table "measurements" MeasurementsS := ⟨⟩

/-- The test context: what the seed database provides. Queries are defined
polymorphically over any context with the tables they use; the registry
instantiates them here. -/
abbrev TestCtx : Ctx := {
  tables := [("customers", CustomersS), ("products", ProductsS), ("orders", OrdersS),
             ("measurements", MeasurementsS)]
  params := [("minAge", .int), ("maxAge", .int), ("customerName", .string),
             ("isAdult", .bool), ("isActive", .bool), ("minPrice", .decimal),
             ("startDate", .dateTime), ("targetId", .guid)] }

/-- Test values for user-named parameters, aligned with the seed data —
the typed bindings the evaluator reads (`SqlPrim.interp` conventions:
milli-unit decimals, normalized date-times, lower-case guids). -/
def seedParams : ParamEnv TestCtx.params :=
  .cons 18 <| .cons 65 <| .cons "John Doe" <|
  .cons true <| .cons true <| .cons 100000 <|
  .cons "2023-01-01 00:00:00" <|
  .cons "11111111-1111-1111-1111-111111111111" .nil

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

/-- Canonical float text: `toString (0.5 : Float)` is `"0.500000"`, engines
print `0.5` — trim to the harness's numeric normal form (same rule as the
integration runner's `trimTrailingZeros`). Seed doubles are binary-exact,
so no shortest-round-trip subtleties arise. -/
def renderFloat (f : Float) : String :=
  let s := toString f
  if s.contains '.' then
    let t := (s.toList.reverse.dropWhile (· == '0')).reverse
    let t := if t.getLast? == some '.' then t.dropLast else t
    String.ofList t
  else s

def renderCell : (t : SqlPrim) → Nullable t → String
  | _, none => "NULL"
  | .int, some i => toString i
  | .long, some i => toString i
  | .double, some f => renderFloat f
  | .decimal, some m => renderDecimal m
  | .string, some s => s
  | .bool, some b => if b then "1" else "0"
  | .dateTime, some s => s
  | .guid, some g => g

def cellsOf : {s : Schema} → Values s → List String
  | _, .nil => []
  | _, .cons (c := c) cell r =>
      renderCell c.ty (SqlType.toNullable cell) :: cellsOf r

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
  | _, .cons (c := c) a _, .cons b _ =>
      cellCmp c.ty (SqlType.toNullable a) (SqlType.toNullable b) != .gt

/-- A table's rows ordered by first column — mirrors the harness's
statement-verification `SELECT * FROM t ORDER BY Id`. -/
def renderTableRows (rows : List (Values s)) : String :=
  renderRows true ((rows.mergeSort firstCellLe).map cellsOf)

/-- Does the compiled statement carry an ORDER BY clause? Same sniff the
integration harness applies to engine output. -/
def sniffOrdered (c : CompiledSql) : Bool := (c.sql.splitOn " ORDER BY ").length > 1

/-- Lexicographic row order over all cells — the canonical order for
comparing unordered result sets `Values`-to-`Values`. -/
def rowLe : {s : Schema} → Values s → Values s → Bool
  | _, .nil, .nil => true
  | _, .cons (c := c) a r, .cons b r' =>
      match cellCmp c.ty (SqlType.toNullable a) (SqlType.toNullable b) with
      | .lt => true
      | .gt => false
      | .eq => rowLe r r'

/-! ## Registry entries -/

/-- The typed value behind a registry entry — what the native-driver sweep
executes and compares against the evaluator (the compile/expected closures
erase it). Statement constructors capture their `HasTable` instance, the
same capability pattern as `fromT`. -/
inductive Registered where
  | query {s : Schema} (q : Query TestCtx s)
  | scalar {t : SqlPrim} {n : Bool} (sc : ScalarQuery TestCtx ⟨t, n⟩)
  | ins {n : String} {s : Schema} [inst : HasTable TestCtx.tables n s]
      (i : InsertStmt TestCtx n s)
  | upd {n : String} {s : Schema} [inst : HasTable TestCtx.tables n s]
      (u : UpdateStmt TestCtx n s)
  | del {n : String} {s : Schema} [inst : HasTable TestCtx.tables n s]
      (d : DeleteStmt TestCtx n s)
  | insSel {n : String} {s : Schema} [inst : HasTable TestCtx.tables n s]
      (st : InsertSelectStmt TestCtx n s)

/-- A registered test case: how it compiles, what rows it must produce
(computed by the evaluator over the typed seed database), and the typed
value itself. -/
structure Case where
  compile : DatabaseType → CompiledSql
  expected : TableEnv TestCtx.tables → String
  ordered : Bool
  payload : Registered

/-- Rendered when evaluation aborts (`EvalError`) — never matches engine
output, so it surfaces as a loud mismatch. No registered case errors today;
an engine-divergent condition (e.g. division by zero) would show up here. -/
def evalFailure (e : EvalError) : String := s!"<eval error: {repr e}>"

/-- Register a query. -/
def q (query : Query TestCtx s) : Case :=
  let ordered := sniffOrdered (query.toSql .sqlite)
  { compile := fun db => query.toSql db
    expected := fun env =>
      match query.run env seedParams with
      | .ok rows => renderRows ordered (rows.map cellsOf)
      | .error e => evalFailure e
    ordered
    payload := .query query }

/-- Register a scalar aggregate query: one row, one cell. -/
def sq (sc : ScalarQuery TestCtx ⟨t, n⟩) : Case :=
  { compile := fun db => sc.toSql db
    expected := fun env =>
      match sc.run env seedParams with
      | .ok cell => renderCell t cell
      | .error e => evalFailure e
    ordered := false
    payload := .scalar sc }

end TQ
