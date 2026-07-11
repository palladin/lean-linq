import LeanLinq.Core.Types

/-! # Runtime values

The value side of the staged language: what a column *holds* when a query is
evaluated in memory (`Query.run`), as opposed to the expression it is staged
as (`SqlExpr`). Sits below `Core/Monad` so `SubQuery` can carry an evaluation
action alongside its compilation action.

Semantics choices (documented, engine-checked by the integration suite):
decimals are exact fixed-point milli-units (three fractional digits, the
scale exercised by DECIMAL(18,2) columns); date-times are normalized
`YYYY-MM-DD HH:MM:SS` strings with civil-calendar arithmetic; guids are
lower-cased; NULL is `Option.none` everywhere. -/

namespace LeanLinq

/-- The Lean type carried by each SQL type at evaluation time. -/
@[reducible] def SqlType.interp : SqlType → Type
  | .int => Int
  | .long => Int
  | .double => Float
  | .decimal => Int          -- milli-units: 999.99 = 999990
  | .string => String
  | .bool => Bool
  | .dateTime => String      -- "YYYY-MM-DD HH:MM:SS"
  | .guid => String          -- lower-case

/-- A nullable runtime value of SQL type `t` — what a column cell, an
evaluated expression, or a parameter binding holds. `none` is SQL NULL and
*only* NULL: resolution failures don't exist (`HasCol`/`HasTable`/`HasParam`
eliminated them), and exceptional conditions are a separate, explicit
channel (`EvalError`). -/
abbrev Nullable (t : SqlType) : Type := Option t.interp

/-- What a **cell** of this column holds: NULL-capable columns store
`Option`, NOT NULL columns store the payload directly — the honest type
(`s.get "Name" : String` when the schema says so). -/
@[reducible] def SqlCol.interp : SqlCol → Type
  | ⟨t, true⟩ => Option t.interp
  | ⟨t, false⟩ => t.interp

/-- Lift a cell to the uniform `Nullable` view (the evaluator's internal
currency): a strict cell is `some`, a nullable cell is itself. -/
@[reducible] def SqlCol.toNullable : {c : SqlCol} → c.interp → Nullable c.ty
  | ⟨_, true⟩, cell => cell
  | ⟨_, false⟩, cell => some cell

/-- Exceptional conditions during evaluation — the statement-aborting
channel, kept separate from SQL NULL (engines abort on these; they do not
produce NULL cells). `internal` marks states unreachable for queries built
through the public surface. -/
inductive EvalError where
  | divByZero
  | noClock                              -- `now` evaluated without a clock in `EvalEnv`
  | unsupported (fn : String) (t : SqlType)   -- e.g. ROUND on double: not implemented
  | internal (msg : String)
  deriving Repr, BEq

/-- Store a `Nullable` computation result into a cell of this column:
`none` into a NOT NULL column is the loud boundary error (a bug or a
missing INSERT value), never a silent NULL. -/
def SqlCol.ofNullable (name : String) :
    (c : SqlCol) → Nullable c.ty → Except EvalError c.interp
  | ⟨_, true⟩, v => .ok v
  | ⟨_, false⟩, some x => .ok x
  | ⟨_, false⟩, none => .error (.internal s!"NULL in NOT NULL column {name}")

/-- A heterogeneous tuple of runtime cells indexed by a schema — the
value-level mirror of `Row`. Each cell's type is honest to its column:
`Option` only where the column is NULL-capable. -/
inductive Values : List (String × SqlCol) → Type where
  | nil : Values []
  | cons : {name : String} → {c : SqlCol} → {s : List (String × SqlCol)} →
      c.interp → Values s → Values ((name, c) :: s)

/-- The all-NULL row over the NULL-lifted schema (LEFT JOIN padding) —
constructible only because `asNull` makes every column NULL-capable. -/
def Values.nulls : (s : Schema) → Values s.asNull
  | [] => .nil
  | (_, _) :: s => .cons (c := ⟨_, true⟩) none (Values.nulls s)

/-! ## Comparing cells

`cmpV` is the total order used for ORDER BY, MIN/MAX, and grouping keys;
`cellCmp` extends it with SQL's NULL placement (NULL sorts smallest). -/

def SqlType.cmpV : (t : SqlType) → t.interp → t.interp → Ordering
  | .int, a, b => compare a b
  | .long, a, b => compare a b
  | .double, a, b => if a < b then .lt else if b < a then .gt else .eq
  | .decimal, a, b => compare a b
  | .string, a, b => compare a b
  | .bool, a, b =>
      match a, b with
      | false, true => .lt
      | true, false => .gt
      | _, _ => .eq
  | .dateTime, a, b => compare a b
  | .guid, a, b => compare a b

def cellCmp (t : SqlType) : Nullable t → Nullable t → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b => t.cmpV a b

def cellBeq (t : SqlType) (a b : Nullable t) : Bool := cellCmp t a b == .eq

def Values.beq : {s : List (String × SqlCol)} → Values s → Values s → Bool
  | _, .nil, .nil => true
  | _, .cons (c := c) a r, .cons b r' => cellBeq c.ty (SqlCol.toNullable a) (SqlCol.toNullable b) && r.beq r'

instance : BEq (Values s) := ⟨Values.beq⟩

/-- A runtime cell packed with its type (order keys, grouping keys). -/
structure AnyCell where
  type : SqlType
  val : Nullable type

def AnyCell.cmp : AnyCell → AnyCell → Ordering
  | ⟨ta, va⟩, ⟨tb, vb⟩ =>
    if h : tb = ta then cellCmp ta va (h ▸ vb)
    else .lt   -- distinct types never meet: keys compare within one column

instance : BEq AnyCell := ⟨fun a b => a.cmp b == .eq⟩

/-! ## Rows in scope, typed databases -/

/-- Cell lookup by column name and expected type (mirrors `HasCol`, but at
run time). The outer `Option` is *presence* (absent column / type mismatch —
unreachable for schema-checked queries), the inner `Nullable` is SQL NULL;
the two are never conflated. -/
def Values.get? : {s : Schema} → Values s →
    (name : String) → (t : SqlType) → Option (Nullable t)
  | _, .nil, _, _ => none
  | _, .cons (name := n') (c := c') cell r, name, t =>
      if n' == name then
        (if h : c'.ty = t then some (h ▸ SqlCol.toNullable cell) else none)
      else r.get? name t

/-- `HasCell s name c` resolves a column name against the schema for
*value* rows, by the same literal-list instance search as `HasCol` — a
misspelled column on fetched data fails at compile time, and the cell type
is honest to the column's declared nullability. -/
class HasCell (s : Schema) (name : String) (c : outParam SqlCol) where
  get : Values s → c.interp

instance (priority := high) : HasCell ((name, c) :: s) name c where
  get | .cons cell _ => cell

instance [i : HasCell s name c] : HasCell ((n', c') :: s) name c where
  get | .cons _ v => i.get v

/-- Typed cell access on a fetched row: `v.get "Name"` — a `String` when
the schema says NOT NULL, an `Option String` when it says `.null`
(contrast `get?`, the runtime string lookup). -/
def Values.get (v : Values s) (name : String) [i : HasCell s name c] :
    c.interp :=
  i.get v

/-- The rows in scope during evaluation: source alias → its current value
row (the value-level counterpart of the compiler's `Row.ofAlias` field
markers). -/
abbrev Scope := List (String × ((s : Schema) × Values s))

def Scope.get? (sc : Scope) (alias name : String) (t : SqlType) : Option (Nullable t) := do
  let ⟨_, v⟩ ← sc.lookup alias
  v.get? name t

/-- A typed database: one row-list per table entry of the context. A query
typed against `c` evaluates against any `TableEnv c.tables` — resolution
happened at elaboration (`HasTable`), so there is no name lookup, no schema
check, and no failure mode at run time. -/
inductive TableEnv : List (String × Schema) → Type where
  | nil : TableEnv []
  | cons : {n : String} → {s : Schema} → {ts : List (String × Schema)} →
      List (Values s) → TableEnv ts → TableEnv ((n, s) :: ts)

/-- Typed parameter bindings: one (nullable) value per parameter entry of
the context — the `TableEnv` of parameters. -/
inductive ParamEnv : List (String × SqlCol) → Type where
  | nil : ParamEnv []
  | cons : {n : String} → {c : SqlCol} → {ps : List (String × SqlCol)} →
      c.interp → ParamEnv ps → ParamEnv ((n, c) :: ps)

/-- Membership of a named parameter in the context's parameter list, by
instance search — the `HasCol`/`HasTable` idiom once more. The evidence *is*
the accessor: resolving a parameter at elaboration time means already
knowing how to read its value from any `ParamEnv ps`, so an unbound
parameter is untypeable rather than silently NULL. -/
class HasParam (ps : List (String × SqlCol)) (n : String) (c : outParam SqlCol) where
  get : ParamEnv ps → c.interp

instance (priority := high) : HasParam ((n, c) :: ps) n c where
  get | .cons v _ => v

instance [h : HasParam ps n c] : HasParam ((n', c') :: ps) n c where
  get | .cons _ env => h.get env

/-- Names zipped with typed cells — what a driver walks to bind the
user-named parameters natively. -/
def ParamEnv.toCells : {ps : List (String × SqlCol)} → ParamEnv ps →
    List (String × ((t : SqlType) × Nullable t))
  | _, .nil => []
  | _, .cons (n := n) (c := c) v rest =>
      (n, ⟨c.ty, SqlCol.toNullable v⟩) :: rest.toCells

/-- Everything evaluation reads besides the query itself: the typed tables,
the typed parameter bindings, and the (optional) current timestamp. -/
structure EvalEnv (c : Ctx) where
  tables : TableEnv c.tables
  params : ParamEnv c.params
  now : Option String := none

/-! ## Decimals: exact milli-units (scale 3) -/

/-- Parse exact decimal digits into milli-units: `"999.99" → 999990`.
Fractional digits beyond the third are truncated. -/
def parseDecimal (digits : String) : Int :=
  let cs := digits.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let num (l : List Char) : Nat := ((String.ofList l).toNat?).getD 0
  let w := cs.takeWhile (· != '.')
  let f := (cs.dropWhile (· != '.')).drop 1
  let v : Int := num w * 1000 + num ((f ++ ['0', '0', '0']).take 3)
  if neg then -v else v

/-- Render milli-units with trailing zeros trimmed: `999990 → "999.99"`,
`25500 → "25.5"`, `1099989 → "1099.989"`, `1000000 → "1000"`. -/
def renderDecimal (millis : Int) : String :=
  let v := millis.natAbs
  let whole := v / 1000
  let frac := v % 1000
  let body :=
    if frac == 0 then s!"{whole}"
    else if frac % 100 == 0 then s!"{whole}.{frac / 100}"
    else if frac % 10 == 0 then
      let f2 := frac / 10
      s!"{whole}." ++ (if f2 < 10 then s!"0{f2}" else s!"{f2}")
    else
      s!"{whole}." ++ (if frac < 10 then s!"00{frac}" else if frac < 100 then s!"0{frac}" else s!"{frac}")
  if millis < 0 then s!"-{body}" else body

def decimalRound (digits : Nat) (millis : Int) : Int :=
  let unit : Int := if digits == 0 then 1000 else if digits == 1 then 100 else if digits == 2 then 10 else 1
  ((millis + unit / 2) / unit) * unit

def decimalCeil (millis : Int) : Int := ((millis + 999) / 1000) * 1000

def decimalFloor (millis : Int) : Int := (millis / 1000) * 1000

/-! ## Civil-date arithmetic (`YYYY-MM-DD[ HH:MM:SS]` strings) -/

/-- Normalize a date-time string: date-only forms gain a midnight time, so
comparisons against stored column values are exact. -/
def normDateTime (s : String) : String :=
  if s.length == 10 then s ++ " 00:00:00"
  else String.ofList ((s.toList.take 19).map fun c => if c == 'T' then ' ' else c)

def parseYMD (s : String) : Int × Int × Int :=
  let cs := s.toList
  let num (l : List Char) : Int := ((String.ofList l).toNat?).getD 0
  (num (cs.take 4), num ((cs.drop 5).take 2), num ((cs.drop 8).take 2))

def daysFromCivil (ymd : Int × Int × Int) : Int :=
  let (y, m, d) := ymd
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := mp + (if mp < 10 then 3 else -9)
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

private def pad2 (n : Int) : String := if n < 10 then s!"0{n}" else s!"{n}"

def fmtDateTime (ymd : Int × Int × Int) : String :=
  s!"{ymd.1}-{pad2 ymd.2.1}-{pad2 ymd.2.2} 00:00:00"

def dateAddDays (s : String) (n : Int) : String :=
  fmtDateTime (civilFromDays (daysFromCivil (parseYMD s) + n))

def dateAddMonths (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  let t := y * 12 + (m - 1) + n
  fmtDateTime (t / 12, t % 12 + 1, d)

def dateAddYears (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  fmtDateTime (y + n, m, d)

def dateDiffDays (a b : String) : Int := daysFromCivil (parseYMD b) - daysFromCivil (parseYMD a)

def dateDiffMonths (a b : String) : Int :=
  let (ya, ma, _) := parseYMD a; let (yb, mb, _) := parseYMD b
  (yb - ya) * 12 + (mb - ma)

def dateDiffYears (a b : String) : Int := (parseYMD b).1 - (parseYMD a).1

/-! ## String functions -/

/-- SQL `LIKE` (`%` any run, `_` any char). -/
def likeMatch (s pat : String) : Bool := go pat.toList s.toList
where
  go : List Char → List Char → Bool
    | [], cs => cs.isEmpty
    | '%' :: ps, cs =>
        go ps cs || (match cs with
          | [] => false
          | _ :: cs' => go ('%' :: ps) cs')
    | '_' :: ps, _ :: cs => go ps cs
    | p :: ps, c :: cs => p == c && go ps cs
    | _ :: _, [] => false
  termination_by ps cs => (cs.length, ps.length)

/-- SQL SUBSTRING: 1-based start. -/
def sqlSubstring (s : String) (start len : Int) : String :=
  String.ofList ((s.toList.drop (start - 1).toNat).take len.toNat)

/-! ## Parameter values -/

/-! ## Display -/

private def cellRepr : (t : SqlType) → Nullable t → String
  | _, none => "NULL"
  | .int, some i => toString i
  | .long, some i => toString i
  | .double, some f => toString f
  | .decimal, some m => renderDecimal m
  | .string, some s => s.quote
  | .bool, some b => toString b
  | .dateTime, some s => s.quote
  | .guid, some g => g.quote

private def Values.reprCells : {s : List (String × SqlCol)} → Values s → List String
  | _, .nil => []
  | _, .cons (c := c) cell r =>
      cellRepr c.ty (SqlCol.toNullable cell) :: r.reprCells

instance : Repr (Values s) :=
  ⟨fun v _ => .text ("(" ++ String.intercalate ", " v.reprCells ++ ")")⟩

end LeanLinq
