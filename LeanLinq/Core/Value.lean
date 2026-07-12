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
@[reducible] def SqlPrim.interp : SqlPrim → Type
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
abbrev Nullable (t : SqlPrim) : Type := Option t.interp

/-- What a **cell** of this column holds: NULL-capable columns store
`Option`, NOT NULL columns store the payload directly — the honest type
(`s.get "Name" : String` when the schema says so). -/
@[reducible] def SqlType.interp : SqlType → Type
  | ⟨t, true⟩ => Option t.interp
  | ⟨t, false⟩ => t.interp

/-- Lift a cell to the uniform `Nullable` view (the evaluator's internal
currency): a strict cell is `some`, a nullable cell is itself. -/
@[reducible] def SqlType.toNullable : {c : SqlType} → c.interp → Nullable c.ty
  | ⟨_, true⟩, cell => cell
  | ⟨_, false⟩, cell => some cell

/-- Exceptional conditions during evaluation — the statement-aborting
channel, kept separate from SQL NULL (engines abort on these; they do not
produce NULL cells). `internal` marks states unreachable for queries built
through the public surface. -/
inductive EvalError where
  | divByZero
  | noClock                              -- `now` evaluated without a clock in `EvalEnv`
  | unsupported (fn : String) (t : SqlPrim)   -- e.g. ROUND on double: not implemented
  | invalidStatement (msg : String)           -- e.g. INSERT with no columns: every engine rejects it
  | internal (msg : String)
  deriving Repr, BEq

/-- Store a `Nullable` computation result into a cell of this column:
`none` into a NOT NULL column is the loud boundary error (a bug or a
missing INSERT value), never a silent NULL. -/
def SqlType.ofNullable (name : String) :
    (c : SqlType) → Nullable c.ty → Except EvalError c.interp
  | ⟨_, true⟩, v => .ok v
  | ⟨_, false⟩, some x => .ok x
  | ⟨_, false⟩, none => .error (.internal s!"NULL in NOT NULL column {name}")

/-- A heterogeneous tuple of runtime cells indexed by a schema — the
value-level mirror of `Row`. Each cell's type is honest to its column:
`Option` only where the column is NULL-capable. -/
inductive Values : List (String × SqlType) → Type where
  | nil : Values []
  | cons : {name : String} → {c : SqlType} → {s : List (String × SqlType)} →
      c.interp → Values s → Values ((name, c) :: s)

/-- The all-NULL row over the NULL-lifted schema (LEFT JOIN padding) —
constructible only because `asNull` makes every column NULL-capable. -/
def Values.nulls : (s : Schema) → Values s.asNull
  | [] => .nil
  | (_, _) :: s => .cons (c := ⟨_, true⟩) none (Values.nulls s)

/-! ## Comparing cells

`cmpV` is the total order used for ORDER BY, MIN/MAX, and grouping keys;
`cellCmp` extends it with SQL's NULL placement (NULL sorts smallest). -/

def SqlPrim.cmpV : (t : SqlPrim) → t.interp → t.interp → Ordering
  | .int, a, b => compare a b
  | .long, a, b => compare a b
  | .double, a, b =>
      -- NaN: equal to itself, greater than everything else (the
      -- PostgreSQL total order) — never silently `.eq` to a number
      if a.isNaN || b.isNaN then
        if a.isNaN && b.isNaN then .eq else if a.isNaN then .gt else .lt
      else if a < b then .lt else if b < a then .gt else .eq
  | .decimal, a, b => compare a b
  | .string, a, b => compare a b
  | .bool, a, b =>
      match a, b with
      | false, true => .lt
      | true, false => .gt
      | _, _ => .eq
  | .dateTime, a, b => compare a b
  | .guid, a, b => compare a b

def cellCmp (t : SqlPrim) : Nullable t → Nullable t → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b => t.cmpV a b

def cellBeq (t : SqlPrim) (a b : Nullable t) : Bool := cellCmp t a b == .eq

def Values.beq : {s : List (String × SqlType)} → Values s → Values s → Bool
  | _, .nil, .nil => true
  | _, .cons (c := c) a r, .cons b r' => cellBeq c.ty (SqlType.toNullable a) (SqlType.toNullable b) && r.beq r'

/-- No two rows equal under `Values.beq` (SQL's DISTINCT notion: NULLs
compare equal). Quadratic — a client-side audit of result sets, not a
query plan. -/
def Values.nodupB : List (Values s) → Bool
  | [] => true
  | v :: vs => vs.all (fun w => !(Values.beq v w)) && Values.nodupB vs

/-- First-occurrence deduplication by an explicit equality — the shape
`List.eraseDups` computes, in a structural recursion the soundness
theorems can induct over (each step keeps the head and filters its
duplicates out of the tail). -/
def List.dedupBy (eq : α → α → Bool) : List α → List α
  | [] => []
  | v :: vs => v :: List.dedupBy eq (vs.filter (fun w => !eq v w))
termination_by l => l.length
decreasing_by
  simp only [List.length_unattach]
  exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-- Deduplication keeps a subsequence of the input (first occurrences,
in order). -/
theorem List.dedupBy_sublist (eq : α → α → Bool) :
    (l : List α) → (List.dedupBy eq l).Sublist l
  | [] => by rw [List.dedupBy]; exact .slnil
  | v :: vs => by
      rw [List.dedupBy]
      exact ((List.dedupBy_sublist eq _).trans List.filter_sublist).cons_cons v
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem List.length_dedupBy_le (eq : α → α → Bool) (l : List α) :
    (List.dedupBy eq l).length ≤ l.length :=
  (List.dedupBy_sublist eq l).length_le

/-- `Bool.all` transfers along sublists. -/
theorem List.all_of_sublist {l' l : List α} {p : α → Bool}
    (h : List.Sublist l' l)
    (ha : l.all p = true) : l'.all p = true := by
  simp only [List.all_eq_true] at ha ⊢
  exact fun x hx => ha x (h.subset hx)

/-- `nodupB` is sublist-closed — the property every `RowInv` conjunct
must have. -/
theorem Values.nodupB_of_sublist {s : Schema} {xs' xs : List (Values s)}
    (h : List.Sublist xs' xs) (hn : Values.nodupB xs = true) :
    Values.nodupB xs' = true := by
  induction h with
  | slnil => rfl
  | cons y h ih =>
      rw [Values.nodupB, Bool.and_eq_true] at hn
      exact ih hn.2
  | cons_cons y h ih =>
      rw [Values.nodupB, Bool.and_eq_true] at hn ⊢
      exact ⟨List.all_of_sublist h hn.1, ih hn.2⟩

/-- Deduplication delivers `nodupB` — the fact `DISTINCT` promises. -/
theorem Values.nodupB_dedupBy {s : Schema} :
    (l : List (Values s)) → Values.nodupB (List.dedupBy Values.beq l) = true
  | [] => by rw [List.dedupBy]; rfl
  | v :: vs => by
      rw [List.dedupBy, Values.nodupB, Bool.and_eq_true]
      refine ⟨?_, Values.nodupB_dedupBy _⟩
      simp only [List.all_eq_true]
      intro w hw
      have hmem := (List.dedupBy_sublist Values.beq _).subset hw
      simpa using (List.mem_filter.mp hmem).2
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

instance : BEq (Values s) := ⟨Values.beq⟩

/-- A runtime cell packed with its type (order keys, grouping keys). -/
structure AnyCell where
  type : SqlPrim
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
    (name : String) → (t : SqlPrim) → Option (Nullable t)
  | _, .nil, _, _ => none
  | _, .cons (name := n') (c := c') cell r, name, t =>
      if n' == name then
        (if h : c'.ty = t then some (h ▸ SqlType.toNullable cell) else none)
      else r.get? name t

/-- `HasCell s name c` resolves a column name against the schema for
*value* rows, by the same literal-list instance search as `HasCol` — a
misspelled column on fetched data fails at compile time, and the cell type
is honest to the column's declared nullability. -/
class HasCell (s : Schema) (name : String) (c : outParam SqlType) where
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

def Scope.get? (sc : Scope) (alias name : String) (t : SqlPrim) : Option (Nullable t) := do
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
inductive ParamEnv : List (String × SqlType) → Type where
  | nil : ParamEnv []
  | cons : {n : String} → {c : SqlType} → {ps : List (String × SqlType)} →
      c.interp → ParamEnv ps → ParamEnv ((n, c) :: ps)

/-- Membership of a named parameter in the context's parameter list, by
instance search — the `HasCol`/`HasTable` idiom once more. The evidence *is*
the accessor: resolving a parameter at elaboration time means already
knowing how to read its value from any `ParamEnv ps`, so an unbound
parameter is untypeable rather than silently NULL. -/
class HasParam (ps : List (String × SqlType)) (n : String) (c : outParam SqlType) where
  get : ParamEnv ps → c.interp

instance (priority := high) : HasParam ((n, c) :: ps) n c where
  get | .cons v _ => v

instance [h : HasParam ps n c] : HasParam ((n', c') :: ps) n c where
  get | .cons _ env => h.get env

/-- Names zipped with typed cells — what a driver walks to bind the
user-named parameters natively. -/
def ParamEnv.toCells : {ps : List (String × SqlType)} → ParamEnv ps →
    List (String × ((t : SqlPrim) × Nullable t))
  | _, .nil => []
  | _, .cons (n := n) (c := c) v rest =>
      (n, ⟨c.ty, SqlType.toNullable v⟩) :: rest.toCells

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

/-- ROUND half *away from zero* (all three engines): `-1.5 → -2`. -/
def decimalRound (digits : Nat) (millis : Int) : Int :=
  let unit : Int := if digits == 0 then 1000 else if digits == 1 then 100 else if digits == 2 then 10 else 1
  if millis ≥ 0 then ((millis + unit / 2).tdiv unit) * unit
  else ((millis - unit / 2).tdiv unit) * unit

-- ceil/floor deliberately use Euclidean `/`: its floor direction on
-- negatives is exactly what CEILING/FLOOR need — do not "fix" to tdiv
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

/-- The time-of-day part of a normalized date-time (midnight for
date-only strings) — date arithmetic preserves it, as engines do. -/
def timeOfDay (s : String) : String :=
  if s.length ≥ 19 then ((s.drop 11).take 8).toString else "00:00:00"

def fmtDateTime (ymd : Int × Int × Int) (time : String := "00:00:00") : String :=
  s!"{ymd.1}-{pad2 ymd.2.1}-{pad2 ymd.2.2} {time}"

def isLeapYear (y : Int) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Int) : Int :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else 31

def dateAddDays (s : String) (n : Int) : String :=
  fmtDateTime (civilFromDays (daysFromCivil (parseYMD s) + n)) (timeOfDay s)

/-- Month arithmetic clamps to the target month's last day
(`2020-01-31 + 1 month = 2020-02-29`), the PostgreSQL/SQL Server
behavior; SQLite instead rolls the overflow into the next month. -/
def dateAddMonths (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  let t := y * 12 + (m - 1) + n
  let (y', m') := (t / 12, t % 12 + 1)
  fmtDateTime (y', m', min d (daysInMonth y' m')) (timeOfDay s)

def dateAddYears (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  fmtDateTime (y + n, m, min d (daysInMonth (y + n) m)) (timeOfDay s)

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

/-! ## Display -/

private def cellRepr : (t : SqlPrim) → Nullable t → String
  | _, none => "NULL"
  | .int, some i => toString i
  | .long, some i => toString i
  | .double, some f => toString f
  | .decimal, some m => renderDecimal m
  | .string, some s => s.quote
  | .bool, some b => toString b
  | .dateTime, some s => s.quote
  | .guid, some g => g.quote

private def Values.reprCells : {s : List (String × SqlType)} → Values s → List String
  | _, .nil => []
  | _, .cons (c := c) cell r =>
      cellRepr c.ty (SqlType.toNullable cell) :: r.reprCells

instance : Repr (Values s) :=
  ⟨fun v _ => .text ("(" ++ String.intercalate ", " v.reprCells ++ ")")⟩

end LeanLinq
