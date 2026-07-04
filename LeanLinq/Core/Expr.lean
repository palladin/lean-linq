import LeanLinq.Core.Monad

namespace LeanLinq

inductive ArithOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive AggOp where
  | sum | avg | min | max
  deriving DecidableEq, Repr

inductive DateUnit where
  | day | month | year
  deriving DecidableEq, Repr

inductive JoinKind where
  | inner | left
  deriving DecidableEq, Repr

inductive SetOp where
  | union | intersect | except
  deriving DecidableEq, Repr

/-- Sort direction for ORDER BY keys. -/
inductive Dir where
  | asc | desc
  deriving DecidableEq, Repr

/-- Intrinsically-typed SQL expressions: `SqlExpr t` can only be built from
operations valid for `t`, so ill-typed SQL is unrepresentable. Numeric
operators are constrained at the notation layer (`Add`/`Sub`/… instances for
the numeric types only); the raw constructors are internal.

Subqueries (`inSub`/`scalarSub`) are stored as staged `SubQuery` compilation
actions, not ASTs — see `SubQuery` for the positivity story. Construct them
with `SqlExpr.inQuery`/`ScalarQuery.embed` (defined with the compiler). -/
inductive SqlExpr : SqlType → Type where
  -- literals (compiled to auto-named parameters, never inlined)
  | intC (i : Int) : SqlExpr .int
  | longC (i : Int) : SqlExpr .long
  | doubleC (f : Float) : SqlExpr .double
  | decimalC (digits : String) : SqlExpr .decimal
  | stringC (s : String) : SqlExpr .string
  | boolC (b : Bool) : SqlExpr .bool
  | dateTimeC (iso : String) : SqlExpr .dateTime
  | guidC (g : String) : SqlExpr .guid
  | nullC (t : SqlType) : SqlExpr t
  -- user-named parameter
  | param (t : SqlType) (name : String) : SqlExpr t
  -- column reference (empty alias renders as a bare column name)
  | field (t : SqlType) (alias name : String) : SqlExpr t
  -- operators
  | arith (op : ArithOp) : SqlExpr t → SqlExpr t → SqlExpr t
  | concat : SqlExpr .string → SqlExpr .string → SqlExpr .string
  | cmp (op : CmpOp) : SqlExpr t → SqlExpr t → SqlExpr .bool
  | and : SqlExpr .bool → SqlExpr .bool → SqlExpr .bool
  | or : SqlExpr .bool → SqlExpr .bool → SqlExpr .bool
  | not : SqlExpr .bool → SqlExpr .bool
  | isNull : SqlExpr t → SqlExpr .bool
  | isNotNull : SqlExpr t → SqlExpr .bool
  | like : SqlExpr .string → SqlExpr .string → SqlExpr .bool
  -- IN over a value list. Stored as Σ-packed elements because the kernel
  -- rejects nested `List (SqlExpr t)` with a local index; the homogeneous
  -- surface is `SqlExpr.inValues`.
  | inList : SqlExpr t → List ((u : SqlType) × SqlExpr u) → SqlExpr .bool
  | inSub : SqlExpr t → SubQuery → SqlExpr .bool
  | scalarSub (t : SqlType) : SubQuery → SqlExpr t
  | caseWhen : SqlExpr .bool → SqlExpr t → SqlExpr t → SqlExpr t
  -- aggregates (meaningful in grouped selects / HAVING / scalar queries)
  | aggE (op : AggOp) : SqlExpr t → SqlExpr t
  | countAll : SqlExpr .int
  -- functions
  | abs : SqlExpr t → SqlExpr t
  | round : SqlExpr t → Int → SqlExpr t
  | ceiling : SqlExpr t → SqlExpr t
  | floor : SqlExpr t → SqlExpr t
  | substring : SqlExpr .string → Int → Int → SqlExpr .string
  | upper : SqlExpr .string → SqlExpr .string
  | lower : SqlExpr .string → SqlExpr .string
  | trim : SqlExpr .string → SqlExpr .string
  | length : SqlExpr .string → SqlExpr .int
  | now : SqlExpr .dateTime
  | datePart (u : DateUnit) : SqlExpr .dateTime → SqlExpr .int
  | dateAdd (u : DateUnit) : SqlExpr .dateTime → Int → SqlExpr .dateTime
  | dateDiff (u : DateUnit) : SqlExpr .dateTime → SqlExpr .dateTime → SqlExpr .int

instance : Inhabited (SqlExpr t) := ⟨.field t "" ""⟩

/-- Explicit literal constructors, for positions where the expected type is
not yet known and coercions cannot fire (e.g. a literal on the left of `==.`). -/
def SqlExpr.int (i : Int) : SqlExpr .int := .intC i
def SqlExpr.long (i : Int) : SqlExpr .long := .longC i
def SqlExpr.dbl (f : Float) : SqlExpr .double := .doubleC f
def SqlExpr.dec (digits : String) : SqlExpr .decimal := .decimalC digits
def SqlExpr.str (s : String) : SqlExpr .string := .stringC s
def SqlExpr.bool (b : Bool) : SqlExpr .bool := .boolC b
def SqlExpr.dt (iso : String) : SqlExpr .dateTime := .dateTimeC iso
def SqlExpr.gd (g : String) : SqlExpr .guid := .guidC g

/-- `e IN (v₁, v₂, …)` over a homogeneous value list. -/
def SqlExpr.inValues (e : SqlExpr t) (vs : List (SqlExpr t)) : SqlExpr .bool :=
  .inList e (vs.map (⟨t, ·⟩))

/-- Date-part / date-arithmetic surface helpers. -/
def SqlExpr.year (e : SqlExpr .dateTime) : SqlExpr .int := .datePart .year e
def SqlExpr.month (e : SqlExpr .dateTime) : SqlExpr .int := .datePart .month e
def SqlExpr.day (e : SqlExpr .dateTime) : SqlExpr .int := .datePart .day e
def SqlExpr.addDays (e : SqlExpr .dateTime) (n : Int) : SqlExpr .dateTime := .dateAdd .day e n
def SqlExpr.addMonths (e : SqlExpr .dateTime) (n : Int) : SqlExpr .dateTime := .dateAdd .month e n
def SqlExpr.addYears (e : SqlExpr .dateTime) (n : Int) : SqlExpr .dateTime := .dateAdd .year e n
def SqlExpr.diffDays (e x : SqlExpr .dateTime) : SqlExpr .int := .dateDiff .day e x
def SqlExpr.diffMonths (e x : SqlExpr .dateTime) : SqlExpr .int := .dateDiff .month e x
def SqlExpr.diffYears (e x : SqlExpr .dateTime) : SqlExpr .int := .dateDiff .year e x

/-- A heterogeneously-typed ORDER BY key with its direction; build with
`e.asc` / `e.desc`. -/
structure OrderKey where
  type : SqlType
  expr : SqlExpr type
  dir : Dir

def SqlExpr.asc (e : SqlExpr t) : OrderKey := ⟨t, e, .asc⟩
def SqlExpr.desc (e : SqlExpr t) : OrderKey := ⟨t, e, .desc⟩

/-- A heterogeneously-typed GROUP BY key; build with `e.key`. -/
structure KeyExpr where
  type : SqlType
  expr : SqlExpr type

def SqlExpr.key (e : SqlExpr t) : KeyExpr := ⟨t, e⟩

/-- The aggregate builder token passed to grouped `select`/`having` lambdas
(mirrors passing an aggregate-function object in LINQ-style APIs). -/
structure Agg where

def Agg.count (_ : Agg) : SqlExpr .int := .countAll
def Agg.sum (_ : Agg) (e : SqlExpr t) : SqlExpr t := .aggE .sum e
def Agg.avg (_ : Agg) (e : SqlExpr t) : SqlExpr t := .aggE .avg e
def Agg.min (_ : Agg) (e : SqlExpr t) : SqlExpr t := .aggE .min e
def Agg.max (_ : Agg) (e : SqlExpr t) : SqlExpr t := .aggE .max e

end LeanLinq
