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

/-- Intrinsically-typed SQL expressions: `SqlExpr ts t` can only be built
from operations valid for `t`, so ill-typed SQL is unrepresentable. The
first index is the ambient *table context* — fixed across a whole query — so
the tables referenced by any embedded subquery are `HasTable`-checked
against the same context as the query it appears in. Numeric operators are
constrained at the notation layer (`Add`/`Sub`/… instances for the numeric
types only); the raw constructors are internal.

Subqueries (`inSub`/`scalarSub`) are stored as staged `SubQuery` actions,
not ASTs — see `SubQuery` for the positivity story. Construct them with
`SqlExpr.inQuery`/`ScalarQuery.embed` (defined with the compiler). -/
inductive SqlExpr : Ctx → SqlType → Type where
  -- literals (compiled to auto-named parameters, never inlined)
  | intC (i : Int) : SqlExpr ts .int
  | longC (i : Int) : SqlExpr ts .long
  | doubleC (f : Float) : SqlExpr ts .double
  | decimalC (digits : String) : SqlExpr ts .decimal
  | stringC (s : String) : SqlExpr ts .string
  | boolC (b : Bool) : SqlExpr ts .bool
  | dateTimeC (iso : String) : SqlExpr ts .dateTime
  | guidC (g : String) : SqlExpr ts .guid
  | nullC (t : SqlType) : SqlExpr ts t
  -- user-named parameter: membership in the context's parameter list is
  -- established here (`HasParam`) and the resolved accessor is stored in
  -- the node — an unbound parameter is untypeable, and its type comes from
  -- the context rather than an annotation
  | param (name : String) {t : SqlType} [inst : HasParam ts.params name t] : SqlExpr ts t
  -- column reference (empty alias renders as a bare column name)
  | field (t : SqlType) (alias name : String) : SqlExpr ts t
  -- operators
  | arith (op : ArithOp) : SqlExpr ts t → SqlExpr ts t → SqlExpr ts t
  | concat : SqlExpr ts .string → SqlExpr ts .string → SqlExpr ts .string
  | cmp (op : CmpOp) : SqlExpr ts t → SqlExpr ts t → SqlExpr ts .bool
  | and : SqlExpr ts .bool → SqlExpr ts .bool → SqlExpr ts .bool
  | or : SqlExpr ts .bool → SqlExpr ts .bool → SqlExpr ts .bool
  | not : SqlExpr ts .bool → SqlExpr ts .bool
  | isNull : SqlExpr ts t → SqlExpr ts .bool
  | isNotNull : SqlExpr ts t → SqlExpr ts .bool
  | like : SqlExpr ts .string → SqlExpr ts .string → SqlExpr ts .bool
  -- IN over a value list. Stored as Σ-packed elements because the kernel
  -- rejects nested `List (SqlExpr ts t)` with a local index; the homogeneous
  -- surface is `SqlExpr.inValues`.
  | inList : SqlExpr ts t → List ((u : SqlType) × SqlExpr ts u) → SqlExpr ts .bool
  | inSub : SqlExpr ts t → SubQuery ts t → SqlExpr ts .bool
  | scalarSub : SubQuery ts t → SqlExpr ts t
  | caseWhen : SqlExpr ts .bool → SqlExpr ts t → SqlExpr ts t → SqlExpr ts t
  -- aggregates (meaningful in grouped selects / HAVING / scalar queries)
  | aggE (op : AggOp) : SqlExpr ts t → SqlExpr ts t
  | countAll : SqlExpr ts .int
  -- functions
  | abs : SqlExpr ts t → SqlExpr ts t
  | round : SqlExpr ts t → Int → SqlExpr ts t
  | ceiling : SqlExpr ts t → SqlExpr ts t
  | floor : SqlExpr ts t → SqlExpr ts t
  | substring : SqlExpr ts .string → Int → Int → SqlExpr ts .string
  | upper : SqlExpr ts .string → SqlExpr ts .string
  | lower : SqlExpr ts .string → SqlExpr ts .string
  | trim : SqlExpr ts .string → SqlExpr ts .string
  | length : SqlExpr ts .string → SqlExpr ts .int
  | now : SqlExpr ts .dateTime
  | datePart (u : DateUnit) : SqlExpr ts .dateTime → SqlExpr ts .int
  | dateAdd (u : DateUnit) : SqlExpr ts .dateTime → Int → SqlExpr ts .dateTime
  | dateDiff (u : DateUnit) : SqlExpr ts .dateTime → SqlExpr ts .dateTime → SqlExpr ts .int

instance : Inhabited (SqlExpr ts t) := ⟨.field t "" ""⟩

/-- Explicit literal constructors, for positions where the expected type is
not yet known and coercions cannot fire (e.g. a literal on the left of `==.`). -/
def SqlExpr.int (i : Int) : SqlExpr ts .int := .intC i

/-- Inject a runtime value as a literal expression — the bridge from
fetched data back into queries (`fetchFor`'s `IN (…)` lists, `Values`
cell embedding via `v["col"]`). -/
class SqlLit (t : SqlType) where
  lit : {ts : Ctx} → t.interp → SqlExpr ts t

instance : SqlLit .int := ⟨.intC⟩
instance : SqlLit .long := ⟨.longC⟩
instance : SqlLit .double := ⟨.doubleC⟩
instance : SqlLit .decimal := ⟨fun m => .decimalC (renderDecimal m)⟩
instance : SqlLit .string := ⟨.stringC⟩
instance : SqlLit .bool := ⟨.boolC⟩
instance : SqlLit .dateTime := ⟨.dateTimeC⟩
instance : SqlLit .guid := ⟨.guidC⟩
def SqlExpr.long (i : Int) : SqlExpr ts .long := .longC i
def SqlExpr.dbl (f : Float) : SqlExpr ts .double := .doubleC f
def SqlExpr.dec (digits : String) : SqlExpr ts .decimal := .decimalC digits
def SqlExpr.str (s : String) : SqlExpr ts .string := .stringC s
def SqlExpr.bool (b : Bool) : SqlExpr ts .bool := .boolC b
def SqlExpr.dt (iso : String) : SqlExpr ts .dateTime := .dateTimeC iso
def SqlExpr.gd (g : String) : SqlExpr ts .guid := .guidC g

/-- `e IN (v₁, v₂, …)` over a homogeneous value list. -/
def SqlExpr.inValues (e : SqlExpr ts t) (vs : List (SqlExpr ts t)) : SqlExpr ts .bool :=
  .inList e (vs.map (⟨t, ·⟩))

/-- Date-part / date-arithmetic surface helpers. -/
def SqlExpr.year (e : SqlExpr ts .dateTime) : SqlExpr ts .int := .datePart .year e
def SqlExpr.month (e : SqlExpr ts .dateTime) : SqlExpr ts .int := .datePart .month e
def SqlExpr.day (e : SqlExpr ts .dateTime) : SqlExpr ts .int := .datePart .day e
def SqlExpr.addDays (e : SqlExpr ts .dateTime) (n : Int) : SqlExpr ts .dateTime := .dateAdd .day e n
def SqlExpr.addMonths (e : SqlExpr ts .dateTime) (n : Int) : SqlExpr ts .dateTime := .dateAdd .month e n
def SqlExpr.addYears (e : SqlExpr ts .dateTime) (n : Int) : SqlExpr ts .dateTime := .dateAdd .year e n
def SqlExpr.diffDays (e x : SqlExpr ts .dateTime) : SqlExpr ts .int := .dateDiff .day e x
def SqlExpr.diffMonths (e x : SqlExpr ts .dateTime) : SqlExpr ts .int := .dateDiff .month e x
def SqlExpr.diffYears (e x : SqlExpr ts .dateTime) : SqlExpr ts .int := .dateDiff .year e x

/-- A heterogeneously-typed ORDER BY key with its direction; build with
`e.asc` / `e.desc`. -/
structure OrderKey (ts : Ctx) where
  type : SqlType
  expr : SqlExpr ts type
  dir : Dir

def SqlExpr.asc (e : SqlExpr ts t) : OrderKey ts := ⟨t, e, .asc⟩
def SqlExpr.desc (e : SqlExpr ts t) : OrderKey ts := ⟨t, e, .desc⟩

/-- A heterogeneously-typed GROUP BY key; build with `e.key`. -/
structure KeyExpr (ts : Ctx) where
  type : SqlType
  expr : SqlExpr ts type

def SqlExpr.key (e : SqlExpr ts t) : KeyExpr ts := ⟨t, e⟩

/-- The aggregate builder token passed to grouped `select`/`having` lambdas
(mirrors passing an aggregate-function object in LINQ-style APIs). -/
structure Agg where

def Agg.count (_ : Agg) : SqlExpr ts .int := .countAll
def Agg.sum (_ : Agg) (e : SqlExpr ts t) : SqlExpr ts t := .aggE .sum e
def Agg.avg (_ : Agg) (e : SqlExpr ts t) : SqlExpr ts t := .aggE .avg e
def Agg.min (_ : Agg) (e : SqlExpr ts t) : SqlExpr ts t := .aggE .min e
def Agg.max (_ : Agg) (e : SqlExpr ts t) : SqlExpr ts t := .aggE .max e

end LeanLinq
