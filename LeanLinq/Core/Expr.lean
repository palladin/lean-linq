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

/-- Intrinsically-typed SQL expressions: `SqlExpr ts c` can only be built
from operations valid for the column type `c`, so ill-typed SQL is
unrepresentable — and `c.nullable` tracks **nullability**, flowing by
construction: literals
are never NULL, column references carry their declared flag, operators OR
their operands' flags (SQL's NULL propagation), aggregates may be NULL
(empty group), `isNull` is never NULL. The context index `ts` is fixed
across a whole query, so the tables referenced by any embedded subquery are
`HasTable`-checked against the same context. Numeric operators are
constrained at the notation layer; the raw constructors are internal.

Subqueries (`inSub`/`scalarSub`) are stored as staged `SubQuery` actions,
not ASTs — see `SubQuery` for the positivity story. Construct them with
`SqlExpr.inQuery`/`ScalarQuery.embed` (defined with the compiler). -/
inductive SqlExpr : Ctx → SqlType → Type where
  -- literals (compiled to auto-named parameters, never inlined; never NULL)
  | intC (i : Int) : SqlExpr ts .int
  | longC (i : Int) : SqlExpr ts .long
  | doubleC (f : Float) : SqlExpr ts .double
  | decimalC (digits : String) : SqlExpr ts .decimal
  | stringC (s : String) : SqlExpr ts .string
  | boolC (b : Bool) : SqlExpr ts .bool
  | dateTimeC (iso : String) : SqlExpr ts .dateTime
  | guidC (g : String) : SqlExpr ts .guid
  | nullC (t : SqlPrim) : SqlExpr ts ⟨t, true⟩
  -- user-named parameter: membership in the context's parameter list is
  -- established here (`HasParam`) and the resolved accessor is stored in
  -- the node — an unbound parameter is untypeable, and both its type and
  -- its nullability come from the context declaration
  | paramE (name : String) {pc : SqlType}
      [inst : HasParam ts.params name pc] : SqlExpr ts pc
  -- column reference with its declared nullability (empty alias renders as
  -- a bare column name)
  | field (c : SqlType) (alias name : String) : SqlExpr ts c
  -- the strict→nullable subtyping node (`Coe` inserts it); compiler and
  -- evaluator treat it as identity
  | widen : SqlExpr ts ⟨t, false⟩ → SqlExpr ts ⟨t, true⟩
  -- operators: flags OR (SQL NULL propagation)
  | arith (op : ArithOp) : SqlExpr ts c → SqlExpr ts c → SqlExpr ts c
  -- text/comparison/branch operators take operands at the nullable flag
  -- (strict operands widen via coercion): `String`/`Bool` literals have no
  -- default-instance channel, so a free flag metavariable on an operand
  -- would strand elaboration — conservative-nullable keeps every position
  -- concrete. Numeric `arith` keeps exact OR-flags (numerals default).
  | concat : SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.string, n⟩
  | cmp (op : CmpOp) : SqlExpr ts ⟨t, true⟩ → SqlExpr ts ⟨t, true⟩ → SqlExpr ts ⟨.bool, true⟩
  | and : SqlExpr ts ⟨.bool, n₁⟩ → SqlExpr ts ⟨.bool, n₂⟩ → SqlExpr ts ⟨.bool, n₁ || n₂⟩
  | or : SqlExpr ts ⟨.bool, n₁⟩ → SqlExpr ts ⟨.bool, n₂⟩ → SqlExpr ts ⟨.bool, n₁ || n₂⟩
  | not : SqlExpr ts ⟨.bool, n⟩ → SqlExpr ts ⟨.bool, n⟩
  -- NULL tests accept any operand flag and are themselves never NULL
  | isNull : SqlExpr ts c → SqlExpr ts .bool
  | isNotNull : SqlExpr ts c → SqlExpr ts .bool
  | like : SqlExpr ts ⟨.string, true⟩ → SqlExpr ts ⟨.string, true⟩ → SqlExpr ts ⟨.bool, true⟩
  -- IN over a value list. Stored as Σ-packed elements because the kernel
  -- rejects nested `List (SqlExpr ts t n)` with a local index; the
  -- homogeneous surface is `SqlExpr.inValues`. Conservatively nullable
  -- (element flags are erased by the packing).
  | inList : SqlExpr ts c → List ((p : SqlType) × SqlExpr ts p) →
      SqlExpr ts ⟨.bool, true⟩
  | inSub : SqlExpr ts ⟨t, n⟩ → SubQuery ts t → SqlExpr ts ⟨.bool, true⟩
  -- a scalar subquery may be empty ⇒ NULL
  | scalarSub : SubQuery ts t → SqlExpr ts ⟨t, true⟩
  | caseWhen : SqlExpr ts ⟨.bool, nc⟩ → SqlExpr ts ⟨t, true⟩ → SqlExpr ts ⟨t, true⟩ →
      SqlExpr ts ⟨t, true⟩
  -- aggregates (meaningful in grouped selects / HAVING / scalar queries):
  -- SUM/AVG/MIN/MAX over an empty group are NULL; COUNT never is
  | aggE (op : AggOp) : SqlExpr ts ⟨t, n⟩ → SqlExpr ts ⟨t, true⟩
  | countAll : SqlExpr ts .int
  -- functions: propagate their operands' flags
  | abs : SqlExpr ts c → SqlExpr ts c
  | round : SqlExpr ts c → Int → SqlExpr ts c
  | ceiling : SqlExpr ts c → SqlExpr ts c
  | floor : SqlExpr ts c → SqlExpr ts c
  | substring : SqlExpr ts ⟨.string, n⟩ → Int → Int → SqlExpr ts ⟨.string, n⟩
  | upper : SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.string, n⟩
  | lower : SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.string, n⟩
  | trim : SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.string, n⟩
  | length : SqlExpr ts ⟨.string, n⟩ → SqlExpr ts ⟨.int, n⟩
  | now : SqlExpr ts .dateTime
  | datePart (u : DateUnit) : SqlExpr ts ⟨.dateTime, n⟩ → SqlExpr ts ⟨.int, n⟩
  | dateAdd (u : DateUnit) : SqlExpr ts ⟨.dateTime, n⟩ → Int → SqlExpr ts ⟨.dateTime, n⟩
  | dateDiff (u : DateUnit) : SqlExpr ts ⟨.dateTime, n₁⟩ → SqlExpr ts ⟨.dateTime, n₂⟩ →
      SqlExpr ts ⟨.int, n₁ || n₂⟩

instance : Inhabited (SqlExpr ts c) := ⟨.field c "" ""⟩

/-- Strict expressions embed into nullable positions (`widen` is identity
at compile time and run time). -/
instance : Coe (SqlExpr ts ⟨t, false⟩) (SqlExpr ts ⟨t, true⟩) := ⟨.widen⟩

/-- Evidence that an expression of flag `ne` fits a position of flag
`nl`, carrying the transport (identity or `widen`). Strict fits anywhere;
nullable fits only nullable — so a NULL-capable value into a NOT NULL
column has **no instance** and fails at elaboration. The strict instances
are high priority: an undetermined literal flag resolves to strict. -/
class FlagFits (ne nl : Bool) where
  fit : {ts : Ctx} → {t : SqlPrim} → SqlExpr ts ⟨t, ne⟩ → SqlExpr ts ⟨t, nl⟩

instance : FlagFits true true := ⟨id⟩
-- default instances (an expression flag nothing else determines resolves
-- late): identity-at-strict outranks widening
@[default_instance 1100] instance : FlagFits false false := ⟨id⟩
@[default_instance] instance : FlagFits false true := ⟨.widen⟩

/-- `p0`, `p1`, … are the compiler's auto-parameter names (one per inlined
literal); a user parameter with such a name would silently alias a
literal's placeholder in the compiled SQL, so the door refuses them. -/
def _root_.String.isReservedParamName (s : String) : Bool :=
  match s.data with
  | 'p' :: rest => !rest.isEmpty && rest.all Char.isDigit
  | _ => false

/-- Reference a declared parameter, **fitted to the position**: the
declared flag (from the context) transports to the expected one — a
strict parameter widens into nullable positions, a nullable parameter
into a strict position fails. Both flags are concrete at resolution
(declaration + expectation), so this is order-safe. Reserved auto-shaped
names (`p{digits}`) are refused by the `rfl` obligation. -/
def SqlExpr.param (name : String) {pt : SqlPrim} {pn m : Bool}
    [HasParam ts.params name ⟨pt, pn⟩] [fits : FlagFits pn m]
    (_h : name.isReservedParamName = false := by decide) :
    SqlExpr ts ⟨pt, m⟩ :=
  fits.fit (.paramE name)

/-- Forget precision: view any expression at the nullable flag (identity
when already nullable, `widen` otherwise) — for storage positions that fix
the flag, e.g. HAVING slots. -/
def SqlExpr.anyNull : {n : Bool} → SqlExpr ts ⟨t, n⟩ → SqlExpr ts ⟨t, true⟩
  | true, e => e
  | false, e => .widen e

/-- Explicit literal constructors, for positions where the expected type is
not yet known and coercions cannot fire (e.g. a literal on the left of
`==.`). Flag-fitted: strict by nature, widening into nullable positions,
defaulting strict when unconstrained. -/
def SqlExpr.int (i : Int) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.int, m⟩ := fits.fit (.intC i)

/-- Inject a runtime value as a literal expression — the bridge from
fetched data back into queries (`fetchFor`'s `IN (…)` lists, `Values`
cell embedding via `v["col"]`). Literals are never NULL. -/
class SqlLit (t : SqlPrim) where
  lit : {ts : Ctx} → t.interp → SqlExpr ts ⟨t, false⟩

instance : SqlLit .int := ⟨.intC⟩
instance : SqlLit .long := ⟨.longC⟩
instance : SqlLit .double := ⟨.doubleC⟩
instance : SqlLit .decimal := ⟨fun m => .decimalC (renderDecimal m)⟩
instance : SqlLit .string := ⟨.stringC⟩
instance : SqlLit .bool := ⟨.boolC⟩
instance : SqlLit .dateTime := ⟨.dateTimeC⟩
instance : SqlLit .guid := ⟨.guidC⟩
def SqlExpr.long (i : Int) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.long, m⟩ := fits.fit (.longC i)
def SqlExpr.dbl (f : Float) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.double, m⟩ := fits.fit (.doubleC f)
def SqlExpr.dec (digits : String) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.decimal, m⟩ := fits.fit (.decimalC digits)
def SqlExpr.str (s : String) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.string, m⟩ := fits.fit (.stringC s)
def SqlExpr.bool (b : Bool) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.bool, m⟩ := fits.fit (.boolC b)
def SqlExpr.dt (iso : String) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.dateTime, m⟩ := fits.fit (.dateTimeC iso)
def SqlExpr.gd (g : String) {m : Bool} [fits : FlagFits false m] :
    SqlExpr ts ⟨.guid, m⟩ := fits.fit (.guidC g)

/-- `e IN (v₁, v₂, …)` over a homogeneous value list. -/
def SqlExpr.inValues (e : SqlExpr ts ⟨t, n⟩) (vs : List (SqlExpr ts ⟨t, true⟩)) :
    SqlExpr ts ⟨.bool, true⟩ :=
  .inList e (vs.map (⟨⟨t, true⟩, ·⟩))

/-- Date-part / date-arithmetic surface helpers. -/
def SqlExpr.year (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := .datePart .year e
def SqlExpr.month (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := .datePart .month e
def SqlExpr.day (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := .datePart .day e
def SqlExpr.addDays (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := .dateAdd .day e k
def SqlExpr.addMonths (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := .dateAdd .month e k
def SqlExpr.addYears (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := .dateAdd .year e k
def SqlExpr.diffDays (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := .dateDiff .day e x
def SqlExpr.diffMonths (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := .dateDiff .month e x
def SqlExpr.diffYears (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := .dateDiff .year e x

/-- A heterogeneously-typed ORDER BY key with its direction; build with
`e.asc` / `e.desc`. -/
structure OrderKey (ts : Ctx) where
  col : SqlType
  expr : SqlExpr ts col
  dir : Dir

def SqlExpr.asc (e : SqlExpr ts c) : OrderKey ts := ⟨c, e, .asc⟩
def SqlExpr.desc (e : SqlExpr ts c) : OrderKey ts := ⟨c, e, .desc⟩

/-- A heterogeneously-typed GROUP BY key; build with `e.key`. -/
structure KeyExpr (ts : Ctx) where
  col : SqlType
  expr : SqlExpr ts col

def SqlExpr.key (e : SqlExpr ts c) : KeyExpr ts := ⟨c, e⟩

/-- The aggregate builder token passed to grouped `select`/`having` lambdas
(mirrors passing an aggregate-function object in LINQ-style APIs). -/
structure Agg where

def Agg.count (_ : Agg) : SqlExpr ts ⟨.int, true⟩ := .widen .countAll
def Agg.sum (_ : Agg) (e : SqlExpr ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ := .aggE .sum e
def Agg.avg (_ : Agg) (e : SqlExpr ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ := .aggE .avg e
def Agg.min (_ : Agg) (e : SqlExpr ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ := .aggE .min e
def Agg.max (_ : Agg) (e : SqlExpr ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ := .aggE .max e

end LeanLinq
