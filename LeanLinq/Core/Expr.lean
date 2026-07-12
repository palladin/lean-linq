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
inductive SqlExprP (ρ : Schema → Type) : Ctx → SqlType → Type where
  -- literals (compiled to auto-named parameters, never inlined; never NULL)
  | intC (i : Int) : SqlExprP ρ ts .int
  | longC (i : Int) : SqlExprP ρ ts .long
  | doubleC (f : Float) : SqlExprP ρ ts .double
  | decimalC (digits : String) : SqlExprP ρ ts .decimal
  | stringC (s : String) : SqlExprP ρ ts .string
  | boolC (b : Bool) : SqlExprP ρ ts .bool
  | dateTimeC (iso : String) : SqlExprP ρ ts .dateTime
  | guidC (g : String) : SqlExprP ρ ts .guid
  | nullC (t : SqlPrim) : SqlExprP ρ ts ⟨t, true⟩
  -- user-named parameter: membership in the context's parameter list is
  -- established here (`HasParam`) and the resolved accessor is stored in
  -- the node — an unbound parameter is untypeable, and both its type and
  -- its nullability come from the context declaration
  | paramE (name : String) {pc : SqlType}
      [inst : HasParam ts.params name pc] : SqlExprP ρ ts pc
  -- column reference with its declared nullability: the occurrence
  -- carries the bound row's ρ-representation (PHOAS) — the compiled view
  -- reads an alias out of it, the evaluating view a whole row. The row's
  -- schema is a phantom here (markers carry the typing discipline).
  | field (c : SqlType) {s' : Schema} (row : ρ s') (name : String) : SqlExprP ρ ts c
  -- the strict→nullable subtyping node (`Coe` inserts it); compiler and
  -- evaluator treat it as identity
  | widen : SqlExprP ρ ts ⟨t, false⟩ → SqlExprP ρ ts ⟨t, true⟩
  -- operators: flags OR (SQL NULL propagation)
  | arith (op : ArithOp) : SqlExprP ρ ts c → SqlExprP ρ ts c → SqlExprP ρ ts c
  -- text/comparison/branch operators take operands at the nullable flag
  -- (strict operands widen via coercion): `String`/`Bool` literals have no
  -- default-instance channel, so a free flag metavariable on an operand
  -- would strand elaboration — conservative-nullable keeps every position
  -- concrete. Numeric `arith` keeps exact OR-flags (numerals default).
  | concat : SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.string, n⟩
  | cmp (op : CmpOp) : SqlExprP ρ ts ⟨t, true⟩ → SqlExprP ρ ts ⟨t, true⟩ → SqlExprP ρ ts ⟨.bool, true⟩
  | and : SqlExprP ρ ts ⟨.bool, n₁⟩ → SqlExprP ρ ts ⟨.bool, n₂⟩ → SqlExprP ρ ts ⟨.bool, n₁ || n₂⟩
  | or : SqlExprP ρ ts ⟨.bool, n₁⟩ → SqlExprP ρ ts ⟨.bool, n₂⟩ → SqlExprP ρ ts ⟨.bool, n₁ || n₂⟩
  | not : SqlExprP ρ ts ⟨.bool, n⟩ → SqlExprP ρ ts ⟨.bool, n⟩
  -- NULL tests accept any operand flag and are themselves never NULL
  | isNull : SqlExprP ρ ts c → SqlExprP ρ ts .bool
  | isNotNull : SqlExprP ρ ts c → SqlExprP ρ ts .bool
  -- EXISTS (subquery): true or false, never NULL — a strict bool like
  -- the null tests. Stored staged (see `ExistsSub`); correlation works
  -- through the scope its eval action receives.
  | existsSub : ExistsSub ts → SqlExprP ρ ts .bool
  | like : SqlExprP ρ ts ⟨.string, true⟩ → SqlExprP ρ ts ⟨.string, true⟩ → SqlExprP ρ ts ⟨.bool, true⟩
  -- IN over a value list. Stored as Σ-packed elements because the kernel
  -- rejects nested `List (SqlExprP ρ ts t n)` with a local index; the
  -- homogeneous surface is `SqlExpr.inValues`. Conservatively nullable
  -- (element flags are erased by the packing).
  | inList : SqlExprP ρ ts c → List ((p : SqlType) × SqlExprP ρ ts p) →
      SqlExprP ρ ts ⟨.bool, true⟩
  | inSub : SqlExprP ρ ts ⟨t, n⟩ → SubQuery ts t → SqlExprP ρ ts ⟨.bool, true⟩
  -- a scalar subquery may be empty ⇒ NULL
  | scalarSub : SubQuery ts t → SqlExprP ρ ts ⟨t, true⟩
  | caseWhen : SqlExprP ρ ts ⟨.bool, nc⟩ → SqlExprP ρ ts ⟨t, true⟩ → SqlExprP ρ ts ⟨t, true⟩ →
      SqlExprP ρ ts ⟨t, true⟩
  -- aggregates (meaningful in grouped selects / HAVING / scalar queries):
  -- SUM/AVG/MIN/MAX over an empty group are NULL; COUNT never is
  | aggE (op : AggOp) : SqlExprP ρ ts ⟨t, n⟩ → SqlExprP ρ ts ⟨t, true⟩
  | countAll : SqlExprP ρ ts .int
  -- functions: propagate their operands' flags
  | abs : SqlExprP ρ ts c → SqlExprP ρ ts c
  | round : SqlExprP ρ ts c → Int → SqlExprP ρ ts c
  | ceiling : SqlExprP ρ ts c → SqlExprP ρ ts c
  | floor : SqlExprP ρ ts c → SqlExprP ρ ts c
  | substring : SqlExprP ρ ts ⟨.string, n⟩ → Int → Int → SqlExprP ρ ts ⟨.string, n⟩
  | upper : SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.string, n⟩
  | lower : SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.string, n⟩
  | trim : SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.string, n⟩
  | length : SqlExprP ρ ts ⟨.string, n⟩ → SqlExprP ρ ts ⟨.int, n⟩
  | now : SqlExprP ρ ts .dateTime
  | datePart (u : DateUnit) : SqlExprP ρ ts ⟨.dateTime, n⟩ → SqlExprP ρ ts ⟨.int, n⟩
  | dateAdd (u : DateUnit) : SqlExprP ρ ts ⟨.dateTime, n⟩ → Int → SqlExprP ρ ts ⟨.dateTime, n⟩
  | dateDiff (u : DateUnit) : SqlExprP ρ ts ⟨.dateTime, n₁⟩ → SqlExprP ρ ts ⟨.dateTime, n₂⟩ →
      SqlExprP ρ ts ⟨.int, n₁ || n₂⟩

/-- The compiled-view row representation: a bound row is its source
alias, with the row's schema as a phantom index — the phantom is what
lets binder receivers drive `HasCol` lookups once binders take ρ-values
directly. The ∀ρ-polymorphic `Query` bundle (and with it the
evaluating/counting instantiations) arrives with the query layer. -/
structure AliasOf (s : Schema) where
  alias : String

abbrev StrRow : Schema → Type := AliasOf

/-- `SqlExpr` is the alias-instantiated view — the spelling the whole
library (and every user) writes. -/
abbrev SqlExpr : Ctx → SqlType → Type := SqlExprP StrRow

/- Constructor wrappers at the alias view, for the three constructors
user code spells by full name (dot-notation on receivers resolves
through the reducible abbrev to `SqlExprP` on its own — aliasing more
would shadow that path). -/
def SqlExpr.caseWhen (c : SqlExpr ts ⟨.bool, nc⟩) (a b : SqlExpr ts ⟨t, true⟩) :
    SqlExpr ts ⟨t, true⟩ := SqlExprP.caseWhen c a b
def SqlExpr.concat (a b : SqlExpr ts ⟨.string, n⟩) : SqlExpr ts ⟨.string, n⟩ :=
  SqlExprP.concat a b
def SqlExpr.now : SqlExpr ts .dateTime := SqlExprP.now

instance : Inhabited (SqlExpr ts c) := ⟨.field (s' := []) c ⟨""⟩ ""⟩

/-- Strict expressions embed into nullable positions (`widen` is identity
at compile time and run time). -/
instance : Coe (SqlExprP ρ ts ⟨t, false⟩) (SqlExprP ρ ts ⟨t, true⟩) := ⟨.widen⟩

/-- Evidence that an expression of flag `ne` fits a position of flag
`nl`, carrying the transport (identity or `widen`). Strict fits anywhere;
nullable fits only nullable — so a NULL-capable value into a NOT NULL
column has **no instance** and fails at elaboration. The strict instances
are high priority: an undetermined literal flag resolves to strict. -/
class FlagFits (ne nl : Bool) where
  fit : {ρ : Schema → Type} → {ts : Ctx} → {t : SqlPrim} →
    SqlExprP ρ ts ⟨t, ne⟩ → SqlExprP ρ ts ⟨t, nl⟩

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
    SqlExprP ρ ts ⟨pt, m⟩ :=
  fits.fit (.paramE name)

/-- Forget precision: view any expression at the nullable flag (identity
when already nullable, `widen` otherwise) — for storage positions that fix
the flag, e.g. HAVING slots. -/
def SqlExprP.anyNull : {n : Bool} → SqlExprP ρ ts ⟨t, n⟩ → SqlExprP ρ ts ⟨t, true⟩
  | true, e => e
  | false, e => .widen e

/-- Explicit literal constructors, for positions where the expected type is
not yet known and coercions cannot fire (e.g. a literal on the left of
`==.`). Flag-fitted: strict by nature, widening into nullable positions,
defaulting strict when unconstrained. -/
def SqlExpr.int (i : Int) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.int, m⟩ := fits.fit (.intC i)

/-- Inject a runtime value as a literal expression — the bridge from
fetched data back into queries (`fetchFor`'s `IN (…)` lists, `Values`
cell embedding via `v["col"]`). Literals are never NULL. -/
class SqlLit (t : SqlPrim) where
  lit : {ts : Ctx} → t.interp → SqlExprP ρ ts ⟨t, false⟩

instance : SqlLit .int := ⟨.intC⟩
instance : SqlLit .long := ⟨.longC⟩
instance : SqlLit .double := ⟨.doubleC⟩
instance : SqlLit .decimal := ⟨fun m => .decimalC (renderDecimal m)⟩
instance : SqlLit .string := ⟨.stringC⟩
instance : SqlLit .bool := ⟨.boolC⟩
instance : SqlLit .dateTime := ⟨.dateTimeC⟩
instance : SqlLit .guid := ⟨.guidC⟩
def SqlExpr.long (i : Int) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.long, m⟩ := fits.fit (.longC i)
def SqlExpr.dbl (f : Float) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.double, m⟩ := fits.fit (.doubleC f)
def SqlExpr.dec (digits : String) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.decimal, m⟩ := fits.fit (.decimalC digits)
def SqlExpr.str (s : String) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.string, m⟩ := fits.fit (.stringC s)
def SqlExpr.bool (b : Bool) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.bool, m⟩ := fits.fit (.boolC b)
def SqlExpr.dt (iso : String) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.dateTime, m⟩ := fits.fit (.dateTimeC iso)
def SqlExpr.gd (g : String) {m : Bool} [fits : FlagFits false m] :
    SqlExprP ρ ts ⟨.guid, m⟩ := fits.fit (.guidC g)

/-- `e IN (v₁, v₂, …)` over a homogeneous value list. -/
def SqlExprP.inValues (e : SqlExprP ρ ts ⟨t, n⟩) (vs : List (SqlExprP ρ ts ⟨t, true⟩)) :
    SqlExprP ρ ts ⟨.bool, true⟩ :=
  .inList e (vs.map (⟨⟨t, true⟩, ·⟩))

/-- `e NOT IN (v₁, …)` — `.not` of the three-valued IN, inheriting SQL's
NULL semantics: a NULL among the values turns a miss into UNKNOWN, which
WHERE filters — the classic `NOT IN` + NULL gotcha behaves exactly as
the engines do. -/
def SqlExprP.notInValues (e : SqlExprP ρ ts ⟨t, n⟩)
    (vs : List (SqlExprP ρ ts ⟨t, true⟩)) : SqlExprP ρ ts ⟨.bool, true⟩ :=
  .not (SqlExprP.inValues e vs)

/-- Date-part / date-arithmetic surface helpers. -/
def SqlExprP.year (e : SqlExprP ρ ts ⟨.dateTime, n⟩) : SqlExprP ρ ts ⟨.int, n⟩ := .datePart .year e
def SqlExprP.month (e : SqlExprP ρ ts ⟨.dateTime, n⟩) : SqlExprP ρ ts ⟨.int, n⟩ := .datePart .month e
def SqlExprP.day (e : SqlExprP ρ ts ⟨.dateTime, n⟩) : SqlExprP ρ ts ⟨.int, n⟩ := .datePart .day e
def SqlExprP.addDays (e : SqlExprP ρ ts ⟨.dateTime, n⟩) (k : Int) : SqlExprP ρ ts ⟨.dateTime, n⟩ := .dateAdd .day e k
def SqlExprP.addMonths (e : SqlExprP ρ ts ⟨.dateTime, n⟩) (k : Int) : SqlExprP ρ ts ⟨.dateTime, n⟩ := .dateAdd .month e k
def SqlExprP.addYears (e : SqlExprP ρ ts ⟨.dateTime, n⟩) (k : Int) : SqlExprP ρ ts ⟨.dateTime, n⟩ := .dateAdd .year e k
def SqlExprP.diffDays (e : SqlExprP ρ ts ⟨.dateTime, n₁⟩) (x : SqlExprP ρ ts ⟨.dateTime, n₂⟩) : SqlExprP ρ ts ⟨.int, n₁ || n₂⟩ := .dateDiff .day e x
def SqlExprP.diffMonths (e : SqlExprP ρ ts ⟨.dateTime, n₁⟩) (x : SqlExprP ρ ts ⟨.dateTime, n₂⟩) : SqlExprP ρ ts ⟨.int, n₁ || n₂⟩ := .dateDiff .month e x
def SqlExprP.diffYears (e : SqlExprP ρ ts ⟨.dateTime, n₁⟩) (x : SqlExprP ρ ts ⟨.dateTime, n₂⟩) : SqlExprP ρ ts ⟨.int, n₁ || n₂⟩ := .dateDiff .year e x

/-- A heterogeneously-typed ORDER BY key with its direction; build with
`e.asc` / `e.desc`. -/
structure OrderKeyP (ρ : Schema → Type) (ts : Ctx) where
  col : SqlType
  expr : SqlExprP ρ ts col
  dir : Dir

abbrev OrderKey : Ctx → Type := OrderKeyP AliasOf

def SqlExprP.asc (e : SqlExprP ρ ts c) : OrderKeyP ρ ts := ⟨c, e, .asc⟩
def SqlExprP.desc (e : SqlExprP ρ ts c) : OrderKeyP ρ ts := ⟨c, e, .desc⟩

/-- A heterogeneously-typed GROUP BY key; build with `e.key`. -/
structure KeyExprP (ρ : Schema → Type) (ts : Ctx) where
  col : SqlType
  expr : SqlExprP ρ ts col

abbrev KeyExpr : Ctx → Type := KeyExprP AliasOf

def SqlExprP.key (e : SqlExprP ρ ts c) : KeyExprP ρ ts := ⟨c, e⟩

/-- The aggregate builder token passed to grouped `select`/`having` lambdas
(mirrors passing an aggregate-function object in LINQ-style APIs). -/
structure Agg where

def Agg.count (_ : Agg) : SqlExprP ρ ts ⟨.int, true⟩ := .widen .countAll
def Agg.sum (_ : Agg) (e : SqlExprP ρ ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ := .aggE .sum e
def Agg.avg (_ : Agg) (e : SqlExprP ρ ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ := .aggE .avg e
def Agg.min (_ : Agg) (e : SqlExprP ρ ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ := .aggE .min e
def Agg.max (_ : Agg) (e : SqlExprP ρ ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ := .aggE .max e

/- Transitional wrappers: the abbrev-typed world (pre-∀ρ-flip receivers
and textual spellings) reaches the generalized defs through
`SqlExpr`-spelled signatures. -/
namespace SqlExpr
def anyNull (e : SqlExpr ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ := SqlExprP.anyNull e
def inValues (e : SqlExpr ts ⟨t, n⟩) (vs : List (SqlExpr ts ⟨t, true⟩)) :
    SqlExpr ts ⟨.bool, true⟩ := SqlExprP.inValues e vs
def notInValues (e : SqlExpr ts ⟨t, n⟩) (vs : List (SqlExpr ts ⟨t, true⟩)) :
    SqlExpr ts ⟨.bool, true⟩ := SqlExprP.notInValues e vs
def year (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := SqlExprP.year e
def month (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := SqlExprP.month e
def day (e : SqlExpr ts ⟨.dateTime, n⟩) : SqlExpr ts ⟨.int, n⟩ := SqlExprP.day e
def addDays (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := SqlExprP.addDays e k
def addMonths (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := SqlExprP.addMonths e k
def addYears (e : SqlExpr ts ⟨.dateTime, n⟩) (k : Int) : SqlExpr ts ⟨.dateTime, n⟩ := SqlExprP.addYears e k
def diffDays (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := SqlExprP.diffDays e x
def diffMonths (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := SqlExprP.diffMonths e x
def diffYears (e : SqlExpr ts ⟨.dateTime, n₁⟩) (x : SqlExpr ts ⟨.dateTime, n₂⟩) : SqlExpr ts ⟨.int, n₁ || n₂⟩ := SqlExprP.diffYears e x
def asc (e : SqlExpr ts c) : OrderKey ts := SqlExprP.asc e
def desc (e : SqlExpr ts c) : OrderKey ts := SqlExprP.desc e
def key (e : SqlExpr ts c) : KeyExpr ts := SqlExprP.key e
end SqlExpr

end LeanLinq
