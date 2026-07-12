import LeanLinq.Core.Table

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

/-- The terminal shape of a comprehension spine: does it end in a plain
projection (`yield`) or a grouped one (`groupYield`, carrying
GROUP BY/HAVING)? Indexing `SpineQ` by this makes the grouping discipline
*static*: `SpineQ.bind` accepts only `.plain` spines, so splicing through a
grouped terminal — which would discard its GROUP BY — is untypeable rather
than guarded at run time. -/
inductive Terminal where
  | plain
  | grouped
  deriving DecidableEq, Repr

/-! Intrinsically-typed SQL expressions: `SqlExpr ts c` can only be built
from operations valid for the column type `c`, so ill-typed SQL is
unrepresentable — and `c.nullable` tracks **nullability**, flowing by
construction: literals
are never NULL, column references carry their declared flag, operators OR
their operands' flags (SQL's NULL propagation), aggregates may be NULL
(empty group), `isNull` is never NULL. The context index `ts` is fixed
across a whole query, so the tables referenced by any embedded subquery are
`HasTable`-checked against the same context. Numeric operators are
constrained at the notation layer; the raw constructors are internal.

Subqueries (`inSub`/`existsSub`/`scalarSub`) are stored **structurally** —
the whole AST is one mutual family, so a correlated subquery is simply a
`QueryP` at the *same* ρ, capturing outer binders like any other subterm.
This is what binders at the opaque atom (`ρ s → …`) buy: the mutual
occurrences all sit in positive positions. Construct them with
`SqlExpr.inQuery`/`.exists'`/`ScalarQuery.embed`. -/
mutual

/-- Intrinsically-typed SQL expressions (see the section comment above).
`ts` is a *parameter* of the whole mutual family — the ambient context is
fixed across a query, its subqueries included, and the kernel's nested
`List (OrderKeyP ρ ts)` support requires it. -/
inductive SqlExprP (ρ : Schema → Type) (ts : Ctx) : SqlType → Type where
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
  -- the null tests. Stored structurally at the same ρ; correlation is
  -- ordinary variable capture.
  | existsSub : QueryP ρ ts s → SqlExprP ρ ts .bool
  | like : SqlExprP ρ ts ⟨.string, true⟩ → SqlExprP ρ ts ⟨.string, true⟩ → SqlExprP ρ ts ⟨.bool, true⟩
  -- IN over a value list. Stored as Σ-packed elements because the kernel
  -- rejects nested `List (SqlExprP ρ ts t n)` with a local index; the
  -- homogeneous surface is `SqlExpr.inValues`. Conservatively nullable
  -- (element flags are erased by the packing).
  | inList : SqlExprP ρ ts c → List ((p : SqlType) × SqlExprP ρ ts p) →
      SqlExprP ρ ts ⟨.bool, true⟩
  | inSub : SqlExprP ρ ts ⟨t, nf⟩ → QueryP ρ ts [(cn, ⟨t, m⟩)] →
      SqlExprP ρ ts ⟨.bool, true⟩
  -- a scalar subquery may be empty ⇒ NULL
  | scalarSub : ScalarQueryP ρ ts ⟨t, n⟩ → SqlExprP ρ ts ⟨t, true⟩
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

/-- A heterogeneous tuple of SQL expressions indexed by a schema: the staged
value flowing through query combinators (each column is an expression, not a
runtime value — MetaOCaml-style staging). The `ts` index is the ambient
table context of the enclosing query, threaded through every cell.

The column name lives only in the index, so it flows in from the expected
type or from `.as`-tagged cells; see the row-literal syntax. -/
inductive RowP (ρ : Schema → Type) (ts : Ctx) : Schema → Type where
  | nil  : RowP ρ ts []
  | cons : {name : String} → {c : SqlType} → {s : Schema} →
      SqlExprP ρ ts c → RowP ρ ts s → RowP ρ ts ((name, c) :: s)

/-- A heterogeneously-typed ORDER BY key with its direction; build with
`e.asc` / `e.desc`. -/
structure OrderKeyP (ρ : Schema → Type) (ts : Ctx) where
  col : SqlType
  expr : SqlExprP ρ ts col
  dir : Dir

/-- A heterogeneously-typed GROUP BY key; build with `e.key`. -/
structure KeyExprP (ρ : Schema → Type) (ts : Ctx) where
  col : SqlType
  expr : SqlExprP ρ ts col

/-- The comprehension *spine*: the monadic core that always compiles to one
flat SELECT. `fromT`/`joinT` bind row variables over sources, `guard` adds a
WHERE conjunct, `order` contributes ORDER BY keys, and the spine ends in one
of two terminals — `yield` (a plain projection, `Terminal.plain`) or
`groupYield` (keys/HAVING/own ORDER BY/grouped projection,
`Terminal.grouped`). `fromQ` brings a full `Query` (with boundary clauses)
back in as a derived table.

**Binders take the opaque atom** (`ρ s → …`), not a row: the atom is the
one slot the ∀ρ-polymorphic term cannot inspect, and keeping the mutual
family out of binder domains is what strict positivity demands. The smart
constructors re-wrap with `RowP.ofAtom`, so surface lambdas still receive
rows.

The `ts` index is the ambient table context: `fromT`/`joinT` *demand* a
`HasTable ts n s` instance and store it in the node — the query keeps track
of its referenced tables as capabilities, resolved at elaboration time, so
evaluation needs no name lookup and running against a database lacking a
table is a type error. -/
inductive SpineQP (ρ : Schema → Type) (ts : Ctx) : Terminal → Schema → Type where
  | yield : {s : Schema} → RowP ρ ts s → SpineQP ρ ts .plain s
  -- the grouped terminal: GROUP BY keys, optional HAVING, its own ORDER BY
  -- keys (the pipeline's aggregate-aware `orderBy`, rendered inside the
  -- grouped statement), and the grouped projection
  | groupYield : {s : Schema} → List (KeyExprP ρ ts) →
      Option (SqlExprP ρ ts ⟨.bool, true⟩) → List (OrderKeyP ρ ts) →
      RowP ρ ts s → SpineQP ρ ts .grouped s
  | guard : {g : Terminal} → {s : Schema} → {nb : Bool} →
      SqlExprP ρ ts ⟨.bool, nb⟩ → SpineQP ρ ts g s → SpineQP ρ ts g s
  -- ORDER BY belongs to the statement being assembled, so it lives on the
  -- spine (keys already applied to the bound rows) and `bind` splices
  -- through it — projections/filters after `orderBy` fuse into the same
  -- flat statement (SQL Server in particular forbids ORDER BY inside a
  -- derived table). In a grouped spine the keys may reference aggregates.
  | order : {g : Terminal} → {s : Schema} →
      List (OrderKeyP ρ ts) → SpineQP ρ ts g s → SpineQP ρ ts g s
  | fromT : {g : Terminal} → {n : String} → {s s' : Schema} →
      [inst : HasTable ts.tables n s] → Table n s →
      (ρ s → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  | joinT : {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (ρ s → SqlExprP ρ ts ⟨.bool, nb⟩) →
      (ρ s → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  -- LEFT JOIN: the joined row is NULL-lifted — its columns read as
  -- nullable in the ON predicate and everything downstream: the
  -- type-level truth of the padding row.
  | joinLeftT : {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (ρ s.asNull → SqlExprP ρ ts ⟨.bool, nb⟩) →
      (ρ s.asNull → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  | fromQ : {g : Terminal} → {s s' : Schema} → QueryP ρ ts s →
      (ρ s → SpineQP ρ ts g s') → SpineQP ρ ts g s'

/-- A full query: a spine (of either terminal shape), or a spine decorated by
*boundary* clauses that `bind` must not splice through (DISTINCT,
LIMIT/OFFSET, set operations) — binding over them wraps the query as a
derived table, which is exactly SQL's semantics. The pipeline's GROUP BY
fuses into a `groupYield` terminal at `select`-time.

Use the `query! { … }` syntax or the pipeline smart constructors rather than
the raw constructors. -/
inductive QueryP (ρ : Schema → Type) (ts : Ctx) : Schema → Type where
  | spine : {g : Terminal} → {s : Schema} → SpineQP ρ ts g s → QueryP ρ ts s
  | distinctC : {s : Schema} → QueryP ρ ts s → QueryP ρ ts s
  | limitC : {s : Schema} → QueryP ρ ts s → Option Nat → Option Nat → QueryP ρ ts s
  | setOpC : {s : Schema} → SetOp → QueryP ρ ts s → QueryP ρ ts s → QueryP ρ ts s

/-- A query returning a single scalar value. The `Bool` index is its
nullability: SUM/AVG/MIN/MAX over an empty group are NULL; `COUNT(*)`
never is. -/
inductive ScalarQueryP (ρ : Schema → Type) (ts : Ctx) : SqlType → Type where
  | aggQ (op : AggOp) {n : String} {t : SqlPrim} {nl : Bool}
      (sp : SpineQP ρ ts .plain [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩
  | countQ {s : Schema} (sp : SpineQP ρ ts .plain s) : ScalarQueryP ρ ts .int

end

/-- The compiled-view row representation: a bound row is its source
alias, with the row's schema as a phantom index — the phantom is what
lets binder receivers drive `HasCol` lookups once binders take ρ-values
directly. The ∀ρ-polymorphic `Query` bundle (and with it the
evaluating/counting instantiations) arrives with the query layer. -/
structure AliasOf (s : Schema) where
  alias : String

/-- `SqlExpr` is the alias-instantiated view — the spelling the
library's internal walks write. -/
abbrev SqlExpr : Ctx → SqlType → Type := SqlExprP AliasOf

/- Constructor wrappers at the alias view, for the three constructors
user code spells by full name (dot-notation on receivers resolves
through the reducible abbrev to `SqlExprP` on its own — aliasing more
would shadow that path). -/
def SqlExpr.caseWhen (c : SqlExprP ρ ts ⟨.bool, nc⟩) (a b : SqlExprP ρ ts ⟨t, true⟩) :
    SqlExprP ρ ts ⟨t, true⟩ := SqlExprP.caseWhen c a b
def SqlExpr.concat (a b : SqlExprP ρ ts ⟨.string, n⟩) : SqlExprP ρ ts ⟨.string, n⟩ :=
  SqlExprP.concat a b
def SqlExpr.now : SqlExprP ρ ts .dateTime := SqlExprP.now

instance : Inhabited (SqlExpr ts c) := ⟨.field (s' := []) c ⟨""⟩ ""⟩

instance : Inhabited (AliasOf s) := ⟨⟨""⟩⟩

/-- Alias-instantiated views of the query family — the spellings the
library's internal walks (compiler, evaluator, `card`) write. -/
abbrev Row : Ctx → Schema → Type := RowP AliasOf
abbrev SpineQ : Ctx → Terminal → Schema → Type := SpineQP AliasOf
abbrev QueryA : Ctx → Schema → Type := QueryP AliasOf
abbrev ScalarA : Ctx → SqlType → Type := ScalarQueryP AliasOf

private def RowP.ofAtomAux (a : ρ s') : (s : Schema) → RowP ρ ts s
  | [] => .nil
  | (nm, c) :: s => .cons (.field c a nm) (RowP.ofAtomAux a s)

/-- The row a binder's atom stands for: every column a `field` reference
through the atom. The smart constructors wrap raw binders with this, so
surface lambdas receive rows while the AST stores only the opaque atom. -/
def RowP.ofAtom {s : Schema} (a : ρ s) : RowP ρ ts s :=
  RowP.ofAtomAux a s

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

abbrev OrderKey : Ctx → Type := OrderKeyP AliasOf

def SqlExprP.asc (e : SqlExprP ρ ts c) : OrderKeyP ρ ts := ⟨c, e, .asc⟩
def SqlExprP.desc (e : SqlExprP ρ ts c) : OrderKeyP ρ ts := ⟨c, e, .desc⟩

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

end LeanLinq
