import LeanLinq.Core.Query
import LeanLinq.Notation

/-! Grouped expressions form a separate, phase-indexed language. Only named
keys, aggregate results, and literals enter it; no ordinary row expression
can be injected, and grouped results cannot escape back into row expressions.
The raw query algebra enforces this distinction too: wrappers lower only
to the intrinsically grouped family, never to ordinary row expressions. -/

namespace LeanLinq

/-- A grouped scalar. Its raw representation is intrinsically grouped and indexed by the
declared key schema. κ keeps ordinary callback captures separate; even
pattern matching the wrapper cannot expose an ordinary row expression. -/
structure GroupExprP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) (c : SqlType) where
  private mk ::
  private raw : GroupedExprP ρ ts ks c

namespace GroupExprP

private def fitRaw : {ne nl : Bool} → [FlagFits ne nl] →
    GroupedExprP ρ ts ks ⟨t, ne⟩ → GroupedExprP ρ ts ks ⟨t, nl⟩
  | false, false, _, e => e
  | false, true, _, e => .widen e
  | true, true, _, e => e
  | true, false, fits, _ => False.elim (Bool.noConfusion (fits.valid rfl))

def widen (e : GroupExprP κ ρ ts ks ⟨t, false⟩) : GroupExprP κ ρ ts ks ⟨t, true⟩ :=
  ⟨.widen e.raw⟩
instance : Coe (GroupExprP κ ρ ts ks ⟨t, false⟩) (GroupExprP κ ρ ts ks ⟨t, true⟩) := ⟨widen⟩

def anyNull : {n : Bool} → GroupExprP κ ρ ts ks ⟨t, n⟩ → GroupExprP κ ρ ts ks ⟨t, true⟩
  | true, e => e
  | false, e => e.widen

def atFlag (n : Bool) (e : GroupExprP κ ρ ts ks ⟨t, false⟩) : GroupExprP κ ρ ts ks ⟨t, n⟩ :=
  match n with
  | false => e
  | true => e.widen

def int (i : Int) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.int, n⟩ :=
  ⟨fitRaw (.intC i)⟩
def long (i : Int) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.long, n⟩ :=
  ⟨fitRaw (.longC i)⟩
def dbl (v : Float) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.double, n⟩ :=
  ⟨fitRaw (.doubleC v)⟩
def dec (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.decimal, n⟩ :=
  ⟨fitRaw (.decimalC v)⟩
def str (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.string, n⟩ :=
  ⟨fitRaw (.stringC v)⟩
def bool (v : Bool) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.bool, n⟩ :=
  ⟨fitRaw (.boolC v)⟩
def dt (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩ :=
  ⟨fitRaw (.dateTimeC v)⟩
def gd (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ks ⟨.guid, n⟩ :=
  ⟨fitRaw (.guidC v)⟩
def null (t : SqlPrim) : GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.nullC t⟩
def param (name : String) {pt : SqlPrim} {pn n : Bool}
    [HasParam ts.params name ⟨pt, pn⟩] [fits : FlagFits pn n]
    (_h : name.isReservedParamName = false := by decide) : GroupExprP κ ρ ts ks ⟨pt, n⟩ :=
  ⟨fitRaw (.paramE name)⟩

def arith (op : ArithOp) [SqlNumeric c.ty]
    (a b : GroupExprP κ ρ ts ks c) : GroupExprP κ ρ ts ks c := ⟨.arith op a.raw b.raw⟩
instance [SqlNumeric t] : Add (GroupExprP κ ρ ts ks ⟨t, n⟩) := ⟨arith .add⟩
instance [SqlNumeric t] : Sub (GroupExprP κ ρ ts ks ⟨t, n⟩) := ⟨arith .sub⟩
instance [SqlNumeric t] : Mul (GroupExprP κ ρ ts ks ⟨t, n⟩) := ⟨arith .mul⟩
instance [SqlNumeric t] : Div (GroupExprP κ ρ ts ks ⟨t, n⟩) := ⟨arith .div⟩
instance : OfNat (GroupExprP κ ρ ts ks ⟨.int, n⟩) k := ⟨atFlag n ⟨.intC k⟩⟩
instance : OfNat (GroupExprP κ ρ ts ks ⟨.long, n⟩) k := ⟨atFlag n ⟨.longC k⟩⟩
instance : Neg (GroupExprP κ ρ ts ks ⟨.int, n⟩) := ⟨fun e => 0 - e⟩
instance : OfScientific (GroupExprP κ ρ ts ks ⟨.decimal, n⟩) :=
  ⟨fun m sign e => atFlag n ⟨.decimalC (scientificDigits m sign e)⟩⟩
instance : OfScientific (GroupExprP κ ρ ts ks ⟨.double, n⟩) :=
  ⟨fun m sign e => atFlag n ⟨.doubleC (OfScientific.ofScientific m sign e)⟩⟩
instance : Coe String (GroupExprP κ ρ ts ks ⟨.string, true⟩) := ⟨fun v => ⟨.widen (.stringC v)⟩⟩
instance : Coe Bool (GroupExprP κ ρ ts ks ⟨.bool, true⟩) := ⟨fun v => ⟨.widen (.boolC v)⟩⟩
instance (priority := high) : Coe String (GroupExprP κ ρ ts ks ⟨.string, false⟩) := ⟨fun v => ⟨.stringC v⟩⟩
instance (priority := high) : Coe Bool (GroupExprP κ ρ ts ks ⟨.bool, false⟩) := ⟨fun v => ⟨.boolC v⟩⟩

def concat (a b : GroupExprP κ ρ ts ks ⟨.string, n⟩) : GroupExprP κ ρ ts ks ⟨.string, n⟩ :=
  ⟨.concat a.raw b.raw⟩
instance : Append (GroupExprP κ ρ ts ks ⟨.string, n⟩) := ⟨concat⟩
def cmp (op : CmpOp) (a b : GroupExprP κ ρ ts ks ⟨t, true⟩) : GroupExprP κ ρ ts ks ⟨.bool, true⟩ :=
  ⟨.cmp op a.raw b.raw⟩
def and (a : GroupExprP κ ρ ts ks ⟨.bool, n₁⟩) (b : GroupExprP κ ρ ts ks ⟨.bool, n₂⟩) :
    GroupExprP κ ρ ts ks ⟨.bool, n₁ || n₂⟩ := ⟨.and a.raw b.raw⟩
def or (a : GroupExprP κ ρ ts ks ⟨.bool, n₁⟩) (b : GroupExprP κ ρ ts ks ⟨.bool, n₂⟩) :
    GroupExprP κ ρ ts ks ⟨.bool, n₁ || n₂⟩ := ⟨.or a.raw b.raw⟩
def not (a : GroupExprP κ ρ ts ks ⟨.bool, n⟩) : GroupExprP κ ρ ts ks ⟨.bool, n⟩ := ⟨.not a.raw⟩
def isNull (e : GroupExprP κ ρ ts ks c) : GroupExprP κ ρ ts ks .bool := ⟨.isNull e.raw⟩
def isNotNull (e : GroupExprP κ ρ ts ks c) : GroupExprP κ ρ ts ks .bool := ⟨.isNotNull e.raw⟩
def like (e p : GroupExprP κ ρ ts ks ⟨.string, true⟩) : GroupExprP κ ρ ts ks ⟨.bool, true⟩ :=
  ⟨.like e.raw p.raw⟩
def caseWhen (p : GroupExprP κ ρ ts ks ⟨.bool, np⟩)
    (a b : GroupExprP κ ρ ts ks ⟨t, true⟩) : GroupExprP κ ρ ts ks ⟨t, true⟩ :=
  ⟨.caseWhen p.raw a.raw b.raw⟩
def inValues (e : GroupExprP κ ρ ts ks ⟨t, n⟩) (vs : List (GroupExprP κ ρ ts ks ⟨t, true⟩)) :
    GroupExprP κ ρ ts ks ⟨.bool, true⟩ := ⟨.inList e.raw (vs.foldr (fun v rest => .cons v.raw rest) .nil)⟩
def notInValues (e : GroupExprP κ ρ ts ks ⟨t, n⟩) (vs : List (GroupExprP κ ρ ts ks ⟨t, true⟩)) :
    GroupExprP κ ρ ts ks ⟨.bool, true⟩ := (e.inValues vs).not
def abs (e : GroupExprP κ ρ ts ks c) [SqlNumeric c.ty] : GroupExprP κ ρ ts ks c := ⟨.abs e.raw⟩
def round (e : GroupExprP κ ρ ts ks c) (digits : Int) [SqlNumeric c.ty] : GroupExprP κ ρ ts ks c :=
  ⟨.round e.raw digits⟩
def ceiling (e : GroupExprP κ ρ ts ks c) [SqlNumeric c.ty] : GroupExprP κ ρ ts ks c := ⟨.ceiling e.raw⟩
def floor (e : GroupExprP κ ρ ts ks c) [SqlNumeric c.ty] : GroupExprP κ ρ ts ks c := ⟨.floor e.raw⟩
def substring (e : GroupExprP κ ρ ts ks ⟨.string, n⟩) (start : Int) (len : Nat) : GroupExprP κ ρ ts ks ⟨.string, n⟩ :=
  ⟨.substring e.raw start len⟩
def upper (e : GroupExprP κ ρ ts ks ⟨.string, n⟩) : GroupExprP κ ρ ts ks ⟨.string, n⟩ := ⟨.upper e.raw⟩
def lower (e : GroupExprP κ ρ ts ks ⟨.string, n⟩) : GroupExprP κ ρ ts ks ⟨.string, n⟩ := ⟨.lower e.raw⟩
def trim (e : GroupExprP κ ρ ts ks ⟨.string, n⟩) : GroupExprP κ ρ ts ks ⟨.string, n⟩ := ⟨.trim e.raw⟩
def length (e : GroupExprP κ ρ ts ks ⟨.string, n⟩) : GroupExprP κ ρ ts ks ⟨.int, n⟩ := ⟨.length e.raw⟩
def now : GroupExprP κ ρ ts ks .dateTime := ⟨.now⟩
def year (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ks ⟨.int, n⟩ := ⟨.datePart .year e.raw⟩
def month (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ks ⟨.int, n⟩ := ⟨.datePart .month e.raw⟩
def day (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ks ⟨.int, n⟩ := ⟨.datePart .day e.raw⟩
def addDays (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩ := ⟨.dateAdd .day e.raw k⟩
def addMonths (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩ := ⟨.dateAdd .month e.raw k⟩
def addYears (e : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ks ⟨.dateTime, n⟩ := ⟨.dateAdd .year e.raw k⟩

end GroupExprP

-- The same tokens elaborate to the ordinary or grouped expression family.
scoped infix:50 " ==. " => GroupExprP.cmp CmpOp.eq
scoped infix:50 " !=. " => GroupExprP.cmp CmpOp.ne
scoped infix:50 " <. " => GroupExprP.cmp CmpOp.lt
scoped infix:50 " <=. " => GroupExprP.cmp CmpOp.le
scoped infix:50 " >. " => GroupExprP.cmp CmpOp.gt
scoped infix:50 " >=. " => GroupExprP.cmp CmpOp.ge
scoped infixl:35 " &&. " => GroupExprP.and
scoped infixl:30 " ||. " => GroupExprP.or
scoped prefix:max "!." => GroupExprP.not

structure GroupCellP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) (name : String) (c : SqlType) where
  expr : GroupExprP κ ρ ts ks c
def GroupExprP.as (e : GroupExprP κ ρ ts ks c) (name : String) : GroupCellP κ ρ ts ks name c := ⟨e⟩

structure GroupRowP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) (s : Schema) where
  private mk ::
  private raw : GroupedRowP ρ ts ks s
def GroupRowP.nil : GroupRowP κ ρ ts ks [] := ⟨.nil⟩
def GroupRowP.consCell (cell : GroupCellP κ ρ ts ks name c) (r : GroupRowP κ ρ ts ks s) :
    GroupRowP κ ρ ts ks ((name, c) :: s) := ⟨.cons cell.expr.raw r.raw⟩
def GroupRowP.col (r : GroupRowP κ ρ ts ks s) (name : String) [i : HasCol s name c] :
    GroupExprP κ ρ ts ks c := ⟨GroupedRowP.get i.ref r.raw⟩
def GroupRowP.append (a : GroupRowP κ ρ ts ks s₁) (b : GroupRowP κ ρ ts ks s₂) :
    GroupRowP κ ρ ts ks (s₁ ++ s₂) := ⟨a.raw.append b.raw⟩
instance : HAppend (GroupRowP κ ρ ts ks s₁) (GroupRowP κ ρ ts ks s₂) (GroupRowP κ ρ ts ks (s₁ ++ s₂)) :=
  ⟨GroupRowP.append⟩

structure GroupOrderKeyP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) where
  private mk ::
  private col : SqlType
  private expr : GroupedExprP ρ ts ks col
  private dir : Dir
def GroupExprP.asc (e : GroupExprP κ ρ ts ks c) : GroupOrderKeyP κ ρ ts ks := ⟨c, e.raw, .asc⟩
def GroupExprP.desc (e : GroupExprP κ ρ ts ks c) : GroupOrderKeyP κ ρ ts ks := ⟨c, e.raw, .desc⟩

/-- The comprehension aggregate capability accepts only ordinary row
expressions. Its private constructor is available only inside a grouped scope. -/
structure GroupAggregateP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) where
  private mk ::
def GroupAggregateP.count (_ : GroupAggregateP κ ρ ts ks) : GroupExprP κ ρ ts ks ⟨.int, true⟩ :=
  ⟨.widen .countAll⟩
def GroupAggregateP.sum (_ : GroupAggregateP κ ρ ts ks) (e : SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .sum e⟩
def GroupAggregateP.avg (_ : GroupAggregateP κ ρ ts ks) (e : SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .avg e⟩
def GroupAggregateP.min (_ : GroupAggregateP κ ρ ts ks) (e : SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .min e⟩
def GroupAggregateP.max (_ : GroupAggregateP κ ρ ts ks) (e : SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .max e⟩

/-- Pipeline aggregate selectors receive the original input row. They cannot
return a grouped expression, so nested aggregation is a type error. -/
structure GroupAggP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) (s : Schema) where
  private mk ::
  private source : RowP ρ ts s
def GroupAggP.count (_ : GroupAggP κ ρ ts ks s) : GroupExprP κ ρ ts ks ⟨.int, true⟩ := ⟨.widen .countAll⟩
def GroupAggP.sum (a : GroupAggP κ ρ ts ks s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .sum (f a.source)⟩
def GroupAggP.avg (a : GroupAggP κ ρ ts ks s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .avg (f a.source)⟩
def GroupAggP.min (a : GroupAggP κ ρ ts ks s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .min (f a.source)⟩
def GroupAggP.max (a : GroupAggP κ ρ ts ks s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ks ⟨t, true⟩ := ⟨.aggE .max (f a.source)⟩

structure GroupedClauseP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (ks : Schema) (s : Schema) where
  row : GroupRowP κ ρ ts ks s
  having? : Option (GroupExprP κ ρ ts ks ⟨.bool, true⟩) := none
  order : List (GroupOrderKeyP κ ρ ts ks) := []

private def keyRowAux (ks : Schema) : (s : Schema) →
    ({c : SqlType} → KeyRef s c → KeyRef ks c) → GroupedRowP ρ ts ks s
  | [], _ => .nil
  | (_, _) :: rest, refs =>
      .cons (.key (refs .here)) (keyRowAux ks rest (fun ref => refs (.there ref)))

/-- Every key reference denotes a typed position in this binding's key row. -/
private def keyRow (ks : Schema) : GroupRowP κ ρ ts ks ks :=
  ⟨keyRowAux ks ks (fun ref => ref)⟩

private def lowerOrders (orders : List (GroupOrderKeyP κ ρ ts ks)) : GroupedOrdersP ρ ts ks :=
  orders.foldr (fun k rest => .cons k.expr k.dir rest) .nil

private def lowerHaving : Option (GroupedExprP ρ ts ks ⟨.bool, true⟩) → GroupedHavingP ρ ts ks
  | none => .none
  | some e => .some e

def groupYieldR (keys : RowP ρ ts ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggregateP κ ρ ts ks → GroupedClauseP κ ρ ts ks out)
    (nonempty : ks ≠ [] := by simp) : SpineQP ρ ts .grouped out :=
  let clause := f (κ := Unit) (keyRow ks) ⟨⟩
  .groupYield keys nonempty (lowerHaving (clause.having?.map (·.raw)))
    (lowerOrders clause.order) clause.row.raw

structure GroupedQueryP (ρ : Schema → Type) (ts : Ctx) (s ks : Schema) where
  private mk ::
  private query : QueryP ρ ts s
  private keys : RowP ρ ts s → RowP ρ ts ks
  private nonempty : ks ≠ []
  private having? : Option (RowP ρ ts s → GroupedExprP ρ ts ks ⟨.bool, true⟩) := none
  private order? : Option (RowP ρ ts s → GroupedOrdersP ρ ts ks) := none

def QueryP.groupBy (q : QueryP ρ ts s) (keys : RowP ρ ts s → RowP ρ ts ks)
    (nonempty : ks ≠ [] := by simp) : GroupedQueryP ρ ts s ks :=
  ⟨q, keys, nonempty, none, none⟩

def GroupedQueryP.having (g : GroupedQueryP ρ ts s ks)
    (p : ∀ {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → GroupExprP κ ρ ts ks ⟨.bool, n⟩) :
    GroupedQueryP ρ ts s ks :=
  { g with having? := some fun r => (p (κ := Unit) (keyRow ks) ⟨r⟩).anyNull.raw }

def GroupedQueryP.orderBy (g : GroupedQueryP ρ ts s ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → List (GroupOrderKeyP κ ρ ts ks)) :
    GroupedQueryP ρ ts s ks :=
  { g with order? := some fun r => lowerOrders (f (κ := Unit) (keyRow ks) ⟨r⟩) }

def GroupedQueryP.select (g : GroupedQueryP ρ ts s ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → GroupRowP κ ρ ts ks out) : QueryP ρ ts out :=
  .spine (g.query.asPlainSpine.dropOrders.bind fun r =>
    .groupYield (g.keys r) g.nonempty (lowerHaving (g.having?.map (· r)))
      ((g.order?.map (· r)).getD .nil) (f (κ := Unit) (keyRow ks) ⟨r⟩).raw)

structure GroupedB (ts : Ctx) (s ks : Schema) : Type 1 where
  private mk ::
  private runAt : ∀ ρ : Schema → Type, GroupedQueryP ρ ts s ks

def QueryB.groupBy (q : QueryB ts s) (keys : ∀ {ρ}, RowP ρ ts s → RowP ρ ts ks)
    (nonempty : ks ≠ [] := by simp) : GroupedB ts s ks :=
  ⟨fun ρ => QueryP.groupBy (q ρ) keys nonempty⟩

def GroupedB.having (g : GroupedB ts s ks)
    (p : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → GroupExprP κ ρ ts ks ⟨.bool, n⟩) :
    GroupedB ts s ks := ⟨fun ρ => (g.runAt ρ).having p⟩

def GroupedB.orderBy (g : GroupedB ts s ks)
    (f : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → List (GroupOrderKeyP κ ρ ts ks)) :
    GroupedB ts s ks := ⟨fun ρ => (g.runAt ρ).orderBy f⟩

def GroupedB.select (g : GroupedB ts s ks)
    (f : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks ks → GroupAggP κ ρ ts ks s → GroupRowP κ ρ ts ks out) : Query ts out :=
  fun ρ => (g.runAt ρ).select f

end LeanLinq
