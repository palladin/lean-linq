import LeanLinq.Core.Query
import LeanLinq.Notation

/-! Grouped expressions form a separate, phase-indexed language. Only named
keys, aggregate results, and literals enter it; no ordinary row expression
can be injected, and grouped results cannot escape back into row expressions.
The private lowering keeps the existing raw query algebra unchanged. -/

namespace LeanLinq

/-- A grouped scalar. Construction from and extraction to ordinary SQL
expressions are intentionally private; κ belongs to one grouped callback. -/
structure GroupExprP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (c : SqlType) where
  private mk ::
  private raw : SqlExprP ρ ts c

namespace GroupExprP

def widen (e : GroupExprP κ ρ ts ⟨t, false⟩) : GroupExprP κ ρ ts ⟨t, true⟩ :=
  ⟨.widen e.raw⟩
instance : Coe (GroupExprP κ ρ ts ⟨t, false⟩) (GroupExprP κ ρ ts ⟨t, true⟩) := ⟨widen⟩

def anyNull : {n : Bool} → GroupExprP κ ρ ts ⟨t, n⟩ → GroupExprP κ ρ ts ⟨t, true⟩
  | true, e => e
  | false, e => e.widen

def atFlag (n : Bool) (e : GroupExprP κ ρ ts ⟨t, false⟩) : GroupExprP κ ρ ts ⟨t, n⟩ :=
  match n with
  | false => e
  | true => e.widen

def int (i : Int) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.int, n⟩ :=
  ⟨fits.fit (.intC i)⟩
def long (i : Int) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.long, n⟩ :=
  ⟨fits.fit (.longC i)⟩
def dbl (v : Float) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.double, n⟩ :=
  ⟨fits.fit (.doubleC v)⟩
def dec (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.decimal, n⟩ :=
  ⟨fits.fit (.decimalC v)⟩
def str (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.string, n⟩ :=
  ⟨fits.fit (.stringC v)⟩
def bool (v : Bool) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.bool, n⟩ :=
  ⟨fits.fit (.boolC v)⟩
def dt (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.dateTime, n⟩ :=
  ⟨fits.fit (.dateTimeC v)⟩
def gd (v : String) {n : Bool} [fits : FlagFits false n] : GroupExprP κ ρ ts ⟨.guid, n⟩ :=
  ⟨fits.fit (.guidC v)⟩
def null (t : SqlPrim) : GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.nullC t⟩
def param (name : String) {pt : SqlPrim} {pn n : Bool}
    [HasParam ts.params name ⟨pt, pn⟩] [fits : FlagFits pn n]
    (h : name.isReservedParamName = false := by decide) : GroupExprP κ ρ ts ⟨pt, n⟩ :=
  ⟨SqlExpr.param name h⟩

def arith (op : ArithOp) [SqlNumeric c.ty]
    (a b : GroupExprP κ ρ ts c) : GroupExprP κ ρ ts c := ⟨.arith op a.raw b.raw⟩
instance [SqlNumeric t] : Add (GroupExprP κ ρ ts ⟨t, n⟩) := ⟨arith .add⟩
instance [SqlNumeric t] : Sub (GroupExprP κ ρ ts ⟨t, n⟩) := ⟨arith .sub⟩
instance [SqlNumeric t] : Mul (GroupExprP κ ρ ts ⟨t, n⟩) := ⟨arith .mul⟩
instance [SqlNumeric t] : Div (GroupExprP κ ρ ts ⟨t, n⟩) := ⟨arith .div⟩
instance : OfNat (GroupExprP κ ρ ts ⟨.int, n⟩) k := ⟨atFlag n ⟨.intC k⟩⟩
instance : OfNat (GroupExprP κ ρ ts ⟨.long, n⟩) k := ⟨atFlag n ⟨.longC k⟩⟩
instance : Neg (GroupExprP κ ρ ts ⟨.int, n⟩) := ⟨fun e => 0 - e⟩
instance : OfScientific (GroupExprP κ ρ ts ⟨.decimal, n⟩) :=
  ⟨fun m sign e => ⟨OfScientific.ofScientific m sign e⟩⟩
instance : OfScientific (GroupExprP κ ρ ts ⟨.double, n⟩) :=
  ⟨fun m sign e => ⟨OfScientific.ofScientific m sign e⟩⟩
instance : Coe String (GroupExprP κ ρ ts ⟨.string, true⟩) := ⟨fun v => ⟨.widen (.stringC v)⟩⟩
instance : Coe Bool (GroupExprP κ ρ ts ⟨.bool, true⟩) := ⟨fun v => ⟨.widen (.boolC v)⟩⟩
instance (priority := high) : Coe String (GroupExprP κ ρ ts ⟨.string, false⟩) := ⟨fun v => ⟨.stringC v⟩⟩
instance (priority := high) : Coe Bool (GroupExprP κ ρ ts ⟨.bool, false⟩) := ⟨fun v => ⟨.boolC v⟩⟩

def concat (a b : GroupExprP κ ρ ts ⟨.string, n⟩) : GroupExprP κ ρ ts ⟨.string, n⟩ :=
  ⟨.concat a.raw b.raw⟩
instance : Append (GroupExprP κ ρ ts ⟨.string, n⟩) := ⟨concat⟩
def cmp (op : CmpOp) (a b : GroupExprP κ ρ ts ⟨t, true⟩) : GroupExprP κ ρ ts ⟨.bool, true⟩ :=
  ⟨.cmp op a.raw b.raw⟩
def and (a : GroupExprP κ ρ ts ⟨.bool, n₁⟩) (b : GroupExprP κ ρ ts ⟨.bool, n₂⟩) :
    GroupExprP κ ρ ts ⟨.bool, n₁ || n₂⟩ := ⟨.and a.raw b.raw⟩
def or (a : GroupExprP κ ρ ts ⟨.bool, n₁⟩) (b : GroupExprP κ ρ ts ⟨.bool, n₂⟩) :
    GroupExprP κ ρ ts ⟨.bool, n₁ || n₂⟩ := ⟨.or a.raw b.raw⟩
def not (a : GroupExprP κ ρ ts ⟨.bool, n⟩) : GroupExprP κ ρ ts ⟨.bool, n⟩ := ⟨.not a.raw⟩
def isNull (e : GroupExprP κ ρ ts c) : GroupExprP κ ρ ts .bool := ⟨.isNull e.raw⟩
def isNotNull (e : GroupExprP κ ρ ts c) : GroupExprP κ ρ ts .bool := ⟨.isNotNull e.raw⟩
def like (e p : GroupExprP κ ρ ts ⟨.string, true⟩) : GroupExprP κ ρ ts ⟨.bool, true⟩ :=
  ⟨.like e.raw p.raw⟩
def caseWhen (p : GroupExprP κ ρ ts ⟨.bool, np⟩)
    (a b : GroupExprP κ ρ ts ⟨t, true⟩) : GroupExprP κ ρ ts ⟨t, true⟩ :=
  ⟨.caseWhen p.raw a.raw b.raw⟩
def inValues (e : GroupExprP κ ρ ts ⟨t, n⟩) (vs : List (GroupExprP κ ρ ts ⟨t, true⟩)) :
    GroupExprP κ ρ ts ⟨.bool, true⟩ := ⟨e.raw.inValues (vs.map (·.raw))⟩
def notInValues (e : GroupExprP κ ρ ts ⟨t, n⟩) (vs : List (GroupExprP κ ρ ts ⟨t, true⟩)) :
    GroupExprP κ ρ ts ⟨.bool, true⟩ := (e.inValues vs).not
def abs (e : GroupExprP κ ρ ts c) [SqlNumeric c.ty] : GroupExprP κ ρ ts c := ⟨.abs e.raw⟩
def round (e : GroupExprP κ ρ ts c) (digits : Int) [SqlNumeric c.ty] : GroupExprP κ ρ ts c :=
  ⟨.round e.raw digits⟩
def ceiling (e : GroupExprP κ ρ ts c) [SqlNumeric c.ty] : GroupExprP κ ρ ts c := ⟨.ceiling e.raw⟩
def floor (e : GroupExprP κ ρ ts c) [SqlNumeric c.ty] : GroupExprP κ ρ ts c := ⟨.floor e.raw⟩
def substring (e : GroupExprP κ ρ ts ⟨.string, n⟩) (start : Int) (len : Nat) : GroupExprP κ ρ ts ⟨.string, n⟩ :=
  ⟨.substring e.raw start len⟩
def upper (e : GroupExprP κ ρ ts ⟨.string, n⟩) : GroupExprP κ ρ ts ⟨.string, n⟩ := ⟨.upper e.raw⟩
def lower (e : GroupExprP κ ρ ts ⟨.string, n⟩) : GroupExprP κ ρ ts ⟨.string, n⟩ := ⟨.lower e.raw⟩
def trim (e : GroupExprP κ ρ ts ⟨.string, n⟩) : GroupExprP κ ρ ts ⟨.string, n⟩ := ⟨.trim e.raw⟩
def length (e : GroupExprP κ ρ ts ⟨.string, n⟩) : GroupExprP κ ρ ts ⟨.int, n⟩ := ⟨.length e.raw⟩
def now : GroupExprP κ ρ ts .dateTime := ⟨.now⟩
def year (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ⟨.int, n⟩ := ⟨e.raw.year⟩
def month (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ⟨.int, n⟩ := ⟨e.raw.month⟩
def day (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) : GroupExprP κ ρ ts ⟨.int, n⟩ := ⟨e.raw.day⟩
def addDays (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ⟨.dateTime, n⟩ := ⟨e.raw.addDays k⟩
def addMonths (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ⟨.dateTime, n⟩ := ⟨e.raw.addMonths k⟩
def addYears (e : GroupExprP κ ρ ts ⟨.dateTime, n⟩) (k : Int) : GroupExprP κ ρ ts ⟨.dateTime, n⟩ := ⟨e.raw.addYears k⟩

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

structure GroupCellP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (name : String) (c : SqlType) where
  expr : GroupExprP κ ρ ts c
def GroupExprP.as (e : GroupExprP κ ρ ts c) (name : String) : GroupCellP κ ρ ts name c := ⟨e⟩

structure GroupRowP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (s : Schema) where
  private mk ::
  private raw : RowP ρ ts s
def GroupRowP.nil : GroupRowP κ ρ ts [] := ⟨.nil⟩
def GroupRowP.consCell (cell : GroupCellP κ ρ ts name c) (r : GroupRowP κ ρ ts s) :
    GroupRowP κ ρ ts ((name, c) :: s) := ⟨.cons cell.expr.raw r.raw⟩
def GroupRowP.col (r : GroupRowP κ ρ ts s) (name : String) [i : HasCol s name c] :
    GroupExprP κ ρ ts c := ⟨i.getImpl r.raw⟩
def GroupRowP.append (a : GroupRowP κ ρ ts s₁) (b : GroupRowP κ ρ ts s₂) :
    GroupRowP κ ρ ts (s₁ ++ s₂) := ⟨a.raw.append b.raw⟩
instance : HAppend (GroupRowP κ ρ ts s₁) (GroupRowP κ ρ ts s₂) (GroupRowP κ ρ ts (s₁ ++ s₂)) :=
  ⟨GroupRowP.append⟩

structure GroupOrderKeyP (κ : Type) (ρ : Schema → Type) (ts : Ctx) where
  private mk ::
  private raw : OrderKeyP ρ ts
def GroupExprP.asc (e : GroupExprP κ ρ ts c) : GroupOrderKeyP κ ρ ts := ⟨e.raw.asc⟩
def GroupExprP.desc (e : GroupExprP κ ρ ts c) : GroupOrderKeyP κ ρ ts := ⟨e.raw.desc⟩

/-- The comprehension aggregate capability accepts only ordinary row
expressions. Its private constructor is available only inside a grouped scope. -/
structure GroupAggregateP (κ : Type) (ρ : Schema → Type) (ts : Ctx) where
  private mk ::
def GroupAggregateP.count (_ : GroupAggregateP κ ρ ts) : GroupExprP κ ρ ts ⟨.int, true⟩ :=
  ⟨.widen .countAll⟩
def GroupAggregateP.sum (_ : GroupAggregateP κ ρ ts) (e : SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .sum e⟩
def GroupAggregateP.avg (_ : GroupAggregateP κ ρ ts) (e : SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .avg e⟩
def GroupAggregateP.min (_ : GroupAggregateP κ ρ ts) (e : SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .min e⟩
def GroupAggregateP.max (_ : GroupAggregateP κ ρ ts) (e : SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .max e⟩

/-- Pipeline aggregate selectors receive the original input row. They cannot
return a grouped expression, so nested aggregation is a type error. -/
structure GroupAggP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (s : Schema) where
  private mk ::
  private source : RowP ρ ts s
def GroupAggP.count (_ : GroupAggP κ ρ ts s) : GroupExprP κ ρ ts ⟨.int, true⟩ := ⟨.widen .countAll⟩
def GroupAggP.sum (a : GroupAggP κ ρ ts s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .sum (f a.source)⟩
def GroupAggP.avg (a : GroupAggP κ ρ ts s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) [SqlNumeric t] :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .avg (f a.source)⟩
def GroupAggP.min (a : GroupAggP κ ρ ts s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .min (f a.source)⟩
def GroupAggP.max (a : GroupAggP κ ρ ts s) (f : RowP ρ ts s → SqlExprP ρ ts ⟨t, n⟩) :
    GroupExprP κ ρ ts ⟨t, true⟩ := ⟨.aggE .max (f a.source)⟩

structure GroupedClauseP (κ : Type) (ρ : Schema → Type) (ts : Ctx) (s : Schema) where
  row : GroupRowP κ ρ ts s
  having? : Option (GroupExprP κ ρ ts ⟨.bool, true⟩) := none
  order : List (GroupOrderKeyP κ ρ ts) := []

private def rowKeys : {s : Schema} → RowP ρ ts s → List (KeyExprP ρ ts)
  | [], .nil => []
  | (_, c) :: _, .cons e rest => ⟨c, e⟩ :: rowKeys rest

/-- The same key occurrence is rendered once per grouped statement, so
parameterized computed keys use identical placeholders in SELECT/GROUP BY. -/
private def markKeys : {s : Schema} → Nat → RowP ρ ts s → RowP ρ ts s
  | [], _, .nil => .nil
  | _ :: _, index, .cons e rest => .cons (.groupKey index e) (markKeys (index + 1) rest)

private def lowerGrouped (keys : RowP ρ ts ks) (h : ks ≠ [])
    (having? : Option (SqlExprP ρ ts ⟨.bool, true⟩))
    (order : List (OrderKeyP ρ ts)) (row : RowP ρ ts out) : SpineQP ρ ts .grouped out :=
  match ks, keys with
  | [], .nil => False.elim (h rfl)
  | (_, c) :: _, .cons e rest => .groupYield ⟨c, e⟩ (rowKeys rest) having? order row

def groupYieldR (keys : RowP ρ ts ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks → GroupAggregateP κ ρ ts → GroupedClauseP κ ρ ts out)
    (nonempty : ks ≠ [] := by simp) : SpineQP ρ ts .grouped out :=
  let marked := markKeys 0 keys
  let clause := f (κ := Unit) ⟨marked⟩ ⟨⟩
  lowerGrouped marked nonempty (clause.having?.map (·.raw)) (clause.order.map (·.raw)) clause.row.raw

structure GroupedQueryP (ρ : Schema → Type) (ts : Ctx) (s ks : Schema) where
  private mk ::
  private query : QueryP ρ ts s
  private keys : RowP ρ ts s → RowP ρ ts ks
  private nonempty : ks ≠ []
  private having? : Option (RowP ρ ts s → SqlExprP ρ ts ⟨.bool, true⟩) := none
  private order? : Option (RowP ρ ts s → List (OrderKeyP ρ ts)) := none

def QueryP.groupBy (q : QueryP ρ ts s) (keys : RowP ρ ts s → RowP ρ ts ks)
    (nonempty : ks ≠ [] := by simp) : GroupedQueryP ρ ts s ks :=
  ⟨q, keys, nonempty, none, none⟩

def GroupedQueryP.having (g : GroupedQueryP ρ ts s ks)
    (p : ∀ {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → GroupExprP κ ρ ts ⟨.bool, n⟩) :
    GroupedQueryP ρ ts s ks :=
  { g with having? := some fun r => (p (κ := Unit) ⟨markKeys 0 (g.keys r)⟩ ⟨r⟩).anyNull.raw }

def GroupedQueryP.orderBy (g : GroupedQueryP ρ ts s ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → List (GroupOrderKeyP κ ρ ts)) :
    GroupedQueryP ρ ts s ks :=
  { g with order? := some fun r => (f (κ := Unit) ⟨markKeys 0 (g.keys r)⟩ ⟨r⟩).map (·.raw) }

def GroupedQueryP.select (g : GroupedQueryP ρ ts s ks)
    (f : ∀ {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → GroupRowP κ ρ ts out) : QueryP ρ ts out :=
  .spine (g.query.asPlainSpine.dropOrders.bind fun r =>
    lowerGrouped (markKeys 0 (g.keys r)) g.nonempty (g.having?.map (· r)) ((g.order?.map (· r)).getD [])
      (f (κ := Unit) ⟨markKeys 0 (g.keys r)⟩ ⟨r⟩).raw)

structure GroupedB (ts : Ctx) (s ks : Schema) : Type 1 where
  private mk ::
  private runAt : ∀ ρ : Schema → Type, GroupedQueryP ρ ts s ks

def QueryB.groupBy (q : QueryB ts s) (keys : ∀ {ρ}, RowP ρ ts s → RowP ρ ts ks)
    (nonempty : ks ≠ [] := by simp) : GroupedB ts s ks :=
  ⟨fun ρ => QueryP.groupBy (q ρ) keys nonempty⟩

def GroupedB.having (g : GroupedB ts s ks)
    (p : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → GroupExprP κ ρ ts ⟨.bool, n⟩) :
    GroupedB ts s ks := ⟨fun ρ => (g.runAt ρ).having p⟩

def GroupedB.orderBy (g : GroupedB ts s ks)
    (f : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → List (GroupOrderKeyP κ ρ ts)) :
    GroupedB ts s ks := ⟨fun ρ => (g.runAt ρ).orderBy f⟩

def GroupedB.select (g : GroupedB ts s ks)
    (f : ∀ {ρ} {κ : Type}, GroupRowP κ ρ ts ks → GroupAggP κ ρ ts s → GroupRowP κ ρ ts out) : Query ts out :=
  fun ρ => (g.runAt ρ).select f

end LeanLinq
