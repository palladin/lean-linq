import LeanLinq.Core.Schema

/-! # Expression evaluation

`SqlExpr.evalG` interprets a staged expression over a *list* of environments
— the members of the current group. Plain (ungrouped) contexts pass a
singleton list; grouped contexts pass one environment per group member, and
an aggregate node folds its argument's per-member values while every other
node simply threads the list through (bare columns read the first member,
SQL's bare-column-in-group semantics). This is what makes aggregates nested
anywhere inside an expression (`COUNT(*) > 1`, `SUM(x) DESC`) evaluate
without any special-casing at use sites.

Three-valued logic throughout: `none` is SQL NULL. Comparisons with NULL are
NULL, `AND`/`OR` are Kleene, `NOT NULL` is NULL, and a `WHERE`/`HAVING`/`ON`
keeps a row only when its predicate is `some true`. -/

namespace LeanLinq

/-- Does an `Ordering` satisfy a comparison operator? -/
def CmpOp.holds (op : CmpOp) (o : Ordering) : Bool :=
  match op with
  | .eq => o == .eq
  | .ne => o != .eq
  | .lt => o == .lt
  | .le => o != .gt
  | .gt => o == .gt
  | .ge => o != .lt

private def intArith (op : ArithOp) (a b : Int) : Option Int :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  | .div => if b == 0 then none else some (a / b)

/-- Arithmetic per SQL type. Decimals are milli-units, so multiplication
rescales and division pre-scales; integer division truncates toward zero. -/
def SqlType.arithV : (t : SqlType) → ArithOp → t.interp → t.interp → Option t.interp
  | .int, op, a, b => intArith op a b
  | .long, op, a, b => intArith op a b
  | .double, op, a, b =>
      some (match op with
        | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b)
  | .decimal, op, a, b =>
      match op with
      | .add => some (a + b)
      | .sub => some (a - b)
      | .mul => some (a * b / 1000)
      | .div => if b == 0 then none else some (a * 1000 / b)
  | .string, _, _, _ => none
  | .bool, _, _, _ => none
  | .dateTime, _, _, _ => none
  | .guid, _, _, _ => none

private def SqlType.sumV : (t : SqlType) → List t.interp → Option t.interp
  | .int, vs => some (vs.foldl (· + ·) 0)
  | .long, vs => some (vs.foldl (· + ·) 0)
  | .double, vs => some (vs.foldl (· + ·) 0)
  | .decimal, vs => some (vs.foldl (· + ·) 0)
  | _, _ => none

private def SqlType.avgV : (t : SqlType) → List t.interp → Option t.interp
  | .int, vs => some (vs.foldl (· + ·) 0 / vs.length)
  | .long, vs => some (vs.foldl (· + ·) 0 / vs.length)
  | .double, vs => some (vs.foldl (· + ·) 0 / Float.ofNat vs.length)
  | .decimal, vs => some (vs.foldl (· + ·) 0 / vs.length)
  | _, _ => none

/-- Fold an aggregate over the non-NULL values of a group (SQL semantics:
NULLs are ignored, an all-NULL/empty group aggregates to NULL). MIN/MAX use
the column order, so they work for every type; SUM/AVG only for numeric. -/
def SqlType.aggV : (t : SqlType) → AggOp → List t.interp → Option t.interp
  | _, _, [] => none
  | t, .min, v :: vs => some (vs.foldl (fun acc x => if t.cmpV x acc == .lt then x else acc) v)
  | t, .max, v :: vs => some (vs.foldl (fun acc x => if t.cmpV x acc == .gt then x else acc) v)
  | t, .sum, vs => t.sumV vs
  | t, .avg, vs => t.avgV vs

def SqlType.absV : (t : SqlType) → t.interp → Option t.interp
  | .int, a => some (a.natAbs : Int)
  | .long, a => some (a.natAbs : Int)
  | .double, a => some a.abs
  | .decimal, a => some (a.natAbs : Int)
  | _, _ => none

def SqlType.roundV : (t : SqlType) → Int → t.interp → Option t.interp
  | .int, _, a => some a
  | .long, _, a => some a
  | .decimal, d, a => some (decimalRound d.toNat a)
  | _, _, _ => none

def SqlType.ceilV : (t : SqlType) → t.interp → Option t.interp
  | .int, a => some a
  | .long, a => some a
  | .decimal, a => some (decimalCeil a)
  | _, _ => none

def SqlType.floorV : (t : SqlType) → t.interp → Option t.interp
  | .int, a => some a
  | .long, a => some a
  | .decimal, a => some (decimalFloor a)
  | _, _ => none

mutual

/-- Evaluate an expression over the environments of the current group
(singleton = ungrouped row context). -/
def SqlExpr.evalG (ee : EvalEnv ts) : List Scope → SqlExpr ts t → Option t.interp
  | _, .intC i => some i
  | _, .longC i => some i
  | _, .doubleC f => some f
  | _, .decimalC d => some (parseDecimal d)
  | _, .stringC s => some s
  | _, .boolC b => some b
  | _, .dateTimeC s => some (normDateTime s)
  | _, .guidC g => some g.toLower
  | _, .nullC _ => none
  | _, .param (inst := i) _ => i.get ee.params
  | envs, .field t' alias name => envs.head?.bind fun env => env.get? alias name t'
  | envs, .arith op a b => do
      let x ← a.evalG ee envs
      let y ← b.evalG ee envs
      t.arithV op x y
  | envs, .concat a b => do
      let x ← a.evalG ee envs
      let y ← b.evalG ee envs
      pure (x ++ y)
  | envs, .cmp (t := t₀) op a b => do
      let x ← a.evalG ee envs
      let y ← b.evalG ee envs
      pure (op.holds (t₀.cmpV x y))
  | envs, .and a b =>
      match a.evalG ee envs, b.evalG ee envs with
      | some false, _ => some false
      | _, some false => some false
      | some true, some true => some true
      | _, _ => none
  | envs, .or a b =>
      match a.evalG ee envs, b.evalG ee envs with
      | some true, _ => some true
      | _, some true => some true
      | some false, some false => some false
      | _, _ => none
  | envs, .not a => (a.evalG ee envs).map (!·)
  | envs, .isNull e => some (e.evalG ee envs).isNone
  | envs, .isNotNull e => some (e.evalG ee envs).isSome
  | envs, .like e p => do
      let s ← e.evalG ee envs
      let pat ← p.evalG ee envs
      pure (likeMatch s pat)
  | envs, .inList (t := t₀) e es =>
      match e.evalG ee envs with
      | none => none
      | some v =>
          let hits := (SqlExpr.evalGList ee envs es).map fun ⟨u, c⟩ =>
            if h : u = t₀ then (h ▸ c).map (fun w => t₀.cmpV v w == Ordering.eq)
            else some false
          if hits.any (· == some true) then some true
          else if hits.any (·.isNone) then none
          else some false
  | envs, .inSub (t := t₀) e sq =>
      match e.evalG ee envs with
      | none => none
      | some v =>
          let hits := (sq.eval ee).map (·.map (fun w => t₀.cmpV v w == Ordering.eq))
          if hits.any (· == some true) then some true
          else if hits.any (·.isNone) then none
          else some false
  | _, .scalarSub sq =>
      match sq.eval ee with
      | c :: _ => c
      | [] => none
  | envs, .caseWhen c a b =>
      if c.evalG ee envs == some true then a.evalG ee envs else b.evalG ee envs
  | envs, .aggE op e =>
      t.aggV op ((envs.map fun env => e.evalG ee [env]).filterMap id)
  | envs, .countAll => some (envs.length : Int)
  | envs, .abs e => (e.evalG ee envs).bind t.absV
  | envs, .round e digits => (e.evalG ee envs).bind (t.roundV digits)
  | envs, .ceiling e => (e.evalG ee envs).bind t.ceilV
  | envs, .floor e => (e.evalG ee envs).bind t.floorV
  | envs, .substring e start len => (e.evalG ee envs).map (sqlSubstring · start len)
  | envs, .upper e => (e.evalG ee envs).map (·.toUpper)
  | envs, .lower e => (e.evalG ee envs).map (·.toLower)
  | envs, .trim e => (e.evalG ee envs).map (·.trimAscii.toString)
  | envs, .length e => (e.evalG ee envs).map (fun s => (s.length : Int))
  | _, .now => ee.now
  | envs, .datePart u e =>
      (e.evalG ee envs).map fun s =>
        match u with
        | .year => (parseYMD s).1
        | .month => (parseYMD s).2.1
        | .day => (parseYMD s).2.2
  | envs, .dateAdd u e n =>
      (e.evalG ee envs).map fun s =>
        match u with
        | .day => dateAddDays s n
        | .month => dateAddMonths s n
        | .year => dateAddYears s n
  | envs, .dateDiff u a b => do
      let x ← a.evalG ee envs
      let y ← b.evalG ee envs
      pure (match u with
        | .day => dateDiffDays x y
        | .month => dateDiffMonths x y
        | .year => dateDiffYears x y)

def SqlExpr.evalGList (ee : EvalEnv ts) (envs : List Scope) :
    List ((u : SqlType) × SqlExpr ts u) → List ((u : SqlType) × Option u.interp)
  | [] => []
  | ⟨u, e⟩ :: es => ⟨u, e.evalG ee envs⟩ :: SqlExpr.evalGList ee envs es

end

/-- Evaluate every cell of a projected row. -/
def Row.evalRow (ee : EvalEnv ts) (envs : List Scope) : {s : Schema} → Row ts s → Values s
  | _, .nil => .nil
  | _, .cons e r => .cons (e.evalG ee envs) (r.evalRow ee envs)

end LeanLinq
