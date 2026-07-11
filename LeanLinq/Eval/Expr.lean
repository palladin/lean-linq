import LeanLinq.Core.Schema

/-! # Expression evaluation

`SqlExpr.evalG` interprets a staged expression over a *list* of scopes — the
members of the current group. Plain (ungrouped) contexts pass a singleton
list; grouped contexts pass one scope per group member, and an aggregate
node folds its argument's per-member values while every other node simply
threads the list through (bare columns read the first member, SQL's
bare-column-in-group semantics). This is what makes aggregates nested
anywhere inside an expression (`COUNT(*) > 1`, `SUM(x) DESC`) evaluate
without any special-casing at use sites.

Two result channels, never conflated:

- **NULL** is `Nullable`'s `none` — three-valued logic throughout:
  comparisons with NULL are NULL, `AND`/`OR` are Kleene, `NOT NULL` is NULL,
  and a `WHERE`/`HAVING`/`ON` keeps a row only when its predicate is
  `some true`.
- **Errors** are `Except.error` — the statement-aborting channel: division
  by zero, `now` without a clock, operations the evaluator does not
  implement (`unsupported`), and internally-unreachable states
  (`internal`). Operands of strict operators are evaluated before the
  operator applies (so an erroring operand aborts even under Kleene
  short-circuits — engines do not guarantee boolean short-circuiting
  either); `CASE WHEN` remains lazy in its branches, as in SQL, so
  `caseWhen (x ==. 0) fallback (y / x)` does not divide by zero. -/

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

private def intArith (op : ArithOp) (a b : Int) : Except EvalError (Nullable .int) :=
  match op with
  | .add => pure (some (a + b))
  | .sub => pure (some (a - b))
  | .mul => pure (some (a * b))
  | .div => if b == 0 then .error .divByZero else pure (some (a / b))

/-- Arithmetic per SQL type. Decimals are milli-units, so multiplication
rescales and division pre-scales; integer division truncates toward zero;
division by zero is an `EvalError`, not NULL. -/
def SqlPrim.arithV : (t : SqlPrim) → ArithOp → t.interp → t.interp →
    Except EvalError (Nullable t)
  | .int, op, a, b => intArith op a b
  | .long, op, a, b => intArith op a b
  | .double, op, a, b =>
      pure (some (match op with
        | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b))
  | .decimal, op, a, b =>
      match op with
      | .add => pure (some (a + b))
      | .sub => pure (some (a - b))
      | .mul => pure (some (a * b / 1000))
      | .div => if b == 0 then .error .divByZero else pure (some (a * 1000 / b))
  | t, op, _, _ => .error (.unsupported s!"arith {repr op}" t)

private def SqlPrim.sumV : (t : SqlPrim) → List t.interp → Except EvalError (Nullable t)
  | .int, vs => pure (some (vs.foldl (· + ·) 0))
  | .long, vs => pure (some (vs.foldl (· + ·) 0))
  | .double, vs => pure (some (vs.foldl (· + ·) 0))
  | .decimal, vs => pure (some (vs.foldl (· + ·) 0))
  | t, _ => .error (.unsupported "SUM" t)

private def SqlPrim.avgV : (t : SqlPrim) → List t.interp → Except EvalError (Nullable t)
  | .int, vs => pure (some (vs.foldl (· + ·) 0 / vs.length))
  | .long, vs => pure (some (vs.foldl (· + ·) 0 / vs.length))
  | .double, vs => pure (some (vs.foldl (· + ·) 0 / Float.ofNat vs.length))
  | .decimal, vs => pure (some (vs.foldl (· + ·) 0 / vs.length))
  | t, _ => .error (.unsupported "AVG" t)

/-- Fold an aggregate over the non-NULL values of a group (SQL semantics:
NULLs are ignored, an all-NULL/empty group aggregates to NULL). MIN/MAX use
the column order, so they work for every type; SUM/AVG only for numeric. -/
def SqlPrim.aggV : (t : SqlPrim) → AggOp → List t.interp → Except EvalError (Nullable t)
  | _, _, [] => pure none
  | t, .min, v :: vs =>
      pure (some (vs.foldl (fun acc x => if t.cmpV x acc == .lt then x else acc) v))
  | t, .max, v :: vs =>
      pure (some (vs.foldl (fun acc x => if t.cmpV x acc == .gt then x else acc) v))
  | t, .sum, vs => t.sumV vs
  | t, .avg, vs => t.avgV vs

def SqlPrim.absV : (t : SqlPrim) → t.interp → Except EvalError (Nullable t)
  | .int, a => pure (some (a.natAbs : Int))
  | .long, a => pure (some (a.natAbs : Int))
  | .double, a => pure (some a.abs)
  | .decimal, a => pure (some (a.natAbs : Int))
  | t, _ => .error (.unsupported "ABS" t)

def SqlPrim.roundV : (t : SqlPrim) → Int → t.interp → Except EvalError (Nullable t)
  | .int, _, a => pure (some a)
  | .long, _, a => pure (some a)
  | .decimal, d, a => pure (some (decimalRound d.toNat a))
  | t, _, _ => .error (.unsupported "ROUND" t)

def SqlPrim.ceilV : (t : SqlPrim) → t.interp → Except EvalError (Nullable t)
  | .int, a => pure (some a)
  | .long, a => pure (some a)
  | .decimal, a => pure (some (decimalCeil a))
  | t, _ => .error (.unsupported "CEILING" t)

def SqlPrim.floorV : (t : SqlPrim) → t.interp → Except EvalError (Nullable t)
  | .int, a => pure (some a)
  | .long, a => pure (some a)
  | .decimal, a => pure (some (decimalFloor a))
  | t, _ => .error (.unsupported "FLOOR" t)

/-- Apply a strict unary SQL operation: NULL in, NULL out; errors pass. -/
private def strict1 (x? : Nullable a)
    (f : a.interp → Except EvalError (Nullable b)) : Except EvalError (Nullable b) :=
  match x? with
  | none => pure none
  | some x => f x

/-- Apply a strict binary SQL operation: any NULL operand yields NULL. -/
private def strict2 (x? y? : Nullable a)
    (f : a.interp → a.interp → Except EvalError (Nullable b)) : Except EvalError (Nullable b) :=
  match x?, y? with
  | some x, some y => f x y
  | _, _ => pure none

mutual

/-- Evaluate an expression over the scopes of the current group
(singleton = ungrouped row context). -/
def SqlExpr.evalG (ee : EvalEnv ts) : List Scope → SqlExpr ts ⟨t, n⟩ →
    Except EvalError (Nullable t)
  | _, .intC i => pure (some i)
  | _, .longC i => pure (some i)
  | _, .doubleC f => pure (some f)
  | _, .decimalC d => pure (some (parseDecimal d))
  | _, .stringC s => pure (some s)
  | _, .boolC b => pure (some b)
  | _, .dateTimeC s => pure (some (normDateTime s))
  | _, .guidC g => pure (some g.toLower)
  | _, .nullC _ => pure none
  | _, .paramE (inst := i) _ => pure (SqlType.toNullable (i.get ee.params))
  | scs, .widen e => e.evalG ee scs
  | scs, .field ⟨t', _⟩ alias name =>
      match scs.head? with
      | none => .error (.internal s!"no row in scope for {alias}.{name}")
      | some sc =>
          match sc.get? alias name t' with
          | some cell => pure cell
          | none => .error (.internal s!"unresolved field {alias}.{name}")
  | scs, .arith op a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) (t.arithV op)
  | scs, .concat a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y => pure (some (x ++ y))
  | scs, .cmp (t := t₀) op a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y =>
        pure (some (op.holds (t₀.cmpV x y)))
  | scs, .and a b => do
      pure (match (← a.evalG ee scs), (← b.evalG ee scs) with
        | some false, _ => some false
        | _, some false => some false
        | some true, some true => some true
        | _, _ => none)
  | scs, .or a b => do
      pure (match (← a.evalG ee scs), (← b.evalG ee scs) with
        | some true, _ => some true
        | _, some true => some true
        | some false, some false => some false
        | _, _ => none)
  | scs, .not a => do pure ((← a.evalG ee scs).map (!·))
  | scs, .isNull e => do pure (some (← e.evalG ee scs).isNone)
  | scs, .isNotNull e => do pure (some (← e.evalG ee scs).isSome)
  | scs, .like e p => do
      strict2 (← e.evalG ee scs) (← p.evalG ee scs) fun s pat =>
        pure (some (likeMatch s pat))
  | scs, .inList (c := ⟨t₀, _⟩) e es => do
      match (← e.evalG ee scs) with
      | none => pure none
      | some v =>
          let hits := (← SqlExpr.evalGList ee scs es).map fun ⟨u, cell⟩ =>
            if h : u = t₀ then
              (h ▸ cell).map (fun w => t₀.cmpV v w == Ordering.eq)
            else some false
          pure (if hits.any (· == some true) then some true
                else if hits.any (·.isNone) then none
                else some false)
  | scs, .inSub (t := t₀) e sq => do
      match (← e.evalG ee scs) with
      | none => pure none
      | some v =>
          let hits := (← sq.eval ee).map (·.map (fun w => t₀.cmpV v w == Ordering.eq))
          pure (if hits.any (· == some true) then some true
                else if hits.any (·.isNone) then none
                else some false)
  | _, .scalarSub sq => do
      pure (match (← sq.eval ee) with
        | c :: _ => c
        | [] => none)
  -- CASE is lazy in its branches (SQL semantics): only the taken branch
  -- evaluates, so a guarded division cannot error
  | scs, .caseWhen c a b => do
      if (← c.evalG ee scs) == some true then a.evalG ee scs else b.evalG ee scs
  | scs, .aggE (t := t₁) op e => do
      t₁.aggV op ((← scs.mapM fun sc => e.evalG ee [sc]).filterMap id)
  | scs, .countAll => pure (some (scs.length : Int))
  | scs, .abs e => do strict1 (← e.evalG ee scs) t.absV
  | scs, .round e digits => do strict1 (← e.evalG ee scs) (t.roundV digits)
  | scs, .ceiling e => do strict1 (← e.evalG ee scs) t.ceilV
  | scs, .floor e => do strict1 (← e.evalG ee scs) t.floorV
  | scs, .substring e start len => do
      pure ((← e.evalG ee scs).map (sqlSubstring · start len))
  | scs, .upper e => do pure ((← e.evalG ee scs).map (·.toUpper))
  | scs, .lower e => do pure ((← e.evalG ee scs).map (·.toLower))
  | scs, .trim e => do pure ((← e.evalG ee scs).map (·.trimAscii.toString))
  | scs, .length e => do pure ((← e.evalG ee scs).map (fun s => (s.length : Int)))
  | _, .now =>
      match ee.now with
      | some s => pure (some s)
      | none => .error .noClock
  | scs, .datePart u e => do
      pure ((← e.evalG ee scs).map fun s =>
        match u with
        | .year => (parseYMD s).1
        | .month => (parseYMD s).2.1
        | .day => (parseYMD s).2.2)
  | scs, .dateAdd u e n => do
      pure ((← e.evalG ee scs).map fun s =>
        match u with
        | .day => dateAddDays s n
        | .month => dateAddMonths s n
        | .year => dateAddYears s n)
  | scs, .dateDiff u a b => do
      strict2 (← a.evalG ee scs) (← b.evalG ee scs) fun x y =>
        pure (some (match u with
          | .day => dateDiffDays x y
          | .month => dateDiffMonths x y
          | .year => dateDiffYears x y))

def SqlExpr.evalGList (ee : EvalEnv ts) (scs : List Scope) :
    List ((p : SqlType) × SqlExpr ts p) →
    Except EvalError (List ((u : SqlPrim) × Nullable u))
  | [] => pure []
  | ⟨p, e⟩ :: es => do
      pure (⟨p.ty, ← e.evalG ee scs⟩ :: (← SqlExpr.evalGList ee scs es))

end

/-- Evaluate every cell of a projected row — the construction boundary
where `Nullable` computation results become honest cells: a NOT NULL
column receiving `none` is a loud internal error, never a silent NULL
(unreachable through the public surface: the flag arithmetic guarantees a
strict projection evaluates non-NULL). -/
def Row.evalRow (ee : EvalEnv ts) (scs : List Scope) :
    {s : Schema} → Row ts s → Except EvalError (Values s)
  | _, .nil => pure .nil
  | _, .cons (name := nm) e r => do
      pure (.cons (← SqlType.ofNullable nm _ (← e.evalG ee scs)) (← r.evalRow ee scs))

end LeanLinq
