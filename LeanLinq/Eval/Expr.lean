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
  | .div => if b == 0 then .error .divByZero else pure (some (a.tdiv b))

/-- Arithmetic per SQL type. Decimals are milli-units, so multiplication
rescales and division pre-scales; integer and decimal division truncate
toward zero (`Int.tdiv` — SQL's direction, not Lean's Euclidean `/`);
division by zero is an `EvalError`, not NULL — for doubles too (the
PostgreSQL/SQL Server behavior; SQLite yields NULL instead). -/
def SqlPrim.arithV : (t : SqlPrim) → ArithOp → t.interp → t.interp →
    Except EvalError (Nullable t)
  | .int, op, a, b => intArith op a b
  | .long, op, a, b => intArith op a b
  | .double, op, a, b =>
      match op with
      | .add => pure (some (a + b))
      | .sub => pure (some (a - b))
      | .mul => pure (some (a * b))
      | .div => if b == 0.0 then .error .divByZero else pure (some (a / b))
  | .decimal, op, a, b =>
      match op with
      | .add => pure (some (a + b))
      | .sub => pure (some (a - b))
      | .mul => pure (some ((a * b).tdiv 1000))
      | .div => if b == 0 then .error .divByZero else pure (some ((a * 1000).tdiv b))
  | t, op, _, _ => .error (.unsupported s!"arith {repr op}" t)

private def SqlPrim.sumV : (t : SqlPrim) → List t.interp → Except EvalError (Nullable t)
  | .int, vs => pure (some (vs.foldl (· + ·) 0))
  | .long, vs => pure (some (vs.foldl (· + ·) 0))
  | .double, vs => pure (some (vs.foldl (· + ·) 0))
  | .decimal, vs => pure (some (vs.foldl (· + ·) 0))
  | t, _ => .error (.unsupported "SUM" t)

private def SqlPrim.avgV : (t : SqlPrim) → List t.interp → Except EvalError (Nullable t)
  | .int, vs => pure (some ((vs.foldl (· + ·) 0).tdiv vs.length))
  | .long, vs => pure (some ((vs.foldl (· + ·) 0).tdiv vs.length))
  | .double, vs => pure (some (vs.foldl (· + ·) 0 / Float.ofNat vs.length))
  | .decimal, vs => pure (some ((vs.foldl (· + ·) 0).tdiv vs.length))
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
def strict1 (x? : Nullable a)
    (f : a.interp → Except EvalError (Nullable b)) : Except EvalError (Nullable b) :=
  match x? with
  | none => pure none
  | some x => f x

/-- Apply a strict binary SQL operation: any NULL operand yields NULL. -/
def strict2 (x? y? : Nullable a)
    (f : a.interp → a.interp → Except EvalError (Nullable b)) : Except EvalError (Nullable b) :=
  match x?, y? with
  | some x, some y => f x y
  | _, _ => pure none

end LeanLinq
