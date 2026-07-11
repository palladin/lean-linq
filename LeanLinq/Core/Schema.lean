import Lean
import LeanLinq.Core.Expr

namespace LeanLinq

/-- A heterogeneous tuple of SQL expressions indexed by a schema: the staged
value flowing through query combinators (each column is an expression, not a
runtime value — MetaOCaml-style staging). The `ts` index is the ambient
table context of the enclosing query, threaded through every cell.

The column name lives only in the index, so it flows in from the expected type
or from `.as`-tagged cells; see the row-literal syntax below. -/
inductive Row : Ctx → Schema → Type where
  | nil  : Row ts []
  | cons : {name : String} → {t : SqlType} → {nl : Bool} → {s : Schema} →
      SqlExpr ts t nl → Row ts s → Row ts ((name, ⟨t, nl⟩) :: s)

/-- A single named output column of a projection; built with `SqlExpr.as`,
consumed by the row-literal syntax `[e₁.as "A", e₂.as "B"]`. The
expression's nullability flag becomes the projected column's. -/
structure Cell (ts : Ctx) (name : String) (t : SqlType) (nl : Bool) where
  expr : SqlExpr ts t nl

protected def Row.default : (s : Schema) → Row ts s
  | [] => .nil
  | (_, ⟨_, _⟩) :: s => .cons default (Row.default s)

instance : Inhabited (Row ts s) := ⟨Row.default s⟩

/-- Name an expression as an output column: `c["Age"].as "Age"`. -/
def SqlExpr.as (e : SqlExpr ts t nl) (name : String) : Cell ts name t nl := ⟨e⟩

/-- Prepend a named cell to a row. Target of the row-literal syntax. -/
def Row.consCell (c : Cell ts name t nl) (r : Row ts s) :
    Row ts ((name, ⟨t, nl⟩) :: s) :=
  .cons c.expr r

/-- Row literal: `![c["Name"].as "Name", c["Id"].as "Id"] : Row ts [("Name", _), ("Id", _)]`.

The `![…]` bracket is deliberately distinct from the `List` literal: overloading
plain `[…]` would break list *patterns* (`match xs with | [a] => …`) in any
scope with LeanLinq notation open, because Lean does not backtrack syntax
choice nodes during pattern elaboration. -/
scoped syntax (name := rowLit) "![" term,+ "]" : term

@[macro rowLit] def expandRowLit : Lean.Macro := fun stx => do
  let cells := stx[1].getSepArgs
  let mut acc ← `(LeanLinq.Row.nil)
  for c in cells.reverse do
    acc ← `(LeanLinq.Row.consCell $(⟨c⟩) $acc)
  return acc

/-- Materialize the staged row of a source: every column becomes a `field`
reference through the given alias (empty alias ⇒ bare column names). Both
staged interpreters instantiate HOAS binders with these marker rows — the
compiler renders the fields, the evaluator looks them up in an alias
scope — so they walk the same instantiated trees. -/
def Row.ofAlias (alias : String) : (s : Schema) → Row ts s
  | [] => .nil
  | (name, ⟨t, nl⟩) :: s => .cons (.field t nl alias name) (Row.ofAlias alias s)

/-- Splice two rows; the natural result selector for `product`:
`fun a b => a ++ b`. -/
def Row.append : Row ts s₁ → Row ts s₂ → Row ts (s₁ ++ s₂)
  | .nil,       r₂ => r₂
  | .cons e r₁, r₂ => .cons e (r₁.append r₂)

instance : HAppend (Row ts s₁) (Row ts s₂) (Row ts (s₁ ++ s₂)) := ⟨Row.append⟩

/-! ## Column access by name

`HasCol s name t` resolves a column name against the schema by typeclass
search over the literal schema list (head instance wins, tail instance
recurses). This is pure syntactic unification of string literals — no
`decide`, no proof terms, no reduction of `String.decEq` — so the resulting
type is always a literal `SqlType` and downstream coercions/operators fire
reliably. A misspelled column fails at compile time with
`failed to synthesize HasCol …`. -/

class HasCol (s : Schema) (name : String) (t : outParam SqlType)
    (nl : outParam Bool) where
  getImpl : {ts : Ctx} → Row ts s → SqlExpr ts t nl

instance (priority := high) : HasCol ((name, ⟨t, nl⟩) :: s) name t nl where
  getImpl | .cons e _ => e

instance [c : HasCol s name t nl] : HasCol ((n', c') :: s) name t nl where
  getImpl | .cons _ r => c.getImpl r

/-- Column access by name: `r.col "Name"`. Prefer the bracket sugar
`r["Name"]`. The expression carries the column's declared nullability. -/
def Row.col (r : Row ts s) (name : String) [c : HasCol s name t nl] :
    SqlExpr ts t nl :=
  c.getImpl r

/-- A fetched cell, ready to embed as a typed literal wherever an
expression is expected: `some x` embeds via `SqlLit`, NULL embeds as SQL
NULL (comparisons with it are three-valued, exactly as the data would
behave in SQL). Like other literals, it needs an expected type to land —
put it on the right of `==.`/`!=.`. -/
structure CellLit (c : SqlCol) where
  cell : c.interp

def CellLit.toExpr [SqlLit t] : {nl : Bool} → CellLit ⟨t, nl⟩ → SqlExpr ts t nl
  | false, ⟨x⟩ => SqlLit.lit x
  | true, ⟨some x⟩ => .widen (SqlLit.lit x)
  | true, ⟨none⟩ => .nullC t

instance [SqlLit t] : Coe (CellLit ⟨t, nl⟩) (SqlExpr ts t nl) := ⟨CellLit.toExpr⟩

/-- Cell access by name on fetched rows: `v.cellLit "Id"`. Prefer the
bracket sugar `v["Id"]`. -/
def Values.cellLit (v : Values s) (name : String) [i : HasCell s name c] :
    CellLit c :=
  ⟨i.get v⟩

/-- Bracket sugar for column access: `c["Name"]` on staged rows (`Row` —
a column *reference*), `p["Name"]` on fetched rows (`Values` — the cell
as a typed *literal*). Dispatch is semantic — a term elaborator inspects
the receiver's type — so `Row` elaborates exactly as it always has
(class-based dispatch would let `binop%` operators solve the result type
before instance search runs). Overlaps with `GetElem` indexing syntax;
arrays/lists still go via core `getElem`. -/
scoped syntax:max (name := colGet) term noWs "[" term "]" : term

open Lean Elab Term Meta in
@[term_elab colGet] def elabColGet : TermElab := fun stx expectedType? => do
  let r ← elabTerm stx[0] none
  let rTy ← whnf (← instantiateMVars (← inferType r))
  if rTy.getAppFn.isMVar then
    tryPostpone
  -- elaborate the lookup with NO expected type — the expected type would
  -- pre-assign the nullability outParam and break resolution for strict
  -- columns in nullable positions — then coerce into the expectation
  -- (inserting `widen`/`CellLit` embedding as needed)
  let e ←
    if rTy.isAppOfArity ``LeanLinq.Values 1 then
      elabTerm (← `(LeanLinq.Values.cellLit $(⟨stx[0]⟩) $(⟨stx[2]⟩))) none
    else
      elabTerm (← `(LeanLinq.Row.col $(⟨stx[0]⟩) $(⟨stx[2]⟩))) none
  match expectedType? with
  | none => return e
  | some exp => do
      -- a strict column in a nullable position widens; decided eagerly by
      -- flag inspection, because the generic coercion machinery only
      -- reports the mismatch after delaying past this elaborator
      let eTy ← instantiateMVars (← inferType e)
      let expW ← instantiateMVars (← whnf exp)
      -- the column's own flag still undecided (schema pending, e.g. inside
      -- a query! expansion): retry once instance search has resolved it,
      -- lest the expected flag leak into the HasCol lookup
      if eTy.isAppOfArity ``LeanLinq.SqlExpr 3 && (eTy.getArg! 2).isMVar then
        tryPostpone
      if eTy.isAppOfArity ``LeanLinq.SqlExpr 3 &&
         expW.isAppOfArity ``LeanLinq.SqlExpr 3 &&
         (eTy.getArg! 2).isConstOf ``Bool.false &&
         (expW.getArg! 2).isConstOf ``Bool.true then
        ensureHasType exp (← mkAppM ``LeanLinq.SqlExpr.widen #[e])
      else
        ensureHasType exp e

/-- Positional column access. -/
def Row.nth : {s : Schema} → Row ts s → (i : Fin s.length) →
    SqlExpr ts (s.get i).2.ty (s.get i).2.nullable
  | _, .nil,      i        => i.elim0
  | _, .cons e _, ⟨0, _⟩   => e
  | _, .cons _ r, ⟨i+1, h⟩ => r.nth ⟨i, Nat.lt_of_succ_lt_succ h⟩

end LeanLinq
