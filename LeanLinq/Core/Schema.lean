import Lean
import LeanLinq.Core.Expr

namespace LeanLinq

/-- A single named output column of a projection; built with `SqlExpr.as`,
consumed by the row-literal syntax `[e₁.as "A", e₂.as "B"]`. The
expression's nullability flag becomes the projected column's. -/
structure CellP (ρ : Schema → Type) (ts : Ctx) (name : String) (c : SqlType) where
  expr : SqlExprP ρ ts c

abbrev Cell : Ctx → String → SqlType → Type := CellP AliasOf

protected def Row.default : (s : Schema) → Row ts s
  | [] => .nil
  | (_, _) :: s => .cons default (Row.default s)

instance : Inhabited (Row ts s) := ⟨Row.default s⟩

/-- Name an expression as an output column: `c["Age"].as "Age"`. -/
def SqlExprP.as (e : SqlExprP ρ ts c) (name : String) : CellP ρ ts name c := ⟨e⟩

def SqlExpr.as (e : SqlExpr ts c) (name : String) : Cell ts name c :=
  SqlExprP.as e name

/-- Prepend a named cell to a row. Target of the row-literal syntax. -/
def RowP.consCell (cell : CellP ρ ts name c) (r : RowP ρ ts s) :
    RowP ρ ts ((name, c) :: s) :=
  .cons cell.expr r

/-- Row literal: `![c["Name"].as "Name", c["Id"].as "Id"] : Row ts [("Name", _), ("Id", _)]`.

The `![…]` bracket is deliberately distinct from the `List` literal: overloading
plain `[…]` would break list *patterns* (`match xs with | [a] => …`) in any
scope with LeanLinq notation open, because Lean does not backtrack syntax
choice nodes during pattern elaboration. -/
scoped syntax (name := rowLit) "![" term,+ "]" : term

@[macro rowLit] def expandRowLit : Lean.Macro := fun stx => do
  let cells := stx[1].getSepArgs
  let mut acc ← `(LeanLinq.RowP.nil)
  for c in cells.reverse do
    acc ← `(LeanLinq.RowP.consCell $(⟨c⟩) $acc)
  return acc

/-- Materialize the staged row of a source: every column becomes a `field`
reference through the given alias (empty alias ⇒ bare column names). Both
staged interpreters instantiate HOAS binders with these marker rows — the
compiler renders the fields, the evaluator looks them up in an alias
scope — so they walk the same instantiated trees. -/
def Row.ofAlias (alias : String) : (s : Schema) → Row ts s
  | [] => .nil
  | (name, c) :: s =>
      .cons (.field (s' := []) c ⟨alias⟩ name) (Row.ofAlias alias s)

/-- Splice two rows; the natural result selector for `product`:
`fun a b => a ++ b`. -/
def RowP.append : RowP ρ ts s₁ → RowP ρ ts s₂ → RowP ρ ts (s₁ ++ s₂)
  | .nil,       r₂ => r₂
  | .cons e r₁, r₂ => .cons e (r₁.append r₂)

instance : HAppend (RowP ρ ts s₁) (RowP ρ ts s₂) (RowP ρ ts (s₁ ++ s₂)) :=
  ⟨RowP.append⟩

/-! ## Column access by name

`HasCol s name t` resolves a column name against the schema by typeclass
search over the literal schema list (head instance wins, tail instance
recurses). This is pure syntactic unification of string literals — no
`decide`, no proof terms, no reduction of `String.decEq` — so the resulting
type is always a literal `SqlPrim` and downstream coercions/operators fire
reliably. A misspelled column fails at compile time with
`failed to synthesize HasCol …`. -/

class HasCol (s : Schema) (name : String) (c : outParam SqlType) where
  getImpl : {ρ : Schema → Type} → {ts : Ctx} → RowP ρ ts s → SqlExprP ρ ts c

instance (priority := high) : HasCol ((name, c) :: s) name c where
  getImpl | .cons e _ => e

instance [i : HasCol s name c] : HasCol ((n', c') :: s) name c where
  getImpl | .cons _ r => i.getImpl r

/-- Column access by name: `r.col "Name"`. Prefer the bracket sugar
`r["Name"]`. The expression carries the column's declared nullability. -/
def RowP.col (r : RowP ρ ts s) (name : String) [i : HasCol s name c] :
    SqlExprP ρ ts c :=
  i.getImpl r

/-- A fetched cell, ready to embed as a typed literal wherever an
expression is expected: `some x` embeds via `SqlLit`, NULL embeds as SQL
NULL (comparisons with it are three-valued, exactly as the data would
behave in SQL). Like other literals, it needs an expected type to land —
put it on the right of `==.`/`!=.`. -/
structure CellLit (c : SqlType) where
  cell : c.interp

def CellLit.toExpr [SqlLit t] : {nl : Bool} → CellLit ⟨t, nl⟩ → SqlExprP ρ ts ⟨t, nl⟩
  | false, ⟨x⟩ => SqlLit.lit x
  | true, ⟨some x⟩ => .widen (SqlLit.lit x)
  | true, ⟨none⟩ => .nullC t

instance [SqlLit t] : Coe (CellLit ⟨t, nl⟩) (SqlExprP ρ ts ⟨t, nl⟩) := ⟨CellLit.toExpr⟩

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
    if rTy.isAppOfArity ``LeanLinq.Values 1 then do
      -- fetched rows: an SqlExpr-expecting position embeds the cell as a
      -- typed literal; every other position reads the honest value
      -- (`String` when the schema says NOT NULL, `Option` under `.null`)
      let wantsExpr ←
        match expectedType? with
        | some exp => do
            let expW ← instantiateMVars (← whnf exp)
            pure (expW.isAppOf ``LeanLinq.SqlExprP)
        | none => pure false
      if wantsExpr then
        elabTerm (← `(LeanLinq.Values.cellLit $(⟨stx[0]⟩) $(⟨stx[2]⟩))) none
      else
        elabTerm (← `(LeanLinq.Values.get $(⟨stx[0]⟩) $(⟨stx[2]⟩))) none
    else
      elabTerm (← `(LeanLinq.RowP.col $(⟨stx[0]⟩) $(⟨stx[2]⟩))) none
  match expectedType? with
  | none => return e
  | some exp => do
      -- a strict column in a nullable position widens; decided eagerly by
      -- flag inspection, because the generic coercion machinery only
      -- reports the mismatch after delaying past this elaborator
      let eTy ← instantiateMVars (← whnf (← inferType e))
      let expW ← instantiateMVars (← whnf exp)
      -- the nullability flag of `SqlExpr ts ⟨t, n⟩` (whnf unfolds the
      -- reducible per-type constants like `SqlType.long` to mk-apps)
      let flagOf : Expr → TermElabM (Option Expr) := fun ty => do
        if ty.isAppOfArity ``LeanLinq.SqlExprP 3 then
          let col ← whnf (ty.getArg! 2)
          if col.isAppOfArity ``LeanLinq.SqlType.mk 2 then
            return some (col.getArg! 1)
          else if col.isMVar then return some col   -- undecided
          else return none
        else return none
      -- the column's own flag still undecided (schema pending, e.g. inside
      -- a query! expansion): retry once instance search has resolved it,
      -- lest the expected flag leak into the HasCol lookup
      match ← flagOf eTy with
      | some f =>
          if f.isMVar then tryPostpone
          match ← flagOf expW with
          | some fe =>
              if f.isConstOf ``Bool.false && fe.isConstOf ``Bool.true then
                ensureHasType exp (← mkAppM ``LeanLinq.SqlExprP.widen #[e])
              else
                ensureHasType exp e
          | none => ensureHasType exp e
      | none => ensureHasType exp e

/-- Positional column access. -/
def RowP.nth : {s : Schema} → RowP ρ ts s → (i : Fin s.length) →
    SqlExprP ρ ts (s.get i).2
  | _, .nil,      i        => i.elim0
  | _, .cons e _, ⟨0, _⟩   => e
  | _, .cons _ r, ⟨i+1, h⟩ => r.nth ⟨i, Nat.lt_of_succ_lt_succ h⟩

namespace SqlExprP
export SqlExpr (as)
end SqlExprP

namespace Row
export RowP (append nth)
end Row

end LeanLinq
