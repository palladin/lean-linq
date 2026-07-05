import LeanLinq.Core.Expr

namespace LeanLinq

/-- A relation schema: ordered column names with their SQL types.

IMPORTANT: concrete schemas must be declared with `abbrev` (not `def`) so that
elaboration — column lookup, projection typing — can see through the name:

```
abbrev Customers : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
```
-/
abbrev Schema := List (String × SqlType)

/-- A heterogeneous tuple of SQL expressions indexed by a schema: the staged
value flowing through query combinators (each column is an expression, not a
runtime value — MetaOCaml-style staging).

The column name lives only in the index, so it flows in from the expected type
or from `.as`-tagged cells; see the row-literal syntax below. -/
inductive Row : Schema → Type where
  | nil  : Row []
  | cons : {name : String} → {t : SqlType} → {s : Schema} →
      SqlExpr t → Row s → Row ((name, t) :: s)

/-- A single named output column of a projection; built with `SqlExpr.as`,
consumed by the row-literal syntax `[e₁.as "A", e₂.as "B"]`. -/
structure Cell (name : String) (t : SqlType) where
  expr : SqlExpr t

protected def Row.default : (s : Schema) → Row s
  | [] => .nil
  | (_, _) :: s => .cons default (Row.default s)

instance : Inhabited (Row s) := ⟨Row.default s⟩

/-- Name an expression as an output column: `c["Age"].as "Age"`. -/
def SqlExpr.as (e : SqlExpr t) (name : String) : Cell name t := ⟨e⟩

/-- Prepend a named cell to a row. Target of the row-literal syntax. -/
def Row.consCell (c : Cell name t) (r : Row s) : Row ((name, t) :: s) :=
  .cons c.expr r

/-- Row literal: `![c["Name"].as "Name", c["Id"].as "Id"] : Row [("Name", _), ("Id", _)]`.

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
environment — so they walk the same instantiated trees. -/
def Row.ofAlias (alias : String) : (s : Schema) → Row s
  | [] => .nil
  | (name, t) :: s => .cons (.field t alias name) (Row.ofAlias alias s)

/-- Splice two rows; the natural result selector for `product`:
`fun a b => a ++ b`. -/
def Row.append : Row s₁ → Row s₂ → Row (s₁ ++ s₂)
  | .nil,       r₂ => r₂
  | .cons e r₁, r₂ => .cons e (r₁.append r₂)

instance : HAppend (Row s₁) (Row s₂) (Row (s₁ ++ s₂)) := ⟨Row.append⟩

/-! ## Column access by name

`HasCol s name t` resolves a column name against the schema by typeclass
search over the literal schema list (head instance wins, tail instance
recurses). This is pure syntactic unification of string literals — no
`decide`, no proof terms, no reduction of `String.decEq` — so the resulting
type is always a literal `SqlType` and downstream coercions/operators fire
reliably. A misspelled column fails at compile time with
`failed to synthesize HasCol …`. -/

class HasCol (s : Schema) (name : String) (t : outParam SqlType) where
  getImpl : Row s → SqlExpr t

instance (priority := high) : HasCol ((name, t) :: s) name t where
  getImpl | .cons e _ => e

instance [c : HasCol s name t] : HasCol ((n', t') :: s) name t where
  getImpl | .cons _ r => c.getImpl r

/-- Column access by name: `r.col "Name"`. Prefer the bracket sugar
`r["Name"]`. -/
def Row.col (r : Row s) (name : String) [c : HasCol s name t] : SqlExpr t :=
  c.getImpl r

/-- Bracket sugar for column access: `c["Name"]`. Overlaps with `GetElem`
indexing syntax; resolved against the receiver (rows here, arrays/lists via
core `getElem`). -/
scoped syntax:max (name := colGet) term noWs "[" term "]" : term

@[macro colGet] def expandColGet : Lean.Macro := fun stx =>
  `(LeanLinq.Row.col $(⟨stx[0]⟩) $(⟨stx[2]⟩))

/-- Positional column access. -/
def Row.nth : {s : Schema} → Row s → (i : Fin s.length) → SqlExpr (s.get i).2
  | _, .nil,      i        => i.elim0
  | _, .cons e _, ⟨0, _⟩   => e
  | _, .cons _ r, ⟨i+1, h⟩ => r.nth ⟨i, Nat.lt_of_succ_lt_succ h⟩

end LeanLinq
