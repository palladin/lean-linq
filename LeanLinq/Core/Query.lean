import LeanLinq.Core.Table

namespace LeanLinq

/-- Deep-embedded, schema-indexed relational queries (the Idris `SqlQuery`
GADT). Predicates and projections are HOAS functions over staged rows.

Use the pipeline API (`Query.from'`, `.filter`, `.select`, `.product`) rather
than the raw constructors — `from` and `where` are Lean keywords, and the
smart-constructor layer insulates user code from internal refactors. -/
inductive Query : Schema → Type where
  | fromTable : {s : Schema} → Table s → Query s
  | whereC    : {s : Schema} → Query s → (Row s → SqlExpr .bool) → Query s
  | selectC   : {s s' : Schema} → Query s → (Row s → Row s') → Query s'
  | productC  : {s₁ s₂ s' : Schema} → Query s₁ → Query s₂ →
      (Row s₁ → Row s₂ → Row s') → Query s'

namespace Query

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table s) : Query s := .fromTable t

/-- `WHERE p` (named `filter` because `where` is a Lean keyword). -/
def filter (q : Query s) (p : Row s → SqlExpr .bool) : Query s := .whereC q p

/-- `SELECT f`: project each row into a new schema. -/
def select (q : Query s) (f : Row s → Row s') : Query s' := .selectC q f

/-- Cartesian product with a result selector; `fun a b => a ++ b` keeps all
columns of both sides. -/
def product (q₁ : Query s₁) (q₂ : Query s₂) (f : Row s₁ → Row s₂ → Row s') :
    Query s' := .productC q₁ q₂ f

end Query

end LeanLinq
