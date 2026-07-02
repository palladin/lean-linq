import LeanLinq.Core.Table

namespace LeanLinq

/-- Deep-embedded, schema-indexed relational queries in monadic-comprehension
form (how C# desugars LINQ, and the shape of T-LINQ):

- `fromT`/`fromQ` *bind* a row variable over a source (table or subquery) —
  cross products are just nested `from`s, so there is no product combinator
  at all;
- `guard` is a WHERE conjunct over the rows bound so far;
- `yield` is the final SELECT projection.

Use the `query { from … where … select … }` syntax or the pipeline smart
constructors (`Query.from'`, `.where'`, `.select`) rather than the raw
constructors. -/
inductive Query : Schema → Type where
  | yield : {s : Schema} → Row s → Query s
  | guard : {s : Schema} → SqlExpr .bool → Query s → Query s
  | fromT : {s s' : Schema} → Table s → (Row s → Query s') → Query s'
  | fromQ : {s s' : Schema} → Query s → (Row s → Query s') → Query s'

/-- Anything that can appear as a `from` source in a query comprehension:
tables and subqueries. -/
class QuerySource (γ : Type) (s : outParam Schema) where
  bind : γ → (Row s → Query s') → Query s'

instance : QuerySource (Table s) s := ⟨.fromT⟩
instance : QuerySource (Query s) s := ⟨.fromQ⟩

namespace Query

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table s) : Query s := .fromT t (fun r => .yield r)

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). -/
def where' (q : Query s) (p : Row s → SqlExpr .bool) : Query s :=
  .fromQ q fun r => .guard (p r) (.yield r)

/-- `SELECT f`: project each row into a new schema. -/
def select (q : Query s) (f : Row s → Row s') : Query s' :=
  .fromQ q fun r => .yield (f r)

end Query

end LeanLinq
