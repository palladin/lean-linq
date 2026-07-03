import LeanLinq.Core.Table

namespace LeanLinq

/-- Deep-embedded, schema-indexed relational queries in monadic-comprehension
form:

- `fromT` *binds* a row variable over a table — cross products are just
  nested `from`s, so there is no product combinator at all;
- `guard` is a WHERE conjunct over the rows bound so far;
- `yield` is the final SELECT projection.

All combinators normalize at construction time (`Query.bind`), so a query is
always a flat spine of `fromT`/`guard` ending in `yield`, and code generation
emits exactly one flat SELECT per query. Constructs that must *not* be
flattened (DISTINCT, LIMIT, GROUP BY, set operations) will be added later as
explicit boundary nodes.

Use the `query! { from … where … select … }` syntax or the pipeline smart
constructors (`Query.from'`, `.where'`, `.select`) rather than the raw
constructors. -/
inductive Query : Schema → Type where
  | yield : {s : Schema} → Row s → Query s
  | guard : {s : Schema} → SqlExpr .bool → Query s → Query s
  | fromT : {s s' : Schema} → Table s → (Row s → Query s') → Query s'

instance : Inhabited (Query s) := ⟨.yield default⟩

namespace Query

/-- Monadic bind — the normalization workhorse (C#'s `SelectMany`, T-LINQ's
`for`-assoc law): splice `k` at every `yield` leaf, extending the
comprehension spine instead of nesting a derived table.

Valid because filtering/projecting the output of a pure SELECT/FROM/WHERE
query is the same as adding conjuncts/projections to it. When boundary nodes
(DISTINCT, LIMIT, GROUP BY) are added, their `bind` cases must wrap in a
subquery node instead of splicing through.

Total: `Query` is a reflexive inductive (`fromT` stores `Row s → Query s'`),
so structural recursion's inductive hypothesis covers `f r` for every `r` —
recursion under the applied HOAS binder is fine. -/
def bind : Query s → (Row s → Query s') → Query s'
  | .yield r,      k => k r
  | .guard b rest, k => .guard b (rest.bind k)
  | .fromT t f,    k => .fromT t (fun r => (f r).bind k)

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table s) : Query s := .fromT t (fun r => .yield r)

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). Splices the
predicate into the query's own WHERE clause. -/
def where' (q : Query s) (p : Row s → SqlExpr .bool) : Query s :=
  q.bind fun r => .guard (p r) (.yield r)

/-- `SELECT f`: project each row into a new schema, replacing the query's
projection in place. -/
def select (q : Query s) (f : Row s → Row s') : Query s' :=
  q.bind fun r => .yield (f r)

end Query

/-- Anything that can appear as a `from` source in a query comprehension:
tables, and queries themselves (which normalize into the enclosing
comprehension via `Query.bind`). -/
class QuerySource (γ : Type) (s : outParam Schema) where
  bind : γ → (Row s → Query s') → Query s'

instance : QuerySource (Table s) s := ⟨.fromT⟩
instance : QuerySource (Query s) s := ⟨Query.bind⟩

end LeanLinq
