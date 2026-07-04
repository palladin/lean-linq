import LeanLinq.Core.Table

namespace LeanLinq

mutual

/-- The comprehension *spine*: the monadic core that always compiles to one
flat SELECT. `fromT`/`joinT` bind row variables over sources, `guard` adds a
WHERE conjunct, `yield` is the projection, and `fromQ` brings a full `Query`
(with boundary clauses) back in as a derived table.

`SpineQ` and `Query` are separate inductives (rather than one) so that the
compiler's mutual recursion — statement ↔ spine — is structural: each hop
recurses on a strict subterm. -/
inductive SpineQ : Schema → Type where
  | yield : {s : Schema} → Row s → SpineQ s
  | guard : {s : Schema} → SqlExpr .bool → SpineQ s → SpineQ s
  | fromT : {s s' : Schema} → Table s → (Row s → SpineQ s') → SpineQ s'
  | joinT : {s s' : Schema} → JoinKind → Table s → (Row s → SqlExpr .bool) →
      (Row s → SpineQ s') → SpineQ s'
  | fromQ : {s s' : Schema} → Query s → (Row s → SpineQ s') → SpineQ s'
  -- ORDER BY belongs to the statement being assembled, so it lives on the
  -- spine (keys already applied to the bound rows) and `bind` splices
  -- through it — projections/filters after `orderBy` fuse into the same
  -- flat statement (SQL Server in particular forbids ORDER BY inside a
  -- derived table).
  | order : {s : Schema} → List OrderKey → SpineQ s → SpineQ s

/-- A full query: a spine, or a spine decorated by *boundary* clauses that
`Query.bind` must not splice through (ORDER BY, DISTINCT, LIMIT/OFFSET,
GROUP BY/HAVING, set operations) — binding over them wraps the query as a
derived table, which is exactly SQL's semantics.

Use the `query! { … }` syntax or the pipeline smart constructors rather than
the raw constructors. -/
inductive Query : Schema → Type where
  | spine : {s : Schema} → SpineQ s → Query s
  | distinctC : {s : Schema} → Query s → Query s
  | limitC : {s : Schema} → Query s → Option Nat → Option Nat → Query s
  | groupedC : {s s' : Schema} → SpineQ s → (Row s → List KeyExpr) →
      Option (Row s → SqlExpr .bool) → (Row s → Agg → Row s') → Query s'
  | setOpC : {s : Schema} → SetOp → Query s → Query s → Query s

end

instance : Inhabited (SpineQ s) := ⟨.yield default⟩
instance : Inhabited (Query s) := ⟨.spine default⟩

/-- View any query as a spine: spines unwrap; boundary-decorated queries
become a derived-table source. -/
def Query.asSpine : Query s → SpineQ s
  | .spine sp => sp
  | q => .fromQ q (fun r => .yield r)

namespace SpineQ

/-- Monadic bind on spines (C#'s `SelectMany` law): splice `k` at every
`yield` leaf, extending the comprehension instead of nesting.

Total: `SpineQ` is a reflexive inductive, so structural recursion's inductive
hypothesis covers `f r` for every `r`. -/
def bind : SpineQ s → (Row s → SpineQ s') → SpineQ s'
  | .yield r,         k => k r
  | .guard b rest,    k => .guard b (rest.bind k)
  | .fromT t f,       k => .fromT t (fun r => (f r).bind k)
  | .joinT j t on' f, k => .joinT j t on' (fun r => (f r).bind k)
  | .fromQ q f,       k => .fromQ q (fun r => (f r).bind k)
  | .order ks rest,   k => .order ks (rest.bind k)

end SpineQ

namespace Query

/-- Monadic bind — the normalization workhorse: spines splice, boundary
queries wrap as derived tables. -/
def bind (q : Query s) (k : Row s → Query s') : Query s' :=
  .spine (q.asSpine.bind (fun r => (k r).asSpine))

/-- The final projection of a comprehension (`select` clause of `query!`). -/
def yield (r : Row s) : Query s := .spine (.yield r)

/-- A WHERE conjunct over already-bound rows (`where` clause of `query!`). -/
def guard (b : SqlExpr .bool) (q : Query s) : Query s :=
  .spine (.guard b q.asSpine)

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table s) : Query s := .spine (.fromT t (fun r => .yield r))

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). Splices the
predicate into the query's own WHERE clause. -/
def where' (q : Query s) (p : Row s → SqlExpr .bool) : Query s :=
  .spine (q.asSpine.bind fun r => .guard (p r) (.yield r))

/-- `SELECT f`: project each row into a new schema, replacing the query's
projection in place. -/
def select (q : Query s) (f : Row s → Row s') : Query s' :=
  .spine (q.asSpine.bind fun r => .yield (f r))

/-- `INNER JOIN t ON on'` with a result selector. Splices into the spine, so
chained joins compile to one flat statement. -/
def innerJoin (q : Query s₁) (t : Table s₂)
    (on' : Row s₁ → Row s₂ → SqlExpr .bool)
    (sel : Row s₁ → Row s₂ → Row s') : Query s' :=
  .spine (q.asSpine.bind fun a => .joinT .inner t (on' a) (fun b => .yield (sel a b)))

/-- `LEFT JOIN t ON on'` with a result selector. -/
def leftJoin (q : Query s₁) (t : Table s₂)
    (on' : Row s₁ → Row s₂ → SqlExpr .bool)
    (sel : Row s₁ → Row s₂ → Row s') : Query s' :=
  .spine (q.asSpine.bind fun a => .joinT .left t (on' a) (fun b => .yield (sel a b)))

/-- `ORDER BY` with one or more directed keys:
`q.orderBy (fun c => [c["Name"].asc, c["Age"].desc])`. Keys reference the
query's *output* columns. -/
def orderBy (q : Query s) (ks : Row s → List OrderKey) : Query s :=
  .spine (q.asSpine.bind fun r => .order (ks r) (.yield r))

/-- `SELECT DISTINCT`. -/
def distinct (q : Query s) : Query s := .distinctC q

/-- `LIMIT`/`OFFSET` (rendered per dialect; SQL Server uses OFFSET/FETCH). -/
def limitOffset (q : Query s) (limit? offset? : Option Nat) : Query s :=
  .limitC q limit? offset?

def limit (q : Query s) (n : Nat) : Query s := q.limitOffset (some n) none
def offset (q : Query s) (n : Nat) : Query s := q.limitOffset none (some n)

def union (q₁ q₂ : Query s) : Query s := .setOpC .union q₁ q₂
def intersect (q₁ q₂ : Query s) : Query s := .setOpC .intersect q₁ q₂
def except (q₁ q₂ : Query s) : Query s := .setOpC .except q₁ q₂

end Query

/-- A query grouped by keys, awaiting `having`/`select` (staged GroupBy →
Having → Select surface; aggregates in a plain `where'` are unrepresentable). -/
structure GroupedQuery (s : Schema) where
  query : Query s
  keys : Row s → List KeyExpr
  having? : Option (Row s → SqlExpr .bool) := none

/-- `GROUP BY` one or more keys: `q.groupBy (fun c => [c["Age"].key])`. -/
def Query.groupBy (q : Query s) (keys : Row s → List KeyExpr) : GroupedQuery s :=
  ⟨q, keys, none⟩

/-- `HAVING` over the grouped rows; the `Agg` token builds aggregates:
`g.having (fun c a => 1 <. a.count)`. -/
def GroupedQuery.having (g : GroupedQuery s)
    (p : Row s → Agg → SqlExpr .bool) : GroupedQuery s :=
  { g with having? := some (fun r => p r ⟨⟩) }

/-- Grouped projection over keys and aggregates:
`g.select (fun c a => ![c["Age"].as "Age", (a.count).as "Cnt"])`. -/
def GroupedQuery.select (g : GroupedQuery s) (f : Row s → Agg → Row s') : Query s' :=
  .groupedC g.query.asSpine g.keys g.having? f

/-- A query returning a single scalar value (COUNT/SUM/AVG/MIN/MAX). -/
inductive ScalarQuery : SqlType → Type where
  | aggQ (op : AggOp) {n : String} {t : SqlType} (sp : SpineQ [(n, t)]) : ScalarQuery t
  | countQ {s : Schema} (sp : SpineQ s) : ScalarQuery .int

/-- `COUNT(*)` over a query. -/
def Query.count (q : Query s) : ScalarQuery .int := .countQ q.asSpine

/-- `SUM` over a single-column query (project first: `q.select … |>.sum`). -/
def Query.sum (q : Query [(n, t)]) : ScalarQuery t := .aggQ .sum q.asSpine
def Query.avg (q : Query [(n, t)]) : ScalarQuery t := .aggQ .avg q.asSpine
def Query.min (q : Query [(n, t)]) : ScalarQuery t := .aggQ .min q.asSpine
def Query.max (q : Query [(n, t)]) : ScalarQuery t := .aggQ .max q.asSpine

/-- Anything that can appear as a `from` source in a query comprehension:
tables, and queries themselves (spines inline via `Query.bind`; boundary
queries become derived tables). -/
class QuerySource (γ : Type) (s : outParam Schema) where
  bind : γ → (Row s → Query s') → Query s'

instance : QuerySource (Table s) s :=
  ⟨fun t k => .spine (.fromT t (fun r => (k r).asSpine))⟩
instance : QuerySource (Query s) s := ⟨Query.bind⟩

end LeanLinq
