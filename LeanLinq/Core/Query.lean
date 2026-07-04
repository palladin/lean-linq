import LeanLinq.Core.Table

namespace LeanLinq

/-- The terminal shape of a comprehension spine: does it end in a plain
projection (`yield`) or a grouped one (`groupYield`, carrying
GROUP BY/HAVING)? Indexing `SpineQ` by this makes the grouping discipline
*static*: `SpineQ.bind` accepts only `.plain` spines, so splicing through a
grouped terminal — which would discard its GROUP BY — is untypeable rather
than guarded at run time. -/
inductive Terminal where
  | plain
  | grouped
  deriving DecidableEq, Repr

mutual

/-- The comprehension *spine*: the monadic core that always compiles to one
flat SELECT. `fromT`/`joinT` bind row variables over sources, `guard` adds a
WHERE conjunct, `order` contributes ORDER BY keys, and the spine ends in one
of two terminals — `yield` (a plain projection, `Terminal.plain`) or
`groupYield` (keys/HAVING/grouped projection, `Terminal.grouped`). `fromQ`
brings a full `Query` (with boundary clauses) back in as a derived table.

`SpineQ` and `Query` are separate inductives (rather than one) so that the
compiler's mutual recursion — statement ↔ spine — is structural: each hop
recurses on a strict subterm. -/
inductive SpineQ : Terminal → Schema → Type where
  | yield : {s : Schema} → Row s → SpineQ .plain s
  -- A *grouped* terminal (the `groupBy`/`having`/`select` tail of a
  -- comprehension): GROUP BY keys, optional HAVING, and the grouped
  -- projection — all plain expressions over the rows bound earlier in the
  -- spine.
  | groupYield : {s : Schema} → List KeyExpr → Option (SqlExpr .bool) →
      Row s → SpineQ .grouped s
  | guard : {g : Terminal} → {s : Schema} → SqlExpr .bool → SpineQ g s → SpineQ g s
  -- ORDER BY belongs to the statement being assembled, so it lives on the
  -- spine (keys already applied to the bound rows) and `bind` splices
  -- through it — projections/filters after `orderBy` fuse into the same
  -- flat statement (SQL Server in particular forbids ORDER BY inside a
  -- derived table). In a grouped spine the keys may reference aggregates.
  | order : {g : Terminal} → {s : Schema} → List OrderKey → SpineQ g s → SpineQ g s
  | fromT : {g : Terminal} → {s s' : Schema} → Table s →
      (Row s → SpineQ g s') → SpineQ g s'
  | joinT : {g : Terminal} → {s s' : Schema} → JoinKind → Table s →
      (Row s → SqlExpr .bool) → (Row s → SpineQ g s') → SpineQ g s'
  | fromQ : {g : Terminal} → {s s' : Schema} → Query s →
      (Row s → SpineQ g s') → SpineQ g s'

/-- A full query: a spine (of either terminal shape), or a spine decorated by
*boundary* clauses that `bind` must not splice through (DISTINCT,
LIMIT/OFFSET, pipeline GROUP BY/HAVING, set operations) — binding over them
wraps the query as a derived table, which is exactly SQL's semantics.

Use the `query! { … }` syntax or the pipeline smart constructors rather than
the raw constructors. -/
inductive Query : Schema → Type where
  | spine : {g : Terminal} → {s : Schema} → SpineQ g s → Query s
  | distinctC : {s : Schema} → Query s → Query s
  | limitC : {s : Schema} → Query s → Option Nat → Option Nat → Query s
  | groupedC : {s s' : Schema} → SpineQ .plain s → (Row s → List KeyExpr) →
      Option (Row s → SqlExpr .bool) → Option (Row s → List OrderKey) →
      (Row s → Agg → Row s') → Query s'
  | setOpC : {s : Schema} → SetOp → Query s → Query s → Query s

end

instance : Inhabited (SpineQ .plain s) := ⟨.yield default⟩
instance : Inhabited (SpineQ .grouped s) := ⟨.groupYield [] none default⟩
instance : Inhabited (Query s) := ⟨.spine (.yield default)⟩

namespace SpineQ

/-- Implementation of `bind`, generalized over the terminal index:
structural recursion over an indexed family needs the index to be a
*variable*, so we recurse at `SpineQ g₀ s` carrying the proof `g₀ = .plain`
and discharge the `groupYield` case with it (`nomatch` on
`.grouped = .plain` — impossibility proved, not handled). -/
private def bindAux : {g₀ : Terminal} → {s : Schema} → SpineQ g₀ s →
    g₀ = .plain → (Row s → SpineQ g s') → SpineQ g s'
  | _, _, .yield r,         _, k => k r
  | _, _, .groupYield ..,   h, _ => nomatch h
  | _, _, .guard b rest,    h, k => .guard b (bindAux rest h k)
  | _, _, .order ks rest,   h, k => .order ks (bindAux rest h k)
  | _, _, .fromT t f,       h, k => .fromT t (fun r => bindAux (f r) h k)
  | _, _, .joinT j t on' f, h, k => .joinT j t on' (fun r => bindAux (f r) h k)
  | _, _, .fromQ q f,       h, k => .fromQ q (fun r => bindAux (f r) h k)

/-- Monadic bind on *plain* spines (C#'s `SelectMany` law): splice `k` at the
`yield` leaves, extending the comprehension instead of nesting. Grouped
spines have no `bind` — a `groupYield` terminal cannot appear at index
`.plain`, so the case that would discard a GROUP BY does not typecheck.

Total: `SpineQ` is a reflexive inductive, so structural recursion's inductive
hypothesis covers `f r` for every `r`. -/
def bind (sp : SpineQ .plain s) (k : Row s → SpineQ g s') : SpineQ g s' :=
  bindAux sp rfl k

end SpineQ

/-- View a query as a *plain* spine suitable for extending (binding more
clauses onto it): plain spines unwrap; grouped spines and boundary-decorated
queries become a derived-table source. The grouped/plain distinction is an
O(1) match on the `Terminal` index — no spine traversal. -/
def Query.asPlainSpine : Query s → SpineQ .plain s
  | .spine (g := .plain) sp => sp
  | q => .fromQ q (fun r => .yield r)

namespace Query

/-- Monadic bind — the normalization workhorse: plain spines splice; grouped
spines and boundary queries wrap as derived tables (on both the receiver and
the continuation's results). -/
def bind (q : Query s) (k : Row s → Query s') : Query s' :=
  .spine (q.asPlainSpine.bind (fun r => (k r).asPlainSpine))

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table s) : Query s := .spine (.fromT t (fun r => .yield r))

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). Splices the
predicate into the query's own WHERE clause. -/
def where' (q : Query s) (p : Row s → SqlExpr .bool) : Query s :=
  .spine (q.asPlainSpine.bind fun r => .guard (p r) (.yield r))

/-- `SELECT f`: project each row into a new schema, replacing the query's
projection in place. -/
def select (q : Query s) (f : Row s → Row s') : Query s' :=
  .spine (q.asPlainSpine.bind fun r => .yield (f r))

/-- `INNER JOIN t ON on'` with a result selector. Splices into the spine, so
chained joins compile to one flat statement. -/
def innerJoin (q : Query s₁) (t : Table s₂)
    (on' : Row s₁ → Row s₂ → SqlExpr .bool)
    (sel : Row s₁ → Row s₂ → Row s') : Query s' :=
  .spine (q.asPlainSpine.bind fun a => .joinT .inner t (on' a) (fun b => .yield (sel a b)))

/-- `LEFT JOIN t ON on'` with a result selector. -/
def leftJoin (q : Query s₁) (t : Table s₂)
    (on' : Row s₁ → Row s₂ → SqlExpr .bool)
    (sel : Row s₁ → Row s₂ → Row s') : Query s' :=
  .spine (q.asPlainSpine.bind fun a => .joinT .left t (on' a) (fun b => .yield (sel a b)))

/-- `ORDER BY` with one or more directed keys:
`q.orderBy (fun c => [c["Name"].asc, c["Age"].desc])`. Keys reference the
query's *output* columns; ordering fuses into the query's own statement. -/
def orderBy (q : Query s) (ks : Row s → List OrderKey) : Query s :=
  .spine (q.asPlainSpine.bind fun r => .order (ks r) (.yield r))

/-- `SELECT DISTINCT`. -/
def distinct (q : Query s) : Query s := .distinctC q

/-- `LIMIT`/`OFFSET` (rendered per dialect; SQL Server uses OFFSET/FETCH).
Applying it to an already-limited query wraps that query as a derived table —
stacking two LIMIT clauses on one statement is not valid SQL. -/
def limitOffset (q : Query s) (limit? offset? : Option Nat) : Query s :=
  match q with
  | .limitC .. => .limitC (.spine (.fromQ q (fun r => .yield r))) limit? offset?
  | _ => .limitC q limit? offset?

/-- `LIMIT n`. Chaining onto a pending `offset` merges into one clause
(`q.offset 10 |>.limit 5` ⇒ `LIMIT 5 OFFSET 10`); onto an existing limit it
wraps (`LIMIT` of a `LIMIT` via a derived table). -/
def limit (q : Query s) (n : Nat) : Query s :=
  match q with
  | .limitC q' none off? => .limitC q' (some n) off?
  | _ => q.limitOffset (some n) none

/-- `OFFSET n`. Chaining onto a pending `limit` merges into one clause
(`q.limit 5 |>.offset 10` ⇒ `LIMIT 5 OFFSET 10`); onto an existing offset it
wraps. -/
def offset (q : Query s) (n : Nat) : Query s :=
  match q with
  | .limitC q' lim? none => .limitC q' lim? (some n)
  | _ => q.limitOffset none (some n)

def union (q₁ q₂ : Query s) : Query s := .setOpC .union q₁ q₂
def intersect (q₁ q₂ : Query s) : Query s := .setOpC .intersect q₁ q₂
def except (q₁ q₂ : Query s) : Query s := .setOpC .except q₁ q₂

end Query

/-- A query grouped by keys, awaiting `having`/`orderBy`/`select` (staged
GroupBy → Having → OrderBy → Select surface; aggregates in a plain `where'`
are unrepresentable). -/
structure GroupedQuery (s : Schema) where
  query : Query s
  keys : Row s → List KeyExpr
  having? : Option (Row s → SqlExpr .bool) := none
  orderKeys? : Option (Row s → List OrderKey) := none

/-- `GROUP BY` one or more keys: `q.groupBy (fun c => [c["Age"].key])`. -/
def Query.groupBy (q : Query s) (keys : Row s → List KeyExpr) : GroupedQuery s :=
  ⟨q, keys, none, none⟩

/-- `HAVING` over the grouped rows; the `Agg` token builds aggregates:
`g.having (fun c a => 1 <. a.count)`. -/
def GroupedQuery.having (g : GroupedQuery s)
    (p : Row s → Agg → SqlExpr .bool) : GroupedQuery s :=
  { g with having? := some (fun r => p r ⟨⟩) }

/-- Aggregate-aware `ORDER BY` on a grouped query, before its `select`:
`g.orderBy (fun o a => [(a.sum o["Amount"]).desc, (a.count).asc])` — renders
inside the grouped statement (`… GROUP BY … HAVING … ORDER BY SUM(…) DESC`). -/
def GroupedQuery.orderBy (g : GroupedQuery s)
    (ks : Row s → Agg → List OrderKey) : GroupedQuery s :=
  { g with orderKeys? := some (fun r => ks r ⟨⟩) }

/-- Grouped projection over keys and aggregates:
`g.select (fun c a => ![c["Age"].as "Age", (a.count).as "Cnt"])`. -/
def GroupedQuery.select (g : GroupedQuery s) (f : Row s → Agg → Row s') : Query s' :=
  .groupedC g.query.asPlainSpine g.keys g.having? g.orderKeys? f

/-- A query returning a single scalar value (COUNT/SUM/AVG/MIN/MAX). -/
inductive ScalarQuery : SqlType → Type where
  | aggQ (op : AggOp) {n : String} {t : SqlType} (sp : SpineQ .plain [(n, t)]) : ScalarQuery t
  | countQ {s : Schema} (sp : SpineQ .plain s) : ScalarQuery .int

/-- `COUNT(*)` over a query. -/
def Query.count (q : Query s) : ScalarQuery .int := .countQ q.asPlainSpine

/-- `SUM` over a single-column query (project first: `q.select … |>.sum`). -/
def Query.sum (q : Query [(n, t)]) : ScalarQuery t := .aggQ .sum q.asPlainSpine
def Query.avg (q : Query [(n, t)]) : ScalarQuery t := .aggQ .avg q.asPlainSpine
def Query.min (q : Query [(n, t)]) : ScalarQuery t := .aggQ .min q.asPlainSpine
def Query.max (q : Query [(n, t)]) : ScalarQuery t := .aggQ .max q.asPlainSpine

/-- Anything that can appear as a `from` source in a query comprehension:
tables, and queries themselves (plain-spine queries inline; grouped or
boundary queries become derived tables — decided statically on the
`Terminal` index). The continuation is spine-valued so the `query!` macro
can fold clauses with their terminal shapes known at elaboration time. -/
class QuerySource (γ : Type) (s : outParam Schema) where
  bind : γ → (Row s → SpineQ g s') → SpineQ g s'

instance : QuerySource (Table s) s := ⟨.fromT⟩
instance : QuerySource (Query s) s :=
  ⟨fun q k =>
    match q with
    | .spine (g := .plain) sp => sp.bind k
    | q => .fromQ q k⟩

end LeanLinq
