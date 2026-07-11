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

-- `inst` binders are named so interpreters can rebind them in patterns
-- (`(inst := i)`), which the unused-variable linter cannot see.
set_option linter.unusedVariables false in
mutual

/-- The comprehension *spine*: the monadic core that always compiles to one
flat SELECT. `fromT`/`joinT` bind row variables over sources, `guard` adds a
WHERE conjunct, `order` contributes ORDER BY keys, and the spine ends in one
of two terminals — `yield` (a plain projection, `Terminal.plain`) or
`groupYield` (keys/HAVING/grouped projection, `Terminal.grouped`). `fromQ`
brings a full `Query` (with boundary clauses) back in as a derived table.

The `ts` index is the ambient table context: `fromT`/`joinT` *demand* a
`HasTable ts n s` instance and store it in the node — the query keeps track
of its referenced tables as capabilities, resolved at elaboration time, so
evaluation needs no name lookup and running against a database lacking a
table is a type error.

`SpineQ` and `Query` are separate inductives (rather than one) so that the
compiler's mutual recursion — statement ↔ spine — is structural: each hop
recurses on a strict subterm. -/
inductive SpineQ : Ctx → Terminal → Schema → Type where
  | yield : {ts : Ctx} → {s : Schema} → Row ts s → SpineQ ts .plain s
  -- A *grouped* terminal (the `groupBy`/`having`/`select` tail of a
  -- comprehension): GROUP BY keys, optional HAVING, and the grouped
  -- projection — all plain expressions over the rows bound earlier in the
  -- spine.
  | groupYield : {ts : Ctx} → {s : Schema} → List (KeyExpr ts) →
      Option (SqlExpr ts .bool true) → Row ts s → SpineQ ts .grouped s
  | guard : {ts : Ctx} → {g : Terminal} → {s : Schema} → {nb : Bool} →
      SqlExpr ts .bool nb → SpineQ ts g s → SpineQ ts g s
  -- ORDER BY belongs to the statement being assembled, so it lives on the
  -- spine (keys already applied to the bound rows) and `bind` splices
  -- through it — projections/filters after `orderBy` fuse into the same
  -- flat statement (SQL Server in particular forbids ORDER BY inside a
  -- derived table). In a grouped spine the keys may reference aggregates.
  | order : {ts : Ctx} → {g : Terminal} → {s : Schema} →
      List (OrderKey ts) → SpineQ ts g s → SpineQ ts g s
  | fromT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      [inst : HasTable ts.tables n s] → Table n s →
      (Row ts s → SpineQ ts g s') → SpineQ ts g s'
  | joinT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (Row ts s → SqlExpr ts .bool nb) →
      (Row ts s → SpineQ ts g s') → SpineQ ts g s'
  -- LEFT JOIN: the joined row is NULL-lifted — its columns read as
  -- nullable in the ON predicate and everything downstream: the
  -- type-level truth of the padding row.
  | joinLeftT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (Row ts s.asNull → SqlExpr ts .bool nb) →
      (Row ts s.asNull → SpineQ ts g s') → SpineQ ts g s'
  | fromQ : {ts : Ctx} → {g : Terminal} → {s s' : Schema} → Query ts s →
      (Row ts s → SpineQ ts g s') → SpineQ ts g s'

/-- A full query: a spine (of either terminal shape), or a spine decorated by
*boundary* clauses that `bind` must not splice through (DISTINCT,
LIMIT/OFFSET, pipeline GROUP BY/HAVING, set operations) — binding over them
wraps the query as a derived table, which is exactly SQL's semantics.

Use the `query! { … }` syntax or the pipeline smart constructors rather than
the raw constructors. -/
inductive Query : Ctx → Schema → Type where
  | spine : {ts : Ctx} → {g : Terminal} → {s : Schema} → SpineQ ts g s → Query ts s
  | distinctC : {ts : Ctx} → {s : Schema} → Query ts s → Query ts s
  | limitC : {ts : Ctx} → {s : Schema} → Query ts s → Option Nat → Option Nat → Query ts s
  | groupedC : {ts : Ctx} → {s s' : Schema} → SpineQ ts .plain s →
      (Row ts s → List (KeyExpr ts)) →
      Option (Row ts s → SqlExpr ts .bool true) →
      Option (Row ts s → List (OrderKey ts)) →
      (Row ts s → Agg → Row ts s') → Query ts s'
  | setOpC : {ts : Ctx} → {s : Schema} → SetOp → Query ts s → Query ts s → Query ts s

end

instance : Inhabited (SpineQ ts .plain s) := ⟨.yield default⟩
instance : Inhabited (SpineQ ts .grouped s) := ⟨.groupYield [] none default⟩
instance : Inhabited (Query ts s) := ⟨.spine (.yield default)⟩

namespace SpineQ

/-- Implementation of `bind`, generalized over the terminal index:
structural recursion over an indexed family needs the index to be a
*variable*, so we recurse at `SpineQ ts g₀ s` carrying the proof
`g₀ = .plain` and discharge the `groupYield` case with it (`nomatch` on
`.grouped = .plain` — impossibility proved, not handled). -/
private def bindAux : {g₀ : Terminal} → {s : Schema} → SpineQ ts g₀ s →
    g₀ = .plain → (Row ts s → SpineQ ts g s') → SpineQ ts g s'
  | _, _, .yield r,         _, k => k r
  | _, _, .groupYield ..,   h, _ => nomatch h
  | _, _, .guard b rest,    h, k => .guard b (bindAux rest h k)
  | _, _, .order ks rest,   h, k => .order ks (bindAux rest h k)
  -- rebuilding a source node reuses its *matched* membership instance —
  -- no fresh instance search
  | _, _, .fromT (inst := i) t f, h, k =>
      .fromT (inst := i) t (fun r => bindAux (f r) h k)
  | _, _, .joinT (inst := i) t on' f, h, k =>
      .joinT (inst := i) t on' (fun r => bindAux (f r) h k)
  | _, _, .joinLeftT (inst := i) t on' f, h, k =>
      .joinLeftT (inst := i) t on' (fun r => bindAux (f r) h k)
  | _, _, .fromQ q f,       h, k => .fromQ q (fun r => bindAux (f r) h k)

/-- Monadic bind on *plain* spines (C#'s `SelectMany` law): splice `k` at the
`yield` leaves, extending the comprehension instead of nesting. Grouped
spines have no `bind` — a `groupYield` terminal cannot appear at index
`.plain`, so the case that would discard a GROUP BY does not typecheck.

Total: `SpineQ` is a reflexive inductive, so structural recursion's inductive
hypothesis covers `f r` for every `r`. -/
def bind (sp : SpineQ ts .plain s) (k : Row ts s → SpineQ ts g s') : SpineQ ts g s' :=
  bindAux sp rfl k

end SpineQ

/-- View a query as a *plain* spine suitable for extending (binding more
clauses onto it): plain spines unwrap; grouped spines and boundary-decorated
queries become a derived-table source. The grouped/plain distinction is an
O(1) match on the `Terminal` index — no spine traversal. -/
def Query.asPlainSpine : Query ts s → SpineQ ts .plain s
  | .spine (g := .plain) sp => sp
  | q => .fromQ q (fun r => .yield r)

namespace Query

/-- Monadic bind — the normalization workhorse: plain spines splice; grouped
spines and boundary queries wrap as derived tables (on both the receiver and
the continuation's results). -/
def bind (q : Query ts s) (k : Row ts s → Query ts s') : Query ts s' :=
  .spine (q.asPlainSpine.bind (fun r => (k r).asPlainSpine))

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table n s) [HasTable ts.tables n s] : Query ts s :=
  .spine (.fromT t (fun r => .yield r))

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). Splices the
predicate into the query's own WHERE clause. -/
def where' (q : Query ts s) (p : Row ts s → SqlExpr ts .bool nb) : Query ts s :=
  .spine (q.asPlainSpine.bind fun r => .guard (p r) (.yield r))

/-- `SELECT f`: project each row into a new schema, replacing the query's
projection in place. -/
def select (q : Query ts s) (f : Row ts s → Row ts s') : Query ts s' :=
  .spine (q.asPlainSpine.bind fun r => .yield (f r))

/-- `INNER JOIN t ON on'` with a result selector. Splices into the spine, so
chained joins compile to one flat statement. -/
def innerJoin (q : Query ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : Row ts s₁ → Row ts s₂ → SqlExpr ts .bool nb)
    (sel : Row ts s₁ → Row ts s₂ → Row ts s') : Query ts s' :=
  .spine (q.asPlainSpine.bind fun a => .joinT t (on' a) (fun b => .yield (sel a b)))

/-- `LEFT JOIN t ON on'` with a result selector. The joined row's columns
are NULL-lifted (`s₂.asNull`) in both the predicate and the selector — an
unmatched left row pads them with NULL, and the types say so. -/
def leftJoin (q : Query ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : Row ts s₁ → Row ts s₂.asNull → SqlExpr ts .bool nb)
    (sel : Row ts s₁ → Row ts s₂.asNull → Row ts s') : Query ts s' :=
  .spine (q.asPlainSpine.bind fun a => .joinLeftT t (on' a) (fun b => .yield (sel a b)))

/-- `ORDER BY` with one or more directed keys:
`q.orderBy (fun c => [c["Name"].asc, c["Age"].desc])`. Keys reference the
query's *output* columns; ordering fuses into the query's own statement. -/
def orderBy (q : Query ts s) (ks : Row ts s → List (OrderKey ts)) : Query ts s :=
  .spine (q.asPlainSpine.bind fun r => .order (ks r) (.yield r))

/-- `SELECT DISTINCT`. -/
def distinct (q : Query ts s) : Query ts s := .distinctC q

/-- `LIMIT`/`OFFSET` (rendered per dialect; SQL Server uses OFFSET/FETCH).
Applying it to an already-limited query wraps that query as a derived table —
stacking two LIMIT clauses on one statement is not valid SQL. -/
def limitOffset (q : Query ts s) (limit? offset? : Option Nat) : Query ts s :=
  match q with
  | .limitC .. => .limitC (.spine (.fromQ q (fun r => .yield r))) limit? offset?
  | _ => .limitC q limit? offset?

/-- `LIMIT n`. Chaining onto a pending `offset` merges into one clause
(`q.offset 10 |>.limit 5` ⇒ `LIMIT 5 OFFSET 10`); onto an existing limit it
wraps (`LIMIT` of a `LIMIT` via a derived table). -/
def limit (q : Query ts s) (n : Nat) : Query ts s :=
  match q with
  | .limitC q' none off? => .limitC q' (some n) off?
  | _ => q.limitOffset (some n) none

/-- `OFFSET n`. Chaining onto a pending `limit` merges into one clause
(`q.limit 5 |>.offset 10` ⇒ `LIMIT 5 OFFSET 10`); onto an existing offset it
wraps. -/
def offset (q : Query ts s) (n : Nat) : Query ts s :=
  match q with
  | .limitC q' lim? none => .limitC q' lim? (some n)
  | _ => q.limitOffset none (some n)

def union (q₁ q₂ : Query ts s) : Query ts s := .setOpC .union q₁ q₂
def intersect (q₁ q₂ : Query ts s) : Query ts s := .setOpC .intersect q₁ q₂
def except (q₁ q₂ : Query ts s) : Query ts s := .setOpC .except q₁ q₂

end Query

/-- A query grouped by keys, awaiting `having`/`orderBy`/`select` (staged
GroupBy → Having → OrderBy → Select surface; aggregates in a plain `where'`
are unrepresentable). -/
structure GroupedQuery (ts : Ctx) (s : Schema) where
  query : Query ts s
  keys : Row ts s → List (KeyExpr ts)
  having? : Option (Row ts s → SqlExpr ts .bool true) := none
  orderKeys? : Option (Row ts s → List (OrderKey ts)) := none

/-- `GROUP BY` one or more keys: `q.groupBy (fun c => [c["Age"].key])`. -/
def Query.groupBy (q : Query ts s) (keys : Row ts s → List (KeyExpr ts)) :
    GroupedQuery ts s :=
  ⟨q, keys, none, none⟩

/-- `HAVING` over the grouped rows; the `Agg` token builds aggregates:
`g.having (fun c a => 1 <. a.count)`. -/
def GroupedQuery.having (g : GroupedQuery ts s)
    (p : Row ts s → Agg → SqlExpr ts .bool nb) : GroupedQuery ts s :=
  { g with having? := some (fun r => (p r ⟨⟩).anyNull) }

/-- Aggregate-aware `ORDER BY` on a grouped query, before its `select`:
`g.orderBy (fun o a => [(a.sum o["Amount"]).desc, (a.count).asc])` — renders
inside the grouped statement (`… GROUP BY … HAVING … ORDER BY SUM(…) DESC`). -/
def GroupedQuery.orderBy (g : GroupedQuery ts s)
    (ks : Row ts s → Agg → List (OrderKey ts)) : GroupedQuery ts s :=
  { g with orderKeys? := some (fun r => ks r ⟨⟩) }

/-- Grouped projection over keys and aggregates:
`g.select (fun c a => ![c["Age"].as "Age", (a.count).as "Cnt"])`. -/
def GroupedQuery.select (g : GroupedQuery ts s) (f : Row ts s → Agg → Row ts s') :
    Query ts s' :=
  .groupedC g.query.asPlainSpine g.keys g.having? g.orderKeys? f

/-- A query returning a single scalar value. The `Bool` index is its
nullability: SUM/AVG/MIN/MAX over an empty group are NULL; `COUNT(*)`
never is. -/
inductive ScalarQuery : Ctx → SqlType → Bool → Type where
  | aggQ (op : AggOp) {ts : Ctx} {n : String} {c : SqlCol}
      (sp : SpineQ ts .plain [(n, c)]) : ScalarQuery ts c.ty true
  | countQ {ts : Ctx} {s : Schema} (sp : SpineQ ts .plain s) : ScalarQuery ts .int false

/-- `COUNT(*)` over a query. -/
def Query.count (q : Query ts s) : ScalarQuery ts .int false := .countQ q.asPlainSpine

/-- `SUM` over a single-column query (project first: `q.select … |>.sum`). -/
def Query.sum (q : Query ts [(n, c)]) : ScalarQuery ts c.ty true := .aggQ .sum q.asPlainSpine
def Query.avg (q : Query ts [(n, c)]) : ScalarQuery ts c.ty true := .aggQ .avg q.asPlainSpine
def Query.min (q : Query ts [(n, c)]) : ScalarQuery ts c.ty true := .aggQ .min q.asPlainSpine
def Query.max (q : Query ts [(n, c)]) : ScalarQuery ts c.ty true := .aggQ .max q.asPlainSpine

/-- Anything that can appear as a `from` source in a query comprehension:
tables (their context membership resolved by `HasTable`), and queries
themselves (plain-spine queries inline; grouped or boundary queries become
derived tables — decided statically on the `Terminal` index). The
continuation is spine-valued so the `query!` macro can fold clauses with
their terminal shapes known at elaboration time. -/
class QuerySource (ts : Ctx) (γ : Type) (s : outParam Schema) where
  bind : γ → (Row ts s → SpineQ ts g s') → SpineQ ts g s'

instance [HasTable ts.tables n s] : QuerySource ts (Table n s) s := ⟨.fromT⟩
instance : QuerySource ts (Query ts s) s :=
  ⟨fun q k =>
    match q with
    | .spine (g := .plain) sp => sp.bind k
    | q => .fromQ q k⟩

end LeanLinq
