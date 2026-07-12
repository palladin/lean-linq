import LeanLinq.Core.Table
import LeanLinq.Core.Bound

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
inductive SpineQP (ρ : Schema → Type) : Ctx → Terminal → Schema → Type where
  | yield : {ts : Ctx} → {s : Schema} → RowP ρ ts s → SpineQP ρ ts .plain s
  -- A *grouped* terminal (the `groupBy`/`having`/`select` tail of a
  -- comprehension): GROUP BY keys, optional HAVING, and the grouped
  -- projection — all plain expressions over the rows bound earlier in the
  -- spine.
  | groupYield : {ts : Ctx} → {s : Schema} → List (KeyExprP ρ ts) →
      Option (SqlExprP ρ ts ⟨.bool, true⟩) → RowP ρ ts s → SpineQP ρ ts .grouped s
  | guard : {ts : Ctx} → {g : Terminal} → {s : Schema} → {nb : Bool} →
      SqlExprP ρ ts ⟨.bool, nb⟩ → SpineQP ρ ts g s → SpineQP ρ ts g s
  -- ORDER BY belongs to the statement being assembled, so it lives on the
  -- spine (keys already applied to the bound rows) and `bind` splices
  -- through it — projections/filters after `orderBy` fuse into the same
  -- flat statement (SQL Server in particular forbids ORDER BY inside a
  -- derived table). In a grouped spine the keys may reference aggregates.
  | order : {ts : Ctx} → {g : Terminal} → {s : Schema} →
      List (OrderKeyP ρ ts) → SpineQP ρ ts g s → SpineQP ρ ts g s
  | fromT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      [inst : HasTable ts.tables n s] → Table n s →
      (RowP ρ ts s → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  | joinT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (RowP ρ ts s → SqlExprP ρ ts ⟨.bool, nb⟩) →
      (RowP ρ ts s → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  -- LEFT JOIN: the joined row is NULL-lifted — its columns read as
  -- nullable in the ON predicate and everything downstream: the
  -- type-level truth of the padding row.
  | joinLeftT : {ts : Ctx} → {g : Terminal} → {n : String} → {s s' : Schema} →
      {nb : Bool} → [inst : HasTable ts.tables n s] → Table n s →
      (RowP ρ ts s.asNull → SqlExprP ρ ts ⟨.bool, nb⟩) →
      (RowP ρ ts s.asNull → SpineQP ρ ts g s') → SpineQP ρ ts g s'
  | fromQ : {ts : Ctx} → {g : Terminal} → {s s' : Schema} → QueryP ρ ts s →
      (RowP ρ ts s → SpineQP ρ ts g s') → SpineQP ρ ts g s'

/-- A full query: a spine (of either terminal shape), or a spine decorated by
*boundary* clauses that `bind` must not splice through (DISTINCT,
LIMIT/OFFSET, pipeline GROUP BY/HAVING, set operations) — binding over them
wraps the query as a derived table, which is exactly SQL's semantics.

Use the `query! { … }` syntax or the pipeline smart constructors rather than
the raw constructors. -/
inductive QueryP (ρ : Schema → Type) : Ctx → Schema → Type where
  | spine : {ts : Ctx} → {g : Terminal} → {s : Schema} → SpineQP ρ ts g s → QueryP ρ ts s
  | distinctC : {ts : Ctx} → {s : Schema} → QueryP ρ ts s → QueryP ρ ts s
  | limitC : {ts : Ctx} → {s : Schema} → QueryP ρ ts s → Option Nat → Option Nat → QueryP ρ ts s
  | groupedC : {ts : Ctx} → {s s' : Schema} → SpineQP ρ ts .plain s →
      (RowP ρ ts s → List (KeyExprP ρ ts)) →
      Option (RowP ρ ts s → SqlExprP ρ ts ⟨.bool, true⟩) →
      Option (RowP ρ ts s → List (OrderKeyP ρ ts)) →
      (RowP ρ ts s → Agg → RowP ρ ts s') → QueryP ρ ts s'
  | setOpC : {ts : Ctx} → {s : Schema} → SetOp → QueryP ρ ts s → QueryP ρ ts s → QueryP ρ ts s

end

/-- Alias-instantiated views — the spellings the library writes. -/
abbrev SpineQ : Ctx → Terminal → Schema → Type := SpineQP AliasOf
abbrev Query : Ctx → Schema → Type := QueryP AliasOf

instance : Inhabited (SpineQ ts .plain s) := ⟨.yield default⟩
instance : Inhabited (SpineQ ts .grouped s) := ⟨.groupYield [] none default⟩
instance : Inhabited (Query ts s) := ⟨.spine (.yield default)⟩

namespace SpineQ

/-- Implementation of `bind`, generalized over the terminal index:
structural recursion over an indexed family needs the index to be a
*variable*, so we recurse at `SpineQ ts g₀ s` carrying the proof
`g₀ = .plain` and discharge the `groupYield` case with it (`nomatch` on
`.grouped = .plain` — impossibility proved, not handled). -/
private def _root_.LeanLinq.SpineQP.bindAux {ρ : Schema → Type} :
    {g₀ : Terminal} → {s : Schema} → SpineQP ρ ts g₀ s →
    g₀ = .plain → (RowP ρ ts s → SpineQP ρ ts g s') → SpineQP ρ ts g s'
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
def _root_.LeanLinq.SpineQP.bind {ρ : Schema → Type} (sp : SpineQP ρ ts .plain s)
    (k : RowP ρ ts s → SpineQP ρ ts g s') : SpineQP ρ ts g s' :=
  SpineQP.bindAux sp rfl k

/-- Strip `ORDER BY` nodes from a spine. Pre-GROUP-BY row order is
meaningless to grouping and a set-operation operand's order is discarded
by the operation — SQL cannot even express either, so both construction
sites strip, keeping the compiled statement valid and the evaluator
aligned with it. -/
def _root_.LeanLinq.SpineQP.dropOrders {ρ : Schema → Type} :
    SpineQP ρ ts g s → SpineQP ρ ts g s
  | .yield r => .yield r
  | .groupYield ks hv r => .groupYield ks hv r
  | .guard b rest => .guard b rest.dropOrders
  | .order _ rest => rest.dropOrders
  | .fromT (inst := i) t f => .fromT (inst := i) t fun r => (f r).dropOrders
  | .joinT (inst := i) t on' f => .joinT (inst := i) t on' fun r => (f r).dropOrders
  | .joinLeftT (inst := i) t on' f => .joinLeftT (inst := i) t on' fun r => (f r).dropOrders
  | .fromQ q f => .fromQ q fun r => (f r).dropOrders

end SpineQ

/-- View a query as a *plain* spine suitable for extending (binding more
clauses onto it): plain spines unwrap; grouped spines and boundary-decorated
queries become a derived-table source. The grouped/plain distinction is an
O(1) match on the `Terminal` index — no spine traversal. -/
def QueryP.asPlainSpine {ρ : Schema → Type} : QueryP ρ ts s → SpineQP ρ ts .plain s
  | .spine (g := .plain) sp => sp
  | q => .fromQ q (fun r => .yield r)

/-! ## Cardinality: how many rows can a query return?

`card` computes an upper bound on the result size from the query value
itself, over the same `Bound` lattice that grades `DbFetch` round trips —
one lattice, two currencies. Bare-table sources are statically unbounded
(⊤ is the truth about them, until keys); **derived-table sources
multiply** — `from x in (q.limit 3)` contributes at most 3 × the
continuation's bound. The continuation is priced at the evaluator's own
marker rows with the evaluator's own alias numbering (`n`, maintained
equal to the scope length): the soundness proof then compares the same
function application on both sides, which is what makes the precision
provable — no uniformity assumption about the HOAS continuation is
needed. For literal queries `card` reduces definitionally, so `by
decide` can consume it inside types. -/

mutual

@[reducible] def SpineQP.cardAux : SpineQ ts g s → Nat → Bound
  | .yield _, _ => .fin 1
  | .groupYield .., _ => .fin 1
  | .guard _ rest, n => rest.cardAux n
  | .order _ rest, n => rest.cardAux n
  -- a bare table's size is not a static fact — ⊤ is the honest bound
  | .fromT (inst := _) _ _, _ => .top
  | .joinT (inst := _) _ _ _, _ => .top
  | .joinLeftT (inst := _) _ _ _, _ => .top
  -- a derived table's size IS a static fact: its query's own card —
  -- priced at the evaluator's marker, so the bound is the one that runs
  | .fromQ (s := s₀) q f, n =>
      q.cardAux n * (f (Row.ofAlias s!"a{n}" s₀)).cardAux (n + 1)

@[reducible] def QueryP.cardAux : Query ts s → Nat → Bound
  | .spine sp, n => sp.cardAux n
  | .distinctC q, n => q.cardAux n
  | .limitC q lim? _, n =>
      match lim? with
      | some l => min (q.cardAux n) (.fin l)
      | none => q.cardAux n
  | .groupedC sp _ _ _ _, n => sp.cardAux n
  | .setOpC .union a b, n => a.cardAux n + b.cardAux n
  | .setOpC .intersect a _, n => a.cardAux n
  | .setOpC .except a _, n => a.cardAux n

end

@[reducible] def QueryP.card (q : Query ts s) : Bound := q.cardAux 0

/-! ## Row invariants: what the query's structure promises about its rows

The second compute-from-the-value family member (after `card`): facts
about the *result rows* harvested from the clauses. Bool-cored (like
`Bound.ble`), so decidability is free and the fetch door can realize
the proof by checking. Every conjunct must be **sublist-closed** (true
of a list ⇒ true of any sublist), because boundary nodes pass a
*selection* of the inner rows through (`limit` takes a prefix,
`distinct` erases duplicates) while transferring the inner invariant.

Phase A carvings: `distinct` contributes `Values.nodupB` (SQL's DISTINCT
notion — NULLs compare equal). Order facts need key-to-output-column
analysis and env-free `where'` facts need projection-survival analysis —
both later; their clauses contribute `true` for now, so the invariant
says less, never lies. The general env-parameterized form
(`RowInv q ps xs`) is the M3 design. -/
def QueryP.rowInvB : Query ts s → List (Values s) → Bool
  | .distinctC q, xs => Values.nodupB xs && q.rowInvB xs
  | .limitC q _ _, xs => q.rowInvB xs
  | .spine _, _ => true
  | .groupedC .., _ => true
  | .setOpC .., _ => true

/-- The row invariant as a proposition — decidable by construction. -/
def Query.RowInv (q : Query ts s) (xs : List (Values s)) : Prop :=
  q.rowInvB xs = true

instance (q : Query ts s) (xs : List (Values s)) : Decidable (q.RowInv xs) :=
  inferInstanceAs (Decidable (_ = true))

/-- The invariant is **sublist-closed**: boundary nodes pass selections
of the inner rows through, so every conjunct must survive that. -/
theorem Query.rowInvB_of_sublist {xs' xs : List (Values s)} :
    (q : Query ts s) → List.Sublist xs' xs →
    q.rowInvB xs = true → q.rowInvB xs' = true
  | .spine _, _, _ => rfl
  | .groupedC .., _, _ => rfl
  | .setOpC .., _, _ => rfl
  | .distinctC q, h, hi => by
      rw [QueryP.rowInvB, Bool.and_eq_true] at hi ⊢
      exact ⟨Values.nodupB_of_sublist h hi.1, Query.rowInvB_of_sublist q h hi.2⟩
  | .limitC q _ _, h, hi => Query.rowInvB_of_sublist q h hi

/-- Every invariant holds of the empty list — the total fallback the
fetch door needs when a live engine violates what the query's own
structure promises (provably unreachable in the reference semantics). -/
theorem Query.rowInvB_nil : (q : Query ts s) → q.rowInvB [] = true
  | .distinctC q => by simp [QueryP.rowInvB, Values.nodupB, rowInvB_nil q]
  | .limitC q _ _ => by simp [QueryP.rowInvB, rowInvB_nil q]
  | .spine _ => rfl
  | .groupedC .. => rfl
  | .setOpC .. => rfl

namespace QueryP

variable {ρ : Schema → Type}


/-- Monadic bind — the normalization workhorse: plain spines splice; grouped
spines and boundary queries wrap as derived tables (on both the receiver and
the continuation's results). -/
def bind (q : QueryP ρ ts s) (k : RowP ρ ts s → QueryP ρ ts s') : QueryP ρ ts s' :=
  .spine (q.asPlainSpine.bind (fun r => (k r).asPlainSpine))

/-- `FROM t` (named `from'` because `from` is a Lean keyword). -/
def from' (t : Table n s) [HasTable ts.tables n s] : QueryP ρ ts s :=
  .spine (.fromT t (fun r => .yield r))

/-- `WHERE p` (named `where'` because `where` is a Lean keyword). Splices the
predicate into the query's own WHERE clause. -/
def where' (q : QueryP ρ ts s) (p : RowP ρ ts s → SqlExprP ρ ts ⟨.bool, nb⟩) : QueryP ρ ts s :=
  .spine (q.asPlainSpine.bind fun r => .guard (p r) (.yield r))

/-- `SELECT f`: project each row into a new schema, replacing the query's
projection in place. -/
def select (q : QueryP ρ ts s) (f : RowP ρ ts s → RowP ρ ts s') : QueryP ρ ts s' :=
  .spine (q.asPlainSpine.bind fun r => .yield (f r))

/-- `INNER JOIN t ON on'` with a result selector. Splices into the spine, so
chained joins compile to one flat statement. -/
def innerJoin (q : QueryP ρ ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : RowP ρ ts s₁ → RowP ρ ts s₂ → SqlExprP ρ ts ⟨.bool, nb⟩)
    (sel : RowP ρ ts s₁ → RowP ρ ts s₂ → RowP ρ ts s') : QueryP ρ ts s' :=
  .spine (q.asPlainSpine.bind fun a => .joinT t (on' a) (fun b => .yield (sel a b)))

/-- `LEFT JOIN t ON on'` with a result selector. The joined row's columns
are NULL-lifted (`s₂.asNull`) in both the predicate and the selector — an
unmatched left row pads them with NULL, and the types say so. -/
def leftJoin (q : QueryP ρ ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : RowP ρ ts s₁ → RowP ρ ts s₂.asNull → SqlExprP ρ ts ⟨.bool, nb⟩)
    (sel : RowP ρ ts s₁ → RowP ρ ts s₂.asNull → RowP ρ ts s') : QueryP ρ ts s' :=
  .spine (q.asPlainSpine.bind fun a => .joinLeftT t (on' a) (fun b => .yield (sel a b)))

/-- `ORDER BY` with one or more directed keys:
`q.orderBy (fun c => [c["Name"].asc, c["Age"].desc])`. Keys reference the
query's *output* columns; ordering fuses into the query's own statement. -/
def orderBy (q : QueryP ρ ts s) (ks : RowP ρ ts s → List (OrderKeyP ρ ts)) : QueryP ρ ts s :=
  .spine (q.asPlainSpine.bind fun r => .order (ks r) (.yield r))

/-- `SELECT DISTINCT`. -/
def distinct (q : QueryP ρ ts s) : QueryP ρ ts s := .distinctC q

/-- `LIMIT`/`OFFSET` (rendered per dialect; SQL Server uses OFFSET/FETCH).
Applying it to an already-limited query wraps that query as a derived table —
stacking two LIMIT clauses on one statement is not valid SQL. -/
def limitOffset (q : QueryP ρ ts s) (limit? offset? : Option Nat) : QueryP ρ ts s :=
  match q with
  | .limitC .. => .limitC (.spine (.fromQ q (fun r => .yield r))) limit? offset?
  | _ => .limitC q limit? offset?

/-- `LIMIT n`. Chaining onto a pending `offset` merges into one clause
(`q.offset 10 |>.limit 5` ⇒ `LIMIT 5 OFFSET 10`); onto an existing limit it
wraps (`LIMIT` of a `LIMIT` via a derived table). -/
def limit (q : QueryP ρ ts s) (n : Nat) : QueryP ρ ts s :=
  match q with
  | .limitC q' none off? => .limitC q' (some n) off?
  | _ => q.limitOffset (some n) none

/-- `OFFSET n`. Chaining onto a pending `limit` merges into one clause
(`q.limit 5 |>.offset 10` ⇒ `LIMIT 5 OFFSET 10`); onto an existing offset it
wraps. -/
def offset (q : QueryP ρ ts s) (n : Nat) : QueryP ρ ts s :=
  match q with
  | .limitC q' lim? none => .limitC q' lim? (some n)
  | _ => q.limitOffset none (some n)

/-- A set-operation operand's ORDER BY is discarded by the operation (SQL
cannot express it), so spine operands are stripped at construction — the
compiler then emits them flat, and boundary operands (nested set ops,
LIMIT, DISTINCT, grouped) as derived tables. -/
private def asSetOperand : QueryP ρ ts s → QueryP ρ ts s
  | .spine sp => .spine sp.dropOrders
  | q => q

def union (q₁ q₂ : QueryP ρ ts s) : QueryP ρ ts s :=
  .setOpC .union (asSetOperand q₁) (asSetOperand q₂)
def intersect (q₁ q₂ : QueryP ρ ts s) : QueryP ρ ts s :=
  .setOpC .intersect (asSetOperand q₁) (asSetOperand q₂)
def except (q₁ q₂ : QueryP ρ ts s) : QueryP ρ ts s :=
  .setOpC .except (asSetOperand q₁) (asSetOperand q₂)

end QueryP

/-- A query grouped by keys, awaiting `having`/`orderBy`/`select` (staged
GroupBy → Having → OrderBy → Select surface; aggregates in a plain `where'`
are unrepresentable). -/
structure GroupedQueryP (ρ : Schema → Type) (ts : Ctx) (s : Schema) where
  query : QueryP ρ ts s
  keys : RowP ρ ts s → List (KeyExprP ρ ts)
  having? : Option (RowP ρ ts s → SqlExprP ρ ts ⟨.bool, true⟩) := none
  orderKeys? : Option (RowP ρ ts s → List (OrderKeyP ρ ts)) := none

/-- `GROUP BY` one or more keys: `q.groupBy (fun c => [c["Age"].key])`. -/
def QueryP.groupBy (q : QueryP ρ ts s) (keys : RowP ρ ts s → List (KeyExprP ρ ts)) :
    GroupedQueryP ρ ts s :=
  ⟨q, keys, none, none⟩

/-- `HAVING` over the grouped rows; the `Agg` token builds aggregates:
`g.having (fun c a => 1 <. a.count)`. -/
def GroupedQueryP.having (g : GroupedQueryP ρ ts s)
    (p : RowP ρ ts s → Agg → SqlExprP ρ ts ⟨.bool, nb⟩) : GroupedQueryP ρ ts s :=
  { g with having? := some (fun r => (p r ⟨⟩).anyNull) }

/-- Aggregate-aware `ORDER BY` on a grouped query, before its `select`:
`g.orderBy (fun o a => [(a.sum o["Amount"]).desc, (a.count).asc])` — renders
inside the grouped statement (`… GROUP BY … HAVING … ORDER BY SUM(…) DESC`). -/
def GroupedQueryP.orderBy (g : GroupedQueryP ρ ts s)
    (ks : RowP ρ ts s → Agg → List (OrderKeyP ρ ts)) : GroupedQueryP ρ ts s :=
  { g with orderKeys? := some (fun r => ks r ⟨⟩) }

/-- Grouped projection over keys and aggregates:
`g.select (fun c a => ![c["Age"].as "Age", (a.count).as "Cnt"])`. -/
def GroupedQueryP.select (g : GroupedQueryP ρ ts s) (f : RowP ρ ts s → Agg → RowP ρ ts s') :
    QueryP ρ ts s' :=
  .groupedC g.query.asPlainSpine.dropOrders g.keys g.having? g.orderKeys? f

/-- A query returning a single scalar value. The `Bool` index is its
nullability: SUM/AVG/MIN/MAX over an empty group are NULL; `COUNT(*)`
never is. -/
inductive ScalarQueryP (ρ : Schema → Type) : Ctx → SqlType → Type where
  | aggQ (op : AggOp) {ts : Ctx} {n : String} {t : SqlPrim} {nl : Bool}
      (sp : SpineQP ρ ts .plain [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩
  | countQ {ts : Ctx} {s : Schema} (sp : SpineQP ρ ts .plain s) : ScalarQueryP ρ ts .int

/-- `COUNT(*)` over a query. -/
def QueryP.count (q : QueryP ρ ts s) : ScalarQueryP ρ ts .int := .countQ q.asPlainSpine

/-- `SUM` over a single-column query (project first: `q.select … |>.sum`). -/
def QueryP.sum (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .sum q.asPlainSpine
def QueryP.avg (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .avg q.asPlainSpine
def QueryP.min (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .min q.asPlainSpine
def QueryP.max (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .max q.asPlainSpine

/-- Alias-instantiated views. -/
abbrev GroupedQuery : Ctx → Schema → Type := GroupedQueryP AliasOf
abbrev ScalarQuery : Ctx → SqlType → Type := ScalarQueryP AliasOf

namespace QueryP
export Query (RowInv)
end QueryP

/- Textual entry points stay pinned at the alias instantiation until the
∀ρ bundle flips them (`Query.from' …` spellings across the corpus). -/
def Query.from' (t : Table n s) [HasTable ts.tables n s] : Query ts s :=
  QueryP.from' t
def Query.distinct (q : Query ts s) : Query ts s := QueryP.distinct q
def Query.limitOffset (q : Query ts s) (l? o? : Option Nat) : Query ts s :=
  QueryP.limitOffset q l? o?
def Query.limit (q : Query ts s) (n : Nat) : Query ts s := QueryP.limit q n
def Query.offset (q : Query ts s) (n : Nat) : Query ts s := QueryP.offset q n

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
