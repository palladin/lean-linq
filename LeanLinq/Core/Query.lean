import LeanLinq.Core.Schema
import LeanLinq.Core.Bound

namespace LeanLinq

instance : Inhabited (SpineQ ts .plain s) := ⟨.yield default⟩
instance : Inhabited (SpineQ ts .grouped s) := ⟨.groupYield [] none [] default⟩
instance : Inhabited (QueryA ts s) := ⟨.spine (.yield default)⟩

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
      .fromT (inst := i) t (fun a => bindAux (f a) h k)
  | _, _, .joinT (inst := i) t on' f, h, k =>
      .joinT (inst := i) t on' (fun a => bindAux (f a) h k)
  | _, _, .joinLeftT (inst := i) t on' f, h, k =>
      .joinLeftT (inst := i) t on' (fun a => bindAux (f a) h k)
  | _, _, .fromQ q f,       h, k => .fromQ q (fun a => bindAux (f a) h k)

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
  | .groupYield ks hv ord r => .groupYield ks hv ord r
  | .guard b rest => .guard b rest.dropOrders
  | .order _ rest => rest.dropOrders
  | .fromT (inst := i) t f => .fromT (inst := i) t fun a => (f a).dropOrders
  | .joinT (inst := i) t on' f => .joinT (inst := i) t on' fun a => (f a).dropOrders
  | .joinLeftT (inst := i) t on' f => .joinLeftT (inst := i) t on' fun a => (f a).dropOrders
  | .fromQ q f => .fromQ q fun a => (f a).dropOrders

end SpineQ

/-- View a query as a *plain* spine suitable for extending (binding more
clauses onto it): plain spines unwrap; grouped spines and boundary-decorated
queries become a derived-table source. The grouped/plain distinction is an
O(1) match on the `Terminal` index — no spine traversal. -/
def QueryP.asPlainSpine {ρ : Schema → Type} : QueryP ρ ts s → SpineQP ρ ts .plain s
  | .spine (g := .plain) sp => sp
  | q => .fromQ q (fun a => .yield (.ofAtom a))

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
  | .fromQ q f, n =>
      q.cardAux n * (f ⟨s!"a{n}"⟩).cardAux (n + 1)

@[reducible] def QueryP.cardAux : QueryA ts s → Nat → Bound
  | .spine sp, n => sp.cardAux n
  | .distinctC q, n => q.cardAux n
  | .limitC q lim? _, n =>
      match lim? with
      | some l => min (q.cardAux n) (.fin l)
      | none => q.cardAux n
  | .setOpC .union a b, n => a.cardAux n + b.cardAux n
  | .setOpC .intersect a _, n => a.cardAux n
  | .setOpC .except a _, n => a.cardAux n

end

@[reducible] def QueryP.card (q : QueryA ts s) : Bound := q.cardAux 0

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
def QueryP.rowInvB : QueryA ts s → List (Values s) → Bool
  | .distinctC q, xs => Values.nodupB xs && q.rowInvB xs
  | .limitC q _ _, xs => q.rowInvB xs
  | .spine _, _ => true
  | .setOpC .., _ => true

/-- The row invariant as a proposition — decidable by construction. -/
def QueryP.RowInvA (q : QueryA ts s) (xs : List (Values s)) : Prop :=
  q.rowInvB xs = true

instance (q : QueryA ts s) (xs : List (Values s)) : Decidable (QueryP.RowInvA q xs) :=
  inferInstanceAs (Decidable (_ = true))

/-- The invariant is **sublist-closed**: boundary nodes pass selections
of the inner rows through, so every conjunct must survive that. -/
theorem Query.rowInvB_of_sublist {xs' xs : List (Values s)} :
    (q : QueryA ts s) → List.Sublist xs' xs →
    q.rowInvB xs = true → q.rowInvB xs' = true
  | .spine _, _, _ => rfl
  | .setOpC .., _, _ => rfl
  | .distinctC q, h, hi => by
      rw [QueryP.rowInvB, Bool.and_eq_true] at hi ⊢
      exact ⟨Values.nodupB_of_sublist h hi.1, Query.rowInvB_of_sublist q h hi.2⟩
  | .limitC q _ _, h, hi => Query.rowInvB_of_sublist q h hi

/-- Every invariant holds of the empty list — the total fallback the
fetch door needs when a live engine violates what the query's own
structure promises (provably unreachable in the reference semantics). -/
theorem Query.rowInvB_nil : (q : QueryA ts s) → q.rowInvB [] = true
  | .distinctC q => by simp [QueryP.rowInvB, Values.nodupB, rowInvB_nil q]
  | .limitC q _ _ => by simp [QueryP.rowInvB, rowInvB_nil q]
  | .spine _ => rfl
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
  .spine (.fromT t (fun a => .yield (.ofAtom a)))

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
  .spine (q.asPlainSpine.bind fun a =>
    .joinT t (fun b => on' a (.ofAtom b)) (fun b => .yield (sel a (.ofAtom b))))

/-- `LEFT JOIN t ON on'` with a result selector. The joined row's columns
are NULL-lifted (`s₂.asNull`) in both the predicate and the selector — an
unmatched left row pads them with NULL, and the types say so. -/
def leftJoin (q : QueryP ρ ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : RowP ρ ts s₁ → RowP ρ ts s₂.asNull → SqlExprP ρ ts ⟨.bool, nb⟩)
    (sel : RowP ρ ts s₁ → RowP ρ ts s₂.asNull → RowP ρ ts s') : QueryP ρ ts s' :=
  .spine (q.asPlainSpine.bind fun a =>
    .joinLeftT t (fun b => on' a (.ofAtom b)) (fun b => .yield (sel a (.ofAtom b))))

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
  | .limitC .. => .limitC (.spine (.fromQ q (fun a => .yield (.ofAtom a)))) limit? offset?
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

/-! Row-shaped spine constructors — the `query!` macro's emission targets:
the ctor fields bind atoms, the macro's user lambdas bind rows. -/

/-- `joinT` with row-shaped binders. -/
def SpineQP.joinR (t : Table n s) [HasTable ts.tables n s]
    (on' : RowP ρ ts s → SqlExprP ρ ts ⟨.bool, nb⟩)
    (k : RowP ρ ts s → SpineQP ρ ts g s') : SpineQP ρ ts g s' :=
  .joinT t (fun a => on' (.ofAtom a)) (fun a => k (.ofAtom a))

/-- `joinLeftT` with row-shaped binders (NULL-lifted). -/
def SpineQP.joinLeftR (t : Table n s) [HasTable ts.tables n s]
    (on' : RowP ρ ts s.asNull → SqlExprP ρ ts ⟨.bool, nb⟩)
    (k : RowP ρ ts s.asNull → SpineQP ρ ts g s') : SpineQP ρ ts g s' :=
  .joinLeftT t (fun a => on' (.ofAtom a)) (fun a => k (.ofAtom a))

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
  .spine (g.query.asPlainSpine.dropOrders.bind fun r =>
    .groupYield (g.keys r) (g.having?.map (· r))
      ((g.orderKeys?.map (· r)).getD []) (f r ⟨⟩))

/-- `COUNT(*)` over a query. -/
def QueryP.count (q : QueryP ρ ts s) : ScalarQueryP ρ ts .int := .countQ q.asPlainSpine

/-- `SUM` over a single-column query (project first: `q.select … |>.sum`). -/
def QueryP.sum (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .sum q.asPlainSpine
def QueryP.avg (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .avg q.asPlainSpine
def QueryP.min (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .min q.asPlainSpine
def QueryP.max (q : QueryP ρ ts [(n, ⟨t, nl⟩)]) : ScalarQueryP ρ ts ⟨t, true⟩ := .aggQ .max q.asPlainSpine

/-- Alias-instantiated view. -/
abbrev GroupedQuery : Ctx → Schema → Type := GroupedQueryP AliasOf

/-- Anything that can appear as a `from` source in a query comprehension:
tables (their context membership resolved by `HasTable`), and queries
themselves (plain-spine queries inline; grouped or boundary queries become
derived tables — decided statically on the `Terminal` index). The
continuation is spine-valued so the `query!` macro can fold clauses with
their terminal shapes known at elaboration time. -/
class QuerySource (ρ : Schema → Type) (ts : Ctx) (γ : Type u)
    (s : outParam Schema) where
  bind : γ → (RowP ρ ts s → SpineQP ρ ts g s') → SpineQP ρ ts g s'

/-- Tables source at every representation. -/
instance [HasTable ts.tables n s] : QuerySource ρ ts (Table n s) s :=
  ⟨fun t k => .fromT t (fun a => k (.ofAtom a))⟩

/-- A per-ρ query sources at its own representation (post-bundle, the
bundle-instance covers all ρ at once by instantiating). -/
instance : QuerySource ρ ts (QueryP ρ ts s) s :=
  ⟨fun q k =>
    match q with
    | .spine (g := .plain) sp => sp.bind k
    | q => .fromQ q (fun a => k (.ofAtom a))⟩

/-! ## The public bundle: one term, every representation

`QueryB` is the PHOAS quantification — a query polymorphic in its row
representation. The compiled view instantiates at `AliasOf`, the
(coming) evaluating view at `Values`, the counting view wherever it
likes: same term, no scope machinery, no uniformity assumptions.
Combinators delegate per-ρ; user lambdas elaborate with the implicit
`∀ {ρ}` inserted by Lean, so surface spellings do not change. -/

def QueryB (ts : Ctx) (s : Schema) : Type 1 :=
  ∀ ρ : Schema → Type, QueryP ρ ts s

namespace QueryB

variable {ts : Ctx} {s s' s₁ s₂ : Schema} {nb : Bool} {n : String}

def bind (q : QueryB ts s)
    (k : ∀ {ρ}, RowP ρ ts s → QueryP ρ ts s') : QueryB ts s' :=
  fun ρ => QueryP.bind (q ρ) k

def from' (t : Table n s) [HasTable ts.tables n s] : QueryB ts s :=
  fun _ => QueryP.from' t

def where' (q : QueryB ts s)
    (p : ∀ {ρ}, RowP ρ ts s → SqlExprP ρ ts ⟨.bool, nb⟩) : QueryB ts s :=
  fun ρ => QueryP.where' (q ρ) p

def select (q : QueryB ts s)
    (f : ∀ {ρ}, RowP ρ ts s → RowP ρ ts s') : QueryB ts s' :=
  fun ρ => QueryP.select (q ρ) f

def innerJoin (q : QueryB ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : ∀ {ρ}, RowP ρ ts s₁ → RowP ρ ts s₂ → SqlExprP ρ ts ⟨.bool, nb⟩)
    (sel : ∀ {ρ}, RowP ρ ts s₁ → RowP ρ ts s₂ → RowP ρ ts s') : QueryB ts s' :=
  fun ρ => QueryP.innerJoin (q ρ) t on' sel

def leftJoin (q : QueryB ts s₁) (t : Table n s₂) [HasTable ts.tables n s₂]
    (on' : ∀ {ρ}, RowP ρ ts s₁ → RowP ρ ts s₂.asNull → SqlExprP ρ ts ⟨.bool, nb⟩)
    (sel : ∀ {ρ}, RowP ρ ts s₁ → RowP ρ ts s₂.asNull → RowP ρ ts s') : QueryB ts s' :=
  fun ρ => QueryP.leftJoin (q ρ) t on' sel

def orderBy (q : QueryB ts s)
    (ks : ∀ {ρ}, RowP ρ ts s → List (OrderKeyP ρ ts)) : QueryB ts s :=
  fun ρ => QueryP.orderBy (q ρ) ks

def distinct (q : QueryB ts s) : QueryB ts s := fun ρ => QueryP.distinct (q ρ)
def limitOffset (q : QueryB ts s) (l? o? : Option Nat) : QueryB ts s :=
  fun ρ => QueryP.limitOffset (q ρ) l? o?
def limit (q : QueryB ts s) (k : Nat) : QueryB ts s :=
  fun ρ => QueryP.limit (q ρ) k
def offset (q : QueryB ts s) (k : Nat) : QueryB ts s :=
  fun ρ => QueryP.offset (q ρ) k

def union (a b : QueryB ts s) : QueryB ts s := fun ρ => QueryP.union (a ρ) (b ρ)
def intersect (a b : QueryB ts s) : QueryB ts s :=
  fun ρ => QueryP.intersect (a ρ) (b ρ)
def except (a b : QueryB ts s) : QueryB ts s := fun ρ => QueryP.except (a ρ) (b ρ)

/-- The grouped pipeline at the bundle level: callbacks are stored
polymorphically and instantiated with the query. -/
structure GroupedB (ts : Ctx) (s : Schema) : Type 1 where
  q : QueryB ts s
  keys : ∀ {ρ}, RowP ρ ts s → List (KeyExprP ρ ts)
  having? : Option (∀ {ρ}, RowP ρ ts s → SqlExprP ρ ts ⟨.bool, true⟩) := none
  orderKeys? : Option (∀ {ρ}, RowP ρ ts s → List (OrderKeyP ρ ts)) := none

def groupBy (q : QueryB ts s)
    (keys : ∀ {ρ}, RowP ρ ts s → List (KeyExprP ρ ts)) : GroupedB ts s :=
  ⟨q, keys, none, none⟩

def GroupedB.having (g : GroupedB ts s)
    (p : ∀ {ρ}, RowP ρ ts s → Agg → SqlExprP ρ ts ⟨.bool, nb⟩) : GroupedB ts s :=
  { g with having? := some fun r => SqlExprP.anyNull (p r ⟨⟩) }

def GroupedB.orderBy (g : GroupedB ts s)
    (ks : ∀ {ρ}, RowP ρ ts s → Agg → List (OrderKeyP ρ ts)) : GroupedB ts s :=
  { g with orderKeys? := some fun r => ks r ⟨⟩ }

def GroupedB.select (g : GroupedB ts s)
    (f : ∀ {ρ}, RowP ρ ts s → Agg → RowP ρ ts s') : QueryB ts s' :=
  fun ρ => GroupedQueryP.select
    ⟨g.q ρ, g.keys, g.having?.map (fun h r => h r),
     g.orderKeys?.map (fun ks r => ks r)⟩ f

end QueryB

/-- The scalar bundle — one term at every representation, like `QueryB`.
Correlated scalar subqueries are per-ρ `ScalarQueryP` values instead. -/
def ScalarB (ts : Ctx) (c : SqlType) : Type 1 :=
  ∀ ρ : Schema → Type, ScalarQueryP ρ ts c

/-- **The public scalar query is the bundle.** -/
abbrev ScalarQuery : Ctx → SqlType → Type 1 := ScalarB

namespace QueryB

/- Scalar aggregates at the bundle level: delegate per-ρ. -/
def count (q : QueryB ts s) : ScalarB ts .int := fun ρ => QueryP.count (q ρ)
def sum (q : QueryB ts [(n, ⟨t, nl⟩)]) : ScalarB ts ⟨t, true⟩ :=
  fun ρ => QueryP.sum (q ρ)
def avg (q : QueryB ts [(n, ⟨t, nl⟩)]) : ScalarB ts ⟨t, true⟩ :=
  fun ρ => QueryP.avg (q ρ)
def min (q : QueryB ts [(n, ⟨t, nl⟩)]) : ScalarB ts ⟨t, true⟩ :=
  fun ρ => QueryP.min (q ρ)
def max (q : QueryB ts [(n, ⟨t, nl⟩)]) : ScalarB ts ⟨t, true⟩ :=
  fun ρ => QueryP.max (q ρ)

end QueryB

/-- The bundle sources at every representation — by instantiating. -/
instance : QuerySource ρ ts (QueryB ts s) s :=
  ⟨fun q k => QuerySource.bind (q ρ) k⟩

/-! ## Expression-level subqueries — structural, at the ambient ρ

A subquery inside an expression is a subterm: it lives at the *same* ρ as
the expression, so a correlated subquery captures outer binders like any
other Lean value. An **uncorrelated** bundle drops into a per-ρ position by
instantiation (the coercion below). -/

/-- Anything that can stand as a subquery inside an expression at
representation ρ: a per-ρ query verbatim (the correlated case — it
captures outer binders, so it is pinned to the ambient ρ), a bundle by
instantiation (the uncorrelated case). -/
class SubQuerySource (ρ : Schema → Type) (ts : Ctx) (γ : Type u)
    (s : outParam Schema) where
  toQ : γ → QueryP ρ ts s

instance : SubQuerySource ρ ts (QueryP ρ ts s) s := ⟨id⟩
instance : SubQuerySource ρ ts (QueryB ts s) s := ⟨fun q => q ρ⟩

/-- `e IN (subquery)` — the subquery must project exactly one column of the
same type. -/
def SqlExprP.inQuery (e : SqlExprP ρ ts ⟨t, nf⟩) (q : γ)
    [i : SubQuerySource ρ ts γ [(cn, ⟨t, m⟩)]] : SqlExprP ρ ts ⟨.bool, true⟩ :=
  .inSub e (i.toQ q)

/-- `e NOT IN (subquery)` — `.not` of the three-valued IN (a NULL in the
subquery result turns a miss into UNKNOWN — the engines' semantics). -/
def SqlExprP.notInQuery (e : SqlExprP ρ ts ⟨t, nf⟩) (q : γ)
    [i : SubQuerySource ρ ts γ [(cn, ⟨t, m⟩)]] : SqlExprP ρ ts ⟨.bool, true⟩ :=
  .not (.inSub e (i.toQ q))

/-- `EXISTS (subquery)` — true iff the subquery returns any row; never
NULL, so a strict bool. Correlated outer references are the point:
`… |>.where' (fun c => SqlExpr.exists' (orders-of c))`. -/
def SqlExprP.exists' (q : γ) [i : SubQuerySource ρ ts γ s] :
    SqlExprP ρ ts .bool :=
  .existsSub (i.toQ q)

/-- `NOT EXISTS (subquery)`. -/
def SqlExprP.notExists (q : γ) [i : SubQuerySource ρ ts γ s] :
    SqlExprP ρ ts .bool :=
  .not (.existsSub (i.toQ q))

namespace SqlExpr
export SqlExprP (inQuery notInQuery exists' notExists)
end SqlExpr

/-- Embed a scalar aggregate query as an expression:
`c["Age"] >. (customers' |>.select … |>.avg).embed`. -/
def ScalarQueryP.embed (sq : ScalarQueryP ρ ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ :=
  .scalarSub sq

/-- Bundle spelling: instantiate at the ambient ρ and embed. -/
def ScalarB.embed (sq : ScalarB ts ⟨t, n⟩) : SqlExprP ρ ts ⟨t, true⟩ :=
  .scalarSub (sq ρ)

/-- **The public query is the bundle**: every pipeline produces one
term at every representation. -/
abbrev Query : Ctx → Schema → Type 1 := QueryB

/-- Bundle a ρ-polymorphic tree. Identity on the value, but the
`Query`-headed result type keeps generalized field notation working on
`query!`-defined constants (a bare `fun ρ => …` def would store the
eta-expanded pi type, whose head is `Function`). -/
def Query.mk (f : ∀ ρ, QueryP ρ ts s) : Query ts s := f

namespace Query
export QueryB (from')
end Query

/-- The row-count bound of a bundle — read at the compiled view (the
alignment theorem makes that the sound instantiation, permanently). -/
@[reducible] def Query.card (q : Query ts s) : Bound := (q AliasOf).card

/-- The row invariant of a bundle. -/
def Query.RowInv (q : Query ts s) (xs : List (Values s)) : Prop :=
  QueryP.RowInvA (q AliasOf) xs

namespace QueryB
export Query (card RowInv)
end QueryB

instance (q : Query ts s) (xs : List (Values s)) : Decidable (q.RowInv xs) :=
  inferInstanceAs (Decidable (_ = true))

end LeanLinq
