import LeanLinq.Eval.Query
import LeanLinq.Theorems
import LeanLinq.Core.Grade

/-! # `DbFetch` — database programs with a round-trip budget in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `DbFetch` closes the *host-language* half: a program that
talks to the database carries its round-trip bound as a type index — a
closed numeral for batched programs, an exact data-dependent expression
for per-row loops, a max-plus polynomial in table sizes for loops
priced by the database itself — and the grading prices composition
honestly —

- `fetch` costs `1`;
- `bind` (a data dependency) costs `m + n`: you cannot know what to ask
  until the previous answer arrives. (Independence — two fetches sharing
  a round — is applicative structure, not monadic; it returns with a
  free-applicative layer over this monad.)

The philosophy: **everything is representable; execution is gated by a
proof.** `exec` takes a budget and an obligation `r ≤ budget`, and each
shape has its proof story, up a ladder of evidence —

- batched programs: closed grades, `by decide`, silent;
- loops over data in hand (`let ys ← for x in xs do body`, the derived
  `forAll` bind-chain): the *exact* dynamic grade `k * xs.length`;
  `decide` once the list is literal, `omega` against a computed budget;
- loops over *just-fetched* rows, bounded deliberately: `fetchLimit q n`
  returns a length-refined list (`{xs // xs.length ≤ n}`; `LIMIT`
  really limits: `Query.run_limit_length_le`), and
  `for p in parents.val do body` fuses into `DbFetchP.forRows`, whose
  budget proof *is* the refinement. Bound `m + k * n`, closed, silent;
- loops over plain just-fetched rows, priced *symbolically*: no
  refinement, no restated bound — `let xs ← q.fetch` then
  `for p in xs do body` fuses into `forFetched`, whose evidence is
  `fetch`'s own contract (rows fit `q.gcard` at every σ). Grade
  `m + k * q.gcard`, in the database's own terms; `exec` refuses it
  statically (no closed budget dominates a table symbol), the sized
  door (`execWithin`) collapses and checks it against live sizes, and
  `execAll` runs unchecked. (Haxl repairs N+1 dynamically by batching;
  the grading surfaces it statically. `fetchFor` remains the bound-1
  batched door for any collection size.)

Under the sugar sits the dependent bind, `DbFetchP.bindD`: a continuation
whose grade may mention the value, priced by a bound `B` plus evidence
`∀ σ a, w.sp a σ → (g a).eval σ ≤ B.eval σ` — conditional on the
producer's strongest postcondition, pointwise at every table-size
valuation σ. `fetch`'s spec is the demonic contract (rows fit `q.gcard`
at every σ), whose `sp` is the contract itself (`sp_fetch`), so the
symbolic per-row loop `forQuery` is *derived*: its evidence consumes
the contract through the `eval` multiplication homomorphism.
Refinements (`forRows`) and user invariants (`bindD'`) are the same
door with simpler evidence.

The reference interpreter here is the in-memory evaluator — the same
denotational semantics the test suite differential-tests — and the native
drivers interpret the same tree against live engines, one statement per
round (`execIO`/`execPg`/`execMs`); `runWithP` is the adequacy door:
the run satisfies its spec, `Wp.sp`-formed about the actual result. -/

/-! `fetch!` do-sugar (declared before the namespace: syntax categories
must live at top level for quotation patterns to work). -/
declare_syntax_cat fetchClause

namespace LeanLinq


/-- The specification monad: weakest-precondition transformers over
table-size valuations — the continuation monad at `Prop` with a σ-Reader.
Given what you want of the result (`post`), the spec answers what must
hold at σ. Its monad laws are definitional, which is what lets the
computation type's indices compose by law rather than by packaging. -/
def Wp (α : Type) : Type := (α → Prop) → (String → Nat) → Prop

namespace Wp

def pure (a : α) : Wp α := fun post _ => post a

def bind (w : Wp α) (f : α → Wp β) : Wp β :=
  fun post σ => w (fun a => f a post σ) σ

/-- Spec refinement: anything `w₂` demands, `w₁` delivers. -/
def le (w₁ w₂ : Wp α) : Prop := ∀ post σ, w₂ post σ → w₁ post σ

/-- The trivial surface spec — the ⊤ of `le` (its obligations can never
be invoked), so **every** program relaxes to it for free. `DbFetch` is
the abbrev at this spec: the plain-typed surface. -/
def triv (α : Type) : Wp α := fun _ _ => False

/-- The strongest-postcondition reading: `a` is a possible result of a
`w`-specified run at σ. This is what the verified door hands back about
the *particular* result — the demonic ∀ in a spec, instantiated. -/
def sp (w : Wp α) (a : α) (σ : String → Nat) : Prop :=
  ∀ post, w post σ → post a

theorem pure_bind (a : α) (f : α → Wp β) : (Wp.pure a).bind f = f a := rfl
theorem bind_assoc (w : Wp α) (f : α → Wp β) (g : β → Wp γ) :
    (w.bind f).bind g = w.bind (fun a => (f a).bind g) := rfl
theorem triv_bind (f : α → Wp β) : (Wp.triv α).bind f = Wp.triv β := rfl

end Wp

/-- A database program with result type `α`, at most `r` round trips
(`r : Grade` — possibly symbolic in table sizes), and specification
`w : Wp α` — a **graded Dijkstra monad** over two effects.

Five constructors: three leaves (`pure`, `fetch`, `fetchCell`), one
sequencing (`bindD` — the monad bind carrying its round budget, whose
spec index is *computed* by `Wp.bind`), and the rule of consequence
(`weakenP`). Nothing else is primitive: loops are derived bind-chains
(mapM-shaped), and independence/batching (`seq`) belongs to a future
free-applicative layer, not the monad. -/
inductive DbFetchP (c : Ctx) : Grade → (α : Type) → Wp α → Type 1 where
  | pure : {α : Type} → (a : α) → DbFetchP c 0 α (Wp.pure a)
  -- the primitive fetch: rows are a PLAIN list, and the spec is the
  -- DEMONIC form of the contract — "whatever rows arrive, they fit the
  -- query's own symbolic card at σ". Demonic is forced: sizes don't
  -- determine contents, so no sound σ-spec can name the particular
  -- rows; the particular reading returns at the door via `Wp.sp`
  | fetch : {s : Schema} → (q : Query c s) →
      DbFetchP c 1 (List (Values s)) (fun post σ =>
        ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs)
  | fetchCell : {t : SqlPrim} → {n : Bool} → ScalarQuery c ⟨t, n⟩ →
      DbFetchP c 1 (Nullable t) (Wp.triv _)
  -- THE bind: value-dependent grade capped by `B`, justified by evidence
  -- conditional on what is actually TRUE of the producer's results —
  -- its strongest postcondition `Wp.sp` (for a fetch producer this is
  -- exactly the contract; for the trivial spec it is unconditional)
  | bindD : {m : Grade} → {α β : Type} → {w : Wp α} → {w₂ : α → Wp β} →
      {g : α → Grade} →
      DbFetchP c m α w → ((a : α) → DbFetchP c (g a) β (w₂ a)) →
      (B : Grade) →
      (∀ σ a, w.sp a σ → (g a).eval σ ≤ B.eval σ) →
      DbFetchP c (m + B) β (w.bind w₂)
  -- the rule of consequence — underivable (indices don't transport
  -- along implication), and the door through which every program
  -- relaxes to the plain surface
  | weakenP : {α : Type} → {r : Grade} → {w₁ w₂ : Wp α} →
      w₁.le w₂ → DbFetchP c r α w₁ → DbFetchP c r α w₂

/-- The plain surface: a program at the trivial spec — where every
corpus ascription lives, reached from any spec by `relax`. -/
abbrev DbFetch (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbFetchP c r α (Wp.triv α)

namespace DbFetch
export DbFetchP (pure fetch fetchCell bindD weakenP)
end DbFetch

namespace DbFetchP

/-- Reconciliation: `sp` of the fetch spec **is** the contract — the
demonic ∀ in the index, the pointwise fact at the door. -/
theorem sp_fetch {s : Schema} (q : Query c s) (xs : List (Values s))
    (σ : String → Nat) :
    Wp.sp (fun post σ => ∀ ys, ys.length ≤ (Query.gcard q).eval σ → post ys)
        xs σ ↔ xs.length ≤ (Query.gcard q).eval σ := by
  constructor
  · intro h
    exact h (fun ys => ys.length ≤ (Query.gcard q).eval σ) (fun _ hb => hb)
  · intro hb post hw
    exact hw xs hb

/-- Relax any spec to the plain surface — free, because `Wp.triv` is the
top of the refinement order. -/
def relax {w : Wp α} (x : DbFetchP c r α w) : DbFetch c r α :=
  .weakenP (fun _ _ h => h.elim) x

/-- Constant-grade sequencing on the plain surface: `bindD` with constant
`g` and unconditional evidence, both sides relaxed in — so bare-`fetch`
producers and `pure`-tailed continuations flow without ceremony. The
result index is `Wp.triv` definitionally (`Wp.triv_bind`). -/
def bind {w : Wp α} {w₂ : α → Wp β} (x : DbFetchP c m α w)
    (k : (a : α) → DbFetchP c n β (w₂ a)) : DbFetch c (m + n) β :=
  .bindD (relax x) (fun a => relax (k a)) n (fun _ _ _ => Nat.le_refl _)

def map {w : Wp α} (f : α → β) (x : DbFetchP c r α w) : DbFetch c r β :=
  Grade.add_zero r ▸ bind x (fun a => .pure (f a))

/-- Reference interpreter: the in-memory evaluator. Total — `DbFetch` is a
reflexive inductive, so structural recursion covers the `bindD`
continuation applied to any value. -/
def runWith (ee : EvalEnv c) : {r : Grade} → {α : Type} → {w : Wp α} →
    DbFetchP c r α w → Except EvalError α
  | _, _, _, .pure a => Except.ok a
  | _, _, _, .fetch q => q.evalRows ee
  | _, _, _, .fetchCell sq => sq.evalCell ee
  | _, _, _, .bindD x f _ _ => do runWith ee (f (← runWith ee x))
  | _, _, _, .weakenP _ x => runWith ee x

/-- The **adequacy** door: the run satisfies its spec. Same semantics as
`runWith`, but the result carries `Wp.sp w` — every demand the spec can
back is a fact about *this* result at *this* run's sizes. The `fetch`
arm does not check its contract, it **constructs** it (`run_gcard` as
`evalRows_gcard_le`); `bindD` chains the producer's `sp` through the
continuation — pure logic, no side conditions; `weakenP` transports
along the refinement. -/
def runWithP (ee : EvalEnv c) : {r : Grade} → {α : Type} → {w : Wp α} →
    DbFetchP c r α w →
    Except EvalError {a : α // w.sp a (TableEnv.sizes ee.tables)}
  | _, _, _, .pure a => .ok ⟨a, fun _ hp => hp⟩
  | _, _, _, .fetch q =>
      match hev : q.evalRows ee with
      | .ok xs => .ok ⟨xs, fun _ hw => hw xs (Query.evalRows_gcard_le q hev)⟩
      | .error e => .error e
  | _, _, _, .fetchCell sq => do .ok ⟨← sq.evalCell ee, fun _ h => h.elim⟩
  | _, _, _, .bindD x f _ _ => do
      let ⟨a, ha⟩ ← runWithP ee x
      let ⟨b, hb⟩ ← runWithP ee (f a)
      .ok ⟨b, fun post hw => hb post (ha _ hw)⟩
  | _, _, _, .weakenP h x => do
      let ⟨a, ha⟩ ← runWithP ee x
      .ok ⟨a, fun post hw => ha post (h post _ hw)⟩

/-- The model handler, *instrumented*: same semantics as `runWith`, plus
the count of rounds actually performed. This is what a symbolic price
certifies against: for a program of grade `r`, the pin is
`(runCount ee prog).2 ≤ (r.eval ee.tables.sizes)` — the price
collapsed against the model's own sizes. -/
def runCount (ee : EvalEnv c) : {r : Grade} → {α : Type} → {w : Wp α} →
    DbFetchP c r α w → Except EvalError (α × Nat)
  | _, _, _, .pure a => Except.ok (a, 0)
  | _, _, _, .fetch q => do Except.ok ((← q.evalRows ee), 1)
  | _, _, _, .fetchCell sq => do Except.ok ((← sq.evalCell ee), 1)
  | _, _, _, .bindD x f _ _ => do
      let (a, m) ← runCount ee x
      let (b, n) ← runCount ee (f a)
      Except.ok (b, m + n)
  | _, _, _, .weakenP _ x => runCount ee x

/-- The execution door: declare a round budget, prove you fit in it. For
closed grades (every batched program) the obligation discharges silently by
`decide`; a data-dependent grade (`xs.length` for runtime `xs`) is not
decidable at elaboration, so the caller supplies the proof — by bounding
the collection or computing the budget from it. A grade over data that
exists only inside the program (just-fetched rows) has no proof to
give: that is N+1, rejected. -/
def exec {w : Wp α} (f : DbFetchP c r α w) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : Except EvalError α :=
  runWith ⟨env, ps, now⟩ f

/-- The **sized** door: a symbolic grade collapses against the model's
own table sizes, and the budget check runs *there* — the door for
programs priced in the database's terms (`customers.size + 1`). -/
def execWithin {w : Wp α} (f : DbFetchP c r α w) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  if r.eval (TableEnv.sizes env) ≤ budget then
    runWith ⟨env, ps, now⟩ f
  else
    .error (.internal s!"round budget exceeded: the program's grade exceeds {budget} at this database's sizes")

/-- The unchecked door: no budget, no obligation — interprets any
program at any grade. The explicit opt-out, visible at the call site. -/
def execAll {w : Wp α} (f : DbFetchP c r α w) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  runWith ⟨env, ps, now⟩ f

/-- Restate a bound as a provably equal one — `1 * ids.length` as
`ids.length`, and so on. The index a program *infers* is built
syntactically from the combinators; equalities like `Nat.one_mul` are
theorems, not reductions, so the elaborator will not rewrite them away.
This is the bridge, and `fetch!` applies it automatically. -/
def withBound {w : Wp α} (x : DbFetchP c m α w) {n : Grade}
    (h : m = n := by first
      | rfl
      | decide
      | ((simp only [Grade.ofNat_eq_nat, Grade.nat_add,
            Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
            Grade.nat_zero_add, Grade.add_nat_zero]) <;>
         first
           | rfl
           | (apply congrArg Grade.nat; omega))) : DbFetchP c n α w :=
  h ▸ x

/-- Grade weakening: a program bounded by `m` is bounded by any `n ≥ m` —
derived, not primitive (`bindD` over `pure ()`), and the spec survives
untouched because the cont-monad's left unit is definitional. -/
def weaken {w : Wp α} (x : DbFetchP c m α w) (n : Grade)
    (h : m ≤ n := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : DbFetchP c n α w :=
  Grade.zero_add n ▸
    (DbFetchP.bindD (.pure ()) (fun _ => x) n (fun σ _ _ => h σ))

/-- `bindD` with its budget proof discharged automatically where possible:
closed facts silently, and the `fetchLimit` refinement (`a.property`,
bare or under the loop's `k *`) when the value is length-refined.
Anything else needs an explicit proof — that is the door doing its job. -/
def bindD' {α β : Type} {w : Wp α} {w₂ : α → Wp β} {g : α → Grade}
    (x : DbFetchP c m α w)
    (f : (a : α) → DbFetchP c (g a) β (w₂ a)) (B : Grade)
    (h : ∀ a, g a ≤ B := by
      intro a
      try simp only [_root_.LeanLinq.Grade.ofNat_eq_nat,
        _root_.LeanLinq.Grade.nat_add,
        _root_.LeanLinq.Grade.nat_mul, _root_.LeanLinq.Grade.nat_one_mul,
        _root_.LeanLinq.Grade.mul_nat_one, Nat.one_mul, Nat.mul_one]
      first
        | exact _root_.LeanLinq.Grade.le_refl _
        | (apply _root_.LeanLinq.Grade.nat_le_nat; omega)
        | exact _root_.LeanLinq.Grade.nat_le_nat a.property
        | fail "cannot bound the dependent continuation — fetch the collection through fetchLimit, or supply the proof") :
    DbFetch c (m + B) β :=
  .bindD (relax x) (fun a => relax (f a)) B (fun σ a _ => h a σ)

/-! ## The derived loop — `forAll` as a bind-chain, mapM-shaped

The loop is not a constructor: it is the fold of its bodies through
`bindD`, at the exact recursion grade, then **semantically** weakened to
the multiplicative public grade (form-level distributivity of canonical
grades is false — `k*n + k` and `k*(n+1)` are eval-equal, not
form-equal — so the bridge is `Grade.eval_add_le`, pointwise). -/

/-- The exact grade of the bind-chain: `k`, once per element. -/
def loopGrade (k : Grade) : List α → Grade
  | [] => 0
  | _ :: as => k + loopGrade k as

theorem le_loopGrade {k : Grade} :
    (xs : List α) → loopGrade k xs ≤ k * Grade.nat xs.length
  | [] => by
      intro σ
      rw [Grade.eval_mul, Grade.eval_nat]
      simp [loopGrade]
  | a :: as => by
      intro σ
      have ih := le_loopGrade (k := k) as σ
      rw [Grade.eval_mul, Grade.eval_nat] at ih ⊢
      calc (loopGrade k (a :: as)).eval σ
          ≤ k.eval σ + (loopGrade k as).eval σ := Grade.eval_add_le σ ..
        _ ≤ k.eval σ + k.eval σ * as.length := Nat.add_le_add_left ih _
        _ = k.eval σ * (as.length + 1) := by rw [Nat.mul_succ]; omega

def loopAux {k : Grade} : (xs : List α) → (f : (a : α) → DbFetch c k β) →
    DbFetch c (loopGrade k xs) (List β)
  | [], _ => relax (.pure [])
  | a :: as, f =>
      DbFetchP.bindD (f a)
        (fun b => Grade.add_zero (loopGrade k as) ▸
          DbFetchP.bindD (loopAux as f) (fun bs => relax (.pure (b :: bs)))
            0 (fun _ _ _ => Nat.le_refl _))
        (loopGrade k as) (fun _ _ _ => Nat.le_refl _)

/-- The per-row loop over a collection in hand — derived, exact grade
`k * xs.length`. Bodies at any spec flow in (relaxed): a bare `.fetch`
body is welcome. -/
def forAll {w₂ : α → Wp β} (xs : List α)
    (f : (a : α) → DbFetchP c k β (w₂ a)) :
    DbFetch c (k * Grade.nat xs.length) (List β) :=
  weaken (loopAux xs (fun a => relax (f a))) _ (le_loopGrade xs)

/-- The post-fetch loop, fused: fetch a **length-refined** collection
(`fetchLimit`), then run `f` per row. The subtype carries the budget
proof — the grade `m + k * n` is closed whenever the bounds are
literals. `fetch!` produces it for `let x ← e` immediately followed by
`for p in x.val do body`. -/
def forRows {n : Nat} {w : Wp {xs : List α // xs.length ≤ n}}
    {w₂ : α → Wp β}
    (x : DbFetchP c m {xs : List α // xs.length ≤ n} w)
    (f : (a : α) → DbFetchP c k β (w₂ a)) :
    DbFetch c (m + k * Grade.nat n) (List β) :=
  .bindD (relax x) (fun a => forAll a.val f) (k * Grade.nat n)
    (fun σ a _ => Grade.mul_le_mul_left k (Grade.nat_le_nat a.property) σ)

/-- The post-fetch loop over **plain** rows: the producer's spec is
`fetch`'s — the demonic contract — and its `sp` (the contract itself,
by `sp_fetch`) is the budget evidence, transported through the
multiplication homomorphism. `q` is implicit, recovered from the spec.
`fetch!` produces it for `let xs ← e` immediately followed by
`for p in xs do body`. -/
def forFetched {q : Query c s} {w₂ : Values s → Wp β}
    (x : DbFetchP c m (List (Values s)) (fun post σ =>
      ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs))
    (f : (v : Values s) → DbFetchP c k β (w₂ v)) :
    DbFetch c (m + k * Query.gcard q) (List β) :=
  relax (.bindD x (fun xs => forAll xs f) (k * Query.gcard q)
    (fun σ xs hsp => by
      rw [Grade.eval_mul, Grade.eval_mul, Grade.eval_nat]
      exact Nat.mul_le_mul_left _ ((sp_fetch q xs σ).mp hsp)))

/-- Fetch `q` and run `f` per row, the whole loop priced by the query's
own symbolic card: grade `1 + k * q.gcard` — the N+1 in the database's
own terms. **Derived, not primitive**: `forFetched` over the primitive
`fetch`. -/
def forQuery {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (w₂ v)) :
    DbFetch c (1 + k * Query.gcard q) (List β) :=
  forFetched (.fetch q) f

end DbFetchP

/-- The batched door: fetch for a whole runtime key set in **one** round —
the keys become an `IN (…)` list inside a single statement, so a thousand
parents still cost grade 1. This is how N+1 collapses to 1+1. -/
def DbFetchP.fetchFor [SqlLit t] (keys : List t.interp)
    (mk : (∀ {ρ}, List (SqlExprP ρ c ⟨t, true⟩)) → Query c s) :
    DbFetch c 1 (List (Values s)) :=
  DbFetchP.map id (DbFetchP.fetch (mk fun {ρ} => keys.map fun k => .widen (SqlLit.lit k)))

/-- Fetch at most `n` rows, **with the bound in the type**: applies
`LIMIT n` to the query and returns a length-refined list — the evidence
a dependent composition (`bindD`/`forRows`) needs, produced by the query
itself. The `LIMIT` is the engine's; the client only *checks* the
length to realize the proof — the rows pass through untouched
(provably so in the reference semantics: `Query.run_limit_length_le`),
and the `take` clamp fires only against a disagreeing engine. -/
def DbFetchP.fetchLimit (q : Query c s) (n : Nat) :
    DbFetch c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbFetchP.map (fun xs =>
    if h : xs.length ≤ n then ⟨xs, h⟩
    else ⟨xs.take n, List.length_take_le n _⟩)
    (DbFetchP.fetch (q.limit n))

/-! Pipeline-flowing spellings: a query ends in `|>.fetch` /
`|>.fetchLimit n` instead of being wrapped in a prefix call — same
constructors, dot-notation on the query. -/

/-- `q.fetch` — the query as a one-round program. The rows are a plain
list; the contract (rows fit `gcard` at every σ) is the spec, demonic —
`bindD`'s evidence consumes it through `sp_fetch`. -/
def Query.fetch (q : Query c s) :
    DbFetchP c 1 (List (Values s)) (fun post σ =>
      ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs) :=
  .fetch q

/-- `q.forQuery f` — the per-row loop priced by the query's own card. -/
def Query.forQuery {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (w₂ v)) :
    DbFetch c (1 + k * Query.gcard q) (List β) :=
  DbFetchP.forQuery q f

/-! `fetch!`'s loop target, overloaded by the iteree: a plain list loops
by `forAll` (grade `k * |xs|`), a query by `forQuery` (grade
`1 + k * q.gcard` — the symbolic price). Two exports of one name; the
elaborator keeps the alternative that typechecks. -/

def LoopList.forLoop {w₂ : α → Wp β} (xs : List α)
    (f : (a : α) → DbFetchP c k β (w₂ a)) :
    DbFetch c (k * Grade.nat xs.length) (List β) :=
  DbFetchP.forAll xs f

def LoopQuery.forLoop {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (w₂ v)) :
    DbFetch c (1 + k * Query.gcard q) (List β) :=
  DbFetchP.forQuery q f

namespace DbFetch
export LeanLinq.LoopList (forLoop)
export LeanLinq.LoopQuery (forLoop)
end DbFetch

/-- `sc.fetch` — a scalar query as a one-round program. -/
def ScalarQuery.fetch (sc : ScalarQuery c ⟨t, n⟩) : DbFetch c 1 (Nullable t) :=
  .fetchCell sc

/-- `q.fetchLimit n` — the length-refined fetch, flowing:
`Query.from' … |>.orderBy … |>.fetchLimit 5`. -/
def Query.fetchLimit (q : Query c s) (n : Nat) :
    DbFetch c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbFetchP.fetchLimit q n

/-! ## `fetch!` — do-notation for the graded monad

`DbFetch` cannot be a `Monad` instance: its bind *changes the index*
(`m + n`), and hiding the grade to fit `Monad`'s fixed `m : Type → Type`
would blind `exec`'s budget check — the entire point. So the sugar is a
macro (the `query!` precedent): do-shaped clauses desugar to the graded
combinators and elaboration infers the grade.

```
def report : DbFetch c 2 _ := fetch! {
  let parents ← .fetch parentsQ
  let ids := extract parents
  let children ← .fetchFor ids childrenQ
  return (parents, children)
}
```

`let x ← e` is `DbFetch.bind`, `let x := e` a plain `let`,
`let ys ← for x in xs do body` is `DbFetch.forAll` (the per-row loop,
exact dynamic grade `k * xs.length`), and the final `return e` is
`DbFetch.pure` — grades compose as `m + n + …`, definitionally the
closed sum for batched programs, so `exec`'s `by decide` discharges
silently. Two niceties keep inferred grades readable: the final
`let ys ← e; return f ys` pair fuses into `map` (no trailing `+ 0`),
and the whole block is wrapped in `withBound`, so a type annotation may
state any provably equal spelling of the grade — `ids.length` where the
raw index is `1 * ids.length`. -/

syntax (name := fetchBind) "let " ident " ← " term : fetchClause
syntax (name := fetchForAll) "let " ident " ← " "for " ident " in " term:max
  " do " term : fetchClause
syntax (name := fetchLet) "let " ident " := " term : fetchClause
syntax (name := fetchRet) "return " term : fetchClause

scoped syntax (name := fetchProg)
  "fetch! " "{" withoutPosition(sepByIndentSemicolon(fetchClause)) "}" : term

open Lean in
/-- `let ys ← for x in xs do body` also parses as plain `let ys ← term`
(term-position `for`), so the parser emits a `choice` node — resolve it
in favor of the dedicated loop clause. -/
def resolveClause (c : Syntax) : Syntax :=
  if c.getKind == Lean.choiceKind then
    (c.getArgs.find? (·.isOfKind ``fetchForAll)).getD c[0]
  else c

open Lean in
/-- Fuse `let x ← e` immediately followed by a loop over `x` into the
post-fetch loop whose budget proof is carried by `e`'s result:
`for p in x.val do body` (length-refined rows — `fetchLimit`) becomes
`DbFetchP.forRows e (fun p => body)`, and `for p in x do body` (plain
rows — the refinement-free spelling) becomes `DbFetchP.forFetched`,
priced by the fetch's own contract (`k * q.gcard`). The binder spelling
is the syntactic marker; `x`'s binder disappears, so any other use of
`x` is an unknown-identifier error (fetch it separately if you need the
rows too). -/
private partial def fuseBoundedLoops : List Syntax → MacroM (List Syntax)
  | [] => return []
  | [c] => return [c]
  | c1 :: c2 :: rest => do
    if c1.isOfKind ``fetchBind && c2.isOfKind ``fetchForAll then
      let x := c1[1]
      let src := c2[6]
      if x.isIdent && src.isIdent && src.getId == x.getId.str "val" then
        let fused ← `(fetchClause| let $(⟨c2[1]⟩):ident ←
          LeanLinq.DbFetchP.forRows $(⟨c1[3]⟩) (fun $(⟨c2[4]⟩):ident => $(⟨c2[8]⟩)))
        return ← fuseBoundedLoops (fused :: rest)
      if x.isIdent && src.isIdent && src.getId == x.getId then
        let fused ← `(fetchClause| let $(⟨c2[1]⟩):ident ←
          LeanLinq.DbFetchP.forFetched $(⟨c1[3]⟩) (fun $(⟨c2[4]⟩):ident => $(⟨c2[8]⟩)))
        return ← fuseBoundedLoops (fused :: rest)
    return c1 :: (← fuseBoundedLoops (c2 :: rest))

open Lean in
@[macro fetchProg] def expandFetch : Lean.Macro := fun stx => do
  let clauses ← fuseBoundedLoops (stx[2].getSepArgs.map resolveClause).toList
  match clauses.reverse with
  | [] => Macro.throwError "fetch! must end with a `return` clause"
  | last :: revRest =>
    unless last.isOfKind ``fetchRet do
      Macro.throwErrorAt last "fetch! must end with a `return` clause"
    -- fuse the final `let ys ← e; return f ys` into `map` (grade `r`, not
    -- `r + 0`) so inferred grades stay clean
    let (init, revRest) ← do
      match revRest with
      | prev :: rest =>
        if prev.isOfKind ``fetchBind then
          pure (← `(LeanLinq.DbFetchP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩)) $(⟨prev[3]⟩)), rest)
        else if prev.isOfKind ``fetchForAll then
          pure (← `(LeanLinq.DbFetchP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩))
            (LeanLinq.DbFetch.forLoop $(⟨prev[6]⟩) (fun $(⟨prev[4]⟩) => $(⟨prev[8]⟩)))), rest)
        else
          pure (← `(LeanLinq.DbFetchP.pure $(⟨last[1]⟩)), revRest)
      | [] => pure (← `(LeanLinq.DbFetchP.pure $(⟨last[1]⟩)), revRest)
    let folded ← revRest.foldlM (init := init) fun (acc : TSyntax `term) c => do
      if c.isOfKind ``fetchBind then
        `(LeanLinq.DbFetchP.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchForAll then
        -- let y ← for x in xs do body — a list loops at its exact grade
        -- k * xs.length, a query at its symbolic price 1 + k * gcard
        `(LeanLinq.DbFetchP.bind
            (LeanLinq.DbFetch.forLoop $(⟨c[6]⟩) (fun $(⟨c[4]⟩) => $(⟨c[8]⟩)))
            (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchLet then
        `(let $(⟨c[1]⟩) := $(⟨c[3]⟩); $acc)
      else
        Macro.throwErrorAt c "expected `let x ← e`, `let x := e`, `let ys ← for x in xs do e`, or a final `return e`"
    `(LeanLinq.DbFetchP.withBound $folded)

namespace QueryB
export Query (fetch fetchLimit forQuery)
end QueryB

namespace ScalarB
export ScalarQuery (fetch)
end ScalarB

/-! ## Program-level specs

`DbFetch` programs are trees and `runWith` is their model handler, so a
spec proved against it — quantified over **every** environment — is a
fact about the *program*, established once; the same tree then meets a
live engine at an IO door. -/

/-- A limited query's symbolic card sits under its limit at every σ —
whatever else the query is (the `limit` arm mins a closed inner bound
or takes the limit itself). -/
theorem gcardAux_limitC_le {ts : Ctx} {s : Schema} (q : QueryA ts s)
    (l : Nat) (off? : Option Nat) (m : Nat) (σ : String → Nat) :
    ((QueryP.limitC q (some l) off?).gcardAux m).eval σ ≤ l := by
  show ((match (q.gcardAux m).closed? with
    | some k => Grade.nat (Nat.min k l)
    | none => Grade.nat l) : Grade).eval σ ≤ l
  cases (q.gcardAux m).closed? with
  | some k => rw [Grade.eval_nat]; exact Nat.min_le_right k l
  | none => rw [Grade.eval_nat]; exact Nat.le_refl l

theorem gcard_limit_le {ts : Ctx} {s : Schema} (q : Query ts s) (n : Nat)
    (σ : String → Nat) : (Query.gcard (q.limit n)).eval σ ≤ n := by
  show ((QueryP.limit (q AliasOf) n).gcardAux 0).eval σ ≤ n
  unfold QueryP.limit
  split
  · exact gcardAux_limitC_le ..
  · unfold QueryP.limitOffset
    split
    · exact gcardAux_limitC_le ..
    · exact gcardAux_limitC_le ..

/-- The spec of the *program*, fully abstract: any query, any limit, any
size valuation — no run-hypothesis at all: `fetch`'s contract carries in
its *type* what this used to prove about the semantics. The page fits by
transitivity. -/
theorem fetchPage_fits {ts : Ctx} {s : Schema} (q : Query ts s) (n : Nat)
    {σ : String → Nat} {xs : List (Values s)}
    (hxs : xs.length ≤ (Query.gcard (q.limit n)).eval σ) :
    xs.length ≤ n :=
  Nat.le_trans hxs (gcard_limit_le q n σ)

end LeanLinq
