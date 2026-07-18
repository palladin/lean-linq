import LeanLinq.Eval.Query
import LeanLinq.Eval.Statements
import LeanLinq.Theorems
import LeanLinq.Core.Grade

/-! # `Db` — database programs with a round-trip budget in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `Db` closes the *host-language* half: a program that
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
  `for p in parents.val do body` fuses into `DbP.forRows`, whose
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

Under the sugar sits the dependent bind, `DbP.bindD`: a continuation
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

/-! `db!` do-sugar (declared before the namespace: syntax categories
must live at top level for quotation patterns to work). -/
declare_syntax_cat fetchClause

namespace LeanLinq


/-- The specification monad: weakest-precondition transformers over
table-size valuations — the continuation monad at `Prop` with a σ-Reader.
Given what you want of the result (`post`), the spec answers what must
hold at σ. Its monad laws are definitional, which is what lets the
computation type's indices compose by law rather than by packaging. -/
def Wp (α : Type) : Type :=
  (α → (String → Nat) → Prop) → (String → Nat) → Prop

namespace Wp

def pure (a : α) : Wp α := fun post σ => post a σ

def bind (w : Wp α) (f : α → Wp β) : Wp β :=
  fun post σ => w (fun a σ' => f a post σ') σ

/-- Spec refinement: anything `w₂` demands, `w₁` delivers. -/
def le (w₁ w₂ : Wp α) : Prop := ∀ post σ, w₂ post σ → w₁ post σ

/-- The trivial surface spec — the ⊤ of `le` (its obligations can never
be invoked), so **every** program relaxes to it for free. `Db` is
the abbrev at this spec: the plain-typed surface. -/
def triv (α : Type) : Wp α := fun _ _ => False

/-- The strongest-postcondition reading: `a` is a possible result of a
`w`-specified run at σ. This is what the verified door hands back about
the *particular* result — the demonic ∀ in a spec, instantiated. -/
def sp (w : Wp α) (a : α) (σ₀ σ₁ : String → Nat) : Prop :=
  ∀ post, w post σ₀ → post a σ₁

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
inductive DbP (c : Ctx) : Grade → (α : Type) → Wp α → Type 1 where
  | pure : {α : Type} → (a : α) → DbP c 0 α (Wp.pure a)
  -- the primitive fetch: rows are a PLAIN list, and the spec is the
  -- DEMONIC form of the contract — "whatever rows arrive, they fit the
  -- query's own symbolic card at σ". Demonic is forced: sizes don't
  -- determine contents, so no sound σ-spec can name the particular
  -- rows; the particular reading returns at the door via `Wp.sp`
  | fetch : {s : Schema} → (q : Query c s) →
      DbP c 1 (List (Values s)) (fun post σ =>
        ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs σ)
  -- the scalar cell, with the spec its shape supports: a COUNT promises
  -- its value fits the spine's symbolic bound (demonic, like fetch);
  -- content aggregates promise nothing — sizes don't determine contents
  | fetchCell : {t : SqlPrim} → {n : Bool} → (sc : ScalarQuery c ⟨t, n⟩) →
      DbP c 1 (Nullable t) (fun post σ =>
        ∀ v, ScalarQueryP.cellBound (sc AliasOf) v σ → post v σ)
  -- THE bind: value-dependent grade capped by `B`, justified by evidence
  -- conditional on what is actually TRUE of the producer's results —
  -- its strongest postcondition `Wp.sp` (for a fetch producer this is
  -- exactly the contract; for the trivial spec it is unconditional)
  | bindD : {m : Grade} → {α β : Type} → {w : Wp α} → {w₂ : α → Wp β} →
      {g : α → Grade} →
      DbP c m α w → ((a : α) → DbP c (g a) β (w₂ a)) →
      (B : Grade) →
      (∀ σ a, w.sp a σ σ → (g a).eval σ ≤ B.eval σ) →
      DbP c (m + B) β (w.bind w₂)
  -- the write effects: one statement, one round, and each carries the
  -- strongest σ-transformer spec its observability supports — INSERT
  -- moves this table's size within [σ n, σ n + 1] (exact bump modulo
  -- duplicate names under the max) and touches nothing else; UPDATE
  -- preserves sizes exactly; DELETE shrinks demonically (contents
  -- decide how many rows die; sizes don't). Backed by the
  -- `HasTable.sizes_set_*` laws at the adequacy door
  | insert : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      InsertStmt c n s → DbP c 1 Nat (fun post σ =>
        ∀ σ', (∀ m, m ≠ n → σ' m = σ m) → σ n ≤ σ' n → σ' n ≤ σ n + 1 →
          post 1 σ')
  | update : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      UpdateStmt c n s → DbP c 1 Nat (fun post σ =>
        ∀ k, k ≤ σ n → post k σ)
  | delete : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      DeleteStmt c n s → DbP c 1 Nat (fun post σ =>
        ∀ σ' k, (∀ m, m ≠ n → σ' m = σ m) → σ' n ≤ σ n → σ n ≤ σ' n + k →
          post k σ')
  -- the rule of consequence — underivable (indices don't transport
  -- along implication), and the door through which every program
  -- relaxes to the plain surface
  | weakenP : {α : Type} → {r : Grade} → {w₁ w₂ : Wp α} →
      w₁.le w₂ → DbP c r α w₁ → DbP c r α w₂

/-- The plain surface: a program at the trivial spec — where every
corpus ascription lives, reached from any spec by `relax`. -/
abbrev Db (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbP c r α (Wp.triv α)

namespace Db
export DbP (pure fetch fetchCell insert update delete bindD weakenP)
end Db

namespace DbP

/-- Reconciliation: `sp` of the fetch spec **is** the contract — the
demonic ∀ in the index, the pointwise fact at the door. -/
theorem sp_fetch {s : Schema} (q : Query c s) (xs : List (Values s))
    (σ : String → Nat) :
    Wp.sp (fun post σ => ∀ ys, ys.length ≤ (Query.gcard q).eval σ → post ys σ)
        xs σ σ ↔ xs.length ≤ (Query.gcard q).eval σ := by
  constructor
  · intro h
    exact h (fun ys _ => ys.length ≤ (Query.gcard q).eval σ) (fun _ hb => hb)
  · intro hb post hw
    exact hw xs hb

/-- Relax any spec to the plain surface — free, because `Wp.triv` is the
top of the refinement order. -/
def relax {w : Wp α} (x : DbP c r α w) : Db c r α :=
  .weakenP (fun _ _ h => h.elim) x

/-- Constant-grade sequencing on the plain surface: `bindD` with constant
`g` and unconditional evidence, both sides relaxed in — so bare-`fetch`
producers and `pure`-tailed continuations flow without ceremony. The
result index is `Wp.triv` definitionally (`Wp.triv_bind`). -/
def bind {w : Wp α} {w₂ : α → Wp β} (x : DbP c m α w)
    (k : (a : α) → DbP c n β (w₂ a)) : Db c (m + n) β :=
  .bindD (relax x) (fun a => relax (k a)) n (fun _ _ _ => Nat.le_refl _)

def map {w : Wp α} (f : α → β) (x : DbP c r α w) : Db c r β :=
  Grade.add_zero r ▸ bind x (fun a => .pure (f a))

/-- The state-threading core: writes move the environment, reads use it
where they stand. Total — `Db` is a reflexive inductive, so
structural recursion covers the `bindD` continuation at any value. -/
def runSt (ps : ParamEnv c.params) (now : Option String) :
    {r : Grade} → {α : Type} → {w : Wp α} → DbP c r α w →
    TableEnv c.tables → Except EvalError (α × TableEnv c.tables)
  | _, _, _, .pure a, env => Except.ok (a, env)
  | _, _, _, .fetch q, env => do Except.ok (← q.evalRows ⟨env, ps, now⟩, env)
  | _, _, _, .fetchCell sq, env => do Except.ok (← sq.evalCell ⟨env, ps, now⟩, env)
  | _, _, _, .insert (inst := inst) i, env => do
      let (env', k) ← i.applyCount (inst := inst) env ps now
      Except.ok (k, env')
  | _, _, _, .update (inst := inst) u, env => do
      let (env', k) ← u.applyCount (inst := inst) env ps now
      Except.ok (k, env')
  | _, _, _, .delete (inst := inst) d, env => do
      let (env', k) ← d.applyCount (inst := inst) env ps now
      Except.ok (k, env')
  | _, _, _, .bindD x f _ _, env => do
      let (a, env') ← runSt ps now x env
      runSt ps now (f a) env'
  | _, _, _, .weakenP _ x, env => runSt ps now x env

/-- Reference interpreter: the in-memory evaluator, final environment
discarded (`runSt` keeps it). -/
def runWith (ee : EvalEnv c) {r : Grade} {α : Type} {w : Wp α}
    (x : DbP c r α w) : Except EvalError α :=
  (runSt ee.params ee.now x ee.tables).map (·.1)

/-- COUNT's cell really is bounded — `enumScopes_gcard_le` at the
top-level scope; content aggregates owe nothing. -/
theorem cellBound_of_evalCell {t : SqlPrim} {nb : Bool}
    (sq : ScalarQuery c ⟨t, nb⟩) {ee : EvalEnv c} {v : Nullable t}
    (h : sq.evalCell ee = .ok v) :
    ScalarQueryP.cellBound (sq AliasOf) v (TableEnv.sizes ee.tables) := by
  unfold ScalarQuery.evalCell at h
  generalize sq AliasOf = sa at h ⊢
  match sa, h with
  | .aggQ op sp, _ => trivial
  | .countQ sp, h => ?_
  rw [ScalarQueryP.evalCellIn.eq_def] at h
  try simp only at h
  obtain ⟨scs, hs, h⟩ := Except.bind_ok h
  try simp only [pure, Except.pure, Except.ok.injEq] at h
  try injection h with h
  subst h
  refine ⟨rfl, ?_⟩
  intro k hk
  injection hk with hk
  subst hk
  refine ⟨by omega, ?_⟩
  have hb := SpineQP.enumScopes_gcard_le sp rfl
    (scopes := [[]]) (fun sc hsc => by
      cases hsc with
      | head => rfl
      | tail _ hx => cases hx) hs
  simp only [List.length_singleton] at hb
  first
    | simpa [Int.toNat_natCast] using hb
    | simpa [Int.toNat_ofNat] using hb
    | omega

/-- What an INSERT does to sizes, from `apply`'s own semantics and the
`sizes_set_*` laws: foreign names fixed, this one in `[σ n, σ n + 1]`. -/
theorem sizes_of_insert {n : String} {s : Schema} [inst : HasTable c.tables n s]
    {i : InsertStmt c n s} {env env' : TableEnv c.tables}
    {ps : ParamEnv c.params} {now : Option String}
    {k : Nat} (h : i.applyCount env ps now = .ok (env', k)) :
    (∀ m, m ≠ n → TableEnv.sizes env' m = TableEnv.sizes env m) ∧
    TableEnv.sizes env n ≤ TableEnv.sizes env' n ∧
    TableEnv.sizes env' n ≤ TableEnv.sizes env n + 1 ∧ k = 1 := by
  unfold InsertStmt.applyCount at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · contradiction
  · split at h
    all_goals first
      | contradiction
      | (injection h with h
         injection h with h1 h2
         subst h1
         subst h2
         refine ⟨fun m hm => inst.sizes_set_other env _ m hm, ?_, ?_, rfl⟩
         · exact inst.sizes_set_mono env _ n
             (by simp [List.length_append])
         · refine Nat.le_trans (inst.sizes_set_le env _ n)
             (Nat.max_le.mpr ⟨?_, ?_⟩)
           · have := inst.rows_sizes env
             simp only [List.length_append, List.length_cons, List.length_nil]
             omega
           · exact Nat.le_succ _)

/-- UPDATE preserves sizes exactly: same row count in, same out. -/
theorem sizes_of_update {n : String} {s : Schema} [inst : HasTable c.tables n s]
    {u : UpdateStmt c n s} {env env' : TableEnv c.tables}
    {ps : ParamEnv c.params} {now : Option String}
    {k : Nat} (h : u.applyCount env ps now = .ok (env', k)) :
    (∀ m, TableEnv.sizes env' m = TableEnv.sizes env m) ∧
    k ≤ TableEnv.sizes env n := by
  unfold UpdateStmt.applyCount at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · contradiction
  · split at h
    all_goals first
      | contradiction
      | (rename_i rcs hrcs
         injection h with h
         injection h with h1 h2
         subst h1
         subst h2
         have hlen : (rcs.map (·.1)).length = (inst.rows env).length := by
           rw [List.length_map]
           exact List.length_mapM_except _ hrcs
         refine ⟨fun m => Nat.le_antisymm
             (inst.sizes_set_anti env _ m (Nat.le_of_eq hlen))
             (inst.sizes_set_mono env _ m (Nat.le_of_eq hlen.symm)), ?_⟩
         refine Nat.le_trans ?_ (inst.rows_sizes env)
         calc rcs.countP (·.2) ≤ rcs.length := List.countP_le_length
           _ = (inst.rows env).length := List.length_mapM_except _ hrcs)

/-- DELETE only shrinks: the survivors are a filter of the rows. -/
theorem sizes_of_delete {n : String} {s : Schema} [inst : HasTable c.tables n s]
    {d : DeleteStmt c n s} {env env' : TableEnv c.tables}
    {ps : ParamEnv c.params} {now : Option String}
    {k : Nat} (h : d.applyCount env ps now = .ok (env', k)) :
    (∀ m, m ≠ n → TableEnv.sizes env' m = TableEnv.sizes env m) ∧
    TableEnv.sizes env' n ≤ TableEnv.sizes env n ∧
    TableEnv.sizes env n ≤ TableEnv.sizes env' n + k := by
  unfold DeleteStmt.applyCount at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  all_goals first
    | contradiction
    | (rename_i rows hrows
       injection h with h
       injection h with h1 h2
       subst h1
       subst h2
       refine ⟨fun m hm => inst.sizes_set_other env _ m hm,
         inst.sizes_set_anti env _ n (List.length_filterM_except_le hrows),
         inst.sizes_set_drop env _ n⟩)

/-- The **adequacy** door: the run satisfies its spec. Same semantics as
`runWith`, but the result carries `Wp.sp w` — every demand the spec can
back is a fact about *this* result at *this* run's sizes. The `fetch`
arm does not check its contract, it **constructs** it (`run_gcard` as
`evalRows_gcard_le`); `bindD` chains the producer's `sp` through the
continuation — pure logic, no side conditions; `weakenP` transports
along the refinement. -/
def runWithP (ps : ParamEnv c.params) (now : Option String) :
    {r : Grade} → {α : Type} → {w : Wp α} → DbP c r α w →
    (env : TableEnv c.tables) →
    Except EvalError {p : α × TableEnv c.tables //
      w.sp p.1 (TableEnv.sizes env) (TableEnv.sizes p.2)}
  | _, _, _, .pure a, env => .ok ⟨(a, env), fun _ hp => hp⟩
  | _, _, _, .fetch q, env =>
      match hev : q.evalRows ⟨env, ps, now⟩ with
      | .ok xs => .ok ⟨(xs, env), fun _ hw => hw xs (Query.evalRows_gcard_le q hev)⟩
      | .error e => .error e
  | _, _, _, .fetchCell sq, env =>
      match hev : sq.evalCell ⟨env, ps, now⟩ with
      | .ok v => .ok ⟨(v, env), fun _ hw => hw v (cellBound_of_evalCell sq hev)⟩
      | .error e => .error e
  | _, _, _, .insert (inst := inst) i, env =>
      match hev : i.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ hw => by
            obtain ⟨hother, hlo, hhi, hk⟩ := sizes_of_insert hev
            subst hk
            exact hw _ hother hlo hhi⟩
      | .error e => .error e
  | _, _, _, .update (inst := inst) u, env =>
      match hev : u.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ hw => by
            obtain ⟨hσ, hk⟩ := sizes_of_update hev
            rw [funext hσ]
            exact hw k hk⟩
      | .error e => .error e
  | _, _, _, .delete (inst := inst) d, env =>
      match hev : d.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ hw => by
            obtain ⟨hother, hself, hdrop⟩ := sizes_of_delete hev
            exact hw _ k hother hself hdrop⟩
      | .error e => .error e
  | _, _, _, .bindD x f _ _, env => do
      let ⟨(a, env₁), ha⟩ ← runWithP ps now x env
      let ⟨(b, env₂), hb⟩ ← runWithP ps now (f a) env₁
      .ok ⟨(b, env₂), fun post hw => hb post (ha _ hw)⟩
  | _, _, _, .weakenP h x, env => do
      let ⟨(a, env'), ha⟩ ← runWithP ps now x env
      .ok ⟨(a, env'), fun post hw => ha post (h post _ hw)⟩

/-- The model handler, *instrumented*: same semantics as `runWith`, plus
the count of rounds actually performed. This is what a symbolic price
certifies against: for a program of grade `r`, the pin is
`(runCount ee prog).2 ≤ (r.eval ee.tables.sizes)` — the price
collapsed against the model's own sizes. -/
def runCountSt (ps : ParamEnv c.params) (now : Option String) :
    {r : Grade} → {α : Type} → {w : Wp α} → DbP c r α w →
    TableEnv c.tables → Except EvalError (α × TableEnv c.tables × Nat)
  | _, _, _, .pure a, env => Except.ok (a, env, 0)
  | _, _, _, .fetch q, env => do Except.ok (← q.evalRows ⟨env, ps, now⟩, env, 1)
  | _, _, _, .fetchCell sq, env => do Except.ok (← sq.evalCell ⟨env, ps, now⟩, env, 1)
  | _, _, _, .insert (inst := inst) i, env => do
      let (env', k) ← i.applyCount (inst := inst) env ps now
      Except.ok (k, env', 1)
  | _, _, _, .update (inst := inst) u, env => do
      let (env', k) ← u.applyCount (inst := inst) env ps now
      Except.ok (k, env', 1)
  | _, _, _, .delete (inst := inst) d, env => do
      let (env', k) ← d.applyCount (inst := inst) env ps now
      Except.ok (k, env', 1)
  | _, _, _, .bindD x f _ _, env => do
      let (a, env', m) ← runCountSt ps now x env
      let (b, env'', n) ← runCountSt ps now (f a) env'
      Except.ok (b, env'', m + n)
  | _, _, _, .weakenP _ x, env => runCountSt ps now x env

def runCount (ee : EvalEnv c) {r : Grade} {α : Type} {w : Wp α}
    (x : DbP c r α w) : Except EvalError (α × Nat) :=
  (runCountSt ee.params ee.now x ee.tables).map (fun (a, _, n) => (a, n))

/-- The execution door: declare a round budget, prove you fit in it. For
closed grades (every batched program) the obligation discharges silently by
`decide`; a data-dependent grade (`xs.length` for runtime `xs`) is not
decidable at elaboration, so the caller supplies the proof — by bounding
the collection or computing the budget from it. A grade over data that
exists only inside the program (just-fetched rows) has no proof to
give: that is N+1, rejected. -/
def exec {w : Wp α} (f : DbP c r α w) (budget : Nat) (env : TableEnv c.tables)
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
def execWithin {w : Wp α} (f : DbP c r α w) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  if r.eval (TableEnv.sizes env) ≤ budget then
    runWith ⟨env, ps, now⟩ f
  else
    .error (.internal s!"round budget exceeded: the program's grade exceeds {budget} at this database's sizes")

/-- The unchecked door: no budget, no obligation — interprets any
program at any grade. The explicit opt-out, visible at the call site. -/
def execAll {w : Wp α} (f : DbP c r α w) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  runWith ⟨env, ps, now⟩ f

/-- Restate a bound as a provably equal one — `1 * ids.length` as
`ids.length`, and so on. The index a program *infers* is built
syntactically from the combinators; equalities like `Nat.one_mul` are
theorems, not reductions, so the elaborator will not rewrite them away.
This is the bridge, and `db!` applies it automatically. -/
def withBound {w : Wp α} (x : DbP c m α w) {n : Grade}
    (h : m = n := by first
      | rfl
      | decide
      | ((simp only [Grade.ofNat_eq_nat, Grade.nat_add,
            Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
            Grade.nat_zero_add, Grade.add_nat_zero]) <;>
         first
           | rfl
           | (apply congrArg Grade.nat; omega))) : DbP c n α w :=
  h ▸ x

/-- Grade weakening: a program bounded by `m` is bounded by any `n ≥ m` —
derived, not primitive (`bindD` over `pure ()`), and the spec survives
untouched because the cont-monad's left unit is definitional. -/
def weaken {w : Wp α} (x : DbP c m α w) (n : Grade)
    (h : m ≤ n := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : DbP c n α w :=
  Grade.zero_add n ▸
    (DbP.bindD (.pure ()) (fun _ => x) n (fun σ _ _ => h σ))

/-- `bindD` with its budget proof discharged automatically where possible:
closed facts silently, and the `fetchLimit` refinement (`a.property`,
bare or under the loop's `k *`) when the value is length-refined.
Anything else needs an explicit proof — that is the door doing its job. -/
def bindD' {α β : Type} {w : Wp α} {w₂ : α → Wp β} {g : α → Grade}
    (x : DbP c m α w)
    (f : (a : α) → DbP c (g a) β (w₂ a)) (B : Grade)
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
    Db c (m + B) β :=
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

def loopAux {k : Grade} : (xs : List α) → (f : (a : α) → Db c k β) →
    Db c (loopGrade k xs) (List β)
  | [], _ => relax (.pure [])
  | a :: as, f =>
      DbP.bindD (f a)
        (fun b => Grade.add_zero (loopGrade k as) ▸
          DbP.bindD (loopAux as f) (fun bs => relax (.pure (b :: bs)))
            0 (fun _ _ _ => Nat.le_refl _))
        (loopGrade k as) (fun _ _ _ => Nat.le_refl _)

/-- The per-row loop over a collection in hand — derived, exact grade
`k * xs.length`. Bodies at any spec flow in (relaxed): a bare `.fetch`
body is welcome. -/
def forAll {w₂ : α → Wp β} (xs : List α)
    (f : (a : α) → DbP c k β (w₂ a)) :
    Db c (k * Grade.nat xs.length) (List β) :=
  weaken (loopAux xs (fun a => relax (f a))) _ (le_loopGrade xs)

/-- The post-fetch loop, fused: fetch a **length-refined** collection
(`fetchLimit`), then run `f` per row. The subtype carries the budget
proof — the grade `m + k * n` is closed whenever the bounds are
literals. `db!` produces it for `let x ← e` immediately followed by
`for p in x.val do body`. -/
def forRows {n : Nat} {w : Wp {xs : List α // xs.length ≤ n}}
    {w₂ : α → Wp β}
    (x : DbP c m {xs : List α // xs.length ≤ n} w)
    (f : (a : α) → DbP c k β (w₂ a)) :
    Db c (m + k * Grade.nat n) (List β) :=
  .bindD (relax x) (fun a => forAll a.val f) (k * Grade.nat n)
    (fun σ a _ => Grade.mul_le_mul_left k (Grade.nat_le_nat a.property) σ)

/-- The post-fetch loop over **plain** rows: the producer's spec is
`fetch`'s — the demonic contract — and its `sp` (the contract itself,
by `sp_fetch`) is the budget evidence, transported through the
multiplication homomorphism. `q` is implicit, recovered from the spec.
`db!` produces it for `let xs ← e` immediately followed by
`for p in xs do body`. -/
def forFetched {q : Query c s} {w₂ : Values s → Wp β}
    (x : DbP c m (List (Values s)) (fun post σ =>
      ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs σ))
    (f : (v : Values s) → DbP c k β (w₂ v)) :
    Db c (m + k * Query.gcard q) (List β) :=
  relax (.bindD x (fun xs => forAll xs f) (k * Query.gcard q)
    (fun σ xs hsp => by
      rw [Grade.eval_mul, Grade.eval_mul, Grade.eval_nat]
      exact Nat.mul_le_mul_left _ ((sp_fetch q xs σ).mp hsp)))

/-- Fetch `q` and run `f` per row, the whole loop priced by the query's
own symbolic card: grade `1 + k * q.gcard` — the N+1 in the database's
own terms. **Derived, not primitive**: `forFetched` over the primitive
`fetch`. -/
def forQuery {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbP c k β (w₂ v)) :
    Db c (1 + k * Query.gcard q) (List β) :=
  forFetched (.fetch q) f

end DbP

/-- The batched door: fetch for a whole runtime key set in **one** round —
the keys become an `IN (…)` list inside a single statement, so a thousand
parents still cost grade 1. This is how N+1 collapses to 1+1. -/
def DbP.fetchFor [SqlLit t] (keys : List t.interp)
    (mk : (∀ {ρ}, List (SqlExprP ρ c ⟨t, true⟩)) → Query c s) :
    Db c 1 (List (Values s)) :=
  DbP.map id (DbP.fetch (mk fun {ρ} => keys.map fun k => .widen (SqlLit.lit k)))

/-- Fetch at most `n` rows, **with the bound in the type**: applies
`LIMIT n` to the query and returns a length-refined list — the evidence
a dependent composition (`bindD`/`forRows`) needs, produced by the query
itself. The `LIMIT` is the engine's; the client only *checks* the
length to realize the proof — the rows pass through untouched
(provably so in the reference semantics: `Query.run_limit_length_le`),
and the `take` clamp fires only against a disagreeing engine. -/
def DbP.fetchLimit (q : Query c s) (n : Nat) :
    Db c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbP.map (fun xs =>
    if h : xs.length ≤ n then ⟨xs, h⟩
    else ⟨xs.take n, List.length_take_le n _⟩)
    (DbP.fetch (q.limit n))

/-! Pipeline-flowing spellings: a query ends in `|>.fetch` /
`|>.fetchLimit n` instead of being wrapped in a prefix call — same
constructors, dot-notation on the query. -/

/-- `q.fetch` — the query as a one-round program. The rows are a plain
list; the contract (rows fit `gcard` at every σ) is the spec, demonic —
`bindD`'s evidence consumes it through `sp_fetch`. -/
def Query.fetch (q : Query c s) :
    DbP c 1 (List (Values s)) (fun post σ =>
      ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs σ) :=
  .fetch q

/-- `q.forQuery f` — the per-row loop priced by the query's own card. -/
def Query.forQuery {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbP c k β (w₂ v)) :
    Db c (1 + k * Query.gcard q) (List β) :=
  DbP.forQuery q f

/-! `db!`'s loop target, overloaded by the iteree: a plain list loops
by `forAll` (grade `k * |xs|`), a query by `forQuery` (grade
`1 + k * q.gcard` — the symbolic price). Two exports of one name; the
elaborator keeps the alternative that typechecks. -/

def LoopList.forLoop {w₂ : α → Wp β} (xs : List α)
    (f : (a : α) → DbP c k β (w₂ a)) :
    Db c (k * Grade.nat xs.length) (List β) :=
  DbP.forAll xs f

def LoopQuery.forLoop {w₂ : Values s → Wp β} (q : Query c s)
    (f : (v : Values s) → DbP c k β (w₂ v)) :
    Db c (1 + k * Query.gcard q) (List β) :=
  DbP.forQuery q f

namespace Db
export LeanLinq.LoopList (forLoop)
export LeanLinq.LoopQuery (forLoop)
end Db

/-- `q.fetchCount` — ask how many rows `q` has, as a one-round program
whose spec is the clean demonic count bound: whatever number comes back
fits `q.gcard` at σ. Derived from `fetchCell (q.count)` — the decode and
the spine↔query bound bridge ride one `weakenP`. -/
def Query.fetchCount (q : Query c s) :
    DbP c 1 Nat (fun post σ =>
      ∀ n, n ≤ (Query.gcard q).eval σ → post n σ) := by
  refine DbP.withBound (n := 1) (.weakenP ?_
    (DbP.bindD (.fetchCell (q.count))
      (fun v => .pure (v.getD 0).toNat) 0 (fun _ _ _ => Nat.le_refl _)))
  intro post σ hpost v hcb
  rcases v with _ | k
  · cases hcb.1
  · refine hpost k.toNat ?_
    have hb := (hcb.2 k rfl).2
    have hbr : ((q AliasOf).asPlainSpine.gcardAux 0) = Query.gcard q := by
      show (QueryP.asPlainSpine (q AliasOf)).gcardAux 0 = (q AliasOf).gcardAux 0
      rw [QueryP.asPlainSpine.eq_def]
      split
      · rename_i sp heq
        rw [heq]
      · rfl
    rwa [hbr] at hb

/-- `sc.fetch` — a scalar query as a one-round program. -/
def ScalarQuery.fetch (sc : ScalarQuery c ⟨t, n⟩) : Db c 1 (Nullable t) :=
  .relax (.fetchCell sc)

/-- `q.fetchLimit n` — the length-refined fetch, flowing:
`Query.from' … |>.orderBy … |>.fetchLimit 5`. -/
def Query.fetchLimit (q : Query c s) (n : Nat) :
    Db c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbP.fetchLimit q n

/-! ## `db!` — do-notation for the graded monad

`Db` cannot be a `Monad` instance: its bind *changes the index*
(`m + n`), and hiding the grade to fit `Monad`'s fixed `m : Type → Type`
would blind `exec`'s budget check — the entire point. So the sugar is a
macro (the `query!` precedent): do-shaped clauses desugar to the graded
combinators and elaboration infers the grade.

```
def report : Db c 2 _ := db! {
  let parents ← .fetch parentsQ
  let ids := extract parents
  let children ← .fetchFor ids childrenQ
  return (parents, children)
}
```

`let x ← e` is `Db.bind`, `let x := e` a plain `let`,
`let ys ← for x in xs do body` is `Db.forAll` (the per-row loop,
exact dynamic grade `k * xs.length`), and the final `return e` is
`Db.pure` — grades compose as `m + n + …`, definitionally the
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
  "db! " "{" withoutPosition(sepByIndentSemicolon(fetchClause)) "}" : term

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
`DbP.forRows e (fun p => body)`, and `for p in x do body` (plain
rows — the refinement-free spelling) becomes `DbP.forFetched`,
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
          LeanLinq.DbP.forRows $(⟨c1[3]⟩) (fun $(⟨c2[4]⟩):ident => $(⟨c2[8]⟩)))
        return ← fuseBoundedLoops (fused :: rest)
      if x.isIdent && src.isIdent && src.getId == x.getId then
        let fused ← `(fetchClause| let $(⟨c2[1]⟩):ident ←
          LeanLinq.DbP.forFetched $(⟨c1[3]⟩) (fun $(⟨c2[4]⟩):ident => $(⟨c2[8]⟩)))
        return ← fuseBoundedLoops (fused :: rest)
    return c1 :: (← fuseBoundedLoops (c2 :: rest))

open Lean in
@[macro fetchProg] def expandFetch : Lean.Macro := fun stx => do
  let clauses ← fuseBoundedLoops (stx[2].getSepArgs.map resolveClause).toList
  match clauses.reverse with
  | [] => Macro.throwError "db! must end with a `return` clause"
  | last :: revRest =>
    unless last.isOfKind ``fetchRet do
      Macro.throwErrorAt last "db! must end with a `return` clause"
    -- fuse the final `let ys ← e; return f ys` into `map` (grade `r`, not
    -- `r + 0`) so inferred grades stay clean
    let (init, revRest) ← do
      match revRest with
      | prev :: rest =>
        if prev.isOfKind ``fetchBind then
          pure (← `(LeanLinq.DbP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩)) $(⟨prev[3]⟩)), rest)
        else if prev.isOfKind ``fetchForAll then
          pure (← `(LeanLinq.DbP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩))
            (LeanLinq.Db.forLoop $(⟨prev[6]⟩) (fun $(⟨prev[4]⟩) => $(⟨prev[8]⟩)))), rest)
        else
          pure (← `(LeanLinq.DbP.pure $(⟨last[1]⟩)), revRest)
      | [] => pure (← `(LeanLinq.DbP.pure $(⟨last[1]⟩)), revRest)
    let folded ← revRest.foldlM (init := init) fun (acc : TSyntax `term) c => do
      if c.isOfKind ``fetchBind then
        `(LeanLinq.DbP.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchForAll then
        -- let y ← for x in xs do body — a list loops at its exact grade
        -- k * xs.length, a query at its symbolic price 1 + k * gcard
        `(LeanLinq.DbP.bind
            (LeanLinq.Db.forLoop $(⟨c[6]⟩) (fun $(⟨c[4]⟩) => $(⟨c[8]⟩)))
            (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchLet then
        `(let $(⟨c[1]⟩) := $(⟨c[3]⟩); $acc)
      else
        Macro.throwErrorAt c "expected `let x ← e`, `let x := e`, `let ys ← for x in xs do e`, or a final `return e`"
    `(LeanLinq.DbP.withBound $folded)

namespace QueryB
export Query (fetch fetchLimit forQuery fetchCount)
end QueryB

namespace ScalarB
export ScalarQuery (fetch)
end ScalarB

/-! ## Program-level specs

`Db` programs are trees and `runWith` is their model handler, so a
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
