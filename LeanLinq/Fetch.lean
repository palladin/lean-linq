import LeanLinq.Eval.Query
import LeanLinq.Theorems
import LeanLinq.Core.Grade

/-! # `DbFetch` — database programs with a round-trip budget in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `DbFetch` closes the *host-language* half: a program that
talks to the database carries its round-trip bound as a type index — a
closed numeral for batched programs, an exact data-dependent expression
for per-row loops, ⊤ for programs that decline to name a bound — and the
grading prices composition honestly —

- `fetch` costs `1`;
- `seq` (independent computations) costs `max m n`: a batching driver runs
  both sides in the same rounds;
- `bind` (a data dependency) costs `m + n`: you cannot know what to ask
  until the previous answer arrives.

The philosophy: **everything is representable; execution is gated by a
proof.** `exec` takes a budget and an obligation `r ≤ budget`, and each
shape has its proof story, up a ladder of evidence —

- batched programs: closed grades, `by decide`, silent;
- loops over data in hand (`let ys ← for x in xs do body`, i.e.
  `DbFetch.forAll`): the *exact* dynamic grade `k * xs.length`; `decide`
  once the list is literal, `omega` against a computed budget;
- loops over *just-fetched* rows: legal exactly when the fetch is
  bounded — `fetchLimit q n` returns a length-refined list
  (`{xs // xs.length ≤ n}`; `LIMIT` really limits:
  `Query.run_limit_length_le`), and `for p in parents.val do body` fuses
  into `DbFetchP.forRows`, whose budget proof *is* the refinement. Bound
  `m + k * n`, closed, silent. N+1, written deliberately, priced by the
  bounded query;
- loops priced by the query's own shape: `q.card` computes the row
  bound from the query value and `fetchBounded` surfaces it as the
  refinement, so the budget proof is the structure itself — soundness
  is a theorem (`Query.run_card_le`);
- loops over plain just-fetched rows, priced *symbolically*: no
  refinement, no restated bound — `let xs ← q.fetch` then
  `for p in xs do body` fuses into `forFetched`, whose evidence is
  `fetch`'s own contract (rows fit `q.gcard` at every σ). Grade
  `m + k * q.gcard`, in the database's own terms; the sized door
  (`execWithin`) collapses and checks it against live sizes;
- loops with no bound at all: the same door at the top of the lattice
  ℕ∞ (`Bound`). `fetchLimit q ⊤` emits no `LIMIT` and its refinement
  is vacuously true, so the same `forRows` fuses — and the grade
  absorbs to ⊤ (`b + ⊤ = ⊤`, likewise `max`/`*`): one unbounded part
  makes the whole program visibly unbounded. Every finite door refuses
  it statically (`exec` demands `r ≤ fin budget`); the explicit
  `execAll` runs it. (Haxl repairs N+1 dynamically by batching; the
  grading surfaces it statically. `fetchFor` remains the bound-1
  batched door for any collection size.)

Under the sugar sits the dependent bind, `DbFetchP.bindD`: a continuation
whose grade may mention the value, priced by a bound `B` plus evidence
`∀ σ a, P a σ → (g a).evalB σ ≤ B.evalB σ` — conditional on the
producer's *postcondition*, pointwise at every table-size valuation σ.
`fetch`'s contract (rows fit `q.card`, and `q.gcard` at every σ) is
such a postcondition, so the symbolic per-row loop `forQuery` is
*derived*: its evidence consumes the contract and transports it through
the `evalB` multiplication homomorphism. Refinements (`forRows`) and
user invariants (`bindD'`) are the same door with simpler evidence.

The reference interpreter here is the in-memory evaluator — the same
denotational semantics the test suite differential-tests — and the native
drivers interpret the same tree against live engines (`execIO`/`execMs`
sequentially; `execPg` through libpq pipeline mode, where `seq` sides and
`forAll` bodies — both independent — share rounds, so the loop *batches*
and the sequential grade is a generous bound). -/

/-! `fetch!` do-sugar (declared before the namespace: syntax categories
must live at top level for quotation patterns to work). -/
declare_syntax_cat fetchClause

namespace LeanLinq


/-- A σ-indexed postcondition: what is true of a computation's result at
the table sizes the run is performed under. Facts ride this index — the
values stay plain. -/
def Post (α : Type) := α → (String → Nat) → Prop

/-- A database program with result type `α`, at most `r` round trips
(`r : Grade` — possibly symbolic in table sizes), and postcondition `P`.

Six constructors, one bind: three leaves (`pure`, `fetch`, `fetchCell`),
two independence markers a batching driver exploits (`seq`, `forAll`),
and `bindD` — the only sequencing, whose evidence is *conditional on the
producer's postcondition, at σ*. Every loop is `bindD` plus a proof;
nothing else is primitive. -/
inductive DbFetchP (c : Ctx) : Grade → (α : Type) → Post α → Type 1 where
  | pure : {α : Type} → α → DbFetchP c 0 α (fun _ _ => True)
  -- the primitive fetch returns a PLAIN list; its facts are its
  -- CONTRACT: rows fit the closed card (σ-free), and the symbolic gcard
  -- at every σ the run answers to
  | fetch : {s : Schema} → (q : Query c s) →
      DbFetchP c 1 (List (Values s)) (fun xs σ =>
        Bound.fin xs.length ≤ q.card ∧
        Bound.fin xs.length ≤ (Query.gcard q).evalB σ)
  | fetchCell : {t : SqlPrim} → {n : Bool} → ScalarQuery c ⟨t, n⟩ →
      DbFetchP c 1 (Nullable t) (fun _ _ => True)
  -- independent computations: a batching driver shares their rounds
  | seq : {m n : Grade} → {α β : Type} → {P : Post (α → β)} → {P' : Post α} →
      DbFetchP c m (α → β) P → DbFetchP c n α P' →
      DbFetchP c (max m n) β (fun _ _ => True)
  -- the per-row loop over a collection in hand: exact grade. The body's
  -- postcondition may depend on the element (a per-key `fetch`'s contract
  -- mentions the per-key query) — the family `Q` absorbs that; the loop
  -- itself promises nothing
  | forAll : {α β : Type} → {k : Grade} → {Q : α → Post β} →
      (xs : List α) → ((a : α) → DbFetchP c k β (Q a)) →
      DbFetchP c (k * Grade.nat xs.length) (List β) (fun _ _ => True)
  -- THE bind: value-dependent grade, capped by `B`, justified by
  -- evidence that may assume the producer's postcondition — at σ
  | bindD : {m : Grade} → {α β : Type} → {P : Post α} → {Q : Post β} →
      {g : α → Grade} →
      DbFetchP c m α P → ((a : α) → DbFetchP c (g a) β Q) →
      (B : Grade) →
      (∀ σ a, P a σ → (g a).evalB σ ≤ B.evalB σ) →
      DbFetchP c (m + B) β Q

/-- The plain spelling: a program with the trivial postcondition — what
every composite program is, since results funnel through `pure`. -/
abbrev DbFetch (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbFetchP c r α (fun _ _ => True)

namespace DbFetch
export DbFetchP (pure fetch fetchCell seq forAll bindD)
end DbFetch

namespace DbFetchP

/-- Constant-grade sequencing — `bindD` with constant `g` and reflexive
evidence. -/
def bind {P : Post α} {Q : Post β} (x : DbFetchP c m α P)
    (k : α → DbFetchP c n β Q) : DbFetchP c (m + n) β Q :=
  .bindD x k n (fun _ _ _ => Bound.le_refl _)

def map {P : Post α} (f : α → β) (x : DbFetchP c r α P) : DbFetchP c r β (fun _ _ => True) :=
  Grade.add_zero r ▸ bind x (fun a => .pure (f a))

/-- Reference interpreter: the in-memory evaluator. Total — `DbFetch` is a
reflexive inductive, so structural recursion covers the `bind`
continuation applied to any value. -/
def runWith (ee : EvalEnv c) : {r : Grade} → {α : Type} → {P : Post α} →
    DbFetchP c r α P → Except EvalError α
  | _, _, _, .pure a => Except.ok a
  | _, _, _, .fetch q => q.evalRows ee
  | _, _, _, .fetchCell sq => sq.evalCell ee
  | _, _, _, .seq f x => do
      Except.ok ((← runWith ee f) (← runWith ee x))
  | _, _, _, .forAll xs f => xs.mapM fun a => runWith ee (f a)
  | _, _, _, .bindD x f _ _ => do runWith ee (f (← runWith ee x))

/-- The model handler, *instrumented*: same semantics as `runWith`, plus
the count of rounds actually performed (sequential model — `seq` sides
and `forAll` bodies each pay). This is what a symbolic price certifies
against: for a program of grade `r`, the pin is
`(runCount ee prog).2 ≤ (r.evalB ee.tables.sizes)` — the price
collapsed against the model's own sizes. -/
def runCount (ee : EvalEnv c) : {r : Grade} → {α : Type} → {P : Post α} →
    DbFetchP c r α P → Except EvalError (α × Nat)
  | _, _, _, .pure a => Except.ok (a, 0)
  | _, _, _, .fetch q => do Except.ok ((← q.evalRows ee), 1)
  | _, _, _, .fetchCell sq => do Except.ok ((← sq.evalCell ee), 1)
  | _, _, _, .seq f x => do
      let (g, m) ← runCount ee f
      let (a, n) ← runCount ee x
      Except.ok (g a, m + n)
  | _, _, _, .forAll xs f => do
      let rs ← xs.mapM fun a => runCount ee (f a)
      Except.ok (rs.map (·.1), (rs.map (·.2)).sum)
  | _, _, _, .bindD x f _ _ => do
      let (a, m) ← runCount ee x
      let (b, n) ← runCount ee (f a)
      Except.ok (b, m + n)

/-- The execution door: declare a round budget, prove you fit in it. For
closed grades (every batched program) the obligation discharges silently by
`decide`; a data-dependent grade (`xs.length` for runtime `xs`) is not
decidable at elaboration, so the caller supplies the proof — by bounding
the collection or computing the budget from it. A grade over data that
exists only inside the program (just-fetched rows) has no proof to
give: that is N+1, rejected. -/
def exec {P : Post α} (f : DbFetchP c r α P) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.ofBound_fin, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | assumption) : Except EvalError α :=
  runWith ⟨env, ps, now⟩ f

/-- The **sized** door: a symbolic grade collapses against the model's
own table sizes, and the budget check runs *there* — the door for
programs priced in the database's terms (`customers.size + 1`). The
check is at run time (the sizes are), but it is a check of the *price*,
before interpretation begins. -/
def execWithin {P : Post α} (f : DbFetchP c r α P) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  if r.evalB (TableEnv.sizes env) ≤ Bound.fin budget then
    runWith ⟨env, ps, now⟩ f
  else
    .error (.internal s!"round budget exceeded: the program's grade exceeds {budget} at this database's sizes")

/-- The unbounded door: no budget, obligation-free (`g ≤ ⊤` always). The
explicit opt-out for ⊤ programs — visible at the call site. -/
def execAll {P : Post α} (f : DbFetchP c r α P) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  runWith ⟨env, ps, now⟩ f

/-- Restate a bound as a provably equal one — `1 * ids.length` as
`ids.length`, and so on. The index a program *infers* is built
syntactically from the combinators; equalities like `Nat.one_mul` are
theorems, not reductions, so the elaborator will not rewrite them away.
This is the bridge, and `fetch!` applies it automatically: with no
constraint from the context, `rfl` pins the stated grade to the inferred
one; against an annotation, `omega` proves them equal. -/
def withBound {P : Post α} (x : DbFetchP c m α P) {n : Grade}
    (h : m = n := by first
      | rfl
      | decide
      | ((simp only [Grade.ofNat_eq_nat, Grade.ofBound_fin, Grade.nat_add,
            Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
            Grade.nat_zero_add, Grade.add_nat_zero,
            Grade.nat_add_ofBound]) <;>
         first
           | rfl
           | (apply congrArg Grade.nat; omega))) : DbFetchP c n α P :=
  h ▸ x

/-- `bindD` with its budget proof discharged automatically where possible:
`decide` for closed facts, `le_top` at ⊤, and the `fetchLimit` refinement
(`a.property`, bare or under the loop's `k *`) when the value is
length-refined. Anything else needs an explicit proof — that is the door
doing its job. -/
def bindD' {α β : Type} {P : Post α} {Q : Post β} {g : α → Grade}
    (x : DbFetchP c m α P)
    (f : (a : α) → DbFetchP c (g a) β Q) (B : Grade)
    (h : ∀ a, g a ≤ B := by
      intro a
      try simp only [_root_.LeanLinq.Grade.ofNat_eq_nat,
        _root_.LeanLinq.Grade.ofBound_fin, _root_.LeanLinq.Grade.nat_add,
        _root_.LeanLinq.Grade.nat_mul, _root_.LeanLinq.Grade.nat_one_mul,
        _root_.LeanLinq.Grade.mul_nat_one, Nat.one_mul, Nat.mul_one]
      first
        | exact _root_.LeanLinq.Grade.le_refl _
        | (apply _root_.LeanLinq.Grade.nat_le_nat; omega)
        | exact _root_.LeanLinq.Grade.le_top _
        | exact a.property
        | exact _root_.LeanLinq.Grade.nat_le_ofBound a.property
        | fail "cannot bound the dependent continuation — fetch the collection through fetchLimit, or supply the proof") :
    DbFetchP c (m + B) β Q :=
  .bindD x f B (fun σ a _ => h a σ)

/-- The post-fetch loop, fused: fetch a **length-refined** collection
(`fetchLimit`), then run `f` per row. The subtype carries the budget
proof — the loop costs at most `k * n` because the refinement says at
most `n` rows exist — so the grade `m + k * n` is closed whenever the
bounds are literals and nothing needs a tactic. This is the N+1 idiom
made legal: bounded query in, priced fan-out out. `fetch!` produces it
for `let x ← e` immediately followed by `for p in x.val do body`
(see `forRows` below). -/
def forRows {n : Bound} {P : Post {xs : List α // Bound.fin xs.length ≤ n}}
    {Q : α → Post β}
    (x : DbFetchP c m {xs : List α // Bound.fin xs.length ≤ n} P)
    (f : (a : α) → DbFetchP c k β (Q a)) :
    DbFetch c (m + k * Grade.ofBound n) (List β) :=
  .bindD x (fun a => .forAll a.val f) (k * Grade.ofBound n)
    (fun σ a _ => Grade.mul_le_mul_left k (Grade.nat_le_ofBound a.property) σ)

/-- The post-fetch loop over **plain** rows: the producer's
postcondition is `fetch`'s contract — the rows fit `q.gcard` at every
σ — and that *is* the budget evidence, transported through the
multiplication homomorphism. `q` is implicit, recovered from the
contract itself; the grade `m + k * q.gcard` prices the fan-out in the
database's own terms with no bound restated. `fetch!` produces it for
`let xs ← e` immediately followed by `for p in xs do body` (the plain
sibling of the `.val` fusion — see `forRows`). -/
def forFetched {q : Query c s} {Q : Values s → Post β}
    (x : DbFetchP c m (List (Values s)) (fun xs σ =>
      Bound.fin xs.length ≤ q.card ∧
      Bound.fin xs.length ≤ (Query.gcard q).evalB σ))
    (f : (v : Values s) → DbFetchP c k β (Q v)) :
    DbFetch c (m + k * Query.gcard q) (List β) :=
  .bindD x (fun xs => .forAll xs f) (k * Query.gcard q)
    (fun σ xs hP => by
      rw [Grade.evalB_mul, Grade.evalB_mul, Grade.evalB_nat]
      exact Bound.mul_le_mul_left _ hP.2)

/-- Fetch `q` and run `f` per row, the whole loop priced by the query's
own symbolic card: grade `1 + k * q.gcard` — the N+1 in the database's
own terms. **Derived, not primitive**: `forFetched` over the primitive
`fetch`. -/
def forQuery {Q : Values s → Post β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (Q v)) :
    DbFetch c (1 + k * Query.gcard q) (List β) :=
  forFetched (.fetch q) f

/-- Weakening: a program bounded by `m` is bounded by any `n ≥ m` —
derived, not primitive (`bindD` over `pure ()` with the constant
family). The door for value-dependent budgets: an inner loop whose
exact grade mentions a fetched value restates to the uniform bound the
enclosing combinator needs, paying with the inequality — which is
where a refinement gets cashed. -/
def weaken {P : Post α} (x : DbFetchP c m α P) (n : Grade)
    (h : m ≤ n := by
      try simp only [Grade.ofNat_eq_nat, Grade.ofBound_fin, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | exact Grade.le_top _
        | assumption) : DbFetchP c n α P :=
  withBound
    ((DbFetchP.pure ()).bindD (g := fun _ => m) (fun _ => x) n
      (fun σ _ _ => h σ))
    (Grade.zero_add n)

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
def DbFetchP.fetchLimit (q : Query c s) (n : Bound) :
    DbFetch c 1 {xs : List (Values s) // .fin xs.length ≤ n} :=
  match n with
  | .fin k =>
      DbFetchP.map (fun xs =>
        if h : xs.length ≤ k then ⟨xs, Bound.fin_le_fin h⟩
        else ⟨xs.take k, Bound.fin_le_fin (List.length_take_le k _)⟩)
        (DbFetchP.fetch (q.limit k))
  | .top => DbFetchP.map (fun xs => ⟨xs, rfl⟩) (DbFetchP.fetch q)

/-- Fetch **with the query's own cardinality bound** in the type: rows
refined by `.fin xs.length ≤ q.card`. For an unbounded query the
refinement is `≤ ⊤` — vacuously true, and the check below is
definitionally the identity; under a `limit` the bound is real and
`forRows` composes off it directly (the refinement's `n` is `q.card`,
whatever shape it takes). Like `fetchLimit`, the engine's answer is only
*checked*: rows pass through untouched, and the clamp arm exists solely
for an engine that disagrees with the query's own structure — the
soundness theorem (`card` never underestimates the reference semantics)
is what makes the check principled rather than defensive. -/
def DbFetchP.fetchBounded (q : Query c s) :
    DbFetch c 1 {xs : List (Values s) // .fin xs.length ≤ q.card} :=
  DbFetchP.map (fun xs =>
    match q.card with
    | .top => ⟨xs, Bound.le_top _⟩
    | .fin k =>
        if h : xs.length ≤ k then ⟨xs, Bound.fin_le_fin h⟩
        else ⟨xs.take k, Bound.fin_le_fin (List.length_take_le k _)⟩)
    (DbFetchP.fetch q)

/-! Pipeline-flowing spellings: a query ends in `|>.fetch` /
`|>.fetchLimit n` instead of being wrapped in a prefix call — same
constructors, dot-notation on the query. -/

/-- `q.fetch` — the query as a one-round program. The rows are a plain
list; the facts (rows fit `card`, and `gcard` at every σ) ride the
postcondition, where `bindD`'s evidence consumes them. -/
def Query.fetch (q : Query c s) :
    DbFetchP c 1 (List (Values s)) (fun xs σ =>
      Bound.fin xs.length ≤ q.card ∧
      Bound.fin xs.length ≤ (Query.gcard q).evalB σ) :=
  .fetch q

/-- `q.forQuery f` — the per-row loop priced by the query's own card. -/
def Query.forQuery {Q : Values s → Post β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (Q v)) :
    DbFetch c (1 + k * Query.gcard q) (List β) :=
  DbFetchP.forQuery q f

/-! `fetch!`'s loop target, overloaded by the iteree: a plain list loops
by `forAll` (grade `k * |xs|`), a query by `forQuery` (grade
`1 + k * q.gcard` — the symbolic price). Two exports of one name; the
elaborator keeps the alternative that typechecks. -/

def LoopList.forLoop {Q : α → Post β} (xs : List α)
    (f : (a : α) → DbFetchP c k β (Q a)) :
    DbFetch c (k * Grade.nat xs.length) (List β) :=
  .forAll xs f

def LoopQuery.forLoop {Q : Values s → Post β} (q : Query c s)
    (f : (v : Values s) → DbFetchP c k β (Q v)) :
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
def Query.fetchLimit (q : Query c s) (n : Bound) :
    DbFetch c 1 {xs : List (Values s) // .fin xs.length ≤ n} :=
  DbFetchP.fetchLimit q n

/-- `q.fetchBounded` — the fetch refined by the query's own `card`,
flowing: `Query.from' … |>.limit 5 |>.fetchBounded`. -/
def Query.fetchBounded (q : Query c s) :
    DbFetch c 1 {xs : List (Values s) // .fin xs.length ≤ q.card} :=
  DbFetchP.fetchBounded q

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
export Query (fetch fetchLimit fetchBounded forQuery)
end QueryB

namespace ScalarB
export ScalarQuery (fetch)
end ScalarB

/-! ## Program-level specs

`DbFetch` programs are trees and `runWith` is their model handler, so a
spec proved against it — quantified over **every** environment — is a
fact about the *program*, established once; the same tree then meets a
live engine at an IO door. -/

/-- A limited query's card sits under its limit — whatever else the
query is. -/
theorem card_limit_le {ts : Ctx} {s : Schema} (q : Query ts s) (n : Nat) :
    (q.limit n).card ≤ Bound.fin n := by
  show (QueryP.limit (q AliasOf) n).card ≤ _
  unfold QueryP.limit
  split
  · exact Bound.min_le_right ..
  · unfold QueryP.limitOffset
    split
    · exact Bound.min_le_right ..
    · exact Bound.min_le_right ..

/-- The spec of the *program*, fully abstract: any query, any limit —
and no run-hypothesis at all anymore: the refined `fetch` carries in its
*type* what this used to prove about the semantics. The page fits by
projection. -/
theorem fetchPage_fits {ts : Ctx} {s : Schema} (q : Query ts s) (n : Nat)
    (xs : {xs : List (Values s) // Bound.fin xs.length ≤ (q.limit n).card}) :
    xs.val.length ≤ n :=
  of_decide_eq_true (Bound.le_trans xs.property (card_limit_le q n))

end LeanLinq
