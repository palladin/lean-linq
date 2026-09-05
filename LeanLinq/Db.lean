import LeanLinq.Eval.Query
import LeanLinq.Eval.Statements
import LeanLinq.Theorems
import LeanLinq.Core.Grade
import LeanLinq.Freer

/-! # `Db` — database programs with the round-trip bill in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `Db` closes the *host-language* half: a program that
talks to the database carries its round-trip bill as part of its
specification — a closed numeral for batched programs, an exact
data-dependent expression for per-row loops, a symbolic function of
table sizes for loops priced by the database itself.

The generic graded Freer Dijkstra monad (`LeanLinq.Freer`) is unchanged:
`pure`, `bindE`, and `weaken` are its three constructors. The seven ordinary
database operations live in `DbOp`; each has one specification (`dbOpWp`)
for its logical contract and cost of one. `DbOp.raise` is a general user-error
effect with cost zero. The outer signature `DbE` adds a
transaction operation whose body uses only `DbOp`, so nesting is rejected
by its type. A transaction carries its body's specification and bill.
The database interpreters count ordinary body operations; transaction
control commands are outside that count. The plain surface is the **bill**:
`Db c r α` means "costs at most `r`", proved at each weakening —

- ops cost `1` (`dbOpWp_bill`, behind `HasBill` inference);
- `bind` (a data dependency) costs `m + n`: you cannot know what to ask
  until the previous answer arrives. (Independence — two fetches sharing
  a round — is applicative structure, not monadic; it returns with a
  free-applicative layer over this monad.)

Execution is gated by a proof: `exec` takes a budget and an obligation
`r ≤ budget`, and each
shape has its proof story, up a ladder of evidence —

- batched programs: closed grades, discharged silently;
- loops over data in hand (`let ys ← for x in xs do body`, the derived
  `forAll` bind-chain): the *exact* dynamic grade `k * xs.length`;
- loops over just-fetched rows, bounded deliberately: `fetchLimit q n`
  returns a length-refined list (`{xs // xs.length ≤ n}`; `LIMIT`
  really limits: `Query.run_limit_length_le`), and
  `for p in parents.val do body` fuses into `DbP.forRows`, whose
  budget proof *is* the refinement. Bill `m + k * n`, closed, silent;
- loops over plain just-fetched rows, priced *symbolically*: no
  refinement, no restated bound — `let xs ← q.execQuery` then
  `for p in xs do body` fuses into `forFetched`, whose proof consumes
  `fetch`'s own contract (rows fit `q.gcard` at σ — and the graded wp
  threads σ, so the price is taken exactly where it was measured).
  Bill `1 + k * q.gcard`, in the database's own terms; `exec` refuses
  it statically, the sized door (`execWithin`) collapses and checks it
  against live sizes, and `execAll` runs unchecked. (`fetchFor`
  remains the bound-1 batched door for any collection size.)

Sequencing bills is `Wp.bill_bind_of_le`: sound when the second bill is
σ-stable — every closed grade — because the first stage's writes cannot
then raise it; symbolic prices compose at the strong specs, where the
wp itself shows what moved. This is the honest form of the old
formal-index composition, and the cost the wp threads makes the bill a
*theorem*: `runWithP` returns the run's op count together with the
`Wp.sp` fact, and `runWithP_count_le` pins count ≤ bill.

The reference interpreter here is the in-memory evaluator — the same
denotational semantics the test suite differential-tests — and the native
drivers interpret ordinary operations against live engines through the
generic fold and bracket transaction bodies on the same connection. `runWithP` is the adequacy
door: the run satisfies its spec, `Wp.sp`-formed about the actual
result, final sizes, and cost. -/

/-! `db!` do-sugar (declared before the namespace: syntax categories
must live at top level for quotation patterns to work). -/
declare_syntax_cat fetchClause

namespace LeanLinq

/-! ## The effect signature -/

/-- Seven query/write operations, plus a user error that issues no statement.
The signature is *data* — `dbOpWp` gives each op its graded spec, the
model gives each op a certified handler, and the drivers give each op
an IO handler. -/
inductive DbOp (c : Ctx) : Type → Type 1 where
  | fetch : {s : Schema} → (q : Query c s) → DbOp c (List (Values s))
  | fetchCell : {t : SqlPrim} → {n : Bool} → (sc : ScalarQuery c ⟨t, n⟩) →
      DbOp c (Nullable t)
  | insert : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      InsertStmt c n s → DbOp c Nat
  | update : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      UpdateStmt c n s → DbOp c Nat
  | delete : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      DeleteStmt c n s → DbOp c Nat
  | insertSelect : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      (st : InsertSelectStmt c n s) → DbOp c Nat
  | insertValues : {n : String} → {s : Schema} → [inst : HasTable c.tables n s] →
      (st : InsertValuesStmt c n s) → DbOp c Nat
  | raise : (message : String) → DbOp c Unit

/-- Queries and writes cost one operation; a user error performs no database
operation. This count is used by the failure-aware database model. -/
abbrev DbOp.cost {α : Type} : DbOp c α → Nat
  | .raise _ => 0
  | _ => 1

/-- The whole meaning of each op: its strongest σ-expressible contract
**and its price**, in one graded spec: queries/writes cost one, raises zero.
`raise` conservatively has the success spec `Wp.pure ()`; it does not erase
preceding costs by making the postcondition vacuous.

- `fetch` is the DEMONIC form of the contract — "whatever rows arrive,
  they fit the query's own symbolic card at σ". Demonic is forced:
  sizes don't determine contents, so no sound σ-spec can name the
  particular rows; the particular reading returns at the door via
  `Wp.sp`.
- `fetchCell` promises what its shape supports: a COUNT's value fits the
  spine's symbolic bound; content aggregates promise nothing.
- the writes carry the strongest σ-transformer their observability
  supports — INSERT moves this table's size within `[σ n, σ n + 1]`
  and touches nothing else; UPDATE preserves sizes exactly; DELETE
  shrinks demonically; INSERT … SELECT grows by exactly the appended
  rows, count within the source's card; batched VALUES grows by at most
  the batch, count exactly its length. Backed by the
  `HasTable.sizes_set_*` laws at the adequacy door. -/
def dbOpWp {α : Type} : DbOp c α → Wp α
  | .raise _ => Wp.pure ()
  | .fetch q => fun post σ k =>
      ∀ xs, xs.length ≤ (Query.gcard q).eval σ → post xs σ (k + 1)
  | .fetchCell sc => fun post σ k =>
      ∀ v, ScalarQueryP.cellBound (sc AliasOf) v σ → post v σ (k + 1)
  | .insert (n := n) (inst := _) _ => fun post σ k =>
      ∀ σ', (∀ m, m ≠ n → σ' m = σ m) → σ n ≤ σ' n → σ' n ≤ σ n + 1 →
        post 1 σ' (k + 1)
  | .update (n := n) (inst := _) _ => fun post σ k =>
      ∀ j, j ≤ σ n → post j σ (k + 1)
  | .delete (n := n) (inst := _) _ => fun post σ k =>
      ∀ σ' j, (∀ m, m ≠ n → σ' m = σ m) → σ' n ≤ σ n → σ n ≤ σ' n + j →
        post j σ' (k + 1)
  | .insertSelect (n := n) (inst := _) st => fun post σ k =>
      ∀ σ' j, (∀ m, m ≠ n → σ' m = σ m) → σ n ≤ σ' n → σ' n ≤ σ n + j →
        j ≤ (Query.gcard st.source).eval σ → post j σ' (k + 1)
  | .insertValues (n := n) (inst := _) st => fun post σ k =>
      ∀ σ', (∀ m, m ≠ n → σ' m = σ m) → σ n ≤ σ' n →
        σ' n ≤ σ n + st.rows.length → post st.rows.length σ' (k + 1)

/-- A transaction body contains only base operations. The outer signature
adds a scoped operation without changing the generic free monad. -/
inductive DbE (c : Ctx) : Type → Type 1 where
  | op : DbOp c α → DbE c α
  | transaction : {α : Type} → {w : Wp α} →
      FreerD (DbOp c) dbOpWp α w → DbE c α

/-- A scoped operation has its body's complete success specification and bill;
it is not charged as a single database operation. -/
def dbWp {α : Type} : DbE c α → Wp α
  | .op e => dbOpWp e
  | .transaction (w := w) _ => w

inductive ScopeMode where
  | outside
  | inside
  deriving DecidableEq, Repr

abbrev TxMode := ScopeMode
namespace TxMode
export ScopeMode (outside inside)
end TxMode

/-- The inside signature has no transaction operation. -/
def DbEffect : ScopeMode → Ctx → Type → Type 1
  | .outside, c => DbE c
  | .inside, c => DbOp c

def dbWpFor : (mode : ScopeMode) → (c : Ctx) → EffWp (DbEffect mode c)
  | .outside, _ => dbWp
  | .inside, _ => dbOpWp

/-- A database program indexed by scope mode and graded specification. Ordinary
operations preserve the mode; only `DbP.transaction` enters a managed scope. -/
abbrev DbPM (mode : ScopeMode) (c : Ctx) (α : Type) (w : Wp α) : Type 1 :=
  FreerD (DbEffect mode c) (dbWpFor mode c) α w

/-- A mode-indexed program specified by its database-operation bill. Transaction
control commands are outside this count. -/
abbrev DbM (mode : ScopeMode) (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbPM mode c α (Wp.bill r)

/-- Programs executed outside a transaction body; existing API spelling. -/
abbrev DbP (c : Ctx) (α : Type) (w : Wp α) : Type 1 :=
  DbPM .outside c α w

abbrev Db (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbM .outside c r α

/-- A transaction body cannot contain another transaction, including through
helpers or the raw transaction effect constructor. -/
abbrev TxDbP (c : Ctx) (α : Type) (w : Wp α) : Type 1 :=
  DbPM .inside c α w

abbrev TxDb (c : Ctx) (r : Grade) (α : Type) : Type 1 :=
  DbM .inside c r α

/-- Every op fits `bill 1` — the op-level bill, once for the whole
signature. -/
theorem dbOpWp_bill {α : Type} (e : DbOp c α) : (dbOpWp e).le (Wp.bill 1) := by
  have hc : ∀ (k : Nat) (σ : String → Nat), k + 1 ≤ k + (1 : Grade).eval σ := by
    intro k σ; simp
  cases e with
  | raise _ => exact Wp.bill_pure () 1
  | fetch q =>
      intro post σ k hb xs _
      exact hb xs σ (k + 1) (hc k σ)
  | fetchCell sc =>
      intro post σ k hb v _
      exact hb v σ (k + 1) (hc k σ)
  | insert i =>
      intro post σ k hb σ' _ _ _
      exact hb 1 σ' (k + 1) (hc k σ)
  | update u =>
      intro post σ k hb j _
      exact hb j σ (k + 1) (hc k σ)
  | delete d =>
      intro post σ k hb σ' j _ _ _
      exact hb j σ' (k + 1) (hc k σ)
  | insertSelect st =>
      intro post σ k hb σ' j _ _ _ _
      exact hb j σ' (k + 1) (hc k σ)
  | insertValues st =>
      intro post σ k hb σ' _ _ _
      exact hb _ σ' (k + 1) (hc k σ)

/-- Known raw raises infer zero, while queries and writes still infer one. -/
theorem dbOpWp_cost {α : Type} (e : DbOp c α) :
    (dbOpWp e).le (Wp.bill (Grade.nat e.cost)) := by
  cases e <;> first
    | exact dbOpWp_bill _
    | exact Wp.bill_pure () 0

instance {α : Type} (e : DbOp c α) : HasBill (dbOpWp e) 1 :=
  ⟨dbOpWp_bill e⟩

/-- A known raise uses the exact zero bill before the general one-operation
upper bound. Ordinary operations retain literal bills in dependent loops. -/
instance (priority := 1100) (message : String) :
    HasBill (dbOpWp (DbOp.raise (c := c) message)) 0 :=
  ⟨Wp.bill_pure () 0⟩

instance {α β : Type} (e : α → DbOp c β) :
    HasBillF (fun a => dbOpWp (e a)) 1 := ⟨fun a => dbOpWp_bill (e a)⟩

instance (priority := 1100) {α : Type} (message : α → String) :
    HasBillF (fun a => dbOpWp (DbOp.raise (c := c) (message a))) 0 :=
  ⟨fun _ => Wp.bill_pure () 0⟩

instance {α : Type} {r : Grade} (op : DbOp c α) [h : HasBill (dbOpWp op) r] :
    HasBill (dbWp (.op op)) r := ⟨h.le⟩

/-- A transaction can be billed only from its body's bill. -/
instance {α : Type} {w : Wp α} {r : Grade}
    (body : FreerD (DbOp c) dbOpWp α w) [h : HasBill w r] :
    HasBill (dbWp (.transaction body)) r := ⟨h.le⟩

/-! ## Grade normalization — pricing `Query.gcard someDef` at the doors

The door tactics decompose grade expressions with `eval_add`/`eval_mul`/
`eval_min` and finish with `omega` — but a grade like
`Query.gcard adults` hides its algebra behind the user's `def`, which
`simp` cannot unfold without knowing the name. Definitional unfolding
can: this simproc rewrites `Grade.eval σ g` to the *applied* form `g σ`
normalized just far enough that every head is a `Nat` operation `omega`
understands (`+`, `*`, `min`, `max` kept opaque; everything else — user
defs, `gcard`'s recursion, the pointwise constructors — unfolded by
defeq). The rewrite carries no proof: every step is `rfl`. -/

open Lean Meta in
private partial def gradeNatNorm (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  let f := e.getAppFn
  let some n := f.constName? | return e
  let args := e.getAppArgs
  -- a *Nat-level* binary operation (exact arity — an over-applied `*` is a
  -- Grade-level product applied to σ, which must keep unfolding instead)
  let isNatOp :=
    ((n == ``Nat.add || n == ``Nat.mul) && args.size == 2) ||
    ((n == ``HAdd.hAdd || n == ``HMul.hMul) && args.size == 6) ||
    ((n == ``Min.min || n == ``Max.max) && args.size == 4)
  if isNatOp then
    let i := args.size - 2
    let j := args.size - 1
    let a ← gradeNatNorm args[i]!
    let b ← gradeNatNorm args[j]!
    return mkAppN f ((args.set! i a).set! j b)
  else
    match ← unfoldDefinition? e with
    | some e' => gradeNatNorm e'
    | none =>
        let e' ← whnf e
        if e' == e then return e else gradeNatNorm e'

open Lean Meta Simp in
simproc gradeEvalNorm (Grade.eval _ _) := fun e => do
  let_expr Grade.eval σ g := e | return .continue
  -- simp runs procs at reducible transparency; the whole point here is
  -- to unfold user `def`s, so switch to default for the normalization
  let e' ← withTransparency .default <| gradeNatNorm (mkApp g σ)
  if e' == e then return .continue
  return .visit { expr := e' }

theorem Grade.stable_add {a b : Grade} (ha : Grade.Stable a)
    (hb : Grade.Stable b) : Grade.Stable (a + b) := by
  intro σ σ'
  rw [Grade.eval_add, Grade.eval_add]
  exact Nat.add_le_add (ha σ σ') (hb σ σ')

macro_rules
  | `(tactic| grade_stable) =>
      `(tactic| first
        | assumption
        | exact LeanLinq.Grade.stable_nat _
        | ((apply LeanLinq.Grade.stable_mul_nat) <;> grade_stable)
        | ((apply LeanLinq.Grade.stable_add) <;> grade_stable))

namespace DbP

/-- Run a body in a managed transaction. Its bill and success specification are
unchanged. The scope handler commits before this program returns its result;
failure rollback is specified separately by `DbP.transaction_failure`. -/
def transaction {α : Type} {w : Wp α} (body : TxDbP c α w) : DbP c α w :=
  FreerD.liftE (DbE.transaction body)

/-- Lift one ordinary operation into either signature, preserving its spec. -/
def liftOp {mode : ScopeMode} {α : Type} (op : DbOp c α) :
    DbPM mode c α (dbOpWp op) :=
  match mode with
  | .outside => FreerD.liftE (DbE.op op)
  | .inside => FreerD.liftE op

/-- Raise a user error in either mode without issuing a query or write.
The conservative Unit success spec preserves the cost of preceding operations;
inside a transaction, normal error handling rolls back the body. -/
def raise {mode : ScopeMode} (message : String) : DbPM mode c Unit (Wp.pure ()) :=
  liftOp (DbOp.raise message)

/-! ## The query/write doors — one database operation each -/

def pure {mode : ScopeMode} {α : Type} (a : α) : DbPM mode c α (Wp.pure a) := FreerD.pure a

def fetch {mode : ScopeMode} {s : Schema} (q : Query c s) :
    DbPM mode c (List (Values s)) (dbOpWp (DbOp.fetch q)) :=
  liftOp (DbOp.fetch q)

def fetchCell {mode : ScopeMode} {t : SqlPrim} {n : Bool} (sc : ScalarQuery c ⟨t, n⟩) :
    DbPM mode c (Nullable t) (dbOpWp (DbOp.fetchCell sc)) :=
  liftOp (DbOp.fetchCell sc)

def insert {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (i : InsertStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.insert i)) :=
  liftOp (DbOp.insert i)

def update {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (u : UpdateStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.update u)) :=
  liftOp (DbOp.update u)

def delete {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (d : DeleteStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.delete d)) :=
  liftOp (DbOp.delete d)

def insertSelect {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (st : InsertSelectStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.insertSelect st)) :=
  liftOp (DbOp.insertSelect st)

def insertValues {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (st : InsertValuesStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.insertValues st)) :=
  liftOp (DbOp.insertValues st)

/-- Reconciliation: `sp` of the fetch spec **is** the contract — the
demonic ∀ in the spec, the pointwise fact at the door — at cost one
effect call. -/
theorem sp_fetch {s : Schema} (q : Query c s) (xs : List (Values s))
    (σ : String → Nat) (k : Nat) :
    Wp.sp (dbOpWp (DbOp.fetch q)) xs σ k σ (k + 1) ↔
      xs.length ≤ (Query.gcard q).eval σ := by
  constructor
  · intro h
    exact h (fun ys _ _ => ys.length ≤ (Query.gcard q).eval σ)
      (fun _ hb => hb)
  · intro hb post hw
    exact hw xs hb

/-! ## The billed surface -/

/-- Relax any spec to its bill — the weakening that *proves* the bill,
with the bill itself recovered by `HasBill` inference (ops fit `1`,
bills fit themselves, `pure` fits `0`). -/
def relax {mode : ScopeMode} {α : Type} {w : Wp α} (x : DbPM mode c α w) {r : Grade}
    [h : HasBill w r] : DbM mode c r α :=
  FreerD.weaken h.le x

/-- Constant-bill sequencing on the plain surface: the derived monad
bind (`bindS`, index composed by `Wp.bind` definitionally), weakened to
`bill (m + n)` by the sequencing law. The side conditions — both bills
max-plus-nonempty, the second σ-stable — discharge silently for every
closed grade. -/
def bind {mode : ScopeMode} {α β : Type} {w : Wp α} {w₂ : α → Wp β} (x : DbPM mode c α w)
    (k : (a : α) → DbPM mode c β (w₂ a)) {m n : Grade}
    [hm : HasBill w m] [hn : HasBillF w₂ n]
    (hns : Grade.Stable n := by grade_stable) : DbM mode c (m + n) β :=
  FreerD.weaken (Wp.bill_bind_of_le hm.le hn.le hns)
    (FreerD.bindS x k)

/-- Mapping is free: the bill does not move. -/
def map {mode : ScopeMode} {α β : Type} {w : Wp α} (f : α → β) (x : DbPM mode c α w) {r : Grade}
    [hr : HasBill w r] : DbM mode c r β :=
  FreerD.weaken (Wp.bill_map_of_le f hr.le) (FreerD.mapS f x)

/-- Restate a bill as a provably equal one — `1 * ids.length` as
`ids.length`, and so on. The bill a program *infers* is built
syntactically from the combinators; equalities like `Nat.one_mul` are
theorems, not reductions, so the elaborator will not rewrite them away.
This is the bridge, and `db!` applies it automatically. -/
def withBound {mode : ScopeMode} {α : Type} {w : Wp α} (x : DbPM mode c α w) {m : Grade}
    [HasBill w m] {n : Grade}
    (h : m = n := by first
      | rfl
      | (refine Grade.ext fun σ => ?_
         simp only [gradeEvalNorm, Grade.ofNat_eq_nat, Grade.eval_add,
           Grade.eval_mul, Grade.eval_min, Grade.eval_nat, Grade.eval_tbl,
           Table.size]
         omega)) : DbM mode c n α :=
  h ▸ relax x

/-- State the bill as any provably **dominating** one — `db!`'s wrapper:
a type ascription is an upper bound (which is what a bill means), so
`DbM mode c 4 α` accepts a program whose raw bill is `1 + 1 * min (|C|, 3)`.
Same pointwise auto-discharge as the doors; a symbolic bill against a
closed ascription still has no proof — the static refusal. -/
def withBill {mode : ScopeMode} {α : Type} {w : Wp α} (x : DbPM mode c α w) {m : Grade}
    [HasBill w m] {n : Grade}
    (h : m ≤ n := by first
      | exact Grade.le_refl _
      | (intro σ
         simp only [gradeEvalNorm, Grade.ofNat_eq_nat, Grade.eval_add,
           Grade.eval_mul, Grade.eval_min, Grade.eval_nat, Grade.eval_tbl,
           Table.size]
         omega)) : DbM mode c n α :=
  FreerD.weaken (Wp.bill_mono h) (FreerD.weaken (HasBill.le) x)

/-- Bill weakening: a program billed at `m` is billed at any `n ≥ m` —
`Wp.bill_mono` behind the same auto-discharge as the doors. -/
def weaken {mode : ScopeMode} {α : Type} (x : DbM mode c m α) (n : Grade)
    (h : m ≤ n := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | (intro σ
           simp only [gradeEvalNorm, Grade.ofNat_eq_nat, Grade.eval_add,
             Grade.eval_mul, Grade.eval_min, Grade.eval_nat, Grade.eval_tbl,
             Table.size]
           omega)
        | assumption) : DbM mode c n α :=
  FreerD.weaken (Wp.bill_mono h) x

/-- Dependent-bill sequencing with its budget proof discharged
automatically where possible: closed facts silently, and the
`fetchLimit` refinement (`a.property`, bare or under the loop's `k *`)
when the value is length-refined. Anything else needs an explicit
proof — that is the door doing its job. -/
def bindD' {α β : Type} {w : Wp α} {g : α → Grade}
    (x : DbPM mode c α w)
    (f : (a : α) → DbM mode c (g a) β) (B : Grade)
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
        | (intro σ
           simp only [_root_.LeanLinq.gradeEvalNorm,
             _root_.LeanLinq.Grade.ofNat_eq_nat,
             _root_.LeanLinq.Grade.eval_add, _root_.LeanLinq.Grade.eval_mul,
             _root_.LeanLinq.Grade.eval_min, _root_.LeanLinq.Grade.eval_nat,
             _root_.LeanLinq.Grade.eval_tbl]
           omega)
        | fail "cannot bound the dependent continuation — fetch the collection through fetchLimit, or supply the proof")
    {m : Grade} [hm : HasBill w m]
    (hBs : Grade.Stable B := by grade_stable) :
    DbM mode c (m + B) β :=
  FreerD.weaken
    (Wp.bill_bindD_of_le hm.le (fun _ => Wp.le_refl _) h hBs)
    (FreerD.bindS x f)

/-! ## The derived loop — a bind-chain, mapM-shaped

The loop is not a constructor: it is the fold of its bodies through
`bindS`, each step weakened by `Wp.bill_loop_step` — pure Nat
arithmetic once `eval_mul` splits the product. σ-stability of the body
bill is the soundness condition (writing bodies are fine: a closed body
price cannot be raised by the rows already written). -/

/-- The per-row loop over a collection in hand — derived, exact bill
`k * xs.length`. Bodies at any spec flow in through their bills: a
bare op body is welcome. -/
def forAll {mode : ScopeMode} {α β : Type} {w₂ : α → Wp β} {kg : Grade}
    [hk : HasBillF w₂ kg]
    (xs : List α) (f : (a : α) → DbPM mode c β (w₂ a))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (kg * Grade.nat xs.length) (List β) :=
  match xs with
  | [] => FreerD.weaken (Wp.bill_pure [] _) (FreerD.pure [])
  | a :: as =>
      FreerD.weaken
        (Wp.bill_loop_step hst as.length (hk.le a) (fun _ => Wp.le_refl _))
        (FreerD.bindS (f a)
          (fun b => DbP.map (b :: ·) (forAll as f hst)))

/-- The post-fetch loop, fused: fetch a **length-refined** collection
(`fetchLimit`), then run `f` per row. The subtype carries the budget
proof — the bill `m + k * n` is closed whenever the bounds are
literals. `db!` produces it for `let x ← e` immediately followed by
`for p in x.val do body`. -/
def forRows {mode : ScopeMode} {α β : Type} {n : Nat} {w : Wp {xs : List α // xs.length ≤ n}}
    {w₂ : α → Wp β}
    (x : DbPM mode c {xs : List α // xs.length ≤ n} w)
    (f : (a : α) → DbPM mode c β (w₂ a))
    {m kg : Grade} [hm : HasBill w m] [hk : HasBillF w₂ kg]
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (m + kg * Grade.nat n) (List β) :=
  FreerD.weaken
    (Wp.bill_bindD_of_le hm.le (fun _ => Wp.le_refl _)
      (fun a => Grade.mul_le_mul_left kg (Grade.nat_le_nat a.property))
      (Grade.stable_mul_nat hst n))
    (FreerD.bindS x (fun a => DbP.forAll a.val f hst))

/-- The post-fetch loop over **plain** rows: the producer is the fetch
op itself, and its contract — rows fit `q.gcard` at σ, with σ threaded
unchanged — pays the loop's symbolic budget. `q` is implicit, recovered
from the spec. `db!` produces it for `let xs ← e` immediately followed
by `for p in xs do body`. -/
def forFetched {mode : ScopeMode} {s : Schema} {β : Type} {q : Query c s}
    {w₂ : Values s → Wp β} {kg : Grade} [hk : HasBillF w₂ kg]
    (x : DbPM mode c (List (Values s)) (dbOpWp (DbOp.fetch q)))
    (f : (v : Values s) → DbPM mode c β (w₂ v))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (1 + kg * Query.gcard q) (List β) :=
  FreerD.weaken
    (by
      intro post σ k hb xs hlen b σ' k₂ hk₂
      refine hb b σ' k₂ ?_
      rw [Grade.eval_mul, Grade.eval_nat] at hk₂
      have hmul : kg.eval σ * xs.length ≤
          kg.eval σ * (Query.gcard q).eval σ :=
        Nat.mul_le_mul_left _ hlen
      have hadd := Grade.le_eval_add (a := (1 : Grade))
        (b := kg * Query.gcard q) σ
      rw [Grade.eval_mul] at hadd
      simp only [Grade.ofNat_eq_nat, Grade.eval_nat] at hadd ⊢
      omega)
    (FreerD.bindS x (fun xs => DbP.forAll xs f hst))

/-- Fetch `q` and run `f` per row, the whole loop priced by the query's
own symbolic card: bill `1 + k * q.gcard` — the N+1 in the database's
own terms. **Derived, not primitive**: `forFetched` over the fetch op. -/
def forQuery {mode : ScopeMode} {s : Schema} {β : Type} {w₂ : Values s → Wp β}
    {kg : Grade} [HasBillF w₂ kg] (q : Query c s)
    (f : (v : Values s) → DbPM mode c β (w₂ v))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (1 + kg * Query.gcard q) (List β) :=
  forFetched (DbP.fetch q) f hst

end DbP

/-- The batched door: fetch for a whole runtime key set in **one** round —
the keys become an `IN (…)` list inside a single statement, so a thousand
parents still cost bill 1. This is how N+1 collapses to 1+1. -/
def DbP.fetchFor {mode : ScopeMode} [SqlLit t] (keys : List t.interp)
    (mk : (∀ {ρ}, List (SqlExprP ρ c ⟨t, true⟩)) → Query c s) :
    DbM mode c 1 (List (Values s)) :=
  DbP.map id (DbP.fetch (mk fun {ρ} => keys.map fun k => .widen (SqlLit.lit k)))

/-- Fetch at most `n` rows, **with the bound in the type**: applies
`LIMIT n` to the query and returns a length-refined list — the evidence
a dependent composition (`bindD'`/`forRows`) needs, produced by the query
itself. The `LIMIT` is the engine's; the client only *checks* the
length to realize the proof — the rows pass through untouched
(provably so in the reference semantics: `Query.run_limit_length_le`),
and the `take` clamp fires only against a disagreeing engine. -/
def DbP.fetchLimit {mode : ScopeMode} (q : Query c s) (n : Nat) :
    DbM mode c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbP.map (fun xs =>
    if h : xs.length ≤ n then ⟨xs, h⟩
    else ⟨xs.take n, List.length_take_le n _⟩)
    (DbP.fetch (q.limit n))

/-! Pipeline-flowing spellings: a query ends in `|>.execQuery` /
`|>.fetchLimit n` instead of being wrapped in a prefix call — same
doors, dot-notation on the query. -/

/-- `q.execQuery` — the query as a one-call program at the fetch op's
own spec (the demonic contract, σ threaded, cost `k + 1`). -/
def Query.execQuery {mode : ScopeMode} (q : Query c s) :
    DbPM mode c (List (Values s)) (dbOpWp (DbOp.fetch q)) :=
  DbP.fetch q

/-- `i.execInsert` — the statement as a one-operation program, flowing:
`customers.insert |>.value … |>.execInsert`. Affected count = 1, sizes
move within the insert's interval spec. -/
def InsertStmt.execInsert {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (i : InsertStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.insert i)) :=
  DbP.insert i

/-- `u.execUpdate` — affected count is the WHERE's hits, sizes exact. -/
def UpdateStmt.execUpdate {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (u : UpdateStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.update u)) :=
  DbP.update u

/-- `st.execInsertSelect` — the batched write, flowing:
`customers.insertFrom q |>.execInsertSelect` — one operation, priced
and bounded by the source query's own card. -/
def InsertSelectStmt.execInsertSelect {mode : ScopeMode} {n : String} {s : Schema}
    [HasTable c.tables n s] (st : InsertSelectStmt c n s) :
    DbPM mode c Nat (dbOpWp (DbOp.insertSelect st)) :=
  DbP.insertSelect st

/-- `st.execInsertValues` — the batched in-hand write, flowing:
`customers.insertAll rows |>.execInsertValues` — one operation, count =
the list's length. -/
def InsertValuesStmt.execInsertValues {mode : ScopeMode} {n : String} {s : Schema}
    [HasTable c.tables n s] (st : InsertValuesStmt c n s) :
    DbPM mode c Nat (dbOpWp (DbOp.insertValues st)) :=
  DbP.insertValues st

/-- `d.execDelete` — the count ties the shrink down. -/
def DeleteStmt.execDelete {mode : ScopeMode} {n : String} {s : Schema} [HasTable c.tables n s]
    (d : DeleteStmt c n s) : DbPM mode c Nat (dbOpWp (DbOp.delete d)) :=
  DbP.delete d

/-- `q.forQuery f` — the per-row loop priced by the query's own card. -/
def Query.forQuery {mode : ScopeMode} {s : Schema} {β : Type} {w₂ : Values s → Wp β}
    {kg : Grade} [HasBillF w₂ kg] (q : Query c s)
    (f : (v : Values s) → DbPM mode c β (w₂ v))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (1 + kg * Query.gcard q) (List β) :=
  DbP.forQuery q f hst

/-! `db!`'s loop target, overloaded by the iteree: a plain list loops
by `forAll` (bill `k * |xs|`), a query by `forQuery` (bill
`1 + k * q.gcard` — the symbolic price). Two exports of one name; the
elaborator keeps the alternative that typechecks. -/

def LoopList.forLoop {mode : ScopeMode} {α β : Type} {w₂ : α → Wp β} {kg : Grade}
    [HasBillF w₂ kg] (xs : List α) (f : (a : α) → DbPM mode c β (w₂ a))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (kg * Grade.nat xs.length) (List β) :=
  DbP.forAll xs f hst

def LoopQuery.forLoop {mode : ScopeMode} {s : Schema} {β : Type} {w₂ : Values s → Wp β}
    {kg : Grade} [HasBillF w₂ kg] (q : Query c s)
    (f : (v : Values s) → DbPM mode c β (w₂ v))
    (hst : Grade.Stable kg := by grade_stable) :
    DbM mode c (1 + kg * Query.gcard q) (List β) :=
  DbP.forQuery q f hst

namespace Db
export DbP (pure «raise» fetch fetchCell insert update delete insertSelect
  insertValues transaction)
export LeanLinq.LoopList (forLoop)
export LeanLinq.LoopQuery (forLoop)
end Db

/-- The `fetchCount` spec: the answer fits the query's own card, σ
preserved, one call of cost — the count-bound door's contract. -/
def Query.countWp (q : Query c s) : Wp Nat :=
  fun post σ k => ∀ n, n ≤ (Query.gcard q).eval σ → post n σ (k + 1)

instance (q : Query c s) : HasBill (Query.countWp q) 1 :=
  ⟨fun _post σ k hb n _ => hb n σ (k + 1) (by simp)⟩

/-- `q.fetchCountP` — ask how many rows `q` has, at the clean demonic
count-bound spec. Derived from the `fetchCell (q.count)` op — the
decode and the spine↔query bound bridge ride one `weaken`. -/
def Query.fetchCountP {mode : ScopeMode} (q : Query c s) : DbPM mode c Nat (Query.countWp q) :=
  FreerD.weaken
    (by
      intro post σ k hpost v hcb
      rcases v with _ | j
      · cases hcb.1
      · refine hpost j.toNat ?_
        have hb := (hcb.2 j rfl).2
        have hbr : ((q AliasOf).asPlainSpine.gcardAux 0) = Query.gcard q := by
          show (QueryP.asPlainSpine (q AliasOf)).gcardAux 0 =
            (q AliasOf).gcardAux 0
          rw [QueryP.asPlainSpine.eq_def]
          split
          · rename_i sp heq
            rw [heq]
          · exact Grade.mul_nat_one _
        rwa [hbr] at hb)
    (FreerD.bindS (DbP.fetchCell (q.count))
      (fun v => FreerD.pure (v.getD 0).toNat))

/-- `q.fetchCount` — the count as a billed one-call program. -/
def Query.fetchCount {mode : ScopeMode} (q : Query c s) : DbM mode c 1 Nat :=
  DbP.relax (Query.fetchCountP q)

/-- Count-then-spend: a `countWp` producer pays a continuation billed at
`n + 1` per counted row — the two-phase pattern's bill, `gcard + 2`. -/
theorem Query.countWp_bill_bind {q : Query c s} {β : Type} :
    Wp.le
      (Wp.bind (Query.countWp q)
        (fun n => (Wp.bill (Grade.nat n + Grade.nat 1) : Wp β)))
      (Wp.bill (Query.gcard q + Grade.nat 2)) := by
  intro post σ k hb n hn b σ' k₂ hk₂
  refine hb b σ' k₂ ?_
  rw [Grade.nat_add, Grade.eval_nat] at hk₂
  have hadd := Grade.le_eval_add (a := Query.gcard q) (b := Grade.nat 2) σ
  rw [Grade.eval_nat] at hadd
  omega

/-- `sc.fetch` — a scalar query as a billed one-call program. -/
def ScalarQuery.fetch {mode : ScopeMode} (sc : ScalarQuery c ⟨t, n⟩) : DbM mode c 1 (Nullable t) :=
  DbP.relax (DbP.fetchCell sc)

/-- `q.fetchLimit n` — the length-refined fetch, flowing:
`Query.from' … |>.orderBy … |>.fetchLimit 5`. -/
def Query.fetchLimit {mode : ScopeMode} (q : Query c s) (n : Nat) :
    DbM mode c 1 {xs : List (Values s) // xs.length ≤ n} :=
  DbP.fetchLimit q n

/-! ## The model interpreters — op handler + the generic folds -/

/-- The model's op handler: the in-memory evaluator, one arm per op —
writes move the environment through `applyCount`. -/
def DbOp.applyOp (ps : ParamEnv c.params) (now : Option String) :
    {β : Type} → DbOp c β → TableEnv c.tables →
    Except EvalError (β × TableEnv c.tables)
  | _, .raise message, _ => .error (.userError message)
  | _, .fetch q, env => do .ok (← q.evalRows ⟨env, ps, now⟩, env)
  | _, .fetchCell sq, env => do .ok (← sq.evalCell ⟨env, ps, now⟩, env)
  | _, .insert (inst := inst) i, env => do
      let (env', k) ← i.applyCount (inst := inst) env ps now
      .ok (k, env')
  | _, .update (inst := inst) u, env => do
      let (env', k) ← u.applyCount (inst := inst) env ps now
      .ok (k, env')
  | _, .delete (inst := inst) d, env => do
      let (env', k) ← d.applyCount (inst := inst) env ps now
      .ok (k, env')
  | _, .insertSelect (inst := inst) st, env => do
      let (env', k) ← st.applyCount (inst := inst) env ps now
      .ok (k, env')
  | _, .insertValues (inst := inst) st, env => do
      let (env', k) ← st.applyCount (inst := inst) env ps now
      .ok (k, env')

/-- Failure-aware database results retain complete table contents and the
number of attempted ordinary operations, including a failed statement. -/
structure DbOutcome (c : Ctx) (α : Type) where
  result : Except EvalError α
  state : TableEnv c.tables
  count : Nat

/-- Database interpretation counts the operations reported by each handler.
The generic free monad and its single-effect folds remain unchanged. -/
private def foldDbOutcome {E : Type → Type 1} {spec : EffWp E}
    (h : {β : Type} → E β → TableEnv c.tables → DbOutcome c β) :
    {α : Type} → {w : Wp α} → FreerD E spec α w →
    TableEnv c.tables → DbOutcome c α
  | _, _, .pure a, env => ⟨.ok a, env, 0⟩
  | _, _, .bindE e next, env =>
      let first := h e env
      match first.result with
      | .error err => ⟨.error err, first.state, first.count⟩
      | .ok b =>
          let rest := foldDbOutcome h (next b) first.state
          { rest with count := first.count + rest.count }
  | _, _, .weaken _ x, env => foldDbOutcome h x env

private def DbOp.applyOutcome (ps : ParamEnv c.params) (now : Option String)
    {β : Type} (e : DbOp c β) (env : TableEnv c.tables) : DbOutcome c β :=
  match DbOp.applyOp ps now e env with
  | .error err => ⟨.error err, env, e.cost⟩
  | .ok (b, env') => ⟨.ok b, env', e.cost⟩

/-- A failed body restores the complete entry state. The continuation is owned
by the surrounding free bind, so it runs only after this handler succeeds. -/
private def DbE.applyOutcome (ps : ParamEnv c.params) (now : Option String) :
    {β : Type} → DbE c β → TableEnv c.tables → DbOutcome c β
  | _, .op e, env => DbOp.applyOutcome ps now e env
  | _, .transaction body, env =>
      let inner := foldDbOutcome (DbOp.applyOutcome ps now) body env
      match inner.result with
      | .error err => ⟨.error err, env, inner.count⟩
      | .ok _ => inner

/-- The model retains state on failure: a failed transaction restores its
entry state, whereas a later outside failure retains the committed body. -/
def DbP.runOutcomeSt (ps : ParamEnv c.params) (now : Option String)
    {mode : ScopeMode} {α : Type} {w : Wp α}
    (x : DbPM mode c α w) (env : TableEnv c.tables) : DbOutcome c α :=
  match mode with
  | .outside => foldDbOutcome (DbE.applyOutcome ps now) x env
  | .inside => foldDbOutcome (DbOp.applyOutcome ps now) x env

/-- Full-state rollback and skipped continuation for a failed transaction.
This failure rule is separate from the success-only `Wp.sp` contract. -/
theorem DbP.transaction_failure {α β : Type} {bodyWp : Wp β}
    {nextWp : β → Wp α} {body : TxDbP c β bodyWp}
    {next : (b : β) → DbP c α (nextWp b)}
    {ps : ParamEnv c.params} {now : Option String}
    {env : TableEnv c.tables} {err : EvalError}
    (failed : (DbP.runOutcomeSt ps now body env).result = .error err) :
    DbP.runOutcomeSt ps now (.bindE (.transaction body) next) env =
      ⟨.error err, env, (DbP.runOutcomeSt ps now body env).count⟩ := by
  change (foldDbOutcome (E := DbOp c) (spec := dbOpWp)
    (fun e => DbOp.applyOutcome ps now e) body env).result = .error err at failed
  change foldDbOutcome (E := DbE c) (spec := dbWp)
    (fun e => DbE.applyOutcome ps now e) (.bindE (.transaction body) next) env =
      ⟨.error err, env, (foldDbOutcome (E := DbOp c) (spec := dbOpWp)
        (fun e => DbOp.applyOutcome ps now e) body env).count⟩
  simp only [foldDbOutcome, DbE.applyOutcome, failed]

/-- The success-only counted runner. Transaction control commands are outside
this database-operation count; a transaction contributes its body's count. -/
def DbP.runCountSt (ps : ParamEnv c.params) (now : Option String)
    {α : Type} {w : Wp α} (x : DbP c α w) (env : TableEnv c.tables) :
    Except EvalError (α × TableEnv c.tables × Nat) :=
  let outcome := DbP.runOutcomeSt ps now x env
  outcome.result.map fun a => (a, outcome.state, outcome.count)

/-- The state-threading core: writes move the environment, reads use it
where they stand. Errors discard state; `runOutcomeSt` retains it. -/
def DbP.runSt (ps : ParamEnv c.params) (now : Option String)
    {α : Type} {w : Wp α} (x : DbP c α w) (env : TableEnv c.tables) :
    Except EvalError (α × TableEnv c.tables) :=
  (DbP.runCountSt ps now x env).map fun (a, final, _) => (a, final)

/-- Reference interpreter, final environment discarded. -/
def DbP.runWith (ee : EvalEnv c) {α : Type} {w : Wp α}
    (x : DbP c α w) : Except EvalError α :=
  (DbP.runSt ee.params ee.now x ee.tables).map (·.1)

def DbP.runCount (ee : EvalEnv c) {α : Type} {w : Wp α}
    (x : DbP c α w) : Except EvalError (α × Nat) :=
  (DbP.runCountSt ee.params ee.now x ee.tables).map (fun (a, _, n) => (a, n))

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

/-- INSERT … SELECT: foreign names fixed, growth by exactly the rows
appended, and — `run_gcard` at the door — the count fits the source's
own symbolic card at this run's sizes. -/
theorem sizes_of_insertSelect {n : String} {s : Schema}
    [inst : HasTable c.tables n s]
    {st : InsertSelectStmt c n s} {env env' : TableEnv c.tables}
    {ps : ParamEnv c.params} {now : Option String} {k : Nat}
    (h : st.applyCount env ps now = .ok (env', k)) :
    (∀ m, m ≠ n → TableEnv.sizes env' m = TableEnv.sizes env m) ∧
    TableEnv.sizes env n ≤ TableEnv.sizes env' n ∧
    TableEnv.sizes env' n ≤ TableEnv.sizes env n + k ∧
    k ≤ (Query.gcard st.source).eval (TableEnv.sizes env) := by
  unfold InsertSelectStmt.applyCount at h
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
         inst.sizes_set_mono env _ n (by simp), ?_, ?_⟩
       · refine Nat.le_trans (inst.sizes_set_le env _ n)
           (Nat.max_le.mpr ⟨?_, Nat.le_add_right ..⟩)
         have := inst.rows_sizes env
         simp only [List.length_append]
         omega
       · exact Query.evalRows_gcard_le st.source hrows)

/-- Batched VALUES: growth capped by the batch, count exactly its
length. -/
theorem sizes_of_insertValues {n : String} {s : Schema}
    [inst : HasTable c.tables n s]
    {st : InsertValuesStmt c n s} {env env' : TableEnv c.tables}
    {ps : ParamEnv c.params} {now : Option String} {k : Nat}
    (h : st.applyCount env ps now = .ok (env', k)) :
    (∀ m, m ≠ n → TableEnv.sizes env' m = TableEnv.sizes env m) ∧
    TableEnv.sizes env n ≤ TableEnv.sizes env' n ∧
    TableEnv.sizes env' n ≤ TableEnv.sizes env n + st.rows.length ∧
    k = st.rows.length := by
  unfold InsertValuesStmt.applyCount at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · contradiction
  · injection h with h
    injection h with h1 h2
    subst h1
    subst h2
    refine ⟨fun m hm => inst.sizes_set_other env _ m hm,
      inst.sizes_set_mono env _ n (by simp), ?_, rfl⟩
    refine Nat.le_trans (inst.sizes_set_le env _ n)
      (Nat.max_le.mpr ⟨?_, Nat.le_add_right ..⟩)
    have := inst.rows_sizes env
    simp only [List.length_append]
    omega

/-- The model's **certified** op handler: each arm does not check the
op's spec, it **constructs** it — `run_gcard` as `evalRows_gcard_le`
for `fetch`, `enumScopes_gcard_le` behind `cellBound_of_evalCell` for
the COUNT cell, the `sizes_of_*` extraction lemmas for the writes —
at cost exactly one database operation on success. `raise` always returns an
error, so it needs no success certificate. The unchanged generic `runWithG`
therefore remains valid for successful base programs. -/
def DbOp.certApply (ps : ParamEnv c.params) (now : Option String) :
    {β : Type} → (e : DbOp c β) → (env : TableEnv c.tables) →
    Except EvalError {p : β × TableEnv c.tables //
      ∀ k, (dbOpWp e).sp p.1 (TableEnv.sizes env) k (TableEnv.sizes p.2) (k + 1)}
  | _, .raise message, _ => .error (.userError message)
  | _, .fetch q, env =>
      match hev : q.evalRows ⟨env, ps, now⟩ with
      | .ok xs => .ok ⟨(xs, env), fun _ _ hw =>
          hw xs (Query.evalRows_gcard_le q hev)⟩
      | .error e => .error e
  | _, .fetchCell sq, env =>
      match hev : sq.evalCell ⟨env, ps, now⟩ with
      | .ok v => .ok ⟨(v, env), fun _ _ hw =>
          hw v (cellBound_of_evalCell sq hev)⟩
      | .error e => .error e
  | _, .insert (inst := inst) i, env =>
      match hev : i.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ _ hw => by
            obtain ⟨hother, hlo, hhi, hk⟩ := sizes_of_insert hev
            subst hk
            exact hw _ hother hlo hhi⟩
      | .error e => .error e
  | _, .update (inst := inst) u, env =>
      match hev : u.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ _ hw => by
            obtain ⟨hσ, hk⟩ := sizes_of_update hev
            rw [funext hσ]
            exact hw k hk⟩
      | .error e => .error e
  | _, .delete (inst := inst) d, env =>
      match hev : d.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ _ hw => by
            obtain ⟨hother, hself, hdrop⟩ := sizes_of_delete hev
            exact hw _ k hother hself hdrop⟩
      | .error e => .error e
  | _, .insertSelect (inst := inst) st, env =>
      match hev : st.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ _ hw => by
            obtain ⟨hother, hlo, hhi, hg⟩ := sizes_of_insertSelect hev
            exact hw _ k hother hlo hhi hg⟩
      | .error e => .error e
  | _, .insertValues (inst := inst) st, env =>
      match hev : st.applyCount (inst := inst) env ps now with
      | .ok (env', k) =>
          .ok ⟨(k, env'), fun _ _ hw => by
            obtain ⟨hother, hlo, hhi, hk⟩ := sizes_of_insertValues hev
            subst hk
            exact hw _ hother hlo hhi⟩
      | .error e => .error e

/-- The outside handler certifies a variable number of database operations:
ordinary operations cost one; transactions reuse the unchanged generic
certified fold over their scope-free body signature. Every successful base
effect costs one; `raise` always fails and has no successful certificate. -/
private def DbE.certApply (ps : ParamEnv c.params) (now : Option String) :
    {β : Type} → (e : DbE c β) → (env : TableEnv c.tables) →
    Except EvalError {p : β × TableEnv c.tables × Nat //
      ∀ k, (dbWp e).sp p.1 (TableEnv.sizes env) k
        (TableEnv.sizes p.2.1) (k + p.2.2)}
  | _, .op e, env => do
      let ⟨(b, final), hb⟩ ← DbOp.certApply ps now e env
      .ok ⟨(b, final, 1), hb⟩
  | _, .transaction body, env =>
      FreerD.runWithG (DbOp.certApply ps now) body env

/-- Database adequacy composes the handler's actual body-operation count.
Transaction success has exactly the body's spec; failure atomicity is stated
separately by `transaction_failure`. The generic Freer folds are unchanged. -/
def DbP.runWithP (ps : ParamEnv c.params) (now : Option String) :
    {α : Type} → {w : Wp α} → DbP c α w → (env : TableEnv c.tables) →
    Except EvalError {p : α × TableEnv c.tables × Nat //
      ∀ k₀, w.sp p.1 (TableEnv.sizes env) k₀ (TableEnv.sizes p.2.1)
        (k₀ + p.2.2)}
  | _, _, .pure a, env => .ok ⟨(a, env, 0), fun _ _ hp => hp⟩
  | _, _, .bindE e next, env => do
      let ⟨(b, middle, firstCount), he⟩ ← DbE.certApply ps now e env
      let ⟨(a, final, nextCount), hn⟩ ← DbP.runWithP ps now (next b) middle
      .ok ⟨(a, final, firstCount + nextCount), fun k₀ => by
        have hcomp := hn (k₀ + firstCount)
        rw [Nat.add_assoc] at hcomp
        exact fun post hw => hcomp post (he k₀ _ hw)⟩
  | _, _, FreerD.weaken hle x, env => do
      let ⟨p, hp⟩ ← DbP.runWithP ps now x env
      .ok ⟨p, fun k₀ post hw => hp k₀ post (hle post _ _ hw)⟩

/-- The actual database-operation count fits the program's bill. -/
theorem DbP.runWithP_count_le {r : Grade} {α : Type}
    {x : Db c r α} {ps : ParamEnv c.params} {now : Option String}
    {env : TableEnv c.tables} {res}
    (_h : DbP.runWithP ps now x env = .ok res) :
    res.val.2.2 ≤ r.eval (TableEnv.sizes env) := by
  have hsp := res.property 0
  have := hsp (fun _ _ k => k ≤ r.eval (TableEnv.sizes env))
    (fun a σ' k' hk => by omega)
  omega

/-- The execution door: declare a budget, prove the bill fits it. For
closed bills (every batched program) the obligation discharges silently;
a data-dependent bill (`xs.length` for runtime `xs`) is not decidable
at elaboration, so the caller supplies the proof — by bounding the
collection or computing the budget from it. A bill over data that
exists only inside the program (just-fetched rows) has no proof to
give: that is N+1, rejected. -/
def DbP.exec {α : Type} {w : Wp α} (f : DbP c α w) (budget : Nat)
    (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    {r : Grade} [HasBill w r]
    (_h : r ≤ Grade.nat budget := by
      try simp only [Grade.ofNat_eq_nat, Grade.nat_add,
        Grade.nat_mul, Grade.nat_one_mul, Grade.mul_nat_one,
        Grade.nat_zero_add, Grade.add_nat_zero]
      first
        | exact Grade.le_refl _
        | (apply Grade.nat_le_nat; omega)
        | (intro σ
           simp only [gradeEvalNorm, Grade.ofNat_eq_nat, Grade.eval_add,
             Grade.eval_mul, Grade.eval_min, Grade.eval_nat, Grade.eval_tbl,
             Table.size]
           omega)
        | assumption) : Except EvalError α :=
  DbP.runWith ⟨env, ps, now⟩ f

/-- The **sized** door: a symbolic bill collapses against the model's
own table sizes, and the budget check runs *there* — the door for
programs priced in the database's terms (`customers.size + 1`). -/
def DbP.execWithin {α : Type} {w : Wp α} (f : DbP c α w) (budget : Nat)
    (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    {r : Grade} [HasBill w r] : Except EvalError α :=
  if r.eval (TableEnv.sizes env) ≤ budget then
    DbP.runWith ⟨env, ps, now⟩ f
  else
    .error (.internal s!"round budget exceeded: the program's bill exceeds {budget} at this database's sizes")

/-- The unchecked door: no budget, no obligation — interprets any
program at any spec. The explicit opt-out, visible at the call site. -/
def DbP.execAll {α : Type} {w : Wp α} (f : DbP c α w)
    (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none) :
    Except EvalError α :=
  DbP.runWith ⟨env, ps, now⟩ f

/-! ## `db!` — do-notation for the graded monad

`Db` cannot be a `Monad` instance: its bind *changes the bill*
(`m + n`), and hiding the grade to fit `Monad`'s fixed `m : Type → Type`
would blind `exec`'s budget check — the entire point. So the sugar is a
macro (the `query!` precedent): do-shaped clauses desugar to the graded
combinators and elaboration infers the bill.

```
def report : Db c 2 _ := db! {
  let parents ← .fetch parentsQ
  let ids := extract parents
  let children ← .fetchFor ids childrenQ
  return (parents, children)
}
```

`let x ← transaction { ...; return value }` handles the whole body before
continuing: commit on success, rollback and propagation on failure. Its bill
is the body's database-operation bill. The body has type `TxDb`, whose
operation signature excludes nested transactions, including through helpers.
`raise message` (or `let _ ← Db.raise message`) works inside or outside a
transaction, costs zero queries/writes, and propagates a user error. A block
still ends with `return`, preserving the conservative Unit success contract.

`let x ← e` is `Db.bind`, `let x := e` a plain `let`,
`let ys ← for x in xs do body` is `Db.forAll` (the per-row loop,
exact dynamic bill `k * xs.length`), and the final `return e` is
`Db.pure` — bills compose as `m + n + …`, definitionally the
closed sum for batched programs, so `exec`'s obligation discharges
silently. Two niceties keep inferred bills readable: the final
`let ys ← e; return f ys` pair fuses into `map` (no trailing `+ 0`),
and the whole block is wrapped in `withBill`, so a type annotation may
state any provably **dominating** spelling of the bill — `ids.length`
where the raw index is `1 * ids.length`, or a stated upper bound over a
`min`-priced limit. -/

syntax (name := fetchBind) "let " ident " ← " term : fetchClause
syntax (name := fetchIgnore) "let " "_" " ← " term : fetchClause
syntax (name := fetchRaise) "raise " term : fetchClause
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

/-- Infer a block's mode from its context, defaulting a standalone block to
outside. Finish its local bill obligations before an enclosing bind asks for
a constant continuation bill. A generic helper's mode remains generic. -/
syntax (name := defaultDbMode) "db_mode% " term : term

open Lean Elab Term Meta in
@[term_elab defaultDbMode] def elabDefaultDbMode : TermElab := fun stx expected => withSynthesize do
  let body ← elabTerm stx[1] expected
  let ty ← whnf (← inferType body)
  if ty.isAppOfArity ``FreerD 4 then
    let effect ← instantiateMVars (ty.getArg! 0)
    if effect.isAppOfArity ``DbEffect 2 then
      let mode ← instantiateMVars (effect.getArg! 0)
      if mode.getAppFn.isMVar then
        discard <| isDefEq mode (mkConst ``ScopeMode.outside)
  return body

open Lean in
@[macro fetchProg] def expandFetch : Lean.Macro := fun stx => do
  let clauses ← fuseBoundedLoops (stx[2].getSepArgs.map resolveClause).toList
  match clauses.reverse with
  | [] => Macro.throwError "db! must end with a `return` clause"
  | last :: revRest =>
    unless last.isOfKind ``fetchRet do
      Macro.throwErrorAt last "db! must end with a `return` clause"
    -- fuse the final `let ys ← e; return f ys` into `map` (bill `r`, not
    -- `r + 0`) so inferred bills stay clean
    let (init, revRest) ← do
      match revRest with
      | prev :: rest =>
        if prev.isOfKind ``fetchBind then
          pure (← `(LeanLinq.DbP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩)) $(⟨prev[3]⟩)), rest)
        else if prev.isOfKind ``fetchIgnore then
          pure (← `(LeanLinq.DbP.map (fun _ => $(⟨last[1]⟩)) $(⟨prev[3]⟩)), rest)
        else if prev.isOfKind ``fetchForAll then
          pure (← `(LeanLinq.DbP.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩))
            (LeanLinq.Db.forLoop $(⟨prev[6]⟩) (fun $(⟨prev[4]⟩) => $(⟨prev[8]⟩)))), rest)
        else
          pure (← `(LeanLinq.DbP.pure $(⟨last[1]⟩)), revRest)
      | [] => pure (← `(LeanLinq.DbP.pure $(⟨last[1]⟩)), revRest)
    let folded ← revRest.foldlM (init := init) fun (acc : TSyntax `term) c => do
      if c.isOfKind ``fetchBind then
        `(LeanLinq.DbP.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchIgnore then
        `(LeanLinq.DbP.bind $(⟨c[3]⟩) (fun _ => $acc))
      else if c.isOfKind ``fetchRaise then
        `(LeanLinq.DbP.bind (LeanLinq.DbP.raise $(⟨c[1]⟩)) (fun _ => $acc))
      else if c.isOfKind ``fetchForAll then
        -- let y ← for x in xs do body — a list loops at its exact bill
        -- k * xs.length, a query at its symbolic price 1 + k * gcard
        `(LeanLinq.DbP.bind
            (LeanLinq.Db.forLoop $(⟨c[6]⟩) (fun $(⟨c[4]⟩) => $(⟨c[8]⟩)))
            (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchLet then
        `(let $(⟨c[1]⟩) := $(⟨c[3]⟩); $acc)
      else
        Macro.throwErrorAt c "expected `let x ← e`, `let x := e`, `raise message`, `let ys ← for x in xs do e`, or a final `return e`"
    `(db_mode% (LeanLinq.DbP.withBill $folded))

/-- A transaction body uses the same graded clauses as `db!`; its expected
inside mode rejects nested transaction terms even when hidden in helpers. -/
scoped syntax (name := transactionBlock)
  "transaction " "{" withoutPosition(sepByIndentSemicolon(fetchClause)) "}" : term

open Lean in
@[macro transactionBlock] def expandTransaction : Lean.Macro := fun stx => do
  let body := Syntax.node stx.getHeadInfo ``fetchProg
    #[mkAtom "db!", mkAtom "{", stx[2], mkAtom "}"]
  `(LeanLinq.DbP.transaction $(⟨body⟩))

namespace QueryB
export Query (execQuery fetchLimit forQuery fetchCount)
end QueryB

namespace ScalarB
export ScalarQuery (fetch)
end ScalarB

/- Expected-type dot notation such as `.fetch q` must also resolve through
mode-polymorphic builder results, before their aliases unfold to FreerD. -/
namespace DbPM
export DbP (pure «raise» fetch fetchCell insert update delete insertSelect insertValues
  fetchFor fetchLimit relax bind map withBound withBill weaken bindD' forAll
  forRows forFetched forQuery)
end DbPM

/- Preserve program dot notation after the public aliases unfold to FreerD.
Execution methods still require the outside effect signature. -/
namespace FreerD
export DbP (relax bind map withBound withBill bindD' forAll forRows
  forFetched forQuery runSt runOutcomeSt runWith runCountSt runCount runWithP
  exec execWithin execAll)
end FreerD

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
  show (Grade.gmin (q.gcardAux m) (Grade.nat l)).eval σ ≤ l
  rw [Grade.eval_min, Grade.eval_nat]
  exact Nat.min_le_right ..

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
