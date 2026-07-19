import LeanLinq.Core.Grade

/-! # The graded Freer Dijkstra monad

The generic core under `Db`: a Freer monad over an abstract effect
signature `E`, intrinsically indexed by a **graded** weakest-precondition
transformer — the spec observes the result, the table sizes, *and the
cost consumed*. One spec object per op (`EffWp`) carries both the op's
logical meaning and its price; grades (`Grade`, canonical max-plus
polynomials) survive as the *bound language* inside specs — `Wp.bill` —
which is what keeps budget checks at the execution doors automatic.

Three constructors and nothing else: `pure`, `bindE` (ONE effect call,
then the rest — Freer normal form, so the cost of a program is
structurally its effect-call count), and `weaken` (the rule of
consequence). Monadic bind is *derived* (`bindS`), total by structural
recursion, its index laws definitional. -/

namespace LeanLinq

/-- The graded specification monad: weakest-precondition transformers
over table-size valuations **and a cost counter**. Given what you want
of the result (`post`, which sees the result, the sizes after, and the
total cost), the spec answers what must hold at σ having already spent
`k`. Its monad laws are definitional — cost and σ thread through `bind`
the same way — which is what lets the computation type's index compose
by law rather than by packaging. -/
def Wp (α : Type) : Type :=
  (α → (String → Nat) → Nat → Prop) → (String → Nat) → Nat → Prop

namespace Wp

def pure (a : α) : Wp α := fun post σ k => post a σ k

def bind (w : Wp α) (f : α → Wp β) : Wp β :=
  fun post σ k => w (fun a σ' k' => f a post σ' k') σ k

/-- Spec refinement: anything `w₂` demands, `w₁` delivers. -/
def le (w₁ w₂ : Wp α) : Prop := ∀ post σ k, w₂ post σ k → w₁ post σ k

/-- The trivial spec — the ⊤ of `le` (its obligations can never be
invoked), so every program relaxes to it for free. Kept as the
"promise nothing at all" corner; the `Db` surface lives at `bill`. -/
def triv (α : Type) : Wp α := fun _ _ _ => False

/-- The strongest-postcondition reading: `a` is a possible result of a
`w`-specified run from `(σ₀, k₀)` ending at `(σ₁, k₁)`. What the
verified door hands back about the *particular* result — the demonic ∀
in a spec, instantiated, cost included. -/
def sp (w : Wp α) (a : α) (σ₀ : String → Nat) (k₀ : Nat)
    (σ₁ : String → Nat) (k₁ : Nat) : Prop :=
  ∀ post, w post σ₀ k₀ → post a σ₁ k₁

theorem pure_bind (a : α) (f : α → Wp β) : (Wp.pure a).bind f = f a := rfl
theorem bind_assoc (w : Wp α) (f : α → Wp β) (g : β → Wp γ) :
    (w.bind f).bind g = w.bind (fun a => (f a).bind g) := rfl
theorem bind_pure (w : Wp α) : w.bind Wp.pure = w := rfl
theorem triv_bind (f : α → Wp β) : (Wp.triv α).bind f = Wp.triv β := rfl

theorem le_refl (w : Wp α) : w.le w := fun _ _ _ h => h
theorem le_trans {w₁ w₂ w₃ : Wp α} (h₁ : w₁.le w₂) (h₂ : w₂.le w₃) :
    w₁.le w₃ := fun post σ k h => h₁ post σ k (h₂ post σ k h)

/-- `bind` is monotone in the producer — no monotonicity of the specs
themselves needed, because `le` quantifies over every post. -/
theorem bind_le_bind_left {w₁ w₂ : Wp α} (f : α → Wp β) (h : w₁.le w₂) :
    (w₁.bind f).le (w₂.bind f) :=
  fun post σ k hw => h _ σ k hw

end Wp

/-! ## σ-stability — the side condition of bill composition

A `bill` prices its grade at the *entry* σ, but a preceding stage may
have moved σ (writes). Sequencing bills is sound exactly when the
second bill cannot be raised by that movement — trivially so for every
closed grade, which is every composition the surface performs
(symbolic prices compose at strong specs, where σ-preservation is
visible in the wp itself). -/

/-- The grade's price never grows at another valuation. Every closed
grade qualifies (`stable_nat`); products with closed lengths preserve
it (`stable_mul_nat`). -/
def Grade.Stable (n : Grade) : Prop :=
  ∀ σ σ' : String → Nat, n.eval σ' ≤ n.eval σ

theorem Grade.stable_nat (j : Nat) : Grade.Stable (Grade.nat j) := by
  intro σ σ'
  simp

theorem Grade.stable_mul_nat {k : Grade} (h : Grade.Stable k) (j : Nat) :
    Grade.Stable (k * Grade.nat j) := by
  intro σ σ'
  rw [Grade.eval_mul, Grade.eval_mul, Grade.eval_nat, Grade.eval_nat]
  exact Nat.mul_le_mul_right j (h σ σ')

/-- Discharge `Grade.NE` goals for kit-built grades. -/
syntax "grade_ne" : tactic

macro_rules
  | `(tactic| grade_ne) =>
    `(tactic| first
        | assumption
        | exact LeanLinq.Grade.ne_nat _
        | exact LeanLinq.Grade.ne_tbl _
        | (apply LeanLinq.Grade.ne_add <;> grade_ne)
        | (apply LeanLinq.Grade.ne_mul <;> grade_ne))

/-- Discharge `Grade.Stable` goals for closed grades. -/
syntax "grade_stable" : tactic

macro_rules
  | `(tactic| grade_stable) =>
    `(tactic| first
        | assumption
        | exact LeanLinq.Grade.stable_nat _
        | ((apply LeanLinq.Grade.stable_mul_nat) <;> grade_stable))

/-! ## The bill — the surface spec -/

namespace Wp

/-- "Says nothing about the result; promises the cost": at entry sizes σ
having spent `k`, every outcome lands within `k + r.eval σ`. The `Db`
surface is this spec — the round-trip bill in the type, now backed by
the cost the wp actually threads. -/
def bill (r : Grade) : Wp α :=
  fun post σ k => ∀ a σ' k', k' ≤ k + r.eval σ → post a σ' k'

theorem bill_mono {r r' : Grade} (h : r ≤ r') :
    (bill r : Wp α).le (bill r') :=
  fun _post σ _k hb a σ' k' hk =>
    hb a σ' k' (Nat.le_trans hk (Nat.add_le_add_left (h σ) _))

/-- `pure` fits any bill: it costs nothing. -/
theorem bill_pure (a : α) (r : Grade) : (Wp.pure a).le (bill r) :=
  fun _post σ k hb => hb a σ k (Nat.le_add_right k _)

/-- The master sequencing law: a stage that fits `bill m` followed by
stages that fit `bill (g a)` — each bounded by a σ-stable `B` — fits
`bill (m + B)`. No monotonicity anywhere: the producer's `le` is applied
at the postcondition the continuation manufactures. -/
theorem bill_bindD_of_le {α β : Type} {w : Wp α} {w₂ : α → Wp β}
    {m B : Grade} {g : α → Grade}
    (hm : w.le (bill m)) (hn : ∀ a, (w₂ a).le (bill (g a)))
    (hg : ∀ a, g a ≤ B)
    (hmne : m.NE) (hBne : B.NE) (hs : Grade.Stable B) :
    (w.bind w₂).le (bill (m + B)) := by
  intro post σ k hb
  refine hm _ σ k ?_
  intro a σ' k₁ hk₁
  refine hn a post σ' k₁ ?_
  intro b σ'' k₂ hk₂
  refine hb b σ'' k₂ ?_
  have hga := hg a σ'
  have hstab := hs σ σ'
  have hadd := Grade.le_eval_add (a := m) (b := B) σ hmne hBne
  omega

/-- Constant-budget sequencing — the surface `bind`'s law. -/
theorem bill_bind_of_le {α β : Type} {w : Wp α} {w₂ : α → Wp β}
    {m n : Grade}
    (hm : w.le (bill m)) (hn : ∀ a, (w₂ a).le (bill n))
    (hmne : m.NE) (hnne : n.NE) (hs : Grade.Stable n) :
    (w.bind w₂).le (bill (m + n)) :=
  bill_bindD_of_le hm hn (fun _ => Grade.le_refl n) hmne hnne hs

/-- Mapping is free: the bill does not move. -/
theorem bill_map_of_le {α β : Type} {w : Wp α} {r : Grade} (f : α → β)
    (hm : w.le (bill r)) :
    (w.bind (fun a => Wp.pure (f a))).le (bill r) := by
  intro post σ k hb
  refine hm _ σ k ?_
  intro a σ' k' hk
  exact hb (f a) σ' k' hk

/-- The loop step: a `bill k`-priced body then a `bill (k * j)`-priced
tail fit `bill (k * (j+1))` — pure Nat arithmetic once `eval_mul`
splits the product. -/
theorem bill_loop_step {kg : Grade} (hks : Grade.Stable kg)
    (j : Nat) {α β : Type} {w : Wp α} {w₂ : α → Wp β}
    (hm : w.le (bill kg)) (hn : ∀ a, (w₂ a).le (bill (kg * Grade.nat j))) :
    (w.bind w₂).le (bill (kg * Grade.nat (j + 1))) := by
  intro post σ k hb
  refine hm _ σ k ?_
  intro a σ' k₁ hk₁
  refine hn a post σ' k₁ ?_
  intro b σ'' k₂ hk₂
  refine hb b σ'' k₂ ?_
  rw [Grade.eval_mul, Grade.eval_nat] at hk₂
  rw [Grade.eval_mul, Grade.eval_nat]
  have hstab := hks σ σ'
  have hmul : kg.eval σ' * j ≤ kg.eval σ * j :=
    Nat.mul_le_mul_right j hstab
  have : kg.eval σ * (j + 1) = kg.eval σ + kg.eval σ * j := by
    rw [Nat.mul_succ]; omega
  omega

end Wp

/-! ## Billing as inference

The surface combinators recover a program's bill from its spec by
typeclass search: each op signature registers one instance (`dbWp e`
fits `bill 1`), `bill r` fits itself, and derived combinators produce
billed programs by construction. -/

/-- `w` fits the bill `r`. -/
class HasBill {α : Type} (w : Wp α) (r : outParam Grade) : Prop where
  le : w.le (Wp.bill r)

instance {α : Type} (r : Grade) : HasBill (Wp.bill r : Wp α) r :=
  ⟨Wp.le_refl _⟩

instance {α : Type} (a : α) : HasBill (Wp.pure a) 0 :=
  ⟨Wp.bill_pure a 0⟩

/-- Every member of the family `w₂` fits the bill `n` — the shape the
surface `bind`'s continuation needs. -/
class HasBillF {α β : Type} (w₂ : α → Wp β) (n : outParam Grade) : Prop where
  le : ∀ a, (w₂ a).le (Wp.bill n)

instance {α β : Type} (w : Wp β) (n : Grade) [h : HasBill w n] :
    HasBillF (fun _ : α => w) n :=
  ⟨fun _ => h.le⟩

instance {α β : Type} (f : α → β) : HasBillF (fun a => Wp.pure (f a)) 0 :=
  ⟨fun a => Wp.bill_pure (f a) 0⟩

/-! ## The monad -/

/-- The whole meaning of an effect signature: one graded spec per op —
its logical contract and its price, unified. -/
def EffWp (E : Type → Type 1) : Type 1 := {α : Type} → E α → Wp α

/-- A Freer program over the effect signature `E`, intrinsically indexed
by its graded spec. Three constructors: `pure` (spec `Wp.pure`, cost 0),
`bindE` — **one** effect call then the rest, the index computed by
`Wp.bind` from the op's own spec — and `weaken`, the rule of
consequence, underivable because indices don't transport along
implication. The monad bind is *derived* (`bindS`). -/
inductive FreerD (E : Type → Type 1) (spec : EffWp E) :
    (α : Type) → Wp α → Type 1 where
  | pure : {α : Type} → (a : α) → FreerD E spec α (Wp.pure a)
  | bindE : {β α : Type} → {w₂ : β → Wp α} →
      (e : E β) → ((b : β) → FreerD E spec α (w₂ b)) →
      FreerD E spec α ((spec e).bind w₂)
  | weaken : {α : Type} → {w w' : Wp α} →
      w.le w' → FreerD E spec α w → FreerD E spec α w'

namespace FreerD

variable {E : Type → Type 1} {spec : EffWp E}

/-- THE bind — derived, total by structural recursion, index laws
definitional (`pure_bind` and `bind_assoc` are `rfl`; the `weaken` arm
rides `bind_le_bind_left`). -/
def bindS {α β : Type} {w₂ : α → Wp β} :
    {w : Wp α} → FreerD E spec α w → ((a : α) → FreerD E spec β (w₂ a)) →
    FreerD E spec β (w.bind w₂)
  | _, .pure a, k => k a
  | _, .bindE e f, k => .bindE e (fun b => bindS (f b) k)
  | _, .weaken h x, k => .weaken (Wp.bind_le_bind_left w₂ h) (bindS x k)

/-- One effect call as a program — the index is `spec e` itself
(`bind`'s right unit is definitional by eta). -/
def liftE {β : Type} (e : E β) : FreerD E spec β (spec e) :=
  .bindE e .pure

def mapS {α β : Type} (f : α → β) {w : Wp α} (x : FreerD E spec α w) :
    FreerD E spec β (w.bind (fun a => Wp.pure (f a))) :=
  bindS x (fun a => .pure (f a))

/-- The generic monadic fold — how a program meets any carrier that can
run one op: the drivers hand this an IO op-handler. -/
def foldM {m : Type → Type} [Monad m] (h : {β : Type} → E β → m β) :
    {α : Type} → {w : Wp α} → FreerD E spec α w → m α
  | _, _, .pure a => Pure.pure a
  | _, _, .bindE e f => do foldM h (f (← h e))
  | _, _, .weaken _ x => foldM h x

/-- The state-threading fold — the model interpreter's shape: one op
handler over a state `S`, errors in `Except`. -/
def foldSt {ε S : Type} (h : {β : Type} → E β → S → Except ε (β × S)) :
    {α : Type} → {w : Wp α} → FreerD E spec α w → S → Except ε (α × S)
  | _, _, .pure a, s => .ok (a, s)
  | _, _, .bindE e f, s => do
      let (b, s₁) ← h e s
      foldSt h (f b) s₁
  | _, _, .weaken _ x, s => foldSt h x s

/-- `foldSt`, instrumented: also counts the effect calls performed. -/
def foldStC {ε S : Type} (h : {β : Type} → E β → S → Except ε (β × S)) :
    {α : Type} → {w : Wp α} → FreerD E spec α w → S →
    Except ε (α × S × Nat)
  | _, _, .pure a, s => .ok (a, s, 0)
  | _, _, .bindE e f, s => do
      let (b, s₁) ← h e s
      let (a, s₂, n) ← foldStC h (f b) s₁
      .ok (a, s₂, 1 + n)
  | _, _, .weaken _ x, s => foldStC h x s

end FreerD

/-! ## The certified fold — per-op `correct`, whole-program adequacy -/

/-- A certified op handler over a state `S` observed through `obs`:
each op's run satisfies the op's own spec, `sp`-formed about the actual
result, at cost exactly one effect call. This is the per-op `correct`
obligation — paid once per (effect, interpreter) pair; `runWithG` lifts
it to every program. -/
def CertHandler (E : Type → Type 1) (spec : EffWp E) (ε S : Type)
    (obs : S → (String → Nat)) : Type 1 :=
  {β : Type} → (e : E β) → (s : S) →
    Except ε {p : β × S //
      ∀ k, (spec e).sp p.1 (obs s) k (obs p.2) (k + 1)}

/-- The adequacy fold: same semantics as `foldStC`, and the result
carries `Wp.sp` — every demand the spec can back is a fact about *this*
result, *this* final state, and *this* op count. The `bindE` arm chains
the op's certificate through the continuation's — pure logic; `weaken`
transports along the refinement. -/
def FreerD.runWithG {E : Type → Type 1} {spec : EffWp E} {ε S : Type}
    {obs : S → (String → Nat)} (h : CertHandler E spec ε S obs) :
    {α : Type} → {w : Wp α} → FreerD E spec α w → (s : S) →
    Except ε {p : α × S × Nat //
      ∀ k₀, w.sp p.1 (obs s) k₀ (obs p.2.1) (k₀ + p.2.2)}
  | _, _, .pure a, s => .ok ⟨(a, s, 0), fun _ _ hp => hp⟩
  | _, _, .bindE e f, s => do
      let ⟨(b, s₁), he⟩ ← h e s
      let ⟨(a₂, s₂, n), hf⟩ ← runWithG h (f b) s₁
      .ok ⟨(a₂, s₂, 1 + n), fun k₀ => by
        have hcomp := hf (k₀ + 1)
        rw [Nat.add_assoc] at hcomp
        exact fun post hw => hcomp post (he k₀ _ hw)⟩
  | _, _, .weaken hle x, s => do
      let ⟨p, hp⟩ ← runWithG h x s
      .ok ⟨p, fun k₀ post hw => hp k₀ post (hle post _ _ hw)⟩

/-- **Count adequacy**: a bill-typed program's actual effect-call count
fits its bill at the entry observation — the bill in the type is a
theorem about every certified run. -/
theorem FreerD.runWithG_count_le {E : Type → Type 1} {spec : EffWp E}
    {ε S : Type} {obs : S → (String → Nat)}
    {h : CertHandler E spec ε S obs} {r : Grade} {α : Type}
    {x : FreerD E spec α (Wp.bill r)} {s : S} {res}
    (_hrun : x.runWithG h s = .ok res) :
    res.val.2.2 ≤ r.eval (obs s) := by
  have hsp := res.property 0
  have := hsp (fun _ _ k => k ≤ r.eval (obs s))
    (fun a σ' k' hk => by omega)
  omega

end LeanLinq
