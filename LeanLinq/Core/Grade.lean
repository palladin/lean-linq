/-! # `Grade` — round budgets, symbolic in table sizes

The round-trip currency of `Db`: a grade **is its collapse** — a
function from table-size valuations to `Nat`. Closed grades (`2`,
`5 + 3`) are the constant functions; symbolic grades price programs in
the database's own terms — `|customers| + 1` is "one round per
customer, plus one" — as the function that reads the size and adds one.

There is no ⊤ and no ℕ∞: the unknown is not "unbounded", it is *a
symbol*, and evaluation at a size valuation `σ : String → Nat` is
application. What ⊤ used to shrug at, a function prices.

**The algebra is pointwise, so the laws are arithmetic.** `+`/`*`/`min`
act valuation-by-valuation, which makes every evaluation homomorphism
`rfl` (`eval_add`, `eval_mul`, `eval_min`) and every comparison a plain
`Nat` fact after `intro σ` — the door tactics decompose any grade
expression with a small `simp only` set and hand the rest to `omega`.
(An earlier design kept grades as canonical max-plus polynomials so the
*index bookkeeping* of a graded monad could be definitional; with cost
inside the wp, grades are values in specs, and values need no normal
form — just arithmetic.)

The order is **semantic**: `a ≤ b` iff `a`'s value sits under `b`'s at
every size valuation. Closed comparisons discharge via `Grade.nat_le_nat`
+ `omega` or pointwise; a symbolic grade at a closed budget simply has
no proof — the static refusal. -/

namespace LeanLinq

/-- A round grade: table-size valuations in, price out. -/
def Grade : Type := (String → Nat) → Nat

namespace Grade

/-- A closed grade. -/
def nat (n : Nat) : Grade := fun _ => n

/-- The size of the named table, as a grade. -/
def tbl (x : String) : Grade := fun σ => σ x

def add (a b : Grade) : Grade := fun σ => a σ + b σ

def mul (a b : Grade) : Grade := fun σ => a σ * b σ

/-- Pointwise `min` — what prices `LIMIT`: `min inner l`, honest even
when the inner bound is symbolic. -/
def gmin (a b : Grade) : Grade := fun σ => min (a σ) (b σ)

instance : OfNat Grade n := ⟨nat n⟩

/-- Nat expressions embed as closed grades — `Db c (n + 1) α`
reads as before. -/
instance : Coe Nat Grade := ⟨nat⟩

instance : Add Grade := ⟨add⟩
instance : Mul Grade := ⟨mul⟩

/-- Collapse against known sizes — application. -/
def eval (σ : String → Nat) : Grade → Nat := fun g => g σ

/-- The order is semantic: dominated at **every** size valuation. -/
def Le (a b : Grade) : Prop := ∀ σ : String → Nat, a.eval σ ≤ b.eval σ

instance : LE Grade := ⟨Le⟩

theorem le_refl (a : Grade) : a ≤ a := fun _ => Nat.le_refl _

theorem le_trans {a b c : Grade} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  fun σ => Nat.le_trans (h₁ σ) (h₂ σ)

/-- Extensionality through `eval` — the equality half of the door
tactics: `refine Grade.ext fun σ => ?_`, decompose, `omega`. -/
theorem ext {a b : Grade} (h : ∀ σ, a.eval σ = b.eval σ) : a = b :=
  funext h

@[simp] theorem eval_nat (σ : String → Nat) (n : Nat) :
    (nat n).eval σ = n := rfl

@[simp] theorem eval_tbl (σ : String → Nat) (x : String) :
    (tbl x).eval σ = σ x := rfl

theorem nat_le_nat {a b : Nat} (h : a ≤ b) : nat a ≤ nat b :=
  fun _ => h

/-- `g + 0 = g` — definitional now (`Nat.add _ 0` reduces). -/
theorem add_zero (g : Grade) : g + (0 : Grade) = g := rfl

theorem zero_add (g : Grade) : (0 : Grade) + g = g :=
  ext fun _ => Nat.zero_add _

theorem mul_one (g : Grade) : g * (1 : Grade) = g :=
  ext fun _ => Nat.mul_one _

theorem one_mul (g : Grade) : (1 : Grade) * g = g :=
  ext fun _ => Nat.one_mul _

/-- Closed addition folds — definitionally. -/
theorem nat_add (a b : Nat) : nat a + nat b = nat (a + b) := rfl

set_option warning.simp.varHead false in
@[simp] theorem ofNat_eq_nat (n : Nat) :
    (no_index (OfNat.ofNat n) : Grade) = nat n := rfl

/-- The unit laws, `nat`-spelled (what the goal looks like after
`ofNat_eq_nat` normalizes literals) — delegating: the spellings are
definitionally equal. -/
theorem mul_nat_one (g : Grade) : g * nat 1 = g := mul_one g

theorem nat_one_mul (g : Grade) : nat 1 * g = g := one_mul g

theorem add_nat_zero (g : Grade) : g + nat 0 = g := add_zero g

theorem nat_zero_add (g : Grade) : nat 0 + g = g := zero_add g

theorem nat_mul (a b : Nat) : nat a * nat b = nat (a * b) := rfl

/-! ## The evaluation homomorphism — now `rfl`

Pointwise algebra evaluates pointwise; the additive law that used to be
NE-conditioned (max-plus −∞ broke it) is an equality with no side
conditions, because the −∞ is no longer a value. -/

section EvalHom

variable (σ : String → Nat)

theorem eval_add (a b : Grade) :
    (a + b).eval σ = a.eval σ + b.eval σ := rfl

theorem eval_mul (a b : Grade) :
    (a * b).eval σ = a.eval σ * b.eval σ := rfl

theorem eval_min (a b : Grade) :
    (gmin a b).eval σ = min (a.eval σ) (b.eval σ) := rfl

/-- The `≥` half of the additive homomorphism, kept under its historic
name for the proofs that consume it — an equality's easy half now. -/
theorem le_eval_add {a b : Grade} :
    a.eval σ + b.eval σ ≤ (a + b).eval σ := Nat.le_refl _

/-- Multiplication is monotone under the semantic order — the transport
the loop's bill proof rides through (`k * nat len ≤ k * gcard` from
`fetch`'s contract). -/
theorem mul_le_mul_left (k : Grade) {a b : Grade} (h : a ≤ b) :
    k * a ≤ k * b :=
  fun σ => Nat.mul_le_mul_left _ (h σ)

end EvalHom

end Grade

end LeanLinq
