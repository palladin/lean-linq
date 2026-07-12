import LeanLinq.Core.Types

/-! # `Bound` — the ℕ∞ lattice of static bounds

One general order for every static bound in the library: it grades
`DbFetch` (round-trip budgets), bounds row counts (`fetchLimit`,
`Query.card`), and absorbs at ⊤. See the `Bound` doc below for the
surface contract. -/

namespace LeanLinq

/-- The bound lattice ℕ∞: a quantity that is finite (`fin n`) or `top`
(⊤, unbounded). One general order for every static bound in the library:
it grades `DbFetch` (the round-trip budget) and bounds row counts
(`fetchLimit`). ⊤ is the top of `≤` and the vacuously-true bound, and it
is absorbing (`⊤ + b = ⊤`, `max ⊤ b = ⊤`): one unbounded part makes the
whole program unbounded, visibly. Every execution still terminates
(finite trees over finite lists); ⊤ only declines to name a bound.

The constructors are the library's spelling, not the user's: surface
code writes numerals (`5`), Nat expressions (`ids.length` — coerced),
and `⊤`; `.fin`/`.top` appear in proofs and the fetch API itself. -/
inductive Bound where
  | fin (n : Nat)
  | top
  deriving DecidableEq, Repr

namespace Bound
instance : OfNat Bound n := ⟨.fin n⟩
@[reducible] def add : Bound → Bound → Bound
  | .fin a, .fin b => .fin (a + b)
  | _, _ => .top
@[reducible] def gmax : Bound → Bound → Bound
  | .fin a, .fin b => .fin (Nat.max a b)
  | _, _ => .top
@[reducible] def mul : Bound → Bound → Bound
  | .fin a, .fin b => .fin (a * b)
  | _, _ => .top
@[reducible] def gmin : Bound → Bound → Bound
  | .fin a, .fin b => .fin (Nat.min a b)
  | .fin a, .top => .fin a
  | .top, b => b
@[reducible] def ble : Bound → Bound → Bool
  | _, .top => true
  | .top, .fin _ => false
  | .fin a, .fin b => a ≤ b
instance : Add Bound := ⟨add⟩
instance : Mul Bound := ⟨mul⟩
instance : Max Bound := ⟨gmax⟩
instance : Min Bound := ⟨gmin⟩
instance : LE Bound := ⟨fun a b => ble a b = true⟩
instance (a b : Bound) : Decidable (a ≤ b) := decEq _ _

/-! The algebra, for the standard tactics: `@[simp]` unit laws and AC
instances, so `simp`/`ac_rfl` rearrange bounds out of the box — no
bespoke lemmas at use sites. -/

@[simp] theorem add_zero : (r : Bound) → r + (0 : Bound) = r
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem zero_add : (n : Bound) → (0 : Bound) + n = n
  | .top => rfl
  | .fin m => congrArg Bound.fin (Nat.zero_add m)
@[simp] theorem one_mul : (n : Bound) → 1 * n = n
  | .top => rfl
  | .fin m => congrArg Bound.fin (Nat.one_mul m)
@[simp] theorem mul_one : (n : Bound) → n * 1 = n
  | .top => rfl
  | .fin m => congrArg Bound.fin (Nat.mul_one m)

/-- Everything is bounded by ⊤ — and definitionally so. -/
theorem le_top (b : Bound) : b ≤ .top := rfl

@[simp] theorem add_top : (a : Bound) → a + .top = .top
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem top_add : (a : Bound) → .top + a = .top
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem mul_top : (a : Bound) → a * .top = .top
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem top_mul : (a : Bound) → .top * a = .top
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem max_top : (a : Bound) → max a .top = .top
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem top_max : (a : Bound) → max .top a = .top
  | .fin _ => rfl
  | .top => rfl

theorem add_comm : (a b : Bound) → a + b = b + a
  | .fin x, .fin y => congrArg Bound.fin (Nat.add_comm x y)
  | .fin _, .top => rfl
  | .top, .fin _ => rfl
  | .top, .top => rfl
theorem add_assoc : (a b c : Bound) → a + b + c = a + (b + c)
  | .fin x, .fin y, .fin z => congrArg Bound.fin (Nat.add_assoc x y z)
  | .fin _, .fin _, .top => rfl
  | .fin _, .top, _ => by cases ‹Bound› <;> rfl
  | .top, _, _ => by rename_i b c; cases b <;> cases c <;> rfl

instance : Std.Commutative (α := Bound) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := Bound) (· + ·) := ⟨add_assoc⟩

theorem le_refl (g : Bound) : g ≤ g := by
  cases g with
  | top => exact rfl
  | fin a => exact decide_eq_true (Nat.le_refl a)

@[simp] theorem min_top : (a : Bound) → min a .top = a
  | .fin _ => rfl
  | .top => rfl
@[simp] theorem top_min : (a : Bound) → min .top a = a
  | .fin _ => rfl
  | .top => rfl

theorem min_le_left : (a b : Bound) → min a b ≤ a
  | .fin x, .fin y => decide_eq_true (Nat.min_le_left x y)
  | .fin x, .top => le_refl (.fin x)
  | .top, .fin _ => rfl
  | .top, .top => rfl

theorem min_le_right : (a b : Bound) → min a b ≤ b
  | .fin x, .fin y => decide_eq_true (Nat.min_le_right x y)
  | .fin _, .top => rfl
  | .top, b => le_refl b

theorem le_min {a b c : Bound} (hb : a ≤ b) (hc : a ≤ c) : a ≤ min b c :=
  match a, b, c with
  | _, .top, _ => by simpa using hc
  | _, .fin _, .top => hb
  | .top, .fin _, .fin _ => nomatch hb
  | .fin _, .fin _, .fin _ =>
      decide_eq_true (Nat.le_min.mpr ⟨of_decide_eq_true hb, of_decide_eq_true hc⟩)

/-- The finite embedding is monotone — the door-proof helper for
symbolic budgets: `(Bound.fin_le_fin (by omega))`. -/
theorem fin_le_fin {a b : Nat} (h : a ≤ b) : Bound.fin a ≤ Bound.fin b :=
  decide_eq_true h

theorem le_trans : {a b c : Bound} → a ≤ b → b ≤ c → a ≤ c
  | _, _, .top, _, _ => rfl
  | .top, .fin _, _, h, _ => nomatch h
  | _, .top, .fin _, _, h => nomatch h
  | .fin _, .fin _, .fin _, h, h' =>
      decide_eq_true (Nat.le_trans (of_decide_eq_true h) (of_decide_eq_true h'))

theorem mul_le_mul_left (k : Bound) : {a b : Bound} → a ≤ b → k * a ≤ k * b
  | .fin _, .top, _ => by cases k <;> exact rfl
  | .top, .top, _ => by cases k <;> exact rfl
  | .top, .fin _, h => nomatch h
  | .fin _, .fin _, h => by
      cases k with
      | top => exact rfl
      | fin kk => exact decide_eq_true (Nat.mul_le_mul_left kk (of_decide_eq_true h))
end Bound

/-- ⊤ — the unbounded `Bound`. -/
scoped notation "⊤" => Bound.top

/-- Nat expressions embed as finite bounds — `DbFetch c (n + 1) α` reads
as before. -/
instance : Coe Nat Bound := ⟨.fin⟩

end LeanLinq
