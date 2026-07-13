import LeanLinq.Core.Bound

/-! # `Grade` — round budgets, symbolic in table sizes

The round-trip currency of `DbFetch`, upgraded from ℕ∞ to **max-plus
polynomials over table names**: a grade is ⊤ or the maximum of a
canonical set of polynomials with `Nat` coefficients in symbols
`|customers|`, `|orders|`, …. Closed grades (`2`, `5 + 3`) are the
constant polynomials and compute exactly as `Bound` does; symbolic
grades price programs in the database's own terms — `|customers| + 1`
is "one round per customer, plus one".

**Canonical forms are the whole trick.** Every operation normalizes
(insertion-sorted monomials and poly-sets, combined coefficients), so
semantically-equal grades are *literally equal terms*:
`1 + 1 * X = X + 1` holds by `decide`, `(X + Y) + Z = X + (Y + Z)` by
`decide` — the graded monad's index bookkeeping needs no `ac_rfl`
gymnastics, because there is nothing left to rearrange. All sorting is
insertion-based (structural recursion), so the kernel reduces it and
`decide` stays available inside types.

The order is **semantic**: `a ≤ b` iff `a` evaluates under `b` at every
size valuation. Monotonicity lemmas are pointwise `Bound`/`Nat` facts —
free — and the doors discharge closed obligations through
`Grade.nat_le_nat` + `omega`. A symbolic grade at a closed door simply
fails to prove — the static refusal, exactly as ⊤ behaves.

`Bound` remains the **row** lattice (closed, matchable — `fetchLimit`,
`fetchBounded`, the refinements); `Grade` is the **round** lattice.
`ofBound` embeds rows into rounds where loops are priced (`forRows`). -/

namespace LeanLinq

/-- A monomial: the sorted multiset of table names it multiplies. -/
abbrev Mono := List String

namespace Grade

/-- Strict order on monomials (lex). -/
def monoLt (a b : Mono) : Bool :=
  match a, b with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => x < y || (x = y && monoLt xs ys)

/-- Insert a name into a sorted monomial (structural, kernel-reduces). -/
def insertName (x : String) : Mono → Mono
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertName x ys

/-- Monomial product: merge the sorted name multisets. -/
def monoMul (a b : Mono) : Mono := a.foldr insertName b

end Grade

/-- A polynomial with `Nat` coefficients over table-name monomials; the
monomial list sorted with combined coefficients (canonical). No zero
coefficients arise: the smart constructors never create them. -/
structure GPoly where
  const : Nat
  monos : List (Nat × Mono)
  deriving DecidableEq, Repr

namespace GPoly

/-- Insert one (coeff, mono) into a sorted-combined monomial list. -/
def insertM (c : Nat) (m : Mono) : List (Nat × Mono) → List (Nat × Mono)
  | [] => [(c, m)]
  | (c', m') :: rest =>
    if m = m' then (c + c', m') :: rest
    else if Grade.monoLt m m' then (c, m) :: (c', m') :: rest
    else (c', m') :: insertM c m rest

/-- Canonicalize a monomial list: sort and combine equal keys. -/
def normM (l : List (Nat × Mono)) : List (Nat × Mono) :=
  l.foldr (fun (c, m) acc => insertM c m acc) []

def add (p q : GPoly) : GPoly :=
  ⟨p.const + q.const, normM (p.monos ++ q.monos)⟩

def mul (p q : GPoly) : GPoly :=
  let cross := p.monos.flatMap fun (c, m) => q.monos.map fun (c', m') =>
    (c * c', Grade.monoMul m m')
  let scaleQ := q.monos.map fun (c, m) => (p.const * c, m)
  let scaleP := p.monos.map fun (c, m) => (q.const * c, m)
  ⟨p.const * q.const, normM (cross ++ scaleQ ++ scaleP)⟩

/-- A monomial's value: the product of its names' sizes. -/
def monoEval (σ : String → Nat) : Mono → Nat
  | [] => 1
  | x :: m => σ x * monoEval σ m

/-- A monomial list's value: Σ coeff × monomial. -/
def sumEval (σ : String → Nat) : List (Nat × Mono) → Nat
  | [] => 0
  | (c, m) :: l => c * monoEval σ m + sumEval σ l

/-- Evaluate against table sizes. -/
def eval (σ : String → Nat) (p : GPoly) : Nat :=
  p.const + sumEval σ p.monos

end GPoly

/-- A round grade: ⊤, or the **max** of a canonical set of polynomials
(max-plus semantics — `+`/`*` distribute over the set pairwise). -/
inductive Grade where
  | polys (ps : List GPoly)
  | top
  deriving DecidableEq, Repr

namespace Grade

/-- Total key order on polynomials, for the canonical set. -/
def polyLe (p q : GPoly) : Bool :=
  p.const < q.const ||
  (p.const = q.const && monosLe p.monos q.monos)
where
  monosLe : List (Nat × Mono) → List (Nat × Mono) → Bool
    | [], _ => true
    | _, [] => false
    | (c, m) :: xs, (c', m') :: ys =>
      if monoLt m m' then true
      else if monoLt m' m then false
      else if c < c' then true
      else if c' < c then false
      else monosLe xs ys

/-- Insertion into the sorted-dedup poly set (structural). -/
def insertPoly (p : GPoly) : List GPoly → List GPoly
  | [] => [p]
  | q :: qs =>
    if p = q then q :: qs
    else if polyLe p q then p :: q :: qs
    else q :: insertPoly p qs

/-- Canonicalize a poly set: sort, dedup. -/
def mkPolys (ps : List GPoly) : List GPoly :=
  ps.foldr insertPoly []

/-- A closed grade. -/
@[reducible] def nat (n : Nat) : Grade := .polys [⟨n, []⟩]

/-- The size of the named table, as a grade. -/
@[reducible] def tbl (x : String) : Grade := .polys [⟨0, [(1, [x])]⟩]

instance : OfNat Grade n := ⟨nat n⟩

/-- Nat expressions embed as closed grades — `DbFetch c (n + 1) α`
reads as before. -/
instance : Coe Nat Grade := ⟨nat⟩

/-- The row lattice embeds into the round lattice. -/
@[reducible] def ofBound : Bound → Grade
  | .fin n => nat n
  | .top => .top

def add : Grade → Grade → Grade
  | .top, _ => .top
  | _, .top => .top
  -- closed grades fold structurally — variable constants included, so a
  -- recursive definition's index (`Grade.nat n + 1`) reduces definitionally
  | .polys [⟨a, []⟩], .polys [⟨b, []⟩] => .polys [⟨a + b, []⟩]
  | .polys ps, .polys qs =>
      -- unit tests by `if`, so `g + 0` reduces even for abstract `g`
      if qs = [⟨0, []⟩] then .polys ps
      else if ps = [⟨0, []⟩] then .polys qs
      else .polys (mkPolys (ps.flatMap fun p => qs.map fun q => p.add q))

def mul : Grade → Grade → Grade
  | .top, _ => .top
  | _, .top => .top
  | .polys ps, .polys qs =>
      if qs = [⟨1, []⟩] then .polys ps
      else if ps = [⟨1, []⟩] then .polys qs
      else .polys (mkPolys (ps.flatMap fun p => qs.map fun q => p.mul q))

def gmax : Grade → Grade → Grade
  | .top, _ => .top
  | _, .top => .top
  | .polys ps, .polys qs => .polys (mkPolys (ps ++ qs))

instance : HasTop Grade := ⟨.top⟩
instance : Add Grade := ⟨add⟩
instance : Mul Grade := ⟨mul⟩
instance : Max Grade := ⟨gmax⟩

/-- Collapse against known sizes — the reading the model interpreter
has (`TableEnv.sizes`). -/
def evalB (σ : String → Nat) : Grade → Bound
  | .polys ps => .fin (ps.foldl (fun acc p => Nat.max acc (p.eval σ)) 0)
  | .top => .top

/-- Collapse against nothing: any symbol makes the grade ⊤ — recovering
the conservative closed reading (`card`'s ⊤ for bare sources). -/
def forget : Grade → Bound
  | .top => .top
  | .polys ps =>
      if ps.all fun p => p.monos.isEmpty then
        .fin (ps.foldl (fun acc p => Nat.max acc p.const) 0)
      else .top

/-- The order is semantic: dominated at **every** size valuation. Closed
comparisons discharge via `nat_le_nat` + `omega`; a symbolic grade at a
closed budget simply has no proof — the static refusal. -/
def Le (a b : Grade) : Prop := ∀ σ : String → Nat, a.evalB σ ≤ b.evalB σ

instance : LE Grade := ⟨Le⟩

theorem le_refl (a : Grade) : a ≤ a := fun _ => Bound.le_refl _

theorem le_trans {a b c : Grade} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  fun σ => Bound.le_trans (h₁ σ) (h₂ σ)

theorem le_top (a : Grade) : a ≤ .top := fun _ => Bound.le_top _

@[simp] theorem evalB_nat (σ : String → Nat) (n : Nat) :
    (nat n).evalB σ = .fin n := by
  simp [evalB, GPoly.eval, GPoly.sumEval, Nat.zero_max]

theorem nat_le_nat {a b : Nat} (h : a ≤ b) : nat a ≤ nat b := by
  intro σ
  simpa [evalB_nat] using Bound.fin_le_fin h

@[simp] theorem evalB_ofBound (σ : String → Nat) (b : Bound) :
    (ofBound b).evalB σ = b := by
  cases b <;> simp [ofBound, evalB, GPoly.eval, GPoly.sumEval, Nat.zero_max]

/-- Row evidence transports into round evidence. -/
theorem ofBound_le {a b : Bound} (h : a ≤ b) : ofBound a ≤ ofBound b := by
  intro σ
  simpa [evalB_ofBound] using h

/-- `.fin`-flavored evidence transports directly (the `forRows` shape). -/
theorem nat_le_ofBound {k : Nat} {b : Bound} (h : Bound.fin k ≤ b) :
    nat k ≤ ofBound b := by
  intro σ
  simpa [evalB_nat, evalB_ofBound] using h

/-- `g + 0 = g` — the `▸`-cast fuel for `DbFetch.map`, by shape cases
(the closed-fold arm splits the reduction paths). -/
theorem add_zero : (g : Grade) → g + (0 : Grade) = g
  | .top => rfl
  | .polys [] => rfl
  | .polys [⟨_, []⟩] => rfl
  | .polys [⟨_, _ :: _⟩] => rfl
  | .polys (⟨_, []⟩ :: _ :: _) => rfl
  | .polys (⟨_, _ :: _⟩ :: _ :: _) => rfl

theorem zero_add : (g : Grade) → (0 : Grade) + g = g
  | .top => rfl
  | .polys [] => rfl
  | .polys [⟨b, []⟩] => by
      show Grade.polys [⟨0 + b, []⟩] = _
      rw [Nat.zero_add]
  | .polys [⟨_, _ :: _⟩] => by
      simp [HAdd.hAdd, Add.add, Grade.add]
  | .polys (⟨_, []⟩ :: _ :: _) => by
      simp [HAdd.hAdd, Add.add, Grade.add]
  | .polys (⟨_, _ :: _⟩ :: _ :: _) => by
      simp [HAdd.hAdd, Add.add, Grade.add]

theorem mul_one : (g : Grade) → g * (1 : Grade) = g
  | .top => rfl
  | .polys _ => rfl

theorem one_mul (g : Grade) : (1 : Grade) * g = g := by
  cases g with
  | top => rfl
  | polys qs =>
      show Grade.mul (.polys [⟨1, []⟩]) (.polys qs) = .polys qs
      by_cases h : qs = [⟨1, []⟩] <;> simp [Grade.mul, h]

/-- Closed addition folds — definitionally, via the fold arm. -/
theorem nat_add (a b : Nat) : nat a + nat b = nat (a + b) := rfl

@[simp] theorem ofNat_eq_nat (n : Nat) :
    (no_index (OfNat.ofNat n) : Grade) = nat n := rfl

@[simp] theorem ofBound_fin (k : Nat) : ofBound (.fin k) = nat k := rfl

@[simp] theorem ofBound_top : ofBound .top = .top := rfl

/-- The unit laws, `nat`-spelled (what the goal looks like after
`ofNat_eq_nat` normalizes literals) — delegating: the spellings are
definitionally equal. -/
theorem mul_nat_one (g : Grade) : g * nat 1 = g := mul_one g

theorem nat_one_mul (g : Grade) : nat 1 * g = g := one_mul g

theorem add_nat_zero (g : Grade) : g + nat 0 = g := add_zero g

theorem nat_zero_add (g : Grade) : nat 0 + g = g := zero_add g

/-- Closed-plus-embedded commutation, by cases on the row bound — the
`fetch!` ladder's bridge for `(n : Bound)`-parametric grades. -/
theorem nat_add_ofBound (a : Nat) (n : Bound) :
    nat a + ofBound n = ofBound n + nat a := by
  cases n with
  | top => rfl
  | fin k => rw [ofBound, nat_add, nat_add, Nat.add_comm]

theorem nat_mul (a b : Nat) : nat a * nat b = nat (a * b) := by
  show Grade.mul _ _ = _
  by_cases hb : b = 1
  · subst hb; simp [Grade.mul, nat]
  · by_cases ha : a = 1
    · subst ha
      simp [Grade.mul, nat,
        show ¬([⟨b, []⟩] = ([⟨1, []⟩] : List GPoly)) by simpa using hb,
        Nat.one_mul]
    · simp [Grade.mul, nat,
        show ¬([⟨b, []⟩] = ([⟨1, []⟩] : List GPoly)) by simpa using hb,
        show ¬([⟨a, []⟩] = ([⟨1, []⟩] : List GPoly)) by simpa using ha,
        GPoly.mul, GPoly.normM, GPoly.insertM, mkPolys, insertPoly]

/-! ## The evaluation homomorphism — `mul_le_mul_left`'s ledger

`bindD` + subtype proofs is the composition story, and the loop's
evidence transports through multiplication: `k * nat len ≤ k * ofBound n`
from the refinement. Monotonicity of `*` under the semantic order needs
evaluation to commute with the smart multiplication — through `normM`,
`mkPolys`, and the pairwise max-set product. Proved bottom-up. -/

section EvalHom

variable (σ : String → Nat)

theorem monoEval_insertName (x : String) (m : Mono) :
    GPoly.monoEval σ (insertName x m) = σ x * GPoly.monoEval σ m := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
      rw [insertName]
      split
      · rfl
      · rw [GPoly.monoEval, ih, GPoly.monoEval,
          Nat.mul_left_comm]

theorem monoEval_monoMul (a b : Mono) :
    GPoly.monoEval σ (monoMul a b) = GPoly.monoEval σ a * GPoly.monoEval σ b := by
  induction a with
  | nil => rw [monoMul, List.foldr_nil, GPoly.monoEval, Nat.one_mul]
  | cons x xs ih =>
      show GPoly.monoEval σ (insertName x (monoMul xs b)) = _
      rw [monoEval_insertName, ih, GPoly.monoEval, Nat.mul_assoc]

theorem sumEval_insertM (c : Nat) (m : Mono) (l : List (Nat × Mono)) :
    GPoly.sumEval σ (GPoly.insertM c m l) =
      c * GPoly.monoEval σ m + GPoly.sumEval σ l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨c', m'⟩ := hd
      rw [GPoly.insertM]
      split
      · next h =>
          subst h
          rw [GPoly.sumEval, GPoly.sumEval, Nat.add_mul]
          omega
      · split
        · rfl
        · rw [GPoly.sumEval, ih, GPoly.sumEval]
          omega

theorem sumEval_normM (l : List (Nat × Mono)) :
    GPoly.sumEval σ (GPoly.normM l) = GPoly.sumEval σ l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨c, m⟩ := hd
      show GPoly.sumEval σ (GPoly.insertM c m (GPoly.normM tl)) = _
      rw [sumEval_insertM, ih, GPoly.sumEval]

theorem sumEval_append (l₁ l₂ : List (Nat × Mono)) :
    GPoly.sumEval σ (l₁ ++ l₂) = GPoly.sumEval σ l₁ + GPoly.sumEval σ l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, GPoly.sumEval, Nat.zero_add]
  | cons hd tl ih =>
      obtain ⟨c, m⟩ := hd
      rw [List.cons_append, GPoly.sumEval, GPoly.sumEval, ih, Nat.add_assoc]

theorem sumEval_scale (k : Nat) (l : List (Nat × Mono)) :
    GPoly.sumEval σ (l.map fun (c, m) => (k * c, m)) = k * GPoly.sumEval σ l := by
  induction l with
  | nil => simp [GPoly.sumEval]
  | cons hd tl ih =>
      obtain ⟨c, m⟩ := hd
      simp only [List.map_cons, GPoly.sumEval, ih, Nat.mul_add, Nat.mul_assoc]

theorem sumEval_row (c : Nat) (m : Mono) (l : List (Nat × Mono)) :
    GPoly.sumEval σ (l.map fun (c', m') => (c * c', monoMul m m')) =
      (c * GPoly.monoEval σ m) * GPoly.sumEval σ l := by
  induction l with
  | nil => simp [GPoly.sumEval]
  | cons hd tl ih =>
      obtain ⟨c', m'⟩ := hd
      simp only [List.map_cons, GPoly.sumEval, ih, monoEval_monoMul]
      rw [Nat.mul_add]
      congr 1
      rw [Nat.mul_mul_mul_comm]

theorem sumEval_cross (ps qs : List (Nat × Mono)) :
    GPoly.sumEval σ (ps.flatMap fun (c, m) => qs.map fun (c', m') =>
      (c * c', monoMul m m')) = GPoly.sumEval σ ps * GPoly.sumEval σ qs := by
  induction ps with
  | nil => simp [GPoly.sumEval]
  | cons hd tl ih =>
      obtain ⟨c, m⟩ := hd
      rw [List.flatMap_cons, sumEval_append, ih, sumEval_row, GPoly.sumEval,
        Nat.add_mul]

theorem eval_mul (p q : GPoly) :
    (p.mul q).eval σ = p.eval σ * q.eval σ := by
  rw [GPoly.mul, GPoly.eval, GPoly.eval, GPoly.eval]
  simp only
  rw [sumEval_normM, sumEval_append, sumEval_append, sumEval_cross,
    sumEval_scale, sumEval_scale, Nat.add_mul, Nat.mul_add, Nat.mul_add,
    Nat.mul_comm (GPoly.sumEval σ p.monos) q.const]
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The max of a poly set's values (foldr form for induction). -/
def maxE (σ : String → Nat) : List GPoly → Nat
  | [] => 0
  | p :: ps => Nat.max (p.eval σ) (maxE σ ps)

theorem foldl_maxE (ps : List GPoly) (i : Nat) :
    ps.foldl (fun acc p => Nat.max acc (p.eval σ)) i = Nat.max i (maxE σ ps) := by
  induction ps generalizing i with
  | nil => simp [maxE]
  | cons p ps ih =>
      rw [List.foldl_cons, ih, maxE]
      exact Nat.max_assoc ..

theorem evalB_polys (ps : List GPoly) :
    (Grade.polys ps).evalB σ = .fin (maxE σ ps) := by
  rw [evalB, foldl_maxE]
  simp

theorem maxE_insertPoly (p : GPoly) (l : List GPoly) :
    maxE σ (insertPoly p l) = Nat.max (p.eval σ) (maxE σ l) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
      rw [insertPoly]
      split
      · next h =>
          subst h
          rw [maxE]
          exact ((Nat.max_assoc ..).symm.trans
            (congrArg (Nat.max · _) (Nat.max_self _))).symm
      · split
        · rfl
        · rw [maxE, ih, maxE]
          exact (Nat.max_left_comm ..).symm

theorem maxE_mkPolys (l : List GPoly) :
    maxE σ (mkPolys l) = maxE σ l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      show maxE σ (insertPoly p (mkPolys ps)) = _
      rw [maxE_insertPoly, ih, maxE]

theorem maxE_append (l₁ l₂ : List GPoly) :
    maxE σ (l₁ ++ l₂) = Nat.max (maxE σ l₁) (maxE σ l₂) := by
  induction l₁ with
  | nil => simp [maxE]
  | cons p ps ih =>
      rw [List.cons_append, maxE, ih, maxE]
      exact (Nat.max_assoc ..).symm

theorem nat_mul_max (a b c : Nat) : a * Nat.max b c = Nat.max (a * b) (a * c) := by
  rcases Nat.le_total b c with h | h
  · simp [Nat.max_eq_right h, Nat.max_eq_right (Nat.mul_le_mul_left a h)]
  · simp [Nat.max_eq_left h, Nat.max_eq_left (Nat.mul_le_mul_left a h)]

theorem nat_max_mul (a b c : Nat) : Nat.max a b * c = Nat.max (a * c) (b * c) := by
  rw [Nat.mul_comm, nat_mul_max, Nat.mul_comm c a, Nat.mul_comm c b]

theorem maxE_row (p : GPoly) (qs : List GPoly) :
    maxE σ (qs.map fun q => p.mul q) = p.eval σ * maxE σ qs := by
  induction qs with
  | nil => simp [maxE]
  | cons q qs ih =>
      rw [List.map_cons, maxE, ih, eval_mul, maxE, nat_mul_max]

theorem maxE_cross (ps qs : List GPoly) :
    maxE σ (ps.flatMap fun p => qs.map fun q => p.mul q) =
      maxE σ ps * maxE σ qs := by
  induction ps with
  | nil => simp [maxE]
  | cons p ps ih =>
      rw [List.flatMap_cons, maxE_append, ih, maxE_row, maxE, nat_max_mul]

theorem evalB_mul_polys (ps qs : List GPoly) :
    (Grade.mul (.polys ps) (.polys qs)).evalB σ =
      .fin (maxE σ ps * maxE σ qs) := by
  show (if qs = [⟨1, []⟩] then Grade.polys ps
    else if ps = [⟨1, []⟩] then Grade.polys qs
    else Grade.polys (mkPolys (ps.flatMap fun p =>
      qs.map fun q => p.mul q))).evalB σ = _
  split
  · next h =>
      subst h
      rw [evalB_polys]
      simp [maxE, GPoly.eval, GPoly.sumEval]
  · split
    · next hps =>
        rw [hps, evalB_polys]
        simp [maxE, GPoly.eval, GPoly.sumEval]
    · rw [evalB_polys, maxE_mkPolys, maxE_cross]

/-- Evaluation commutes with the smart multiplication. -/
theorem evalB_mul : (a b : Grade) → (a * b).evalB σ = a.evalB σ * b.evalB σ
  | .top, .top => rfl
  | .top, .polys _ => rfl
  | .polys ps, .top => by
      show Grade.top.evalB σ = (Grade.polys ps).evalB σ * Bound.top
      rw [evalB_polys]
      rfl
  | .polys ps, .polys qs => by
      show (Grade.mul (.polys ps) (.polys qs)).evalB σ = _
      rw [evalB_mul_polys, evalB_polys, evalB_polys]
      rfl

/-- Multiplication is monotone under the semantic order — the transport
`bindD`'s subtype evidence rides through (`k * nat len ≤ k * ofBound n`
from the refinement's `fin len ≤ n`). -/
theorem mul_le_mul_left (k : Grade) {a b : Grade} (h : a ≤ b) :
    k * a ≤ k * b := by
  intro σ
  rw [evalB_mul, evalB_mul]
  exact Bound.mul_le_mul_left _ (h σ)

end EvalHom

end Grade

end LeanLinq
