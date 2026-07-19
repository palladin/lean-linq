import LeanLinq.Eval.Query

/-! # Theorems about the executable semantics

Queries are total, deeply-embedded values with a denotational semantics
(`Query.run`), so facts about result sets are *theorems*, not conventions.
This file is the home of that (deliberately small, demand-driven) corpus.

Every fetch door that refines its rows runs a decidable check whose
adequacy is a theorem here — the checks are provably the identity in
the reference semantics, auditing only live engines:

- `run_limit_length_le` — `LIMIT n` really limits (`fetchLimit`);
- `run_gcard` — evaluation never returns more rows than the query's
  symbolic bound, collapsed at the environment's own sizes. This is
  `fetch`'s contract as a theorem about the reference semantics: the
  name↔instance coherence it needs is the `HasTable.rows_sizes` law,
  so it carries no hypotheses. -/

namespace LeanLinq

/-- Evaluating any query under a `.limitC _ (some n) _` head yields at most
`n` rows: the evaluator's limit arm is `(rows.drop off).take n`. -/
theorem Query.evalRows_limitC_length_le {ts : Ctx} {s : Schema}
    (q : QueryA ts s) (n : Nat) (off? : Option Nat) (ee : EvalEnv ts)
    {rows : List (Values s)}
    (h : (QueryP.limitC q (some n) off?).evalRowsIn ee [] = .ok rows) :
    rows.length ≤ n := by
  rw [QueryP.evalRowsIn.eq_def] at h
  simp only at h
  cases hq : q.evalRowsIn ee [] with
  | error e =>
      rw [hq] at h
      simp [Bind.bind, Except.bind] at h
  | ok inner =>
      rw [hq] at h
      simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact List.length_take_le n _

/-- `q.limit n` returns at most `n` rows — `LIMIT` really limits, in the
executable semantics. The proof only needs that `Query.limit` always
produces a `.limitC _ (some n) _` head (merging a pending offset or
wrapping an already-limited query as a derived table). -/
theorem Query.run_limit_length_le {ts : Ctx} {s : Schema}
    (q : Query ts s) (n : Nat) (env : TableEnv ts.tables)
    (ps : ParamEnv ts.params) (now : Option String)
    {rows : List (Values s)}
    (h : (q.limit n).run env ps now = .ok rows) :
    rows.length ≤ n := by
  unfold Query.run Query.evalRows at h
  unfold QueryB.limit QueryP.limit at h
  split at h
  · exact Query.evalRows_limitC_length_le _ n _ _ h
  · unfold QueryP.limitOffset at h
    split at h
    · exact Query.evalRows_limitC_length_le _ n _ _ h
    · exact Query.evalRows_limitC_length_le _ n _ _ h


/-! ## Soundness of `gcard`

The compute-from-the-value symbolic bound never underestimates the
reference semantics: whatever `evalRows` produces fits under `gcard`
evaluated at the run's own table sizes. The induction mirrors the
evaluator's downward walk; every *source* arm cashes the
`HasTable.rows_sizes` law (the instance reads at most as many rows as
the size valuation prices for its name), and the alias-counter
invariant `hn` aligns `gcard`'s marker instantiation with the
evaluator's, so the `fromQ`/loop cases compare the same continuation
application on both sides. -/

/-- `filterAuxM` over `Except`: the accumulator grows only by input
elements, one at a time. -/
theorem List.filterAuxM_except_sub {ε : Type _} {p : α → Except ε Bool} :
    (l acc : List α) → {ys : List α} → List.filterAuxM p l acc = .ok ys →
    ys.length ≤ l.length + acc.length ∧ ∀ y ∈ ys, y ∈ l ∨ y ∈ acc
  | [], acc, ys, h => by
      simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨by omega, fun y hy => .inr hy⟩
  | a :: l, acc, ys, h => by
      rw [List.filterAuxM] at h
      obtain ⟨b, _, h⟩ := Except.bind_ok h
      obtain ⟨hlen, hmem⟩ := List.filterAuxM_except_sub l (cond b (a :: acc) acc) h
      constructor
      · cases b <;> simp only [cond] at hlen <;> simp only [List.length_cons] at * <;> omega
      · intro y hy
        rcases hmem y hy with h1 | h2
        · exact .inl (List.mem_cons_of_mem _ h1)
        · cases b with
          | true =>
              rcases List.mem_cons.mp h2 with rfl | h3
              · exact .inl (List.mem_cons_self ..)
              · exact .inr h3
          | false => exact .inr h2

theorem List.length_filterM_except_le {ε : Type _} {p : α → Except ε Bool}
    {l ys : List α} (h : l.filterM p = .ok ys) : ys.length ≤ l.length := by
  rw [List.filterM] at h
  obtain ⟨zs, hz, h⟩ := Except.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simpa using (List.filterAuxM_except_sub l [] hz).1

theorem List.mem_of_filterM_except {ε : Type _} {p : α → Except ε Bool}
    {l ys : List α} (h : l.filterM p = .ok ys) : ∀ y ∈ ys, y ∈ l := by
  rw [List.filterM] at h
  obtain ⟨zs, hz, h⟩ := Except.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro y hy
  rcases (List.filterAuxM_except_sub l [] hz).2 y (List.mem_reverse.mp hy) with h1 | h2
  · exact h1
  · cases h2

/-- A `mapM` whose per-element action returns `Option`, `filterMap id`-ed:
the survivors are among the inputs. -/
theorem List.filterMap_mapM_except_mem {ε : Type _} {f : α → Except ε (Option α)}
    {l : List α} {ys : List (Option α)} (h : l.mapM f = .ok ys)
    (hf : ∀ x y, f x = .ok (some y) → y = x) :
    ∀ y ∈ ys.filterMap id, y ∈ l := by
  intro y hy
  obtain ⟨o, ho, hoy⟩ := List.mem_filterMap.mp hy
  obtain ⟨x, hx, hfx⟩ := List.mem_of_mapM_except _ h o ho
  cases o with
  | none => cases hoy
  | some z =>
      cases hoy
      exact (hf x y hfx) ▸ hx

theorem List.length_filterMap_mapM_except_le {ε : Type _}
    {f : α → Except ε (Option α)} {l : List α} {ys : List (Option α)}
    (h : l.mapM f = .ok ys) : (ys.filterMap id).length ≤ l.length := by
  calc (ys.filterMap id).length
      ≤ ys.length := List.length_filterMap_le _ _
    _ = l.length := List.length_mapM_except _ h

/-- A `flatMap` of uniformly bounded images is bounded by
count × bound. -/
theorem List.length_flatMap_le {K : Nat} {f : α → List β} :
    (l : List α) → (h : ∀ a ∈ l, (f a).length ≤ K) →
    (l.flatMap f).length ≤ l.length * K
  | [], _ => by simp
  | a :: l, h => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.succ_mul]
      have ht := List.length_flatMap_le l (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have ha := h a (List.mem_cons_self ..)
      omega

mutual

/-- Result counts of the downward walk are bounded by
`#incoming-scopes × gcard`, at the environment's own sizes. The `hn`
invariant — the alias counter equals every incoming scope's length —
aligns the bound's marker instantiation with the evaluator's. Source
arms cash `HasTable.rows_sizes`. -/
theorem SpineQP.evalScopes_gcard_le {ts : Ctx} {g : Terminal} {s : Schema}
    {ee : EvalEnv ts} : (sp : SpineQ ts g s) → {n : Nat} → {scopes : List Scope} →
    {rs : List (List Scope × Values s)} →
    (hn : ∀ sc ∈ scopes, n = sc.length) →
    sp.evalScopes ee n scopes = .ok rs →
    rs.length ≤ scopes.length * (sp.gcardAux n).eval (TableEnv.sizes ee.tables)
  | .yield r, n, scopes, rs, _, h => by
      rw [show ((SpineQP.yield r).gcardAux n) = Grade.nat 1 from rfl,
        Grade.eval_nat, Nat.mul_one]
      exact Nat.le_of_eq (List.length_mapM_except _ h)
  | .groupYield ks hv ord r, n, scopes, rs, _, h => by
      rw [show ((SpineQP.groupYield ks hv ord r).gcardAux n) = Grade.nat 1 from rfl,
        Grade.eval_nat, Nat.mul_one]
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨keyed, hk, h⟩ := Except.bind_ok h
      obtain ⟨tagged?, ht, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      calc (sortTagged (tagged?.filterMap id)).length
          = (tagged?.filterMap id).length := sortTagged_length _
        _ ≤ tagged?.length := List.length_filterMap_le _ _
        _ = _ := List.length_mapM_except _ ht
        _ ≤ 0 + keyed.length := foldl_insertGrouped_length_le _ _
        _ = keyed.length := Nat.zero_add _
        _ = scopes.length := List.length_mapM_except _ hk
  | .guard b rest, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨survivors, hs, h⟩ := Except.bind_ok h
      refine Nat.le_trans (SpineQP.evalScopes_gcard_le rest ?_ h) ?_
      · intro sc' hsc'
        refine hn sc' (List.filterMap_mapM_except_mem hs ?_ sc' hsc')
        intro x y hfx
        obtain ⟨bv, _, hfx⟩ := Except.bind_ok hfx
        simp only [pure, Except.pure, Except.ok.injEq] at hfx
        split at hfx
        · exact (Option.some.injEq ..).mp hfx |>.symm
        · cases hfx
      · rw [show ((SpineQP.guard b rest).gcardAux n) = rest.gcardAux n from rfl]
        exact Nat.mul_le_mul_right _ (List.length_filterMap_mapM_except_le hs)
  | .order ks rest, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨rs', hr, h⟩ := Except.bind_ok h
      obtain ⟨tagged, ht, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have : (sortTagged tagged).length = rs'.length := by
        rw [sortTagged_length, List.length_mapM_except _ ht]
      rw [show ((SpineQP.order ks rest).gcardAux n) = rest.gcardAux n from rfl]
      exact this ▸ SpineQP.evalScopes_gcard_le rest hn hr
  | .fromT (s := s₀) (n := nm) (inst := i) _ f, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      have hext : ∀ sc' ∈ (scopes.flatMap fun sc =>
          (i.rows ee.tables).map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc),
          n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨sc, hsc, hmem⟩ := List.mem_flatMap.mp hsc'
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hmem
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.evalScopes_gcard_le (f ⟨s!"a{n}"⟩) hext h
      have hexts : (scopes.flatMap fun sc =>
          (i.rows ee.tables).map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc).length
            ≤ scopes.length * TableEnv.sizes ee.tables nm :=
        List.length_flatMap_le scopes (fun sc _ =>
          Nat.le_trans (Nat.le_of_eq (List.length_map ..)) (i.rows_sizes ee.tables))
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * TableEnv.sizes ee.tables nm) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hexts
        _ = scopes.length *
              ((SpineQP.fromT (inst := i) _ f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.fromT (inst := i) _ f).gcardAux n) =
              Grade.tbl nm * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Grade.eval_tbl, Nat.mul_assoc]
  | .joinT (s := s₀) (n := nm) (inst := i) _ on' f, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨hits, hh, h⟩ := Except.bind_ok h
      have hmemE := List.mem_of_filterM_except hh
      have hext : ∀ sc' ∈ hits, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨sc, hsc, hmem⟩ := List.mem_flatMap.mp (hmemE sc' hsc')
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hmem
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.evalScopes_gcard_le (f ⟨s!"a{n}"⟩) hext h
      have hhits : hits.length ≤ scopes.length * TableEnv.sizes ee.tables nm :=
        Nat.le_trans (List.length_filterM_except_le hh)
          (List.length_flatMap_le scopes (fun sc _ =>
            Nat.le_trans (Nat.le_of_eq (List.length_map ..)) (i.rows_sizes ee.tables)))
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * TableEnv.sizes ee.tables nm) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hhits
        _ = scopes.length *
              ((SpineQP.joinT (inst := i) _ on' f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.joinT (inst := i) _ on' f).gcardAux n) =
              Grade.tbl nm * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Grade.eval_tbl, Nat.mul_assoc]
  | .joinLeftT (s := s₀) (n := nm) (inst := i) _ on' f, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      have hpart : ∀ part ∈ parts,
          part.length ≤ TableEnv.sizes ee.tables nm + 1 := by
        intro part hp
        obtain ⟨sc, _, hev⟩ := List.mem_of_mapM_except _ hm part hp
        obtain ⟨hits, hh, hev⟩ := Except.bind_ok hev
        have hR : hits.length ≤ TableEnv.sizes ee.tables nm :=
          Nat.le_trans (List.length_filterM_except_le hh) (i.rows_sizes ee.tables)
        split at hev
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          simp only [List.length_cons, List.length_nil]
          omega
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          rw [List.length_map]
          exact Nat.le_succ_of_le hR
      have hext : ∀ sc' ∈ parts.flatten, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨part, hp, hin⟩ := List.mem_flatten.mp hsc'
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hp
        obtain ⟨hits, _, hev⟩ := Except.bind_ok hev
        split at hev
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          rw [List.mem_singleton] at hin
          subst hin
          simpa using congrArg Nat.succ (hn sc hsc)
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hin
          simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.evalScopes_gcard_le (f ⟨s!"a{n}"⟩) hext h
      have hflat : parts.flatten.length ≤
          scopes.length * (TableEnv.sizes ee.tables nm + 1) :=
        List.length_mapM_except _ hm ▸ List.length_flatten_le parts hpart
      have htop : TableEnv.sizes ee.tables nm + 1 ≤
          (Grade.tbl nm + 1).eval (TableEnv.sizes ee.tables) := by
        simp [Grade.eval_add]
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * ((Grade.tbl nm + 1).eval (TableEnv.sizes ee.tables))) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ (Nat.le_trans hflat
              (Nat.mul_le_mul_left _ htop))
        _ = scopes.length *
              ((SpineQP.joinLeftT (inst := i) _ on' f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.joinLeftT (inst := i) _ on' f).gcardAux n) =
              (Grade.tbl nm + 1) * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Nat.mul_assoc]
  | .fromQ (s := s₀) q f, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      have hpart : ∀ part ∈ parts,
          part.length ≤ (q.gcardAux n).eval (TableEnv.sizes ee.tables) := by
        intro part hp
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hp
        obtain ⟨rows, hq, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        rw [List.length_map]
        exact hn sc hsc ▸ QueryP.evalRowsIn_gcard_le q hq
      have hext : ∀ sc' ∈ parts.flatten, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨part, hp, hin⟩ := List.mem_flatten.mp hsc'
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hp
        obtain ⟨rows, _, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hin
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.evalScopes_gcard_le (f ⟨s!"a{n}"⟩) hext h
      have hflat : parts.flatten.length ≤
          scopes.length * (q.gcardAux n).eval (TableEnv.sizes ee.tables) :=
        List.length_mapM_except _ hm ▸ List.length_flatten_le parts hpart
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * (q.gcardAux n).eval (TableEnv.sizes ee.tables)) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hflat
        _ = scopes.length *
              ((SpineQP.fromQ q f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.fromQ q f).gcardAux n) =
              q.gcardAux n * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Nat.mul_assoc]

/-- The count walk (`enumScopes`) is bounded the same way — the third
member of the induction, arm-for-arm the row walk minus terminal work. -/
theorem SpineQP.enumScopes_gcard_le {ts : Ctx} {g : Terminal} {s : Schema}
    {ee : EvalEnv ts} : (sp : SpineQ ts g s) → {n : Nat} → {scopes : List Scope} →
    {rs : List Scope} → (hp : g = .plain) →
    (hn : ∀ sc ∈ scopes, n = sc.length) →
    sp.enumScopes ee n scopes hp = .ok rs →
    rs.length ≤ scopes.length * (sp.gcardAux n).eval (TableEnv.sizes ee.tables)
  | .yield r, n, scopes, rs, _, _, h => by
      rw [show ((SpineQP.yield r).gcardAux n) = Grade.nat 1 from rfl,
        Grade.eval_nat, Nat.mul_one]
      simp only [SpineQP.enumScopes, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
  | .groupYield .., _, _, _, hp, _, _ => nomatch hp
  | .guard b rest, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      obtain ⟨survivors, hs, h⟩ := Except.bind_ok h
      refine Nat.le_trans (SpineQP.enumScopes_gcard_le rest hp ?_ h) ?_
      · intro sc' hsc'
        refine hn sc' (List.filterMap_mapM_except_mem hs ?_ sc' hsc')
        intro x y hfx
        obtain ⟨bv, _, hfx⟩ := Except.bind_ok hfx
        simp only [pure, Except.pure, Except.ok.injEq] at hfx
        split at hfx
        · exact (Option.some.injEq ..).mp hfx |>.symm
        · cases hfx
      · rw [show ((SpineQP.guard b rest).gcardAux n) = rest.gcardAux n from rfl]
        exact Nat.mul_le_mul_right _ (List.length_filterMap_mapM_except_le hs)
  | .order ks rest, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      rw [show ((SpineQP.order ks rest).gcardAux n) = rest.gcardAux n from rfl]
      exact SpineQP.enumScopes_gcard_le rest hp hn h
  | .fromT (s := s₀) (n := nm) (inst := i) _ f, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      have hext : ∀ sc' ∈ (scopes.flatMap fun sc =>
          (i.rows ee.tables).map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc),
          n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨sc, hsc, hmem⟩ := List.mem_flatMap.mp hsc'
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hmem
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.enumScopes_gcard_le (f ⟨s!"a{n}"⟩) hp hext h
      have hexts : (scopes.flatMap fun sc =>
          (i.rows ee.tables).map fun v => (s!"a{n}", ⟨s₀, v⟩) :: sc).length
            ≤ scopes.length * TableEnv.sizes ee.tables nm :=
        List.length_flatMap_le scopes (fun sc _ =>
          Nat.le_trans (Nat.le_of_eq (List.length_map ..)) (i.rows_sizes ee.tables))
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * TableEnv.sizes ee.tables nm) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hexts
        _ = scopes.length *
              ((SpineQP.fromT (inst := i) _ f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.fromT (inst := i) _ f).gcardAux n) =
              Grade.tbl nm * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Grade.eval_tbl, Nat.mul_assoc]
  | .joinT (s := s₀) (n := nm) (inst := i) _ on' f, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      obtain ⟨hits, hh, h⟩ := Except.bind_ok h
      have hmemE := List.mem_of_filterM_except hh
      have hext : ∀ sc' ∈ hits, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨sc, hsc, hmem⟩ := List.mem_flatMap.mp (hmemE sc' hsc')
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hmem
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.enumScopes_gcard_le (f ⟨s!"a{n}"⟩) hp hext h
      have hhits : hits.length ≤ scopes.length * TableEnv.sizes ee.tables nm :=
        Nat.le_trans (List.length_filterM_except_le hh)
          (List.length_flatMap_le scopes (fun sc _ =>
            Nat.le_trans (Nat.le_of_eq (List.length_map ..)) (i.rows_sizes ee.tables)))
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * TableEnv.sizes ee.tables nm) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hhits
        _ = scopes.length *
              ((SpineQP.joinT (inst := i) _ on' f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.joinT (inst := i) _ on' f).gcardAux n) =
              Grade.tbl nm * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Grade.eval_tbl, Nat.mul_assoc]
  | .joinLeftT (s := s₀) (n := nm) (inst := i) _ on' f, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      have hpart : ∀ part ∈ parts,
          part.length ≤ TableEnv.sizes ee.tables nm + 1 := by
        intro part hpm
        obtain ⟨sc, _, hev⟩ := List.mem_of_mapM_except _ hm part hpm
        obtain ⟨hits, hh, hev⟩ := Except.bind_ok hev
        have hR : hits.length ≤ TableEnv.sizes ee.tables nm :=
          Nat.le_trans (List.length_filterM_except_le hh) (i.rows_sizes ee.tables)
        split at hev
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          simp only [List.length_cons, List.length_nil]
          omega
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          rw [List.length_map]
          exact Nat.le_succ_of_le hR
      have hext : ∀ sc' ∈ parts.flatten, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨part, hpm, hin⟩ := List.mem_flatten.mp hsc'
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hpm
        obtain ⟨hits, _, hev⟩ := Except.bind_ok hev
        split at hev
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          rw [List.mem_singleton] at hin
          subst hin
          simpa using congrArg Nat.succ (hn sc hsc)
        · simp only [pure, Except.pure, Except.ok.injEq] at hev
          subst hev
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hin
          simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.enumScopes_gcard_le (f ⟨s!"a{n}"⟩) hp hext h
      have hflat : parts.flatten.length ≤
          scopes.length * (TableEnv.sizes ee.tables nm + 1) :=
        List.length_mapM_except _ hm ▸ List.length_flatten_le parts hpart
      have htop : TableEnv.sizes ee.tables nm + 1 ≤
          (Grade.tbl nm + 1).eval (TableEnv.sizes ee.tables) := by
        simp [Grade.eval_add]
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * ((Grade.tbl nm + 1).eval (TableEnv.sizes ee.tables))) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ (Nat.le_trans hflat
              (Nat.mul_le_mul_left _ htop))
        _ = scopes.length *
              ((SpineQP.joinLeftT (inst := i) _ on' f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.joinLeftT (inst := i) _ on' f).gcardAux n) =
              (Grade.tbl nm + 1) * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Nat.mul_assoc]
  | .fromQ (s := s₀) q f, n, scopes, rs, hp, hn, h => by
      rw [SpineQP.enumScopes.eq_def] at h
      simp only at h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      have hpart : ∀ part ∈ parts,
          part.length ≤ (q.gcardAux n).eval (TableEnv.sizes ee.tables) := by
        intro part hpm
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hpm
        obtain ⟨rows, hq, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        rw [List.length_map]
        exact hn sc hsc ▸ QueryP.evalRowsIn_gcard_le q hq
      have hext : ∀ sc' ∈ parts.flatten, n + 1 = sc'.length := by
        intro sc' hsc'
        obtain ⟨part, hpm, hin⟩ := List.mem_flatten.mp hsc'
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hpm
        obtain ⟨rows, _, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hin
        simpa using congrArg Nat.succ (hn sc hsc)
      have hbelow := SpineQP.enumScopes_gcard_le (f ⟨s!"a{n}"⟩) hp hext h
      have hflat : parts.flatten.length ≤
          scopes.length * (q.gcardAux n).eval (TableEnv.sizes ee.tables) :=
        List.length_mapM_except _ hm ▸ List.length_flatten_le parts hpart
      calc rs.length
          ≤ _ * ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            hbelow
        _ ≤ (scopes.length * (q.gcardAux n).eval (TableEnv.sizes ee.tables)) *
              ((f ⟨s!"a{n}"⟩).gcardAux (n + 1)).eval (TableEnv.sizes ee.tables) :=
            Nat.mul_le_mul_right _ hflat
        _ = scopes.length *
              ((SpineQP.fromQ q f).gcardAux n).eval (TableEnv.sizes ee.tables) := by
            rw [show ((SpineQP.fromQ q f).gcardAux n) =
              q.gcardAux n * (f ⟨s!"a{n}"⟩).gcardAux (n + 1) from rfl,
              Grade.eval_mul, Nat.mul_assoc]

theorem QueryP.evalRowsIn_gcard_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : QueryA ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs →
    xs.length ≤ (q.gcardAux sc.length).eval (TableEnv.sizes ee.tables)
  | .spine sp, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨rs, hsp, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have := SpineQP.evalScopes_gcard_le sp
        (scopes := [sc]) (fun x hx => by cases hx with
          | head => rfl
          | tail _ hx => cases hx) hsp
      rw [List.length_map]
      simpa [Nat.one_mul] using this
  | .distinctC q, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Nat.le_trans (List.length_dedupBy_le _ _)
        (QueryP.evalRowsIn_gcard_le q hq)
  | .limitC q lim? off?, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      have hin := QueryP.evalRowsIn_gcard_le q hq
      cases lim? with
      | some l =>
          subst h
          have htake : ((inner.drop (off?.getD 0)).take l).length ≤ l :=
            List.length_take_le ..
          have hinner : ((inner.drop (off?.getD 0)).take l).length ≤ inner.length :=
            Nat.le_trans (List.take_sublist ..).length_le
              (List.drop_sublist ..).length_le
          simp only [QueryP.gcardAux, Grade.eval_min, Grade.eval_nat]
          exact Nat.le_min.mpr ⟨by omega, htake⟩
      | none =>
          subst h
          exact Nat.le_trans (List.drop_sublist ..).length_le hin
  | .setOpC op a b, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨ra, hra, h⟩ := Except.bind_ok h
      obtain ⟨rb, hrb, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      cases op with
      | union =>
          subst h
          refine Nat.le_trans ?_ (Grade.le_eval_add (TableEnv.sizes ee.tables))
          calc (List.dedupBy Values.beq (ra ++ rb)).length
              ≤ (ra ++ rb).length := List.length_dedupBy_le _ _
            _ = ra.length + rb.length := List.length_append
            _ ≤ _ := Nat.add_le_add (QueryP.evalRowsIn_gcard_le a hra)
                (QueryP.evalRowsIn_gcard_le b hrb)
      | intersect =>
          subst h
          refine Nat.le_trans ?_ (QueryP.evalRowsIn_gcard_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _
      | except =>
          subst h
          refine Nat.le_trans ?_ (QueryP.evalRowsIn_gcard_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _

end

/-- **`gcard` is sound**: evaluation never returns more rows than the
query's symbolic bound, collapsed at the environment's own table sizes.
`fetch`'s contract, as a theorem about the reference semantics — no
hypotheses: the name↔instance coherence is the `HasTable.rows_sizes`
law. -/
theorem Query.run_gcard {ts : Ctx} {s : Schema}
    (q : Query ts s) (env : TableEnv ts.tables) (ps : ParamEnv ts.params)
    (now : Option String) {xs : List (Values s)}
    (h : q.run env ps now = .ok xs) :
    xs.length ≤ (Query.gcard q).eval (TableEnv.sizes env) :=
  QueryP.evalRowsIn_gcard_le (q AliasOf) h

/-- The `EvalEnv`-shaped spelling — what the verified interpreter's
`fetch` arm constructs its postcondition with (`DbP.runWithP`). -/
theorem Query.evalRows_gcard_le {ts : Ctx} {s : Schema}
    (q : Query ts s) {ee : EvalEnv ts} {xs : List (Values s)}
    (h : q.evalRows ee = .ok xs) :
    xs.length ≤ (Query.gcard q).eval (TableEnv.sizes ee.tables) :=
  QueryP.evalRowsIn_gcard_le (q AliasOf) h

end LeanLinq
