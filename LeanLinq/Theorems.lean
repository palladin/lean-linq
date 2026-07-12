import LeanLinq.Eval.Query

/-! # Theorems about the executable semantics

Queries are total, deeply-embedded values with a denotational semantics
(`Query.run`), so facts about result sets are *theorems*, not conventions.
This file is the home of that (deliberately small, demand-driven) corpus.

Every fetch door that refines its rows runs a decidable check whose
adequacy is a theorem here — the checks are provably the identity in
the reference semantics, auditing only live engines:

- `run_limit_length_le` — `LIMIT n` really limits (`fetchLimit`);
- `run_card_le` — evaluation never exceeds the query's cardinality
  bound (`fetchBounded`);
- `run_rowInv` — evaluation satisfies the row invariant the structure
  promises, e.g. DISTINCT really deduplicates (`fetchInv`). -/

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

/-! ## Soundness of `card` and `RowInv`

The two compute-from-the-value refinements never underestimate the
reference semantics: whatever `evalRows` produces fits under `card` and
satisfies `RowInv`. These are the theorems that make the fetch doors'
runtime checks principled — provably the identity in the reference
semantics, auditing only a live engine. -/

/-- The derived-table composition bound: `rows` under `A`, every part
under `B`, one part per row — the flatten fits under `A * B`. -/
theorem Bound.fin_flatten_le {A B : Bound} {rows : List α}
    {parts : List (List β)}
    (hlen : parts.length = rows.length)
    (hrows : Bound.fin rows.length ≤ A)
    (hparts : ∀ part ∈ parts, Bound.fin part.length ≤ B) :
    Bound.fin parts.flatten.length ≤ A * B := by
  cases hA : A with
  | top => exact Bound.le_top _
  | fin a =>
      cases hB : B with
      | top =>
          cases a <;> exact Bound.le_top _
      | fin b =>
          subst hA; subst hB
          refine Bound.fin_le_fin ?_
          calc parts.flatten.length
              ≤ parts.length * b :=
                List.length_flatten_le parts (fun l hl =>
                  of_decide_eq_true (hparts l hl))
            _ = rows.length * b := by rw [hlen]
            _ ≤ a * b :=
                Nat.mul_le_mul_right b (of_decide_eq_true hrows)

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

mutual

/-- Result counts of the downward walk are bounded by
`#incoming-scopes × card`. The `hn` invariant — the alias counter equals
every incoming scope's length — aligns the card's marker instantiation
with the evaluator's: the `fromQ` case compares the *same* continuation
application on both sides. -/
theorem SpineQP.evalScopes_length_le {ts : Ctx} {g : Terminal} {s : Schema}
    {ee : EvalEnv ts} : (sp : SpineQ ts g s) → {n : Nat} → {scopes : List Scope} →
    {rs : List (List Scope × Values s)} →
    (hn : ∀ sc ∈ scopes, n = sc.length) →
    sp.evalScopes ee n scopes = .ok rs →
    Bound.fin rs.length ≤ Bound.fin scopes.length * sp.cardAux n
  | .yield r, n, scopes, rs, _, h => by
      rw [show (SpineQP.yield r).cardAux n = Bound.fin 1 from rfl, Bound.mul_fin_one]
      exact Bound.fin_le_fin (Nat.le_of_eq (List.length_mapM_except _ h))
  | .groupYield ks hv ord r, n, scopes, rs, _, h => by
      rw [show (SpineQP.groupYield ks hv ord r).cardAux n = Bound.fin 1 from rfl,
        Bound.mul_fin_one]
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨keyed, hk, h⟩ := Except.bind_ok h
      obtain ⟨tagged?, ht, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine Bound.fin_le_fin ?_
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
      refine Bound.le_trans
        (SpineQP.evalScopes_length_le rest ?_ h)
        (Bound.mul_le_mul
          (Bound.fin_le_fin (List.length_filterMap_mapM_except_le hs))
          (Bound.le_refl _))
      intro sc' hsc'
      refine hn sc' (List.filterMap_mapM_except_mem hs ?_ sc' hsc')
      intro x y hfx
      obtain ⟨bv, _, hfx⟩ := Except.bind_ok hfx
      simp only [pure, Except.pure, Except.ok.injEq] at hfx
      split at hfx
      · exact (Option.some.injEq ..).mp hfx |>.symm
      · cases hfx
  | .order ks rest, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨rs', hr, h⟩ := Except.bind_ok h
      obtain ⟨tagged, ht, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have : (sortTagged tagged).length = rs'.length := by
        rw [sortTagged_length, List.length_mapM_except _ ht]
      rw [show (SpineQP.order ks rest).cardAux n = rest.cardAux n from rfl]
      exact this ▸ SpineQP.evalScopes_length_le rest hn hr
  | .fromT (inst := _) _ _, _, _, _, _, _ => Bound.le_top _
  | .joinT (inst := _) _ _ _, _, _, _, _, _ => Bound.le_top _
  | .joinLeftT (inst := _) _ _ _, _, _, _, _, _ => Bound.le_top _
  | .fromQ (s := s₀) q f, n, scopes, rs, hn, h => by
      rw [SpineQP.evalScopes.eq_def] at h
      simp only at h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      have hflat : Bound.fin parts.flatten.length
          ≤ Bound.fin scopes.length * q.cardAux n := by
        refine Bound.fin_flatten_le (List.length_mapM_except _ hm) (Bound.le_refl _) ?_
        intro part hpart
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hpart
        obtain ⟨rows, hq, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        rw [List.length_map]
        exact hn sc hsc ▸ QueryP.evalRowsIn_card_le q hq
      have hbelow := SpineQP.evalScopes_length_le (f ⟨s!"a{n}"⟩)
        (n := n + 1) (scopes := parts.flatten) ?_ h
      · refine Bound.mul_assoc (Bound.fin scopes.length) (q.cardAux n) _ ▸
          Bound.le_trans hbelow
            (Bound.mul_le_mul hflat (Bound.le_refl _))
      · intro ext hext
        obtain ⟨part, hpart, hin⟩ := List.mem_flatten.mp hext
        obtain ⟨sc, hsc, hev⟩ := List.mem_of_mapM_except _ hm part hpart
        obtain ⟨rows, _, hev⟩ := Except.bind_ok hev
        simp only [pure, Except.pure, Except.ok.injEq] at hev
        subst hev
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hin
        simpa using congrArg Nat.succ (hn sc hsc)

/-- **`card` is sound**: evaluation never returns more rows than the
query's cardinality bound — including through derived tables, where the
bound genuinely multiplies. -/
theorem QueryP.evalRowsIn_card_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : QueryA ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs → Bound.fin xs.length ≤ q.cardAux sc.length
  | .spine sp, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨rs, hsp, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have := SpineQP.evalScopes_length_le sp
        (scopes := [sc]) (fun x hx => by cases hx with
          | head => rfl
          | tail _ hx => cases hx) hsp
      rw [List.length_map]
      simpa [Bound.fin_one_mul] using this
  | .distinctC q, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_trans
        (Bound.fin_le_fin (List.length_dedupBy_le _ _))
        (QueryP.evalRowsIn_card_le q hq)
  | .limitC q lim? off?, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hin := QueryP.evalRowsIn_card_le q hq
      cases lim? with
      | some l =>
          refine Bound.le_min (Bound.le_trans (Bound.fin_le_fin ?_) hin)
            (Bound.fin_le_fin ?_)
          · exact Nat.le_trans
              (by simpa only [List.length_take] using Nat.min_le_right l _)
              (by simp only [List.length_drop]; omega)
          · simpa only [List.length_take] using Nat.min_le_left l _
      | none =>
          exact Bound.le_trans (Bound.fin_le_fin (by simp [List.length_drop])) hin
  | .setOpC op a b, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨ra, hra, h⟩ := Except.bind_ok h
      obtain ⟨rb, hrb, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      cases op with
      | union =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_)
            (Bound.add_le_add (QueryP.evalRowsIn_card_le a hra)
              (QueryP.evalRowsIn_card_le b hrb))
          calc (List.dedupBy Values.beq (ra ++ rb)).length
              ≤ (ra ++ rb).length := List.length_dedupBy_le _ _
            _ = ra.length + rb.length := List.length_append
      | intersect =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_) (QueryP.evalRowsIn_card_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _
      | except =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_) (QueryP.evalRowsIn_card_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _

end

/-- **`RowInv` is sound**: evaluation always satisfies the row
invariant the query's structure promises. -/
theorem Query.evalRowsIn_rowInv {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : QueryA ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs → q.rowInvB xs = true
  | .spine .., _, _, _ => rfl
  | .setOpC .., _, _, _ => rfl
  | .distinctC q, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [QueryP.rowInvB, Bool.and_eq_true]
      exact ⟨Values.nodupB_dedupBy _,
        Query.rowInvB_of_sublist q (List.dedupBy_sublist _ _)
          (Query.evalRowsIn_rowInv q hq)⟩
  | .limitC q lim? off?, sc, xs, h => by
      rw [QueryP.evalRowsIn.eq_def] at h
      simp only at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      cases lim? with
      | some l =>
          exact Query.rowInvB_of_sublist q
            ((List.take_sublist ..).trans (List.drop_sublist ..))
            (Query.evalRowsIn_rowInv q hq)
      | none =>
          exact Query.rowInvB_of_sublist q (List.drop_sublist ..)
            (Query.evalRowsIn_rowInv q hq)

/-- Public spelling over `Query.run`. -/
theorem Query.run_card_le {ts : Ctx} {s : Schema}
    (q : Query ts s) (env : TableEnv ts.tables) (ps : ParamEnv ts.params)
    (now : Option String) {xs : List (Values s)}
    (h : q.run env ps now = .ok xs) : Bound.fin xs.length ≤ q.card :=
  QueryP.evalRowsIn_card_le (q AliasOf) h

/-- Public spelling over `Query.run`. -/
theorem Query.run_rowInv {ts : Ctx} {s : Schema}
    (q : Query ts s) (env : TableEnv ts.tables) (ps : ParamEnv ts.params)
    (now : Option String) {xs : List (Values s)}
    (h : q.run env ps now = .ok xs) : q.RowInv xs :=
  Query.evalRowsIn_rowInv (q AliasOf) h

end LeanLinq
