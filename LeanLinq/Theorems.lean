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
    (q : Query ts s) (n : Nat) (off? : Option Nat) (ee : EvalEnv ts)
    {rows : List (Values s)}
    (h : (Query.limitC q (some n) off?).evalRows ee = .ok rows) :
    rows.length ≤ n := by
  simp only [Query.evalRows, Query.evalRowsIn] at h
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
  unfold Query.run at h
  unfold Query.limit at h
  split at h
  · exact Query.evalRows_limitC_length_le _ n _ _ h
  · unfold Query.limitOffset at h
    split at h
    · exact Query.evalRows_limitC_length_le _ n _ _ h
    · exact Query.evalRows_limitC_length_le _ n _ _ h

/-! ## Soundness of `card` and `RowInv`

The two compute-from-the-value refinements never underestimate the
reference semantics: whatever `evalRows` produces fits under `card` and
satisfies `RowInv`. These are the theorems that make the fetch doors'
runtime checks principled — provably the identity in the reference
semantics, auditing only a live engine. -/

/-- Sources are ⊤-headed (trivial), sourceless chains yield at most one
branch — so a spine's branch count is bounded by its card. -/
theorem SpineQ.evalSpine_length_le {ts : Ctx} {g : Terminal} {s : Schema}
    {ee : EvalEnv ts} : (sp : SpineQ ts g s) → {n : Nat} → {sc : Scope} →
    {brs : List (Branch ts g s)} →
    sp.evalSpine ee n sc = .ok brs → Bound.fin brs.length ≤ sp.card
  | .yield r, _, _, brs, h => by
      simp only [SpineQ.evalSpine, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_refl _
  | .groupYield .., _, _, brs, h => by
      simp only [SpineQ.evalSpine, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_refl _
  | .guard b rest, _, _, brs, h => by
      simp only [SpineQ.evalSpine] at h
      obtain ⟨bv, _, h⟩ := Except.bind_ok h
      split at h
      · exact SpineQ.evalSpine_length_le rest h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact Bound.zero_le _
  | .order _ rest, _, _, brs, h => by
      simp only [SpineQ.evalSpine] at h
      obtain ⟨brs₀, hrest, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa using SpineQ.evalSpine_length_le rest hrest
  | .fromT (g := .plain) (inst := _) _ _, _, _, _, _ => rfl
  | .fromT (g := .grouped) (inst := _) _ _, _, _, _, _ => rfl
  | .joinT (g := .plain) (inst := _) _ _ _, _, _, _, _ => rfl
  | .joinT (g := .grouped) (inst := _) _ _ _, _, _, _, _ => rfl
  | .joinLeftT (g := .plain) (inst := _) _ _ _, _, _, _, _ => rfl
  | .joinLeftT (g := .grouped) (inst := _) _ _ _, _, _, _, _ => rfl
  | .fromQ (g := .plain) _ _, _, _, _, _ => rfl
  | .fromQ (g := .grouped) _ _, _, _, _, _ => rfl

/-- **`card` is sound**: evaluation never returns more rows than the
query's cardinality bound. -/
theorem Query.evalRowsIn_card_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : Query ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs → Bound.fin xs.length ≤ q.card
  | .spine (g := .plain) sp, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨brs, hsp, hfin⟩ := Except.bind_ok h
      rw [show xs.length = brs.length from finishPlain_length hfin]
      exact SpineQ.evalSpine_length_le sp hsp
  | .spine (g := .grouped) sp, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨brs, hsp, hfin⟩ := Except.bind_ok h
      exact Bound.le_trans
        (Bound.fin_le_fin (finishGrouped_length_le hfin))
        (SpineQ.evalSpine_length_le sp hsp)
  | .distinctC q, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_trans
        (Bound.fin_le_fin (List.length_dedupBy_le _ _))
        (Query.evalRowsIn_card_le q hq)
  | .limitC q lim? off?, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hin := Query.evalRowsIn_card_le q hq
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
  | .groupedC sp keys hv? ord? sel, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨brs, hsp, hcore⟩ := Except.bind_ok h
      have hlen := groupedCore_length_le hcore
      rw [List.length_map] at hlen
      exact Bound.le_trans (Bound.fin_le_fin hlen)
        (SpineQ.evalSpine_length_le sp hsp)
  | .setOpC op a b, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨ra, hra, h⟩ := Except.bind_ok h
      obtain ⟨rb, hrb, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      cases op with
      | union =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_)
            (Bound.add_le_add (Query.evalRowsIn_card_le a hra)
              (Query.evalRowsIn_card_le b hrb))
          calc (List.dedupBy Values.beq (ra ++ rb)).length
              ≤ (ra ++ rb).length := List.length_dedupBy_le _ _
            _ = ra.length + rb.length := List.length_append
      | intersect =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_) (Query.evalRowsIn_card_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _
      | except =>
          subst h
          refine Bound.le_trans (Bound.fin_le_fin ?_) (Query.evalRowsIn_card_le a hra)
          calc (List.dedupBy Values.beq _).length
              ≤ (ra.filter _).length := List.length_dedupBy_le _ _
            _ ≤ ra.length := List.length_filter_le _ _

/-- **`RowInv` is sound**: evaluation always satisfies the row
invariant the query's structure promises. -/
theorem Query.evalRowsIn_rowInv {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : Query ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs → q.rowInvB xs = true
  | .spine .., _, _, _ => rfl
  | .groupedC .., _, _, _ => rfl
  | .setOpC .., _, _, _ => rfl
  | .distinctC q, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [Query.rowInvB, Bool.and_eq_true]
      exact ⟨Values.nodupB_dedupBy _,
        Query.rowInvB_of_sublist q (List.dedupBy_sublist _ _)
          (Query.evalRowsIn_rowInv q hq)⟩
  | .limitC q lim? off?, sc, xs, h => by
      simp only [Query.evalRowsIn] at h
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
  Query.evalRowsIn_card_le q h

/-- Public spelling over `Query.run`. -/
theorem Query.run_rowInv {ts : Ctx} {s : Schema}
    (q : Query ts s) (env : TableEnv ts.tables) (ps : ParamEnv ts.params)
    (now : Option String) {xs : List (Values s)}
    (h : q.run env ps now = .ok xs) : q.RowInv xs :=
  Query.evalRowsIn_rowInv q h

end LeanLinq
