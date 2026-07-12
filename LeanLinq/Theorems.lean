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
    (h : (QueryP.limitC q (some n) off?).evalRows ee = .ok rows) :
    rows.length ≤ n := by
  simp only [Query.evalRows, QueryP.evalRowsIn] at h
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
  unfold Query.limit QueryP.limit at h
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

mutual

/-- Branch counts are bounded by the spine's card. The `hn` invariant —
the alias counter equals the scope length — is what aligns the card's
marker instantiation with the evaluator's: the `fromQ` case compares
the *same* continuation application on both sides. -/
theorem SpineQP.evalSpine_length_le {ts : Ctx} {g : Terminal} {s : Schema}
    {ee : EvalEnv ts} : (sp : SpineQ ts g s) → {n : Nat} → {sc : Scope} →
    {brs : List (Branch ts g s)} → (hn : n = sc.length) →
    sp.evalSpine ee n sc = .ok brs → Bound.fin brs.length ≤ sp.cardAux n
  | .yield r, _, _, brs, _, h => by
      simp only [SpineQP.evalSpine, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_refl _
  | .groupYield .., _, _, brs, _, h => by
      simp only [SpineQP.evalSpine, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_refl _
  | .guard b rest, _, _, brs, hn, h => by
      simp only [SpineQP.evalSpine] at h
      obtain ⟨bv, _, h⟩ := Except.bind_ok h
      split at h
      · exact SpineQP.evalSpine_length_le rest hn h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact Bound.zero_le _
  | .order _ rest, _, _, brs, hn, h => by
      simp only [SpineQP.evalSpine] at h
      obtain ⟨brs₀, hrest, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa using SpineQP.evalSpine_length_le rest hn hrest
  | .fromT (g := .plain) (inst := _) _ _, _, _, _, _, _ => rfl
  | .fromT (g := .grouped) (inst := _) _ _, _, _, _, _, _ => rfl
  | .joinT (g := .plain) (inst := _) _ _ _, _, _, _, _, _ => rfl
  | .joinT (g := .grouped) (inst := _) _ _ _, _, _, _, _, _ => rfl
  | .joinLeftT (g := .plain) (inst := _) _ _ _, _, _, _, _, _ => rfl
  | .joinLeftT (g := .grouped) (inst := _) _ _ _, _, _, _, _, _ => rfl
  | .fromQ (s := s₀) q f, n, sc, brs, hn, h => by
      simp only [SpineQP.evalSpine] at h
      obtain ⟨rows, hq, h⟩ := Except.bind_ok h
      obtain ⟨parts, hm, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine Bound.fin_flatten_le (List.length_mapM_except _ hm)
        (hn ▸ QueryP.evalRowsIn_card_le q hq) ?_
      intro part hpart
      obtain ⟨v, _, hev⟩ := List.mem_of_mapM_except _ hm part hpart
      exact SpineQP.evalSpine_length_le _ (by simp [hn]) hev

/-- **`card` is sound**: evaluation never returns more rows than the
query's cardinality bound — including through derived tables, where the
bound genuinely multiplies. -/
theorem QueryP.evalRowsIn_card_le {ts : Ctx} {s : Schema} {ee : EvalEnv ts} :
    (q : Query ts s) → {sc : Scope} → {xs : List (Values s)} →
    q.evalRowsIn ee sc = .ok xs → Bound.fin xs.length ≤ q.cardAux sc.length
  | .spine (g := .plain) sp, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
      obtain ⟨brs, hsp, hfin⟩ := Except.bind_ok h
      rw [show xs.length = brs.length from finishPlain_length hfin]
      exact SpineQP.evalSpine_length_le sp rfl hsp
  | .spine (g := .grouped) sp, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
      obtain ⟨brs, hsp, hfin⟩ := Except.bind_ok h
      exact Bound.le_trans
        (Bound.fin_le_fin (finishGrouped_length_le hfin))
        (SpineQP.evalSpine_length_le sp rfl hsp)
  | .distinctC q, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
      obtain ⟨inner, hq, h⟩ := Except.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Bound.le_trans
        (Bound.fin_le_fin (List.length_dedupBy_le _ _))
        (QueryP.evalRowsIn_card_le q hq)
  | .limitC q lim? off?, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
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
  | .groupedC sp keys hv? ord? sel, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
      obtain ⟨brs, hsp, hcore⟩ := Except.bind_ok h
      have hlen := groupedCore_length_le hcore
      rw [List.length_map] at hlen
      exact Bound.le_trans (Bound.fin_le_fin hlen)
        (SpineQP.evalSpine_length_le sp rfl hsp)
  | .setOpC op a b, sc, xs, h => by
      simp only [QueryP.evalRowsIn] at h
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
      rw [QueryP.rowInvB, Bool.and_eq_true]
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
  QueryP.evalRowsIn_card_le q h

/-- Public spelling over `Query.run`. -/
theorem Query.run_rowInv {ts : Ctx} {s : Schema}
    (q : Query ts s) (env : TableEnv ts.tables) (ps : ParamEnv ts.params)
    (now : Option String) {xs : List (Values s)}
    (h : q.run env ps now = .ok xs) : q.RowInv xs :=
  Query.evalRowsIn_rowInv q h

end LeanLinq
