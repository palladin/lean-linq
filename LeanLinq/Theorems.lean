import LeanLinq.Eval.Query

/-! # Theorems about the executable semantics

Queries are total, deeply-embedded values with a denotational semantics
(`Query.run`), so facts about result sets are *theorems*, not conventions.
This file is the home of that (deliberately small, demand-driven) corpus.

The first inhabitant pays rent immediately: `DbFetch.fetchLimit` returns a
length-refined list whose proof is realized by a length check (the `take`
clamp fires only against a disagreeing engine) — and `run_limit_length_le`
is the adequacy statement for that check in the reference semantics: a
`LIMIT n` query already returns at most `n` rows. -/

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

end LeanLinq
