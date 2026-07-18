import LeanLinq.Core.Monad
import LeanLinq.Core.Grade

namespace LeanLinq

/-- A database table: both the name and the schema are type indices, so a
table reference is fully static —

```
abbrev Customers : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table "customers" Customers := ⟨⟩
```

The schema stays in literal form during elaboration (column lookup,
projection typing), and the name is what `HasTable` resolves against the
ambient context. -/
structure Table (n : String) (s : Schema)

/-- The table's size as a symbolic **grade**: `customers.size : Grade`
is `|customers|` — the name comes from the type, so the symbol is
well-formed by construction, and it prices `Db` programs directly
(`Db c (customers.size + 1) α`). -/
def Table.size (_ : Table n s) : Grade := .tbl n

/-- Membership of a table in the ambient context, by instance search over
the literal context list — the `HasTable` analogue of `HasCol`. The evidence
*is* the access: resolving a table at elaboration time means already knowing
how to read (and write) its rows in any `TableEnv ts`, so evaluation
performs no name lookup, no schema check, and has no failure mode.

A query over a table absent from the context fails at compile time with
`failed to synthesize HasTable …`. -/
class HasTable (ts : List (String × Schema)) (n : String) (s : outParam Schema) where
  rows : TableEnv ts → List (Values s)
  set : TableEnv ts → List (Values s) → TableEnv ts
  /-- The law that ties the instance (how the evaluator *reads* a table)
  to the name (how `gcard` *prices* it): however the rows are reached,
  there are at most `sizes n` of them. `TableEnv.sizes` takes the max
  over same-named tables precisely so both canonical instances prove
  this with no disequality side conditions. This is what `run_gcard`
  cashes at every source node. -/
  rows_sizes : ∀ env : TableEnv ts, (rows env).length ≤ env.sizes n
  /-- Writes move sizes honestly: foreign names untouched… -/
  sizes_set_other : ∀ (env : TableEnv ts) (rs : List (Values s)) (m : String),
    m ≠ n → TableEnv.sizes (set env rs) m = env.sizes m
  /-- …growing this table never shrinks a size… -/
  sizes_set_mono : ∀ (env : TableEnv ts) (rs : List (Values s)) (m : String),
    (rows env).length ≤ rs.length → env.sizes m ≤ TableEnv.sizes (set env rs) m
  /-- …shrinking it never grows one… -/
  sizes_set_anti : ∀ (env : TableEnv ts) (rs : List (Values s)) (m : String),
    rs.length ≤ (rows env).length → TableEnv.sizes (set env rs) m ≤ env.sizes m
  /-- …and the new size is capped by the write and what was there. -/
  sizes_set_le : ∀ (env : TableEnv ts) (rs : List (Values s)) (m : String),
    TableEnv.sizes (set env rs) m ≤ Nat.max rs.length (env.sizes m)

private theorem le_sizes_head {n : String} {s : Schema} {ts : List (String × Schema)}
    (rs : List (Values s)) (env : TableEnv ts) :
    rs.length ≤ TableEnv.sizes (.cons rs env : TableEnv ((n, s) :: ts)) n := by
  show rs.length ≤ if n = n then Nat.max rs.length (env.sizes n) else env.sizes n
  rw [if_pos rfl]
  exact Nat.le_max_left ..

private theorem le_sizes_tail {n n' : String} {s' : Schema}
    {ts : List (String × Schema)} {k : Nat}
    (rs : List (Values s')) (env : TableEnv ts) (hk : k ≤ env.sizes n) :
    k ≤ TableEnv.sizes (.cons rs env : TableEnv ((n', s') :: ts)) n := by
  show k ≤ if n = n' then Nat.max rs.length (env.sizes n) else env.sizes n
  by_cases hq : n = n'
  · rw [if_pos hq]
    subst hq
    exact Nat.le_trans hk (Nat.le_max_right ..)
  · rwa [if_neg hq]

private theorem sizes_cons {n : String} {s : Schema} {ts : List (String × Schema)}
    (rs : List (Values s)) (env : TableEnv ts) (m : String) :
    TableEnv.sizes (.cons rs env : TableEnv ((n, s) :: ts)) m =
      if m = n then Nat.max rs.length (env.sizes m) else env.sizes m := rfl

instance (priority := high) : HasTable ((n, s) :: ts) n s where
  rows | .cons rs _ => rs
  set | .cons _ env, rs => .cons rs env
  rows_sizes | .cons rs env => le_sizes_head rs env
  sizes_set_other
    | .cons rs env, rs', m, hm => by
        simp only []
        rw [sizes_cons, sizes_cons, if_neg hm, if_neg hm]
  sizes_set_mono
    | .cons rs env, rs', m, hlen => by
        simp only []
        rw [sizes_cons, sizes_cons]
        split
        · exact Nat.max_le.mpr ⟨Nat.le_trans hlen (Nat.le_max_left ..),
            Nat.le_max_right ..⟩
        · exact Nat.le_refl _
  sizes_set_anti
    | .cons rs env, rs', m, hlen => by
        simp only []
        rw [sizes_cons, sizes_cons]
        split
        · exact Nat.max_le.mpr ⟨Nat.le_trans hlen (Nat.le_max_left ..),
            Nat.le_max_right ..⟩
        · exact Nat.le_refl _
  sizes_set_le
    | .cons rs env, rs', m => by
        simp only []
        rw [sizes_cons, sizes_cons]
        split
        · exact Nat.max_le.mpr ⟨Nat.le_max_left ..,
            Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)⟩
        · exact Nat.le_max_right ..

instance [h : HasTable ts n s] : HasTable ((n', s') :: ts) n s where
  rows | .cons _ env => h.rows env
  set | .cons rs env, rs' => .cons rs (h.set env rs')
  rows_sizes | .cons rs env => le_sizes_tail rs env (h.rows_sizes env)
  sizes_set_other
    | .cons rs env, rs', m, hm => by
        simp only []
        rw [sizes_cons, sizes_cons, h.sizes_set_other env rs' m hm]
  sizes_set_mono
    | .cons rs env, rs', m, hlen => by
        simp only []
        rw [sizes_cons, sizes_cons]
        have := h.sizes_set_mono env rs' m hlen
        split
        · exact Nat.max_le.mpr ⟨Nat.le_max_left ..,
            Nat.le_trans this (Nat.le_max_right ..)⟩
        · exact this
  sizes_set_anti
    | .cons rs env, rs', m, hlen => by
        simp only []
        rw [sizes_cons, sizes_cons]
        have := h.sizes_set_anti env rs' m hlen
        split
        · exact Nat.max_le.mpr ⟨Nat.le_max_left ..,
            Nat.le_trans this (Nat.le_max_right ..)⟩
        · exact this
  sizes_set_le
    | .cons rs env, rs', m => by
        simp only []
        rw [sizes_cons, sizes_cons]
        have := h.sizes_set_le env rs' m
        split
        · exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left ..)
              (Nat.le_max_right ..),
            Nat.le_trans this (Nat.max_le.mpr ⟨Nat.le_max_left ..,
              Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)⟩)⟩
        · exact this

end LeanLinq
