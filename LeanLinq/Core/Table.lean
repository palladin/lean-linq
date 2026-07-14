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
well-formed by construction, and it prices `DbFetch` programs directly
(`DbFetch c (customers.size + 1) α`). -/
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

instance (priority := high) : HasTable ((n, s) :: ts) n s where
  rows | .cons rs _ => rs
  set | .cons _ env, rs => .cons rs env
  rows_sizes | .cons rs env => le_sizes_head rs env

instance [h : HasTable ts n s] : HasTable ((n', s') :: ts) n s where
  rows | .cons _ env => h.rows env
  set | .cons rs env, rs' => .cons rs (h.set env rs')
  rows_sizes | .cons rs env => le_sizes_tail rs env (h.rows_sizes env)

end LeanLinq
