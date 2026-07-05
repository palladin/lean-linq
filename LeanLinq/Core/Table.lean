import LeanLinq.Core.Schema

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

instance (priority := high) : HasTable ((n, s) :: ts) n s where
  rows | .cons rs _ => rs
  set | .cons _ env, rs => .cons rs env

instance [h : HasTable ts n s] : HasTable ((n', s') :: ts) n s where
  rows | .cons _ env => h.rows env
  set | .cons rs env, rs' => .cons rs (h.set env rs')

end LeanLinq
