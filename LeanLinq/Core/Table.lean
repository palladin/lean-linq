import LeanLinq.Core.Schema

namespace LeanLinq

/-- A database table with schema `s`. The schema is a type index (not a field)
so that query types stay in literal form during elaboration:

```
abbrev Customers : Schema := [("Id", .int), ("Name", .string), ("Age", .int)]
def customers : Table Customers := ⟨"Customers"⟩
```
-/
structure Table (s : Schema) where
  name : String

end LeanLinq
