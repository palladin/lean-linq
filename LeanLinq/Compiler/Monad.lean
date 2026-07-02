import LeanLinq.Core.Types

namespace LeanLinq

/-- State threaded through SQL generation: a counter for derived-table aliases
and the accumulated named parameters. -/
structure CompileState where
  aliasCounter : Nat := 0
  params : Array (String × SqlValue) := #[]

abbrev CompileM := StateM CompileState

/-- Allocate a fresh derived-table alias: `c0`, `c1`, … -/
def freshAlias : CompileM String :=
  modifyGet fun st =>
    (s!"c{st.aliasCounter}", { st with aliasCounter := st.aliasCounter + 1 })

/-- Allocate a named parameter (`@p0`, `@p1`, … — SQLite naming style)
for a literal value and return its placeholder. -/
def pushParam (v : SqlValue) : CompileM String :=
  modifyGet fun st =>
    let name := s!"@p{st.params.size}"
    (name, { st with params := st.params.push (name, v) })

/-- The result of compiling a query: SQL text plus its named parameters. -/
structure Compiled where
  sql : String
  params : Array (String × SqlValue)
  deriving Repr, BEq

end LeanLinq
