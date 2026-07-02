import LeanLinq.Core.Query
import LeanLinq.Compiler.Expr

namespace LeanLinq

/-- Materialize the staged row of a source: every column becomes a `field`
reference through the given alias. -/
def Row.ofAlias (alias : String) : (s : Schema) → Row s
  | [] => .nil
  | (name, t) :: s => .cons (.field t alias name) (Row.ofAlias alias s)

/-- Render a projected row as a SELECT list: `expr AS name` per column. -/
def Row.selectList : {s : Schema} → Row s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e r => do
      let item ← e.compile
      let rest ← r.selectList
      pure (s!"{item} AS {name}" :: rest)

/-- Walk a comprehension spine, accumulating FROM sources and WHERE conjuncts
until the final `yield`, then emit one flat SELECT. Subquery sources (`fromQ`)
compile recursively into derived tables.

`partial` because binder constructors force recursion on the continuation
*applied* to a materialized row — not a structural subterm (each application
still peels one constructor, so this always terminates at runtime). -/
partial def Query.compileParts :
    {s : Schema} → Query s → Array String → Array String → CompileM String
  | _, .yield r, froms, wheres => do
      let items ← r.selectList
      let sel := String.intercalate ", " items
      let fromClause :=
        if froms.isEmpty then "" else s!" FROM {String.intercalate ", " froms.toList}"
      let whereClause :=
        if wheres.isEmpty then "" else s!" WHERE {String.intercalate " AND " wheres.toList}"
      pure s!"SELECT {sel}{fromClause}{whereClause}"
  | _, .guard b rest, froms, wheres => do
      let w ← b.compile
      rest.compileParts froms (wheres.push w)
  | _, .fromT (s := s₀) t k, froms, wheres => do
      let alias ← freshAlias
      (k (Row.ofAlias alias s₀)).compileParts (froms.push s!"{t.name} AS {alias}") wheres
  | _, .fromQ (s := s₀) q k, froms, wheres => do
      let sub ← q.compileParts #[] #[]
      let alias ← freshAlias
      (k (Row.ofAlias alias s₀)).compileParts (froms.push s!"({sub}) AS {alias}") wheres

/-- Compile a query to SQL text. -/
def Query.compile (q : Query s) : CompileM String :=
  q.compileParts #[] #[]

/-- Compile a query to SQL text plus named parameters (SQLite conventions). -/
def Query.toSql (q : Query s) : Compiled :=
  let (sql, st) := Id.run (q.compile.run {})
  { sql, params := st.params }

end LeanLinq
