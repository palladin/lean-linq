import LeanLinq.Core.Query
import LeanLinq.Compiler.Expr

namespace LeanLinq

/-- Materialize the staged row of a derived table: every column becomes a
`field` reference through the given alias (the Idris `mapToTuple`). -/
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

/-- Compile a query to SQL. Every combinator wraps its child as a derived
table with a fresh alias (the Idris scheme) — no flattening in milestone 1,
so the output shape is fully predictable. -/
def Query.compile : {s : Schema} → Query s → CompileM String
  | _, .fromTable t => pure s!"SELECT * FROM {t.name}"
  | s, .whereC q p => do
      let inner ← q.compile
      let alias ← freshAlias
      let pred ← (p (Row.ofAlias alias s)).compile
      pure s!"SELECT * FROM ({inner}) AS {alias} WHERE {pred}"
  | _, .selectC (s := s₀) q f => do
      let inner ← q.compile
      let alias ← freshAlias
      let items ← (f (Row.ofAlias alias s₀)).selectList
      pure s!"SELECT {String.intercalate ", " items} FROM ({inner}) AS {alias}"
  | _, .productC (s₁ := s₁) (s₂ := s₂) q₁ q₂ f => do
      let inner₁ ← q₁.compile
      let inner₂ ← q₂.compile
      let alias₁ ← freshAlias
      let alias₂ ← freshAlias
      let items ← (f (Row.ofAlias alias₁ s₁) (Row.ofAlias alias₂ s₂)).selectList
      pure s!"SELECT {String.intercalate ", " items} FROM ({inner₁}) AS {alias₁}, ({inner₂}) AS {alias₂}"

/-- Compile a query to SQL text plus named parameters (SQLite conventions). -/
def Query.toSql (q : Query s) : Compiled :=
  let (sql, st) := Id.run (q.compile.run {})
  { sql, params := st.params }

end LeanLinq
