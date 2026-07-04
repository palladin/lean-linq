import LeanLinq.Core.Types

namespace LeanLinq

/-- State threaded through SQL generation: a counter for source aliases and
the accumulated named parameters. -/
structure CompileState where
  aliasCounter : Nat := 0
  params : Array (String × SqlValue) := #[]

/-- Compilation reads the target dialect and threads `CompileState`. -/
abbrev CompileM := ReaderT DatabaseType (StateM CompileState)

/-- A staged subquery producing a single column of type `t`: expressions
embed subqueries as their *compilation action* rather than their AST. This
breaks the `SqlExpr`/`Query` cycle that would otherwise violate strict
positivity through the HOAS binders (`Row → Query` puts `Query` occurrences
inside `Row`'s expression fields, to the left of an arrow).

The index is a phantom carrying the erased query's column type, so the
type-match between a subquery and the expression it embeds into is visible
in the AST, not just enforced at the smart constructors
(`SqlExpr.inQuery` / `ScalarQuery.embed` — the only intended producers). -/
structure SubQuery (t : SqlType) where
  compile : CompileM String

/-- Allocate a fresh source alias: `a0`, `a1`, … -/
def freshAlias : CompileM String := fun _ =>
  modifyGet fun st =>
    (s!"a{st.aliasCounter}", { st with aliasCounter := st.aliasCounter + 1 })

/-- Parameter prefix: `@` for SQL Server, `:` for SQLite/PostgreSQL. -/
def DatabaseType.paramPrefix : DatabaseType → String
  | .sqlServer => "@"
  | _ => ":"

/-- Quote an identifier: `[x]` for SQL Server, `"x"` for SQLite/PostgreSQL. -/
def DatabaseType.quoteIdent (db : DatabaseType) (s : String) : String :=
  match db with
  | .sqlServer => s!"[{s}]"
  | _ => s!"\"{s}\""

def quote (s : String) : CompileM String := fun db => pure (db.quoteIdent s)

/-- Allocate an auto-named parameter (`@p0` / `:p0`) for a literal value and
return its placeholder. -/
def pushParam (v : SqlValue) : CompileM String := fun db =>
  modifyGet fun st =>
    let name := s!"{db.paramPrefix}p{st.params.size}"
    (name, { st with params := st.params.push (name, v) })

/-- Reference a user-named parameter (`@minAge` / `:minAge`). Its value is
supplied at execution time, so it is recorded with a `null` placeholder;
repeated references record it once. -/
def refParam (name : String) : CompileM String := fun db =>
  modifyGet fun st =>
    let full := s!"{db.paramPrefix}{name}"
    if st.params.any (·.1 == full) then (full, st)
    else (full, { st with params := st.params.push (full, .null) })

/-- The result of compiling a query or statement: SQL text plus its named
parameters (auto parameters carry their values, user-named ones `null`). -/
structure CompiledSql where
  sql : String
  params : Array (String × SqlValue)
  deriving Repr, BEq

end LeanLinq
