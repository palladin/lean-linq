import LeanLinq.Core.Query
import LeanLinq.Compiler.Expr

namespace LeanLinq

/-- Materialize the staged row of a source: every column becomes a `field`
reference through the given alias (empty alias ⇒ bare column names). -/
def Row.ofAlias (alias : String) : (s : Schema) → Row s
  | [] => .nil
  | (name, t) :: s => .cons (.field t alias name) (Row.ofAlias alias s)

/-- Render a projected row as a SELECT list: `expr AS name` per column. -/
def Row.selectList : {s : Schema} → Row s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e r => do
      let item ← e.compile
      let rest ← r.selectList
      return s!"{item} AS {← quote name}" :: rest

/-- The default projection callback: render the yielded row, no extra tail. -/
def Row.defaultSelect (r : Row s) : CompileM (String × String) := do
  return (String.intercalate ", " (← r.selectList), "")

def SetOp.token : SetOp → String
  | .union => "UNION" | .intersect => "INTERSECT" | .except => "EXCEPT"

def JoinKind.token : JoinKind → String
  | .inner => "INNER JOIN" | .left => "LEFT JOIN"

/-- A FROM item: `isJoin` marks JOIN clauses (attached with a space) versus
plain sources (comma-separated). -/
private def renderFroms (froms : Array (Bool × String)) : String :=
  match froms.toList with
  | [] => ""
  | (_, first) :: rest =>
    let tail := rest.foldl (fun acc (isJoin, s) =>
      acc ++ (if isJoin then " " else ", ") ++ s) ""
    s!" FROM {first}{tail}"

private def renderWheres (wheres : Array String) : String :=
  if wheres.isEmpty then ""
  else s!" WHERE {String.intercalate " AND " wheres.toList}"

def compileOrderKeys (ks : List OrderKey) : CompileM String := do
  let items ← ks.mapM fun k => do
    let e ← k.expr.compile
    return s!"{e} {if k.dir == .asc then "ASC" else "DESC"}"
  return String.intercalate ", " items

def compileGroupKeys (ks : List KeyExpr) : CompileM String := do
  let items ← ks.mapM (·.expr.compile)
  return String.intercalate ", " items

mutual

/-- Compile a full query. Boundary clauses (ORDER BY, DISTINCT, LIMIT, set
ops, GROUP BY) decorate the statement produced by the spine underneath. -/
def Query.compileStmt : Query s → CompileM String
  | .spine sp => sp.compileSpine #[] #[] #[] Row.defaultSelect
  | .distinctC q => do
      let inner ← q.compileStmt
      return if inner.startsWith "SELECT " then
        "SELECT DISTINCT " ++ (inner.drop "SELECT ".length)
      else inner
  | .limitC q lim? off? => do
      let inner ← q.compileStmt
      match (← read) with
      | .sqlServer =>
          let ob := if (inner.splitOn " ORDER BY ").length > 1 then "" else " ORDER BY (SELECT NULL)"
          let offN := off?.getD 0
          let fetch := match lim? with
            | some l => s!" FETCH NEXT {l} ROWS ONLY"
            | none => ""
          return s!"{inner}{ob} OFFSET {offN} ROWS{fetch}"
      | .sqlite =>
          return match lim?, off? with
            | some l, some o => s!"{inner} LIMIT {l} OFFSET {o}"
            | some l, none => s!"{inner} LIMIT {l}"
            | none, some o => s!"{inner} LIMIT -1 OFFSET {o}"
            | none, none => inner
      | .postgres =>
          return match lim?, off? with
            | some l, some o => s!"{inner} LIMIT {l} OFFSET {o}"
            | some l, none => s!"{inner} LIMIT {l}"
            | none, some o => s!"{inner} OFFSET {o}"
            | none, none => inner
  | .groupedC (s := s₀) sp keys having? sel =>
      sp.compileSpine #[] #[] #[] fun r => do
        let items ← (sel r ⟨⟩).selectList
        let ks ← compileGroupKeys (keys r)
        let hv ← match having? with
          | none => pure ""
          | some h => do
              let hs ← (h r).compile
              pure s!" HAVING {hs}"
        return (String.intercalate ", " items, s!" GROUP BY {ks}{hv}")
  | .setOpC op a b => do
      return s!"{← a.compileStmt} {op.token} {← b.compileStmt}"

/-- Walk a comprehension spine accumulating FROM sources, JOIN clauses, and
WHERE conjuncts until the final `yield`, then assemble one flat SELECT via
the projection callback (which also supplies a statement tail, e.g.
`GROUP BY … HAVING …`). -/
def SpineQ.compileSpine : SpineQ s → Array (Bool × String) → Array String →
    Array String → (Row s → CompileM (String × String)) → CompileM String
  | .yield r, froms, wheres, orders, k => do
      let (sel, tail) ← k r
      let orderClause :=
        if orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " orders.toList}"
      return s!"SELECT {sel}{renderFroms froms}{renderWheres wheres}{tail}{orderClause}"
  | .guard b rest, froms, wheres, orders, k => do
      let w ← b.compile
      rest.compileSpine froms (wheres.push w) orders k
  | .order ks rest, froms, wheres, orders, k => do
      let rendered ← compileOrderKeys ks
      rest.compileSpine froms wheres (orders.push rendered) k
  | .fromT (s := s₀) t f, froms, wheres, orders, k => do
      let alias ← freshAlias
      let item := s!"{← quote t.name} {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine (froms.push (false, item)) wheres orders k
  | .joinT (s := s₀) kind t on' f, froms, wheres, orders, k => do
      let alias ← freshAlias
      let row := Row.ofAlias alias s₀
      let onStr ← (on' row).compile
      let item := s!"{kind.token} {← quote t.name} {← quote alias} ON {onStr}"
      (f row).compileSpine (froms.push (true, item)) wheres orders k
  | .fromQ (s := s₀) q f, froms, wheres, orders, k => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let item := s!"({sub}) {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine (froms.push (false, item)) wheres orders k

end

/-- Compile a scalar aggregate query. -/
def ScalarQuery.compile : ScalarQuery t → CompileM String
  | .countQ sp => sp.compileSpine #[] #[] #[] fun _ => pure ("COUNT(*)", "")
  | .aggQ op sp => sp.compileSpine #[] #[] #[] fun r =>
      match r with
      | .cons e .nil => do return (s!"{op.token}({← e.compile})", "")

private def runCompile (m : CompileM String) (db : DatabaseType) : Compiled :=
  let (sql, st) := Id.run ((m.run db).run {})
  { sql, params := st.params }

/-- Compile a query to SQL text plus named parameters for the given dialect. -/
def Query.toSql (q : Query s) (db : DatabaseType := .sqlite) : Compiled :=
  runCompile q.compileStmt db

def Query.toSqlite (q : Query s) : Compiled := q.toSql .sqlite
def Query.toSqlServer (q : Query s) : Compiled := q.toSql .sqlServer
def Query.toPostgres (q : Query s) : Compiled := q.toSql .postgres

/-- Compile a scalar query for the given dialect. -/
def ScalarQuery.toSql (sq : ScalarQuery t) (db : DatabaseType := .sqlite) : Compiled :=
  runCompile sq.compile db

/-- `e IN (subquery)` — the subquery must project exactly one column of the
same type. Stored as a staged compilation action (see `SubQuery`). -/
def SqlExpr.inQuery (e : SqlExpr t) (q : Query [(n, t)]) : SqlExpr .bool :=
  .inSub e q.compileStmt

/-- Embed a scalar aggregate query as an expression:
`c["Age"] >. (customers' |>.select … |>.avg).embed`. -/
def ScalarQuery.embed (sq : ScalarQuery t) : SqlExpr t :=
  .scalarSub t sq.compile

end LeanLinq
