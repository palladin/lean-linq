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

/-- The clauses accumulated while walking a spine, plus statement-level
modifiers. No string inspection anywhere: DISTINCT is a fact about the
statement being assembled, not a rewrite of its text. -/
structure StmtAcc where
  froms : Array (Bool × String) := #[]   -- (isJoin, rendered source)
  wheres : Array String := #[]
  orders : Array String := #[]
  distinct : Bool := false

/-- Does the statement produced for this spine carry an ORDER BY clause?
Purely structural: continuations are applied to a default row (the spine's
shape does not depend on row values). ORDER BY inside a derived table
(`fromQ`) does not count — it belongs to the inner statement. -/
def SpineQ.hasOrder : SpineQ g s → Bool
  | .yield _ => false
  | .groupYield .. => false
  | .guard _ rest => rest.hasOrder
  | .order _ _ => true
  | .fromT (g := .plain) _ f => (f default).hasOrder
  | .fromT (g := .grouped) _ f => (f default).hasOrder
  | .joinT (g := .plain) _ _ _ f => (f default).hasOrder
  | .joinT (g := .grouped) _ _ _ f => (f default).hasOrder
  | .fromQ (g := .plain) _ f => (f default).hasOrder
  | .fromQ (g := .grouped) _ f => (f default).hasOrder

/-- Does the statement produced for this query end with an ORDER BY clause
(needed by SQL Server, whose OFFSET/FETCH requires one)? -/
def Query.hasOrderBy : Query s → Bool
  | .spine sp => sp.hasOrder
  | .distinctC q => q.hasOrderBy
  | .limitC q _ _ => q.hasOrderBy
  | .groupedC sp _ _ ord? _ => sp.hasOrder || ord?.isSome
  | .setOpC .. => false

mutual

/-- Compile a full query. Boundary clauses (DISTINCT, LIMIT, set ops,
GROUP BY) decorate the statement produced by the spine underneath. -/
def Query.compileStmt : Query s → CompileM String
  | .spine sp => sp.compileSpine {} Row.defaultSelect
  -- spines assemble with the DISTINCT flag …
  | .distinctC (.spine sp) => sp.compileSpine { distinct := true } Row.defaultSelect
  -- … other boundary queries become a derived table under a distinct SELECT
  -- (structural recursion forbids `asSpine` here: it can wrap `q`, producing
  -- a larger term)
  | .distinctC (s := s₀) q => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let (sel, _) ← Row.defaultSelect (Row.ofAlias alias s₀)
      return s!"SELECT DISTINCT {sel} FROM ({sub}) {← quote alias}"
  | .limitC q lim? off? => do
      let inner ← q.compileStmt
      match (← read) with
      | .sqlServer =>
          let ob := if q.hasOrderBy then "" else " ORDER BY (SELECT NULL)"
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
  | .groupedC sp keys having? orderKeys? sel =>
      sp.compileSpine {} fun r => do
        let items ← (sel r ⟨⟩).selectList
        let ks ← compileGroupKeys (keys r)
        let hv ← match having? with
          | none => pure ""
          | some h => do
              let hs ← (h r).compile
              pure s!" HAVING {hs}"
        let ob ← match orderKeys? with
          | none => pure ""
          | some oks => do
              let rendered ← compileOrderKeys (oks r)
              pure s!" ORDER BY {rendered}"
        return (String.intercalate ", " items, s!" GROUP BY {ks}{hv}{ob}")
  | .setOpC op a b => do
      return s!"{← a.compileStmt} {op.token} {← b.compileStmt}"

/-- Walk a comprehension spine accumulating FROM sources, JOIN clauses, and
WHERE conjuncts until the final `yield`, then assemble one flat SELECT via
the projection callback (which also supplies a statement tail, e.g.
`GROUP BY … HAVING …`). -/
def SpineQ.compileSpine : SpineQ g s → StmtAcc →
    (Row s → CompileM (String × String)) → CompileM String
  | .yield r, acc, k => do
      let (sel, tail) ← k r
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      return s!"{head} {sel}{renderFroms acc.froms}{renderWheres acc.wheres}{tail}{orderClause}"
  -- the grouped terminal carries its own projection and GROUP BY/HAVING
  -- tail; the caller's projection callback does not apply
  | .groupYield ks hv r, acc, _ => do
      let items ← r.selectList
      let ksStr ← compileGroupKeys ks
      let hvStr ← match hv with
        | none => pure ""
        | some h => do
            let hs ← h.compile
            pure s!" HAVING {hs}"
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      return s!"{head} {String.intercalate ", " items}{renderFroms acc.froms}{renderWheres acc.wheres} GROUP BY {ksStr}{hvStr}{orderClause}"
  | .guard b rest, acc, k => do
      let w ← b.compile
      rest.compileSpine { acc with wheres := acc.wheres.push w } k
  | .order ks rest, acc, k => do
      let rendered ← compileOrderKeys ks
      rest.compileSpine { acc with orders := acc.orders.push rendered } k
  | .fromT (s := s₀) t f, acc, k => do
      let alias ← freshAlias
      let item := s!"{← quote t.name} {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine
        { acc with froms := acc.froms.push (false, item) } k
  | .joinT (s := s₀) kind t on' f, acc, k => do
      let alias ← freshAlias
      let row := Row.ofAlias alias s₀
      let onStr ← (on' row).compile
      let item := s!"{kind.token} {← quote t.name} {← quote alias} ON {onStr}"
      (f row).compileSpine { acc with froms := acc.froms.push (true, item) } k
  | .fromQ (s := s₀) q f, acc, k => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let item := s!"({sub}) {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine
        { acc with froms := acc.froms.push (false, item) } k

end

/-- Compile a scalar aggregate query. -/
def ScalarQuery.compile : ScalarQuery t → CompileM String
  | .countQ sp => sp.compileSpine {} fun _ => pure ("COUNT(*)", "")
  | .aggQ op sp => sp.compileSpine {} fun r =>
      match r with
      | .cons e .nil => do return (s!"{op.token}({← e.compile})", "")

private def runCompile (m : CompileM String) (db : DatabaseType) : CompiledSql :=
  let (sql, st) := Id.run ((m.run db).run {})
  { sql, params := st.params }

/-- Compile a query to SQL text plus named parameters for the given dialect. -/
def Query.toSql (q : Query s) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile q.compileStmt db

def Query.toSqlite (q : Query s) : CompiledSql := q.toSql .sqlite
def Query.toSqlServer (q : Query s) : CompiledSql := q.toSql .sqlServer
def Query.toPostgres (q : Query s) : CompiledSql := q.toSql .postgres

/-- Compile a scalar query for the given dialect. -/
def ScalarQuery.toSql (sq : ScalarQuery t) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile sq.compile db

/-- `e IN (subquery)` — the subquery must project exactly one column of the
same type. Stored as a staged compilation action (see `SubQuery`). -/
def SqlExpr.inQuery (e : SqlExpr t) (q : Query [(n, t)]) : SqlExpr .bool :=
  .inSub e ⟨q.compileStmt⟩

/-- Embed a scalar aggregate query as an expression:
`c["Age"] >. (customers' |>.select … |>.avg).embed`. -/
def ScalarQuery.embed (sq : ScalarQuery t) : SqlExpr t :=
  .scalarSub ⟨sq.compile⟩

end LeanLinq
