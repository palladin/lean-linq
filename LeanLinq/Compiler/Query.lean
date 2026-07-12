import LeanLinq.Core.Query
import LeanLinq.Compiler.Expr
import LeanLinq.Eval.Query

namespace LeanLinq

/-- Render a projected row as a SELECT list: `expr AS name` per column. -/
def Row.selectList : {s : Schema} → Row ts s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e r => do
      let item ← e.compile
      let rest ← r.selectList
      return s!"{item} AS {← quote name}" :: rest

/-- The default projection callback: render the yielded row, no extra tail. -/
def Row.defaultSelect (r : Row ts s) : CompileM (String × String) := do
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

def compileOrderKeys (ks : List (OrderKey ts)) : CompileM String := do
  let db ← read
  let items ← ks.mapM fun k => do
    let e ← k.expr.compile
    -- the evaluator (and SQLite/SQL Server) sort NULL smallest; PostgreSQL
    -- defaults to NULLS LAST on ASC — make the placement explicit there
    let nulls := if db == .postgres then
        (if k.dir == .asc then " NULLS FIRST" else " NULLS LAST") else ""
    return s!"{e} {if k.dir == .asc then "ASC" else "DESC"}{nulls}"
  return String.intercalate ", " items

def compileGroupKeys (ks : List (KeyExpr ts)) : CompileM String := do
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
def SpineQ.hasOrder : SpineQ ts g s → Bool
  | .yield _ => false
  | .groupYield .. => false
  | .guard _ rest => rest.hasOrder
  | .order _ _ => true
  | .fromT (g := .plain) (inst := _) _ f => (f default).hasOrder
  | .fromT (g := .grouped) (inst := _) _ f => (f default).hasOrder
  | .joinT (g := .plain) (inst := _) _ _ f => (f default).hasOrder
  | .joinT (g := .grouped) (inst := _) _ _ f => (f default).hasOrder
  | .joinLeftT (g := .plain) (inst := _) _ _ f => (f default).hasOrder
  | .joinLeftT (g := .grouped) (inst := _) _ _ f => (f default).hasOrder
  | .fromQ (g := .plain) _ f => (f default).hasOrder
  | .fromQ (g := .grouped) _ f => (f default).hasOrder

/-- Does the statement produced for this query end with an ORDER BY clause
(needed by SQL Server, whose OFFSET/FETCH requires one)? -/
def Query.hasOrderBy : Query ts s → Bool
  | .spine sp => sp.hasOrder
  | .distinctC q => q.hasOrderBy
  | .limitC q _ _ => q.hasOrderBy
  | .groupedC sp _ _ ord? _ => sp.hasOrder || ord?.isSome
  | .setOpC .. => false

/-- What spine assembly needs from the caller, by terminal shape: *plain*
terminals take a projection callback — select list plus statement tail —
which is how scalar queries substitute `COUNT(*)` and pipeline grouping
injects its `GROUP BY … HAVING …`; *grouped* terminals own their projection
and tail, so there is nothing to pass. -/
@[reducible] def SelectK : Ctx → Terminal → Schema → Type
  | ts, .plain, s => Row ts s → CompileM (String × String)
  | _, .grouped, _ => Unit

mutual

/-- Compile a full query. Boundary clauses (DISTINCT, LIMIT, set ops,
GROUP BY) decorate the statement produced by the spine underneath. -/
def Query.compileStmt : Query ts s → CompileM String
  | .spine (g := .plain) sp => sp.compileSpine {} Row.defaultSelect
  | .spine (g := .grouped) sp => sp.compileSpine {} ()
  -- spines assemble with the DISTINCT flag …
  | .distinctC (.spine (g := .plain) sp) => sp.compileSpine { distinct := true } Row.defaultSelect
  | .distinctC (.spine (g := .grouped) sp) => sp.compileSpine { distinct := true } ()
  -- … other boundary queries become a derived table under a distinct SELECT
  -- (structural recursion forbids `asSpine` here: it can wrap `q`, producing
  -- a larger term)
  | .distinctC (s := s₀) q => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      -- the marker row is render-only; pin its (otherwise unconstrained) ts
      let (sel, _) ← Row.defaultSelect (Row.ofAlias alias s₀ : Row ts s₀)
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
              let hs ← (h r).compilePred
              pure s!" HAVING {hs}"
        let ob ← match orderKeys? with
          | none => pure ""
          | some oks => do
              let rendered ← compileOrderKeys (oks r)
              pure s!" ORDER BY {rendered}"
        -- zero keys = one group over all rows: SQL spells that with *no*
        -- GROUP BY clause (an empty one is a syntax error)
        let gb := if ks.isEmpty then "" else s!" GROUP BY {ks}"
        return (String.intercalate ", " items, s!"{gb}{hv}{ob}")
  | .setOpC (s := s₀) op a b => do
      -- operands need structural parenthesization: PostgreSQL/SQL Server
      -- give INTERSECT higher precedence and EXCEPT chains associate left,
      -- so a nested operand compiled flat silently changes meaning — and
      -- SQLite rejects parenthesized compounds, so nesting wraps as a
      -- derived table. Plain spines compile flat with their (dead) ORDER
      -- BY stripped: an operand's order is discarded by the operation.
      let ca ← match a with
        | .spine (g := .plain) sp => sp.compileSpine {} Row.defaultSelect
        | .spine (g := .grouped) sp => sp.compileSpine {} ()
        | qa => do
            let sub ← qa.compileStmt
            let alias ← freshAlias
            let (sel, _) ← Row.defaultSelect (Row.ofAlias alias s₀ : Row ts s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      let cb ← match b with
        | .spine (g := .plain) sp => sp.compileSpine {} Row.defaultSelect
        | .spine (g := .grouped) sp => sp.compileSpine {} ()
        | qb => do
            let sub ← qb.compileStmt
            let alias ← freshAlias
            let (sel, _) ← Row.defaultSelect (Row.ofAlias alias s₀ : Row ts s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      return s!"{ca} {op.token} {cb}"

/-- Walk a comprehension spine accumulating FROM sources, JOIN clauses, and
WHERE conjuncts until the terminal, then assemble one flat SELECT. The third
argument's type follows the terminal (`SelectK`): a projection callback for
plain spines, nothing for grouped ones. -/
def SpineQ.compileSpine : SpineQ ts g s → StmtAcc → SelectK ts g s → CompileM String
  | .yield r, acc, k => do
      let (sel, tail) ← k r
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      return s!"{head} {sel}{renderFroms acc.froms}{renderWheres acc.wheres}{tail}{orderClause}"
  -- the grouped terminal carries its own projection and GROUP BY/HAVING
  -- tail; by type (`SelectK .grouped`), there is no caller callback at all
  | .groupYield ks hv r, acc, () => do
      let items ← r.selectList
      let ksStr ← compileGroupKeys ks
      let hvStr ← match hv with
        | none => pure ""
        | some h => do
            let hs ← h.compilePred
            pure s!" HAVING {hs}"
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      let gb := if ksStr.isEmpty then "" else s!" GROUP BY {ksStr}"
      return s!"{head} {String.intercalate ", " items}{renderFroms acc.froms}{renderWheres acc.wheres}{gb}{hvStr}{orderClause}"
  | .guard b rest, acc, k => do
      let w ← b.compilePred
      rest.compileSpine { acc with wheres := acc.wheres.push w } k
  | .order ks rest, acc, k => do
      let rendered ← compileOrderKeys ks
      rest.compileSpine { acc with orders := acc.orders.push rendered } k
  | .fromT (n := nm) (s := s₀) (inst := _) _ f, acc, k => do
      let alias ← freshAlias
      let item := s!"{← quote nm} {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine
        { acc with froms := acc.froms.push (false, item) } k
  | .joinT (n := nm) (s := s₀) (inst := _) _ on' f, acc, k => do
      let alias ← freshAlias
      let row := Row.ofAlias alias s₀
      let onStr ← (on' row).compilePred
      let item := s!"{JoinKind.inner.token} {← quote nm} {← quote alias} ON {onStr}"
      (f row).compileSpine { acc with froms := acc.froms.push (true, item) } k
  | .joinLeftT (n := nm) (s := s₀) (inst := _) _ on' f, acc, k => do
      let alias ← freshAlias
      let row := Row.ofAlias alias s₀.asNull
      let onStr ← (on' row).compilePred
      let item := s!"{JoinKind.left.token} {← quote nm} {← quote alias} ON {onStr}"
      (f row).compileSpine { acc with froms := acc.froms.push (true, item) } k
  | .fromQ (s := s₀) q f, acc, k => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let item := s!"({sub}) {← quote alias}"
      (f (Row.ofAlias alias s₀)).compileSpine
        { acc with froms := acc.froms.push (false, item) } k

end

/-- Compile a scalar aggregate query. -/
def ScalarQuery.compile : ScalarQuery ts c → CompileM String
  | .countQ sp => sp.compileSpine {} fun _ => pure ("COUNT(*)", "")
  | .aggQ op sp => sp.compileSpine {} fun r =>
      match r with
      | .cons e .nil => do return (s!"{op.token}({← e.compile})", "")

private def runCompile (m : CompileM String) (db : DatabaseType) : CompiledSql :=
  let (sql, st) := Id.run ((m.run db).run {})
  { sql, params := st.params }

/-- Compile a query to SQL text plus named parameters for the given dialect. -/
def Query.toSql (q : Query ts s) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile q.compileStmt db

def Query.toSqlite (q : Query ts s) : CompiledSql := q.toSql .sqlite
def Query.toSqlServer (q : Query ts s) : CompiledSql := q.toSql .sqlServer
def Query.toPostgres (q : Query ts s) : CompiledSql := q.toSql .postgres

/-- Compile a scalar query for the given dialect. -/
def ScalarQuery.toSql (sq : ScalarQuery ts c) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile sq.compile db

/-- `e IN (subquery)` — the subquery must project exactly one column of the
same type. Stored as its staged actions (see `SubQuery`): compilation for
`toSql`, evaluation for `run`. -/
def SqlExpr.inQuery (e : SqlExpr ts ⟨t, nf⟩) (q : Query ts [(cn, ⟨t, m⟩)]) :
    SqlExpr ts ⟨.bool, true⟩ :=
  .inSub e ⟨q.compileStmt, fun ee sc => (q.evalRowsIn ee sc).map fun rows =>
    rows.map fun | .cons cell .nil => SqlType.toNullable cell⟩

/-- Embed a scalar aggregate query as an expression:
`c["Age"] >. (customers' |>.select … |>.avg).embed`. -/
def ScalarQuery.embed (sq : ScalarQuery ts ⟨t, n⟩) : SqlExpr ts ⟨t, true⟩ :=
  .scalarSub ⟨sq.compile, fun ee sc => (sq.evalCellIn ee sc).map fun c => [c]⟩

end LeanLinq
