import LeanLinq.Core.Query
import LeanLinq.Compiler.Expr
import LeanLinq.Eval.Query

namespace LeanLinq

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
def SpineQP.hasOrder : SpineQ ts g s → Bool
  | .yield _ => false
  | .groupYield _ _ ord _ => !ord.isEmpty
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
def QueryP.hasOrderBy : QueryA ts s → Bool
  | .spine sp => sp.hasOrder
  | .distinctC q => q.hasOrderBy
  | .limitC q _ _ => q.hasOrderBy
  | .setOpC .. => false

namespace SpineQ
export SpineQP (hasOrder)
end SpineQ

namespace Query
export QueryP (hasOrderBy)
end Query

/-- What a *plain* terminal renders as its SELECT list, defunctionalized
(the compile walk is one structural mutual ring with the expression
compiler, so a function-valued callback would defeat the termination
argument): the yielded row itself, `COUNT(*)`, or an aggregate over the
row's single column. Grouped terminals own their projection and ignore
this. -/
inductive SelSpec where
  | defaultSel
  | countSel
  | aggSel (op : AggOp)

/-- The SELECT list of a boundary derived table: every column of the
marker row `alias.col AS col` — rendered textually (a marker `field`
compiles to exactly this), keeping the walk's recursion structural. -/
private def aliasSelect (alias : String) : Schema → CompileM (List String)
  | [] => pure []
  | (nm, _) :: s => do
      return s!"{← quote alias}.{← quote nm} AS {← quote nm}" :: (← aliasSelect alias s)

/-- Predicate-position wrapping (WHERE / ON / HAVING / AND / OR / NOT /
CASE WHEN): T-SQL bit values are not predicates, so on SQL Server a
non-predicate boolean wraps as `({e} = 1)`. Non-recursive — the ring
inlines it after compiling the operand. -/
def predWrap (isPred : Bool) (s : String) : CompileM String := do
  if (← read) == .sqlServer && !isPred then
    return s!"({s} = 1)"
  else
    return s

mutual

/-- Render an expression to SQL text for the ambient dialect, allocating a
named parameter for every literal (never inlining values). -/
def SqlExprP.compile : SqlExpr ts c → CompileM String
  | .intC i        => pushParam (.int i)
  | .longC i       => pushParam (.long i)
  | .doubleC f     => pushParam (.double f)
  | .decimalC d    => pushParam (.decimal d)
  | .stringC s     => pushParam (.string s)
  | .boolC b       => pushParam (.bool b)
  | .dateTimeC s   => pushParam (.dateTime (normDateTime s)) -- SQLite compares strings: ship the normalized form the evaluator uses
  | .guidC g       => pushParam (.guid g)
  | .nullC _       => pure "NULL"
  | .paramE (inst := _) name => refParam name
  | .widen e => e.compile
  | .field _ row name => do
      if row.alias.isEmpty then quote name
      else return s!"{← quote row.alias}.{← quote name}"
  | .arith op a b  => return s!"({← a.compile} {op.token} {← b.compile})"
  | .concat a b    => do
      let tok := if (← read) == .sqlServer then "+" else "||"
      return s!"({← a.compile} {tok} {← b.compile})"
  | .cmp (t := t₀) op a b => do
      let sa ← a.compile
      let sb ← b.compile
      -- SQL Server: predicates are not values; convert before comparing.
      let wrap (e : SqlExpr ts ⟨t₀, true⟩) (s : String) : String :=
        if t₀ == .bool && e.isPredicate then s!"CASE WHEN {s} THEN 1 ELSE 0 END" else s
      if (← read) == .sqlServer then
        return s!"({wrap a sa} {op.token} {wrap b sb})"
      else
        return s!"({sa} {op.token} {sb})"
  | .and a b       => return s!"({← predWrap a.isPredicate (← a.compile)} AND {← predWrap b.isPredicate (← b.compile)})"
  | .or a b        => return s!"({← predWrap a.isPredicate (← a.compile)} OR {← predWrap b.isPredicate (← b.compile)})"
  | .not a         => return s!"(NOT {← predWrap a.isPredicate (← a.compile)})"
  | .isNull e      => return s!"{← e.compile} IS NULL"
  | .isNotNull e   => return s!"{← e.compile} IS NOT NULL"
  | .like e p      => return s!"{← e.compile} LIKE {← p.compile}"
  -- an empty IN list is invalid SQL (PostgreSQL/SQL Server reject `IN ()`);
  -- SQL's `x IN (empty)` is FALSE without evaluating x, so compile exactly that
  | .inList _ []   => return "(1 = 0)"
  | .inList e es   => return s!"{← e.compile} IN ({String.intercalate ", " (← SqlExprP.compileList es)})"
  | .inSub e sub   => return s!"{← e.compile} IN ({← sub.compileStmt})"
  | .existsSub sub => return s!"EXISTS ({← sub.compileStmt})"
  | .scalarSub sub => return s!"({← sub.compileScalar})"
  | .caseWhen c a b =>
      return s!"CASE WHEN {← predWrap c.isPredicate (← c.compile)} THEN {← a.compile} ELSE {← b.compile} END"
  | .aggE op e     => return s!"{op.token}({← e.compile})"
  | .countAll      => pure "COUNT(*)"
  | .abs e         => return s!"ABS({← e.compile})"
  | .round e digits => do
      let p ← pushParam (.int digits)
      return s!"ROUND({← e.compile}, {p})"
  | .ceiling e     => do
      let name := match (← read) with
        | .sqlite => "CEIL"
        | _ => "CEILING"
      return s!"{name}({← e.compile})"
  | .floor e       => return s!"FLOOR({← e.compile})"
  | .substring e start len => do
      let name := if (← read) == .sqlite then "SUBSTR" else "SUBSTRING"
      let p1 ← pushParam (.int start)
      let p2 ← pushParam (.int len)
      return s!"{name}({← e.compile}, {p1}, {p2})"
  | .upper e       => return s!"UPPER({← e.compile})"
  | .lower e       => return s!"LOWER({← e.compile})"
  | .trim e        => return s!"TRIM({← e.compile})"
  | .length e      => do
      let name := if (← read) == .sqlServer then "LEN" else "LENGTH"
      return s!"{name}({← e.compile})"
  | .now           =>
      return match (← read) with
        | .sqlServer => "GETDATE()"
        | .sqlite => "datetime('now')"
        | .postgres => "NOW()"
  | .datePart u e  => do
      let x ← e.compile
      return match (← read) with
        | .sqlServer => s!"{u.upperName}({x})"
        | .sqlite => s!"CAST(strftime('{u.strftimeFmt}', {x}) AS INTEGER)"
        | .postgres => s!"EXTRACT({u.upperName} FROM {x})"
  | .dateAdd u e n => do
      let x ← e.compile
      match (← read) with
      | .sqlServer => do
          let p ← pushParam (.int n)
          return s!"DATEADD({u.token}, {p}, {x})"
      | .sqlite =>
          let amount := if n ≥ 0 then s!"+{n}" else toString n
          return s!"datetime({x}, '{amount} {u.token}')"
      | .postgres =>
          return s!"({x} + INTERVAL '{n} {u.token}')"
  | .dateDiff u a b => do
      let x ← a.compile
      let y ← b.compile
      return match (← read) with
        | .sqlServer => s!"DATEDIFF({u.token}, {x}, {y})"
        | .sqlite =>
          match u with
          | .day => s!"CAST((julianday({y}) - julianday({x})) AS INTEGER)"
          | .month => s!"CAST(((CAST(strftime('%Y', {y}) AS INTEGER) - CAST(strftime('%Y', {x}) AS INTEGER)) * 12 + (CAST(strftime('%m', {y}) AS INTEGER) - CAST(strftime('%m', {x}) AS INTEGER))) AS INTEGER)"
          | .year => s!"CAST((CAST(strftime('%Y', {y}) AS INTEGER) - CAST(strftime('%Y', {x}) AS INTEGER)) AS INTEGER)"
        | .postgres =>
          match u with
          | .day => s!"EXTRACT(DAY FROM ({y} - {x}))"
          | .month => s!"(EXTRACT(YEAR FROM {y}) - EXTRACT(YEAR FROM {x})) * 12 + (EXTRACT(MONTH FROM {y}) - EXTRACT(MONTH FROM {x}))"
          | .year => s!"(EXTRACT(YEAR FROM {y}) - EXTRACT(YEAR FROM {x}))"

def SqlExprP.compileList :
    List ((p : SqlType) × SqlExpr ts p) → CompileM (List String)
  | [] => pure []
  | ⟨_, e⟩ :: es => return (← e.compile) :: (← SqlExprP.compileList es)

/-- Render a projected row as a SELECT list: `expr AS name` per column. -/
def RowP.selectList : {s : Schema} → Row ts s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e r => do
      let item ← e.compile
      let rest ← r.selectList
      return s!"{item} AS {← quote name}" :: rest

def compileOrderKeyItems : List (OrderKey ts) → CompileM (List String)
  | [] => pure []
  | ⟨_, e, dir⟩ :: ks => do
      let db ← read
      let x ← e.compile
      -- the evaluator (and SQLite/SQL Server) sort NULL smallest; PostgreSQL
      -- defaults to NULLS LAST on ASC — make the placement explicit there
      let nulls := if db == .postgres then
          (if dir == .asc then " NULLS FIRST" else " NULLS LAST") else ""
      let item := s!"{x} {if dir == .asc then "ASC" else "DESC"}{nulls}"
      return item :: (← compileOrderKeyItems ks)

def compileGroupKeyItems : List (KeyExpr ts) → CompileM (List String)
  | [] => pure []
  | ⟨_, e⟩ :: ks => do
      return (← e.compile) :: (← compileGroupKeyItems ks)

/-- Compile a full query. Boundary clauses (DISTINCT, LIMIT, set ops,
GROUP BY) decorate the statement produced by the spine underneath. -/
def QueryP.compileStmt : QueryA ts s → CompileM String
  | .spine sp => sp.compileSpine {} .defaultSel
  -- spines assemble with the DISTINCT flag …
  | .distinctC (.spine sp) => sp.compileSpine { distinct := true } .defaultSel
  -- … other boundary queries become a derived table under a distinct SELECT
  -- (structural recursion forbids `asSpine` here: it can wrap `q`, producing
  -- a larger term)
  | .distinctC (s := s₀) q => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let sel := String.intercalate ", " (← aliasSelect alias s₀)
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
  | .setOpC (s := s₀) op a b => do
      -- operands need structural parenthesization: PostgreSQL/SQL Server
      -- give INTERSECT higher precedence and EXCEPT chains associate left,
      -- so a nested operand compiled flat silently changes meaning — and
      -- SQLite rejects parenthesized compounds, so nesting wraps as a
      -- derived table. Plain spines compile flat with their (dead) ORDER
      -- BY stripped: an operand's order is discarded by the operation.
      let ca ← match a with
        | .spine sp => sp.compileSpine {} .defaultSel
        | qa => do
            let sub ← qa.compileStmt
            let alias ← freshAlias
            let sel := String.intercalate ", " (← aliasSelect alias s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      let cb ← match b with
        | .spine sp => sp.compileSpine {} .defaultSel
        | qb => do
            let sub ← qb.compileStmt
            let alias ← freshAlias
            let sel := String.intercalate ", " (← aliasSelect alias s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      return s!"{ca} {op.token} {cb}"

/-- Walk a comprehension spine accumulating FROM sources, JOIN clauses, and
WHERE conjuncts until the terminal, then assemble one flat SELECT. The third
argument (`SelSpec`) tells a *plain* terminal what to render as its SELECT
list; grouped terminals own their projection and ignore it. -/
def SpineQP.compileSpine : SpineQ ts g s → StmtAcc → SelSpec → CompileM String
  | .yield r, acc, k => do
      let (sel, tail) ← match k with
        | .defaultSel => do
            pure (String.intercalate ", " (← r.selectList), "")
        | .countSel => pure ("COUNT(*)", "")
        | .aggSel op =>
            match r with
            | .cons e .nil => do pure (s!"{op.token}({← e.compile})", "")
            | _ => pure ("", "")   -- unreachable: aggQ spines are single-column
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      return s!"{head} {sel}{renderFroms acc.froms}{renderWheres acc.wheres}{tail}{orderClause}"
  -- the grouped terminal carries its own projection and GROUP BY/HAVING/
  -- ORDER BY tail; the projection spec is plain-only and ignored here
  | .groupYield ks hv ord r, acc, _ => do
      let items ← r.selectList
      let ksStr := String.intercalate ", " (← compileGroupKeyItems ks)
      let hvStr ← match hv with
        | none => pure ""
        | some h => do
            let hs ← predWrap h.isPredicate (← h.compile)
            pure s!" HAVING {hs}"
      let ownOb ← match ord with
        | [] => pure ""
        | _ => do
            pure s!" ORDER BY {String.intercalate ", " (← compileOrderKeyItems ord)}"
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      let gb := if ksStr.isEmpty then "" else s!" GROUP BY {ksStr}"
      return s!"{head} {String.intercalate ", " items}{renderFroms acc.froms}{renderWheres acc.wheres}{gb}{hvStr}{ownOb}{orderClause}"
  | .guard b rest, acc, k => do
      let w ← predWrap b.isPredicate (← b.compile)
      rest.compileSpine { acc with wheres := acc.wheres.push w } k
  | .order ks rest, acc, k => do
      let rendered := String.intercalate ", " (← compileOrderKeyItems ks)
      rest.compileSpine { acc with orders := acc.orders.push rendered } k
  | .fromT (n := nm) (inst := _) _ f, acc, k => do
      let alias ← freshAlias
      let item := s!"{← quote nm} {← quote alias}"
      (f ⟨alias⟩).compileSpine
        { acc with froms := acc.froms.push (false, item) } k
  | .joinT (n := nm) (inst := _) _ on' f, acc, k => do
      let alias ← freshAlias
      let onE := on' ⟨alias⟩
      let onStr ← predWrap onE.isPredicate (← onE.compile)
      let item := s!"{JoinKind.inner.token} {← quote nm} {← quote alias} ON {onStr}"
      (f ⟨alias⟩).compileSpine { acc with froms := acc.froms.push (true, item) } k
  | .joinLeftT (n := nm) (inst := _) _ on' f, acc, k => do
      let alias ← freshAlias
      let onE := on' ⟨alias⟩
      let onStr ← predWrap onE.isPredicate (← onE.compile)
      let item := s!"{JoinKind.left.token} {← quote nm} {← quote alias} ON {onStr}"
      (f ⟨alias⟩).compileSpine { acc with froms := acc.froms.push (true, item) } k
  | .fromQ q f, acc, k => do
      let sub ← q.compileStmt
      let alias ← freshAlias
      let item := s!"({sub}) {← quote alias}"
      (f ⟨alias⟩).compileSpine
        { acc with froms := acc.froms.push (false, item) } k

/-- Compile a scalar aggregate query. -/
def ScalarQueryP.compileScalar : ScalarA ts c → CompileM String
  | .countQ sp => sp.compileSpine {} .countSel
  | .aggQ op sp => sp.compileSpine {} (.aggSel op)

end

/-- Compile a boolean expression for a predicate position. -/
def SqlExprP.compilePred (e : SqlExpr ts c) : CompileM String := do
  predWrap e.isPredicate (← e.compile)

namespace SpineQ
export SpineQP (compileSpine)
end SpineQ

namespace Query
export QueryP (compileStmt)
end Query


private def runCompile (m : CompileM String) (db : DatabaseType) : CompiledSql :=
  let (sql, st) := Id.run ((m.run db).run {})
  { sql, params := st.params }

/-- Compile a query to SQL text plus named parameters for the given dialect. -/
def Query.toSql (q : Query ts s) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile (q AliasOf).compileStmt db

def Query.toSqlite (q : Query ts s) : CompiledSql := q.toSql .sqlite
def Query.toSqlServer (q : Query ts s) : CompiledSql := q.toSql .sqlServer

def Query.toPostgres (q : Query ts s) : CompiledSql := q.toSql .postgres

namespace QueryB
export Query (toSql toSqlite toSqlServer toPostgres)
end QueryB

/-- Compile a scalar query for the given dialect. -/
def ScalarQuery.toSql (sq : ScalarQuery ts c) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile (sq AliasOf).compileScalar db

namespace ScalarB
export ScalarQuery (toSql)
end ScalarB



end LeanLinq
