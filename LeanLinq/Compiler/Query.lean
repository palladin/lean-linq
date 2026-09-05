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
  | .groupYield _ _ _ ord _ => !ord.isEmpty
  | .guard _ rest => rest.hasOrder
  | .order ks rest => !ks.isEmpty || rest.hasOrder
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
  | .limitC q lim? _ => lim? != some 0 && q.hasOrderBy
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
argument): the yielded row itself, `COUNT(*)`, or the projected input of a
scalar aggregate. Input modes discard ordering until a LIMIT/OFFSET boundary
requires it. Grouped terminals own their projection. -/
inductive SelSpec : Schema → Type where
  | defaultSel : SelSpec s
  | countSel : SelSpec s
  /-- Intermediate input sources retain their schema names. -/
  | inputSel : SelSpec s
  /-- The final scalar input discards its public name in favor of `value`. -/
  | scalarInputSel : SelSpec [(name, c)]

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

/-- T-SQL predicates need a scalar representation in projections, comparison
operands, CASE branches, and other value positions. Test both truth values:
`ELSE 0` alone would silently turn SQL UNKNOWN into FALSE. Reusing the
rendered text also reuses the parameters already allocated for the predicate. -/
def valueWrap (isPred : Bool) (s : String) : CompileM String := do
  if (← read) == .sqlServer && isPred then
    return s!"CASE WHEN {s} THEN 1 WHEN NOT ({s}) THEN 0 ELSE NULL END"
  else
    return s

/-- The current key binding is total and indexed by its actual schema. -/
structure CompiledGroupKey where
  sql : String
  isPredicate : Bool

inductive GroupKeyEnv : Schema → Type where
  | nil : GroupKeyEnv []
  | cons : CompiledGroupKey → GroupKeyEnv rest → GroupKeyEnv ((name, c) :: rest)

def GroupKeyEnv.get : GroupKeyEnv ks → KeyRef ks c → CompiledGroupKey
  | .cons value _, .here => value
  | .cons _ rest, .there ref => rest.get ref

def GroupKeyEnv.isPredicate (keys : GroupKeyEnv ks) {c : SqlType} (ref : KeyRef ks c) : Bool :=
  (keys.get ref).isPredicate

def GroupKeyEnv.groupByItems : GroupKeyEnv ks → CompileM (List String)
  | .nil => pure []
  | .cons key rest => do
      return (← valueWrap key.isPredicate key.sql) :: (← rest.groupByItems)

/-- Grouped compilation always has an explicit source-projection binding. -/
structure GroupCompileEnv (ks : Schema) where
  projectionAlias : String
  keys : GroupKeyEnv ks

def GroupCompileEnv.get (env : GroupCompileEnv ks) (ref : KeyRef ks c) : CompiledGroupKey :=
  env.keys.get ref

def GroupCompileEnv.isPredicate (env : GroupCompileEnv ks) {c : SqlType} (ref : KeyRef ks c) : Bool :=
  (env.get ref).isPredicate

private def projectGroupValue (alias sql : String) : CompileM String := do
  let name := s!"g{(← get).groupItems.size}"
  modify fun st => { st with groupItems := st.groupItems.push (name, sql) }
  return s!"{← quote alias}.{← quote name}"

/-- MySQL must retain the derived projection through prepared comparisons and
aggregate arguments instead of merging it into the containing statement. -/
private def projectionBarrier : CompileM String := do
  return if (← read) == .mysql then " LIMIT 18446744073709551615" else ""

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
      checkFieldScope row.alias name
      if row.alias.isEmpty then quote name
      else return s!"{← quote row.alias}.{← quote name}"
  | .arith (c := c₀) (numeric := _) op a b  => do
      -- MySQL: `/` on integers yields DECIMAL; integer division is DIV
      let tok := if (← read) == .mysql && op == .div
          && (c₀.ty == .int || c₀.ty == .long)
        then "DIV" else op.token
      return s!"({← valueWrap a.isPredicate (← a.compile)} {tok} {← valueWrap b.isPredicate (← b.compile)})"
  | .concat a b    => do
      -- MySQL: || is logical OR — string concatenation is CONCAT
      if (← read) == .mysql then
        return s!"CONCAT({← a.compile}, {← b.compile})"
      let tok := if (← read) == .sqlServer then "+" else "||"
      return s!"({← a.compile} {tok} {← b.compile})"
  | .cmp op a b => do
      let sa ← valueWrap a.isPredicate (← a.compile)
      let sb ← valueWrap b.isPredicate (← b.compile)
      return s!"({sa} {op.token} {sb})"
  | .and a b       => return s!"({← predWrap a.isPredicate (← a.compile)} AND {← predWrap b.isPredicate (← b.compile)})"
  | .or a b        => return s!"({← predWrap a.isPredicate (← a.compile)} OR {← predWrap b.isPredicate (← b.compile)})"
  | .not a         => return s!"(NOT {← predWrap a.isPredicate (← a.compile)})"
  | .isNull e      => return s!"{← valueWrap e.isPredicate (← e.compile)} IS NULL"
  | .isNotNull e   => return s!"{← valueWrap e.isPredicate (← e.compile)} IS NOT NULL"
  | .like e p      => return s!"{← e.compile} LIKE {← p.compile}"
  -- an empty IN list is invalid SQL (PostgreSQL/SQL Server reject `IN ()`);
  -- SQL's `x IN (empty)` is FALSE without evaluating x, so compile exactly that
  | .inList _ []   => return "(1 = 0)"
  | .inList e es   => return s!"{← valueWrap e.isPredicate (← e.compile)} IN ({String.intercalate ", " (← SqlExprP.compileList es)})"
  | .inSub e sub   => return s!"{← valueWrap e.isPredicate (← e.compile)} IN ({← withCompileStatement sub.compileStmt})"
  | .existsSub sub => return s!"EXISTS ({← withCompileStatement sub.compileStmt})"
  | .scalarSub sub => return s!"({← withCompileStatement sub.compileScalar})"
  | .caseWhen c a b =>
      return s!"CASE WHEN {← predWrap c.isPredicate (← c.compile)} THEN {← valueWrap a.isPredicate (← a.compile)} ELSE {← valueWrap b.isPredicate (← b.compile)} END"
  | .abs (numeric := _) e => return s!"ABS({← valueWrap e.isPredicate (← e.compile)})"
  | .round (numeric := _) e digits => do
      let p ← pushParam (.int digits)
      return s!"ROUND({← valueWrap e.isPredicate (← e.compile)}, {p})"
  | .ceiling (numeric := _) e => do
      let name := match (← read) with
        | .sqlite => "CEIL"
        | _ => "CEILING"
      return s!"{name}({← valueWrap e.isPredicate (← e.compile)})"
  | .floor (numeric := _) e => return s!"FLOOR({← valueWrap e.isPredicate (← e.compile)})"
  | .substring e start len => do
      let db ← read
      let name := if db == .sqlite then "SUBSTR" else "SUBSTRING"
      let len : Int := len
      -- PostgreSQL/SQL Server count positions before the first character
      -- against the requested length; SQLite/MySQL use different native
      -- conventions for zero/negative starts, so lower those explicitly.
      let (start, len) :=
        if (db == .sqlite || db == .mysql) && start ≤ 0 then
          (1, max 0 (len + start - 1))
        else (start, len)
      let p1 ← pushParam (.int start)
      let p2 ← pushParam (.int len)
      return s!"{name}({← e.compile}, {p1}, {p2})"
  | .upper e       => return s!"UPPER({← e.compile})"
  | .lower e       => return s!"LOWER({← e.compile})"
  | .trim e        => return s!"TRIM({← e.compile})"
  | .length e      => do
      -- MySQL LENGTH is bytes; CHAR_LENGTH is characters (the semantics)
      let name := match (← read) with
        | .sqlServer => "LEN"
        | .mysql => "CHAR_LENGTH"
        | _ => "LENGTH"
      return s!"{name}({← e.compile})"
  | .now           =>
      return match (← read) with
        | .sqlServer => "GETDATE()"
        | .sqlite => "datetime('now')"
        | .postgres => "NOW()"
        | .mysql => "NOW()"
  | .datePart u e  => do
      let x ← e.compile
      return match (← read) with
        | .sqlServer => s!"{u.upperName}({x})"
        | .sqlite => s!"CAST(strftime('{u.strftimeFmt}', {x}) AS INTEGER)"
        | .postgres => s!"EXTRACT({u.upperName} FROM {x})"
        | .mysql => s!"EXTRACT({u.upperName} FROM {x})"
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
      | .mysql =>
          return s!"DATE_ADD({x}, INTERVAL {n} {u.token.toUpper})"
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
        | .mysql =>
          -- calendar-component convention (the evaluator's), not
          -- TIMESTAMPDIFF's anniversary counting
          match u with
          | .day => s!"DATEDIFF({y}, {x})"
          | .month => s!"((YEAR({y}) - YEAR({x})) * 12 + (MONTH({y}) - MONTH({x})))"
          | .year => s!"(YEAR({y}) - YEAR({x}))"


def GroupedExprP.compile (keys : GroupCompileEnv ks) :
    GroupedExprP AliasOf ts ks c → CompileM String
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
  | .widen e => e.compile keys
  | .key ref => pure (keys.get ref).sql
  | .arith (c := c₀) (numeric := _) op a b  => do
      -- MySQL: `/` on integers yields DECIMAL; integer division is DIV
      let tok := if (← read) == .mysql && op == .div
          && (c₀.ty == .int || c₀.ty == .long)
        then "DIV" else op.token
      return s!"({← valueWrap (a.isPredicate keys.isPredicate) (← a.compile keys)} {tok} {← valueWrap (b.isPredicate keys.isPredicate) (← b.compile keys)})"
  | .concat a b    => do
      -- MySQL: || is logical OR — string concatenation is CONCAT
      if (← read) == .mysql then
        return s!"CONCAT({← a.compile keys}, {← b.compile keys})"
      let tok := if (← read) == .sqlServer then "+" else "||"
      return s!"({← a.compile keys} {tok} {← b.compile keys})"
  | .cmp op a b => do
      let sa ← valueWrap (a.isPredicate keys.isPredicate) (← a.compile keys)
      let sb ← valueWrap (b.isPredicate keys.isPredicate) (← b.compile keys)
      return s!"({sa} {op.token} {sb})"
  | .and a b       => return s!"({← predWrap (a.isPredicate keys.isPredicate) (← a.compile keys)} AND {← predWrap (b.isPredicate keys.isPredicate) (← b.compile keys)})"
  | .or a b        => return s!"({← predWrap (a.isPredicate keys.isPredicate) (← a.compile keys)} OR {← predWrap (b.isPredicate keys.isPredicate) (← b.compile keys)})"
  | .not a         => return s!"(NOT {← predWrap (a.isPredicate keys.isPredicate) (← a.compile keys)})"
  | .isNull e      => return s!"{← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)} IS NULL"
  | .isNotNull e   => return s!"{← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)} IS NOT NULL"
  | .like e p      => return s!"{← e.compile keys} LIKE {← p.compile keys}"
  -- an empty IN list is invalid SQL (PostgreSQL/SQL Server reject `IN ()`);
  -- SQL's `x IN (empty)` is FALSE without evaluating x, so compile exactly that
  | .inList _ .nil   => return "(1 = 0)"
  | .inList e es   => return s!"{← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)} IN ({String.intercalate ", " (← GroupedExprsP.compileList keys es)})"
  | .caseWhen c a b =>
      return s!"CASE WHEN {← predWrap (c.isPredicate keys.isPredicate) (← c.compile keys)} THEN {← valueWrap (a.isPredicate keys.isPredicate) (← a.compile keys)} ELSE {← valueWrap (b.isPredicate keys.isPredicate) (← b.compile keys)} END"
  | .aggE op e => do
      let sourceArg ← withProjectedSource do valueWrap e.isPredicate (← e.compile)
      let arg ← projectGroupValue keys.projectionAlias sourceArg
      return s!"{op.token}({arg})"
  | .countAll => pure "COUNT(*)"
  | .abs (numeric := _) e => return s!"ABS({← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)})"
  | .round (numeric := _) e digits => do
      let p ← pushParam (.int digits)
      return s!"ROUND({← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)}, {p})"
  | .ceiling (numeric := _) e => do
      let name := match (← read) with
        | .sqlite => "CEIL"
        | _ => "CEILING"
      return s!"{name}({← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)})"
  | .floor (numeric := _) e => return s!"FLOOR({← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)})"
  | .substring e start len => do
      let db ← read
      let name := if db == .sqlite then "SUBSTR" else "SUBSTRING"
      let len : Int := len
      -- PostgreSQL/SQL Server count positions before the first character
      -- against the requested length; SQLite/MySQL use different native
      -- conventions for zero/negative starts, so lower those explicitly.
      let (start, len) :=
        if (db == .sqlite || db == .mysql) && start ≤ 0 then
          (1, max 0 (len + start - 1))
        else (start, len)
      let p1 ← pushParam (.int start)
      let p2 ← pushParam (.int len)
      return s!"{name}({← e.compile keys}, {p1}, {p2})"
  | .upper e       => return s!"UPPER({← e.compile keys})"
  | .lower e       => return s!"LOWER({← e.compile keys})"
  | .trim e        => return s!"TRIM({← e.compile keys})"
  | .length e      => do
      -- MySQL LENGTH is bytes; CHAR_LENGTH is characters (the semantics)
      let name := match (← read) with
        | .sqlServer => "LEN"
        | .mysql => "CHAR_LENGTH"
        | _ => "LENGTH"
      return s!"{name}({← e.compile keys})"
  | .now           =>
      return match (← read) with
        | .sqlServer => "GETDATE()"
        | .sqlite => "datetime('now')"
        | .postgres => "NOW()"
        | .mysql => "NOW()"
  | .datePart u e  => do
      let x ← e.compile keys
      return match (← read) with
        | .sqlServer => s!"{u.upperName}({x})"
        | .sqlite => s!"CAST(strftime('{u.strftimeFmt}', {x}) AS INTEGER)"
        | .postgres => s!"EXTRACT({u.upperName} FROM {x})"
        | .mysql => s!"EXTRACT({u.upperName} FROM {x})"
  | .dateAdd u e n => do
      let x ← e.compile keys
      match (← read) with
      | .sqlServer => do
          let p ← pushParam (.int n)
          return s!"DATEADD({u.token}, {p}, {x})"
      | .sqlite =>
          let amount := if n ≥ 0 then s!"+{n}" else toString n
          return s!"datetime({x}, '{amount} {u.token}')"
      | .postgres =>
          return s!"({x} + INTERVAL '{n} {u.token}')"
      | .mysql =>
          return s!"DATE_ADD({x}, INTERVAL {n} {u.token.toUpper})"
  | .dateDiff u a b => do
      let x ← a.compile keys
      let y ← b.compile keys
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
        | .mysql =>
          -- calendar-component convention (the evaluator's), not
          -- TIMESTAMPDIFF's anniversary counting
          match u with
          | .day => s!"DATEDIFF({y}, {x})"
          | .month => s!"((YEAR({y}) - YEAR({x})) * 12 + (MONTH({y}) - MONTH({x})))"
          | .year => s!"(YEAR({y}) - YEAR({x}))"

def SqlExprP.compileList :
    List ((p : SqlType) × SqlExpr ts p) → CompileM (List String)
  | [] => pure []
  | ⟨_, e⟩ :: es => return (← valueWrap e.isPredicate (← e.compile)) :: (← SqlExprP.compileList es)

/-- Render a projected row as a SELECT list: `expr AS name` per column. -/
def RowP.selectList : {s : Schema} → Row ts s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e r => do
      let item ← valueWrap e.isPredicate (← e.compile)
      let rest ← r.selectList
      return s!"{item} AS {← quote name}" :: rest

def compileOrderKeyItems : List (OrderKey ts) → CompileM (List String)
  | [] => pure []
  | ⟨_, e, dir⟩ :: ks => do
      let db ← read
      let x ← valueWrap e.isPredicate (← e.compile)
      -- the evaluator (and SQLite/SQL Server) sort NULL smallest; PostgreSQL
      -- defaults to NULLS LAST on ASC — make the placement explicit there
      let nulls := if db == .postgres then
          (if dir == .asc then " NULLS FIRST" else " NULLS LAST") else ""
      let item := s!"{x} {if dir == .asc then "ASC" else "DESC"}{nulls}"
      return item :: (← compileOrderKeyItems ks)

/-- Render each key once as a local projected column; lookup remains total. -/
def RowP.compileGroupKeys (alias : String) : Row ts ks → CompileM (GroupKeyEnv ks)
  | .nil => pure .nil
  | .cons e rest => do
      let scalarSql ← withProjectedSource do valueWrap e.isPredicate (← e.compile)
      let sql ← projectGroupValue alias scalarSql
      let tail ← rest.compileGroupKeys alias
      return .cons { sql, isPredicate := false } tail

def GroupedExprsP.compileList (keys : GroupCompileEnv ks) :
    GroupedExprsP AliasOf ts ks → CompileM (List String)
  | .nil => pure []
  | .cons e rest => do
      return (← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)) ::
        (← rest.compileList keys)

def GroupedRowP.selectList (keys : GroupCompileEnv ks) :
    {s : Schema} → GroupedRowP AliasOf ts ks s → CompileM (List String)
  | [], .nil => pure []
  | (name, _) :: _, .cons e rest => do
      let item ← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)
      return s!"{item} AS {← quote name}" :: (← rest.selectList keys)

def GroupedHavingP.compileClause (keys : GroupCompileEnv ks) :
    GroupedHavingP AliasOf ts ks → CompileM String
  | .none => pure ""
  | .some e => do
      return s!" HAVING {← predWrap (e.isPredicate keys.isPredicate) (← e.compile keys)}"

def GroupedOrdersP.compileItems (keys : GroupCompileEnv ks) :
    GroupedOrdersP AliasOf ts ks → CompileM (List String)
  | .nil => pure []
  | .cons e dir rest => do
      let x ← valueWrap (e.isPredicate keys.isPredicate) (← e.compile keys)
      let nulls := if (← read) == .postgres then
          (if dir == .asc then " NULLS FIRST" else " NULLS LAST") else ""
      let item := s!"{x} {if dir == .asc then "ASC" else "DESC"}{nulls}"
      return item :: (← rest.compileItems keys)

/-- Compile a full query. Aggregate inputs discard dead ordering through
projection/DISTINCT boundaries; LIMIT restores ordering needed to choose rows. -/
def QueryP.compileStmt (dropOrders : Bool := false) : QueryA ts s → CompileM String
  | .spine sp => sp.compileSpine {} (if dropOrders then .inputSel else .defaultSel)
  -- spines assemble with the DISTINCT flag …
  | .distinctC (.spine sp) =>
      sp.compileSpine { distinct := true } (if dropOrders then .inputSel else .defaultSel)
  -- … other boundary queries become a derived table under a distinct SELECT
  -- (structural recursion forbids `asSpine` here: it can wrap `q`, producing
  -- a larger term)
  | .distinctC (s := s₀) q => do
      let sub ← withCompileStatement (q.compileStmt dropOrders)
      let alias ← freshAlias
      let sel := String.intercalate ", " (← aliasSelect alias s₀)
      return s!"SELECT DISTINCT {sel} FROM ({sub}) {← quote alias}"
  | .limitC (s := s₀) q lim? off? => do
      let inner ← q.compileStmt false
      match (← read) with
      | .sqlServer =>
          let ob := if q.hasOrderBy then "" else " ORDER BY (SELECT NULL)"
          let offN := off?.getD 0
          -- FETCH requires a positive row count in T-SQL. Keep pagination
          -- legal inside the derived table, then make the outer result empty.
          if lim? == some 0 then
            let alias ← freshAlias
            let sel := String.intercalate ", " (← aliasSelect alias s₀)
            return s!"SELECT TOP (0) {sel} FROM ({inner}{ob} OFFSET {offN} ROWS FETCH NEXT 1 ROWS ONLY) {← quote alias}"
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
      | .mysql =>
          -- MySQL has no bare OFFSET: the documented idiom is a huge LIMIT
          return match lim?, off? with
            | some l, some o => s!"{inner} LIMIT {l} OFFSET {o}"
            | some l, none => s!"{inner} LIMIT {l}"
            | none, some o => s!"{inner} LIMIT 18446744073709551615 OFFSET {o}"
            | none, none => inner
  | .setOpC (s := s₀) op a b => do
      -- operands need structural parenthesization: PostgreSQL/SQL Server
      -- give INTERSECT higher precedence and EXCEPT chains associate left,
      -- so a nested operand compiled flat silently changes meaning — and
      -- SQLite rejects parenthesized compounds, so nesting wraps as a
      -- derived table. Plain spines compile flat with their (dead) ORDER
      -- BY stripped: an operand's order is discarded by the operation.
      let ca ← match a with
        | .spine sp => withCompileStatement (sp.compileSpine {} (if dropOrders then .inputSel else .defaultSel))
        | qa => do
            let sub ← withCompileStatement (qa.compileStmt dropOrders)
            let alias ← freshAlias
            let sel := String.intercalate ", " (← aliasSelect alias s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      let cb ← match b with
        | .spine sp => withCompileStatement (sp.compileSpine {} (if dropOrders then .inputSel else .defaultSel))
        | qb => do
            let sub ← withCompileStatement (qb.compileStmt dropOrders)
            let alias ← freshAlias
            let sel := String.intercalate ", " (← aliasSelect alias s₀)
            pure s!"SELECT {sel} FROM ({sub}) {← quote alias}"
      return s!"{ca} {op.token} {cb}"

/-- Walk a comprehension spine accumulating FROM sources, JOIN clauses, and
WHERE conjuncts until the terminal, then assemble one flat SELECT. The third
argument (`SelSpec`) tells a *plain* terminal what to render as its SELECT
list. Grouped terminals own their projection; input modes also suppress their
dead ordering. -/
def SpineQP.compileSpine : SpineQ ts g s → StmtAcc → SelSpec s → CompileM String
  | .yield r, acc, k => do
      let sel ← match k with
        | .defaultSel | .inputSel => do
            pure (String.intercalate ", " (← r.selectList))
        | .countSel => pure "COUNT(*)"
        | .scalarInputSel => match r with
          | .cons e .nil => do
              let value ← valueWrap e.isPredicate (← e.compile)
              pure s!"{value} AS {← quote "value"}"
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let orderClause :=
        if acc.orders.isEmpty then ""
        else s!" ORDER BY {String.intercalate ", " acc.orders.toList}"
      return s!"{head} {sel}{renderFroms acc.froms}{renderWheres acc.wheres}{orderClause}"
  -- The grouped terminal owns its projection and GROUP BY/HAVING tail.
  -- Input modes discard ORDER BY when no LIMIT needs it.
  | .groupYield rowKeys _ hv ord r, acc, k => do
      let outerItems := (← get).groupItems
      let alias ← freshAlias
      modify fun st => { st with groupItems := #[] }
      let boundKeys ← rowKeys.compileGroupKeys alias
      let keys : GroupCompileEnv _ := { projectionAlias := alias, keys := boundKeys }
      let items ← r.selectList keys
      let ksStr := String.intercalate ", " (← boundKeys.groupByItems)
      let hvStr ← hv.compileClause keys
      let ownOb ← match k with
        | .inputSel | .scalarInputSel => pure ""
        | _ => if ord.isEmpty then pure "" else do
            pure s!" ORDER BY {String.intercalate ", " (← ord.compileItems keys)}"
      let head := if acc.distinct then "SELECT DISTINCT" else "SELECT"
      let innerItems ← (← get).groupItems.toList.mapM fun (name, sql) => do
        pure s!"{sql} AS {← quote name}"
      let inner := s!"SELECT {String.intercalate ", " innerItems}{renderFroms acc.froms}{renderWheres acc.wheres}{← projectionBarrier}"
      modify fun st => { st with groupItems := outerItems }
      return s!"{head} {String.intercalate ", " items} FROM ({inner}) {← quote alias} GROUP BY {ksStr}{hvStr}{ownOb}"
  | .guard b rest, acc, k => do
      let w ← predWrap b.isPredicate (← b.compile)
      rest.compileSpine { acc with wheres := acc.wheres.push w } k
  | .order ks rest, acc, k => do
      if ks.isEmpty then return ← rest.compileSpine acc k
      match k with
      | .countSel => rest.compileSpine acc .countSel
      | .inputSel => rest.compileSpine acc .inputSel
      | .scalarInputSel => rest.compileSpine acc .scalarInputSel
      | .defaultSel =>
          let rendered := String.intercalate ", " (← compileOrderKeyItems ks)
          rest.compileSpine { acc with orders := acc.orders.push rendered } .defaultSel
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
      let dropOrders := match k with | .inputSel | .scalarInputSel => true | _ => false
      let sub ← withDerivedSource (q.compileStmt dropOrders)
      let alias ← freshAlias
      let item := s!"({sub}) {← quote alias}"
      (f ⟨alias⟩).compileSpine
        { acc with froms := acc.froms.push (false, item) } k

/-- Compile a scalar aggregate query. -/
def ScalarQueryP.compileScalar : ScalarA ts c → CompileM String
  | .countQ sp => sp.compileSpine {} .countSel
  | .aggQ op sp => do
      -- Preserve the query's input projection before applying the aggregate.
      -- The operand is now a local column even when its source expression
      -- captures outer rows, so SQL cannot move the aggregate to that scope.
      let input ← withDerivedSource (sp.compileSpine {} .scalarInputSel)
      let alias ← freshAlias
      return s!"SELECT {op.token}({← quote alias}.{← quote "value"}) FROM ({input}{← projectionBarrier}) {← quote alias}"

end

/-- Compile a boolean expression for a predicate position. -/
def SqlExprP.compilePred (e : SqlExpr ts c) : CompileM String := do
  predWrap e.isPredicate (← e.compile)

/-- Compile an expression for a SELECT item or another scalar-value position. -/
def SqlExprP.compileValue (e : SqlExpr ts c) : CompileM String := do
  valueWrap e.isPredicate (← e.compile)

namespace SpineQ
export SpineQP (compileSpine)
end SpineQ

namespace Query
export QueryP (compileStmt)
end Query


private def runCompile (m : CompileM String) (db : DatabaseType) : CompiledSql :=
  let (sql, st) := Id.run ((m.run db).run {})
  { sql, params := st.params }

/-- Run compilation and reject unsupported SQL before handing it to a driver. -/
def runCompileChecked (m : CompileM String) (db : DatabaseType) : Except CompileError CompiledSql :=
  let (sql, st) := Id.run ((m.run db).run {})
  match st.error? with
  | some e => .error e
  | none => .ok { sql, params := st.params }

/-- Low-level, unchecked SQL rendering retained for inspection and compatibility.
Use `toSqlChecked` for executable SQL; native drivers use the checked path. -/
def Query.toSql (q : Query ts s) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile (q AliasOf).compileStmt db

/-- Compile a query, reporting unsupported correlated FROM sources explicitly. -/
def Query.toSqlChecked (q : Query ts s) (db : DatabaseType := .sqlite) : Except CompileError CompiledSql :=
  runCompileChecked (q AliasOf).compileStmt db

def Query.toSqlite (q : Query ts s) : CompiledSql := q.toSql .sqlite
def Query.toSqlServer (q : Query ts s) : CompiledSql := q.toSql .sqlServer
def Query.toMysql (q : Query ts s) : CompiledSql := q.toSql .mysql

def Query.toPostgres (q : Query ts s) : CompiledSql := q.toSql .postgres

namespace QueryB
export Query (toSql toSqlChecked toSqlite toSqlServer toPostgres)
end QueryB

/-- Compile a scalar query for the given dialect. -/
def ScalarQuery.toSql (sq : ScalarQuery ts c) (db : DatabaseType := .sqlite) : CompiledSql :=
  runCompile (sq AliasOf).compileScalar db

def ScalarQuery.toSqlChecked (sq : ScalarQuery ts c) (db : DatabaseType := .sqlite) : Except CompileError CompiledSql :=
  runCompileChecked (sq AliasOf).compileScalar db

namespace ScalarB
export ScalarQuery (toSql toSqlChecked)
end ScalarB



end LeanLinq
