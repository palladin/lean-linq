import LeanLinq.Core.Expr

namespace LeanLinq

def ArithOp.token : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

def CmpOp.token : CmpOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

def AggOp.token : AggOp → String
  | .sum => "SUM" | .avg => "AVG" | .min => "MIN" | .max => "MAX"

def DateUnit.token : DateUnit → String
  | .day => "day" | .month => "month" | .year => "year"

/-- `strftime` format string for a date part (SQLite). -/
def DateUnit.strftimeFmt : DateUnit → String
  | .day => "%d" | .month => "%m" | .year => "%Y"

/-- `EXTRACT` field name (PostgreSQL) / part function (SQL Server). -/
def DateUnit.upperName : DateUnit → String
  | .day => "DAY" | .month => "MONTH" | .year => "YEAR"

/-- Whether a boolean expression is a *predicate* (comparison/logic/…) as
opposed to a BIT-like value (column, parameter, literal, CASE). T-SQL has no
first-class booleans: comparing a predicate requires converting it to a value
first (`CASE WHEN p THEN 1 ELSE 0 END`). -/
def SqlExpr.isPredicate : SqlExpr ts c → Bool
  | .cmp .. | .and .. | .or .. | .not .. | .isNull .. | .isNotNull ..
  | .like .. | .inList .. | .inSub .. => true
  | .widen e => e.isPredicate
  | _ => false

mutual

/-- Render an expression to SQL text for the ambient dialect, allocating a
named parameter for every literal (never inlining values). -/
def SqlExpr.compile : SqlExpr ts c → CompileM String
  | .intC i        => pushParam (.int i)
  | .longC i       => pushParam (.long i)
  | .doubleC f     => pushParam (.double f)
  | .decimalC d    => pushParam (.decimal d)
  | .stringC s     => pushParam (.string s)
  | .boolC b       => pushParam (.bool b)
  | .dateTimeC s   => pushParam (.dateTime s)
  | .guidC g       => pushParam (.guid g)
  | .nullC _       => pure "NULL"
  | .paramE (inst := _) name => refParam name
  | .widen e => e.compile
  | .field _ alias name => do
      if alias.isEmpty then quote name
      else return s!"{← quote alias}.{← quote name}"
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
  | .and a b       => return s!"({← a.compile} AND {← b.compile})"
  | .or a b        => return s!"({← a.compile} OR {← b.compile})"
  | .not a         => return s!"(NOT {← a.compile})"
  | .isNull e      => return s!"{← e.compile} IS NULL"
  | .isNotNull e   => return s!"{← e.compile} IS NOT NULL"
  | .like e p      => return s!"{← e.compile} LIKE {← p.compile}"
  | .inList e es   => return s!"{← e.compile} IN ({String.intercalate ", " (← SqlExpr.compileList es)})"
  | .inSub e sub   => return s!"{← e.compile} IN ({← sub.compile})"
  | .scalarSub sub => return s!"({← sub.compile})"
  | .caseWhen c a b =>
      return s!"CASE WHEN {← c.compile} THEN {← a.compile} ELSE {← b.compile} END"
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

def SqlExpr.compileList :
    List ((p : SqlType) × SqlExpr ts p) → CompileM (List String)
  | [] => pure []
  | ⟨_, e⟩ :: es => return (← e.compile) :: (← SqlExpr.compileList es)

end

end LeanLinq
