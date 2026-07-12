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
def SqlExprP.isPredicate : SqlExpr ts c → Bool
  | .cmp .. | .and .. | .or .. | .not .. | .isNull .. | .isNotNull ..
  | .like .. | .inList .. | .inSub .. | .existsSub .. => true
  | .widen e => e.isPredicate
  | _ => false

namespace SqlExpr
export SqlExprP (isPredicate)
end SqlExpr

end LeanLinq
