import LeanLinq.Core.Expr
import LeanLinq.Compiler.Monad

namespace LeanLinq

/-- Render an expression to SQL text, allocating a named parameter for every
literal (never inlining values into the SQL string). -/
def SqlExpr.compile : SqlExpr t → CompileM String
  | .intC i        => pushParam (.int i)
  | .boolC b       => pushParam (.bool b)
  | .stringC s     => pushParam (.string s)
  | .plus a b      => return s!"({← a.compile} + {← b.compile})"
  | .concat a b    => return s!"({← a.compile} || {← b.compile})"
  | .eq a b        => return s!"({← a.compile} = {← b.compile})"
  | .lt a b        => return s!"({← a.compile} < {← b.compile})"
  | .and a b       => return s!"({← a.compile} AND {← b.compile})"
  | .or a b        => return s!"({← a.compile} OR {← b.compile})"
  | .not a         => return s!"(NOT {← a.compile})"
  | .field _ alias name => pure s!"{alias}.{name}"

end LeanLinq
