import LeanLinq

/-! # Shared text-format cell codecs

PostgreSQL (text result format) and SQL Server (every cell read via
`dbconvert → SYBCHAR`) both move cells as text; these are the common
codecs, aligned with the `SqlPrim.interp` conventions so decoded rows are
cell-for-cell comparable with `Query.run`. -/

namespace LeanLinq.Driver

/-- Integer column text may arrive `numeric`-formatted (`AVG(int)` yields
`325.0000000000000000`); take the integral part. Non-exact integer AVG is
engine-variant and allowlisted, so truncation never disagrees with the
evaluator on swept cases. -/
def parseIntText (txt : String) : Int :=
  ((String.ofList (txt.toList.takeWhile (· != '.'))).toInt?).getD 0

/-- Minimal float parser (`-?digits[.digits]`); the corpus has no double
columns, so scientific notation is out of scope. -/
def parseFloat (s : String) : Float :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let num (l : List Char) : Nat := ((String.ofList l).toNat?).getD 0
  let w := cs.takeWhile (· != '.')
  let f := (cs.dropWhile (· != '.')).drop 1
  let v := Float.ofNat (num w) + Float.ofNat (num f) / Float.ofNat (10 ^ f.length)
  if neg then -v else v

/-- Decode one non-NULL text cell at its schema type. Bool accepts the
engines' spellings (`t`/`true` from PostgreSQL, `1` from SQL Server). -/
def parseCell (t : SqlPrim) (txt : String) : Nullable t :=
  match t with
  | .int => some (parseIntText txt)
  | .long => some (parseIntText txt)
  | .double => some (parseFloat txt)
  | .decimal => some (parseDecimal txt)
  | .string => some txt
  | .bool => some (txt == "t" || txt == "true" || txt == "1")
  | .dateTime => some (normDateTime txt)
  | .guid => some txt.toLower

/-- Render a typed parameter cell as wire text. `1`/`0` for booleans — valid
boolean input text on PostgreSQL and the native form for SQL Server `bit`. -/
def cellText : (t : SqlPrim) → t.interp → String
  | .int, i => toString i
  | .long, i => toString i
  | .double, f => toString f
  | .decimal, m => LeanLinq.renderDecimal m
  | .string, s => s
  | .bool, b => if b then "1" else "0"
  | .dateTime, s => s
  | .guid, g => g

/-- Store a decoded wire cell into its column: a NULL arriving in a NOT
NULL column is a protocol error — the driver refuses what the schema
forbids. -/
def cellFromWire (name : String) (c : SqlType) (v : Nullable c.ty) :
    IO c.interp :=
  match c, v with
  | ⟨_, true⟩, v => pure v
  | ⟨_, false⟩, some x => pure x
  | ⟨_, false⟩, none =>
      throw (IO.userError s!"driver: NULL in NOT NULL column {name}")

end LeanLinq.Driver
