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
evaluator on swept cases. `none` on unparseable text — never a silent 0. -/
def parseIntText? (txt : String) : Option Int :=
  (String.ofList (txt.toList.takeWhile (· != '.'))).toInt?

private def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Full float text: `[+-]digits[.digits][eE[+-]digits]`, plus
PostgreSQL's `NaN`/`Infinity`/`-Infinity`. `none` on anything else. -/
def parseFloat? (s : String) : Option Float :=
  if s == "NaN" then some (0.0 / 0.0)
  else if s == "Infinity" then some (1.0 / 0.0)
  else if s == "-Infinity" then some (-(1.0 / 0.0))
  else do
    let cs := s.toList
    let (neg, cs) := match cs with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | _ => (false, cs)
    let intPart := cs.takeWhile Char.isDigit
    let cs := cs.drop intPart.length
    let (fracPart, cs) := match cs with
      | '.' :: rest => (rest.takeWhile Char.isDigit, (rest.dropWhile Char.isDigit))
      | _ => ([], cs)
    if intPart.isEmpty && fracPart.isEmpty then none else
    let (expNeg, expDigits, cs) := match cs with
      | 'e' :: rest | 'E' :: rest =>
          match rest with
          | '-' :: r => (true, r.takeWhile Char.isDigit, r.dropWhile Char.isDigit)
          | '+' :: r => (false, r.takeWhile Char.isDigit, r.dropWhile Char.isDigit)
          | r => (false, r.takeWhile Char.isDigit, r.dropWhile Char.isDigit)
      | _ => (false, ['0'], cs)
    if expDigits.isEmpty || !cs.isEmpty then none else
    let mant := digitsToNat (intPart ++ fracPart)
    let exp10 : Int := (if expNeg then -(digitsToNat expDigits : Int)
                        else (digitsToNat expDigits : Int)) - fracPart.length
    let v := if exp10 < 0 then Float.ofScientific mant true (-exp10).toNat
             else Float.ofScientific mant false exp10.toNat
    some (if neg then -v else v)

/-- Decimal text validated before the milli-unit parse: `[+-]digits[.digits]`. -/
def parseDecimal? (txt : String) : Option Int :=
  let cs := match txt.toList with
    | '-' :: rest => rest
    | rest => rest
  let intPart := cs.takeWhile Char.isDigit
  let rest := cs.drop intPart.length
  let ok := match rest with
    | [] => !intPart.isEmpty
    | '.' :: fr => !intPart.isEmpty && !fr.isEmpty && fr.all Char.isDigit
    | _ => false
  if ok then some (parseDecimal txt) else none

/-- Decode one non-NULL text cell at its schema type — **loudly**: wire
text that fails to parse is an error, never a silent zero/false. Bool
accepts the engines' spellings (`t`/`true` from PostgreSQL, `1` from SQL
Server). -/
def parseCell (t : SqlPrim) (txt : String) : Except String (Nullable t) :=
  match t with
  | .int => match parseIntText? txt with
      | some i => .ok (some i)
      | none => .error s!"unreadable int cell text: '{txt}'"
  | .long => match parseIntText? txt with
      | some i => .ok (some i)
      | none => .error s!"unreadable long cell text: '{txt}'"
  | .double => match parseFloat? txt with
      | some f => .ok (some f)
      | none => .error s!"unreadable double cell text: '{txt}'"
  | .decimal => match parseDecimal? txt with
      | some m => .ok (some m)
      | none => .error s!"unreadable decimal cell text: '{txt}'"
  | .string => .ok (some txt)
  | .bool =>
      if txt == "t" || txt == "true" || txt == "1" then .ok (some true)
      else if txt == "f" || txt == "false" || txt == "0" then .ok (some false)
      else .error s!"unreadable bool cell text: '{txt}'"
  | .dateTime => .ok (some (normDateTime txt))
  | .guid => .ok (some txt.toLower)

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
