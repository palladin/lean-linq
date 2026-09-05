import LeanLinq

/-! Placeholder translation for SQL emitted by the compiler. Quoted identifiers
and string literals are SQL text, even when they contain a parameter's name. -/

namespace LeanLinq.Driver

private partial def scanParams (entries : List (String × String)) :
    List Char → Option Char → List Char → Array String → String × Array String
  | [], _, acc, names => (String.ofList acc.reverse, names)
  | c :: cs, some quote, acc, names =>
      if c == quote then
        match cs with
        | d :: ds =>
            if d == quote then scanParams entries ds (some quote) (d :: c :: acc) names
            else scanParams entries cs none (c :: acc) names
        | [] => scanParams entries cs none (c :: acc) names
      else scanParams entries cs (some quote) (c :: acc) names
  | c :: cs, none, acc, names =>
      if c == '\'' || c == '"' || c == '`' then
        scanParams entries cs (some c) (c :: acc) names
      else if c == ':' then
        -- A PostgreSQL cast is not a named parameter.
        match cs with
        | ':' :: rest => scanParams entries rest none (':' :: ':' :: acc) names
        | _ =>
            let tail := String.ofList (c :: cs)
            match entries.find? (fun (name, _) => tail.startsWith name) with
            | some (name, replacement) =>
                scanParams entries (cs.drop (name.length - 1)) none
                  (replacement.toList.reverse ++ acc) (names.push name)
            | none => scanParams entries cs none (c :: acc) names
      else scanParams entries cs none (c :: acc) names

/-- Replace named placeholders outside SQL quotes, returning the names in
occurrence order. Doubled quote delimiters are preserved. The compiler emits
standard quoted strings/identifiers; this is not a parser for arbitrary raw SQL.
Longest-name-first matching keeps `:p1` distinct from `:p10`. -/
def rewriteParams (sql : String) (entries : List (String × String)) :
    String × Array String :=
  scanParams (entries.mergeSort (fun a b => a.1.length ≥ b.1.length))
    sql.toList none [] #[]

end LeanLinq.Driver
