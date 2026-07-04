import Tests.Queries2
import Tests.StatementsT
import Tests.Basic

/-! # Golden-test runner

Compiles every registered query/statement for all three dialects and compares
against `Tests/golden/{sqlite,sqlserver,postgres}.golden` (one line per case:
`name<TAB>sql<TAB>params`). Regenerate with `lake exe tests -- --update` (or
`lake exe tests --update`), then review the diff. -/

open LeanLinq TQ

def dbName : DatabaseType → String
  | .sqlite => "sqlite"
  | .sqlServer => "sqlserver"
  | .postgres => "postgres"

def renderValue : SqlValue → String
  | .int i => s!"int {i}"
  | .long i => s!"long {i}"
  | .double f => s!"double {f}"
  | .decimal d => s!"decimal {d}"
  | .string s => s!"string {s.quote}"
  | .bool b => s!"bool {b}"
  | .dateTime s => s!"dateTime {s.quote}"
  | .guid g => s!"guid {g.quote}"
  | .null => "null"

def renderLine (name : String) (c : CompiledSql) : String :=
  let ps := String.intercalate "; " (c.params.toList.map fun (n, v) => s!"{n}={renderValue v}")
  s!"{name}\t{c.sql}\t{ps}"

def allCases : List (String × (DatabaseType → CompiledSql)) :=
  queryCases ++ statementCases

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let mut failures := 0
  let mut total := 0
  for db in [DatabaseType.sqlite, DatabaseType.sqlServer, DatabaseType.postgres] do
    let path := s!"Tests/golden/{dbName db}.golden"
    let lines := allCases.map fun (n, f) => renderLine n (f db)
    if update then
      IO.FS.createDirAll "Tests/golden"
      IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")
      IO.println s!"updated {path} ({lines.length} cases)"
    else
      let expected := (← IO.FS.lines path).toList.filter (· ≠ "")
      if expected.length != lines.length then
        IO.eprintln s!"{path}: golden has {expected.length} lines, expected {lines.length} — run with --update"
        failures := failures + 1
      for (got, want) in lines.zip expected do
        total := total + 1
        if got != want then
          failures := failures + 1
          IO.eprintln s!"FAIL [{dbName db}]"
          IO.eprintln s!"  want: {want}"
          IO.eprintln s!"   got: {got}"
  if update then
    return 0
  else if failures == 0 then
    IO.println s!"all {total} golden checks passed ({allCases.length} cases × 3 dialects)"
    return 0
  else
    IO.eprintln s!"{failures} golden checks FAILED"
    return 1
