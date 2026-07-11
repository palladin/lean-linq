import Tests.QueriesC
import Tests.StatementsT
import Tests.Seed
import Tests.SeedSql

/-! # Integration runner

Executes every registered query/statement against live databases:
SQLite (local temp file), PostgreSQL and SQL Server (docker compose services,
driven through `psql`/`sqlcmd` inside the containers). Parameters are inlined
as dialect-escaped literals *for execution only* — the library itself never
inlines. Row results are normalized and checked three ways: against
`Tests/golden/results-{db}.golden` (regenerate with
`lake exe integration --update`); against the *evaluator* — every case's
expected rows are computed by `Query.run` over `seedEnv`, so the engines are
differential-tested against the executable semantics; and against each other
(cross-dialect agreement, modulo a known-variant allowlist — AVG division
semantics).

Usage: `lake exe integration [--db sqlite,postgres,mssql] [--update]` -/

open LeanLinq TQ

/-! ## Parameter inlining (execution only) -/

def sqlLiteral (db : DatabaseType) : SqlValue → String
  | .int i => toString i
  | .long i => toString i
  | .double f => toString f
  | .decimal d => d
  | .string s => s!"'{s.replace "'" "''"}'"
  | .bool b =>
      match db with
      | .postgres => if b then "true" else "false"
      | _ => if b then "1" else "0"
  | .dateTime s =>
      -- PG can't type a bare literal inside EXTRACT(...); a real driver would
      -- bind a typed timestamp parameter here.
      match db with
      | .postgres => s!"TIMESTAMP '{s}'"
      | _ => s!"'{s}'"
  | .guid g => s!"'{g}'"
  | .null => "NULL"

/-- Substitute every parameter placeholder with a literal (longest placeholder
first, so `:p10` is not clobbered by `:p1`). Named parameters (stored with a
`null` placeholder value) resolve from `bindings`. -/
def inlineParams (db : DatabaseType) (c : CompiledSql) : String :=
  let entries := c.params.toList.map fun (name, v) =>
    let v := if v == SqlValue.null then
        ((bindings.lookup ((name.toList.drop 1) |> String.ofList)).getD SqlValue.null)
      else v
    (name, sqlLiteral db v)
  let entries := entries.mergeSort (fun a b => a.1.length ≥ b.1.length)
  entries.foldl (fun sql (n, lit) => sql.replace n lit) c.sql

/-! ## CLI bridges -/

def mssqlPassword := "Test123!Strong"

/-- Run SQL through the dialect's CLI client; returns (success, stdout). -/
def execSql (db : DatabaseType) (sqliteFile : String) (sql : String)
    (database : String := "testdb") : IO (Bool × String) := do
  let (cmd, args) :=
    match db with
    | .sqlite =>
        ("sqlite3", #["-batch", "-cmd", ".separator \"\\t\"", "-cmd", ".nullvalue NULL",
                      sqliteFile, sql])
    | .postgres =>
        ("docker", #["compose", "exec", "-T", "postgres", "psql", "-X",
                     "-U", "testuser", "-d", database, "-v", "ON_ERROR_STOP=1",
                     "-At", "-F", "\t", "-P", "null=NULL", "-c", sql])
    | .sqlServer =>
        ("docker", #["compose", "exec", "-T", "mssql",
                     "/opt/mssql-tools18/bin/sqlcmd", "-C", "-S", "localhost",
                     "-U", "sa", "-P", mssqlPassword, "-d", database,
                     "-h", "-1", "-s", "\t", "-W", "-b",
                     "-Q", s!"SET NOCOUNT ON; {sql}"])
  let out ← IO.Process.output { cmd, args }
  pure (out.exitCode == 0, if out.exitCode == 0 then out.stdout else out.stdout ++ out.stderr)

/-- Check a dialect is reachable. Also catches spawn failures (missing
`sqlite3` or `docker` binary), which otherwise throw instead of skipping. -/
def probe (db : DatabaseType) (sqliteFile : String) : IO Bool := do
  try
    match db with
    | .sqlite =>
        let out ← IO.Process.output { cmd := "sqlite3", args := #["--version"] }
        pure (out.exitCode == 0)
    | .sqlServer =>
        -- also creates testdb on first contact
        let (ok, _) ← execSql db sqliteFile
          "IF DB_ID('testdb') IS NULL CREATE DATABASE testdb" (database := "master")
        pure ok
    | .postgres =>
        let (ok, _) ← execSql db sqliteFile "SELECT 1"
        pure ok
  catch _ => pure false

/-! ## Output normalization -/

def isDigits (s : List Char) : Bool := !s.isEmpty && s.all (·.isDigit)

def looksNumeric (s : String) : Bool :=
  let cs := match s.toList with
    | '-' :: rest => rest
    | cs => cs
  !cs.isEmpty && cs.all (fun c => c.isDigit || c == '.') &&
    (cs.filter (· == '.')).length ≤ 1

def trimTrailingZeros (s : String) : String :=
  if s.contains '.' then
    let t := (s.toList.reverse.dropWhile (· == '0')).reverse
    let t := if t.getLast? == some '.' then t.dropLast else t
    String.ofList t
  else s

def looksDateTime (s : String) : Bool :=
  let cs := s.toList
  s.length ≥ 19 && isDigits (cs.take 4) && cs[4]? == some '-' && cs[7]? == some '-' &&
    (cs[10]? == some ' ' || cs[10]? == some 'T') && cs[13]? == some ':'

def looksGuid (s : String) : Bool :=
  s.length == 36 &&
    (s.toList.zipIdx.all fun (c, i) =>
      if i == 8 || i == 13 || i == 18 || i == 23 then c == '-' else c.isHexDigit)

def normCell (raw : String) : String :=
  let s := raw
  if s == "NULL" then "NULL"
  else if s == "t" || s == "true" || s == "True" then "1"
  else if s == "f" || s == "false" || s == "False" then "0"
  else if looksDateTime s then ((s.toList.take 19).map fun c => if c == 'T' then ' ' else c) |> String.ofList
  else if looksNumeric s then trimTrailingZeros s
  else if looksGuid s then s.toLower
  else s

/-- psql prints command tags (`BEGIN`, `INSERT 0 1`, …) even in tuples-only
mode when `-c` contains multiple statements; drop them. -/
def isCommandTag (l : String) : Bool :=
  l == "BEGIN" || l == "ROLLBACK" || l == "COMMIT" || l == "SET" ||
  (l.startsWith "INSERT " && isDigits ((l.toList.drop 7).filter (· != ' '))) ||
  (l.startsWith "UPDATE " && isDigits (l.toList.drop 7)) ||
  (l.startsWith "DELETE " && isDigits (l.toList.drop 7))

def normalizeOutput (sql : String) (out : String) : String :=
  let lines := (out.splitOn "\n").map (fun l => (l.toList.filter (· != '\r')) |> String.ofList)
  let rows := lines.filter (fun l => l ≠ "" && !isCommandTag l)
  let rows := rows.map fun l => String.intercalate "," ((l.splitOn "\t").map normCell)
  let ordered := (sql.splitOn " ORDER BY ").length > 1
  let rows := if ordered then rows else rows.mergeSort (fun a b => a ≤ b)
  String.intercalate "|" rows

/-! ## Case execution -/

/-- Statement cases verify table state inside a rolled-back transaction. -/
def stmtVerifyTable (name : String) : String :=
  if name == "InsertWithNewColumns" || name == "UpdateWithNewColumns" ||
     name == "InsertWithNewColumnsNull" || name == "UpdateSetNewColumnsNull"
  then "products" else "customers"

def stmtBatch (db : DatabaseType) (name : String) (stmt : String) : String :=
  let table := stmtVerifyTable name
  let verify :=
    match db with
    | .sqlServer => s!"SELECT * FROM [{table}] ORDER BY [Id]"
    | _ => s!"SELECT * FROM \"{table}\" ORDER BY \"Id\""
  match db with
  | .sqlServer => s!"BEGIN TRAN; {stmt}; {verify}; ROLLBACK TRAN;"
  | _ => s!"BEGIN; {stmt}; {verify}; ROLLBACK;"

structure CaseResult where
  name : String
  result : String       -- normalized rows, "<executed>", or "ERROR: …"
  isError : Bool

def runCase (db : DatabaseType) (sqliteFile : String) (isStmt : Bool)
    (name : String) (compiled : CompiledSql) : IO CaseResult := do
  let sql := inlineParams db compiled
  let batch := if isStmt then stmtBatch db name sql else sql
  let (ok, out) ← execSql db sqliteFile batch
  if !ok then
    return { name, result := s!"ERROR: {out.replace "\n" " | "}", isError := true }
  if skipResults.contains name then
    return { name, result := "<executed>", isError := false }
  -- statements: verification SELECT is ordered
  let sqlForOrder := if isStmt then batch else sql
  return { name, result := normalizeOutput sqlForOrder out, isError := false }

def dialects : List (String × DatabaseType) :=
  [("sqlite", .sqlite), ("postgres", .postgres), ("mssql", .sqlServer)]

def goldenPath (dn : String) : String := s!"Tests/golden/results-{dn}.golden"

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let selected :=
    match args.idxOf? "--db" with
    | some i =>
      match args[i+1]? with
      | some csv => csv.splitOn ","
      | none => dialects.map Prod.fst
    | none => dialects.map Prod.fst
  let allNamed : List (Bool × String × Case) :=
    queryCases.map (fun (n, c) => (false, n, c)) ++
    twinCases.map (fun (n, c) => (false, n, c)) ++
    statementCases.map (fun (n, c) => (true, n, c))
  let sqliteFile ← do
    let tmp := s!"/tmp/leanlinq-integration.db"
    if ← System.FilePath.pathExists tmp then IO.FS.removeFile tmp
    pure tmp
  let mut failures := 0
  let mut collected : List (String × List CaseResult) := []
  for (dn, db) in dialects do
    unless selected.contains dn do continue
    unless (← probe db sqliteFile) do
      let hint :=
        if db == DatabaseType.sqlite then "is the `sqlite3` CLI installed?"
        else "is `docker compose up -d --wait` running?"
      IO.eprintln s!"[{dn}] unreachable — skipped ({hint})"
      continue
    let (ok, out) ← execSql db sqliteFile (setupSql db)
    unless ok do
      IO.eprintln s!"[{dn}] schema setup FAILED: {out}"
      failures := failures + 1
      continue
    let mut results : List CaseResult := []
    for (isStmt, name, c) in allNamed do
      let r ← runCase db sqliteFile isStmt name (c.compile db)
      if r.isError then
        failures := failures + 1
        IO.eprintln s!"EXEC FAIL [{dn}] {name}: {r.result}"
      results := results ++ [r]
    collected := collected ++ [(dn, results)]
    -- the evaluator as oracle: expected rows computed by `Query.run` over
    -- `seedEnv` from the same query value that produced the SQL (skipped only
    -- where no single answer exists: time-dependent results self-skip as
    -- `<executed>`, engine-variant cases sit on the allowlist)
    for (entry, r) in allNamed.zip results do
      let (_, name, c) := entry
      if !r.isError && r.result != "<executed>" &&
         !crossDialectAllowlist.contains name then
        let want := c.expected seedEnv
        if want != r.result then
          failures := failures + 1
          IO.eprintln s!"EVAL MISMATCH [{dn}] {name}\n  eval:   {want}\n  engine: {r.result}"
    let lines := results.map fun r => s!"{r.name}\t{r.result}"
    if update then
      if results.any (·.isError) then
        IO.eprintln s!"[{dn}] not updating golden: run had execution errors"
      else
        IO.FS.writeFile (goldenPath dn) (String.intercalate "\n" lines ++ "\n")
        IO.println s!"updated {goldenPath dn} ({lines.length} cases)"
    else
      let expected := (← IO.FS.lines (goldenPath dn)).toList.filter (· ≠ "")
      if expected.length != lines.length then
        IO.eprintln s!"[{dn}] golden has {expected.length} lines, expected {lines.length} — run --update"
        failures := failures + 1
      let mut passed := 0
      for (got, want) in lines.zip expected do
        if got == want then
          passed := passed + 1
        else
          failures := failures + 1
          IO.eprintln s!"FAIL [{dn}]\n  want: {want}\n   got: {got}"
      IO.println s!"[{dn}] {passed}/{lines.length} cases match golden"
  -- cross-dialect comparison against the first dialect that ran
  match collected with
  | (refName, refResults) :: rest =>
    for (dn, results) in rest do
      for ab in refResults.zip results do
        let (a, b) := ab
        if a.name == b.name && !crossDialectAllowlist.contains a.name &&
           !skipResults.contains a.name && !a.isError && !b.isError &&
           a.result != b.result then
          failures := failures + 1
          IO.eprintln s!"CROSS-DIALECT MISMATCH {a.name}: [{refName}] {a.result} ≠ [{dn}] {b.result}"
  | [] => IO.eprintln "no dialect ran"
  if failures == 0 then
    IO.println "integration: all green"
    return 0
  else
    IO.eprintln s!"integration: {failures} failures"
    return 1
