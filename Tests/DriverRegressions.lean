import LeanLinq.Driver.Sqlite
import LeanLinq.Driver.Postgres
import LeanLinq.Driver.Mysql
import Tests.CompilerRegressions
import Tests.GroupedRegressions
import Tests.GroupedAstTyping

/-! Driver boundary regressions. The wire preparation checks need no servers;
SQLite runs against an isolated in-memory database. Expected values are explicit,
so these checks do not depend on the query evaluator sharing driver behavior. -/

open LeanLinq

namespace DriverRegressions

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError s!"driver regression: {label}")

-- Zero signs, subnormal boundaries, normal boundaries, precise fractions,
-- and adjacent values near one. Compare bits rather than Float equality.
private def finiteBits : Array UInt64 := #[
  0, 0x8000000000000000, 1, 0x8000000000000001,
  0x000fffffffffffff, 0x0010000000000000, 0x7fefffffffffffff,
  0xffefffffffffffff, 0x3fb999999999999a, 0x3ff3c0ca4283de1b,
  0x3e7ad7f29abcaf48, 0x3fefffffffffffff, 0x3ff0000000000000,
  0x3ff0000000000001]

private def checkFloatText : IO Unit := do
  for bits in finiteBits do
    let f := Float.ofBits bits
    let literal := Driver.valueText (.double f)
    let named := Driver.cellText .double f
    check (literal == some named) "literal and named double bindings disagree"
    check ((Driver.parseFloat? named).map Float.toBits == some bits)
      s!"double wire text did not round-trip bits {bits}"
  check (Driver.floatText (Float.ofBits 0x7ff0000000000000) == "Infinity") "positive infinity"
  check (Driver.floatText (Float.ofBits 0xfff0000000000000) == "-Infinity") "negative infinity"
  check (Driver.floatText (Float.ofBits 0x7ff8000000000001) == "NaN") "NaN"

private def checkWire : IO Unit := do
  -- Quoted strings/identifiers include escaped delimiters and names that look
  -- like parameters; only the three unquoted occurrences should be rewritten.
  let sql := "SELECT \"x\"\":p1\", `x``:p10`, ':p1'' :p10', :p10 + :p1 + :p10, 1::int"
  let compiled : CompiledSql := { sql, params := #[(":p1", .int 1), (":p10", .int 10)] }
  check (Pg.toWire compiled ==
    "SELECT \"x\"\":p1\", `x``:p10`, ':p1'' :p10', $2 + $1 + $2, 1::int")
    "PostgreSQL rewrote quoted text or lost repeated parameter positions"
  let (mysql, values) ← Mysql.toWire compiled []
  check (mysql ==
    "SELECT \"x\"\":p1\", `x``:p10`, ':p1'' :p10', ? + ? + ?, 1::int")
    "MySQL rewrote quoted text"
  check (values == #[some "10", some "1", some "10"])
    "MySQL parameter occurrence order/count"
  let exact := Float.ofBits 0x3e7ad7f29abcaf48
  let doubles : CompiledSql := {
    sql := "SELECT :literal, :named, :nil, :empty"
    params := #[(":literal", .double exact), (":named", .null),
      (":nil", .null), (":empty", .string "")] }
  let cells : List (String × ((t : SqlPrim) × Nullable t)) :=
    [("named", ⟨.double, some exact⟩), ("nil", ⟨.string, none⟩)]
  let (_, bound) ← Mysql.toWire doubles cells
  check (bound == #[some (Driver.floatText exact), some (Driver.floatText exact), none, some ""])
    "MySQL double/NULL/empty-string bindings"

abbrev FloatCtx : Ctx := { tables := [], params := [("value", .double)] }
abbrev FloatResult : Schema := [("Literal", .double), ("Named", .double)]

private def floatProjection (f : Float) : Query FloatCtx FloatResult := fun _ =>
  .spine (.yield ![(SqlExprP.doubleC f).as "Literal",
    (SqlExpr.param (ts := FloatCtx) "value").as "Named"])

/-- The same literal and named-parameter precision check on every native driver.
These queries have no FROM clause and create or modify no tables. -/
def checkDoubleQueries
    (query : Query FloatCtx FloatResult → ParamEnv FloatCtx.params → IO (List (Values FloatResult)))
    (samples : List Float := [0.1, 1.23456789, 0.0000001, -0.0000001, -123456.789123]) :
    IO Unit := do
  for f in samples do
    let rows ← query (floatProjection f) (.cons f .nil)
    match rows with
    | [.cons literal (.cons named .nil)] =>
        check (literal.toBits == f.toBits && named.toBits == f.toBits)
          s!"native double literal/named parameter lost precision for bits {f.toBits}"
    | _ => throw (IO.userError "driver regression: native double projection row shape")

private def sameRows (got expected : List (Values s)) : Bool :=
  got.length == expected.length && expected.all (fun row => got.count row == expected.count row)

/-- Execute the compiler regressions through each engine, including SQL Server's
predicate-to-value conversion for UNKNOWN, false, and true. The fixture uses a
dedicated test table and does not affect the main differential sweep's seeds. -/
def checkCompilerQueries
    (db : DatabaseType)
    (query : {s : Schema} → Query CompilerRegressions.C s → IO (List (Values s)))
    (execRaw : String → IO Unit) : IO Unit := do
  let quote := db.quoteIdent
  let table := quote "compiler_items"
  execRaw s!"DROP TABLE IF EXISTS {table}; CREATE TABLE {table} ({quote "Id"} INTEGER, {quote "Bucket"} INTEGER, {quote "Value"} INTEGER); INSERT INTO {table} VALUES (1,1,NULL),(2,1,0),(3,2,2)"
  try
    check (sameRows (← query GroupedAstTyping.rawQuery)
      [.cons 11 (.cons 2 (.cons (some 0) .nil)), .cons 12 (.cons 3 (.cons (some 2) .nil))])
      "two computed raw grouping keys retain their positions"
    check (sameRows (← query GroupedRegressions.computedKey)
      [.cons 2 .nil, .cons 3 .nil, .cons 5 .nil]) "named computed grouping key"
    check (sameRows (← query GroupedRegressions.computedLiteralKey)
      [.cons 2 .nil, .cons 3 .nil]) "computed grouping key literal parameter reuse"
    check (sameRows (← query GroupedRegressions.computedKeyAggregate)
      [.cons 2 (.cons (some 3) .nil), .cons 3 (.cons (some 3) .nil)])
      "computed grouping key with SUM, HAVING, and ORDER BY"
    check (sameRows (← query GroupedRegressions.computedKeyCountOnly)
      [.cons (some 2) .nil, .cons (some 1) .nil]) "count-only computed-key grouping"
    check (sameRows (← query GroupedRegressions.computedKeyCase)
      [.cons (some 3) (.cons 12 .nil), .cons (some 6) (.cons 13 .nil)])
      "computed grouping key inside CASE and arithmetic"
    check ((← query GroupedRegressions.constantKey) == [.cons 1 (.cons (some 3) .nil)])
      "constant grouping key"
    check ((← query GroupedRegressions.emptyConstantKey) == [])
      "constant grouping key over an empty source"
    check (sameRows (← query GroupedRegressions.predicateKey)
      [.cons none (.cons (some 1) .nil), .cons (some false) (.cons (some 1) .nil),
       .cons (some true) (.cons (some 1) .nil)]) "predicate grouping key preserves NULL/false/true"
    check (sameRows (← query GroupedRegressions.nonkeyAggregates)
      [.cons 1 (.cons (some 3) (.cons (some 0) .nil)),
       .cons 2 (.cons (some 3) (.cons (some 2) .nil))]) "row-selector aggregates"
    let emptyGroups := CompilerRegressions.source.limit 0
      |>.groupBy (fun r => ![r["Bucket"].as "Bucket"])
      |>.select (fun _ a => ![a.count.as "Count"])
    check ((← query emptyGroups) == []) "grouping a LIMIT 0 source produced a row"
    check (sameRows (← query CompilerRegressions.groupedUnion)
      [.cons 1 (.cons (some 2) .nil), .cons 2 (.cons (some 1) .nil)]) "grouped UNION"
    let expected : List (Values CompilerRegressions.S) := [
      .cons 1 (.cons 1 (.cons none .nil)),
      .cons 2 (.cons 1 (.cons (some 0) .nil)),
      .cons 3 (.cons 2 (.cons (some 2) .nil))]
    for q in [CompilerRegressions.emptyOrder, CompilerRegressions.correlatedExpression,
        CompilerRegressions.correlatedNestedExpression, CompilerRegressions.correlatedProjection] do
      check (sameRows (← query q) expected) "empty ordering or expression correlation"
    check (sameRows (← query CompilerRegressions.predicateProjection)
      [.cons none .nil, .cons (some false) .nil, .cons (some true) .nil])
      "projected predicate lost UNKNOWN/false/true"
    check (sameRows (← query CompilerRegressions.conditionalPredicate)
      [.cons none .nil, .cons (some false) .nil, .cons (some true) .nil])
      "predicate CASE branch lost UNKNOWN/false/true"
    check ((← query CompilerRegressions.comparedPredicate) ==
      [.cons 2 (.cons 1 (.cons (some 0) .nil))])
      "predicate comparison did not preserve UNKNOWN"
    let error ← try
      let _ ← query CompilerRegressions.correlatedSource
      pure ""
    catch e => pure (toString e)
    check (error.startsWith "SQL compilation: correlated derived-table source is unsupported:")
      "driver executed unsupported derived-table correlation"
  finally
    execRaw s!"DROP TABLE {table}"

private abbrev CodecS : Schema := [("I", .long), ("T", .string), ("F", .double)]
private abbrev CodecCtx : Ctx := { tables := [("driver_codec", CodecS)] }
private abbrev NamedCtx : Ctx := {
  tables := CodecCtx.tables
  params := [("number", .long), ("integer", .int), ("text", .string)] }
private def codecTable : Table "driver_codec" CodecS := ⟨⟩

private def emptyGrouped := (Query.from' (ts := CodecCtx) codecTable |>.limit 0)
  |>.groupBy (fun r => ![r["I"].as "I"])
  |>.select (fun _ a => ![a.count.as "Count"])

private def emptyGroupedBudget : Db CodecCtx 1 Nat := db! {
  let rows ← emptyGrouped.execQuery
  let batches ← for row in rows do
    Query.from' (ts := CodecCtx) codecTable |>.execQuery
  return batches.length
}

#guard (Query.gcard emptyGrouped).eval (fun _ => 99) == 0

private def expectRangeError (action : IO α) : IO Unit := do
  let message ← try
    let _ ← action
    pure ""
  catch e => pure (toString e)
  check (message.startsWith "sqlite3 bind: integer outside signed 64-bit range:")
    "out-of-range integer was not rejected during binding"

private def checkSqlite : IO Unit := do
  let conn ← Sqlite.connect ":memory:"
  try
    checkDoubleQueries (fun q ps => conn.query q ps)
    -- Exercise bind_double/column_double across binary64 boundaries, including
    -- negative zero. SQLite's SQL decimal parser varies across versions and
    -- can overflow exact DBL_MAX text; the driver binds doubles in binary.
    checkDoubleQueries (fun q ps => conn.query q ps) (finiteBits.toList.map Float.ofBits)
    checkCompilerQueries .sqlite (fun q => conn.query q) conn.execRaw
    conn.execRaw "CREATE TABLE compiler_quoted (\"a\"\"b\" INTEGER); INSERT INTO compiler_quoted VALUES (7)"
    check ((← conn.query CompilerRegressions.quoted) == [.cons 7 .nil]) "escaped identifier"
    conn.execRaw "CREATE TABLE driver_codec (I INTEGER, T TEXT, F REAL); INSERT INTO driver_codec VALUES (1, '', 0.0)"
    let source : Query CodecCtx CodecS := Query.from' (ts := CodecCtx) codecTable
    let namedFrom : Query NamedCtx CodecS := Query.from' (ts := NamedCtx) codecTable
    let text := "α" ++ String.singleton (Char.ofNat 0) ++ "after" ++ String.singleton (Char.ofNat 0)
    let literalText := source.select (fun _ => ![(SqlExpr.str text).as "S"])
    let namedText : Query NamedCtx [("S", .string)] :=
      namedFrom.select (fun _ => ![(SqlExpr.param (ts := NamedCtx) "text").as "S"])
    let params (i : Int) : ParamEnv NamedCtx.params := .cons i (.cons i (.cons text .nil))
    check ((← conn.query literalText) == [.cons text .nil]) "SQLite literal string with embedded NUL"
    check ((← conn.query namedText (params 0)) == [.cons text .nil]) "SQLite named string with embedded NUL"
    let namedLong : Query NamedCtx [("I", .long)] :=
      namedFrom.select (fun _ => ![(SqlExpr.param (ts := NamedCtx) "number").as "I"])
    let namedInt : Query NamedCtx [("I", .int)] :=
      namedFrom.select (fun _ => ![(SqlExpr.param (ts := NamedCtx) "integer").as "I"])
    for i in [-9223372036854775808, 0, 9223372036854775807] do
      let long := source.select (fun _ => ![(SqlExpr.long i).as "I"])
      let int := source.select (fun _ => ![(SqlExpr.int i).as "I"])
      check ((← conn.query long) == [.cons i .nil]) "SQLite literal long boundary"
      check ((← conn.query int) == [.cons i .nil]) "SQLite literal int boundary"
      check ((← conn.query namedLong (params i)) == [.cons i .nil]) "SQLite named long boundary"
      check ((← conn.query namedInt (params i)) == [.cons i .nil]) "SQLite named int boundary"
    for i in [-9223372036854775809, 9223372036854775808, 2^100] do
      expectRangeError (conn.query (source.select (fun _ => ![(SqlExpr.long i).as "I"])))
      expectRangeError (conn.query (source.select (fun _ => ![(SqlExpr.int i).as "I"])))
      expectRangeError (conn.query namedLong (params i))
      expectRangeError (conn.query namedInt (params i))
    check ((← conn.query emptyGrouped) == []) "grouping an empty source produced a row"
    check ((← emptyGroupedBudget.execIO conn 1) == 0) "empty grouped fetch exceeded its cardinality budget"
    -- Unsupported outer captures must fail compilation before engine access.
    -- A closed connection makes accidental execution observable.
    conn.close
    let error ← try
      let _ ← conn.query CompilerRegressions.outerAggregate
      pure ""
    catch e => pure (toString e)
    check (error.startsWith
      "SQL compilation: invalid aggregate: aggregate arguments cannot capture an outer query row")
      "SQLite executed a query that failed checked compilation"
  finally
    conn.close

def run : IO Unit := do
  checkFloatText
  checkWire
  checkSqlite
  IO.println "driver boundary regressions: all green"

end DriverRegressions
