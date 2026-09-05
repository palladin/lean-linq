import LeanLinq.Core.Value

namespace LeanLinq

/-- Unsupported SQL shapes are explicit failures at checked compilation and
native execution boundaries; the evaluator may still interpret the tree. -/
inductive CompileError where
  | correlatedDerivedTable (alias column : String)
  | invalidAggregate (reason : String)
  | invalidGrouping (reason : String)
  deriving Repr, BEq

instance : ToString CompileError where
  toString
    | .correlatedDerivedTable alias column =>
        s!"correlated derived-table source is unsupported: {alias}.{column} references a source in the containing statement"
    | .invalidAggregate reason => s!"invalid aggregate: {reason}"
    | .invalidGrouping reason => s!"invalid grouping: {reason}"

/-- Preprojection for grouping keys that must become real columns before
grouping, rather than repeated parameterized expressions. -/
structure GroupProjection where
  alias : String
  items : Array (String × String) := #[]

/-- State threaded through SQL generation: a counter for source aliases and
the accumulated named parameters. -/
structure CompileState where
  aliasCounter : Nat := 0
  params : Array (String × SqlValue) := #[]
  /-- First alias allocated in the statement currently being rendered. -/
  statementStart : Nat := 0
  /-- Sibling aliases that a non-lateral derived table cannot reference.
  Outer expression-subquery scopes remain visible and are not in this range. -/
  forbiddenAliases : List (Nat × Nat) := []
  derivedDepth : Nat := 0
  allowAggregate : Bool := false
  inAggregate : Bool := false
  /-- Aggregate argument ownership survives nested expression subqueries.
  `inAggregate` separately tracks nesting within the current SQL statement. -/
  aggregateOwners : List Nat := []
  /-- Rendered explicit grouping keys in the current grouped statement.
  Reusing their SQL preserves parameter identity for computed keys. -/
  groupKeySql : Option (List (Nat × String)) := none
  groupProjection : Option GroupProjection := none
  error? : Option CompileError := none

/-- Compilation reads the target dialect and threads `CompileState`. -/
abbrev CompileM := ReaderT DatabaseType (StateM CompileState)

def recordCompileError (e : CompileError) : CompileM Unit :=
  modify fun st => { st with error? := st.error?.or (some e) }

/-- A nested SELECT has its own local FROM scope, while ordinary expression
subqueries can still capture sources in the enclosing query. -/
def withCompileStatement (m : CompileM α) : CompileM α := do
  let outer ← get
  modify fun st => { st with
    statementStart := st.aliasCounter
    allowAggregate := false
    inAggregate := false
    groupKeySql := none
    groupProjection := none }
  let result ← m
  modify fun st => { st with
    statementStart := outer.statementStart
    allowAggregate := outer.allowAggregate
    inAggregate := outer.inAggregate
    groupKeySql := outer.groupKeySql
    groupProjection := outer.groupProjection }
  return result

/-- FROM-derived tables cannot capture sibling FROM sources without LATERAL
or APPLY. Keep their forbidden scopes through any expression subqueries. -/
def withDerivedSource (m : CompileM α) : CompileM α := do
  let outer ← get
  modify fun st => { st with
    statementStart := st.aliasCounter
    forbiddenAliases := (outer.statementStart, outer.aliasCounter) :: outer.forbiddenAliases
    derivedDepth := outer.derivedDepth + 1
    allowAggregate := false, inAggregate := false, groupKeySql := none
    groupProjection := none }
  let result ← m
  modify fun st => { st with
    statementStart := outer.statementStart
    forbiddenAliases := outer.forbiddenAliases
    derivedDepth := outer.derivedDepth
    allowAggregate := outer.allowAggregate, inAggregate := outer.inAggregate
    groupKeySql := outer.groupKeySql
    groupProjection := outer.groupProjection }
  return result

/-- Key expressions and aggregate arguments belong to the source projection,
so their own children must compile against the original source aliases. -/
def withoutGroupProjection (m : CompileM α) : CompileM α := do
  let outer := (← get).groupProjection
  modify fun st => { st with groupProjection := none }
  let result ← m
  modify fun st => { st with groupProjection := outer }
  return result

def checkFieldScope (alias column : String) : CompileM Unit := do
  let st ← get
  let index? := if alias.startsWith "a" then (alias.drop 1).toString.toNat? else none
  let forbidden : Bool :=
    if alias.isEmpty then st.derivedDepth > 0
    else match index? with
      | none => false
      | some n => st.forbiddenAliases.any (fun (lo, hi) => lo ≤ n && n < hi)
  if forbidden then recordCompileError (.correlatedDerivedTable alias column)
  -- SQL can hoist an aggregate whose argument only mentions outer rows to
  -- that outer query, changing even its empty-input cardinality. Conservatively
  -- reject all outer captures inside aggregate arguments; correlations in
  -- the scalar query's WHERE/ON remain supported.
  let outerAggregate : Bool := st.aggregateOwners.any fun owner =>
    alias.isEmpty || index?.any (· < owner)
  if outerAggregate then
    recordCompileError (.invalidAggregate "aggregate arguments cannot capture an outer query row")

def withAggregateContext (allowed : Bool) (m : CompileM α) : CompileM α := do
  let previous := (← get).allowAggregate
  modify fun st => { st with allowAggregate := allowed }
  let result ← m
  modify fun st => { st with allowAggregate := previous }
  return result

def withAggregateArgument (m : CompileM α) : CompileM α := do
  let outer ← get
  modify fun st => { st with
    inAggregate := true
    aggregateOwners := st.statementStart :: st.aggregateOwners }
  let result ← m
  modify fun st => { st with
    inAggregate := outer.inAggregate
    aggregateOwners := outer.aggregateOwners }
  return result

def checkAggregate : CompileM Unit := do
  let st ← get
  if st.inAggregate then
    recordCompileError (.invalidAggregate "aggregate functions cannot be nested")
  else if !st.allowAggregate then
    recordCompileError (.invalidAggregate "aggregate outside grouped SELECT, HAVING, or ORDER BY")

/-- Allocate a fresh source alias: `a0`, `a1`, … -/
def freshAlias : CompileM String := fun _ =>
  modifyGet fun st =>
    (s!"a{st.aliasCounter}", { st with aliasCounter := st.aliasCounter + 1 })

/-- Parameter prefix: `@` for SQL Server, `:` for SQLite/PostgreSQL. -/
def DatabaseType.paramPrefix : DatabaseType → String
  | .sqlServer => "@"
  | _ => ":"

/-- Quote an identifier: `[x]` for SQL Server, `"x"` for SQLite/PostgreSQL. -/
def DatabaseType.quoteIdent (db : DatabaseType) (s : String) : String :=
  match db with
  | .sqlServer => "[" ++ s.replace "]" "]]" ++ "]"
  | .mysql => "`" ++ s.replace "`" "``" ++ "`"
  | _ => "\"" ++ s.replace "\"" "\"\"" ++ "\""

def quote (s : String) : CompileM String := fun db => pure (db.quoteIdent s)

/-- Allocate an auto-named parameter (`@p0` / `:p0`) for a literal value and
return its placeholder. -/
def pushParam (v : SqlValue) : CompileM String := fun db =>
  modifyGet fun st =>
    let name := s!"{db.paramPrefix}p{st.params.size}"
    (name, { st with params := st.params.push (name, v) })

/-- Reference a user-named parameter (`@minAge` / `:minAge`). Its value is
supplied at execution time, so it is recorded with a `null` placeholder;
repeated references record it once. -/
def refParam (name : String) : CompileM String := fun db =>
  modifyGet fun st =>
    let full := s!"{db.paramPrefix}{name}"
    if st.params.any (·.1 == full) then (full, st)
    else (full, { st with params := st.params.push (full, .null) })

/-- The result of compiling a query or statement: SQL text plus its named
parameters. Two kinds share the array:

- **auto parameters** (`p0, p1, …`, one per literal in the AST) carry
  their values here. They are a *compilation artifact*: the evaluator
  never sees them — it evaluates the literal constructors directly —
  and they exist so a value never appears inside the SQL text. That is
  the injection guarantee, and also what lets engines reuse one
  prepared plan across literal values and lets values travel through
  typed bind APIs (OIDs, declarations) instead of string escaping.
- **user parameters** (declared in `Ctx.params`) are recorded with a
  `null` placeholder meaning "supplied at execution": drivers bind
  them by name from the same typed `ParamEnv` the evaluator reads.

Data travels as data; only structure travels as text. -/
structure CompiledSql where
  sql : String
  params : Array (String × SqlValue)
  deriving Repr, BEq

end LeanLinq
