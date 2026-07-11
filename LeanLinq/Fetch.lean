import LeanLinq.Eval.Query

/-! # `DbFetch` — database programs with a round-trip budget in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `DbFetch` closes the *host-language* half: a program that
talks to the database carries a static upper bound on its round trips as a
type index, and the grading prices composition honestly —

- `fetch` costs `1`;
- `seq` (independent computations) costs `max m n`: a batching driver runs
  both sides in the same rounds;
- `bind` (a data dependency) costs `m + n`: you cannot know what to ask
  until the previous answer arrives.

Execution demands a *bound plus proof*: `exec` takes a budget and an
obligation `r ≤ budget`, auto-discharged by `decide` when the grade is a
closed numeral (every batched program). Because Lean is dependently typed, a
per-row loop over a runtime collection *is* writable — its grade is
`xs.length` — but at `exec` the obligation `xs.length ≤ budget` is not
decidable at elaboration and must be **proved by the user**, which is only
possible after explicitly bounding the collection (`xs.take k`). Unbounded
data-dependent fan-out — classic N+1 — admits no proof, so it never
elaborates. (Haxl repairs N+1 dynamically by batching; the grade rejects it
statically instead.)

The interpreter here is the in-memory evaluator — the same denotational
semantics the integration suite differential-tests — so `DbFetch` programs
run today; a future IO driver interprets the same tree against live engines,
batching `seq` for real. -/

/-! `fetch!` do-sugar (declared before the namespace: syntax categories
must live at top level for quotation patterns to work). -/
declare_syntax_cat fetchClause

namespace LeanLinq

/-- A database program with result type `α` and at most `r` round trips. -/
inductive DbFetch (c : Ctx) : Nat → Type → Type 1 where
  | pure : {α : Type} → α → DbFetch c 0 α
  | fetch : {s : Schema} → Query c s → DbFetch c 1 (List (Values s))
  | fetchCell : {t : SqlType} → ScalarQuery c t → DbFetch c 1 (Nullable t)
  -- independent computations: a batching driver shares their rounds
  | seq : {m n : Nat} → {α β : Type} →
      DbFetch c m (α → β) → DbFetch c n α → DbFetch c (max m n) β
  -- a data dependency genuinely costs rounds
  | bind : {m n : Nat} → {α β : Type} →
      DbFetch c m α → (α → DbFetch c n β) → DbFetch c (m + n) β

namespace DbFetch

def map (f : α → β) (x : DbFetch c r α) : DbFetch c r β :=
  x.bind (fun a => .pure (f a))

/-- Reference interpreter: the in-memory evaluator. Total — `DbFetch` is a
reflexive inductive, so structural recursion covers the `bind`
continuation applied to any value. -/
def runWith (ee : EvalEnv c) : {r : Nat} → {α : Type} → DbFetch c r α →
    Except EvalError α
  | _, _, .pure a => Except.ok a
  | _, _, .fetch q => q.evalRows ee
  | _, _, .fetchCell sq => sq.evalCell ee
  | _, _, .seq f x => do Except.ok ((← f.runWith ee) (← x.runWith ee))
  | _, _, .bind x k => do (k (← x.runWith ee)).runWith ee

/-- The execution door: declare a round budget, prove you fit in it. For
closed grades (every batched program) the obligation discharges silently by
`decide`; a data-dependent grade (`xs.length` for runtime `xs`) is not
decidable at elaboration, so the caller must bound the collection and
supply the proof — unbounded N+1 has no proof to give. -/
def exec (f : DbFetch c r α) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    (_h : r ≤ budget := by decide) : Except EvalError α :=
  f.runWith ⟨env, ps, now⟩

end DbFetch

/-- Inject a runtime value as a literal expression (the bridge `fetchFor`
uses to turn a runtime key set into one `IN (…)` list). -/
class SqlLit (t : SqlType) where
  lit : {c : Ctx} → t.interp → SqlExpr c t

instance : SqlLit .int := ⟨.intC⟩
instance : SqlLit .long := ⟨.longC⟩
instance : SqlLit .double := ⟨.doubleC⟩
instance : SqlLit .decimal := ⟨fun m => .decimalC (renderDecimal m)⟩
instance : SqlLit .string := ⟨.stringC⟩
instance : SqlLit .bool := ⟨.boolC⟩
instance : SqlLit .dateTime := ⟨.dateTimeC⟩
instance : SqlLit .guid := ⟨.guidC⟩

/-- The batched door: fetch for a whole runtime key set in **one** round —
the keys become an `IN (…)` list inside a single statement, so a thousand
parents still cost grade 1. This is how N+1 collapses to 1+1. -/
def DbFetch.fetchFor [SqlLit t] (keys : List t.interp)
    (mk : List (SqlExpr c t) → Query c s) : DbFetch c 1 (List (Values s)) :=
  .fetch (mk (keys.map SqlLit.lit))

/-! ## `fetch!` — do-notation for the graded monad

`DbFetch` cannot be a `Monad` instance: its bind *changes the index*
(`m + n`), and hiding the grade to fit `Monad`'s fixed `m : Type → Type`
would blind `exec`'s budget check — the entire point. So the sugar is a
macro (the `query!` precedent): do-shaped clauses desugar to the graded
combinators and elaboration infers the grade.

```
def report : DbFetch c 2 _ := fetch! {
  let parents ← .fetch parentsQ
  let ids := extract parents
  let children ← .fetchFor ids childrenQ
  return (parents, children)
}
```

`let x ← e` is `DbFetch.bind`, `let x := e` a plain `let`, and the final
`return e` is `DbFetch.pure` — grades compose as `m + n + … + 0`, which is
definitionally the closed sum for batched programs, so `exec`'s `by decide`
still discharges silently. -/

syntax (name := fetchBind) "let " ident " ← " term : fetchClause
syntax (name := fetchLet) "let " ident " := " term : fetchClause
syntax (name := fetchRet) "return " term : fetchClause

scoped syntax (name := fetchProg)
  "fetch! " "{" withoutPosition(sepByIndentSemicolon(fetchClause)) "}" : term

open Lean in
@[macro fetchProg] def expandFetch : Lean.Macro := fun stx => do
  let clauses := stx[2].getSepArgs.toList
  match clauses.reverse with
  | [] => Macro.throwError "fetch! must end with a `return` clause"
  | last :: revRest =>
    unless last.isOfKind ``fetchRet do
      Macro.throwErrorAt last "fetch! must end with a `return` clause"
    let init ← `(LeanLinq.DbFetch.pure $(⟨last[1]⟩))
    let folded ← revRest.foldlM (init := init) fun (acc : TSyntax `term) c => do
      if c.isOfKind ``fetchBind then
        `(LeanLinq.DbFetch.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchLet then
        `(let $(⟨c[1]⟩) := $(⟨c[3]⟩); $acc)
      else
        Macro.throwErrorAt c "expected `let x ← e`, `let x := e`, or a final `return e`"
    return folded

end LeanLinq
