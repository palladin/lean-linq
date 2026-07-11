import LeanLinq.Eval.Query

/-! # `DbFetch` — database programs with a round-trip budget in the type

The N+1 problem needs the ability to run a query per row of a previous
result. Inside the query language that is unrepresentable (one `Query` value
⇒ one statement); `DbFetch` closes the *host-language* half: a program that
talks to the database carries its round-trip bound as a type index — a
closed numeral for batched programs, an exact data-dependent expression
for per-row loops — and the grading prices composition honestly —

- `fetch` costs `1`;
- `seq` (independent computations) costs `max m n`: a batching driver runs
  both sides in the same rounds;
- `bind` (a data dependency) costs `m + n`: you cannot know what to ask
  until the previous answer arrives.

Execution demands a *bound plus proof*: `exec` takes a budget and an
obligation `r ≤ budget`, auto-discharged by `decide` when the grade is a
closed numeral (every batched program). A data-dependent grade
(`xs.length`) is not decidable at elaboration, so the user proves the
obligation — possible exactly when the collection is in scope at the
door: bound it (`xs.take k`), or compute the budget from it and let
`omega` close the goal. What has no proof is a grade over data that
exists only *inside* the program — rows a previous fetch returned —
which is classic N+1, and it never elaborates. (Haxl repairs N+1
dynamically by batching; the grade rejects it statically instead.)

The loop has first-class sugar: `let ys ← for x in xs do body`
(`DbFetch.forAll`) carries the *exact* dynamic grade `k * xs.length` in
the type — writable wherever `xs` is already in scope, provable with
`omega`-style facts at the door (`by decide` once the list is literal).
No constant-bound variant exists: over just-fetched rows the loop's
grade would mention the fetched value, which `bind` cannot type, so
in-program N+1 stays unwritable and `fetchFor` is the post-fetch door.
Explicit per-row fan-out is for data you already hold.

The reference interpreter here is the in-memory evaluator — the same
denotational semantics the test suite differential-tests — and the native
drivers interpret the same tree against live engines (`execIO`/`execMs`
sequentially; `execPg` through libpq pipeline mode, where `seq` sides and
`forAll` bodies — both independent — share rounds, so the loop *batches*
and the sequential grade is a generous bound). -/

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
  -- the per-row loop, first class: one body per element of a collection
  -- already in hand, with the *exact* data-dependent grade in the index —
  -- `k * xs.length` names the round count precisely (an `∃ n` would hide
  -- the number the budget check needs). Over just-fetched rows it cannot
  -- appear: `bind`'s continuation grade cannot mention the fetched value.
  | forAll : {α β : Type} → {k : Nat} →
      (xs : List α) → (α → DbFetch c k β) → DbFetch c (k * xs.length) (List β)

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
  | _, _, .forAll xs f => xs.mapM fun a => (f a).runWith ee

/-- The execution door: declare a round budget, prove you fit in it. For
closed grades (every batched program) the obligation discharges silently by
`decide`; a data-dependent grade (`xs.length` for runtime `xs`) is not
decidable at elaboration, so the caller supplies the proof — by bounding
the collection or computing the budget from it. A grade over data that
exists only inside the program (just-fetched rows) has no proof to
give: that is N+1, rejected. -/
def exec (f : DbFetch c r α) (budget : Nat) (env : TableEnv c.tables)
    (ps : ParamEnv c.params := by exact .nil) (now : Option String := none)
    (_h : r ≤ budget := by decide) : Except EvalError α :=
  f.runWith ⟨env, ps, now⟩

/-- Restate a grade as a provably equal one — `1 * ids.length` as
`ids.length`, and so on. The index a program *infers* is built
syntactically from the combinators; equalities like `Nat.one_mul` are
theorems, not reductions, so the elaborator will not rewrite them away.
This is the bridge, and `fetch!` applies it automatically: with no
constraint from the context, `rfl` pins the stated grade to the inferred
one; against an annotation, `omega` proves them equal. -/
def withGrade (x : DbFetch c m α) {n : Nat}
    (h : m = n := by first | rfl | omega) : DbFetch c n α :=
  h ▸ x

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

`let x ← e` is `DbFetch.bind`, `let x := e` a plain `let`,
`let ys ← for x in xs do body` is `DbFetch.forAll` (the per-row loop,
exact dynamic grade `k * xs.length`), and the final `return e` is
`DbFetch.pure` — grades compose as `m + n + …`, definitionally the
closed sum for batched programs, so `exec`'s `by decide` discharges
silently. Two niceties keep inferred grades readable: the final
`let ys ← e; return f ys` pair fuses into `map` (no trailing `+ 0`),
and the whole block is wrapped in `withGrade`, so a type annotation may
state any provably equal spelling of the grade — `ids.length` where the
raw index is `1 * ids.length`. -/

syntax (name := fetchBind) "let " ident " ← " term : fetchClause
syntax (name := fetchForAll) "let " ident " ← " "for " ident " in " term:max
  " do " term : fetchClause
syntax (name := fetchLet) "let " ident " := " term : fetchClause
syntax (name := fetchRet) "return " term : fetchClause

scoped syntax (name := fetchProg)
  "fetch! " "{" withoutPosition(sepByIndentSemicolon(fetchClause)) "}" : term

open Lean in
/-- `let ys ← for x in xs do body` also parses as plain `let ys ← term`
(term-position `for`), so the parser emits a `choice` node — resolve it
in favor of the dedicated loop clause. -/
def resolveClause (c : Syntax) : Syntax :=
  if c.getKind == Lean.choiceKind then
    (c.getArgs.find? (·.isOfKind ``fetchForAll)).getD c[0]
  else c

open Lean in
@[macro fetchProg] def expandFetch : Lean.Macro := fun stx => do
  let clauses := (stx[2].getSepArgs.map resolveClause).toList
  match clauses.reverse with
  | [] => Macro.throwError "fetch! must end with a `return` clause"
  | last :: revRest =>
    unless last.isOfKind ``fetchRet do
      Macro.throwErrorAt last "fetch! must end with a `return` clause"
    -- fuse the final `let ys ← e; return f ys` into `map` (grade `r`, not
    -- `r + 0`) so inferred grades stay clean
    let (init, revRest) ← do
      match revRest with
      | prev :: rest =>
        if prev.isOfKind ``fetchBind then
          pure (← `(LeanLinq.DbFetch.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩)) $(⟨prev[3]⟩)), rest)
        else if prev.isOfKind ``fetchForAll then
          pure (← `(LeanLinq.DbFetch.map (fun $(⟨prev[1]⟩) => $(⟨last[1]⟩))
            (LeanLinq.DbFetch.forAll $(⟨prev[6]⟩) (fun $(⟨prev[4]⟩) => $(⟨prev[8]⟩)))), rest)
        else
          pure (← `(LeanLinq.DbFetch.pure $(⟨last[1]⟩)), revRest)
      | [] => pure (← `(LeanLinq.DbFetch.pure $(⟨last[1]⟩)), revRest)
    let folded ← revRest.foldlM (init := init) fun (acc : TSyntax `term) c => do
      if c.isOfKind ``fetchBind then
        `(LeanLinq.DbFetch.bind $(⟨c[3]⟩) (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchForAll then
        -- let y ← for x in xs do body — exact grade k * xs.length
        `(LeanLinq.DbFetch.bind
            (LeanLinq.DbFetch.forAll $(⟨c[6]⟩) (fun $(⟨c[4]⟩) => $(⟨c[8]⟩)))
            (fun $(⟨c[1]⟩) => $acc))
      else if c.isOfKind ``fetchLet then
        `(let $(⟨c[1]⟩) := $(⟨c[3]⟩); $acc)
      else
        Macro.throwErrorAt c "expected `let x ← e`, `let x := e`, `let ys ← for x in xs do e`, or a final `return e`"
    `(LeanLinq.DbFetch.withGrade $folded)

end LeanLinq
