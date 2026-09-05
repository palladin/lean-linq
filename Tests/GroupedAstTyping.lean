import Tests.CompilerRegressions

/-! Grouping invariants hold in the raw AST, independently of private wrappers.
Key references and environments have the same schema, and ordinary row
expressions cannot contain a grouped key or aggregate. -/

namespace GroupedAstTyping
open LeanLinq

abbrev S := CompilerRegressions.S
abbrev C := CompilerRegressions.C
abbrev KS : Schema := [("Bucket", .int)]
def rows := CompilerRegressions.items

-- The old ordinary-expression escape hatches no longer exist.
#check_failure SqlExprP.groupKey
#check_failure SqlExprP.aggE
#check_failure SqlExprP.countAll
#check_failure GroupedExprP.field

def groupedKey : GroupedExprP AliasOf C KS .int := .key .here
def groupedCount : GroupedExprP AliasOf C KS .int := .countAll
def groupedSum : GroupedExprP AliasOf C KS (.null .int) := .aggE .sum (.intC 1)
def groupedPredicate : GroupedExprP AliasOf C KS (.null .bool) :=
  .cmp .gt (.widen .countAll) (.widen (.intC 0))
def groupedRow : GroupedRowP AliasOf C KS [("Count", .int)] :=
  .cons groupedCount .nil
def keys : RowP AliasOf C KS := .cons (.intC 1) .nil
def groupedSpine : SpineQP AliasOf C .grouped [("Count", .int)] :=
  .groupYield keys (by decide) (.some groupedPredicate)
    (.cons groupedKey .asc .nil) groupedRow

-- A grouped value is neither a row expression nor an aggregate operand.
#check_failure (groupedKey : SqlExpr C .int)
#check_failure (groupedCount : SqlExpr C .int)
#check_failure (GroupedExprP.aggE .sum groupedSum : GroupedExprP AliasOf C KS (.null .int))
#check_failure (GroupedExprP.aggE .sum groupedKey : GroupedExprP AliasOf C KS (.null .int))
#check_failure (RowP.cons groupedCount RowP.nil : RowP AliasOf C [("Count", .int)])
#check_failure (SpineQP.yield groupedRow : SpineQP AliasOf C .plain [("Count", .int)])
#check_failure (SpineQP.guard groupedPredicate (.yield (RowP.nil : RowP AliasOf C [])))
#check_failure (OrderKeyP.mk .int groupedCount .asc : OrderKeyP AliasOf C)

-- Raw grouped terminals require grouped projections, HAVING, and ordering.
#check_failure (SpineQP.groupYield keys (by decide) .none .nil
  (RowP.nil : RowP AliasOf C []) : SpineQP AliasOf C .grouped [])
#check_failure (SpineQP.groupYield keys (by decide)
  (.some (SqlExprP.widen (.boolC true))) .nil groupedRow)
#check_failure (SpineQP.groupYield keys (by decide) .none
  [((SqlExpr.int 1 : SqlExpr C .int).asc)] groupedRow)

-- Empty ordering still cannot wrap a grouped terminal. The plain positive
-- control prevents an unrelated constructor-name failure from passing this.
example : SpineQP AliasOf C .plain [] := .order [] (.yield .nil)
#check_failure (SpineQP.order [] groupedSpine)

-- A group's expression schema must match the keys supplied by that terminal.
#check_failure (SpineQP.groupYield
  (RowP.cons (.intC 2) .nil : RowP AliasOf C [("Other", .int)])
  (by decide) .none .nil groupedRow)
#check_failure (GroupedExprP.key (KeyRef.here : KeyRef KS .int) :
  GroupedExprP AliasOf C [("Other", .int)] .int)

abbrev TwoKeys : Schema := [("Number", .int), ("Text", .null .string)]
def secondKey : KeyRef TwoKeys (.null .string) := .there .here
def keyValues : Values TwoKeys := .cons 7 (.cons (some "second") .nil)

-- Key lookup consumes a complete heterogeneous environment and returns its
-- declared cell directly. There is no missing-key result or default value.
example {ks : Schema} {c : SqlType} : KeyRef ks c → Values ks → c.interp :=
  KeyRef.getValues
#guard KeyRef.getValues secondKey keyValues == some "second"
#guard KeyRef.getValues secondKey (.cons 7 (.cons none .nil)) == none
#guard KeyRef.getValues (KeyRef.here : KeyRef TwoKeys .int) keyValues == 7
#check_failure (KeyRef.here : KeyRef [] .int)
#check_failure (KeyRef.here : KeyRef TwoKeys .string)
#check_failure (KeyRef.there (KeyRef.there KeyRef.here) : KeyRef TwoKeys .int)
#check_failure (KeyRef.getValues secondKey Values.nil)
#check_failure (KeyRef.getValues secondKey (.cons 7 .nil))

-- Generated wrapper recursors can expose only the intrinsic grouped AST.
-- These successful extractors ensure the following failures exercise the
-- extracted value's type, rather than relying on accessor privacy.
noncomputable def extractExpr {κ : Type} {ρ : Schema → Type} {ks : Schema} {c : SqlType}
    (e : GroupExprP κ ρ C ks c) : GroupedExprP ρ C ks c :=
  GroupExprP.rec (motive := fun _ => GroupedExprP ρ C ks c) (fun raw => raw) e
noncomputable def extractRow {κ : Type} {ρ : Schema → Type} {ks s : Schema}
    (r : GroupRowP κ ρ C ks s) : GroupedRowP ρ C ks s :=
  GroupRowP.rec (motive := fun _ => GroupedRowP ρ C ks s) (fun raw => raw) r

#check_failure (fun e : GroupExprP Unit AliasOf C KS .int =>
  (extractExpr e : SqlExpr C .int))
#check_failure (fun r : GroupRowP Unit AliasOf C KS [("Count", .int)] =>
  (extractRow r : RowP AliasOf C [("Count", .int)]))
#check_failure (fun e : GroupExprP Unit AliasOf C KS .int =>
  (GroupedExprP.aggE .sum (extractExpr e) : GroupedExprP AliasOf C KS (.null .int)))

-- Pin the representation mismatches, so an unrelated elaboration failure
-- cannot accidentally satisfy the central intrinsic-typing checks.
/--
error: Type mismatch
  extractExpr e
has type
  GroupedExprP AliasOf C KS SqlType.int
but is expected to have type
  SqlExpr C SqlType.int
-/
#guard_msgs in
example (e : GroupExprP Unit AliasOf C KS .int) : SqlExpr C .int := extractExpr e

/--
error: Application type mismatch: The argument
  groupedSum
has type
  GroupedExprP AliasOf C KS (SqlType.null SqlPrim.int)
but is expected to have type
  SqlExprP AliasOf C { ty := SqlPrim.int, nullable := true }
in the application
  GroupedExprP.aggE Aggregate.sum groupedSum
-/
#guard_msgs in
example : GroupedExprP AliasOf C KS (.null .int) :=
  GroupedExprP.aggE (n := true) .sum groupedSum

/--
error: Application type mismatch: The argument
  groupedSpine
has type
  SpineQP AliasOf C Terminal.grouped [("Count", SqlType.int)]
but is expected to have type
  SpineQP AliasOf C Terminal.plain [("Count", SqlType.int)]
in the application
  SpineQP.order [] groupedSpine
-/
#guard_msgs in
example : SpineQP AliasOf C .plain [("Count", .int)] := .order [] groupedSpine

/--
error: Application type mismatch: The argument
  Values.nil
has type
  Values []
but is expected to have type
  Values TwoKeys
in the application
  secondKey.getValues Values.nil
-/
#guard_msgs in
example : Option String := KeyRef.getValues secondKey Values.nil

-- The second of two computed keys is read from the same complete key schema.
-- Reversing projection order catches positional lookup mistakes independently
-- of ordinary column lookup and verifies that raw groupYield remains useful.
def rawQuery : Query C [("Second", .int), ("First", .int), ("Sum", .null .int)] := fun _ =>
  .spine (.fromT rows (fun atom =>
    let r := RowP.ofAtom atom
    let ks : RowP _ C [("First", .int), ("Second", .int)] :=
      ![(r["Bucket"] + 1).as "First", (r["Bucket"] + 10).as "Second"]
    .groupYield ks (by decide) .none .nil
      (.cons (.key (.there .here))
        (.cons (.key .here) (.cons (.aggE .sum r["Value"]) .nil)))))
def env := CompilerRegressions.env
#guard (rawQuery.run env).toOption == some [
  .cons 11 (.cons 2 (.cons (some 0) .nil)), .cons 12 (.cons 3 (.cons (some 2) .nil))]
#guard [DatabaseType.sqlite, .postgres, .mysql, .sqlServer].all fun db =>
  (rawQuery.toSqlChecked db).isOk

-- Grouped IN keeps the ordinary empty-list semantics and does not demand its
-- left operand. A division error makes accidental evaluation observable.
private def ee : EvalEnv C := ⟨env, .nil, none⟩
private def badGroupedInt : GroupedExprP AliasOf C KS .int :=
  .arith .div (.intC 1) (.intC 0)
private def emptyMembership : GroupedExprP AliasOf C KS (.null .bool) :=
  .inList badGroupedInt .nil
private def nullMembership : GroupedExprP AliasOf C KS (.null .bool) :=
  .inList (.nullC .int) .nil
#guard (GroupedExprP.evalG ee (.cons 1 .nil) [[]] emptyMembership).toOption == some (some false)
#guard (GroupedExprP.evalG ee (.cons 1 .nil) [[]] nullMembership).toOption == some (some false)
#guard (GroupedExprP.evalG ee (.cons 1 .nil) [[]] (.not emptyMembership)).toOption == some (some true)

end GroupedAstTyping
