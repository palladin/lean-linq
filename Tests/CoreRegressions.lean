import LeanLinq

/-! Independent expected results for literal construction and the grouping
invariant that protects cardinality-based database budgets. -/

namespace CoreRegressions
open LeanLinq

abbrev S : Schema := [("Id", .int)]
abbrev C : Ctx := { tables := [("items", S)] }
def items : Table "items" S := ⟨⟩
def env : TableEnv C.tables := .cons [.cons 1 .nil] .nil
def source := Query.from' (ts := C) items

-- A global aggregate has different empty-input cardinality from GROUP BY.
-- Requiring a first key prevents the original two-statements-for-budget-1 bug.
#check_failure source.groupBy (fun _ => (RowP.nil : RowP _ C []))
#check_failure (source AliasOf).groupBy (fun _ => (RowP.nil : RowP _ C []))
#check_failure (SpineQP.groupYield (RowP.nil : RowP AliasOf C []) (by decide)
  .none .nil (.nil : GroupedRowP AliasOf C [] []) : SpineQP AliasOf C .grouped [])

def emptyGrouped := (source.limit 0).groupBy (fun r => ![r["Id"].as "Id"])
  |>.select (fun _ a => ![a.count.as "Count"])

def emptyFanOut : Db C 1 Nat := db! {
  let rows ← emptyGrouped.execQuery
  let batches ← for _r in rows do source.execQuery
  return batches.length
}

#guard (emptyGrouped.run env).toOption == some []
#guard emptyGrouped.gcard.eval (fun _ => 10) == 0
#guard (emptyFanOut.exec 1 env).toOption == some 0
#guard (source.limit 0 |>.count |>.run env).toOption == some (some 0)

def decimalPowers := source.select (fun _ =>
  ![(1e3 : SqlExprP _ C .decimal).as "Positive",
    (1.2e3 : SqlExprP _ C .decimal).as "Fractional",
    (1e-3 : SqlExprP _ C .decimal).as "Negative"])

-- Values are exact milli-units, independently specified rather than derived
-- by evaluating another spelling of the same literal.
#guard (decimalPowers.run env).toOption ==
  some [.cons 1000000 (.cons 1200000 (.cons 1 .nil))]
#guard (decimalPowers.toSql .sqlite).params ==
  #[(":p0", .decimal "1000"), (":p1", .decimal "1200"), (":p2", .decimal "0.001")]

def textQuery := source.select (fun _ => ![(SqlExpr.str "hello").as "Text"])
#check_failure textQuery.sum
#check_failure textQuery.avg
#check_failure ((source.groupBy (fun r => ![r["Id"].as "Id"]))
  |>.select (fun _ a => ![(a.sum (fun _ => SqlExpr.str "hello")).as "Sum"]))

end CoreRegressions
