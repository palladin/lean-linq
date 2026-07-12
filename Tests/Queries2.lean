import Tests.Queries1

/-! Ported query shapes, part 2: parameters, bool columns, CASE, LIKE, ABS,
decimal/dateTime/guid columns, string/date/math functions, LIMIT/OFFSET,
DISTINCT, set operations — plus the registry consumed by the golden runner. -/

open LeanLinq

namespace TQ

/- Definitions are pinned to `TestCtx` at each query head: an unannotated
`def` cannot leave the context as a metavariable (instance search would be
stuck), and the corpus only ever runs against the seed context. -/

def ParameterAsIntParam := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"] >. SqlExpr.param "minAge")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def ParameterAsStringParam := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"] ==. SqlExpr.param "customerName")
  |>.select (fun c => ![c["Id"].as "Id", c["Age"].as "Age"])
def ParameterAsBoolParam := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => (c["Age"] >. 18) ==. SqlExpr.param "isAdult")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"])
def BoolColumnDirectComparison := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["IsActive"] ==. SqlExpr.param "isActive")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                        c["IsActive"].as "IsActive"])
def BoolColumnLiteralTrue := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["IsActive"] ==. true)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                        c["IsActive"].as "IsActive"])
def BoolColumnLiteralFalse := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["IsActive"] ==. false)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                        c["IsActive"].as "IsActive"])

def CaseStringExpression := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id",
      (SqlExpr.caseWhen (c["Age"] >. 18) (SqlExpr.str "Adult") (SqlExpr.str "Minor")).as "AgeGroup"])
def CaseIntExpression := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id",
      (SqlExpr.caseWhen (c["Age"] >. 65) (SqlExpr.int 1) (SqlExpr.int 0)).as "IsSenior"])
def CaseBoolExpression := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id",
      (SqlExpr.caseWhen (c["Age"] >. 18) (c["IsActive"]) (SqlExpr.bool false)).as "ActiveAdult"])
def CaseInWhere := Query.from' (ts := TestCtx) customers
  |>.where' (fun c =>
      SqlExpr.caseWhen (c["Age"] >. 18) (SqlExpr.str "Adult") (SqlExpr.str "Minor") ==. "Adult")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

def LikeWildcard := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"].like "Jo%")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def LikeSingleChar := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"].like "J_n")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def LikeBothWildcards := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"].like "%o_n%")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def LikeExact := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"].like "John")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

def AbsColumn := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id", (c["Age"].abs).as "AbsAge"])
def AbsInWhere := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"].abs >. 30)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"])
def AbsExpression := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id", ((c["Age"] - 50).abs).as "AbsDiff"])
def AbsParameter := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"].abs >. (SqlExpr.param (ts := TestCtx) "minAge").abs)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"])

def FromWhereDecimalComparison := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["Price"] >. 100.50)
def FromSelectDecimalArithmetic := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["ProductName"].as "ProductName",
      (p["Price"] * 1.1).as "Marked", (p["Price"] + 10.0).as "Plus",
      (p["Price"] - 5.0).as "Minus"])
def FromWhereDecimalIsNull := Query.from' (ts := TestCtx) products |>.where' (fun p => p["Price"].isNull)
def FromWhereDecimalIsNotNull := Query.from' (ts := TestCtx) products |>.where' (fun p => p["Price"].isNotNull)
def CaseDecimalExpression := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["ProductName"].as "ProductName",
      (SqlExpr.caseWhen (p["Price"] >. 1000.0) (SqlExpr.str "Expensive")
        (SqlExpr.caseWhen (p["Price"] >. 100.0) (SqlExpr.str "Moderate")
          (SqlExpr.str "Cheap"))).as "ExpensiveFlag"])
def ParameterAsDecimalParam := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["Price"] >. SqlExpr.param "minPrice")

def FromWhereCreatedDateComparison := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["CreatedDate"] >. SqlExpr.dt "2024-01-01")
def FromWhereCreatedDateIsNull := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["CreatedDate"].isNull)
def FromWhereCreatedDateIsNotNull := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["CreatedDate"].isNotNull)
def FromSelectCreatedDateMinMax := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["ProductName"].as "ProductName",
      p["CreatedDate"].as "EarliestDate", p["CreatedDate"].as "LatestDate"])
def CaseDateTimeExpression := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["ProductName"].as "ProductName",
      (SqlExpr.caseWhen (p["CreatedDate"] <. SqlExpr.dt "2020-01-01") (SqlExpr.str "Old")
        (SqlExpr.caseWhen (p["CreatedDate"] <. SqlExpr.dt "2024-01-01") (SqlExpr.str "Recent")
          (SqlExpr.str "New"))).as "Age"])
def ParameterAsDateTimeParam := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["CreatedDate"] >. SqlExpr.param "startDate")

def FromWhereUniqueIdEquals := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["UniqueId"] ==. SqlExpr.gd "12345678-1234-1234-1234-123456789012")
def FromWhereUniqueIdNotEquals := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["UniqueId"] !=. SqlExpr.gd "00000000-0000-0000-0000-000000000000")
def FromWhereUniqueIdIsNull := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["UniqueId"].isNull)
def FromWhereUniqueIdIsNotNull := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["UniqueId"].isNotNull)
def CaseGuidExpression := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["ProductName"].as "ProductName",
      (SqlExpr.caseWhen (p["UniqueId"] ==. SqlExpr.gd "00000000-0000-0000-0000-000000000000")
        (SqlExpr.str "Empty") (SqlExpr.str "HasId")).as "Status"])
def ParameterAsGuidParam := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["UniqueId"] ==. SqlExpr.param "targetId")

def StringSubstring := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["ProductName"].substring 1 5).as "Sub"])
def StringUpper := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["ProductName"].upper).as "Upper"])
def StringLower := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["ProductName"].lower).as "Lower"])
def StringTrim := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["ProductName"].trim).as "Trimmed"])
def StringLength := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["ProductName"].length).as "Len"])
def StringFunctionsInWhere := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"].upper ==. "JOHN" &&. c["Name"].length >. 3)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def StringFunctionsInSelect := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Id"].as "Id",
      (c["Name"].upper).as "UpperName", (c["Name"].lower).as "LowerName",
      (c["Name"].trim).as "TrimmedName", (c["Name"].length).as "NameLength",
      (c["Name"].substring 1 3).as "FirstThree"])

def DateTimeNow := Query.from' (ts := TestCtx) products
  |>.select (fun _ => ![(SqlExpr.now).as "Now"])
def DateTimeYear := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].year).as "Year"])
def DateTimeMonth := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].month).as "Month"])
def DateTimeDay := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].day).as "Day"])
def DateTimeAddDays := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].addDays 30).as "Plus30"])
def DateTimeAddMonths := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].addMonths 6).as "Plus6M"])
def DateTimeAddYears := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].addYears 1).as "Plus1Y"])
def DateTimeDiffDays := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].diffDays (SqlExpr.dt "2025-01-01")).as "Diff"])
def DateTimeDiffMonths := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].diffMonths (SqlExpr.dt "2025-01-01")).as "Diff"])
def DateTimeDiffYears := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["CreatedDate"].diffYears (SqlExpr.dt "2025-01-01")).as "Diff"])
def DateTimeFunctionsInWhere := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["CreatedDate"].year ==. 2024 &&. p["CreatedDate"].month >. 6)
  |>.select (fun p => ![p["Id"].as "Id", p["CreatedDate"].as "CreatedDate"])
def DateTimeFunctionsInSelect := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["Id"].as "Id",
      (p["CreatedDate"].year).as "CreatedYear", (p["CreatedDate"].month).as "CreatedMonth",
      (p["CreatedDate"].day).as "CreatedDay", (p["CreatedDate"].addDays 7).as "NextWeek",
      (p["CreatedDate"].addMonths 1).as "NextMonth",
      (p["CreatedDate"].diffDays SqlExpr.now).as "DaysAgo"])

def DecimalRound := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["Price"].round 2).as "Rounded"])
def DecimalCeiling := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["Price"].ceiling).as "Ceil"])
def DecimalFloor := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![(p["Price"].floor).as "Floor"])
def MathFunctionsInWhere := Query.from' (ts := TestCtx) products
  |>.where' (fun p => p["Price"].round 0 >. 100.0 &&. p["Price"].ceiling <. 1000.0)
  |>.select (fun p => ![p["Id"].as "Id", p["Price"].as "Price"])
def MathFunctionsInSelect := Query.from' (ts := TestCtx) products
  |>.select (fun p => ![p["Id"].as "Id", p["Price"].as "OriginalPrice",
      (p["Price"].round 2).as "RoundedPrice", (p["Price"].ceiling).as "CeilingPrice",
      (p["Price"].floor).as "FloorPrice"])

def FromLimitOffset := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.limitOffset (some 5) (some 10)
def FromSelectLimitOffset := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
  |>.limitOffset (some 3) (some 5)
def FromWhereLimitOffset := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.limit 10
def FromWhereSelectLimitOffset := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"] >=. 21)
  |>.orderBy (fun c => [c["Id"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"])
  |>.limitOffset (some 5) (some 15)
def FromOrderByLimitOffset := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Name"].asc]) |>.select (fun c => c)
  |>.limitOffset (some 10) (some 5)
def FromWhereOrderByLimitOffset := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.orderBy (fun c => [c["Age"].desc]) |>.select (fun c => c)
  |>.limitOffset (some 20) (some 10)
def FromWhereOrderBySelectLimitOffset := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Name"] !=. "")
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].desc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"])
  |>.limit 5
def FromLimitOffsetOnly := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.limit 10
def FromOffsetOnly := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.offset 5
def FromLimitOffsetWithoutOrderBy := Query.from' (ts := TestCtx) customers
  |>.select (fun c => c)
  |>.limit 10

def FromSelectDistinct := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Name"].as "Name"]) |>.distinct
def FromSelectDistinctWhere := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.select (fun c => ![c["Name"].as "Name"]) |>.distinct
def FromSelectDistinctOrderBy := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Name"].as "Name"]) |>.distinct
def FromSelectDistinctMultipleColumns := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Name"].as "Name", c["Age"].as "Age"]) |>.distinct

/-- Chained limit/offset must merge into one clause, not stack two LIMITs. -/
def LimitThenOffset := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.limit 3 |>.offset 1
def OffsetThenLimit := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.offset 1 |>.limit 2
/-- Re-limiting a limited query wraps it as a derived table. -/
def LimitThenLimit := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Id"].asc]) |>.select (fun c => c)
  |>.limit 3 |>.limit 2

/-- DISTINCT over a boundary query (LIMIT): dedupe applies *after* the limit,
so the limited query becomes a derived table under SELECT DISTINCT. -/
def FromOrderByLimitDistinct := Query.from' (ts := TestCtx) customers
  |>.select (fun c => ![c["Name"].as "Name"])
  |>.orderBy (fun r => [r["Name"].asc])
  |>.limit 2
  |>.distinct
  |>.orderBy (fun r => [r["Name"].asc])

private def idOnly (k : Int) := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["Id"] ==. SqlExpr.long k)
  |>.select (fun c => ![c["Id"].as "Id"])

/-- Nested set operations parenthesize *structurally* (derived tables):
flat rendering would let PostgreSQL/SQL Server bind INTERSECT tighter —
`({3} ∪ {1}) ∩ {1}` is `{1}`, not `{3} ∪ ({1} ∩ {1}) = {1,3}`. -/
def UnionThenIntersect := ((idOnly 3).union (idOnly 1)).intersect (idOnly 1)

/-- Right-nested EXCEPT: `{1,2,3,4} \ ({1} \ {1})` is everything —
flat rendering associates left and loses row 1. -/
def ExceptNested :=
  (Query.from' (ts := TestCtx) customers |>.select (fun c => ![c["Id"].as "Id"]))
    |>.except ((idOnly 1).except (idOnly 1))

/-- A LIMIT inside a set-operation operand stays *inside* (derived
table); rendered flat, SQLite would apply it to the whole compound. -/
def UnionWithLimitOperand :=
  ((Query.from' (ts := TestCtx) customers |>.select (fun c => ![c["Id"].as "Id"])
      |>.orderBy (fun r => [r["Id"].asc]) |>.limit 1)).union (idOnly 3)

/-- ORDER BY before GROUP BY is meaningless to the grouping and SQL
cannot express it: the spine's order nodes are stripped at construction,
leaving one clean GROUP BY statement. -/
def FromOrderByGroupBySelect := Query.from' (ts := TestCtx) customers
  |>.orderBy (fun c => [c["Name"].asc])
  |>.groupBy (fun c => [c["Age"].key])
  |>.select (fun r a => ![r["Age"].as "Age", (a.count).as "N"])

/-- A boolean column in predicate position: T-SQL bit values are not
predicates, so SQL Server compiles `([IsActive] = 1)`. -/
def FromWhereBoolColumnAnd := Query.from' (ts := TestCtx) customers
  |>.where' (fun c => c["IsActive"] &&. (c["Age"] >=. 18))
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

/-- ORDER BY over a nullable key with a NULL present (the LEFT JOIN pad):
the evaluator and SQLite/SQL Server sort NULL smallest, and the compiler
now pins PostgreSQL to the same placement (`NULLS FIRST` on ASC). -/
def LeftJoinOrderByNullableKey := Query.from' (ts := TestCtx) customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Name"].as "Name", o["Amount"].as "Amount"])
  |>.orderBy (fun r => [r["Amount"].asc, r["Name"].asc])

/-! Double coverage: the `.double` column type, differentially tested for
the first time — decode, arithmetic, comparison, NULLs, ordering,
aggregates. Seed values are binary-exact so engine text never wobbles. -/
def MeasurementsSelect := Query.from' (ts := TestCtx) measurements
  |>.orderBy (fun m => [m["Id"].asc])
  |>.select (fun m => ![m["Id"].as "Id", m["Value"].as "Value", m["Factor"].as "Factor"])

def MeasurementsArith := Query.from' (ts := TestCtx) measurements
  |>.orderBy (fun m => [m["Id"].asc])
  |>.select (fun m => ![m["Id"].as "Id",
      (m["Value"] * 2.0 + 0.5).as "Scaled",
      (m["Value"] / 2.0).as "Halved"])

def MeasurementsCompare := Query.from' (ts := TestCtx) measurements
  |>.where' (fun m => m["Value"] >. 1.0)
  |>.select (fun m => ![m["Id"].as "Id", m["Value"].as "Value"])

def MeasurementsFactorNull := Query.from' (ts := TestCtx) measurements
  |>.where' (fun m => m["Factor"].isNull)
  |>.select (fun m => ![m["Id"].as "Id"])

def MeasurementsOrderByFactor := Query.from' (ts := TestCtx) measurements
  |>.orderBy (fun m => [m["Factor"].asc, m["Id"].asc])
  |>.select (fun m => ![m["Id"].as "Id", m["Factor"].as "Factor"])

def MeasurementsSum := Query.from' (ts := TestCtx) measurements
  |>.select (fun m => ![m["Value"].as "Value"]) |>.sum
def MeasurementsAvg := Query.from' (ts := TestCtx) measurements
  |>.select (fun m => ![m["Value"].as "Value"]) |>.avg
def MeasurementsMin := Query.from' (ts := TestCtx) measurements
  |>.select (fun m => ![m["Value"].as "Value"]) |>.min
def MeasurementsMax := Query.from' (ts := TestCtx) measurements
  |>.select (fun m => ![m["Value"].as "Value"]) |>.max

def UnionQ :=
  (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] >. 30)
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
  |>.union
  (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Name"] ==. "Alice")
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
def IntersectQ :=
  (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] >. 25)
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
  |>.intersect
  (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Name"] ==. "John")
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
def ExceptQ :=
  (Query.from' (ts := TestCtx) customers
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
  |>.except
  (Query.from' (ts := TestCtx) customers
    |>.where' (fun c => c["Age"] <. 18)
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))

/-! Comprehension-syntax parity cases: the same shapes expressed with
`query!` clauses (join/leftJoin/orderBy/groupBy/having/distinct/limit). -/

def LinqJoin := (query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "Name", o["Amount"].as "Amount"]
} : Query TestCtx _)
def LinqLeftJoin := (query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "Name", o["Amount"].as "Amount"]
} : Query TestCtx _)
def LinqOrderBy := (query! {
  from c in customers
  orderBy c["Name"].asc, c["Age"].desc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
} : Query TestCtx _)
def LinqGroupBy := (query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "Total"]
} : Query TestCtx _)
def LinqGroupByHaving := (query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  having a.count >. 1
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "Total"]
} : Query TestCtx _)
def LinqDistinctLimit := (query! {
  from c in customers
  where c["Age"] >. 18
  orderBy c["Name"].asc
  select ![c["Name"].as "Name"]
  distinct
  limit 2
} : Query TestCtx _)
def LinqComplex := (query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 18
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![c["Id"].as "CustomerId", c["Name"].as "CustomerName",
           (a.sum o["Amount"]).as "TotalSpent"]
} : Query TestCtx _)
def LinqLimitOffset := (query! {
  from c in customers
  orderBy c["Id"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
  limit 2 offset 1
} : Query TestCtx _)

/-- The full query registry: name ↦ per-dialect compilation. -/
def queryCases : List (String × Case) := [
  ("From", q From), ("FromStatic", q FromStatic), ("FromSelect", q FromSelect),
  ("FromSelectSingle", q FromSelectSingle), ("FromSelectExpression", q FromSelectExpression),
  ("FromWhereInt", q FromWhereInt), ("FromWhereString", q FromWhereString),
  ("FromWhereMultiple", q FromWhereMultiple), ("FromWhereOr", q FromWhereOr),
  ("FromWhereAnd", q FromWhereAnd), ("FromOrderByAsc", q FromOrderByAsc),
  ("FromOrderByDesc", q FromOrderByDesc), ("FromWhereSelect", q FromWhereSelect),
  ("FromWhereAndSelect", q FromWhereAndSelect), ("FromWhereOrderBy", q FromWhereOrderBy),
  ("FromSelectOrderBy", q FromSelectOrderBy),
  ("FromWhereSelectOrderBy", q FromWhereSelectOrderBy),
  ("FromWhereOrderBySelect", q FromWhereOrderBySelect),
  ("FromWhereOrderBySelectNamed", q FromWhereOrderBySelectNamed),
  ("FromWhereSelectNamed", q FromWhereSelectNamed),
  ("FromProductWhereSelect", q FromProductWhereSelect),
  ("FromWhereSelectParameterized", q FromWhereSelectParameterized),
  ("FromWhereFusionTwo", q FromWhereFusionTwo),
  ("FromWhereFusionThree", q FromWhereFusionThree),
  ("FromWhereFusionWithSelect", q FromWhereFusionWithSelect),
  ("FromWhereFusionWithOrderBy", q FromWhereFusionWithOrderBy),
  ("FromOrderByThenBy", q FromOrderByThenBy),
  ("FromOrderByThenByDescending", q FromOrderByThenByDescending),
  ("FromOrderByDescendingThenBy", q FromOrderByDescendingThenBy),
  ("FromOrderByMultiple", q FromOrderByMultiple),
  ("FromWhereOrderByThenBy", q FromWhereOrderByThenBy),
  ("FromOrderByThenBySelect", q FromOrderByThenBySelect),
  ("FromWhereIsNull", q FromWhereIsNull), ("FromWhereIsNotNull", q FromWhereIsNotNull),
  ("FromWhereIsNullInt", q FromWhereIsNullInt),
  ("FromWhereIsNotNullInt", q FromWhereIsNotNullInt),
  ("FromWhereIsNullCombined", q FromWhereIsNullCombined),
  ("FromWhereAgeGreaterThanSum", q FromWhereAgeGreaterThanSum),
  ("SumAges", sq SumAges), ("CountCustomers", sq CountCustomers),
  ("CountActiveCustomers", sq CountActiveCustomers), ("SumPrices", sq SumPrices),
  ("AvgPrices", sq AvgPrices), ("MinPrice", sq MinPrice), ("MaxPrice", sq MaxPrice),
  ("SumExpensivePrices", sq SumExpensivePrices),
  ("AvgExpensivePrices", sq AvgExpensivePrices),
  ("FromWhereAgeGreaterThanAverageAge", q FromWhereAgeGreaterThanAverageAge),
  ("FromWhereAgeIn", q FromWhereAgeIn),
  ("FromWhereAgeInSubquery", q FromWhereAgeInSubquery),
  ("FromWhereAgeInSubqueryWithClosure", q FromWhereAgeInSubqueryWithClosure),
  ("FromWhereCorrelatedInSubquery", q FromWhereCorrelatedInSubquery),
  ("FromWhereCorrelatedScalarSubquery", q FromWhereCorrelatedScalarSubquery),
  ("FromWhereInEmptyList", q FromWhereInEmptyList),
  ("FromSelectNegativeDivision", q FromSelectNegativeDivision),
  ("DateTimeAddMonthsClamp", q DateTimeAddMonthsClamp),
  ("UnionThenIntersect", q UnionThenIntersect),
  ("ExceptNested", q ExceptNested),
  ("UnionWithLimitOperand", q UnionWithLimitOperand),
  ("FromOrderByGroupBySelect", q FromOrderByGroupBySelect),
  ("FromWhereBoolColumnAnd", q FromWhereBoolColumnAnd),
  ("LeftJoinOrderByNullableKey", q LeftJoinOrderByNullableKey),
  ("MeasurementsSelect", q MeasurementsSelect),
  ("MeasurementsArith", q MeasurementsArith),
  ("MeasurementsCompare", q MeasurementsCompare),
  ("MeasurementsFactorNull", q MeasurementsFactorNull),
  ("MeasurementsOrderByFactor", q MeasurementsOrderByFactor),
  ("MeasurementsSum", sq MeasurementsSum),
  ("MeasurementsAvg", sq MeasurementsAvg),
  ("MeasurementsMin", sq MeasurementsMin),
  ("MeasurementsMax", sq MeasurementsMax),
  ("FromSubquery", q FromSubquery),
  ("FromWhereSelectWhereFromNested", q FromWhereSelectWhereFromNested),
  ("FromWhereSelectWhereNested", q FromWhereSelectWhereNested),
  ("FromGroupBySelect", q FromGroupBySelect),
  ("FromGroupByMultipleSelect", q FromGroupByMultipleSelect),
  ("FromGroupByHavingSelect", q FromGroupByHavingSelect),
  ("FromWhereGroupBySelect", q FromWhereGroupBySelect),
  ("InnerJoinBasic", q InnerJoinBasic), ("InnerJoinWithSelect", q InnerJoinWithSelect),
  ("InnerJoinWithWhere", q InnerJoinWithWhere),
  ("InnerJoinWithOrderBy", q InnerJoinWithOrderBy),
  ("LeftJoinBasic", q LeftJoinBasic), ("LeftJoinWithSelect", q LeftJoinWithSelect),
  ("LeftJoinWithWhere", q LeftJoinWithWhere), ("LeftJoinWithOrderBy", q LeftJoinWithOrderBy),
  ("InnerJoinWithGroupBy", q InnerJoinWithGroupBy),
  ("LeftJoinWithAggregates", q LeftJoinWithAggregates),
  ("MultipleInnerJoinsFusion", q MultipleInnerJoinsFusion),
  ("MixedJoinTypesFusion", q MixedJoinTypesFusion),
  ("JoinFusionWithWhere", q JoinFusionWithWhere),
  ("FromGroupByOrderBySelect", q FromGroupByOrderBySelect),
  ("FromGroupByOrderByMultipleSelect", q FromGroupByOrderByMultipleSelect),
  ("FromGroupByOrderByThreeKeysSelect", q FromGroupByOrderByThreeKeysSelect),
  ("FromGroupByMultipleOrderBySelect", q FromGroupByMultipleOrderBySelect),
  ("FromGroupByHavingOrderBySelect", q FromGroupByHavingOrderBySelect),
  ("ComplexJoinWhereGroupByHavingOrderBySelect", q ComplexJoinWhereGroupByHavingOrderBySelect),
  ("ComplexLeftJoinWhereGroupByOrderBySelect", q ComplexLeftJoinWhereGroupByOrderBySelect),
  ("FromGroupByMinMaxSelect", q FromGroupByMinMaxSelect),
  ("FromGroupByAvgSelect", q FromGroupByAvgSelect),
  ("FromGroupByDecimalAggregatesSelect", q FromGroupByDecimalAggregatesSelect),
  ("FromGroupByDecimalSumSelect", q FromGroupByDecimalSumSelect),
  ("FromGroupByDecimalAvgSelect", q FromGroupByDecimalAvgSelect),
  ("FromSelectSum", sq FromSelectSum), ("FromSelectAvg", sq FromSelectAvg),
  ("FromSelectMin", sq FromSelectMin), ("FromSelectMax", sq FromSelectMax),
  ("ParameterAsIntParam", q ParameterAsIntParam),
  ("ParameterAsStringParam", q ParameterAsStringParam),
  ("ParameterAsBoolParam", q ParameterAsBoolParam),
  ("BoolColumnDirectComparison", q BoolColumnDirectComparison),
  ("BoolColumnLiteralTrue", q BoolColumnLiteralTrue),
  ("BoolColumnLiteralFalse", q BoolColumnLiteralFalse),
  ("CaseStringExpression", q CaseStringExpression),
  ("CaseIntExpression", q CaseIntExpression),
  ("CaseBoolExpression", q CaseBoolExpression), ("CaseInWhere", q CaseInWhere),
  ("LikeWildcard", q LikeWildcard), ("LikeSingleChar", q LikeSingleChar),
  ("LikeBothWildcards", q LikeBothWildcards), ("LikeExact", q LikeExact),
  ("AbsColumn", q AbsColumn), ("AbsInWhere", q AbsInWhere),
  ("AbsExpression", q AbsExpression), ("AbsParameter", q AbsParameter),
  ("FromWhereDecimalComparison", q FromWhereDecimalComparison),
  ("FromSelectDecimalArithmetic", q FromSelectDecimalArithmetic),
  ("FromWhereDecimalIsNull", q FromWhereDecimalIsNull),
  ("FromWhereDecimalIsNotNull", q FromWhereDecimalIsNotNull),
  ("CaseDecimalExpression", q CaseDecimalExpression),
  ("ParameterAsDecimalParam", q ParameterAsDecimalParam),
  ("FromWhereCreatedDateComparison", q FromWhereCreatedDateComparison),
  ("FromWhereCreatedDateIsNull", q FromWhereCreatedDateIsNull),
  ("FromWhereCreatedDateIsNotNull", q FromWhereCreatedDateIsNotNull),
  ("FromSelectCreatedDateMinMax", q FromSelectCreatedDateMinMax),
  ("CaseDateTimeExpression", q CaseDateTimeExpression),
  ("ParameterAsDateTimeParam", q ParameterAsDateTimeParam),
  ("FromWhereUniqueIdEquals", q FromWhereUniqueIdEquals),
  ("FromWhereUniqueIdNotEquals", q FromWhereUniqueIdNotEquals),
  ("FromWhereUniqueIdIsNull", q FromWhereUniqueIdIsNull),
  ("FromWhereUniqueIdIsNotNull", q FromWhereUniqueIdIsNotNull),
  ("CaseGuidExpression", q CaseGuidExpression),
  ("ParameterAsGuidParam", q ParameterAsGuidParam),
  ("StringSubstring", q StringSubstring), ("StringUpper", q StringUpper),
  ("StringLower", q StringLower), ("StringTrim", q StringTrim),
  ("StringLength", q StringLength),
  ("StringFunctionsInWhere", q StringFunctionsInWhere),
  ("StringFunctionsInSelect", q StringFunctionsInSelect),
  ("DateTimeNow", q DateTimeNow), ("DateTimeYear", q DateTimeYear),
  ("DateTimeMonth", q DateTimeMonth), ("DateTimeDay", q DateTimeDay),
  ("DateTimeAddDays", q DateTimeAddDays), ("DateTimeAddMonths", q DateTimeAddMonths),
  ("DateTimeAddYears", q DateTimeAddYears), ("DateTimeDiffDays", q DateTimeDiffDays),
  ("DateTimeDiffMonths", q DateTimeDiffMonths), ("DateTimeDiffYears", q DateTimeDiffYears),
  ("DateTimeFunctionsInWhere", q DateTimeFunctionsInWhere),
  ("DateTimeFunctionsInSelect", q DateTimeFunctionsInSelect),
  ("DecimalRound", q DecimalRound), ("DecimalCeiling", q DecimalCeiling),
  ("DecimalFloor", q DecimalFloor), ("MathFunctionsInWhere", q MathFunctionsInWhere),
  ("MathFunctionsInSelect", q MathFunctionsInSelect),
  ("FromLimitOffset", q FromLimitOffset), ("FromSelectLimitOffset", q FromSelectLimitOffset),
  ("FromWhereLimitOffset", q FromWhereLimitOffset),
  ("FromWhereSelectLimitOffset", q FromWhereSelectLimitOffset),
  ("FromOrderByLimitOffset", q FromOrderByLimitOffset),
  ("FromWhereOrderByLimitOffset", q FromWhereOrderByLimitOffset),
  ("FromWhereOrderBySelectLimitOffset", q FromWhereOrderBySelectLimitOffset),
  ("FromLimitOffsetOnly", q FromLimitOffsetOnly), ("FromOffsetOnly", q FromOffsetOnly),
  ("FromLimitOffsetWithoutOrderBy", q FromLimitOffsetWithoutOrderBy),
  ("FromSelectDistinct", q FromSelectDistinct),
  ("FromSelectDistinctWhere", q FromSelectDistinctWhere),
  ("FromSelectDistinctOrderBy", q FromSelectDistinctOrderBy),
  ("FromSelectDistinctMultipleColumns", q FromSelectDistinctMultipleColumns),
  ("FromOrderByLimitDistinct", q FromOrderByLimitDistinct),
  ("LimitThenOffset", q LimitThenOffset), ("OffsetThenLimit", q OffsetThenLimit),
  ("LimitThenLimit", q LimitThenLimit),
  ("Union", q UnionQ), ("Intersect", q IntersectQ), ("Except", q ExceptQ),
  ("LinqJoin", q LinqJoin), ("LinqLeftJoin", q LinqLeftJoin),
  ("LinqOrderBy", q LinqOrderBy), ("LinqGroupBy", q LinqGroupBy),
  ("LinqGroupByHaving", q LinqGroupByHaving),
  ("LinqDistinctLimit", q LinqDistinctLimit), ("LinqComplex", q LinqComplex),
  ("LinqLimitOffset", q LinqLimitOffset)
]

end TQ
