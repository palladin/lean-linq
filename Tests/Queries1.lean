import Tests.Tables

/-! Ported query shapes, part 1: FROM/WHERE/SELECT/ORDER BY, NULL checks,
scalar aggregates, IN, subqueries, GROUP BY, joins.

Where the source API differs (key-selector joins, aggregate ORDER BY), the
shape is expressed in this DSL's idiom: on-predicates for joins, and ordering
by the aliased output column after a grouped select. -/

open LeanLinq

namespace TQ

def From := Query.from' customers
def FromStatic := Query.from' customers

def FromSelect := Query.from' customers
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def FromSelectSingle := Query.from' customers
  |>.select (fun c => ![c["Age"].as "Age"])
def FromSelectExpression := Query.from' customers
  |>.select (fun c => ![(c["Id"] * 100).as "Calc", (c["Name"] ++ " - Customer").as "Label"])

def FromWhereInt := Query.from' customers |>.where' (fun c => c["Age"] >. 18)
def FromWhereString := Query.from' customers |>.where' (fun c => c["Name"] ==. "John")
def FromWhereMultiple := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18 &&. c["Name"] !=. "Admin")
def FromWhereOr := Query.from' customers
  |>.where' (fun c => (c["Age"] >. 18 &&. c["Age"] <. 65) ||. c["Name"] ==. "VIP")
def FromWhereAnd := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18 &&. c["Name"] ==. "John")

def FromOrderByAsc := Query.from' customers |>.orderBy (fun c => [c["Name"].asc])
def FromOrderByDesc := Query.from' customers |>.orderBy (fun c => [c["Age"].desc])

def FromWhereSelect := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 21)
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def FromWhereAndSelect := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 21 &&. c["Name"] !=. "")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def FromWhereOrderBy := Query.from' customers
  |>.where' (fun c => c["Age"] >. 21 &&. c["Name"] !=. "")
  |>.orderBy (fun c => [c["Age"].asc])
def FromSelectOrderBy := Query.from' customers
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", (c["Age"] + 5).as "AgePlus"])
def FromWhereSelectOrderBy := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![(c["Id"] + 1).as "IdPlus", (c["Name"] ++ "!").as "Loud"])
def FromWhereOrderBySelect := Query.from' customers
  |>.where' (fun c => c["Age"] >. 21 &&. c["Name"] !=. "")
  |>.orderBy (fun c => [c["Age"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name", (c["Age"] + 10).as "AgePlus"])
def FromWhereOrderBySelectNamed := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 21 &&. c["Name"] !=. "")
  |>.orderBy (fun c => [c["Name"].asc])
  |>.select (fun c => ![c["Id"].as "CustomerId",
                        (c["Name"] ++ " (Customer)").as "CustomerInfo",
                        (c["Age"] + 5).as "AdjustedAge"])
def FromWhereSelectNamed := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.select (fun c => ![c["Id"].as "OriginalId",
                        (c["Id"] * 100).as "ModifiedId",
                        c["Name"].as "CustomerName"])
def FromProductWhereSelect := Query.from' products
  |>.where' (fun p => p["ProductName"] !=. "Discontinued")
  |>.select (fun p => ![p["Id"].as "Id", p["ProductName"].as "ProductName"])
def FromWhereSelectParameterized := Query.from' customers
  |>.where' (fun c => c["Age"] >=. SqlExpr.param .int "minAge" &&.
                      c["Age"] <=. SqlExpr.param .int "maxAge")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

def FromWhereFusionTwo := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.where' (fun c => c["Name"] !=. "Admin")
def FromWhereFusionThree := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.where' (fun c => c["Name"] !=. "Admin")
  |>.where' (fun c => c["Age"] <. 65)
def FromWhereFusionWithSelect := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 21)
  |>.where' (fun c => c["Name"] !=. "")
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])
def FromWhereFusionWithOrderBy := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.where' (fun c => c["Name"] !=. "Admin")
  |>.orderBy (fun c => [c["Name"].asc])

def FromOrderByThenBy := Query.from' customers
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].asc])
def FromOrderByThenByDescending := Query.from' customers
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].desc])
def FromOrderByDescendingThenBy := Query.from' customers
  |>.orderBy (fun c => [c["Age"].desc, c["Name"].asc])
def FromOrderByMultiple := Query.from' customers
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].desc, c["Id"].asc])
def FromWhereOrderByThenBy := Query.from' customers
  |>.where' (fun c => c["Age"] >. 18)
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].desc])
def FromOrderByThenBySelect := Query.from' customers
  |>.orderBy (fun c => [c["Name"].asc, c["Age"].asc])
  |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"])

def FromWhereIsNull := Query.from' customers |>.where' (fun c => c["Name"].isNull)
def FromWhereIsNotNull := Query.from' customers |>.where' (fun c => c["Name"].isNotNull)
def FromWhereIsNullInt := Query.from' customers |>.where' (fun c => c["Age"].isNull)
def FromWhereIsNotNullInt := Query.from' customers |>.where' (fun c => c["Age"].isNotNull)
def FromWhereIsNullCombined := Query.from' customers
  |>.where' (fun c => c["Name"].isNull &&. c["Age"].isNotNull)

def sumAgesScalar := Query.from' customers
  |>.select (fun c => ![c["Age"].as "Age"]) |>.sum
def FromWhereAgeGreaterThanSum := Query.from' customers
  |>.where' (fun c => c["Age"] >. sumAgesScalar.embed)
def SumAges := sumAgesScalar
def CountCustomers := Query.from' customers |>.count
def CountActiveCustomers := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 18) |>.count
def SumPrices := Query.from' products |>.select (fun p => ![p["Price"].as "Price"]) |>.sum
def AvgPrices := Query.from' products |>.select (fun p => ![p["Price"].as "Price"]) |>.avg
def MinPrice := Query.from' products |>.select (fun p => ![p["Price"].as "Price"]) |>.min
def MaxPrice := Query.from' products |>.select (fun p => ![p["Price"].as "Price"]) |>.max
def SumExpensivePrices := Query.from' products
  |>.where' (fun p => p["Price"] >. 100.0)
  |>.select (fun p => ![p["Price"].as "Price"]) |>.sum
def AvgExpensivePrices := Query.from' products
  |>.where' (fun p => p["Price"] >. 100.0)
  |>.select (fun p => ![p["Price"].as "Price"]) |>.avg
def FromWhereAgeGreaterThanAverageAge := FromWhereAgeGreaterThanSum

def FromWhereAgeIn := Query.from' customers
  |>.where' (fun c => c["Age"].inValues [18, 21, 25, 30])
def FromWhereAgeInSubquery := Query.from' customers
  |>.where' (fun c => c["Age"].inQuery
      (Query.from' customers
        |>.where' (fun x => x["Name"] ==. "VIP")
        |>.select (fun x => ![x["Age"].as "Age"])))
def FromWhereAgeInSubqueryWithClosure := Query.from' customers
  |>.where' (fun c => c["Age"].inQuery
      (Query.from' customers
        |>.where' (fun x => x["Name"] ==. c["Name"] ++ "_VIP")
        |>.select (fun x => ![x["Age"].as "Age"])))
def FromSubquery :=
  (Query.from' customers
    |>.select (fun x => ![x["Id"].as "Id", (x["Age"] + 1).as "NewAge"]))
  |>.select (fun x => ![x["Id"].as "Id", x["NewAge"].as "NewAge"])
def FromWhereSelectWhereFromNested :=
  (Query.from' customers
    |>.where' (fun c => c["Age"] >. 18)
    |>.select (fun c => ![c["Id"].as "Id", c["Name"].as "Name"]))
  |>.where' (fun x => x["Id"] >. 100)
  |>.select (fun x => ![x["Id"].as "Id", x["Name"].as "Name"])
def FromWhereSelectWhereNested := FromWhereSelectWhereFromNested

def FromGroupBySelect := Query.from' customers
  |>.groupBy (fun c => [c["Age"].key])
  |>.select (fun c a => ![c["Age"].as "Age", (a.count).as "Count"])
def FromGroupByMultipleSelect := Query.from' customers
  |>.groupBy (fun c => [c["Age"].key, c["Name"].key])
  |>.select (fun c a => ![c["Age"].as "Age", c["Name"].as "Name", (a.count).as "Count"])
def FromGroupByHavingSelect := Query.from' customers
  |>.groupBy (fun c => [c["Age"].key])
  |>.having (fun _ a => a.count >. 1)
  |>.select (fun c a => ![c["Age"].as "Age", (a.count).as "Count"])
def FromWhereGroupBySelect := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 18)
  |>.groupBy (fun c => [c["Age"].key])
  |>.select (fun c a => ![c["Age"].as "Age", (a.count).as "Count"])

def InnerJoinBasic := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["Amount"].as "Amount"])
def InnerJoinWithSelect := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Name"].as "CustomerName", o["Amount"].as "OrderAmount"])
def InnerJoinWithWhere := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 18)
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                    o["Id"].as "OrderId", o["Amount"].as "Amount"])
  |>.where' (fun r => r["Amount"] >. 100)
def InnerJoinWithOrderBy := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["Amount"].as "Amount"])
  |>.orderBy (fun r => [r["Name"].asc])
def LeftJoinBasic := Query.from' customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["Amount"].as "Amount"])
def LeftJoinWithSelect := Query.from' customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![(c["Name"] ++ " (Customer)").as "CustomerInfo",
                    o["Amount"].as "OrderAmount"])
def LeftJoinWithWhere := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 21)
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                    o["Id"].as "OrderId", o["Amount"].as "OrderAmount"])
  |>.where' (fun r => r["Age"] <. 65)
def LeftJoinWithOrderBy := Query.from' customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["Amount"].as "Amount"])
  |>.orderBy (fun r => [r["Name"].asc, r["Amount"].desc])

def InnerJoinWithGroupBy := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "CustomerId", c["Name"].as "CustomerName",
                    o["Amount"].as "Amount"])
  |>.groupBy (fun r => [r["CustomerId"].key, r["CustomerName"].key])
  |>.select (fun r a => ![r["CustomerId"].as "CustomerId",
                          r["CustomerName"].as "CustomerName",
                          (a.sum r["Amount"]).as "TotalAmount"])
def LeftJoinWithAggregates := Query.from' customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                    o["Amount"].as "Amount"])
  |>.groupBy (fun r => [r["Id"].key])
  |>.select (fun r a => ![r["Id"].as "CustomerId", (a.count).as "OrderCount",
                          (a.sum r["Amount"]).as "TotalSpent"])
def MultipleInnerJoinsFusion := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["ProductId"].as "ProductId"])
  |>.innerJoin products (fun co p => co["ProductId"] ==. p["Id"])
      (fun co p => ![co["Id"].as "Id", co["Name"].as "Name",
                     co["ProductId"].as "OrderProductId", p["ProductName"].as "ProductName"])
def MixedJoinTypesFusion := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["Id"].as "OrderId", o["ProductId"].as "ProductId"])
  |>.leftJoin products (fun co p => co["ProductId"] ==. p["Id"])
      (fun co p => ![co["Id"].as "Id", co["Name"].as "Name",
                     co["ProductId"].as "OrderProductId", p["ProductName"].as "ProductName"])
def JoinFusionWithWhere := Query.from' customers
  |>.where' (fun c => c["Age"] >=. 18)
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name",
                    o["ProductId"].as "ProductId", o["Amount"].as "Amount"])
  |>.innerJoin products (fun co p => co["ProductId"] ==. p["Id"])
      (fun co p => ![co["Id"].as "Id", co["Name"].as "Name",
                     co["Amount"].as "Amount", p["ProductName"].as "ProductName"])
  |>.where' (fun r => r["Amount"] >. 100)

def FromGroupByOrderBySelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount"])
  |>.orderBy (fun r => [r["TotalAmount"].desc])
def FromGroupByOrderByMultipleSelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId",
                          (a.sum o["Amount"]).as "TotalAmount", (a.count).as "OrderCount"])
  |>.orderBy (fun r => [r["TotalAmount"].desc, r["OrderCount"].asc])
def FromGroupByOrderByThreeKeysSelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId",
                          (a.sum o["Amount"]).as "TotalAmount", (a.count).as "OrderCount"])
  |>.orderBy (fun r => [r["TotalAmount"].desc, r["OrderCount"].asc, r["CustomerId"].asc])
def FromGroupByMultipleOrderBySelect := Query.from' customers
  |>.groupBy (fun c => [c["Age"].key, c["Name"].key])
  |>.select (fun c a => ![c["Age"].as "Age", c["Name"].as "Name", (a.count).as "Count"])
  |>.orderBy (fun r => [r["Count"].desc])
def FromGroupByHavingOrderBySelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.having (fun _ a => a.count >. 1)
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount"])
  |>.orderBy (fun r => [r["TotalAmount"].desc])
def ComplexJoinWhereGroupByHavingOrderBySelect := Query.from' customers
  |>.innerJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                    o["Amount"].as "Amount"])
  |>.where' (fun r => r["Age"] >=. 18 &&. r["Amount"] >. 50)
  |>.groupBy (fun r => [r["Id"].key, r["Name"].key])
  |>.having (fun r a => a.count >. 2 &&. a.sum r["Amount"] >. 500)
  |>.select (fun r a => ![r["Id"].as "CustomerId", r["Name"].as "CustomerName",
                          (a.count).as "TotalOrders", (a.sum r["Amount"]).as "TotalSpent",
                          (a.sum r["Amount"] / a.count).as "AvgOrderValue"])
  |>.orderBy (fun r => [r["TotalSpent"].desc, r["TotalOrders"].asc])
def ComplexLeftJoinWhereGroupByOrderBySelect := Query.from' customers
  |>.leftJoin orders (fun c o => c["Id"] ==. o["CustomerId"])
      (fun c o => ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
                    o["Amount"].as "Amount"])
  |>.where' (fun r => r["Age"] >=. 21)
  |>.groupBy (fun r => [r["Id"].key, r["Name"].key])
  |>.select (fun r a => ![r["Id"].as "CustomerId", r["Name"].as "CustomerName",
                          (a.count).as "OrderCount", (a.sum r["Amount"]).as "TotalSpent"])
  |>.orderBy (fun r => [r["TotalSpent"].desc, r["CustomerName"].asc])
def FromGroupByMinMaxSelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId",
                          (a.min o["Amount"]).as "MinAmount", (a.max o["Amount"]).as "MaxAmount",
                          (a.count).as "OrderCount"])
def FromGroupByAvgSelect := Query.from' orders
  |>.groupBy (fun o => [o["CustomerId"].key])
  |>.select (fun o a => ![o["CustomerId"].as "CustomerId",
                          (a.avg o["Amount"]).as "AvgAmount", (a.count).as "OrderCount"])
def FromGroupByDecimalAggregatesSelect := Query.from' products
  |>.groupBy (fun p => [p["ProductName"].key])
  |>.select (fun p a => ![p["ProductName"].as "ProductName",
                          (a.sum p["Price"]).as "TotalPrice", (a.avg p["Price"]).as "AvgPrice",
                          (a.min p["Price"]).as "MinPrice", (a.max p["Price"]).as "MaxPrice",
                          (a.count).as "ProductCount"])
def FromGroupByDecimalSumSelect := Query.from' products
  |>.groupBy (fun p => [p["ProductName"].key])
  |>.select (fun p a => ![p["ProductName"].as "ProductName", (a.sum p["Price"]).as "TotalPrice"])
def FromGroupByDecimalAvgSelect := Query.from' products
  |>.groupBy (fun p => [p["ProductName"].key])
  |>.select (fun p a => ![p["ProductName"].as "ProductName", (a.avg p["Price"]).as "AvgPrice"])

def FromSelectSum := Query.from' orders |>.select (fun o => ![o["Amount"].as "Amount"]) |>.sum
def FromSelectAvg := Query.from' orders |>.select (fun o => ![o["Amount"].as "Amount"]) |>.avg
def FromSelectMin := Query.from' orders |>.select (fun o => ![o["Amount"].as "Amount"]) |>.min
def FromSelectMax := Query.from' orders |>.select (fun o => ![o["Amount"].as "Amount"]) |>.max

end TQ
