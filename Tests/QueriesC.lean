import Tests.Queries2

/-! # Comprehension twins

Every pipeline query case re-expressed with `query!` clause syntax, named
`C<Original>`. Twins compute the same rows (the integration oracle is shared
by name fallback), though the generated SQL may legitimately differ — e.g.
comprehension grouping orders by aggregate *expressions* where the pipeline
orders by output alias, and comprehension clauses always fuse flat.

Statements have no comprehension form; the trailing-`orderBy`-after-`distinct`
shape (`FromOrderByLimitDistinct`) is approximated with the fused clause order
(same rows). -/

open LeanLinq

namespace TQ

def CFrom := query! { from c in customers
                      select c }
def CFromStatic := query! { from c in customers
                            select c }
def CFromSelect := query! {
  from c in customers
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromSelectSingle := query! {
  from c in customers
  select ![c["Age"].as "Age"]
}
def CFromSelectExpression := query! {
  from c in customers
  select ![(c["Id"] * 100).as "Calc", (c["Name"] ++ " - Customer").as "Label"]
}
def CFromWhereInt := query! {
  from c in customers
  where c["Age"] >. 18
  select c
}
def CFromWhereString := query! {
  from c in customers
  where c["Name"] ==. "John"
  select c
}
def CFromWhereMultiple := query! {
  from c in customers
  where c["Age"] >. 18 &&. c["Name"] !=. "Admin"
  select c
}
def CFromWhereOr := query! {
  from c in customers
  where (c["Age"] >. 18 &&. c["Age"] <. 65) ||. c["Name"] ==. "VIP"
  select c
}
def CFromWhereAnd := query! {
  from c in customers
  where c["Age"] >. 18 &&. c["Name"] ==. "John"
  select c
}
def CFromOrderByAsc := query! {
  from c in customers
  orderBy c["Name"].asc
  select c
}
def CFromOrderByDesc := query! {
  from c in customers
  orderBy c["Age"].desc
  select c
}
def CFromWhereSelect := query! {
  from c in customers
  where c["Age"] >=. 21
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromWhereAndSelect := query! {
  from c in customers
  where c["Age"] >=. 21 &&. c["Name"] !=. ""
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromWhereOrderBy := query! {
  from c in customers
  where c["Age"] >. 21 &&. c["Name"] !=. ""
  orderBy c["Age"].asc
  select c
}
def CFromSelectOrderBy := query! {
  from c in customers
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name", (c["Age"] + 5).as "AgePlus"]
}
def CFromWhereSelectOrderBy := query! {
  from c in customers
  where c["Age"] >. 18
  orderBy c["Name"].asc
  select ![(c["Id"] + 1).as "IdPlus", (c["Name"] ++ "!").as "Loud"]
}
def CFromWhereOrderBySelect := query! {
  from c in customers
  where c["Age"] >. 21 &&. c["Name"] !=. ""
  orderBy c["Age"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name", (c["Age"] + 10).as "AgePlus"]
}
def CFromWhereOrderBySelectNamed := query! {
  from c in customers
  where c["Age"] >=. 21 &&. c["Name"] !=. ""
  orderBy c["Name"].asc
  select ![c["Id"].as "CustomerId", (c["Name"] ++ " (Customer)").as "CustomerInfo",
           (c["Age"] + 5).as "AdjustedAge"]
}
def CFromWhereSelectNamed := query! {
  from c in customers
  where c["Age"] >. 18
  select ![c["Id"].as "OriginalId", (c["Id"] * 100).as "ModifiedId",
           c["Name"].as "CustomerName"]
}
def CFromProductWhereSelect := query! {
  from p in products
  where p["ProductName"] !=. "Discontinued"
  select ![p["Id"].as "Id", p["ProductName"].as "ProductName"]
}
def CFromWhereSelectParameterized := query! {
  from c in customers
  where c["Age"] >=. SqlExpr.param .int "minAge" &&.
        c["Age"] <=. SqlExpr.param .int "maxAge"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromWhereFusionTwo := query! {
  from c in customers
  where c["Age"] >. 18
  where c["Name"] !=. "Admin"
  select c
}
def CFromWhereFusionThree := query! {
  from c in customers
  where c["Age"] >. 18
  where c["Name"] !=. "Admin"
  where c["Age"] <. 65
  select c
}
def CFromWhereFusionWithSelect := query! {
  from c in customers
  where c["Age"] >=. 21
  where c["Name"] !=. ""
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromWhereFusionWithOrderBy := query! {
  from c in customers
  where c["Age"] >. 18
  where c["Name"] !=. "Admin"
  orderBy c["Name"].asc
  select c
}
def CFromOrderByThenBy := query! {
  from c in customers
  orderBy c["Name"].asc, c["Age"].asc
  select c
}
def CFromOrderByThenByDescending := query! {
  from c in customers
  orderBy c["Name"].asc, c["Age"].desc
  select c
}
def CFromOrderByDescendingThenBy := query! {
  from c in customers
  orderBy c["Age"].desc, c["Name"].asc
  select c
}
def CFromOrderByMultiple := query! {
  from c in customers
  orderBy c["Name"].asc, c["Age"].desc, c["Id"].asc
  select c
}
def CFromWhereOrderByThenBy := query! {
  from c in customers
  where c["Age"] >. 18
  orderBy c["Name"].asc, c["Age"].desc
  select c
}
def CFromOrderByThenBySelect := query! {
  from c in customers
  orderBy c["Name"].asc, c["Age"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CFromWhereIsNull := query! {
  from c in customers
  where c["Name"].isNull
  select c
}
def CFromWhereIsNotNull := query! {
  from c in customers
  where c["Name"].isNotNull
  select c
}
def CFromWhereIsNullInt := query! {
  from c in customers
  where c["Age"].isNull
  select c
}
def CFromWhereIsNotNullInt := query! {
  from c in customers
  where c["Age"].isNotNull
  select c
}
def CFromWhereIsNullCombined := query! {
  from c in customers
  where c["Name"].isNull &&. c["Age"].isNotNull
  select c
}
def cSumAgesScalar := (query! {
  from c in customers
  select ![c["Age"].as "Age"]
}).sum
def CFromWhereAgeGreaterThanSum := query! {
  from c in customers
  where c["Age"] >. cSumAgesScalar.embed
  select c
}
def CSumAges := cSumAgesScalar
def CCountCustomers := (query! { from c in customers
                                 select c }).count
def CCountActiveCustomers := (query! {
  from c in customers
  where c["Age"] >=. 18
  select c
}).count
def CSumPrices := (query! { from p in products
                            select ![p["Price"].as "Price"] }).sum
def CAvgPrices := (query! { from p in products
                            select ![p["Price"].as "Price"] }).avg
def CMinPrice := (query! { from p in products
                           select ![p["Price"].as "Price"] }).min
def CMaxPrice := (query! { from p in products
                           select ![p["Price"].as "Price"] }).max
def CSumExpensivePrices := (query! {
  from p in products
  where p["Price"] >. 100.0
  select ![p["Price"].as "Price"]
}).sum
def CAvgExpensivePrices := (query! {
  from p in products
  where p["Price"] >. 100.0
  select ![p["Price"].as "Price"]
}).avg
def CFromWhereAgeGreaterThanAverageAge := CFromWhereAgeGreaterThanSum
def CFromWhereAgeIn := query! {
  from c in customers
  where c["Age"].inValues [18, 21, 25, 30]
  select c
}
def CFromWhereAgeInSubquery := query! {
  from c in customers
  where c["Age"].inQuery (query! {
    from x in customers
    where x["Name"] ==. "VIP"
    select ![x["Age"].as "Age"]
  })
  select c
}
def CFromWhereAgeInSubqueryWithClosure := query! {
  from c in customers
  where c["Age"].inQuery (query! {
    from x in customers
    -- explicit concat: inside the nested query! the outer binder's column
    -- type is not yet resolved when `++` searches for its HAppend instance
    where x["Name"] ==. SqlExpr.concat (c["Name"]) "_VIP"
    select ![x["Age"].as "Age"]
  })
  select c
}
def CFromSubquery := query! {
  from x in (query! {
    from c in customers
    select ![c["Id"].as "Id", (c["Age"] + 1).as "NewAge"]
  })
  select ![x["Id"].as "Id", x["NewAge"].as "NewAge"]
}
def CFromWhereSelectWhereFromNested := query! {
  from x in (query! {
    from c in customers
    where c["Age"] >. 18
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  })
  where x["Id"] >. 100
  select ![x["Id"].as "Id", x["Name"].as "Name"]
}
def CFromWhereSelectWhereNested := CFromWhereSelectWhereFromNested
def CFromGroupBySelect := query! {
  from c in customers
  groupBy c["Age"].key into a
  select ![c["Age"].as "Age", (a.count).as "Count"]
}
def CFromGroupByMultipleSelect := query! {
  from c in customers
  groupBy c["Age"].key, c["Name"].key into a
  select ![c["Age"].as "Age", c["Name"].as "Name", (a.count).as "Count"]
}
def CFromGroupByHavingSelect := query! {
  from c in customers
  groupBy c["Age"].key into a
  having a.count >. 1
  select ![c["Age"].as "Age", (a.count).as "Count"]
}
def CFromWhereGroupBySelect := query! {
  from c in customers
  where c["Age"] >=. 18
  groupBy c["Age"].key into a
  select ![c["Age"].as "Age", (a.count).as "Count"]
}
def CInnerJoinBasic := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  select ![c["Id"].as "Id", c["Name"].as "Name", o["Id"].as "OrderId",
           o["Amount"].as "Amount"]
}
def CInnerJoinWithSelect := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  select ![c["Name"].as "CustomerName", o["Amount"].as "OrderAmount"]
}
def CInnerJoinWithWhere := query! {
  from c in customers
  where c["Age"] >=. 18
  join o in orders on c["Id"] ==. o["CustomerId"]
  where o["Amount"] >. 100
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
           o["Id"].as "OrderId", o["Amount"].as "Amount"]
}
def CInnerJoinWithOrderBy := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  orderBy c["Name"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name", o["Id"].as "OrderId",
           o["Amount"].as "Amount"]
}
def CLeftJoinBasic := query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  select ![c["Id"].as "Id", c["Name"].as "Name", o["Id"].as "OrderId",
           o["Amount"].as "Amount"]
}
def CLeftJoinWithSelect := query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  select ![(c["Name"] ++ " (Customer)").as "CustomerInfo", o["Amount"].as "OrderAmount"]
}
def CLeftJoinWithWhere := query! {
  from c in customers
  where c["Age"] >=. 21
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] <. 65
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
           o["Id"].as "OrderId", o["Amount"].as "OrderAmount"]
}
def CLeftJoinWithOrderBy := query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  orderBy c["Name"].asc, o["Amount"].desc
  select ![c["Id"].as "Id", c["Name"].as "Name", o["Id"].as "OrderId",
           o["Amount"].as "Amount"]
}
def CInnerJoinWithGroupBy := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  groupBy c["Id"].key, c["Name"].key into a
  select ![c["Id"].as "CustomerId", c["Name"].as "CustomerName",
           (a.sum o["Amount"]).as "TotalAmount"]
}
def CLeftJoinWithAggregates := query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  groupBy c["Id"].key into a
  select ![c["Id"].as "CustomerId", (a.count).as "OrderCount",
           (a.sum o["Amount"]).as "TotalSpent"]
}
def CMultipleInnerJoinsFusion := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  join p in products on o["ProductId"] ==. p["Id"]
  select ![c["Id"].as "Id", c["Name"].as "Name",
           o["ProductId"].as "OrderProductId", p["ProductName"].as "ProductName"]
}
def CMixedJoinTypesFusion := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  leftJoin p in products on o["ProductId"] ==. p["Id"]
  select ![c["Id"].as "Id", c["Name"].as "Name",
           o["ProductId"].as "OrderProductId", p["ProductName"].as "ProductName"]
}
def CJoinFusionWithWhere := query! {
  from c in customers
  where c["Age"] >=. 18
  join o in orders on c["Id"] ==. o["CustomerId"]
  join p in products on o["ProductId"] ==. p["Id"]
  where o["Amount"] >. 100
  select ![c["Id"].as "Id", c["Name"].as "Name", o["Amount"].as "Amount",
           p["ProductName"].as "ProductName"]
}
def CFromGroupByOrderBySelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  orderBy (a.sum o["Amount"]).desc
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount"]
}
def CFromGroupByOrderByMultipleSelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  orderBy (a.sum o["Amount"]).desc, (a.count).asc
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount",
           (a.count).as "OrderCount"]
}
def CFromGroupByOrderByThreeKeysSelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  orderBy (a.sum o["Amount"]).desc, (a.count).asc, o["CustomerId"].asc
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount",
           (a.count).as "OrderCount"]
}
def CFromGroupByMultipleOrderBySelect := query! {
  from c in customers
  groupBy c["Age"].key, c["Name"].key into a
  orderBy (a.count).desc
  select ![c["Age"].as "Age", c["Name"].as "Name", (a.count).as "Count"]
}
def CFromGroupByHavingOrderBySelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  having a.count >. 1
  orderBy (a.sum o["Amount"]).desc
  select ![o["CustomerId"].as "CustomerId", (a.sum o["Amount"]).as "TotalAmount"]
}
def CComplexJoinWhereGroupByHavingOrderBySelect := query! {
  from c in customers
  join o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 18 &&. o["Amount"] >. 50
  groupBy c["Id"].key, c["Name"].key into a
  having a.count >. 2 &&. a.sum o["Amount"] >. 500
  orderBy (a.sum o["Amount"]).desc, (a.count).asc
  select ![c["Id"].as "CustomerId", c["Name"].as "CustomerName",
           (a.count).as "TotalOrders", (a.sum o["Amount"]).as "TotalSpent",
           (a.sum o["Amount"] / a.count).as "AvgOrderValue"]
}
def CComplexLeftJoinWhereGroupByOrderBySelect := query! {
  from c in customers
  leftJoin o in orders on c["Id"] ==. o["CustomerId"]
  where c["Age"] >=. 21
  groupBy c["Id"].key, c["Name"].key into a
  orderBy (a.sum o["Amount"]).desc, c["Name"].asc
  select ![c["Id"].as "CustomerId", c["Name"].as "CustomerName",
           (a.count).as "OrderCount", (a.sum o["Amount"]).as "TotalSpent"]
}
def CFromGroupByMinMaxSelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  select ![o["CustomerId"].as "CustomerId", (a.min o["Amount"]).as "MinAmount",
           (a.max o["Amount"]).as "MaxAmount", (a.count).as "OrderCount"]
}
def CFromGroupByAvgSelect := query! {
  from o in orders
  groupBy o["CustomerId"].key into a
  select ![o["CustomerId"].as "CustomerId", (a.avg o["Amount"]).as "AvgAmount",
           (a.count).as "OrderCount"]
}
def CFromGroupByDecimalAggregatesSelect := query! {
  from p in products
  groupBy p["ProductName"].key into a
  select ![p["ProductName"].as "ProductName", (a.sum p["Price"]).as "TotalPrice",
           (a.avg p["Price"]).as "AvgPrice", (a.min p["Price"]).as "MinPrice",
           (a.max p["Price"]).as "MaxPrice", (a.count).as "ProductCount"]
}
def CFromGroupByDecimalSumSelect := query! {
  from p in products
  groupBy p["ProductName"].key into a
  select ![p["ProductName"].as "ProductName", (a.sum p["Price"]).as "TotalPrice"]
}
def CFromGroupByDecimalAvgSelect := query! {
  from p in products
  groupBy p["ProductName"].key into a
  select ![p["ProductName"].as "ProductName", (a.avg p["Price"]).as "AvgPrice"]
}
def CFromSelectSum := (query! { from o in orders
                                select ![o["Amount"].as "Amount"] }).sum
def CFromSelectAvg := (query! { from o in orders
                                select ![o["Amount"].as "Amount"] }).avg
def CFromSelectMin := (query! { from o in orders
                                select ![o["Amount"].as "Amount"] }).min
def CFromSelectMax := (query! { from o in orders
                                select ![o["Amount"].as "Amount"] }).max
def CParameterAsIntParam := query! {
  from c in customers
  where c["Age"] >. SqlExpr.param .int "minAge"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CParameterAsStringParam := query! {
  from c in customers
  where c["Name"] ==. SqlExpr.param .string "customerName"
  select ![c["Id"].as "Id", c["Age"].as "Age"]
}
def CParameterAsBoolParam := query! {
  from c in customers
  where (c["Age"] >. 18) ==. SqlExpr.param .bool "isAdult"
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"]
}
def CBoolColumnDirectComparison := query! {
  from c in customers
  where c["IsActive"] ==. SqlExpr.param .bool "isActive"
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
           c["IsActive"].as "IsActive"]
}
def CBoolColumnLiteralTrue := query! {
  from c in customers
  where c["IsActive"] ==. true
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
           c["IsActive"].as "IsActive"]
}
def CBoolColumnLiteralFalse := query! {
  from c in customers
  where c["IsActive"] ==. false
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age",
           c["IsActive"].as "IsActive"]
}
def CCaseStringExpression := query! {
  from c in customers
  select ![c["Id"].as "Id",
           (SqlExpr.caseWhen (c["Age"] >. 18) (SqlExpr.str "Adult")
             (SqlExpr.str "Minor")).as "AgeGroup"]
}
def CCaseIntExpression := query! {
  from c in customers
  select ![c["Id"].as "Id",
           (SqlExpr.caseWhen (c["Age"] >. 65) (SqlExpr.int 1) (SqlExpr.int 0)).as "IsSenior"]
}
def CCaseBoolExpression := query! {
  from c in customers
  select ![c["Id"].as "Id",
           (SqlExpr.caseWhen (c["Age"] >. 18) (c["IsActive"]) (SqlExpr.bool false)).as "ActiveAdult"]
}
def CCaseInWhere := query! {
  from c in customers
  where SqlExpr.caseWhen (c["Age"] >. 18) (SqlExpr.str "Adult") (SqlExpr.str "Minor") ==. "Adult"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CLikeWildcard := query! {
  from c in customers
  where c["Name"].like "Jo%"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CLikeSingleChar := query! {
  from c in customers
  where c["Name"].like "J_n"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CLikeBothWildcards := query! {
  from c in customers
  where c["Name"].like "%o_n%"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CLikeExact := query! {
  from c in customers
  where c["Name"].like "John"
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CAbsColumn := query! {
  from c in customers
  select ![c["Id"].as "Id", (c["Age"].abs).as "AbsAge"]
}
def CAbsInWhere := query! {
  from c in customers
  where c["Age"].abs >. 30
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"]
}
def CAbsExpression := query! {
  from c in customers
  select ![c["Id"].as "Id", ((c["Age"] - 50).abs).as "AbsDiff"]
}
def CAbsParameter := query! {
  from c in customers
  where c["Age"].abs >. (SqlExpr.param .int "minAge").abs
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"]
}
def CFromWhereDecimalComparison := query! {
  from p in products
  where p["Price"] >. 100.50
  select p
}
def CFromSelectDecimalArithmetic := query! {
  from p in products
  select ![p["ProductName"].as "ProductName", (p["Price"] * 1.1).as "Marked",
           (p["Price"] + 10.0).as "Plus", (p["Price"] - 5.0).as "Minus"]
}
def CFromWhereDecimalIsNull := query! {
  from p in products
  where p["Price"].isNull
  select p
}
def CFromWhereDecimalIsNotNull := query! {
  from p in products
  where p["Price"].isNotNull
  select p
}
def CCaseDecimalExpression := query! {
  from p in products
  select ![p["ProductName"].as "ProductName",
           (SqlExpr.caseWhen (p["Price"] >. 1000.0) (SqlExpr.str "Expensive")
             (SqlExpr.caseWhen (p["Price"] >. 100.0) (SqlExpr.str "Moderate")
               (SqlExpr.str "Cheap"))).as "ExpensiveFlag"]
}
def CParameterAsDecimalParam := query! {
  from p in products
  where p["Price"] >. SqlExpr.param .decimal "minPrice"
  select p
}
def CFromWhereCreatedDateComparison := query! {
  from p in products
  where p["CreatedDate"] >. SqlExpr.dt "2024-01-01"
  select p
}
def CFromWhereCreatedDateIsNull := query! {
  from p in products
  where p["CreatedDate"].isNull
  select p
}
def CFromWhereCreatedDateIsNotNull := query! {
  from p in products
  where p["CreatedDate"].isNotNull
  select p
}
def CFromSelectCreatedDateMinMax := query! {
  from p in products
  select ![p["ProductName"].as "ProductName", p["CreatedDate"].as "EarliestDate",
           p["CreatedDate"].as "LatestDate"]
}
def CCaseDateTimeExpression := query! {
  from p in products
  select ![p["ProductName"].as "ProductName",
           (SqlExpr.caseWhen (p["CreatedDate"] <. SqlExpr.dt "2020-01-01") (SqlExpr.str "Old")
             (SqlExpr.caseWhen (p["CreatedDate"] <. SqlExpr.dt "2024-01-01") (SqlExpr.str "Recent")
               (SqlExpr.str "New"))).as "Age"]
}
def CParameterAsDateTimeParam := query! {
  from p in products
  where p["CreatedDate"] >. SqlExpr.param .dateTime "startDate"
  select p
}
def CFromWhereUniqueIdEquals := query! {
  from p in products
  where p["UniqueId"] ==. SqlExpr.gd "12345678-1234-1234-1234-123456789012"
  select p
}
def CFromWhereUniqueIdNotEquals := query! {
  from p in products
  where p["UniqueId"] !=. SqlExpr.gd "00000000-0000-0000-0000-000000000000"
  select p
}
def CFromWhereUniqueIdIsNull := query! {
  from p in products
  where p["UniqueId"].isNull
  select p
}
def CFromWhereUniqueIdIsNotNull := query! {
  from p in products
  where p["UniqueId"].isNotNull
  select p
}
def CCaseGuidExpression := query! {
  from p in products
  select ![p["ProductName"].as "ProductName",
           (SqlExpr.caseWhen (p["UniqueId"] ==. SqlExpr.gd "00000000-0000-0000-0000-000000000000")
             (SqlExpr.str "Empty") (SqlExpr.str "HasId")).as "Status"]
}
def CParameterAsGuidParam := query! {
  from p in products
  where p["UniqueId"] ==. SqlExpr.param .guid "targetId"
  select p
}
def CStringSubstring := query! {
  from p in products
  select ![(p["ProductName"].substring 1 5).as "Sub"]
}
def CStringUpper := query! {
  from p in products
  select ![(p["ProductName"].upper).as "Upper"]
}
def CStringLower := query! {
  from p in products
  select ![(p["ProductName"].lower).as "Lower"]
}
def CStringTrim := query! {
  from p in products
  select ![(p["ProductName"].trim).as "Trimmed"]
}
def CStringLength := query! {
  from p in products
  select ![(p["ProductName"].length).as "Len"]
}
def CStringFunctionsInWhere := query! {
  from c in customers
  where c["Name"].upper ==. "JOHN" &&. c["Name"].length >. 3
  select ![c["Id"].as "Id", c["Name"].as "Name"]
}
def CStringFunctionsInSelect := query! {
  from c in customers
  select ![c["Id"].as "Id", (c["Name"].upper).as "UpperName",
           (c["Name"].lower).as "LowerName", (c["Name"].trim).as "TrimmedName",
           (c["Name"].length).as "NameLength", (c["Name"].substring 1 3).as "FirstThree"]
}
def CDateTimeNow := query! {
  from _p in products
  select ![(SqlExpr.now).as "Now"]
}
def CDateTimeYear := query! {
  from p in products
  select ![(p["CreatedDate"].year).as "Year"]
}
def CDateTimeMonth := query! {
  from p in products
  select ![(p["CreatedDate"].month).as "Month"]
}
def CDateTimeDay := query! {
  from p in products
  select ![(p["CreatedDate"].day).as "Day"]
}
def CDateTimeAddDays := query! {
  from p in products
  select ![(p["CreatedDate"].addDays 30).as "Plus30"]
}
def CDateTimeAddMonths := query! {
  from p in products
  select ![(p["CreatedDate"].addMonths 6).as "Plus6M"]
}
def CDateTimeAddYears := query! {
  from p in products
  select ![(p["CreatedDate"].addYears 1).as "Plus1Y"]
}
def CDateTimeDiffDays := query! {
  from p in products
  select ![(p["CreatedDate"].diffDays (SqlExpr.dt "2025-01-01")).as "Diff"]
}
def CDateTimeDiffMonths := query! {
  from p in products
  select ![(p["CreatedDate"].diffMonths (SqlExpr.dt "2025-01-01")).as "Diff"]
}
def CDateTimeDiffYears := query! {
  from p in products
  select ![(p["CreatedDate"].diffYears (SqlExpr.dt "2025-01-01")).as "Diff"]
}
def CDateTimeFunctionsInWhere := query! {
  from p in products
  where p["CreatedDate"].year ==. 2024 &&. p["CreatedDate"].month >. 6
  select ![p["Id"].as "Id", p["CreatedDate"].as "CreatedDate"]
}
def CDateTimeFunctionsInSelect := query! {
  from p in products
  select ![p["Id"].as "Id", (p["CreatedDate"].year).as "CreatedYear",
           (p["CreatedDate"].month).as "CreatedMonth", (p["CreatedDate"].day).as "CreatedDay",
           (p["CreatedDate"].addDays 7).as "NextWeek",
           (p["CreatedDate"].addMonths 1).as "NextMonth",
           (p["CreatedDate"].diffDays SqlExpr.now).as "DaysAgo"]
}
def CDecimalRound := query! {
  from p in products
  select ![(p["Price"].round 2).as "Rounded"]
}
def CDecimalCeiling := query! {
  from p in products
  select ![(p["Price"].ceiling).as "Ceil"]
}
def CDecimalFloor := query! {
  from p in products
  select ![(p["Price"].floor).as "Floor"]
}
def CMathFunctionsInWhere := query! {
  from p in products
  where p["Price"].round 0 >. 100.0 &&. p["Price"].ceiling <. 1000.0
  select ![p["Id"].as "Id", p["Price"].as "Price"]
}
def CMathFunctionsInSelect := query! {
  from p in products
  select ![p["Id"].as "Id", p["Price"].as "OriginalPrice",
           (p["Price"].round 2).as "RoundedPrice", (p["Price"].ceiling).as "CeilingPrice",
           (p["Price"].floor).as "FloorPrice"]
}
def CFromLimitOffset := query! {
  from c in customers
  orderBy c["Id"].asc
  select c
  limit 5 offset 10
}
def CFromSelectLimitOffset := query! {
  from c in customers
  orderBy c["Id"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name"]
  limit 3 offset 5
}
def CFromWhereLimitOffset := query! {
  from c in customers
  where c["Age"] >. 18
  orderBy c["Id"].asc
  select c
  limit 10
}
def CFromWhereSelectLimitOffset := query! {
  from c in customers
  where c["Age"] >=. 21
  orderBy c["Id"].asc
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"]
  limit 5 offset 15
}
def CFromOrderByLimitOffset := query! {
  from c in customers
  orderBy c["Name"].asc
  select c
  limit 10 offset 5
}
def CFromWhereOrderByLimitOffset := query! {
  from c in customers
  where c["Age"] >. 18
  orderBy c["Age"].desc
  select c
  limit 20 offset 10
}
def CFromWhereOrderBySelectLimitOffset := query! {
  from c in customers
  where c["Name"] !=. ""
  orderBy c["Name"].asc, c["Age"].desc
  select ![c["Id"].as "Id", c["Name"].as "Name", c["Age"].as "Age"]
  limit 5
}
def CFromLimitOffsetOnly := query! {
  from c in customers
  orderBy c["Id"].asc
  select c
  limit 10
}
def CFromOffsetOnly := query! {
  from c in customers
  orderBy c["Id"].asc
  select c
  offset 5
}
def CFromLimitOffsetWithoutOrderBy := query! {
  from c in customers
  select c
  limit 10
}
def CFromSelectDistinct := query! {
  from c in customers
  select ![c["Name"].as "Name"]
  distinct
}
def CFromSelectDistinctWhere := query! {
  from c in customers
  where c["Age"] >. 18
  select ![c["Name"].as "Name"]
  distinct
}
def CFromSelectDistinctOrderBy := query! {
  from c in customers
  orderBy c["Name"].asc
  select ![c["Name"].as "Name"]
  distinct
}
def CFromSelectDistinctMultipleColumns := query! {
  from c in customers
  orderBy c["Name"].asc
  select ![c["Name"].as "Name", c["Age"].as "Age"]
  distinct
}
/-- Approximated: trailing `orderBy` (after `distinct`) is not a comprehension
clause, so the ordering fuses before DISTINCT/LIMIT — same rows, same order. -/
def CFromOrderByLimitDistinct := query! {
  from c in customers
  orderBy c["Name"].asc
  select ![c["Name"].as "Name"]
  distinct
  limit 2
}
def CUnion :=
  (query! {
    from c in customers
    where c["Age"] >. 30
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  }).union (query! {
    from c in customers
    where c["Name"] ==. "Alice"
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  })
def CIntersect :=
  (query! {
    from c in customers
    where c["Age"] >. 25
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  }).intersect (query! {
    from c in customers
    where c["Name"] ==. "John"
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  })
def CExcept :=
  (query! {
    from c in customers
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  }).except (query! {
    from c in customers
    where c["Age"] <. 18
    select ![c["Id"].as "Id", c["Name"].as "Name"]
  })

/-- Comprehension twins registry: `C<Original>` for every pipeline query. -/
def twinCases : List (String × Case) := [
  ("CFrom", q CFrom), ("CFromStatic", q CFromStatic), ("CFromSelect", q CFromSelect),
  ("CFromSelectSingle", q CFromSelectSingle),
  ("CFromSelectExpression", q CFromSelectExpression),
  ("CFromWhereInt", q CFromWhereInt), ("CFromWhereString", q CFromWhereString),
  ("CFromWhereMultiple", q CFromWhereMultiple), ("CFromWhereOr", q CFromWhereOr),
  ("CFromWhereAnd", q CFromWhereAnd), ("CFromOrderByAsc", q CFromOrderByAsc),
  ("CFromOrderByDesc", q CFromOrderByDesc), ("CFromWhereSelect", q CFromWhereSelect),
  ("CFromWhereAndSelect", q CFromWhereAndSelect),
  ("CFromWhereOrderBy", q CFromWhereOrderBy),
  ("CFromSelectOrderBy", q CFromSelectOrderBy),
  ("CFromWhereSelectOrderBy", q CFromWhereSelectOrderBy),
  ("CFromWhereOrderBySelect", q CFromWhereOrderBySelect),
  ("CFromWhereOrderBySelectNamed", q CFromWhereOrderBySelectNamed),
  ("CFromWhereSelectNamed", q CFromWhereSelectNamed),
  ("CFromProductWhereSelect", q CFromProductWhereSelect),
  ("CFromWhereSelectParameterized", q CFromWhereSelectParameterized),
  ("CFromWhereFusionTwo", q CFromWhereFusionTwo),
  ("CFromWhereFusionThree", q CFromWhereFusionThree),
  ("CFromWhereFusionWithSelect", q CFromWhereFusionWithSelect),
  ("CFromWhereFusionWithOrderBy", q CFromWhereFusionWithOrderBy),
  ("CFromOrderByThenBy", q CFromOrderByThenBy),
  ("CFromOrderByThenByDescending", q CFromOrderByThenByDescending),
  ("CFromOrderByDescendingThenBy", q CFromOrderByDescendingThenBy),
  ("CFromOrderByMultiple", q CFromOrderByMultiple),
  ("CFromWhereOrderByThenBy", q CFromWhereOrderByThenBy),
  ("CFromOrderByThenBySelect", q CFromOrderByThenBySelect),
  ("CFromWhereIsNull", q CFromWhereIsNull),
  ("CFromWhereIsNotNull", q CFromWhereIsNotNull),
  ("CFromWhereIsNullInt", q CFromWhereIsNullInt),
  ("CFromWhereIsNotNullInt", q CFromWhereIsNotNullInt),
  ("CFromWhereIsNullCombined", q CFromWhereIsNullCombined),
  ("CFromWhereAgeGreaterThanSum", q CFromWhereAgeGreaterThanSum),
  ("CSumAges", sq CSumAges), ("CCountCustomers", sq CCountCustomers),
  ("CCountActiveCustomers", sq CCountActiveCustomers), ("CSumPrices", sq CSumPrices),
  ("CAvgPrices", sq CAvgPrices), ("CMinPrice", sq CMinPrice), ("CMaxPrice", sq CMaxPrice),
  ("CSumExpensivePrices", sq CSumExpensivePrices),
  ("CAvgExpensivePrices", sq CAvgExpensivePrices),
  ("CFromWhereAgeGreaterThanAverageAge", q CFromWhereAgeGreaterThanAverageAge),
  ("CFromWhereAgeIn", q CFromWhereAgeIn),
  ("CFromWhereAgeInSubquery", q CFromWhereAgeInSubquery),
  ("CFromWhereAgeInSubqueryWithClosure", q CFromWhereAgeInSubqueryWithClosure),
  ("CFromSubquery", q CFromSubquery),
  ("CFromWhereSelectWhereFromNested", q CFromWhereSelectWhereFromNested),
  ("CFromWhereSelectWhereNested", q CFromWhereSelectWhereNested),
  ("CFromGroupBySelect", q CFromGroupBySelect),
  ("CFromGroupByMultipleSelect", q CFromGroupByMultipleSelect),
  ("CFromGroupByHavingSelect", q CFromGroupByHavingSelect),
  ("CFromWhereGroupBySelect", q CFromWhereGroupBySelect),
  ("CInnerJoinBasic", q CInnerJoinBasic),
  ("CInnerJoinWithSelect", q CInnerJoinWithSelect),
  ("CInnerJoinWithWhere", q CInnerJoinWithWhere),
  ("CInnerJoinWithOrderBy", q CInnerJoinWithOrderBy),
  ("CLeftJoinBasic", q CLeftJoinBasic), ("CLeftJoinWithSelect", q CLeftJoinWithSelect),
  ("CLeftJoinWithWhere", q CLeftJoinWithWhere),
  ("CLeftJoinWithOrderBy", q CLeftJoinWithOrderBy),
  ("CInnerJoinWithGroupBy", q CInnerJoinWithGroupBy),
  ("CLeftJoinWithAggregates", q CLeftJoinWithAggregates),
  ("CMultipleInnerJoinsFusion", q CMultipleInnerJoinsFusion),
  ("CMixedJoinTypesFusion", q CMixedJoinTypesFusion),
  ("CJoinFusionWithWhere", q CJoinFusionWithWhere),
  ("CFromGroupByOrderBySelect", q CFromGroupByOrderBySelect),
  ("CFromGroupByOrderByMultipleSelect", q CFromGroupByOrderByMultipleSelect),
  ("CFromGroupByOrderByThreeKeysSelect", q CFromGroupByOrderByThreeKeysSelect),
  ("CFromGroupByMultipleOrderBySelect", q CFromGroupByMultipleOrderBySelect),
  ("CFromGroupByHavingOrderBySelect", q CFromGroupByHavingOrderBySelect),
  ("CComplexJoinWhereGroupByHavingOrderBySelect", q CComplexJoinWhereGroupByHavingOrderBySelect),
  ("CComplexLeftJoinWhereGroupByOrderBySelect", q CComplexLeftJoinWhereGroupByOrderBySelect),
  ("CFromGroupByMinMaxSelect", q CFromGroupByMinMaxSelect),
  ("CFromGroupByAvgSelect", q CFromGroupByAvgSelect),
  ("CFromGroupByDecimalAggregatesSelect", q CFromGroupByDecimalAggregatesSelect),
  ("CFromGroupByDecimalSumSelect", q CFromGroupByDecimalSumSelect),
  ("CFromGroupByDecimalAvgSelect", q CFromGroupByDecimalAvgSelect),
  ("CFromSelectSum", sq CFromSelectSum), ("CFromSelectAvg", sq CFromSelectAvg),
  ("CFromSelectMin", sq CFromSelectMin), ("CFromSelectMax", sq CFromSelectMax),
  ("CParameterAsIntParam", q CParameterAsIntParam),
  ("CParameterAsStringParam", q CParameterAsStringParam),
  ("CParameterAsBoolParam", q CParameterAsBoolParam),
  ("CBoolColumnDirectComparison", q CBoolColumnDirectComparison),
  ("CBoolColumnLiteralTrue", q CBoolColumnLiteralTrue),
  ("CBoolColumnLiteralFalse", q CBoolColumnLiteralFalse),
  ("CCaseStringExpression", q CCaseStringExpression),
  ("CCaseIntExpression", q CCaseIntExpression),
  ("CCaseBoolExpression", q CCaseBoolExpression), ("CCaseInWhere", q CCaseInWhere),
  ("CLikeWildcard", q CLikeWildcard), ("CLikeSingleChar", q CLikeSingleChar),
  ("CLikeBothWildcards", q CLikeBothWildcards), ("CLikeExact", q CLikeExact),
  ("CAbsColumn", q CAbsColumn), ("CAbsInWhere", q CAbsInWhere),
  ("CAbsExpression", q CAbsExpression), ("CAbsParameter", q CAbsParameter),
  ("CFromWhereDecimalComparison", q CFromWhereDecimalComparison),
  ("CFromSelectDecimalArithmetic", q CFromSelectDecimalArithmetic),
  ("CFromWhereDecimalIsNull", q CFromWhereDecimalIsNull),
  ("CFromWhereDecimalIsNotNull", q CFromWhereDecimalIsNotNull),
  ("CCaseDecimalExpression", q CCaseDecimalExpression),
  ("CParameterAsDecimalParam", q CParameterAsDecimalParam),
  ("CFromWhereCreatedDateComparison", q CFromWhereCreatedDateComparison),
  ("CFromWhereCreatedDateIsNull", q CFromWhereCreatedDateIsNull),
  ("CFromWhereCreatedDateIsNotNull", q CFromWhereCreatedDateIsNotNull),
  ("CFromSelectCreatedDateMinMax", q CFromSelectCreatedDateMinMax),
  ("CCaseDateTimeExpression", q CCaseDateTimeExpression),
  ("CParameterAsDateTimeParam", q CParameterAsDateTimeParam),
  ("CFromWhereUniqueIdEquals", q CFromWhereUniqueIdEquals),
  ("CFromWhereUniqueIdNotEquals", q CFromWhereUniqueIdNotEquals),
  ("CFromWhereUniqueIdIsNull", q CFromWhereUniqueIdIsNull),
  ("CFromWhereUniqueIdIsNotNull", q CFromWhereUniqueIdIsNotNull),
  ("CCaseGuidExpression", q CCaseGuidExpression),
  ("CParameterAsGuidParam", q CParameterAsGuidParam),
  ("CStringSubstring", q CStringSubstring), ("CStringUpper", q CStringUpper),
  ("CStringLower", q CStringLower), ("CStringTrim", q CStringTrim),
  ("CStringLength", q CStringLength),
  ("CStringFunctionsInWhere", q CStringFunctionsInWhere),
  ("CStringFunctionsInSelect", q CStringFunctionsInSelect),
  ("CDateTimeNow", q CDateTimeNow), ("CDateTimeYear", q CDateTimeYear),
  ("CDateTimeMonth", q CDateTimeMonth), ("CDateTimeDay", q CDateTimeDay),
  ("CDateTimeAddDays", q CDateTimeAddDays), ("CDateTimeAddMonths", q CDateTimeAddMonths),
  ("CDateTimeAddYears", q CDateTimeAddYears), ("CDateTimeDiffDays", q CDateTimeDiffDays),
  ("CDateTimeDiffMonths", q CDateTimeDiffMonths),
  ("CDateTimeDiffYears", q CDateTimeDiffYears),
  ("CDateTimeFunctionsInWhere", q CDateTimeFunctionsInWhere),
  ("CDateTimeFunctionsInSelect", q CDateTimeFunctionsInSelect),
  ("CDecimalRound", q CDecimalRound), ("CDecimalCeiling", q CDecimalCeiling),
  ("CDecimalFloor", q CDecimalFloor), ("CMathFunctionsInWhere", q CMathFunctionsInWhere),
  ("CMathFunctionsInSelect", q CMathFunctionsInSelect),
  ("CFromLimitOffset", q CFromLimitOffset),
  ("CFromSelectLimitOffset", q CFromSelectLimitOffset),
  ("CFromWhereLimitOffset", q CFromWhereLimitOffset),
  ("CFromWhereSelectLimitOffset", q CFromWhereSelectLimitOffset),
  ("CFromOrderByLimitOffset", q CFromOrderByLimitOffset),
  ("CFromWhereOrderByLimitOffset", q CFromWhereOrderByLimitOffset),
  ("CFromWhereOrderBySelectLimitOffset", q CFromWhereOrderBySelectLimitOffset),
  ("CFromLimitOffsetOnly", q CFromLimitOffsetOnly),
  ("CFromOffsetOnly", q CFromOffsetOnly),
  ("CFromLimitOffsetWithoutOrderBy", q CFromLimitOffsetWithoutOrderBy),
  ("CFromSelectDistinct", q CFromSelectDistinct),
  ("CFromSelectDistinctWhere", q CFromSelectDistinctWhere),
  ("CFromSelectDistinctOrderBy", q CFromSelectDistinctOrderBy),
  ("CFromSelectDistinctMultipleColumns", q CFromSelectDistinctMultipleColumns),
  ("CFromOrderByLimitDistinct", q CFromOrderByLimitDistinct),
  ("CUnion", q CUnion), ("CIntersect", q CIntersect), ("CExcept", q CExcept)
]

end TQ
