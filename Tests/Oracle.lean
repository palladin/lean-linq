/-! # In-memory oracle: executable query semantics over the seed data

Every deterministic integration case has its expected rows *computed* here by
Lean list pipelines that mirror the SQL semantics — `where'`/`filter`,
`select`/`map`, joins as `flatMap`, GROUP BY as grouping + aggregation,
ORDER BY as stable sorts, LIMIT/OFFSET as `take`/`drop` — the LINQ-to-objects
side of language-integrated query. NULL semantics ride on `Option` (SQL
comparisons with NULL are not satisfied ⇒ `Option.any`; aggregates ignore
NULLs ⇒ `filterMap`), decimals are exact fixed-point (milli-units), and date
arithmetic uses the standard civil-calendar algorithms.

Cases with no single correct answer are absent: time-dependent (`DateTimeNow`,
`DateTimeFunctionsInSelect`), engine-variant integer AVG (`FromSelectAvg`),
and the all-ties ORDER BY (`FromGroupByMultipleOrderBySelect`). -/

namespace Oracle

/-! ## LINQ-to-objects vocabulary -/

def _root_.List.where' (xs : List α) (p : α → Bool) : List α := xs.filter p
def _root_.List.select (xs : List α) (f : α → β) : List β := xs.map f
def _root_.List.orderBy' (xs : List α) (le : α → α → Bool) : List α := xs.mergeSort le

def innerJoin (xs : List α) (ys : List β) (on : α → β → Bool) : List (α × β) :=
  xs.flatMap fun x => (ys.where' (on x)).select ((x, ·))

def leftJoin (xs : List α) (ys : List β) (on : α → β → Bool) : List (α × Option β) :=
  xs.flatMap fun x =>
    match ys.where' (on x) with
    | [] => [(x, none)]
    | ms => ms.select ((x, some ·))

def groupOn [BEq κ] (xs : List α) (key : α → κ) : List (κ × List α) :=
  ((xs.select key).eraseDups).select fun k => (k, xs.where' (key · == k))

def sumBy (xs : List α) (f : α → Int) : Int := xs.foldl (· + f ·) 0
def minBy (xs : List α) (f : α → Int) : Int := (xs.select f).foldl min ((xs.select f).headD 0)
def maxBy (xs : List α) (f : α → Int) : Int := (xs.select f).foldl max ((xs.select f).headD 0)

/-- SQL aggregate over a nullable column: NULLs are ignored; all-NULL ⇒ NULL. -/
def sumOpt (xs : List (Option Int)) : Option Int :=
  match xs.filterMap id with
  | [] => none
  | vs => some (vs.foldl (· + ·) 0)

/-- SQL `LIKE` (`%` any run, `_` any char). -/
def like (s pat : String) : Bool := go pat.toList s.toList
where
  go : List Char → List Char → Bool
    | [], cs => cs.isEmpty
    | '%' :: ps, cs =>
        go ps cs || (match cs with
          | [] => false
          | _ :: cs' => go ('%' :: ps) cs')
    | '_' :: ps, _ :: cs => go ps cs
    | p :: ps, c :: cs => p == c && go ps cs
    | _ :: _, [] => false
  termination_by ps cs => (cs.length, ps.length)

/-! ## Exact decimals: milli-units (3 fractional digits) -/

/-- Render milli-units with trailing zeros trimmed: `999990 → "999.99"`,
`25500 → "25.5"`, `1099989 → "1099.989"`, `1000000 → "1000"`. -/
def dec (millis : Int) : String :=
  let v := millis.natAbs
  let whole := v / 1000
  let frac := v % 1000
  let body :=
    if frac == 0 then s!"{whole}"
    else if frac % 100 == 0 then s!"{whole}.{frac / 100}"
    else if frac % 10 == 0 then
      let f2 := frac / 10
      s!"{whole}." ++ (if f2 < 10 then s!"0{f2}" else s!"{f2}")
    else
      s!"{whole}." ++ (if frac < 10 then s!"00{frac}" else if frac < 100 then s!"0{frac}" else s!"{frac}")
  if millis < 0 then s!"-{body}" else body

def roundTo (digits : Nat) (millis : Int) : Int :=
  let unit : Int := if digits == 0 then 1000 else if digits == 1 then 100 else if digits == 2 then 10 else 1
  ((millis + unit / 2) / unit) * unit
def ceilTo0 (millis : Int) : Int := ((millis + 999) / 1000) * 1000
def floorTo0 (millis : Int) : Int := (millis / 1000) * 1000

/-! ## Civil-date arithmetic (all seed times are midnight) -/

def parseYMD (s : String) : Int × Int × Int :=
  let cs := s.toList
  let num (l : List Char) : Int := ((String.ofList l).toNat?).getD 0
  (num (cs.take 4), num ((cs.drop 5).take 2), num ((cs.drop 8).take 2))

def daysFromCivil (ymd : Int × Int × Int) : Int :=
  let (y, m, d) := ymd
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := mp + (if mp < 10 then 3 else -9)
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

def pad2 (n : Int) : String := if n < 10 then s!"0{n}" else s!"{n}"
def fmtDT (ymd : Int × Int × Int) : String :=
  s!"{ymd.1}-{pad2 ymd.2.1}-{pad2 ymd.2.2} 00:00:00"

def addDays (s : String) (n : Int) : String :=
  fmtDT (civilFromDays (daysFromCivil (parseYMD s) + n))
def addMonths (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  let t := y * 12 + (m - 1) + n
  fmtDT (t / 12, t % 12 + 1, d)
def addYears (s : String) (n : Int) : String :=
  let (y, m, d) := parseYMD s
  fmtDT (y + n, m, d)
def diffDays (a b : String) : Int := daysFromCivil (parseYMD b) - daysFromCivil (parseYMD a)
def diffMonths (a b : String) : Int :=
  let (ya, ma, _) := parseYMD a; let (yb, mb, _) := parseYMD b
  (yb - ya) * 12 + (mb - ma)
def diffYears (a b : String) : Int := (parseYMD b).1 - (parseYMD a).1

def substr (s : String) (start len : Nat) : String :=
  String.ofList ((s.toList.drop (start - 1)).take len)

/-! ## Seed data (mirrors `setupSql` in the integration runner) -/

structure Cust where
  id : Int
  age : Int
  name : String
  active : Bool

def customers : List Cust :=
  [⟨1, 25, "John Doe", true⟩, ⟨2, 30, "Jane Smith", true⟩,
   ⟨3, 16, "Minor User", false⟩, ⟨4, 65, "Senior User", true⟩]

structure Product where
  id : Int
  name : String
  priceM : Option Int          -- milli-units: 999.99 = 999990
  created : Option String
  uid : Option String

def products : List Product :=
  [⟨1, "Laptop", some 999990, some "2023-01-15 00:00:00",
    some "11111111-1111-1111-1111-111111111111"⟩,
   ⟨2, "Mouse", some 25500, some "2023-06-10 00:00:00",
    some "22222222-2222-2222-2222-222222222222"⟩,
   ⟨3, "Discontinued", none, none, none⟩]

structure Order where
  id : Int
  customerId : Int
  productId : Int
  amount : Int

def orders : List Order :=
  [⟨1, 1, 1, 500⟩, ⟨2, 1, 2, 150⟩, ⟨3, 2, 1, 300⟩, ⟨4, 4, 2, 75⟩]

/-! ## Cell rendering (the harness's normalized format) -/

def ci (n : Int) : String := toString n
def cb (v : Bool) : String := if v then "1" else "0"
def nullC : String := "NULL"
def optS (v : Option String) : String := v.getD nullC
def optI (v : Option Int) : String := (v.map ci).getD nullC
def optD (v : Option Int) : String := (v.map dec).getD nullC

def custRow (c : Cust) : List String := [ci c.id, ci c.age, c.name, cb c.active]
def prodRow (p : Product) : List String :=
  [ci p.id, p.name, optD p.priceM, optS p.created, optS p.uid]

structure OCase where
  rows : List (List String)
  /-- Whether the query fixes row order (ORDER BY / statement verification);
  unordered cases are compared after lexicographic sorting, mirroring the
  harness. -/
  ordered : Bool

def u (rows : List (List String)) : OCase := ⟨rows, false⟩
def o (rows : List (List String)) : OCase := ⟨rows, true⟩

def render (c : OCase) : String :=
  let rows := c.rows.select (String.intercalate ",")
  let rows := if c.ordered then rows else rows.mergeSort (fun a b => a ≤ b)
  String.intercalate "|" rows

/-! ## The oracle: each case is an executable mirror of its query -/

private def sumAges : Int := sumBy customers (·.age)
private def joinedCO := innerJoin customers orders (fun c o => c.id == o.customerId)

def oracles : List (String × OCase) := [
  -- FROM / SELECT / WHERE
  ("From", u (customers.select custRow)),
  ("FromStatic", u (customers.select custRow)),
  ("FromSelect", u (customers.select fun c => [ci c.id, c.name])),
  ("FromSelectSingle", u (customers.select fun c => [ci c.age])),
  ("FromSelectExpression", u (customers.select fun c =>
    [ci (c.id * 100), c.name ++ " - Customer"])),
  ("FromWhereInt", u (customers.where' (·.age > 18) |>.select custRow)),
  ("FromWhereString", u (customers.where' (·.name == "John") |>.select custRow)),
  ("FromWhereMultiple", u
    (customers.where' (fun c => c.age > 18 && c.name != "Admin") |>.select custRow)),
  ("FromWhereOr", u
    (customers.where' (fun c => (c.age > 18 && c.age < 65) || c.name == "VIP")
      |>.select custRow)),
  ("FromWhereAnd", u
    (customers.where' (fun c => c.age > 18 && c.name == "John") |>.select custRow)),
  ("FromOrderByAsc", o (customers.orderBy' (·.name ≤ ·.name) |>.select custRow)),
  ("FromOrderByDesc", o (customers.orderBy' (·.age ≥ ·.age) |>.select custRow)),
  ("FromWhereSelect", u
    (customers.where' (·.age ≥ 21) |>.select fun c => [ci c.id, c.name])),
  ("FromWhereAndSelect", u
    (customers.where' (fun c => c.age ≥ 21 && c.name != "")
      |>.select fun c => [ci c.id, c.name])),
  ("FromWhereOrderBy", o
    (customers.where' (fun c => c.age > 21 && c.name != "")
      |>.orderBy' (·.age ≤ ·.age) |>.select custRow)),
  ("FromSelectOrderBy", o
    (customers.orderBy' (·.name ≤ ·.name)
      |>.select fun c => [ci c.id, c.name, ci (c.age + 5)])),
  ("FromWhereSelectOrderBy", o
    (customers.where' (·.age > 18) |>.orderBy' (·.name ≤ ·.name)
      |>.select fun c => [ci (c.id + 1), c.name ++ "!"])),
  ("FromWhereOrderBySelect", o
    (customers.where' (fun c => c.age > 21 && c.name != "")
      |>.orderBy' (·.age ≤ ·.age)
      |>.select fun c => [ci c.id, c.name, ci (c.age + 10)])),
  ("FromWhereOrderBySelectNamed", o
    (customers.where' (fun c => c.age ≥ 21 && c.name != "")
      |>.orderBy' (·.name ≤ ·.name)
      |>.select fun c => [ci c.id, c.name ++ " (Customer)", ci (c.age + 5)])),
  ("FromWhereSelectNamed", u
    (customers.where' (·.age > 18)
      |>.select fun c => [ci c.id, ci (c.id * 100), c.name])),
  ("FromProductWhereSelect", u
    (products.where' (·.name != "Discontinued") |>.select fun p => [ci p.id, p.name])),
  ("FromWhereSelectParameterized", u
    (customers.where' (fun c => c.age ≥ 18 && c.age ≤ 65)
      |>.select fun c => [ci c.id, c.name])),
  -- WHERE fusion
  ("FromWhereFusionTwo", u
    (customers.where' (·.age > 18) |>.where' (·.name != "Admin") |>.select custRow)),
  ("FromWhereFusionThree", u
    (customers.where' (·.age > 18) |>.where' (·.name != "Admin")
      |>.where' (·.age < 65) |>.select custRow)),
  ("FromWhereFusionWithSelect", u
    (customers.where' (·.age ≥ 21) |>.where' (·.name != "")
      |>.select fun c => [ci c.id, c.name])),
  ("FromWhereFusionWithOrderBy", o
    (customers.where' (·.age > 18) |>.where' (·.name != "Admin")
      |>.orderBy' (·.name ≤ ·.name) |>.select custRow)),
  -- multi-key ORDER BY (stable sorts compose ThenBy lexicographically)
  ("FromOrderByThenBy", o
    (customers.orderBy' (fun a b => a.name < b.name || (a.name == b.name && a.age ≤ b.age))
      |>.select custRow)),
  ("FromOrderByThenByDescending", o
    (customers.orderBy' (fun a b => a.name < b.name || (a.name == b.name && a.age ≥ b.age))
      |>.select custRow)),
  ("FromOrderByDescendingThenBy", o
    (customers.orderBy' (fun a b => a.age > b.age || (a.age == b.age && a.name ≤ b.name))
      |>.select custRow)),
  ("FromOrderByMultiple", o
    (customers.orderBy' (fun a b => a.name < b.name ||
        (a.name == b.name && (a.age > b.age || (a.age == b.age && a.id ≤ b.id))))
      |>.select custRow)),
  ("FromWhereOrderByThenBy", o
    (customers.where' (·.age > 18)
      |>.orderBy' (fun a b => a.name < b.name || (a.name == b.name && a.age ≥ b.age))
      |>.select custRow)),
  ("FromOrderByThenBySelect", o
    (customers.orderBy' (fun a b => a.name < b.name || (a.name == b.name && a.age ≤ b.age))
      |>.select fun c => [ci c.id, c.name])),
  -- NULL checks (customer columns are non-null in the seed)
  ("FromWhereIsNull", u []),
  ("FromWhereIsNotNull", u (customers.select custRow)),
  ("FromWhereIsNullInt", u []),
  ("FromWhereIsNotNullInt", u (customers.select custRow)),
  ("FromWhereIsNullCombined", u []),
  -- scalar aggregates
  ("FromWhereAgeGreaterThanSum", u
    (customers.where' (·.age > sumAges) |>.select custRow)),
  ("SumAges", u [[ci sumAges]]),
  ("CountCustomers", u [[ci customers.length]]),
  ("CountActiveCustomers", u [[ci (customers.where' (·.age ≥ 18)).length]]),
  ("SumPrices", u [[optD (sumOpt (products.select (·.priceM)))]]),
  ("AvgPrices", u
    (let vs := products.select (·.priceM) |>.filterMap id
     [[dec (sumBy vs id / vs.length)]])),
  ("MinPrice", u [[dec (minBy (products.filterMap (·.priceM)) id)]]),
  ("MaxPrice", u [[dec (maxBy (products.filterMap (·.priceM)) id)]]),
  ("SumExpensivePrices", u
    [[optD (sumOpt ((products.where' (·.priceM.any (· > 100000))).select (·.priceM)))]]),
  ("AvgExpensivePrices", u
    (let vs := (products.where' (·.priceM.any (· > 100000))).filterMap (·.priceM)
     [[dec (sumBy vs id / vs.length)]])),
  ("FromWhereAgeGreaterThanAverageAge", u
    (customers.where' (·.age > sumAges) |>.select custRow)),
  -- IN / subqueries
  ("FromWhereAgeIn", u
    (customers.where' (fun c => [18, 21, 25, 30].contains c.age) |>.select custRow)),
  ("FromWhereAgeInSubquery", u
    (let vipAges := customers.where' (·.name == "VIP") |>.select (·.age)
     customers.where' (fun c => vipAges.contains c.age) |>.select custRow)),
  ("FromWhereAgeInSubqueryWithClosure", u
    (customers.where' (fun c =>
        (customers.where' (·.name == c.name ++ "_VIP") |>.select (·.age)).contains c.age)
      |>.select custRow)),
  ("FromSubquery", u
    (customers.select (fun c => (c.id, c.age + 1))
      |>.select fun (id, newAge) => [ci id, ci newAge])),
  ("FromWhereSelectWhereFromNested", u
    (customers.where' (·.age > 18) |>.select (fun c => (c.id, c.name))
      |>.where' (fun x => x.1 > 100) |>.select fun (id, n) => [ci id, n])),
  ("FromWhereSelectWhereNested", u
    (customers.where' (·.age > 18) |>.select (fun c => (c.id, c.name))
      |>.where' (fun x => x.1 > 100) |>.select fun (id, n) => [ci id, n])),
  -- GROUP BY
  ("FromGroupBySelect", u
    (groupOn customers (·.age) |>.select fun (age, g) => [ci age, ci g.length])),
  ("FromGroupByMultipleSelect", u
    (groupOn customers (fun c => (c.age, c.name))
      |>.select fun ((age, name), g) => [ci age, name, ci g.length])),
  ("FromGroupByHavingSelect", u
    (groupOn customers (·.age) |>.where' (fun (_, g) => g.length > 1)
      |>.select fun (age, g) => [ci age, ci g.length])),
  ("FromWhereGroupBySelect", u
    (groupOn (customers.where' (·.age ≥ 18)) (·.age)
      |>.select fun (age, g) => [ci age, ci g.length])),
  -- joins
  ("InnerJoinBasic", u
    (joinedCO.select fun (c, oo) => [ci c.id, c.name, ci oo.id, ci oo.amount])),
  ("InnerJoinWithSelect", u
    (joinedCO.select fun (c, oo) => [c.name, ci oo.amount])),
  ("InnerJoinWithWhere", u
    (innerJoin (customers.where' (·.age ≥ 18)) orders (fun c oo => c.id == oo.customerId)
      |>.where' (fun (_, oo) => oo.amount > 100)
      |>.select fun (c, oo) => [ci c.id, c.name, ci c.age, ci oo.id, ci oo.amount])),
  ("InnerJoinWithOrderBy", o
    (joinedCO.orderBy' (fun a b => a.1.name ≤ b.1.name)
      |>.select fun (c, oo) => [ci c.id, c.name, ci oo.id, ci oo.amount])),
  ("LeftJoinBasic", u
    (leftJoin customers orders (fun c oo => c.id == oo.customerId)
      |>.select fun (c, oo?) =>
        [ci c.id, c.name, optI (oo?.map (·.id)), optI (oo?.map (·.amount))])),
  ("LeftJoinWithSelect", u
    (leftJoin customers orders (fun c oo => c.id == oo.customerId)
      |>.select fun (c, oo?) => [c.name ++ " (Customer)", optI (oo?.map (·.amount))])),
  ("LeftJoinWithWhere", u
    (leftJoin (customers.where' (·.age ≥ 21)) orders (fun c oo => c.id == oo.customerId)
      |>.where' (fun (c, _) => c.age < 65)
      |>.select fun (c, oo?) =>
        [ci c.id, c.name, ci c.age, optI (oo?.map (·.id)), optI (oo?.map (·.amount))])),
  ("LeftJoinWithOrderBy", o
    (leftJoin customers orders (fun c oo => c.id == oo.customerId)
      |>.orderBy' (fun a b => a.1.name < b.1.name ||
          (a.1.name == b.1.name &&
            (a.2.map (·.amount) |>.getD (-1)) ≥ (b.2.map (·.amount) |>.getD (-1))))
      |>.select fun (c, oo?) =>
        [ci c.id, c.name, optI (oo?.map (·.id)), optI (oo?.map (·.amount))])),
  ("InnerJoinWithGroupBy", u
    (groupOn joinedCO (fun (c, _) => (c.id, c.name))
      |>.select fun ((id, name), g) => [ci id, name, ci (sumBy g (·.2.amount))])),
  ("LeftJoinWithAggregates", u
    (groupOn (leftJoin customers orders (fun c oo => c.id == oo.customerId)) (·.1.id)
      |>.select fun (id, g) =>
        [ci id, ci g.length, optI (sumOpt (g.select (·.2.map (·.amount))))])),
  ("MultipleInnerJoinsFusion", u
    (innerJoin joinedCO products (fun (_, oo) p => oo.productId == p.id)
      |>.select fun ((c, oo), p) => [ci c.id, c.name, ci oo.productId, p.name])),
  ("MixedJoinTypesFusion", u
    (leftJoin joinedCO products (fun (_, oo) p => oo.productId == p.id)
      |>.select fun ((c, oo), p?) => [ci c.id, c.name, ci oo.productId, optS (p?.map (·.name))])),
  ("JoinFusionWithWhere", u
    (innerJoin (innerJoin (customers.where' (·.age ≥ 18)) orders
        (fun c oo => c.id == oo.customerId)) products (fun (_, oo) p => oo.productId == p.id)
      |>.where' (fun ((_, oo), _) => oo.amount > 100)
      |>.select fun ((c, oo), p) => [ci c.id, c.name, ci oo.amount, p.name])),
  -- GROUP BY + ORDER BY (order by the aggregated output)
  ("FromGroupByOrderBySelect", o
    (groupOn orders (·.customerId)
      |>.select (fun (k, g) => (k, sumBy g (·.amount)))
      |>.orderBy' (fun a b => a.2 ≥ b.2)
      |>.select fun (k, total) => [ci k, ci total])),
  ("FromGroupByOrderByMultipleSelect", o
    (groupOn orders (·.customerId)
      |>.select (fun (k, g) => (k, sumBy g (·.amount), g.length))
      |>.orderBy' (fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2))
      |>.select fun (k, total, cnt) => [ci k, ci total, ci cnt])),
  ("FromGroupByOrderByThreeKeysSelect", o
    (groupOn orders (·.customerId)
      |>.select (fun (k, g) => (k, sumBy g (·.amount), g.length))
      |>.orderBy' (fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 &&
          (a.2.2 < b.2.2 || (a.2.2 == b.2.2 && a.1 ≤ b.1))))
      |>.select fun (k, total, cnt) => [ci k, ci total, ci cnt])),
  ("FromGroupByHavingOrderBySelect", o
    (groupOn orders (·.customerId)
      |>.where' (fun (_, g) => g.length > 1)
      |>.select (fun (k, g) => (k, sumBy g (·.amount)))
      |>.orderBy' (fun a b => a.2 ≥ b.2)
      |>.select fun (k, total) => [ci k, ci total])),
  ("ComplexJoinWhereGroupByHavingOrderBySelect", o
    (groupOn (joinedCO.where' fun (c, oo) => c.age ≥ 18 && oo.amount > 50)
        (fun (c, _) => (c.id, c.name))
      |>.where' (fun (_, g) => g.length > 2 && sumBy g (·.2.amount) > 500)
      |>.select (fun ((id, name), g) =>
          (id, name, g.length, sumBy g (·.2.amount), sumBy g (·.2.amount) / g.length))
      |>.orderBy' (fun a b => a.2.2.2.1 > b.2.2.2.1 ||
          (a.2.2.2.1 == b.2.2.2.1 && a.2.2.1 ≤ b.2.2.1))
      |>.select fun (id, name, cnt, total, avg) =>
        [ci id, name, ci cnt, ci total, ci avg])),
  ("ComplexLeftJoinWhereGroupByOrderBySelect", o
    (groupOn ((leftJoin customers orders (fun c oo => c.id == oo.customerId)).where'
        fun (c, _) => c.age ≥ 21) (fun (c, _) => (c.id, c.name))
      |>.select (fun ((id, name), g) =>
          (id, name, g.length, (sumOpt (g.select (·.2.map (·.amount)))).getD 0))
      |>.orderBy' (fun a b => a.2.2.2 > b.2.2.2 || (a.2.2.2 == b.2.2.2 && a.2.1 ≤ b.2.1))
      |>.select fun (id, name, cnt, total) => [ci id, name, ci cnt, ci total])),
  ("FromGroupByMinMaxSelect", u
    (groupOn orders (·.customerId)
      |>.select fun (k, g) =>
        [ci k, ci (minBy g (·.amount)), ci (maxBy g (·.amount)), ci g.length])),
  ("FromGroupByAvgSelect", u
    (groupOn orders (·.customerId)
      |>.select fun (k, g) => [ci k, ci (sumBy g (·.amount) / g.length), ci g.length])),
  ("FromGroupByDecimalAggregatesSelect", u
    (groupOn products (·.name)
      |>.select fun (name, g) =>
        let vs := g.filterMap (·.priceM)
        [name, optD (sumOpt (g.select (·.priceM))),
         optD (if vs.isEmpty then none else some (sumBy vs id / vs.length)),
         optD (if vs.isEmpty then none else some (minBy vs id)),
         optD (if vs.isEmpty then none else some (maxBy vs id)),
         ci g.length])),
  ("FromGroupByDecimalSumSelect", u
    (groupOn products (·.name)
      |>.select fun (name, g) => [name, optD (sumOpt (g.select (·.priceM)))])),
  ("FromGroupByDecimalAvgSelect", u
    (groupOn products (·.name)
      |>.select fun (name, g) =>
        let vs := g.filterMap (·.priceM)
        [name, optD (if vs.isEmpty then none else some (sumBy vs id / vs.length))])),
  ("FromSelectSum", u [[ci (sumBy orders (·.amount))]]),
  ("FromSelectMin", u [[ci (minBy orders (·.amount))]]),
  ("FromSelectMax", u [[ci (maxBy orders (·.amount))]]),
  -- parameters / booleans (bindings: minAge=18, customerName="John Doe", …)
  ("ParameterAsIntParam", u
    (customers.where' (·.age > 18) |>.select fun c => [ci c.id, c.name])),
  ("ParameterAsStringParam", u
    (customers.where' (·.name == "John Doe") |>.select fun c => [ci c.id, ci c.age])),
  ("ParameterAsBoolParam", u
    (customers.where' (fun c => (c.age > 18) == true)
      |>.select fun c => [ci c.id, c.name, ci c.age])),
  ("BoolColumnDirectComparison", u
    (customers.where' (·.active == true)
      |>.select fun c => [ci c.id, c.name, ci c.age, cb c.active])),
  ("BoolColumnLiteralTrue", u
    (customers.where' (·.active == true)
      |>.select fun c => [ci c.id, c.name, ci c.age, cb c.active])),
  ("BoolColumnLiteralFalse", u
    (customers.where' (·.active == false)
      |>.select fun c => [ci c.id, c.name, ci c.age, cb c.active])),
  -- CASE
  ("CaseStringExpression", u
    (customers.select fun c => [ci c.id, if c.age > 18 then "Adult" else "Minor"])),
  ("CaseIntExpression", u
    (customers.select fun c => [ci c.id, ci (if c.age > 65 then 1 else 0)])),
  ("CaseBoolExpression", u
    (customers.select fun c => [ci c.id, cb (if c.age > 18 then c.active else false)])),
  ("CaseInWhere", u
    (customers.where' (fun c => (if c.age > 18 then "Adult" else "Minor") == "Adult")
      |>.select fun c => [ci c.id, c.name])),
  -- LIKE
  ("LikeWildcard", u
    (customers.where' (like ·.name "Jo%") |>.select fun c => [ci c.id, c.name])),
  ("LikeSingleChar", u
    (customers.where' (like ·.name "J_n") |>.select fun c => [ci c.id, c.name])),
  ("LikeBothWildcards", u
    (customers.where' (like ·.name "%o_n%") |>.select fun c => [ci c.id, c.name])),
  ("LikeExact", u
    (customers.where' (like ·.name "John") |>.select fun c => [ci c.id, c.name])),
  -- ABS
  ("AbsColumn", u (customers.select fun c => [ci c.id, ci c.age.natAbs])),
  ("AbsInWhere", u
    (customers.where' (fun c => (c.age.natAbs : Int) > 30)
      |>.select fun c => [ci c.id, c.name, ci c.age])),
  ("AbsExpression", u (customers.select fun c => [ci c.id, ci (c.age - 50).natAbs])),
  ("AbsParameter", u
    (customers.where' (fun c => (c.age.natAbs : Int) > (18 : Int).natAbs)
      |>.select fun c => [ci c.id, c.name, ci c.age])),
  -- decimal column
  ("FromWhereDecimalComparison", u
    (products.where' (·.priceM.any (· > 100500)) |>.select prodRow)),
  ("FromSelectDecimalArithmetic", u
    (products.select fun p =>
      [p.name, optD (p.priceM.map (fun v => v * 11 / 10)),
       optD (p.priceM.map (· + 10000)), optD (p.priceM.map (· - 5000))])),
  ("FromWhereDecimalIsNull", u (products.where' (·.priceM.isNone) |>.select prodRow)),
  ("FromWhereDecimalIsNotNull", u (products.where' (·.priceM.isSome) |>.select prodRow)),
  ("CaseDecimalExpression", u
    (products.select fun p =>
      [p.name, if p.priceM.any (· > 1000000) then "Expensive"
               else if p.priceM.any (· > 100000) then "Moderate" else "Cheap"])),
  ("ParameterAsDecimalParam", u
    (products.where' (·.priceM.any (· > 100000)) |>.select prodRow)),
  -- dateTime column
  ("FromWhereCreatedDateComparison", u
    (products.where' (·.created.any (· > "2024-01-01")) |>.select prodRow)),
  ("FromWhereCreatedDateIsNull", u (products.where' (·.created.isNone) |>.select prodRow)),
  ("FromWhereCreatedDateIsNotNull", u (products.where' (·.created.isSome) |>.select prodRow)),
  ("FromSelectCreatedDateMinMax", u
    (products.select fun p => [p.name, optS p.created, optS p.created])),
  ("CaseDateTimeExpression", u
    (products.select fun p =>
      [p.name, if p.created.any (· < "2020-01-01") then "Old"
               else if p.created.any (· < "2024-01-01") then "Recent" else "New"])),
  ("ParameterAsDateTimeParam", u
    (products.where' (·.created.any (· > "2023-01-01")) |>.select prodRow)),
  -- guid column
  ("FromWhereUniqueIdEquals", u
    (products.where' (·.uid.any (· == "12345678-1234-1234-1234-123456789012"))
      |>.select prodRow)),
  ("FromWhereUniqueIdNotEquals", u
    (products.where' (·.uid.any (· != "00000000-0000-0000-0000-000000000000"))
      |>.select prodRow)),
  ("FromWhereUniqueIdIsNull", u (products.where' (·.uid.isNone) |>.select prodRow)),
  ("FromWhereUniqueIdIsNotNull", u (products.where' (·.uid.isSome) |>.select prodRow)),
  ("CaseGuidExpression", u
    (products.select fun p =>
      [p.name, if p.uid.any (· == "00000000-0000-0000-0000-000000000000")
               then "Empty" else "HasId"])),
  ("ParameterAsGuidParam", u
    (products.where' (·.uid.any (· == "11111111-1111-1111-1111-111111111111"))
      |>.select prodRow)),
  -- string functions
  ("StringSubstring", u (products.select fun p => [substr p.name 1 5])),
  ("StringUpper", u (products.select fun p => [p.name.toUpper])),
  ("StringLower", u (products.select fun p => [p.name.toLower])),
  ("StringTrim", u (products.select fun p => [p.name.trimAscii.toString])),
  ("StringLength", u (products.select fun p => [ci p.name.length])),
  ("StringFunctionsInWhere", u
    (customers.where' (fun c => c.name.toUpper == "JOHN" && c.name.length > 3)
      |>.select fun c => [ci c.id, c.name])),
  ("StringFunctionsInSelect", u
    (customers.select fun c =>
      [ci c.id, c.name.toUpper, c.name.toLower, c.name.trimAscii.toString,
       ci c.name.length, substr c.name 1 3])),
  -- date functions (fixed target date 2025-01-01)
  ("DateTimeYear", u (products.select fun p => [optI (p.created.map fun s => (parseYMD s).1)])),
  ("DateTimeMonth", u (products.select fun p => [optI (p.created.map fun s => (parseYMD s).2.1)])),
  ("DateTimeDay", u (products.select fun p => [optI (p.created.map fun s => (parseYMD s).2.2)])),
  ("DateTimeAddDays", u (products.select fun p => [optS (p.created.map (addDays · 30))])),
  ("DateTimeAddMonths", u (products.select fun p => [optS (p.created.map (addMonths · 6))])),
  ("DateTimeAddYears", u (products.select fun p => [optS (p.created.map (addYears · 1))])),
  ("DateTimeDiffDays", u
    (products.select fun p => [optI (p.created.map (diffDays · "2025-01-01 00:00:00"))])),
  ("DateTimeDiffMonths", u
    (products.select fun p => [optI (p.created.map (diffMonths · "2025-01-01 00:00:00"))])),
  ("DateTimeDiffYears", u
    (products.select fun p => [optI (p.created.map (diffYears · "2025-01-01 00:00:00"))])),
  ("DateTimeFunctionsInWhere", u
    (products.where' (fun p => p.created.any (fun s =>
        (parseYMD s).1 == 2024 && (parseYMD s).2.1 > 6))
      |>.select fun p => [ci p.id, optS p.created])),
  -- math functions
  ("DecimalRound", u (products.select fun p => [optD (p.priceM.map (roundTo 2))])),
  ("DecimalCeiling", u (products.select fun p => [optD (p.priceM.map ceilTo0)])),
  ("DecimalFloor", u (products.select fun p => [optD (p.priceM.map floorTo0)])),
  ("MathFunctionsInWhere", u
    (products.where' (fun p =>
        p.priceM.any (fun v => roundTo 0 v > 100000) &&
        p.priceM.any (fun v => ceilTo0 v < 1000000))
      |>.select fun p => [ci p.id, optD p.priceM])),
  ("MathFunctionsInSelect", u
    (products.select fun p =>
      [ci p.id, optD p.priceM, optD (p.priceM.map (roundTo 2)),
       optD (p.priceM.map ceilTo0), optD (p.priceM.map floorTo0)])),
  -- LIMIT/OFFSET (ordered by Id; take/drop mirror LIMIT/OFFSET)
  ("FromLimitOffset", o
    (customers.orderBy' (·.id ≤ ·.id) |>.drop 10 |>.take 5 |>.select custRow)),
  ("FromSelectLimitOffset", o
    (customers.orderBy' (·.id ≤ ·.id) |>.drop 5 |>.take 3
      |>.select fun c => [ci c.id, c.name])),
  ("FromWhereLimitOffset", o
    (customers.where' (·.age > 18) |>.orderBy' (·.id ≤ ·.id) |>.take 10
      |>.select custRow)),
  ("FromWhereSelectLimitOffset", o
    (customers.where' (·.age ≥ 21) |>.orderBy' (·.id ≤ ·.id) |>.drop 15 |>.take 5
      |>.select fun c => [ci c.id, c.name, ci c.age])),
  ("FromOrderByLimitOffset", o
    (customers.orderBy' (·.name ≤ ·.name) |>.drop 5 |>.take 10 |>.select custRow)),
  ("FromWhereOrderByLimitOffset", o
    (customers.where' (·.age > 18) |>.orderBy' (·.age ≥ ·.age) |>.drop 10 |>.take 20
      |>.select custRow)),
  ("FromWhereOrderBySelectLimitOffset", o
    (customers.where' (·.name != "")
      |>.orderBy' (fun a b => a.name < b.name || (a.name == b.name && a.age ≥ b.age))
      |>.take 5 |>.select fun c => [ci c.id, c.name, ci c.age])),
  ("FromLimitOffsetOnly", o
    (customers.orderBy' (·.id ≤ ·.id) |>.take 10 |>.select custRow)),
  ("FromOffsetOnly", o
    (customers.orderBy' (·.id ≤ ·.id) |>.drop 5 |>.select custRow)),
  ("FromLimitOffsetWithoutOrderBy", u (customers.take 10 |>.select custRow)),
  -- DISTINCT
  ("FromSelectDistinct", u ((customers.select fun c => [c.name]).eraseDups)),
  ("FromSelectDistinctWhere", u
    ((customers.where' (·.age > 18) |>.select fun c => [c.name]).eraseDups)),
  ("FromSelectDistinctOrderBy", o
    ((customers.orderBy' (·.name ≤ ·.name) |>.select fun c => [c.name]).eraseDups)),
  ("FromSelectDistinctMultipleColumns", o
    ((customers.orderBy' (·.name ≤ ·.name)
      |>.select fun c => [c.name, ci c.age]).eraseDups)),
  -- set operations (UNION/INTERSECT/EXCEPT deduplicate)
  ("Union", u
    (((customers.where' (·.age > 30) |>.select fun c => [ci c.id, c.name]) ++
      (customers.where' (·.name == "Alice") |>.select fun c => [ci c.id, c.name])).eraseDups)),
  ("Intersect", u
    (let a := customers.where' (·.age > 25) |>.select fun c => [ci c.id, c.name]
     let b := customers.where' (·.name == "John") |>.select fun c => [ci c.id, c.name]
     (a.where' b.contains).eraseDups)),
  ("Except", u
    (let a := customers.select fun c => [ci c.id, c.name]
     let b := customers.where' (·.age < 18) |>.select fun c => [ci c.id, c.name]
     (a.where' (fun r => !b.contains r)).eraseDups)),
  -- statements: expected table state = seed transformed by the mutation
  ("InsertBasic", o
    (customers.select custRow ++ [[ci 200, ci 25, "John Doe", nullC]])),
  ("UpdateBasic", o
    (customers.select fun c =>
      [ci c.id, ci (if c.id == 200 then 26 else c.age), c.name, cb c.active])),
  ("UpdateMultiple", o
    (customers.select fun c =>
      if c.id == 200 then [ci c.id, ci 27, "John Smith", cb c.active] else custRow c)),
  ("UpdateConditional", o
    (customers.select fun c =>
      [ci c.id, ci (if c.age ≥ 18 && c.name != "Admin" then c.age + 1 else c.age),
       c.name, cb c.active])),
  ("DeleteBasic", o (customers.where' (·.id != 200) |>.select custRow)),
  ("DeleteConditional", o
    (customers.where' (fun c => !(c.age < 18 || c.name == "Temp")) |>.select custRow)),
  ("DeleteAll", o []),
  ("UpdateSetNull", o
    (customers.select fun c => [ci c.id, ci c.age, nullC, cb c.active])),
  ("UpdateSetNullInt", o
    (customers.select fun c => [ci c.id, nullC, c.name, cb c.active])),
  ("UpdateSetNullMixed", o
    (customers.select fun c => [ci c.id, nullC, "John", cb c.active])),
  ("UpdateSetNullWhere", o
    (customers.select fun c =>
      if c.id == 200 then [ci c.id, ci c.age, nullC, cb c.active] else custRow c)),
  ("InsertWithNull", o
    (customers.select custRow ++ [[ci 202, ci 25, nullC, nullC]])),
  ("InsertWithNullInt", o
    (customers.select custRow ++ [[ci 203, nullC, "John", nullC]])),
  ("InsertWithNewColumns", o
    (products.select prodRow ++
      [[ci 200, "Test Product", dec 99990, "2024-08-18 00:00:00",
        "12345678-1234-1234-1234-123456789012"]])),
  ("UpdateWithNewColumns", o
    (products.select fun p =>
      if p.id == 100 then
        [ci p.id, p.name, dec 119990, "2024-12-25 00:00:00",
         "87654321-4321-4321-4321-210987654321"]
      else prodRow p)),
  ("InsertWithNewColumnsNull", o
    (products.select prodRow ++ [[ci 201, "Null Test", nullC, nullC, nullC]])),
  ("UpdateSetNewColumnsNull", o
    (products.select fun p =>
      if p.id == 101 then [ci p.id, p.name, nullC, nullC, nullC] else prodRow p))
]

end Oracle
