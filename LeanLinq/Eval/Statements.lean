import LeanLinq.Statements

/-! # Statement evaluation

INSERT/UPDATE/DELETE as `Db → Db` table transforms, completing the
executable semantics: the statement value that compiles to SQL also applies
in memory. WHERE follows the same three-valued discipline as queries (a row
is affected only when the predicate is `some true`); rows are addressed via
the empty-alias marker row, exactly as the statement compiler renders them. -/

namespace LeanLinq

/-- Write a cell by column name (first match; type mismatch keeps the old
value — unreachable for `HasCol`-checked statements). -/
private def Values.setCol (name : String) (t' : SqlType) (cell : Option t'.interp) :
    {s : Schema} → Values s → Values s
  | _, .nil => .nil
  | _, .cons (name := n) (t := tc) c r =>
      if n == name then
        (if h : t' = tc then .cons (h ▸ cell) r else .cons c r)
      else .cons c (r.setCol name t' cell)

/-- Build the inserted row in schema order: unmentioned columns are NULL. -/
private def buildInsertRow (db : Db) (vs : List (String × ((u : SqlType) × SqlExpr u))) :
    (s : Schema) → Values s
  | [] => .nil
  | (n, t) :: rest =>
      let cell : Option t.interp :=
        match vs.find? (·.1 == n) with
        | some (_, ⟨u, e⟩) => if h : u = t then h ▸ (e.evalG db [([] : Env)]) else none
        | none => none
      .cons cell (buildInsertRow db vs rest)

def InsertStmt.apply (i : InsertStmt s) (db : Db) : Db :=
  db.setTable i.table.name s (db.rowsOf i.table.name s ++ [buildInsertRow db i.values s])

def UpdateStmt.apply (u : UpdateStmt s) (db : Db) : Db :=
  let marker := Row.ofAlias "" s
  let rows := (db.rowsOf u.table.name s).map fun v =>
    let env : Env := [("", ⟨s, v⟩)]
    let hit := match u.where? with
      | none => true
      | some p => (p marker).evalG db [env] == some true
    if hit then
      -- every SET expression sees the pre-update row (SQL semantics)
      u.sets.foldl (init := v) fun acc (n, f) =>
        match f marker with
        | ⟨t', e⟩ => acc.setCol n t' (e.evalG db [env])
    else v
  db.setTable u.table.name s rows

def DeleteStmt.apply (d : DeleteStmt s) (db : Db) : Db :=
  let marker := Row.ofAlias "" s
  let rows := (db.rowsOf d.table.name s).filter fun v =>
    match d.where? with
    | none => false                     -- unconditional DELETE clears the table
    | some p =>
        let env : Env := [("", ⟨s, v⟩)]
        (p marker).evalG db [env] != some true
  db.setTable d.table.name s rows

end LeanLinq
