import LeanLinq.Statements

/-! # Statement evaluation

INSERT/UPDATE/DELETE as `TableEnv ts → TableEnv ts` transforms, completing
the executable semantics: the statement value that compiles to SQL also
applies in memory. The target table is read and written through its
`HasTable` instance — resolution happened at elaboration, so applying a
statement to a database lacking its table is a type error, not a silent
no-op. WHERE follows the same three-valued discipline as queries (a row is
affected only when the predicate is `some true`); rows are addressed via the
empty-alias marker row, exactly as the statement compiler renders them. -/

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
private def buildInsertRow (ee : EvalEnv ts)
    (vs : List (String × ((u : SqlType) × SqlExpr ts u))) :
    (s : Schema) → Values s
  | [] => .nil
  | (n, t) :: rest =>
      let cell : Option t.interp :=
        match vs.find? (·.1 == n) with
        | some (_, ⟨u, e⟩) => if h : u = t then h ▸ (e.evalG ee [([] : Scope)]) else none
        | none => none
      .cons cell (buildInsertRow ee vs rest)

def InsertStmt.apply (i : InsertStmt ts n s) [inst : HasTable ts n s]
    (env : TableEnv ts) (params : List (String × SqlValue) := [])
    (now : Option String := none) : TableEnv ts :=
  let ee : EvalEnv ts := ⟨env, params, now⟩
  inst.set env (inst.rows env ++ [buildInsertRow ee i.values s])

def UpdateStmt.apply (u : UpdateStmt ts n s) [inst : HasTable ts n s]
    (env : TableEnv ts) (params : List (String × SqlValue) := [])
    (now : Option String := none) : TableEnv ts :=
  let ee : EvalEnv ts := ⟨env, params, now⟩
  let marker := Row.ofAlias "" s
  inst.set env <| (inst.rows env).map fun v =>
    let sc : Scope := [("", ⟨s, v⟩)]
    let hit := match u.where? with
      | none => true
      | some p => (p marker).evalG ee [sc] == some true
    if hit then
      -- every SET expression sees the pre-update row (SQL semantics)
      u.sets.foldl (init := v) fun acc (nm, f) =>
        match f marker with
        | ⟨t', e⟩ => acc.setCol nm t' (e.evalG ee [sc])
    else v

def DeleteStmt.apply (d : DeleteStmt ts n s) [inst : HasTable ts n s]
    (env : TableEnv ts) (params : List (String × SqlValue) := [])
    (now : Option String := none) : TableEnv ts :=
  let ee : EvalEnv ts := ⟨env, params, now⟩
  let marker := Row.ofAlias "" s
  inst.set env <| (inst.rows env).filter fun v =>
    match d.where? with
    | none => false                     -- unconditional DELETE clears the table
    | some p =>
        let sc : Scope := [("", ⟨s, v⟩)]
        (p marker).evalG ee [sc] != some true

end LeanLinq
