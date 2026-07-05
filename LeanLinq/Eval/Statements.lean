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
private def Values.setCol (name : String) (t' : SqlType) (cell : Nullable t') :
    {s : Schema} → Values s → Values s
  | _, .nil => .nil
  | _, .cons (name := n) (t := tc) c r =>
      if n == name then
        (if h : t' = tc then .cons (h ▸ cell) r else .cons c r)
      else .cons c (r.setCol name t' cell)

/-- Build the inserted row in schema order: unmentioned columns are NULL. -/
private def buildInsertRow (ee : EvalEnv ts)
    (vs : List (String × ((u : SqlType) × SqlExpr ts u))) :
    (s : Schema) → Except EvalError (Values s)
  | [] => pure .nil
  | (n, t) :: rest => do
      let cell : Nullable t ←
        match vs.find? (·.1 == n) with
        | some (_, ⟨u, e⟩) =>
            if h : u = t then do pure (h ▸ (← e.evalG ee [([] : Scope)]))
            else pure none
        | none => pure none
      pure (.cons cell (← buildInsertRow ee vs rest))

def InsertStmt.apply (i : InsertStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) := do
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  pure (inst.set env (inst.rows env ++ [← buildInsertRow ee i.values s]))

def UpdateStmt.apply (u : UpdateStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) := do
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  let marker := Row.ofAlias "" s
  let rows ← (inst.rows env).mapM fun v => do
    let sc : Scope := [("", ⟨s, v⟩)]
    let hit ← match u.where? with
      | none => pure true
      | some p => do pure ((← (p marker).evalG ee [sc]) == some true)
    if hit then
      -- every SET expression sees the pre-update row (SQL semantics)
      u.sets.foldlM (init := v) fun acc (nm, f) =>
        match f marker with
        | ⟨t', e⟩ => do pure (acc.setCol nm t' (← e.evalG ee [sc]))
    else pure v
  pure (inst.set env rows)

def DeleteStmt.apply (d : DeleteStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) := do
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  let marker := Row.ofAlias "" s
  let rows ← (inst.rows env).filterM fun v => do
    match d.where? with
    | none => pure false                -- unconditional DELETE clears the table
    | some p =>
        let sc : Scope := [("", ⟨s, v⟩)]
        pure ((← (p marker).evalG ee [sc]) != some true)
  pure (inst.set env rows)

end LeanLinq
