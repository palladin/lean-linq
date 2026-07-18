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
value — unreachable for `HasCol`-checked statements). A write boundary:
NULL into a NOT NULL column is a loud error (unreachable through the
flag-checked builders). -/
private def Values.setCol (name : String) (t' : SqlPrim) (cell : Nullable t') :
    {s : Schema} → Values s → Except EvalError (Values s)
  | _, .nil => pure .nil
  | _, .cons (name := nc) (c := cc) old r =>
      if nc == name then
        (if h : t' = cc.ty then do
          pure (.cons (← SqlType.ofNullable name cc (h ▸ cell)) r)
        else pure (.cons old r))
      else do pure (.cons old (← r.setCol name t' cell))

/-- Build the inserted row in schema order: an unmentioned NULL-capable
column is NULL; an unmentioned NOT NULL column is a loud error — never a
silent NULL. -/
private def buildInsertRow (ee : EvalEnv ts)
    (vs : List (String × ((p : SqlType) × SqlExpr ts p))) :
    (s : Schema) → Except EvalError (Values s)
  | [] => pure .nil
  | (nm, c) :: rest => do
      let cell ←
        match vs.find? (·.1 == nm) with
        | some (_, ⟨⟨u, _⟩, e⟩) =>
            if h : u = c.ty then
              do SqlType.ofNullable nm c (h ▸ (← e.evalG ee [([] : Scope)]))
            else SqlType.ofNullable nm c none
        | none => SqlType.ofNullable nm c none
      pure (.cons cell (← buildInsertRow ee vs rest))

/-- Apply with the affected-row count — what SQL statements report.
INSERT of a `VALUES` row affects exactly 1. -/
def InsertStmt.applyCount (i : InsertStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) :
    Except EvalError (TableEnv ts.tables × Nat) := do
  if i.values.isEmpty then
    throw (.invalidStatement "INSERT with no columns")
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  pure (inst.set env (inst.rows env ++ [← buildInsertRow ee i.values s]), 1)

def InsertStmt.apply (i : InsertStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) :=
  (i.applyCount env ps now).map (·.1)

/-- Apply with the affected-row count: UPDATE reports its WHERE hits. -/
def UpdateStmt.applyCount (u : UpdateStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) :
    Except EvalError (TableEnv ts.tables × Nat) := do
  if u.sets.isEmpty then
    throw (.invalidStatement "UPDATE with no assignments")
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  let marker := Row.ofAlias "" s
  let rcs ← (inst.rows env).mapM fun v => do
    let sc : Scope := [("", ⟨s, v⟩)]
    let hit ← match u.where? with
      | none => pure true
      | some p => do pure ((← (p marker).evalG ee [sc]) == some true)
    if hit then
      -- every SET expression sees the pre-update row (SQL semantics)
      let v' ← u.sets.foldlM (init := v) fun acc (nm, f) =>
        match f marker with
        | ⟨⟨t', _⟩, e⟩ => do acc.setCol nm t' (← e.evalG ee [sc])
      pure (v', true)
    else pure (v, false)
  pure (inst.set env (rcs.map (·.1)), rcs.countP (·.2))

def UpdateStmt.apply (u : UpdateStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) :=
  (u.applyCount env ps now).map (·.1)

/-- Apply with the affected-row count: DELETE reports the rows removed. -/
def DeleteStmt.applyCount (d : DeleteStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) :
    Except EvalError (TableEnv ts.tables × Nat) := do
  let ee : EvalEnv ts := ⟨env, ps, now⟩
  let marker := Row.ofAlias "" s
  let rows ← (inst.rows env).filterM fun v => do
    match d.where? with
    | none => pure false                -- unconditional DELETE clears the table
    | some p =>
        let sc : Scope := [("", ⟨s, v⟩)]
        pure ((← (p marker).evalG ee [sc]) != some true)
  pure (inst.set env rows, (inst.rows env).length - rows.length)

def DeleteStmt.apply (d : DeleteStmt ts n s) [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) :=
  (d.applyCount env ps now).map (·.1)

/-- Apply with the affected-row count: the source's rows, appended —
affected = however many the query yields. -/
def InsertSelectStmt.applyCount (st : InsertSelectStmt ts n s)
    [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) :
    Except EvalError (TableEnv ts.tables × Nat) := do
  let rows ← st.source.evalRows ⟨env, ps, now⟩
  pure (inst.set env (inst.rows env ++ rows), rows.length)

def InsertSelectStmt.apply (st : InsertSelectStmt ts n s)
    [inst : HasTable ts.tables n s]
    (env : TableEnv ts.tables) (ps : ParamEnv ts.params := by exact .nil)
    (now : Option String := none) : Except EvalError (TableEnv ts.tables) :=
  (st.applyCount env ps now).map (·.1)

end LeanLinq
