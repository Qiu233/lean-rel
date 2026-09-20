import LeanRel.Frontend.Lens
import LeanRel.SQL.Execute

namespace LeanRel.Compiler

private def rowPredicate (row : Record) : SQL.Expr :=
  row.foldl (fun p (name, value) => .binary .and p
    (if value == .null then .unary .isNull (.column [name])
     else .binary .eq (.column [name]) (.param value))) (.boolean true)

/-- Snapshot changes become keyed DML with old-row preconditions. Keys are never
guessed from positional row order. Deletes run before inserts for changed keys. -/
def compileChanges (result : Frontend.UpdateResult)
    (render : SQL.Statement → Except String SQL.Prepared) : Except String SQL.Batch := do
  let reads ← result.reads.mapM fun snapshot => do
    let names := snapshot.table.names
    let q : SQL.Query := .select {
      columns := names.map fun n => (.column [n], none)
      from_ := some (.table [snapshot.table.name])
    }
    let rows ← snapshot.rows.mapM fun row => names.mapM (Record.getField row)
    return {statement := ← render (.query q), expectedRows := rows : SQL.ReadCheck}
  let mut statements := []
  for change in result.changes do
    change.table.validateRows change.before
    change.table.validateRows change.after
    if change.table.key.isEmpty then throw "SQL change propagation requires a key"
    for old in change.before do
      if !(change.after.any fun row => agree old row change.table.key) then
        let statement ← render (.delete [change.table.name] (some (rowPredicate old)))
        statements := statements ++ [⟨statement, some 1⟩]
  for change in result.changes do
    for row in change.after do
      if let some old := change.before.find? (fun old => agree old row change.table.key) then
        if !sameRecord old row then
          let changed := row.filter fun (n, v) => old.lookup n != some v
          let statement ← render (.update [change.table.name]
            (changed.map fun (n, v) => (n, .param v)) (some (rowPredicate old)))
          statements := statements ++ [⟨statement, some 1⟩]
      else
        let values ← change.table.names.mapM fun n => return SQL.Expr.param (← Record.getField row n)
        let statement ← render (.insert [change.table.name] change.table.names (.values [values]))
        statements := statements ++ [⟨statement, some 1⟩]
  return {statements, reads}

def applyUpdate (connection : SQL.Connection) (request : Frontend.Update) (snapshot : Database) :
    IO (Except String (List SQL.ResultSet)) := do
  match request.run snapshot >>= (compileChanges · connection.render) with
  | .error e => return .error e
  | .ok batch => connection.run batch

/-- Fetch a consistent snapshot, compute the native update, and commit only if
all read sources still match. A conflict is returned to the caller, never retried silently. -/
def executeUpdate (connection : SQL.Connection) (request : Frontend.Update) :
    IO (Except String (List SQL.ResultSet)) := do
  match ← connection.snapshot request.sources with
  | .error error => return .error error
  | .ok snapshot => applyUpdate connection request snapshot

end LeanRel.Compiler
