import LeanRel.SQL.Execute
import SQLite.LowLevel
import Std.Sync.Mutex

/-! Native SQLite execution through leanprover/leansqlite. A connection owns a
live SQLite handle. Batches on that handle are serialized and run atomically. -/
namespace LeanRel.Backend.SQLite

private def bind (stmt : _root_.SQLite.Stmt) (index : Int32) : Value → IO Unit
  | .null => stmt.bindNull index
  | .int n => do
    if n < Int64.minValue.toInt || n > Int64.maxValue.toInt then
      throw (IO.userError "SQLite integer parameter is outside the signed 64-bit range")
    stmt.bindInt64 index n.toInt64
  | .real n => do
    if n.isNaN || n.isInf then throw (IO.userError "SQLite real parameters must be finite")
    stmt.bindFloat index n
  | .bool b => stmt.bindInt32 index (if b then 1 else 0)
  | .text s => stmt.bindText index s
  | .blob bytes => stmt.bindBlob index ⟨bytes⟩
  | _ => throw (IO.userError "SQLite parameters must be scalar")

private def column (stmt : _root_.SQLite.Stmt) (index : Int32) : IO Value := do
  match ← stmt.columnType index with
  | .null => return .null
  | .integer => return .int (← stmt.columnInt64 index).toInt
  | .float => return .real (← stmt.columnDouble index)
  | .text => return .text (← stmt.columnText index)
  | .blob => return .blob (← stmt.columnBlob index).data

private def execute (db : _root_.SQLite) (prepared : SQL.Prepared)
    (readOnly := false) : IO SQL.ResultSet := do
  let stmt ← db.prepare prepared.sql
  if readOnly && !(← stmt.isReadonly) then
    throw (IO.userError "a snapshot check must be read-only")
  if (← stmt.bindParameterCount).toNat != prepared.parameters.size then
    throw (IO.userError "SQLite parameter count mismatch")
  for (value, i) in prepared.parameters.zipIdx do
    bind stmt (Int32.ofInt (Int.ofNat (i + 1))) value
  let indices := List.range stmt.columnCount.toNat
  let columns ← indices.mapM fun i => stmt.columnName (Int32.ofInt (Int.ofNat i))
  let before ← db.totalChanges
  let mut rows := #[]
  while ← stmt.step do
    rows := rows.push (← indices.mapM fun i => column stmt (Int32.ofInt (Int.ofNat i)))
  let after ← db.totalChanges
  let changes ← db.changes
  let affected := if before == after then 0 else changes.toInt.toNat
  return {columns, rows := rows.toList, affected}

-- SQLite represents booleans as integers. Compare bags, retaining multiplicity.
private def canonical : Value → Value
  | .bool b => .int (if b then 1 else 0)
  | v => v

private def sameRows (actual expected : List (List Value)) : Bool := Id.run do
  let mut remaining := expected.map (List.map canonical)
  for row in actual.map (List.map canonical) do
    if !remaining.contains row then return false
    remaining := remaining.erase row
  return remaining.isEmpty

private def runBatch (db : _root_.SQLite) (batch : SQL.Batch) : IO (List SQL.ResultSet) :=
  db.transaction (mode := .immediate) do
    for read in batch.reads do
      let actual ← execute db read.statement (readOnly := true)
      if !sameRows actual.rows read.expectedRows then
        throw (IO.userError "stale snapshot: source changed before lens update")
    batch.statements.mapM fun step => do
      let result ← execute db step.statement
      if let some expected := step.expectedAffected then
        if result.affected != expected then
          throw (IO.userError "write conflict: unexpected affected row count")
      return result

/-- Open a persistent native handle, including for `:memory:`. leansqlite manages
handle/statement lifetimes; the mutex serializes whole transactions. -/
def connect (path : System.FilePath) (busyTimeoutMs : Int32 := 10000) : IO SQL.Connection := do
  let db ← _root_.SQLite.openWith path {threading := some .fullmutex} (busyTimeoutMs := busyTimeoutMs)
  db.exec "PRAGMA foreign_keys = ON"
  let mutex ← Std.Mutex.new db
  return {
    render := fun statement => match statement with
      | .begin | .commit | .rollback => .error "Connection.execute already manages a transaction; pass its statements as one batch"
      | statement => SQL.render .sqlite statement
    run := fun batch => mutex.atomically do
      try
        return .ok (← runBatch (← get) batch)
      catch error => return .error error.toString
  }

end LeanRel.Backend.SQLite
