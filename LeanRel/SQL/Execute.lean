import LeanRel.SQL.Render

namespace LeanRel.SQL

structure ResultSet where
  columns : List String := []
  rows : List (List Value) := []
  affected : Nat := 0
  deriving Repr, Inhabited

structure CheckedStatement where
  statement : Prepared
  expectedAffected : Option Nat := none
  deriving Repr

structure ReadCheck where
  statement : Prepared
  expectedRows : List (List Value)
  deriving Repr

/-- A driver must execute a batch atomically, validating reads under isolation that
prevents concurrent changes until commit. Errors roll back the entire batch. -/
structure Batch where
  statements : List CheckedStatement := []
  reads : List ReadCheck := []
  deriving Repr

/-- A backend supplies its renderer and transaction runner. No particular SQL
database, connection library or transport is required by the public middle end. -/
structure Connection where
  render : Statement → Except String Prepared
  run : Batch → IO (Except String (List ResultSet))

def Connection.execute (connection : Connection) (statements : List Statement) : IO (Except String (List ResultSet)) := do
  match statements.mapM connection.render with
  | .error e => return .error e
  | .ok statements => connection.run {statements := statements.map fun s => ⟨s, none⟩}

private partial def jsonValue : Lean.Json → Except String Value
  | .null => .ok .null
  | .bool b => .ok (.bool b)
  | .str s => .ok (.text s)
  | j@(.num _) => match j.getInt? with
    | .ok n => .ok (.int n)
    | .error _ => Value.real <$> (Lean.fromJson? j : Except String Float)
  | .arr xs => Value.list <$> xs.toList.mapM jsonValue
  | .obj _ => .error "expected positional JSON rows for a nested collection"

private partial def unpack (shape : Shape) (cells : List Value) : Except String (Value × List Value) := do
  match shape with
  | .scalar =>
    match cells with
    | [] => throw "missing SQL result column"
    | x :: xs => return (x, xs)
  | .record fields =>
    let (fields, rest) ← fields.foldlM (fun (acc, rest) (name, shape) => do
      let (value, rest) ← unpack shape rest
      return (acc ++ [(name, value)], rest)) ([], cells)
    return (.record fields, rest)
  | .list element =>
    let (cell, rest) ← match cells with
      | [] => throw "missing nested SQL result column"
      | cell :: rest => pure (cell, rest)
    let cell ← match cell with
      | .text s => Lean.Json.parse s >>= jsonValue
      | cell => pure cell
    let .list rows := cell | throw "expected a JSON array for a nested collection"
    let values ← rows.mapM fun row => do
      let .list cells := row | throw "expected a positional row in a nested collection"
      let (value, remaining) ← unpack element cells
      if !remaining.isEmpty then throw "too many columns in a nested collection row"
      pure value
    return (.list values, rest)

def ResultSet.decode [Codec α] (result : ResultSet) : Except String (List α) :=
  result.rows.mapM fun row => do
    let (value, rest) ← unpack (Codec.shape (α := α)) row
    if !rest.isEmpty then throw "too many SQL result columns"
    Codec.decode value

def Connection.query [Codec α] (connection : Connection) (q : Query) : IO (Except String (List α)) := do
  match ← connection.execute [.query q] with
  | .error e => return .error e
  | .ok [result] => return result.decode
  | .ok _ => return .error "driver returned an invalid number of result sets"

private def normalizeCell (type : ScalarType) (value : Value) : Except String Value := do
  let result ← match type, value with
    | .bool, .int 0 => pure (.bool false)
    | .bool, .int 1 => pure (.bool true)
    | .real, .int n => pure (.real n.toFloat)
    | .nullable _, .null => pure .null
    | .nullable inner, value => normalizeCell inner value
    | _, value => pure value
  if !type.accepts result then throw "database value does not match its declared schema"
  return result

/-- Read all participating sources in one batch. Lens writes will recheck this
snapshot under the driver's write transaction before applying changes. -/
def Connection.snapshot (connection : Connection) (tables : List TableDef) : IO (Except String Database) := do
  let queries := tables.map fun table => Statement.query (.select {
    columns := table.names.map fun name => (.column [name], none)
    from_ := some (.table [table.name])})
  match ← connection.execute queries with
  | .error error => return .error error
  | .ok results => return do
    if results.length != tables.length then throw "driver returned an invalid number of snapshots"
    (tables.zip results).mapM fun (table, result) => do
      table.validate
      let rows ← result.rows.mapM fun cells => do
        if cells.length != table.columns.length then throw "snapshot column count mismatch"
        (table.columns.zip cells).mapM fun (column, value) =>
          return (column.name, ← normalizeCell column.type value)
      table.validateRows rows
      return (table.name, rows)

end LeanRel.SQL
