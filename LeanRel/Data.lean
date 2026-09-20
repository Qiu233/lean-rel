import Lean

/-! Data shared by interpreters. This module has no dependency on SQL. -/
namespace LeanRel

inductive Value where
  | null
  | int (value : Int)
  | real (value : Float)
  | bool (value : Bool)
  | text (value : String)
  | blob (value : Array UInt8)
  | record (fields : List (String × Value))
  | list (values : List Value)
  deriving Repr, BEq, Inhabited

abbrev Record := List (String × Value)
abbrev Relation := List Record
abbrev Database := List (String × Relation)

def Record.getField (r : Record) (name : String) : Except String Value :=
  match r.lookup name with
  | some v => .ok v
  | none => .error s!"unknown field: {name}"

def Record.project (r : Record) (names : List String) : Except String Record :=
  names.mapM fun name => return (name, ← Record.getField r name)

def Record.set (r : Record) (name : String) (value : Value) : Record :=
  r.map fun (n, v) => (n, if n == name then value else v)

def Database.getTable (db : Database) (name : String) : Except String Relation :=
  match db.lookup name with
  | some rows => .ok rows
  | none => .error s!"unknown source: {name}"

def Database.set (db : Database) (name : String) (rows : Relation) : Database :=
  (name, rows) :: db.filter (fun entry => entry.1 != name)

inductive ScalarType where
  | int | real | bool | text | blob
  | nullable (inner : ScalarType)
  deriving Repr, BEq, DecidableEq, Inhabited

def ScalarType.denote : ScalarType → Type
  | .int => Int
  | .real => Float
  | .bool => Bool
  | .text => String
  | .blob => Array UInt8
  | .nullable t => Option t.denote

def ScalarType.accepts : ScalarType → Value → Bool
  | .int, .int _ | .real, .real _ | .bool, .bool _ | .text, .text _ => true
  | .blob, .blob _ => true
  | .nullable _, .null => true
  | .nullable t, v => t.accepts v
  | _, _ => false

structure Column where
  name : String
  type : ScalarType
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Schema := List Column

structure FunctionalDependency where
  determinant : List String
  dependent : List String
  deriving Repr, BEq, Inhabited

structure TableDef where
  name : String
  columns : Schema
  key : List String := []
  dependencies : List FunctionalDependency := []
  deriving Repr, BEq, Inhabited

def TableDef.names (t : TableDef) := t.columns.map Column.name

def TableDef.fds (t : TableDef) : List FunctionalDependency :=
  (if t.key.isEmpty then [] else [⟨t.key, t.names⟩]) ++ t.dependencies

def agree (a b : Record) (names : List String) : Bool :=
  names.all fun n => a.lookup n == b.lookup n

def sameRecord (a b : Record) : Bool :=
  a.length == b.length && agree a b (a.map Prod.fst)

def uniqueRecords (rows : Relation) : Relation :=
  rows.foldl (fun acc r => if acc.any (sameRecord r) then acc else acc ++ [r]) []

def sameRelation (a b : Relation) : Bool :=
  a.all (fun r => b.any (sameRecord r)) && b.all (fun r => a.any (sameRecord r))

def TableDef.validate (t : TableDef) : Except String Unit := do
  if t.name.isEmpty then throw "a source needs a name"
  let names := t.names
  if names.isEmpty then throw "a schema needs at least one column"
  if names.any String.isEmpty || names.eraseDups.length != names.length then
    throw "empty or duplicate column name"
  if t.key.eraseDups.length != t.key.length then throw "duplicate key column"
  for n in t.key do
    if !names.contains n then throw s!"unknown key column: {n}"
    if let some c := t.columns.find? (·.name == n) then
      if let .nullable _ := c.type then throw s!"nullable key column: {n}"
  for fd in t.dependencies do
    for n in fd.determinant ++ fd.dependent do
      if !names.contains n then throw s!"unknown dependency column: {n}"

def TableDef.validateRows (t : TableDef) (rows : Relation) : Except String Unit := do
  t.validate
  for row in rows do
    if row.length != t.columns.length || (row.map Prod.fst).eraseDups.length != row.length then
      throw s!"invalid record shape for {t.name}"
    for col in t.columns do
      let v ← Record.getField row col.name
      if !col.type.accepts v then throw s!"type mismatch at {t.name}.{col.name}"
  if !t.key.isEmpty then
    for (row, i) in rows.zipIdx do
      if (rows.drop (i + 1)).any (fun other => agree row other t.key) then
        throw s!"duplicate key in {t.name}"
  for fd in t.fds do
    for a in rows do
      for b in rows do
        if agree a b fd.determinant && !agree a b fd.dependent then
          throw s!"functional dependency violated in {t.name}"

inductive Shape where
  | scalar
  | record (fields : List (String × Shape))
  | list (element : Shape)
  deriving Repr, BEq, Inhabited

class Codec (α : Type) where
  encode : α → Value
  decode : Value → Except String α
  shape : Shape

instance : Codec Int where
  encode := .int
  decode | .int n => .ok n | _ => .error "expected integer"
  shape := .scalar
instance : Codec Nat where
  encode n := .int (Int.ofNat n)
  decode
    | .int (.ofNat n) => .ok n
    | _ => .error "expected a nonnegative integer"
  shape := .scalar
instance : Codec Bool where
  encode := .bool
  decode | .bool b => .ok b | .int 0 => .ok false | .int 1 => .ok true | _ => .error "expected boolean"
  shape := .scalar
instance : Codec Float where
  encode := .real
  decode | .real n => .ok n | .int n => .ok n.toFloat | _ => .error "expected real number"
  shape := .scalar
instance : Codec String where
  encode := .text
  decode | .text s => .ok s | _ => .error "expected text"
  shape := .scalar
instance : Codec (Array UInt8) where
  encode := .blob
  decode | .blob bytes => .ok bytes | _ => .error "expected binary data"
  shape := .scalar
instance [Codec α] : Codec (Option α) where
  encode | none => .null | some a => Codec.encode a
  decode | .null => .ok none | v => some <$> Codec.decode v
  shape := Codec.shape (α := α)
instance [Codec α] : Codec (List α) where
  encode xs := .list (xs.map Codec.encode)
  decode | .list xs => xs.mapM Codec.decode | _ => .error "expected collection"
  shape := .list (Codec.shape (α := α))
instance [Codec α] [Codec β] : Codec (α × β) where
  encode p := .record [("fst", Codec.encode p.1), ("snd", Codec.encode p.2)]
  decode
    | .record r => do return (← Codec.decode (← Record.getField r "fst"), ← Codec.decode (← Record.getField r "snd"))
    | _ => .error "expected pair"
  shape := .record [("fst", Codec.shape (α := α)), ("snd", Codec.shape (α := β))]

/-- Extensible mapping for schema field types. Users may supply new codecs/mappings. -/
class ColumnType (α : Type) where
  type : ScalarType

/-- A schema's generated field container can hold values, SQL expressions, or
another interpreter's representation without making schema declarations SQL-specific. -/
class SchemaRow (α : Type) where
  Fields : (Type → Type) → Type
  tabulate {F : Type → Type} : (∀ β, String → F β) → Fields F
  fold {F : Type → Type} {γ : Type} : Fields F → (∀ β, String → F β → γ) → List γ

class RowFields (ρ : Type) (F : Type → Type) (α : outParam Type) where
  fold {γ : Type} : ρ → (∀ β, String → F β → γ) → List γ

instance : ColumnType Int := ⟨.int⟩
instance : ColumnType Float := ⟨.real⟩
instance : ColumnType Bool := ⟨.bool⟩
instance : ColumnType String := ⟨.text⟩
instance : ColumnType (Array UInt8) := ⟨.blob⟩
instance [ColumnType α] : ColumnType (Option α) := ⟨.nullable (ColumnType.type (α := α))⟩

/-- A typed data source, independent of a query language or a database backend. -/
structure Source (α : Type) where
  definition : TableDef
  deriving Repr

/-- Add functional dependencies for relational lens validation and propagation.
Native source reads and lens updates validate them; SQL DDL does not encode them. -/
def Source.withDependencies (source : Source α) (dependencies : List FunctionalDependency) : Source α :=
  {source with definition := {source.definition with
    dependencies := source.definition.dependencies ++ dependencies}}

/-- The default table for a row type. Schema declarations generate this instance
without adding `table` or `schema` declarations to the row type's namespace. -/
class HasTable (α : Type) where
  table : Source α

export HasTable (table)

/-- Runtime schema metadata from the same instance that supplies `table`. -/
def HasTable.schema (α : Type) [HasTable α] : TableDef :=
  (@table α _).definition

end LeanRel
