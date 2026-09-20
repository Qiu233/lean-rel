import LeanRel.Data

/-! Public, backend-independent SQL syntax tree. It does not import the frontend. -/
namespace LeanRel.SQL

abbrev Ident := List String

inductive BinOp where
  | eq | ne | lt | le | gt | ge | add | sub | mul | div | mod | and | or | concat | like
  | nullSafeEq
  deriving Repr, BEq, Inhabited
inductive UnOp where
  | not | negate | isNull | isNotNull
  deriving Repr, BEq, Inhabited
inductive JoinKind where
  | inner | left | right | full | cross
  deriving Repr, BEq, Inhabited
inductive SetOp where
  | union | intersect | except
  deriving Repr, BEq, Inhabited
inductive SqlType where
  | integer | boolean | text | real | date | timestamp | blob
  | varchar (length : Nat)
  | decimal (precision scale : Nat)
  deriving Repr, BEq, Inhabited

mutual
  inductive Expr where
    | column (name : Ident)
    | param (value : Value)
    | null
    | boolean (value : Bool)
    | star (qualifier : Option String := none)
    | binary (op : BinOp) (left right : Expr)
    | unary (op : UnOp) (arg : Expr)
    | call (name : String) (args : List Expr) (distinct : Bool := false)
    | caseWhen (branches : List (Expr × Expr)) (otherwise : Expr)
    | cast (arg : Expr) (type : SqlType)
    | scalar (query : Query)
    | exists (query : Query)
    | inQuery (arg : Expr) (query : Query)
    | inList (arg : Expr) (values : List Expr)
    | over (function : Expr) (partition : List Expr) (order : List (Expr × Bool))
    /-- A nested collection of positional rows. Column flags mark nested collections;
    ordering names refer to projected columns of the child query. -/
    | collection (query : Query) (columns : List (String × Bool)) (order : List (String × Bool))
    | collectionLength (collection : Expr)
    deriving Repr
  inductive Source where
    | table (name : Ident) (alias : Option String := none)
    | subquery (query : Query) (alias : String) (lateral : Bool := false)
    | join (kind : JoinKind) (left right : Source) (on : Option Expr)
    deriving Repr
  inductive Query where
    | select (body : Select)
    | set (op : SetOp) (all : Bool) (left right : Query)
    | with_ (recursive : Bool) (bindings : List (String × Query)) (body : Query)
    deriving Repr
  structure Select where
    columns : List (Expr × Option String)
    distinct : Bool := false
    from_ : Option Source := none
    where_ : Option Expr := none
    groupBy : List Expr := []
    having : Option Expr := none
    orderBy : List (Expr × Bool) := []
    limit : Option Nat := none
    offset : Option Nat := none
    deriving Repr
end

structure ColumnDef where
  name : String
  type : SqlType
  nullable : Bool := false
  defaultValue : Option Expr := none
  deriving Repr

inductive Constraint where
  | primaryKey (columns : List String)
  | unique (columns : List String)
  | foreignKey (columns : List String) (table : Ident) (target : List String)
  | check (predicate : Expr)
  deriving Repr

structure CreateTable where
  name : Ident
  columns : List ColumnDef
  constraints : List Constraint := []
  ifNotExists : Bool := false
  deriving Repr

inductive InsertSource where
  | values (rows : List (List Expr))
  | query (query : Query)
  deriving Repr

inductive Statement where
  | query (query : Query)
  | insert (table : Ident) (columns : List String) (source : InsertSource)
      (returning : List (Expr × Option String) := [])
  | update (table : Ident) (assignments : List (String × Expr)) (where_ : Option Expr)
      (returning : List (Expr × Option String) := [])
      (alias : Option String := none)
  | delete (table : Ident) (where_ : Option Expr) (returning : List (Expr × Option String) := [])
      (alias : Option String := none)
  | createTable (table : CreateTable)
  | createIndex (name : String) (table : Ident) (columns : List String) (unique : Bool := false)
  | createView (name : Ident) (query : Query)
  | dropTable (name : Ident) (ifExists : Bool := false)
  | begin | commit | rollback
  deriving Repr

def scalarType : ScalarType → SqlType × Bool
  | .int => (.integer, false)
  | .real => (.real, false)
  | .bool => (.boolean, false)
  | .text => (.text, false)
  | .blob => (.blob, false)
  | .nullable t => ((scalarType t).1, true)

def CreateTable.ofTable (table : TableDef) : Except String CreateTable := do
  table.validate
  return {
    name := [table.name]
    columns := table.columns.map fun c =>
      {name := c.name, type := (scalarType c.type).1, nullable := (scalarType c.type).2}
    constraints := if table.key.isEmpty then [] else [.primaryKey table.key]
  }

end LeanRel.SQL
