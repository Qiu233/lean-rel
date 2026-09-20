import LeanRel.Data
import LeanRel.Parser

namespace LeanRel
open Lean Meta Elab Command Term

/-- Persisted elaborator metadata, also available after importing a compiled module. -/
structure SchemaInfo where
  rowType : Name
  definition : TableDef
  projections : Array (Name × String)
  deriving Inhabited, Repr

initialize schemaExtension : SimplePersistentEnvExtension SchemaInfo (Array SchemaInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

def findSchema? (env : Environment) (name : Name) : Option SchemaInfo :=
  (schemaExtension.getState env).find? fun s => s.rowType == name

declare_syntax_cat schemaColumnConstraint
syntax identDispatch(&"NOT") &"NULL" : schemaColumnConstraint
syntax identDispatch(&"PRIMARY") &"KEY" : schemaColumnConstraint
-- Constraints delimit an unparenthesized Lean type without reserving their names.
@[run_parser_attribute_hooks]
private def schemaColumnType : Parser.Parser :=
  Parser.withForbiddens #["NOT", "PRIMARY"] Parser.termParser

declare_syntax_cat schemaEntry
syntax (priority := low) ident schemaColumnType schemaColumnConstraint* : schemaEntry
syntax identDispatch(&"PRIMARY") &"KEY" "(" ident,+ ")" : schemaEntry
syntax (name := schemaDecl) identDispatch(&"schema") ident str " (" schemaEntry,+ ")" : command

private def scalarTypeTerm : ScalarType → TermElabM (TSyntax `term)
  | .int => `(ScalarType.int)
  | .real => `(ScalarType.real)
  | .bool => `(ScalarType.bool)
  | .text => `(ScalarType.text)
  | .blob => `(ScalarType.blob)
  | .nullable t => do `(ScalarType.nullable $(← scalarTypeTerm t))

@[command_elab schemaDecl]
unsafe def elabSchema : CommandElab := fun stx => do
  let `(command| schema $name:ident $dbName:str ($[$entries:schemaEntry],*)) := stx
    | throwUnsupportedSyntax
  let mut fieldNames : Array Ident := #[]
  let mut types : Array (TSyntax `term) := #[]
  let mut required : Array Bool := #[]
  let mut primaryKey : Option (Array Ident) := none
  for entry in entries do
    match entry with
    | `(schemaEntry| PRIMARY KEY ($[$keys:ident],*)) =>
      if primaryKey.isSome then throwErrorAt entry "a schema can declare only one PRIMARY KEY"
      primaryKey := some keys
    | `(schemaEntry| $n:ident $t:term $[$constraints:schemaColumnConstraint]*) =>
      if fieldNames.any (·.getId == n.getId) then throwErrorAt n "duplicate schema field"
      if n.getId.isAnonymous || n.getId.components.length != 1 then
        throwErrorAt n "a field needs a simple identifier"
      if n.getId.toString.toUpper == "TABLE" then
        throwErrorAt n "schema field '{n.getId}' is reserved by the SQL standard (TABLE)"
      let mut notNull := false
      for constraint in constraints do
        match constraint with
        | `(schemaColumnConstraint| NOT NULL) =>
          if notNull then throwErrorAt constraint "duplicate NOT NULL constraint"
          notNull := true
        | `(schemaColumnConstraint| PRIMARY KEY) =>
          if primaryKey.isSome then throwErrorAt constraint "a schema can declare only one PRIMARY KEY"
          primaryKey := some #[n]
        | _ => throwUnsupportedSyntax
      fieldNames := fieldNames.push n
      types := types.push t
      required := required.push notNull
    | _ => throwUnsupportedSyntax
  let names := fieldNames.map fun n => n.getId.toString
  let columnTypes ← liftTermElabM do
    types.mapM fun type => do
      let code ← elabTerm (← `(ColumnType.type (α := $type))) (some (mkConst ``ScalarType))
      synthesizeSyntheticMVarsNoPostponing
      evalExpr ScalarType (mkConst ``ScalarType) (← instantiateMVars code)
  for ((n, type), notNull) in (fieldNames.zip columnTypes).zip required do
    if notNull then
      if let .nullable _ := type then
        throwErrorAt n "NOT NULL conflicts with the nullable Lean type of '{n.getId}'"
  let definition : TableDef := {
    name := dbName.getString
    columns := (names.zip columnTypes).toList.map fun (n, t) => ⟨n, t⟩
    key := (primaryKey.getD #[]).toList.map (·.getId.toString)
  }
  if let .error err := definition.validate then throwErrorAt stx err
  elabCommand (← `(structure $name where
    $[$fieldNames:ident : $types:term]*
    deriving Repr, BEq))
  let columnsName := mkIdent (name.getId ++ `Columns)
  let family := mkIdent `F
  let liftedTypes ← types.mapM fun type => `($family $type)
  elabCommand (← `(structure $columnsName ($family : Type → Type) where
    $[$fieldNames:ident : $liftedTypes:term]*))
  let make := mkIdent `make
  let generated ← (names.zip types).mapM fun (n, type) => `($make $type $(quote n))
  let fieldsRow := mkIdent `fieldsRow
  let visit := mkIdent `visit
  let visited ← (fieldNames.zip types).mapM fun (n, type) => do
    let projection := mkIdent (fieldsRow.getId ++ n.getId)
    `($visit $type $(quote n.getId.toString) $projection)
  elabCommand (← `(@[reducible] instance : SchemaRow $name where
    Fields := $columnsName
    tabulate $make:ident := { $[$fieldNames:ident := $generated:term],* }
    fold $fieldsRow:ident $visit:ident := [$visited,*]))
  elabCommand (← `(instance ($family : Type → Type) : RowFields ($columnsName $family) $family $name where
    fold $fieldsRow:ident $visit:ident := [$visited,*]))
  let row := mkIdent `row
  let raw := mkIdent `fields
  let encoders ← fieldNames.mapM fun f => do
    let proj : TSyntax `term := ⟨(mkIdent (row.getId ++ f.getId)).raw⟩
    `(($(quote f.getId.toString), Codec.encode $proj))
  let decoders ← fieldNames.mapM fun f =>
    `(← Codec.decode (← Record.getField $raw $(quote f.getId.toString)))
  let shapes ← (names.zip types).mapM fun (n, t) => `(($(quote n), Codec.shape (α := $t)))
  elabCommand (← `(instance : Codec $name where
    encode $row:ident := Value.record [$encoders,*]
    decode value := match value with
      | Value.record $raw => do
        return { $[$fieldNames:ident := $decoders:term],* : $name }
      | _ => Except.error "expected schema record"
    shape := Shape.record [$shapes,*]))
  let cols ← liftTermElabM do
    definition.columns.toArray.mapM fun c => do `(Column.mk $(quote c.name) $(← scalarTypeTerm c.type))
  elabCommand (← `(instance : HasTable $name where
    table := ⟨{
      name := $dbName, columns := [$cols,*], key := $(quote definition.key)}⟩))
  let fullName := (← getCurrNamespace) ++ name.getId
  let info : SchemaInfo := {
    rowType := fullName
    definition
    projections := fieldNames.map fun f => (fullName ++ f.getId, f.getId.toString)
  }
  modifyEnv fun env => schemaExtension.addEntry env info

end LeanRel
