import LeanRel.Data

namespace LeanRel
open Lean Meta Elab Command Term

/-- Persisted elaborator metadata, also available after importing a compiled module. -/
structure SchemaInfo where
  rowType : Name
  source : Name
  definition : TableDef
  projections : Array (Name × String)
  deriving Inhabited, Repr

initialize schemaExtension : SimplePersistentEnvExtension SchemaInfo (Array SchemaInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

def findSchema? (env : Environment) (name : Name) : Option SchemaInfo :=
  (schemaExtension.getState env).find? fun s => s.rowType == name || s.source == name

syntax schemaField := ident " : " term
syntax schemaDependency := "[" ident,* "]" " -> " "[" ident,* "]"
syntax (name := schemaDecl) "schema " ident str " {" schemaField,+ "}"
  &"key" "[" ident,* "]" (&"dependencies" "{" sepBy1(schemaDependency, ";") "}")? : command

private def scalarTypeTerm : ScalarType → TermElabM (TSyntax `term)
  | .int => `(ScalarType.int)
  | .real => `(ScalarType.real)
  | .bool => `(ScalarType.bool)
  | .text => `(ScalarType.text)
  | .blob => `(ScalarType.blob)
  | .nullable t => do `(ScalarType.nullable $(← scalarTypeTerm t))

@[command_elab schemaDecl]
unsafe def elabSchema : CommandElab := fun stx => do
  let `(schema $name:ident $dbName:str { $[$fields:schemaField],* } key [$[$keys:ident],*]
    $[dependencies { $[$fds:schemaDependency];* }]?) := stx | throwUnsupportedSyntax
  let mut fieldNames : Array Ident := #[]
  let mut types : Array (TSyntax `term) := #[]
  for f in fields do
    let `(schemaField| $n:ident : $t:term) := f | throwUnsupportedSyntax
    if fieldNames.any (·.getId == n.getId) then throwErrorAt n "duplicate schema field"
    if n.getId.isAnonymous || n.getId.components.length != 1 then
      throwErrorAt n "a field needs a simple identifier"
    fieldNames := fieldNames.push n
    types := types.push t
  let names := fieldNames.map fun n => n.getId.toString
  let mut dependencies : Array FunctionalDependency := #[]
  for fd in fds.getD #[] do
    let `(schemaDependency| [$[$xs:ident],*] -> [$[$ys:ident],*]) := fd | throwUnsupportedSyntax
    dependencies := dependencies.push ⟨xs.toList.map (·.getId.toString), ys.toList.map (·.getId.toString)⟩
  let columnTypes ← liftTermElabM do
    types.mapM fun type => do
      let code ← elabTerm (← `(ColumnType.type (α := $type))) (some (mkConst ``ScalarType))
      synthesizeSyntheticMVarsNoPostponing
      evalExpr ScalarType (mkConst ``ScalarType) (← instantiateMVars code)
  let definition : TableDef := {
    name := dbName.getString
    columns := (names.zip columnTypes).toList.map fun (n, t) => ⟨n, t⟩
    key := keys.toList.map (·.getId.toString)
    dependencies := dependencies.toList
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
  let schemaId := mkIdent (name.getId ++ `schema)
  let tableId := mkIdent (name.getId ++ `table)
  let cols ← liftTermElabM do
    definition.columns.toArray.mapM fun c => do `(Column.mk $(quote c.name) $(← scalarTypeTerm c.type))
  let deps ← dependencies.mapM fun d =>
    `(FunctionalDependency.mk $(quote d.determinant) $(quote d.dependent))
  elabCommand (← `(def $schemaId : TableDef := {
    name := $dbName, columns := [$cols,*], key := $(quote definition.key), dependencies := [$deps,*]}))
  elabCommand (← `(def $tableId : Source $name := ⟨$schemaId⟩))
  let fullName := (← getCurrNamespace) ++ name.getId
  let info : SchemaInfo := {
    rowType := fullName
    source := fullName ++ `table
    definition
    projections := fieldNames.map fun f => (fullName ++ f.getId, f.getId.toString)
  }
  modifyEnv fun env => schemaExtension.addEntry env info

end LeanRel
