import LeanRel.Frontend.Syntax

/-! Relational lenses with set semantics and checked snapshot propagation.
The select/merge and left-deleting join algorithms follow relational lenses.
This is a reference implementation, not an incremental database optimizer. -/
namespace LeanRel.Frontend

private def encodeRecord [Codec α] (row : α) : Except String Record :=
  match Codec.encode row with
  | .record fields => .ok fields
  | _ => .error "a relational view needs a record codec"

private def filterM (rows : Relation) (p : Record → Except String Bool) : Except String Relation := do
  let marked ← rows.mapM fun r => return (r, ← p r)
  return (marked.filter Prod.snd).map Prod.fst

/-- Revise old records using the functional dependencies witnessed by the new view. -/
def revise (fds : List FunctionalDependency) (old fresh : Relation) : Relation :=
  (List.range (fds.length + 1)).foldl (fun rows _ =>
    fds.foldl (fun rows fd => rows.map fun row =>
      match fresh.find? (fun n => agree row n fd.determinant) with
      | none => row
      | some n => row.map fun (name, v) =>
        (name, if fd.dependent.contains name then (n.lookup name).getD v else v)) rows) old

def merge (fds : List FunctionalDependency) (old fresh : Relation) : Relation :=
  uniqueRecords (revise fds old fresh ++ fresh)

private def naturalJoin (shared : List String) (a b : Relation) : Relation :=
  uniqueRecords (a.flatMap fun a => (b.filter fun b => agree a b shared).map fun b =>
    a ++ b.filter (fun (n, _) => !(a.map Prod.fst).contains n))

private def closure (fds : List FunctionalDependency) (names : List String) (fuel : Nat) : List String :=
  (List.range fuel).foldl (fun known _ => fds.foldl (fun known fd =>
    if fd.determinant.all known.contains then (known ++ fd.dependent).eraseDups else known) known) names

structure View (α : Type) where
  definition : TableDef
  sources : List TableDef
  encode : α → Except String Record
  decode : Record → Except String α
  getRows : Database → Except String Relation
  putRows : Database → Relation → Except String Database

namespace View

def base [Codec α] (source : Source α) : View α where
  definition := source.definition
  sources := [source.definition]
  encode := encodeRecord
  decode row := Codec.decode (.record row)
  getRows db := do
    let rows ← db.getTable source.definition.name
    source.definition.validateRows rows
    if source.definition.key.isEmpty then throw "an updatable source needs a key"
    return rows
  putRows db rows := do
    source.definition.validateRows rows
    if source.definition.key.isEmpty then throw "an updatable source needs a key"
    return db.set source.definition.name rows

def get (v : View α) : Query α := ⟨fun db => do (← v.getRows db).mapM v.decode⟩

def select (v : View α) (predicate : α → Bool) : View α :=
  let p row := do return predicate (← v.decode row)
  {v with
    getRows := fun db => do filterM (← v.getRows db) p
    putRows := fun db fresh => do
      v.definition.validateRows fresh
      for r in fresh do
        if !(← p r) then throw "selection lens: updated row violates the view predicate"
      let old ← v.getRows db
      let hidden ← filterM old fun r => return !(← p r)
      let revised := merge v.definition.fds hidden fresh
      let updated ← filterM revised fun r => return !(← p r) || fresh.any (sameRecord r)
      v.putRows db updated}

/-- Key-preserving projection. Dropped fields are recovered from the old source;
defaults apply only to newly inserted keys. -/
def project [Codec β] (v : View α) (target : Source β) (defaults : Record := []) : View β :=
  let names := target.definition.names
  let check : Except String Unit := do
    target.definition.validate
    if v.definition.key.isEmpty || !v.definition.key.all names.contains then
      throw "projection lens must retain the source key"
    if target.definition.key != v.definition.key then
      throw "projection lens key must equal the retained source key"
    for c in target.definition.columns do
      if !v.definition.columns.contains c then throw s!"unknown or incompatible projected column: {c.name}"
    if (defaults.map Prod.fst).eraseDups.length != defaults.length then throw "duplicate projection default"
    for (n, _) in defaults do
      if names.contains n || !v.definition.names.contains n then throw s!"invalid dropped-column default: {n}"
  {
    definition := target.definition
    sources := v.sources
    encode := encodeRecord
    decode := fun r => Codec.decode (.record r)
    getRows := fun db => do
      check
      (← v.getRows db).mapM fun r => Record.project r names
    putRows := fun db fresh => do
      check
      target.definition.validateRows fresh
      let old ← v.getRows db
      let expanded ← fresh.mapM fun row => do
        let previous := old.find? fun old => agree old row v.definition.key
        v.definition.names.mapM fun n => do
          if let some x := row.lookup n then return (n, x)
          if let some old := previous then return (n, ← Record.getField old n)
          return (n, ← Record.getField defaults n)
      v.putRows db expanded
  }

def rename (v : View α) (mapping : List (String × String)) : View α :=
  let name n := (mapping.lookup n).getD n
  let forward (r : Record) := r.map fun (n, x) => (name n, x)
  let backward (r : Record) := r.map fun (n, x) =>
    ((mapping.find? (·.2 == n)).map Prod.fst |>.getD n, x)
  let definition := {v.definition with
    columns := v.definition.columns.map fun c => {c with name := name c.name}
    key := v.definition.key.map name
    dependencies := v.definition.dependencies.map fun fd =>
      ⟨fd.determinant.map name, fd.dependent.map name⟩}
  let check : Except String Unit := do
    definition.validate
    if (mapping.map Prod.fst).eraseDups.length != mapping.length then throw "duplicate rename source"
    for (n, _) in mapping do
      if !v.definition.names.contains n then throw s!"unknown rename column: {n}"
  {
    definition, sources := v.sources
    encode := fun row => forward <$> v.encode row
    decode := fun row => v.decode (backward row)
    getRows := fun db => do check; return (← v.getRows db).map forward
    putRows := fun db rows => do check; v.putRows db (rows.map backward)
  }

inductive DeletePolicy where
  | left | right | both
  deriving BEq, Repr

/-- Natural join with an explicit deletion policy. Shared fields must determine
the right side; overlapping source ownership is rejected. -/
def join (left : View α) (right : View β) (deletion : DeletePolicy := .left) : View (α × β) :=
  let leftNames := left.definition.names
  let rightNames := right.definition.names
  let shared := leftNames.filter rightNames.contains
  let definition : TableDef := {
    name := s!"{left.definition.name} ⋈ {right.definition.name}"
    columns := left.definition.columns ++ right.definition.columns.filter (fun c => !leftNames.contains c.name)
    key := left.definition.key
    dependencies := left.definition.fds ++ right.definition.fds
  }
  let check : Except String Unit := do
    definition.validate
    if left.sources.any (fun l => right.sources.any (·.name == l.name)) then
      throw "join lens sources overlap; self-join updates require an explicit strategy"
    for c in right.definition.columns do
      if leftNames.contains c.name && !left.definition.columns.contains c then
        throw s!"incompatible join column: {c.name}"
    let determined := closure right.definition.fds shared (rightNames.length + 1)
    if !rightNames.all determined.contains then
      throw "join lens: shared columns must functionally determine the right side"
  {
    definition, sources := left.sources ++ right.sources
    encode := fun (l, r) => do
      let l ← left.encode l
      let r ← right.encode r
      if !agree l r shared then throw "join update assigns inconsistent shared fields"
      return l ++ r.filter (fun (n, _) => !leftNames.contains n)
    decode := fun row => do
      return (← left.decode (← Record.project row leftNames), ← right.decode (← Record.project row rightNames))
    getRows := fun db => do
      check
      return naturalJoin shared (← left.getRows db) (← right.getRows db)
    putRows := fun db fresh => do
      check
      definition.validateRows fresh
      let l ← left.getRows db
      let r ← right.getRows db
      let l' := merge left.definition.fds l (uniqueRecords (← fresh.mapM (Record.project · leftNames)))
      let r' := merge right.definition.fds r (uniqueRecords (← fresh.mapM (Record.project · rightNames)))
      let excess := (naturalJoin shared l' r').filter fun row => !fresh.any (sameRecord row)
      let badL ← excess.mapM (Record.project · leftNames)
      let badR ← excess.mapM (Record.project · rightNames)
      let l' := if deletion == .right then l' else l'.filter fun row => !badL.any (sameRecord row)
      let r' := if deletion == .left then r' else r'.filter fun row => !badR.any (sameRecord row)
      let db ← left.putRows db l'
      right.putRows db r'
  }

end View

instance : ToQuery View α := ⟨View.get⟩

structure Snapshot where
  table : TableDef
  rows : Relation
  deriving Repr

structure SourceChange where
  table : TableDef
  before : Relation
  after : Relation
  deriving Repr

structure UpdateResult where
  database : Database
  reads : List Snapshot
  changes : List SourceChange
  deriving Repr

/-- A baked update request whose computation is ordinary Lean code. -/
structure Update where
  run : Database → Except String UpdateResult
  sources : List TableDef

def View.put (view : View α) (desired : List α) : Update := { sources := view.sources, run := fun db => do
  let _ ← view.getRows db
  let fresh ← desired.mapM view.encode
  view.definition.validateRows fresh
  let reads ← view.sources.mapM fun table => do
    let rows ← db.getTable table.name
    table.validateRows rows
    return {table, rows : Snapshot}
  let updated ← view.putRows db fresh
  -- Checked acceptance contract: never emit changes that do not reproduce the desired view.
  if !sameRelation (← view.getRows updated) fresh then
    throw "lens update is ambiguous or violates the selected policy (PutGet failed)"
  let mut changes := []
  for snapshot in reads do
    let rows ← updated.getTable snapshot.table.name
    snapshot.table.validateRows rows
    if !sameRelation rows snapshot.rows then
      changes := changes ++ [{table := snapshot.table, before := snapshot.rows, after := rows}]
  return {database := updated, reads, changes} }

def View.modify (view : View α) (transform : α → α) : Update := { sources := view.sources, run := fun db => do
  let rows ← view.get.run db
  (view.put (rows.map transform)).run db }

open Lean Elab Term
syntax:max (name := updateComprehension) "update " "[" term " | " queryQualifier,+ "]" : term

@[term_elab updateComprehension]
def elabUpdate : TermElab := fun stx expected => do
  let `(update [ $result:term | $[$qualifiers:queryQualifier],* ]) := stx | throwUnsupportedSyntax
  let first := qualifiers[0]!
  let `(queryQualifier| $x:ident $[: $type:term]? ← $view:term) := first
    | throwErrorAt first "an update comprehension starts with a view generator"
  let mut body := result
  for qualifier in (qualifiers.extract 1 qualifiers.size).reverse do
    body ← match qualifier with
      | `(queryQualifier| let $y:ident := $v:term) => `(let $y := $v; $body)
      | `(queryQualifier| $p:term) => `(if $p then $body else $x)
      | _ => throwErrorAt qualifier "compose views with View.join before updating; subsequent qualifiers are guards or lets"
  let transform ← match type with
    | some type => `(fun ($x : $type) => $body)
    | none => `(fun $x => $body)
  elabTerm (← `(View.modify $view $transform)) expected

end LeanRel.Frontend
