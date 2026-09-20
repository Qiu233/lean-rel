import Tests.Schema
import Tests.MiddleOnly
import Tests.Compiler
import Tests.FunctionScopes
import Tests.SchemaAccess

open LeanRel LeanRel.Frontend LeanRel.Tests
open scoped LeanRel.SQL

deriving instance Inhabited for LeanRel.Tests.Person

private def check (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAIL: {name}")
  IO.println s!"ok: {name}"

private def get {α} (value : Except String α) : IO α := IO.ofExcept value

-- Compiled in a separate module from schema/rule declarations: tests extension persistence.
def adultsSQL (n : Int) := sql% adults n
def sourceSQL (source : Source Person) := sql% [p.name | p ← source]
def joinQuery := query% [ (p.name, t.label) | p : Person ← table, t : Team ← table, p.teamId == t.teamId ]
def joinSQL := sql% joinQuery
def ordered := (query% [ (p.id, p.age) | p : Person ← table ]).sortBy Prod.snd
def paged := (ordered.take 2).filter (fun p => p.2 ≥ 20)
def pagedSQL := sql% paged
def teamIds := (query% [p.teamId | p : Person ← table]).distinct
def teamIdsSQL := sql% teamIds
def countSQL := sql% (adults 18).count
def sumSQL := sql% (query% [p.age | p : Person ← table]).sum
def anySQL := sql% (Query.scan (@table Person _)).any (fun p => p.age > 29)
def allSQL := sql% (Query.scan (@table Person _)).all (fun p => p.age > 20)
open LeanRel.SQL.Standard in
def lowerSQL := sql% [p.name.toLower | p : Person ← table]
def fallbackSQL := sql% [valueOr p.note p.name | p : Person ← table]
def optionalSQL := sql% [p.id | p : Person ← table, p.note == none]
def bonus (age : Int) : Int := if age ≥ 18 then age + 2 else age
def helperSQL := sql% [(p.id, bonus p.age) | p : Person ← table]

def nestedTeams := query% [(t.label, members) | t : Team ← table,
  members ← (query% [(p.name, p.note) | p : Person ← table, p.teamId == t.teamId]).sortBy Prod.fst |>.collect]
def nestedTeamsSQL := sql% nestedTeams
def groups := (Query.scan (@table Person _)).groupBy (·.teamId) |>.sortBy Prod.fst
def groupsSQL := sql% groups
def groupSizes := query% [(g.1, g.2.length) | g ← groups]
def groupSizesSQL := sql% groupSizes
def deepNested := query% [(t.label, members) | t : Team ← table,
  members ← (query% [(p.name, others) | p : Person ← table, p.teamId == t.teamId,
    others ← (query% [q.id | q : Person ← table, q.teamId == p.teamId]).collect]).collect]
def deepNestedSQL := sql% deepNested

def middleAdult (minimum : Int) (p : Person.Columns SQL.Scalar) : SQL.Scalar Bool :=
  p.age >=. SQL.param minimum
def nativeMiddle (minimum : Int) := sql! [
  SELECT (p.name, p.age + 1) FROM p IN @table Person _
  WHERE middleAdult minimum p ORDER BY [p.id.asc]]
def nativeMiddleJoin := sql! [
  SELECT (p.name, t.label) FROM p IN @table Person _
  JOIN t IN @table Team _ ON p.teamId ==. t.teamId ORDER BY [p.id.asc]]
def nativeCorrelated := sql! [SELECT t.label FROM t IN @table Team _ WHERE
  (sql! [SELECT p.id FROM p IN @table Person _ WHERE p.teamId ==. t.teamId]).exists_
  ORDER BY [t.teamId.asc]]
def nativeGrouped := sql! [SELECT (p.teamId, p.id.count) FROM p IN @table Person _
  GROUP BY p.teamId HAVING p.id.count >. 1 ORDER BY [p.teamId.asc]]
def nativeRecord := sql! [SELECT p FROM p IN @table Person _ ORDER BY [p.id.asc]]

-- Full Lean terms and a later syntax extension work without changing a central AST.
syntax "unless " term : queryQualifier
macro_rules
  | `(queryQualifier%[ unless $p:term ] $body:term) => `(if $p then Query.empty else $body)
-- The block clause extension exercises the public queryBody% extension point.
syntax "unless " term "; " comprehension : comprehension
macro_rules
  | `(queryBody%{ unless $p:term; $body:comprehension }) =>
    `(if $p then Query.empty else queryBody%{ $body })

def extendedSQL (minimum : Int) := sql% [
  p.name | p : Person <- table, let cutoff := minimum, unless p.age < cutoff]
def blockQuery (minimum : Int) : Query String := query% {
  for query : Person in table; let cutoff := minimum;
  unless query.age < cutoff; yield query.name }
def blockSQL (minimum : Int) : SQL.Query := sql% {
  for query : Person in table; let cutoff := minimum;
  unless query.age < cutoff; yield query.name }

def nativeNested := query% [
  (p.name, scores) |
  p : Person ← table,
  let bump := fun (n : Int) => match p.note with | none => n + 1 | some _ => n,
  scores ← (query% [bump n | n ← [p.age, p.age + 1]]).collect]

def raiseAdults := update% [ {p with age := p.age + 1} | p ← peopleView, p.age ≥ 18 ]
def badSelection := update% [ {p with age := 1} | p ← adultsView ]
def renameBrief := update% [ {p with name := p.name ++ "!"} | p ← briefView, p.id == 1 ]
def renameTeams := update% [ (pair.1, {pair.2 with label := pair.2.label ++ "!"}) | pair ← joinedView ]
def raiseRating := update% [ {t with rating := 9} | t ← tracksView.select (·.album == 1), t.track == 5 ]

private def insertRows (table : TableDef) (rows : Relation) : SQL.Statement :=
  .insert [table.name] table.names (.values (rows.map fun row => table.names.map fun n => .param ((row.lookup n).getD .null)))

private def compareQuery [Codec α] [BEq α] (connection : SQL.Connection) (name : String)
    (native : Query α) (compiled : SQL.Query) : IO Unit := do
  let expected ← get (native.run database)
  let actual ← get (← connection.query (α := α) compiled)
  check name (expected == actual)

def main : IO Unit := do
  LeanRel.Tests.FunctionScopes.run
  check "native comprehensions" ((← get ((adults 18).run database)) == [("Ada", 31), ("Chen", 26)])
  check "native nested terms" ((← get (nativeNested.run database)) == [("Ada", [31, 32]), ("Bo", [16, 17]), ("Chen", [26, 27])])
  let extended := query% [p.name | p : Person ← table, unless p.age < 18]
  check "open DSL clause" ((← get (extended.run database)) == ["Ada", "Chen"])
  let ascii := query% [p.name | p : Person <- table, p.age ≥ 18]
  check "shared left-arrow parser" ((← get (ascii.run database)) == ["Ada", "Chen"])
  let noChange ← get ((peopleView.put people).run database)
  check "lens GetPut" noChange.changes.isEmpty
  check "selection predicate rejection" ((badSelection.run database).toOption.isNone)
  let modified ← get (raiseAdults.run database)
  check "update qualifier preserves unselected rows" ((← get (peopleView.get.run modified.database)).map (·.age) == [31, 16, 26])
  let projected ← get (renameBrief.run database)
  check "projection preserves hidden fields" ((← get (peopleView.get.run projected.database)).head!.age == 30)
  let inserted ← get ((briefView.put [⟨1, "Ada"⟩, ⟨2, "Bo"⟩, ⟨3, "Chen"⟩, ⟨4, "New"⟩]).run database)
  check "projection insertion defaults" ((← get (peopleView.get.run inserted.database)).getLast!.age == 0)
  let joined ← get (renameTeams.run database)
  check "join propagates shared dimension" ((← get ((View.base (@table Team _)).get.run joined.database)).map (·.label) == ["A!", "B!", "unreferenced"])
  let rated ← get (raiseRating.run database)
  let ratedRows ← get (tracksView.get.run rated.database)
  check "selection revises hidden FD dependents" ((ratedRows.filter (·.track == 5)).all (·.rating == 9))
  check "self-join policy is explicit" (((peopleView.join peopleView).get.run database).toOption.isNone)
  let duplicate := people ++ [people.head!]
  check "duplicate keys rejected" (((peopleView.put duplicate).run database).toOption.isNone)

  let file := System.FilePath.mk ".lake/lean-rel-tests.sqlite"
  if ← file.pathExists then IO.FS.removeFile file
  let connection ← Backend.SQLite.connect file
  let create ← get ([(HasTable.schema Person), (HasTable.schema Team), (HasTable.schema Track)].mapM fun t => SQL.Statement.createTable <$> SQL.CreateTable.ofTable t)
  let _ ← get (← connection.execute (create ++ [insertRows (HasTable.schema Person) (records people), insertRows (HasTable.schema Team) (records teams), insertRows (HasTable.schema Track) (records tracks)]))
  compareQuery connection "SQL/native projection and parameters" (adults 18) (adultsSQL 18)
  compareQuery connection "runtime source with static row metadata" (query% [p.name | p : Person ← table]) (sourceSQL (@table Person _))
  compareQuery connection "sql% comprehension shares clause extensions" (query% [p.name | p : Person ← table, unless p.age < 18]) (extendedSQL 18)
  compareQuery connection "query% and sql% blocks share expansion and ordinary query binder" (blockQuery 18) (blockSQL 18)
  compareQuery connection "SQL/native join" joinQuery joinSQL
  compareQuery connection "SQL/native order + take + filter" paged pagedSQL
  compareQuery connection "SQL/native distinct" teamIds teamIdsSQL
  compareQuery connection "SQL/native count" (adults 18).count countSQL
  compareQuery connection "SQL/native sum" (query% [p.age | p : Person ← table]).sum sumSQL
  compareQuery connection "SQL/native any" ((Query.scan (@table Person _)).any (fun p => p.age > 29)) anySQL
  compareQuery connection "SQL/native all" ((Query.scan (@table Person _)).all (fun p => p.age > 20)) allSQL
  compareQuery connection "scoped standard LOWER translation" (query% [p.name.toLower | p : Person ← table]) lowerSQL
  compareQuery connection "imported declaration attribute with implicit parameter"
    (query% [valueOr p.note p.name | p : Person ← table]) fallbackSQL
  compareQuery connection "nullable equality" (query% [p.id | p : Person ← table, p.note == none]) optionalSQL
  compareQuery connection "native helper and conditionals" (query% [(p.id, bonus p.age) | p : Person ← table]) helperSQL
  compareQuery connection "ordered correlated nested collections and empty groups" nestedTeams nestedTeamsSQL
  compareQuery connection "native grouping" groups groupsSQL
  compareQuery connection "native collection length" groupSizes groupSizesSQL
  compareQuery connection "two levels of nested collections" deepNested deepNestedSQL
  check "middle end reuses typed Lean predicate" ((← get (← (nativeMiddle 18).fetch connection)) == [("Ada", 31), ("Chen", 26)])
  check "middle end dot fields and join binders" ((← get (← nativeMiddleJoin.fetch connection)) == [("Ada", "A"), ("Bo", "A"), ("Chen", "B")])
  check "middle end nested scopes" ((← get (← nativeCorrelated.fetch connection)) == ["A", "B"])
  check "middle end grouping" ((← get (← nativeGrouped.fetch connection)) == [(10, 2)])
  check "middle end whole record projection" ((← get (← nativeRecord.fetch connection)) == people)

  let memory ← Backend.SQLite.connect ":memory:"
  let createPerson ← get (SQL.CreateTable.ofTable (HasTable.schema Person))
  let _ ← get (← memory.execute [.createTable createPerson])
  let batch ← get sql! [INSERT INTO @table Person _ VALUES people]
  let _ ← get (← memory.execute [batch])
  let _ ← get (← memory.execute [sql! [UPDATE p IN @table Person _ SET {p with age := p.age + 1}
    WHERE middleAdult 18 p]])
  check "native leansqlite memory connection persists" ((← get (← (nativeMiddle 18).fetch memory)) == [("Ada", 32), ("Chen", 27)])
  let _ ← get (← memory.execute [sql! [DELETE FROM p IN @table Person _ WHERE p.age <. 18]])
  check "middle end typed delete" ((← get (← nativeRecord.fetch memory)).length == 2)
  let _ ← get (← Compiler.executeUpdate memory raiseAdults)
  check "lens reads its database snapshot" ((← get (← (nativeMiddle 18).fetch memory)) == [("Ada", 33), ("Chen", 28)])

  let scalars ← get (← memory.execute [sql! [SELECT ${(true)}, ${(3.5 : Float)}, ${(none : Option String)}, ${(#[0, 1, 255] : Array UInt8)}]])
  check "native SQLite scalar bindings including BLOB" (scalars[0]!.rows == [[.int 1, .real 3.5, .null, .blob #[0, 1, 255]]])
  let tooLarge ← memory.execute [sql! [SELECT ${(9223372036854775808 : Int)}]]
  check "SQLite rejects integer overflow before binding" tooLarge.toOption.isNone
  let itemDDL ← get (SQL.CreateTable.ofTable (HasTable.schema MiddleOnly.Item))
  let item : MiddleOnly.Item := ⟨1, "binary", true, #[0, 255]⟩
  let itemInsert ← get sql! [INSERT INTO @table MiddleOnly.Item _ VALUES [item]]
  let _ ← get (← memory.execute [.createTable itemDDL, itemInsert])
  let _ ← get (← Compiler.executeUpdate memory
    (update% [{i with enabled := !i.enabled} | i : MiddleOnly.Item ← View.base table]))
  let items ← get (← (sql! [SELECT i FROM i IN @table MiddleOnly.Item _]).fetch memory)
  check "snapshot decodes SQLite boolean and BLOB" (items == [{item with enabled := false}])
  let metadataDDL ← get (SQL.CreateTable.ofTable (HasTable.schema MetadataField))
  let metadata : MetadataField := ⟨1, "public", "people"⟩
  let metadataInsert ← get sql! [INSERT INTO @table MetadataField _ VALUES [metadata]]
  let _ ← get (← memory.execute [.createTable metadataDDL, metadataInsert])
  let _ ← get (← Compiler.executeUpdate memory
    (update% [{r with schema := r.schema ++ "_updated"} | r : MetadataField ← View.base table]))
  let metadataRows ← get (← memory.query (α := String × String) SchemaAccess.metadataQuery)
  check "schema field survives typed update and SQL query" (metadataRows == [("public_updated", "people")])
  let changed ← get (← memory.execute [sql! [UPDATE p IN @table Person _ SET {p with age := p.age + 2}
    WHERE (sql! [SELECT i.id FROM i IN @table MiddleOnly.Item _ WHERE i.id ==. p.id]).exists_]])
  check "correlated native update" (changed[0]!.affected == 1)
  let missing ← get (memory.render sql! [UPDATE people SET age = 999 WHERE id = 500])
  let conflict ← memory.run {statements := [⟨missing, some 1⟩]}
  check "checked write conflict" conflict.toOption.isNone

  let middle ← get (← connection.execute [
    sql! [ SELECT teamId, COUNT(*) AS total FROM people GROUP BY teamId HAVING COUNT(*) > 0 ORDER BY teamId],
    sql! [ WITH grown AS (SELECT name FROM people WHERE age >= 18) SELECT name FROM grown ORDER BY name],
    sql! [ SELECT name, ROW_NUMBER() OVER (ORDER BY age DESC) AS ranking FROM people ORDER BY ranking],
    sql! [ SELECT name FROM people WHERE id IN (1, 3) UNION SELECT label FROM teams WHERE teamId = 30],
    sql! [ SELECT p.name FROM people AS p LEFT JOIN teams AS t ON p.teamId = t.teamId WHERE t.label IS NOT NULL ORDER BY p.id],
    sql! [ SELECT CASE WHEN age >= 18 THEN "adult" ELSE "minor" END FROM people ORDER BY id]
  ])
  check "SQL grouping/having" (middle[0]!.rows == [[.int 10, .int 2], [.int 20, .int 1]])
  check "SQL CTE" (middle[1]!.rows == [[.text "Ada"], [.text "Chen"]])
  check "SQL window" (middle[2]!.rows == [[.text "Ada", .int 1], [.text "Chen", .int 2], [.text "Bo", .int 3]])
  check "SQL set operations" (middle[3]!.rows.length == 3)
  check "SQL outer join" (middle[4]!.rows.length == 3)
  check "SQL CASE" (middle[5]!.rows == [[.text "adult"], [.text "minor"], [.text "adult"]])

  let hostile := "O'Brien'); DROP TABLE people; --"
  let _ ← get (← connection.execute [sql! [ INSERT INTO people (id, name, age, teamId, note) VALUES (4, ${hostile}, 19, 10, NULL)]])
  let exact ← get (← connection.execute [sql! [ SELECT name FROM people WHERE id = 4]])
  check "SQL parameter injection boundary" (exact[0]!.rows == [[.text hostile]])
  let stale ← Compiler.applyUpdate connection raiseAdults database
  check "snapshot detects concurrent inserts" stale.toOption.isNone
  let _ ← get (← connection.execute [sql! [ DELETE FROM people WHERE id = 4]])
  let _ ← get (← Compiler.applyUpdate connection raiseAdults database)
  let ages ← get (← connection.execute [sql! [ SELECT age FROM people ORDER BY id]])
  check "lens changes execute as SQL" (ages[0]!.rows == [[.int 31], [.int 16], [.int 26]])
  let _ ← get (← Compiler.executeUpdate connection raiseRating)
  let ratings ← get (← connection.execute [sql! [SELECT rating FROM tracks WHERE track = 5 ORDER BY album]])
  check "explicit source FD propagates to hidden SQL rows" (ratings[0]!.rows == [[.int 9], [.int 9]])
  let rollback ← connection.execute [
    sql! [ UPDATE people SET age = 100 WHERE id = 1],
    sql! [ INSERT INTO people (id, name, age, teamId, note) VALUES (1, "duplicate", 0, 10, NULL)]]
  check "transaction failure" rollback.toOption.isNone
  let afterRollback ← get (← connection.execute [sql! [ SELECT age FROM people WHERE id = 1]])
  check "transaction rollback is atomic" (afterRollback[0]!.rows == [[.int 31]])

  let pg ← get (SQL.render .postgresql sql! [ SELECT name FROM people WHERE age > ${(18 : Int)}])
  let mysql ← get (SQL.render .mysql sql! [ SELECT name FROM people WHERE age > ${(18 : Int)}])
  check "PostgreSQL placeholders" (pg.sql.contains "$1" && pg.parameters.size == 1)
  check "MySQL quoting and placeholders" (mysql.sql.contains "`people`" && mysql.parameters.size == 1)
  check "unsupported backend capability" ((SQL.render .mysql sql! [ DELETE FROM people WHERE id = 1 RETURNING id]).toOption.isNone)
  let ddl ← get (SQL.render .sqlite sql! [ CREATE TABLE defaults (id INTEGER NOT NULL, name TEXT DEFAULT "it's", PRIMARY KEY (id))])
  check "DDL literals have no bind parameters" ddl.parameters.isEmpty
  IO.FS.removeFile file
  IO.println "All tests passed."
