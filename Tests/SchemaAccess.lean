import Tests.Schema

open LeanRel LeanRel.Frontend LeanRel.Tests

namespace LeanRel.Tests.SchemaAccess

-- Generated instances survive imports; no per-row helper declarations remain.
#guard (HasTable.schema Person).name == "people"
#guard (@table Person _).definition.key == ["id"]
#guard_msgs (drop info) in
#check_failure Person.table
#guard_msgs (drop info) in
#check_failure Person.schema

def qualified := query% [p.name | p : Person ← HasTable.table]
def typed := query% [p.name | p : Person ← table]
def sourceKnown := query% [p.name | p ← (table : Source Person)]
def resultKnown : Query Person := query% [p | p ← table]
def inferredBlock : Query Person := query% { for p in table; yield p }
def typedList := query% [n + 1 | n : Int <- [1, 2, 3]]
def inferredList : Query Int := query% [n + 1 | n ← [1, 2, 3]]
def typedQuery := query% [p.name | p : Person ← resultKnown]
def typedView := query% [p.name | p : Person ← View.base table]

#guard (typed.run database).toOption == some ["Ada", "Bo", "Chen"]
#guard (qualified.run database).toOption == (typed.run database).toOption
#guard (sourceKnown.run database).toOption == (typed.run database).toOption
#guard (resultKnown.run database).toOption == some people
#guard (inferredBlock.run database).toOption == some people
#guard (typedList.run []).toOption == some [2, 3, 4]
#guard (inferredList.run []).toOption == some [2, 3, 4]
#guard (typedQuery.run database).toOption == (typed.run database).toOption
#guard (typedView.run database).toOption == (typed.run database).toOption

#guard_msgs (drop info) in
#check_failure query% [p | p : Team ← (table : Source Person)]
#guard_msgs (drop info) in
#check_failure query% [n | n : Int ← table]

-- Local instances choose the source; both metadata and SQL use the same table.
private def relocated : Source Person :=
  ⟨{ HasTable.schema Person with name := "people_archive" }⟩
section
local instance : HasTable Person := ⟨relocated⟩
def relocatedSQL := sql% [p.name | p : Person ← table]
#guard (HasTable.schema Person).name == "people_archive"
#guard ((query% [p | p : Person ← table]).run [("people_archive", records people)]).toOption == some people
#guard ((SQL.render .sqlite (.query relocatedSQL)).toOption.map (·.sql)).any
  (·.contains "\"people_archive\"")
end
#guard (HasTable.schema Person).name == "people"

-- SCHEMA is non-reserved in SQL:2023; its record projection is now usable.
#guard (MetadataField.mk 1 "public" "people").schema == "public"
#guard (HasTable.schema MetadataField).names == ["id", "schema", "tableName"]
def metadataQuery := sql% [(r.schema, r.tableName) | r : MetadataField ← table]

-- SQL-style constraints can precede the columns, or follow a column's Lean type.
schema CompositeKey "composite_keys" (
  PRIMARY KEY (leftId, rightId),
  leftId Int NOT NULL,
  rightId Int,
  note Option String
)
schema InlineKey "inline_keys" (id Int PRIMARY KEY NOT NULL, label String)
schema Keyless "keyless" (value Int, note (Option String))

#guard (HasTable.schema CompositeKey).key == ["leftId", "rightId"]
#guard (HasTable.schema CompositeKey).columns[2]!.type == .nullable .text
#guard (HasTable.schema InlineKey).key == ["id"]
#guard (HasTable.schema Keyless).key.isEmpty
#guard ((query% [r.value | r : Keyless ← table]).run
  [("keyless", records [Keyless.mk 1 none, Keyless.mk 1 none])]).toOption == some [1, 1]
#guard ((View.base (@table Keyless _)).get.run [("keyless", [])]).toOption.isNone
#guard ((SQL.CreateTable.ofTable (HasTable.schema InlineKey) >>= fun ddl =>
  SQL.render .sqlite (.createTable ddl)).toOption.map (·.sql)) ==
  some "CREATE TABLE \"inline_keys\" (\"id\" BIGINT NOT NULL, \"label\" TEXT NOT NULL, PRIMARY KEY (\"id\"))"

-- Additional FDs still reject invalid snapshots after moving out of the command.
private def inconsistentTracks : Database :=
  [("tracks", records [Track.mk 1 5 3, Track.mk 2 5 4])]
#guard (HasTable.schema Track).dependencies.isEmpty
#guard ((Query.scan (@table Track _)).run inconsistentTracks).toOption.isSome
#guard (tracksView.get.run inconsistentTracks).toOption.isNone
#guard ((View.base ((@table Track _).withDependencies [⟨["missing"], ["rating"]⟩])).get.run database).toOption.isNone

/-- error: a schema can declare only one PRIMARY KEY -/
#guard_msgs in
schema MultipleKeys "bad" (id Int PRIMARY KEY, other Int PRIMARY KEY)

/-- error: a schema can declare only one PRIMARY KEY -/
#guard_msgs in
schema MixedKeys "bad" (id Int PRIMARY KEY, PRIMARY KEY (id))

/-- error: nullable key column: id -/
#guard_msgs in
schema NullableKey "bad" (id Option Int PRIMARY KEY)

/-- error: NOT NULL conflicts with the nullable Lean type of 'note' -/
#guard_msgs in
schema NullableRequired "bad" (note Option String NOT NULL)

/-- error: duplicate NOT NULL constraint -/
#guard_msgs in
schema DuplicateRequired "bad" (id Int NOT NULL NOT NULL)

/-- error: a schema needs at least one column -/
#guard_msgs in
schema MissingColumns "bad" (PRIMARY KEY (id))

/-- error: schema field 'table' is reserved by the SQL standard (TABLE) -/
#guard_msgs in
schema ReservedTable "reserved_table" (id Int PRIMARY KEY, table String)

/-- error: schema field 'TaBlE' is reserved by the SQL standard (TABLE) -/
#guard_msgs in
schema ReservedMixedCase "reserved_table" (id Int PRIMARY KEY, TaBlE String)

end LeanRel.Tests.SchemaAccess
