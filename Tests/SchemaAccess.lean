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

/-- error: schema field 'table' is reserved by the SQL standard (TABLE) -/
#guard_msgs in
schema ReservedTable "reserved_table" { id : Int, table : String } key [id]

/-- error: schema field 'TaBlE' is reserved by the SQL standard (TABLE) -/
#guard_msgs in
schema ReservedMixedCase "reserved_table" { id : Int, TaBlE : String } key [id]

end LeanRel.Tests.SchemaAccess
