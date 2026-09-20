import LeanRel

namespace LeanRel.Tests
open Frontend

abbrev Age := Int
schema Person "people" (
  id Int PRIMARY KEY,
  name String NOT NULL,
  age Age, teamId Int,
  note Option String
)
schema Team "teams" (teamId Int, label String, PRIMARY KEY (teamId))
schema Brief "brief" (id Int PRIMARY KEY, name String)
schema Track "tracks" (album Int, track Int, rating Int, PRIMARY KEY (album, track))
schema MetadataField "metadata_fields" (id Int PRIMARY KEY, schema String, tableName String)

-- General functional dependencies belong to lens source configuration, not SQL DDL.
def tracksSource := (@table Track _).withDependencies [⟨["track"], ["rating"]⟩]
def tracksView := View.base tracksSource

-- Test declaration attributes and SQL arity excluding implicit Lean parameters.
@[sql_function "COALESCE" 2]
def valueOr {α : Type} (value : Option α) (fallback : α) : α := value.getD fallback

def people : List Person := [
  ⟨1, "Ada", 30, 10, none⟩,
  ⟨2, "Bo", 16, 10, some "young"⟩,
  ⟨3, "Chen", 25, 20, none⟩]
def teams : List Team := [⟨10, "A"⟩, ⟨20, "B"⟩, ⟨30, "unreferenced"⟩]
def tracks : List Track := [⟨1, 5, 3⟩, ⟨2, 5, 3⟩, ⟨1, 7, 4⟩]

def records [Codec α] (xs : List α) : Relation := xs.filterMap fun x =>
  match Codec.encode x with | .record r => some r | _ => none

def database : Database := [("people", records people), ("teams", records teams), ("tracks", records tracks)]

def adults (minimum : Int) := query% [ (p.name, p.age + 1) | p : Person ← table, p.age ≥ minimum ]
def peopleView := View.base (@table Person _)
def adultsView := peopleView.select (fun p => p.age ≥ 18)
def briefView := peopleView.project (@table Brief _) [("age", .int 0), ("teamId", .int 10), ("note", .null)]
def joinedView := peopleView.join (View.base (@table Team _))

end LeanRel.Tests
