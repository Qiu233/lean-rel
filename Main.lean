import LeanRel

open LeanRel LeanRel.Frontend
open scoped LeanRel.SQL

schema Person "people" (
  id Int PRIMARY KEY,
  name String NOT NULL,
  age Int
)

def adults (minimum : Int) := query% [
  (p.name, p.age + 1) | p : Person ← table, p.age ≥ minimum]

def adultsSQL (minimum : Int) := sql% [row | row ← adults minimum]

def eligible (minimum : Int) (p : Person.Columns SQL.Scalar) : SQL.Scalar Bool :=
  p.age >=. SQL.param minimum

def directSQL (minimum : Int) := sql! [
  SELECT (p.name, p.age + 1) FROM p IN @table Person _
  WHERE eligible minimum p ORDER BY [p.id.asc]]

def birthday := update [
  {p with age := p.age + 1} | p : Person ← View.base table, p.age ≥ 18]

def main : IO Unit := do
  let connection ← Backend.SQLite.connect ":memory:"
  let create ← IO.ofExcept (SQL.CreateTable.ofTable (HasTable.schema Person))
  let rows : List Person := [⟨1, "Ada", 30⟩, ⟨2, "Bo", 16⟩, ⟨3, "Chen", 25⟩]
  let insert ← IO.ofExcept sql! [INSERT INTO @table Person _ VALUES rows]
  let _ ← IO.ofExcept (← connection.execute [.createTable create, insert])
  let frontend ← IO.ofExcept (← connection.query (α := String × Int) (adultsSQL 18))
  let middle ← IO.ofExcept (← (directSQL 18).fetch connection)
  IO.println s!"comprehension → SQL: {repr frontend}"
  IO.println s!"direct SQL with Lean terms: {repr middle}"
  let prepared ← IO.ofExcept (SQL.render .sqlite (directSQL 18))
  IO.println prepared.sql
  IO.println s!"parameters: {repr prepared.parameters}"
  let _ ← IO.ofExcept (← Compiler.executeUpdate connection birthday)
  let after ← IO.ofExcept (← (sql! [SELECT p FROM p IN @table Person _ ORDER BY [p.id.asc]]).fetch connection)
  IO.println s!"after lens update: {repr after}"
