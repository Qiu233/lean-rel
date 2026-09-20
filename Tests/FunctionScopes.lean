import Tests.FunctionRules

open LeanRel LeanRel.Frontend LeanRel.Tests.FunctionRules

namespace LeanRel.Tests.FunctionScopes

private def usesCall (query : SQL.Query) (name : String) (arity : Nat) : Bool :=
  match query with
  | .select s => match s.columns with
    | [(.call fn args _, _)] => fn == name && args.length == arity
    | _ => false
  | _ => false

-- Importing LeanRel loads the standard namespace without activating its rules.
#guard_msgs (drop info) in
#check_failure sql% [r.text.toLower | r ← FunctionRow.table]
#guard_msgs (drop info) in
#check_failure sql% [nativeLower r.text | r ← FunctionRow.table]
#guard_msgs (drop info) in
#check_failure sql% [TextTranslations.nativeUpper r.text | r ← FunctionRow.table]
#guard_msgs (drop info) in
#check_failure sql% [fileOnlyUpper r.text | r ← FunctionRow.table]

#guard usesCall TextTranslations.insideNamespace "LOWER" 1
#guard usesCall fileLocalSQL "UPPER" 1

open TextTranslations in
def scopedLowerSQL := sql% [nativeLower r.text | r ← FunctionRow.table]

open scoped LeanRel.Tests.FunctionRules.TextTranslations in
def scopedUpperSQL := sql% [TextTranslations.nativeUpper r.text | r ← FunctionRow.table]

#guard usesCall scopedLowerSQL "LOWER" 1
#guard usesCall scopedUpperSQL "UPPER" 1

-- `open ... in` and an `open` in a section must not leak activation.
#guard_msgs (drop info) in
#check_failure sql% [nativeLower r.text | r ← FunctionRow.table]

section
open TextTranslations

#guard usesCall (sql% [nativeLower r.text | r ← FunctionRow.table]) "LOWER" 1

section
attribute [local sql_function "CUSTOM_LOWER" 1] nativeLower
#guard usesCall (sql% [nativeLower r.text | r ← FunctionRow.table]) "CUSTOM_LOWER" 1
end

-- Closing the inner section restores the active scoped rule.
#guard usesCall (sql% [nativeLower r.text | r ← FunctionRow.table]) "LOWER" 1
end

#guard_msgs (drop info) in
#check_failure sql% [nativeLower r.text | r ← FunctionRow.table]

section
@[local sql_function "UPPER" 1]
opaque sectionOnlyUpper (s : String) : String := s.toUpper

#guard usesCall (sql% [sectionOnlyUpper r.text | r ← FunctionRow.table]) "UPPER" 1
end

#guard_msgs (drop info) in
#check_failure sql% [sectionOnlyUpper r.text | r ← FunctionRow.table]

abbrev StandardResult := String × String × String × Nat × Nat × Int × Float × String

section
open LeanRel.SQL.Standard

def standardQuery : Query StandardResult := query% [
  (r.text.toLower, r.text.toUpper, r.text ++ "!", r.text.length,
   r.number.natAbs, r.number.sign, r.real.abs, r.optional.getD r.text)
  | r ← FunctionRow.table]
def standardSQL := sql% standardQuery
end

-- The library's standard rules obey the same scope boundaries.
#guard_msgs (drop info) in
#check_failure sql% [r.text.toLower | r ← FunctionRow.table]

open scoped LeanRel.SQL.Standard in
def standardScopedSQL := sql% [r.text.toUpper | r ← FunctionRow.table]

#guard usesCall standardScopedSQL "UPPER" 1

private def rows : List FunctionRow := [
  ⟨1, "Äb你好", -7, -2.5, none⟩,
  ⟨2, "", 0, 0.0, some ""⟩,
  ⟨3, "AbC", 42, 1.25, some "fallback"⟩]

def run : IO Unit := do
  let connection ← Backend.SQLite.connect ":memory:"
  let create ← IO.ofExcept (SQL.CreateTable.ofTable FunctionRow.schema)
  let insert ← IO.ofExcept sql! [INSERT INTO FunctionRow.table VALUES rows]
  let _ ← IO.ofExcept (← connection.execute [.createTable create, insert])
  let records := rows.filterMap fun row => match Codec.encode row with
    | .record fields => some fields
    | _ => none
  let database := [(FunctionRow.schema.name, records)]
  let expected ← IO.ofExcept (standardQuery.run database)
  let actual ← IO.ofExcept (← connection.query (α := StandardResult) standardSQL)
  unless actual == expected do throw (IO.userError "standard SQL functions disagree with native query")
  IO.println "ok: scoped standard functions, Unicode character length, numeric and nullable values"
  let lower ← IO.ofExcept (← connection.query (α := String) scopedLowerSQL)
  let upper ← IO.ofExcept (← connection.query (α := String) scopedUpperSQL)
  unless lower == rows.map (fun r => nativeLower r.text) &&
      upper == rows.map (fun r => TextTranslations.nativeUpper r.text) do
    throw (IO.userError "imported scoped SQL attributes failed")
  IO.println "ok: imported scoped attributes on existing and new declarations"
  for dialect in [SQL.Dialect.postgresql, .mysql] do
    let prepared ← IO.ofExcept (SQL.render dialect (.query standardSQL))
    unless prepared.sql.contains "CHAR_LENGTH(" do
      throw (IO.userError "standard string length must count characters, not bytes")
  IO.println "ok: standard character length rendering for PostgreSQL and MySQL"

end LeanRel.Tests.FunctionScopes
