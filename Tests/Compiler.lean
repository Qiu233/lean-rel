import Tests.Schema

open LeanRel LeanRel.Frontend LeanRel.Tests

-- Native syntax remains valid, but an unsupported interpretation must never be
-- silently replaced by SQL's usual arithmetic/equality/ordering.
section
local instance : HAdd Int Int Int := ⟨Int.sub⟩
#guard_msgs (drop info) in
#check_failure sql% [p.age + 1 | p : Person ← table]
end

section
local instance : BEq Int := ⟨fun _ _ => true⟩
#guard_msgs (drop info) in
#check_failure sql% [p.age | p : Person ← table, p.age == 18]
#guard_msgs (drop info) in
#check_failure sql% (query% [p.age | p : Person ← table]).distinct
end

section
local instance : Ord Int := ⟨fun a b => compare b a⟩
#guard_msgs (drop info) in
#check_failure sql% (Query.scan (@table Person _)).sortBy (·.age)
end

#guard_msgs (drop info) in
#check_failure fun (opaqueRequest : Query Int) => sql% opaqueRequest

namespace SyntaxRegression

-- Importing the frontend must leave `query` available as an ordinary name.
def query (values : List Nat) := values.length
#guard query [1, 2, 3] == 3

-- Both comprehension entry points bind as tightly as an ordinary term argument.
def nativeArgument : Query String := id query% [p.name | p : Person ← table]
def sqlArgument : SQL.Query := id sql% [p.name | p : Person ← table]

-- DSL words remain usable as Lean declarations, parameters, and record fields.
def yield (SELECT : Nat) := SELECT + 1
def sql_function (WHERE : Nat) := yield WHERE
def keywordTerms (sql! sql_query! sql_expr! sql_fields! : Nat) :=
  sql! + sql_query! + sql_expr! + sql_fields!
#guard sql_function 2 == 3
#guard keywordTerms 1 2 3 4 == 10

abbrev PRIMARY := Int
schema KeywordFields "keyword_fields" (
  id (PRIMARY) PRIMARY KEY,
  yield Option String,
  SELECT Int
)
#guard (KeywordFields.mk 1 (some "value") 2).yield == some "value"
#guard (HasTable.schema KeywordFields).key == ["id"]
#guard ((query% { yield* [1, 2, 3] }).run []).toOption == some [1, 2, 3]
def yieldBinder := sql% { for yield : Person in table; yield yield.id }

open scoped LeanRel.SQL in
def keywordPlan (FROM : Source Person) (WHERE : Int) (LIMIT : Nat) := sql! [
  SELECT p.id FROM p IN (FROM) WHERE p.age >=. SQL.param (WHERE)
  ORDER BY [p.id.asc] LIMIT (LIMIT)]
#guard ((SQL.render .sqlite (keywordPlan (@table Person _) 18 2).statement).toOption.map
  (·.parameters)) == some #[.int 18]

-- Nested brackets reset the outer term's clause delimiters without parentheses.
open scoped LeanRel.SQL in
def nestedArgument := sql! [
  SELECT p.id FROM p IN @table Person _ WHERE SQL.Plan.exists_ sql! [
    SELECT q.id FROM q IN @table Person _ WHERE q.id ==. p.id]]
#guard (SQL.render .sqlite nestedArgument.statement).isOk

-- Literal and special-form parsing must win over the generic identifier parser;
-- escaped SQL identifiers still refer to columns with those names.
#guard ((SQL.render .sqlite sql! [SELECT NULL, TRUE, FALSE, CAST(1 AS INTEGER)]).toOption.map
  (·.sql)) == some "SELECT NULL, TRUE, FALSE, CAST(?1 AS BIGINT)"
#guard ((SQL.render .sqlite sql! [SELECT «NULL», «TRUE» FROM t]).toOption.map
  (·.sql)) == some "SELECT \"NULL\", \"TRUE\" FROM \"t\""
#guard (SQL.render .sqlite sql! [SELECT id FROM t
  WHERE name LIKE "A%" AND id IN (1, 2) OR note IS NULL
  UNION SELECT id FROM u]).isOk

end SyntaxRegression
