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

end SyntaxRegression
