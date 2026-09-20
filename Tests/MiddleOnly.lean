-- This module deliberately imports neither the frontend nor its SQL adapter.
import LeanRel.Schema
import LeanRel.SQL.NativeSyntax

namespace LeanRel.Tests.MiddleOnly
open LeanRel
open scoped LeanRel.SQL

schema Item "items" { id : Int, title : String, enabled : Bool, bytes : Array UInt8 } key [id]

def reusable (i : Item.Columns SQL.Scalar) := i.enabled &&. (i.id >. 0)
def query := sql! [SELECT i FROM i IN Item.table WHERE reusable i]
def prepared := SQL.render .sqlite sql! [SELECT i.title FROM i IN Item.table WHERE reusable i]
def raw := SQL.render .sqlite sql! [SELECT title FROM items WHERE enabled = TRUE]
def fragment := sql_expr! [id > ${(3 : Int)}]
def composed := sql_query! [SELECT title FROM @{Item.schema} WHERE @{fragment}]

#guard_msgs (drop info) in
#check_failure sql! [SELECT i.missing FROM i IN Item.table]
#guard_msgs (drop info) in
#check_failure sql! [SELECT i.title + i.id FROM i IN Item.table]
#guard_msgs (drop info) in
#check_failure sql! [UPDATE i IN Item.table SET {i with id := "wrong"}]
#guard_msgs (drop info) in
#check_failure sql! [SELECT i.title FROM i IN Item.table WHERE i.id]
#guard_msgs (drop info) in
#check_failure i.title

/-- error: unknown key column: missing -/
#guard_msgs in
schema BadKey "bad" { id : Int } key [missing]

/-- error: duplicate schema field -/
#guard_msgs in
schema BadFields "bad" { id : Int, id : Int } key [id]

end LeanRel.Tests.MiddleOnly
