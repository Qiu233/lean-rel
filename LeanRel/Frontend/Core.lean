import LeanRel.Data

/-! Native, baked query requests. Query bodies are Lean functions, not a closed expression AST.
Interpreters/compilers may recognize these combinators without imposing their vocabulary on Lean.
-/
namespace LeanRel.Frontend

structure Query (α : Type) where
  run : Database → Except String (List α)

namespace Query

def pure (value : α) : Query α := ⟨fun _ => .ok [value]⟩
def empty : Query α := ⟨fun _ => .ok []⟩
def bind (q : Query α) (f : α → Query β) : Query β := ⟨fun db => do
  let rows ← q.run db
  return (← rows.mapM fun row => (f row).run db).flatten⟩
def map (f : α → β) (q : Query α) : Query β := q.bind (pure ∘ f)
def filter (q : Query α) (p : α → Bool) : Query α :=
  q.bind fun row => if p row then pure row else empty
def ofList (rows : List α) : Query α := ⟨fun _ => .ok rows⟩
def scan [Codec α] (source : Source α) : Query α := ⟨fun db => do
  let rows ← db.getTable source.definition.name
  source.definition.validateRows rows
  rows.mapM fun row => Codec.decode (.record row)⟩
def unionAll (left right : Query α) : Query α := ⟨fun db => do
  return (← left.run db) ++ (← right.run db)⟩
def distinct [BEq α] (q : Query α) : Query α := ⟨fun db => return (← q.run db).eraseDups⟩
def take (q : Query α) (n : Nat) : Query α := ⟨fun db => return (← q.run db).take n⟩
def drop (q : Query α) (n : Nat) : Query α := ⟨fun db => return (← q.run db).drop n⟩
def sortBy [Ord β] (q : Query α) (key : α → β) (descending := false) : Query α := ⟨fun db => do
  return (← q.run db).mergeSort fun a b =>
    if descending then compare (key b) (key a) != .gt else compare (key a) (key b) != .gt⟩
def count (q : Query α) : Query Int := ⟨fun db => return [Int.ofNat (← q.run db).length]⟩
def sum (q : Query Int) : Query Int := ⟨fun db => return [(← q.run db).foldl (· + ·) 0]⟩
def any (q : Query α) (p : α → Bool) : Query Bool := ⟨fun db => return [(← q.run db).any p]⟩
def all (q : Query α) (p : α → Bool) : Query Bool := ⟨fun db => return [(← q.run db).all p]⟩
def collect (q : Query α) : Query (List α) := ⟨fun db => return [← q.run db]⟩
def groupBy [BEq β] (q : Query α) (key : α → β) : Query (β × List α) := ⟨fun db => do
  let rows ← q.run db
  let keys := (rows.map key).eraseDups
  return keys.map fun k => (k, rows.filter fun row => key row == k)⟩

end Query

instance : Monad Query where
  pure := Query.pure
  bind := Query.bind
  map := Query.map

class ToQuery (source : Type) (element : outParam Type) where
  toQuery : source → Query element
instance [Codec α] : ToQuery (Source α) α := ⟨Query.scan⟩
instance : ToQuery (Query α) α := ⟨id⟩
instance : ToQuery (List α) α := ⟨Query.ofList⟩

end LeanRel.Frontend
