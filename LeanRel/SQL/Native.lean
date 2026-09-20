import LeanRel.SQL.Execute

/-! SQL builders are ordinary Lean values/functions. Schema-generated field
containers provide dot notation and record updates without string column lookup.
This layer depends on neither the rich frontend nor a database driver. -/
namespace LeanRel.SQL

abbrev Build := StateM Nat

structure Scalar (α : Type) where
  build : Build Expr

private def freshAlias : Build String := do
  let n ← get
  modify (· + 1)
  return s!"s{n}"

def param [Codec α] [ColumnType α] (value : α) : Scalar α := ⟨pure (.param (Codec.encode value))⟩

namespace Scalar

def column (name : Ident) : Scalar α := ⟨pure (.column name)⟩
private def binary (op : BinOp) (a : Scalar α) (b : Scalar β) : Scalar γ :=
  ⟨do return .binary op (← a.build) (← b.build)⟩
private def unary (op : UnOp) (a : Scalar α) : Scalar β :=
  ⟨do return .unary op (← a.build)⟩

def isNull (a : Scalar α) : Scalar Bool := unary .isNull a
def isNotNull (a : Scalar α) : Scalar Bool := unary .isNotNull a
def same (a b : Scalar α) : Scalar Bool := binary .nullSafeEq a b

def lower (a : Scalar String) : Scalar String :=
  ⟨do return .call "LOWER" [← a.build]⟩
def upper (a : Scalar String) : Scalar String :=
  ⟨do return .call "UPPER" [← a.build]⟩
def coalesce (a : Scalar (Option α)) (fallback : Scalar α) : Scalar α :=
  ⟨do return .call "COALESCE" [← a.build, ← fallback.build]⟩
def count (a : Scalar α) : Scalar Int := ⟨do return .call "COUNT" [← a.build]⟩
def sum (a : Scalar Int) : Scalar (Option Int) := ⟨do return .call "SUM" [← a.build]⟩
def avg (a : Scalar Int) : Scalar (Option Float) := ⟨do return .call "AVG" [← a.build]⟩

def asc (a : Scalar α) : Build (Expr × Bool) := do return (← a.build, false)
def desc (a : Scalar α) : Build (Expr × Bool) := do return (← a.build, true)

class Numeric (α : Type) : Prop where
instance : Numeric Int := ⟨⟩
instance : Numeric Float := ⟨⟩
instance [Numeric α] : Numeric (Option α) := ⟨⟩

instance [Numeric α] : Add (Scalar α) := ⟨binary .add⟩
instance [Numeric α] : Sub (Scalar α) := ⟨binary .sub⟩
instance [Numeric α] : Mul (Scalar α) := ⟨binary .mul⟩
instance [Numeric α] : Div (Scalar α) := ⟨binary .div⟩
instance [Numeric α] : Neg (Scalar α) := ⟨unary .negate⟩
instance : Append (Scalar String) := ⟨binary .concat⟩
instance (n : Nat) : OfNat (Scalar Int) n := ⟨param (Int.ofNat n)⟩
instance (n : Nat) : OfNat (Scalar Float) n := ⟨param n.toFloat⟩
instance (n : Nat) : OfNat (Scalar (Option Int)) n := ⟨param (some (Int.ofNat n))⟩
instance : Coe String (Scalar String) := ⟨param⟩
instance : Coe Bool (Scalar Bool) := ⟨param⟩
instance : Coe (Scalar α) (Scalar (Option α)) := ⟨fun a => ⟨a.build⟩⟩

/-- SQL comparison preserves three-valued truth for nullable operands. -/
class Comparison (α : Type) (truth : outParam Type) : Prop where
instance : Comparison Int Bool := ⟨⟩
instance : Comparison Float Bool := ⟨⟩
instance : Comparison String Bool := ⟨⟩
instance : Comparison Bool Bool := ⟨⟩
instance [Comparison α β] : Comparison (Option α) (Option Bool) := ⟨⟩

def eq [Comparison α β] (a b : Scalar α) : Scalar β := binary .eq a b
def ne [Comparison α β] (a b : Scalar α) : Scalar β := binary .ne a b
def lt [Comparison α β] (a b : Scalar α) : Scalar β := binary .lt a b
def le [Comparison α β] (a b : Scalar α) : Scalar β := binary .le a b
def gt [Comparison α β] (a b : Scalar α) : Scalar β := binary .gt a b
def ge [Comparison α β] (a b : Scalar α) : Scalar β := binary .ge a b

class Truth (α : Type) : Prop where
instance : Truth Bool := ⟨⟩
instance : Truth (Option Bool) := ⟨⟩
def and [Truth α] (a b : Scalar α) : Scalar α := binary .and a b
def or [Truth α] (a b : Scalar α) : Scalar α := binary .or a b
def not [Truth α] (a : Scalar α) : Scalar α := unary .not a

def choose [Truth β] (p : Scalar β) (yes no : Scalar α) : Scalar α :=
  ⟨do return .caseWhen [(← p.build, ← yes.build)] (← no.build)⟩

end Scalar

scoped infix:50 " ==. " => Scalar.eq
scoped infix:50 " !=. " => Scalar.ne
scoped infix:50 " <. " => Scalar.lt
scoped infix:50 " <=. " => Scalar.le
scoped infix:50 " >. " => Scalar.gt
scoped infix:50 " >=. " => Scalar.ge
scoped infixl:35 " &&. " => Scalar.and
scoped infixl:30 " ||. " => Scalar.or

/-- A typed SELECT builder; aliases and correlated subqueries share a fresh-name
supply. `query` bakes it into the public, database-independent SQL AST. -/
structure Plan (α : Type) where
  build : Build Select

class Projection (ρ : Type) (α : outParam Type) where
  columns : ρ → List (Build Expr)

instance : Projection (Scalar α) α := ⟨fun s => [s.build]⟩
instance [Projection ρ α] [Projection σ β] : Projection (ρ × σ) (α × β) :=
  ⟨fun (a, b) => Projection.columns a ++ Projection.columns b⟩
instance (priority := low) [RowFields ρ Scalar α] : Projection ρ α :=
  ⟨fun row => RowFields.fold (F := Scalar) row fun _ _ v => v.build⟩

def select [Projection ρ α] (projection : ρ) : Plan α := ⟨do
  let columns ← (Projection.columns projection).zipIdx.mapM fun (c, i) =>
    return (← c, some s!"c{i}")
  return {columns}⟩

abbrev Columns (α : Type) [SchemaRow α] := SchemaRow.Fields (α := α) Scalar

private def tableColumns [SchemaRow α] (alias : String) : Columns α :=
  SchemaRow.tabulate fun _ name => Scalar.column (if alias.isEmpty then [name] else [alias, name])

def fromTable [SchemaRow α] (source : LeanRel.Source α) (body : Columns α → Plan β) : Plan β := ⟨do
  let name ← freshAlias
  let result ← (body (tableColumns name)).build
  let table := Source.table [source.definition.name] (some name)
  let from_ := match result.from_ with
    | none => table
    | some other => .join .cross table other none
  return {result with from_ := some from_}⟩

namespace Plan

def query (p : Plan α) : Query := .select (p.build.run' 0)
def statement (p : Plan α) : Statement := .query p.query

def where_ [Scalar.Truth β] (predicate : Scalar β) (p : Plan α) : Plan α := ⟨do
  let result ← p.build
  let predicate ← predicate.build
  return {result with where_ := some (match result.where_ with
    | none => predicate | some old => .binary .and predicate old)}⟩

def groupBy [Projection ρ β] (keys : ρ) (p : Plan α) : Plan α := ⟨do
  let result ← p.build
  return {result with groupBy := ← (Projection.columns keys).mapM id}⟩

def having [Scalar.Truth β] (predicate : Scalar β) (p : Plan α) : Plan α := ⟨do
  let result ← p.build
  return {result with having := some (← predicate.build)}⟩

def orderBy (keys : List (Build (Expr × Bool))) (p : Plan α) : Plan α := ⟨do
  let result ← p.build
  return {result with orderBy := ← keys.mapM id}⟩

def distinct (p : Plan α) : Plan α := ⟨do return {← p.build with distinct := true}⟩
def limit (n : Nat) (p : Plan α) : Plan α := ⟨do return {← p.build with limit := some n}⟩
def offset (n : Nat) (p : Plan α) : Plan α := ⟨do return {← p.build with offset := some n}⟩

def exists_ (p : Plan α) : Scalar Bool := ⟨do return .exists (.select (← p.build))⟩

def fetch [Codec α] (p : Plan α) (connection : Connection) : IO (Except String (List α)) :=
  connection.query p.query

end Plan

instance : CoeOut (Plan α) Query := ⟨Plan.query⟩
instance : CoeOut (Plan α) Statement := ⟨Plan.statement⟩

/-- Encode complete native records in schema order. No repeated column/value lists. -/
def insertRows [Codec α] (source : LeanRel.Source α) (rows : List α) : Except String Statement := do
  let rows ← rows.mapM fun row => match Codec.encode row with
    | .record row => pure row
    | _ => throw "INSERT needs a schema record"
  source.definition.validateRows rows
  let values ← rows.mapM fun row => source.definition.names.mapM fun name =>
    Expr.param <$> Record.getField row name
  return .insert [source.definition.name] source.definition.names (.values values)

/-- A native record update produces assignments only for changed expressions. -/
def updateRows [SchemaRow α] [Scalar.Truth β]
    (source : LeanRel.Source α) (change : Columns α → Columns α)
    (predicate : Columns α → Scalar β) : Statement := Id.run do
  let build : Build Statement := do
    let alias ← freshAlias
    let row : Columns α := tableColumns alias
    let assignments ← (SchemaRow.fold (α := α) (F := Scalar) (change row) fun _ name expression => do
      return (name, ← expression.build)).mapM id
    let assignments := assignments.filter fun (name, expression) => match expression with
      | .column [qualifier, original] => qualifier != alias || name != original
      | _ => true
    return .update [source.definition.name] assignments (some (← (predicate row).build)) [] (some alias)
  return build.run' 0

def deleteRows [SchemaRow α] [Scalar.Truth β] (source : LeanRel.Source α)
    (predicate : Columns α → Scalar β) : Statement :=
  (do
    let alias ← freshAlias
    let condition ← (predicate (tableColumns alias)).build
    pure (Statement.delete [source.definition.name] (some condition) [] (some alias))).run' 0

end LeanRel.SQL
