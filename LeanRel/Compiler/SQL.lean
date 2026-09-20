import LeanRel.Schema
import LeanRel.Frontend.Syntax
import LeanRel.SQL.Ast

/-! SQL is an optional consumer of elaborated Lean queries. This module is the only
place where the frontend and SQL meet. Native functions remain usable by the reference
interpreter even when this compiler has no translation for them. -/
namespace LeanRel.Compiler.SQL
open Lean Meta Elab Term

initialize registerTraceClass `LeanRel.sql

structure FunctionRule where
  function : Name
  sqlName : String
  arity : Nat
  deriving Inhabited

/-- Rules follow Lean's global/local/scoped attribute semantics, including when
the marked function was imported. The most recently activated rule takes precedence. -/
initialize functionRules : SimpleScopedEnvExtension FunctionRule (NameMap FunctionRule) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun rules rule => rules.insert rule.function rule
  }

/-- Declare the SQL interpretation of a native scalar function. -/
syntax (name := sql_function) &"sql_function " str num : attr

-- ParametricAttribute rejects imported declarations, but users must be able to
-- write `attribute [sql_function "LOWER" 1] String.toLower` in an adapter module.
initialize
  registerBuiltinAttribute {
    name := `sql_function
    descr := "translate a native scalar function to a SQL function call"
    add := fun decl stx kind => do
      let `(attr| sql_function $sql:str $arity:num) := stx | throwUnsupportedSyntax
      functionRules.add ⟨decl, sql.getString, arity.getNat⟩ kind
  }

private inductive Binding where
  | scalar (code : Lean.Expr)
  | record (fields : List (String × Binding))
  | collection (code : Lean.Expr) (element : Binding)
  deriving Inhabited

private abbrev Bindings := List (FVarId × Binding)
private abbrev CompileM := StateT Nat TermElabM

private def guarded {α} (action : CompileM α) : CompileM α := fun s => withIncRecDepth (action s)

private structure Plan where
  value : Binding
  from_ : Option Lean.Expr := none
  predicates : List Lean.Expr := []
  order : List (Lean.Expr × Lean.Expr) := []
  distinct : Bool := false
  limit : Option Lean.Expr := none
  offset : Option Lean.Expr := none
  deriving Inhabited

private def exprType := Lean.mkConst ``LeanRel.SQL.Expr
private def sourceType := Lean.mkConst ``LeanRel.SQL.Source
private def option (type : Lean.Expr) : Option Lean.Expr → CompileM Lean.Expr
  | none => pure (mkApp (Lean.mkConst ``Option.none [0]) type)
  | some e => mkAppM ``Option.some #[e]
private def list (type : Lean.Expr) (xs : List Lean.Expr) : CompileM Lean.Expr := mkListLit type xs
private def pair (a b : Lean.Expr) : CompileM Lean.Expr := mkAppM ``Prod.mk #[a, b]
private def pairType (a b : Lean.Expr) := mkApp2 (Lean.mkConst ``Prod [0, 0]) a b
private def alias : CompileM String := do
  let n ← get
  modify (· + 1)
  return s!"q{n}"
private def col (table name : String) : CompileM Lean.Expr :=
  mkAppM ``LeanRel.SQL.Expr.column #[toExpr [table, name]]
private def boolean (b : Bool) : CompileM Lean.Expr :=
  mkAppM ``LeanRel.SQL.Expr.boolean #[toExpr b]
private def binary (op : Name) (a b : Lean.Expr) : CompileM Lean.Expr :=
  mkAppM ``LeanRel.SQL.Expr.binary #[Lean.mkConst op, a, b]
private def unary (op : Name) (a : Lean.Expr) : CompileM Lean.Expr :=
  mkAppM ``LeanRel.SQL.Expr.unary #[Lean.mkConst op, a]
private def conjunction (xs : List Lean.Expr) : CompileM Lean.Expr := do
  match xs with
  | [] => boolean true
  | x :: xs => xs.foldlM (binary ``LeanRel.SQL.BinOp.and) x

private partial def leaves : Binding → List Lean.Expr
  | .scalar e => [e]
  | .record fields => (fields.map fun (_, v) => leaves v).flatten
  | .collection e _ => [e]

private partial def collectionColumns : Binding → List Bool
  | .scalar _ => [false]
  | .collection _ _ => [true]
  | .record fields => (fields.map fun (_, v) => collectionColumns v).flatten

private partial def rebind (table : String) (b : Binding) : StateT Nat CompileM Binding := do
  match b with
  | .scalar _ =>
    let n ← get
    modify (· + 1)
    return .scalar (← col table s!"c{n}")
  | .record fs => return .record (← fs.mapM fun (n, v) => return (n, ← rebind table v))
  | .collection _ element =>
    let n ← get
    modify (· + 1)
    return .collection (← col table s!"c{n}") element

private def scalar (b : Binding) : CompileM Lean.Expr :=
  match b with
  | .scalar e => pure e
  | _ => throwError "SQL scalar expression expected; a record or collection was provided"

private def field (b : Binding) (name : String) : CompileM Binding := do
  match b with
  | .record fs =>
    match fs.lookup name with
    | some value => return value
    | none => throwError "unknown compiled field {name}"
  | _ => throwError "field {name} is not a compiled record field"

private def emit (p : Plan) (includeOrderColumns := false) : CompileM Lean.Expr := do
  let mut cols ← (leaves p.value).zipIdx |>.mapM fun (e, i) => do
    pair e (← option (Lean.mkConst ``String) (some (toExpr s!"c{i}")))
  if includeOrderColumns then
    cols := cols ++ (← p.order.zipIdx.mapM fun ((e, _), i) => do
      pair e (← option (Lean.mkConst ``String) (some (toExpr s!"o{i}"))))
  if cols.isEmpty then throwError "SQL cannot return an empty record"
  let columns ← list (pairType exprType (mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``String))) cols
  let order ← p.order.mapM fun (e, d) => pair e d
  let predicate ← if p.predicates.isEmpty then pure none else some <$> conjunction p.predicates
  let s ← mkAppM ``LeanRel.SQL.Select.mk #[
    columns, toExpr p.distinct, ← option sourceType p.from_,
    ← option exprType predicate,
    ← list exprType [], ← option exprType none,
    ← list (pairType exprType (Lean.mkConst ``Bool)) order,
    ← option (Lean.mkConst ``Nat) p.limit, ← option (Lean.mkConst ``Nat) p.offset]
  mkAppM ``LeanRel.SQL.Query.select #[s]

private def collectPlan (p : Plan) : CompileM Binding := do
  if p.distinct && !p.order.isEmpty then
    throwError "place sortBy after distinct when collecting ordered results"
  let columns := (collectionColumns p.value).zipIdx.map fun (nested, i) => (s!"c{i}", nested)
  let order ← p.order.zipIdx.mapM fun ((_, desc), i) => pair (toExpr s!"o{i}") desc
  let code ← mkAppM ``LeanRel.SQL.Expr.collection #[← emit p true, toExpr columns,
    ← list (pairType (Lean.mkConst ``String) (Lean.mkConst ``Bool)) order]
  return .collection code p.value

private def materialize (p : Plan) (lateral := false) : CompileM Plan := do
  if p.distinct && !p.order.isEmpty then
    throwError "SQL lowering of ordered DISTINCT needs an explicit ordering after distinct"
  let name ← alias
  let q ← emit p true
  let src ← mkAppM ``LeanRel.SQL.Source.subquery #[q, toExpr name, toExpr lateral]
  let value ← (rebind name p.value).run' 0
  let order ← p.order.zipIdx.mapM fun ((_, desc), i) => return (← col name s!"o{i}", desc)
  return {value, from_ := some src, order}

private def barrier (p : Plan) := p.distinct || p.limit.isSome || p.offset.isSome

private def combine (a b : Plan) : CompileM Plan := do
  let from_ ← match a.from_, b.from_ with
    | none, b => pure b
    | a, none => pure a
    | some a, some b => do
      let on_ ← option exprType none
      some <$> mkAppM ``LeanRel.SQL.Source.join #[Lean.mkConst ``LeanRel.SQL.JoinKind.cross, a, b, on_]
  return {b with from_, predicates := a.predicates ++ b.predicates, order := a.order ++ b.order}

private def depends (env : Bindings) (e : Lean.Expr) := e.hasAnyFVar fun id => env.any (·.1 == id)

-- These definitions freeze the standard dictionaries at this module's compile
-- time; an importing module's local instance must not silently change SQL semantics.
@[instance_reducible] private def intOrd : Ord Int := inferInstance
@[instance_reducible] private def natOrd : Ord Nat := inferInstance
@[instance_reducible] private def stringOrd : Ord String := inferInstance
@[instance_reducible] private def boolOrd : Ord Bool := inferInstance
private def floatLT (a b : Float) : Prop := a < b
private def floatLE (a b : Float) : Prop := a ≤ b
private def stringLT (a b : String) : Prop := a < b
private def stringLE (a b : String) : Prop := a ≤ b

private partial def standardOrd (type : Lean.Expr) : CompileM Lean.Expr := do
  let type ← whnf type
  if type.isConstOf ``Int then return Lean.mkConst ``intOrd
  if type.isConstOf ``Nat then return Lean.mkConst ``natOrd
  if type.isConstOf ``String then return Lean.mkConst ``stringOrd
  if type.isConstOf ``Bool then return Lean.mkConst ``boolOrd
  throwError "SQL sortBy currently supports standard Int, Nat, String, and Bool orderings"

private def requireLawfulEquality (type dictionary : Lean.Expr) : CompileM Unit := do
  let lawful := mkApp2 (Lean.mkConst ``LawfulBEq [0]) type dictionary
  unless (← synthInstance? lawful).isSome do
    throwError "SQL equality/distinct/groupBy requires LawfulBEq for the actual comparison instance"

private def requirePrimitive (e : Lean.Expr) (arity : Nat) (names : List Name) : CompileM Unit := do
  let args := e.getAppArgs
  let operation := mkAppN e.getAppFn (args.extract 0 (args.size - arity))
  for name in names do
    if ← isDefEq operation (Lean.mkConst name) then return
  throwError "SQL lowering cannot assume the semantics of this overloaded operation: {e.getAppFn}"

private partial def peel (e : Lean.Expr) : Lean.Expr :=
  match e.consumeMData.headBeta with
  | .letE _ _ value body _ => peel (body.instantiate1 value)
  | e => e

private def unfold (e : Lean.Expr) : CompileM Lean.Expr := do
  if let some e' ← unfoldDefinition? e (ignoreTransparency := true) then
    if e' != e then return e'
  let e' ← whnfCore e
  if e' != e then return e'
  throwError "SQL lowering has no rule for {e}. The native query is still valid; add a [sql_function] attribute or provide a translatable definition."

private partial def conditional (p : Lean.Expr) (a b : Binding) : CompileM Binding := do
  match a, b with
  | .scalar a, .scalar b =>
    let branches ← list (pairType exprType exprType) [← pair p a]
    return .scalar (← mkAppM ``LeanRel.SQL.Expr.caseWhen #[branches, b])
  | .record as_, .record bs =>
    if as_.map Prod.fst != bs.map Prod.fst then throwError "conditional record shapes disagree"
    return .record (← (as_.zip bs).mapM fun ((n, a), (_, b)) => return (n, ← conditional p a b))
  | _, _ => throwError "conditional result shapes disagree"

mutual
  private partial def value (env : Bindings) (expression : Lean.Expr) : CompileM Binding := do
    guarded do
      let e := peel expression
      trace[LeanRel.sql] "term: {e}"
      if let .fvar id := e then
        if let some b := env.lookup id then return b
      if let .proj type idx target := e then
        if depends env target then
          let names := getStructureFields (← getEnv) type
          return ← field (← value env target) names[idx]!.toString
      let fn := e.getAppFn.constName?.getD .anonymous
      let args := e.getAppArgs
      if fn == ``List.length && depends env args.back! then
        let .collection code _ ← value env args.back!
          | throwError "List.length requires a compiled collection"
        return .scalar (← mkAppM ``LeanRel.SQL.Expr.collectionLength #[code])
      if let some info ← getProjectionFnInfo? fn then
        if args.size > info.numParams && depends env args[info.numParams]! then
          let ctor ← getConstInfoCtor info.ctorName
          let names := getStructureFields (← getEnv) ctor.induct
          return ← field (← value env args[info.numParams]!) names[info.i]!.toString
      if fn == ``ite && args.size == 5 then
        return ← conditional (← scalar (← value env args[1]!))
          (← value env args[3]!) (← value env args[4]!)
      -- Records are decomposed before parameterization; their fields retain native types.
      let type ← whnf (← inferType e)
      let scalarInstance ← synthInstance? (mkApp (Lean.mkConst ``ColumnType) type)
      if scalarInstance.isNone then
        if let some info := getStructureInfo? (← getEnv) (type.getAppFn.constName?.getD .anonymous) then
          if info.fieldNames.isEmpty then throwError "SQL cannot return an empty structure"
          if let some (.ctorInfo ctor) := (← getEnv).find? fn then
            let fields ← info.fieldNames.toList.zipIdx.mapM fun (name, idx) => do
              return (name.toString, ← value env args[ctor.numParams + idx]!)
            return .record fields
          if depends env e then return ← value env (← unfold e)
          let fields ← info.fieldNames.toList.mapM fun name => do
            return (name.toString, ← value env (← mkProjection e name))
          return .record fields
      if !depends env e then
        let e ← if ← isProp e then mkDecide e else pure e
        let encoded ← mkAppM ``Codec.encode #[e]
        return .scalar (← mkAppM ``LeanRel.SQL.Expr.param #[encoded])
      if fn == ``decide then return ← value env args[0]!
      if fn == ``Bool.not || fn == ``Not then
        return .scalar (← unary ``LeanRel.SQL.UnOp.not (← scalar (← value env args.back!)))
      if fn == ``Neg.neg then
        requirePrimitive e 1 [``Int.neg, ``Float.neg]
        return .scalar (← unary ``LeanRel.SQL.UnOp.negate (← scalar (← value env args.back!)))
      if fn == ``HAdd.hAdd then requirePrimitive e 2 [``Int.add, ``Float.add]
      if fn == ``HSub.hSub then requirePrimitive e 2 [``Int.sub, ``Float.sub]
      if fn == ``HMul.hMul then requirePrimitive e 2 [``Int.mul, ``Float.mul]
      if fn == ``LT.lt then requirePrimitive e 2 [``Int.lt, ``Nat.lt, ``floatLT, ``stringLT]
      if fn == ``LE.le then requirePrimitive e 2 [``Int.le, ``Nat.le, ``floatLE, ``stringLE]
      if fn == ``BEq.beq then requireLawfulEquality args[0]! args[1]!
      let op := if fn == ``HAdd.hAdd then some ``LeanRel.SQL.BinOp.add
        else if fn == ``HSub.hSub then some ``LeanRel.SQL.BinOp.sub
        else if fn == ``HMul.hMul then some ``LeanRel.SQL.BinOp.mul
        else if fn == ``LT.lt then some ``LeanRel.SQL.BinOp.lt
        else if fn == ``LE.le then some ``LeanRel.SQL.BinOp.le
        else if fn == ``Bool.and || fn == ``And then some ``LeanRel.SQL.BinOp.and
        else if fn == ``Bool.or || fn == ``Or then some ``LeanRel.SQL.BinOp.or
        else if fn == ``Eq || fn == ``BEq.beq then some ``LeanRel.SQL.BinOp.nullSafeEq
        else none
      if let some op := op then
        let a := leaves (← value env args[args.size - 2]!)
        let b := leaves (← value env args.back!)
        if a.length != b.length then throwError "comparison result shapes disagree"
        if a.length != 1 && op != ``LeanRel.SQL.BinOp.nullSafeEq then throwError "scalar operands required"
        return .scalar (← conjunction (← (a.zip b).mapM fun (a, b) => binary op a b))
      if let some rule := (functionRules.getState (← getEnv)).find? fn then
        let args ← (args.toList.drop (args.size - rule.arity)).mapM fun a => do scalar (← value env a)
        return .scalar (← mkAppM ``LeanRel.SQL.Expr.call #[toExpr rule.sqlName, ← list exprType args, toExpr false])
      return ← value env (← unfold e)

  private partial def compile (env : Bindings) (expression : Lean.Expr) : CompileM Plan := do
    guarded do
      let e := peel expression
      trace[LeanRel.sql] "term: {e}"
      let fn := e.getAppFn.constName?.getD .anonymous
      let args := e.getAppArgs
      if fn == ``Frontend.Query.scan then
        let src := peel args.back!
        let rowType ← whnf args[0]!
        let some info := findSchema? (← getEnv) (rowType.getAppFn.constName?.getD .anonymous)
          | throwError "SQL scan requires a row type declared by schema, got {rowType}"
        let name ← alias
        let tableName ← mkAppM ``TableDef.name #[← mkAppM ``LeanRel.Source.definition #[src]]
        let from_ ← mkAppM ``LeanRel.SQL.Source.table #[← list (Lean.mkConst ``String) [tableName],
          ← option (Lean.mkConst ``String) (some (toExpr name))]
        let fs ← info.definition.columns.mapM fun c => return (c.name, Binding.scalar (← col name c.name))
        return {value := .record fs, from_ := some from_}
      if fn == ``Frontend.Query.pure then return {value := ← value env args.back!}
      if fn == ``Frontend.Query.empty then
        throwError "an empty query needs a surrounding conditional to determine its SQL result shape"
      if fn == ``Frontend.Query.bind then
        let mut left ← compile env args[2]!
        if barrier left then left ← materialize left (depends env args[2]!)
        withLocalDeclD `row args[0]! fun row => do
          let mut right ← compile ((row.fvarId!, left.value) :: env) (mkApp args[3]! row)
          if barrier right then right ← materialize right (depends ((row.fvarId!, left.value) :: env) (mkApp args[3]! row))
          combine left right
      else if fn == ``ite && args.size == 5 then
        let isEmpty (x : Lean.Expr) := (peel x).isAppOf ``Frontend.Query.empty
        if isEmpty args[4]! then
          let mut p ← compile env args[3]!
          if barrier p then p ← materialize p (depends env args[3]!)
          return {p with predicates := (← scalar (← value env args[1]!)) :: p.predicates}
        if isEmpty args[3]! then
          let mut p ← compile env args[4]!
          if barrier p then p ← materialize p (depends env args[4]!)
          return {p with predicates := (← unary ``LeanRel.SQL.UnOp.not (← scalar (← value env args[1]!))) :: p.predicates}
        if !depends env args[1]! then
          let a ← emit (← compile env args[3]!)
          let b ← emit (← compile env args[4]!)
          let q ← mkAppM ``ite #[args[1]!, a, b]
          let name ← alias
          let shape := (← compile env args[3]!).value
          return {value := ← (rebind name shape).run' 0, from_ := some (← mkAppM ``LeanRel.SQL.Source.subquery #[q, toExpr name, toExpr false])}
        throwError "row-dependent conditional queries require an empty branch or explicit union"
      else if fn == ``Frontend.Query.map then
        let mut p ← compile env args.back!
        if barrier p then p ← materialize p (depends env args.back!)
        withLocalDeclD `row args[0]! fun row => do
          return {p with value := ← value ((row.fvarId!, p.value) :: env) (mkApp args[2]! row)}
      else if fn == ``Frontend.Query.filter then
        let mut p ← compile env args[1]!
        if barrier p then p ← materialize p (depends env args[1]!)
        withLocalDeclD `row args[0]! fun row => do
          let predicate ← scalar (← value ((row.fvarId!, p.value) :: env) (mkApp args[2]! row))
          return {p with predicates := p.predicates ++ [predicate]}
      else if fn == ``Frontend.Query.take || fn == ``Frontend.Query.drop then
        let mut p ← compile env args[1]!
        if barrier p then p ← materialize p (depends env args[1]!)
        return if fn == ``Frontend.Query.take then {p with limit := some args[2]!}
          else {p with offset := some args[2]!}
      else if fn == ``Frontend.Query.distinct then
        requireLawfulEquality args[0]! args[1]!
        let mut p ← compile env args.back!
        if barrier p then p ← materialize p (depends env args.back!)
        if !p.order.isEmpty then throwError "place sortBy after distinct for portable SQL semantics"
        return {p with distinct := true}
      else if fn == ``Frontend.Query.sortBy then
        unless ← isDefEq args[2]! (← standardOrd args[0]!) do
          throwError "SQL sortBy cannot use a custom Ord instance"
        let mut p ← compile env args[3]!
        if barrier p then p ← materialize p (depends env args[3]!)
        withLocalDeclD `row args[1]! fun row => do
          let keys := leaves (← value ((row.fvarId!, p.value) :: env) (mkApp args[4]! row))
          return {p with order := keys.map (·, args[5]!) ++ p.order}
      else if fn == ``Frontend.Query.unionAll then
        let a ← compile env args[1]!
        let b ← compile env args[2]!
        if (leaves a.value).length != (leaves b.value).length then throwError "UNION shape mismatch"
        let q ← mkAppM ``LeanRel.SQL.Query.set #[Lean.mkConst ``LeanRel.SQL.SetOp.union, toExpr true, ← emit a, ← emit b]
        let name ← alias
        return {value := ← (rebind name a.value).run' 0, from_ := some (← mkAppM ``LeanRel.SQL.Source.subquery #[q, toExpr name, toExpr (depends env e)])}
      else if fn == ``Frontend.Query.count || fn == ``Frontend.Query.sum then
        let mut p ← compile env args.back!
        if barrier p then p ← materialize p
        let aggregate ← if fn == ``Frontend.Query.count then
            mkAppM ``LeanRel.SQL.Expr.call #[toExpr "COUNT", ← list exprType [← mkAppM ``LeanRel.SQL.Expr.star #[← option (Lean.mkConst ``String) none]], toExpr false]
          else do
            let sum ← mkAppM ``LeanRel.SQL.Expr.call #[toExpr "SUM", ← list exprType [← scalar p.value], toExpr false]
            let zero ← mkAppM ``LeanRel.SQL.Expr.param #[← mkAppM ``Value.int #[toExpr (0 : Int)]]
            mkAppM ``LeanRel.SQL.Expr.call #[toExpr "COALESCE", ← list exprType [sum, zero], toExpr false]
        let q ← emit {p with value := .scalar aggregate, order := []}
        return {value := .scalar (← mkAppM ``LeanRel.SQL.Expr.scalar #[q])}
      else if fn == ``Frontend.Query.any || fn == ``Frontend.Query.all then
        let mut p ← compile env args[1]!
        if barrier p then p ← materialize p
        withLocalDeclD `row args[0]! fun row => do
          let mut predicate ← scalar (← value ((row.fvarId!, p.value) :: env) (mkApp args[2]! row))
          if fn == ``Frontend.Query.all then predicate ← unary ``LeanRel.SQL.UnOp.not predicate
          let q ← emit {p with predicates := p.predicates ++ [predicate], order := []}
          let mut test ← mkAppM ``LeanRel.SQL.Expr.exists #[q]
          if fn == ``Frontend.Query.all then test ← unary ``LeanRel.SQL.UnOp.not test
          return {value := .scalar test}
      else if fn == ``Frontend.Query.collect then
        return {value := ← collectPlan (← compile env args.back!)}
      else if fn == ``Frontend.Query.groupBy then
        requireLawfulEquality args[0]! args[2]!
        let mut outer ← compile env args[3]!
        if barrier outer then outer ← materialize outer (depends env args[3]!)
        let key ← withLocalDeclD `row args[1]! fun row =>
          value ((row.fvarId!, outer.value) :: env) (mkApp args[4]! row)
        outer ← materialize {outer with value := key, distinct := true, order := []}
        let mut inner ← compile env args[3]!
        if barrier inner then inner ← materialize inner (depends env args[3]!)
        let innerKey ← withLocalDeclD `row args[1]! fun row =>
          value ((row.fvarId!, inner.value) :: env) (mkApp args[4]! row)
        let equality ← conjunction (← ((leaves outer.value).zip (leaves innerKey)).mapM fun (a, b) =>
          binary ``LeanRel.SQL.BinOp.nullSafeEq a b)
        let members ← collectPlan {inner with predicates := inner.predicates ++ [equality]}
        return {outer with value := .record [("fst", outer.value), ("snd", members)]}
      else return ← compile env (← unfold e)
end

syntax (name := lowerSQL) "sql% " term : term
syntax:max (name := sqlComprehension) "sql%" querySpec : term

private def lowerProgram (program : Syntax) (expected : Option Lean.Expr) : TermElabM Lean.Expr := do
  let e ← elabTerm program none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let result ← (do emit (← compile [] e)).run' 0
  if let some expected := expected then
    unless ← isDefEq (← inferType result) expected do throwError "sql% produces SQL.Query"
  return result

/-- Bake an existing Lean query definition or combinator expression into SQL. -/
@[term_elab lowerSQL]
def elabLowerSQL : TermElab := fun stx expected => do
  let `(sql% $program:term) := stx | throwUnsupportedSyntax
  lowerProgram program expected

/-- The same comprehension as `query%`, baked directly into SQL. -/
@[term_elab sqlComprehension]
def elabSQLComprehension : TermElab := fun stx expected => do
  let `(sql% $body:querySpec) := stx | throwUnsupportedSyntax
  lowerProgram (← liftMacroM (Frontend.expandQuerySpec body)) expected

end LeanRel.Compiler.SQL
