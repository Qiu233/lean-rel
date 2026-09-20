import LeanRel.SQL.Syntax
import LeanRel.SQL.Native

namespace LeanRel.SQL.Notation
open Lean

/-- Resolve schema instances before elaborating field projections in a callback.
The source type is known here, even when ordinary application elaboration has
not yet synthesized the implicit SchemaRow argument. -/
syntax:max (name := sqlFields) "sql_fields!" "(" term ")" "fun" ident "=>" term : term

open Elab Term Meta in
@[term_elab sqlFields]
def elabSqlFields : TermElab := fun stx expected => do
  let `(sql_fields! ($source:term) fun $row:ident => $body:term) := stx | throwUnsupportedSyntax
  let source ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let type ← whnf (← inferType (← instantiateMVars source))
  unless type.isAppOfArity ``LeanRel.Source 1 do throwError "expected a typed schema source"
  let α := type.getArg! 0
  let schemaInst ← synthInstance (mkApp (Lean.mkConst ``SchemaRow) α)
  let fields ← whnf (mkApp3 (Lean.mkConst ``SchemaRow.Fields) α schemaInst (Lean.mkConst ``Scalar))
  let fields ← exprToSyntax fields
  elabTerm (← `(fun ($row : $fields) => $body)) expected

-- Native terms, SQL clause order, and a lexical row binder. IN distinguishes a
-- typed Lean source from a literal SQL table name. No term rewriting is needed.
syntax nativeSqlJoin := "JOIN" ident "IN" term "ON" term
syntax:max (name := nativeSqlSelect) "sql!" "[" "SELECT" ("DISTINCT")? term
  "FROM" ident "IN" term nativeSqlJoin*
  ("WHERE" term)? ("GROUP" "BY" term)? ("HAVING" term)?
  ("ORDER" "BY" term)? ("LIMIT" term)? ("OFFSET" term)? "]" : term
syntax:max (name := nativeSqlInsert) "sql!" "[" "INSERT" "INTO" term "VALUES" term "]" : term
syntax:max (name := nativeSqlUpdate) "sql!" "[" "UPDATE" ident "IN" term
  "SET" term ("WHERE" term)? "]" : term
syntax:max (name := nativeSqlDelete) "sql!" "[" "DELETE" "FROM" ident "IN" term
  ("WHERE" term)? "]" : term

macro_rules
  | `(sql! [SELECT $[DISTINCT%$distinct]? $projection:term FROM $row:ident IN $source:term $[$joins:nativeSqlJoin]*
      $[WHERE $predicate:term]? $[GROUP BY $keys:term]? $[HAVING $having:term]?
      $[ORDER BY $order:term]? $[LIMIT $limit:term]? $[OFFSET $offset:term]?]) => do
    let mut body ← `(SQL.select $projection)
    if let some predicate := predicate then body ← `(Plan.where_ $predicate $body)
    if let some keys := keys then body ← `(Plan.groupBy $keys $body)
    if let some having := having then body ← `(Plan.having $having $body)
    if let some order := order then body ← `(Plan.orderBy $order $body)
    if distinct.isSome then body ← `(Plan.distinct $body)
    if let some limit := limit then body ← `(Plan.limit $limit $body)
    if let some offset := offset then body ← `(Plan.offset $offset $body)
    for join in joins.reverse do
      let `(nativeSqlJoin| JOIN $name:ident IN $table:term ON $condition:term) := join | Macro.throwUnsupported
      body ← `(SQL.fromTable $table (sql_fields! ($table) fun $name => Plan.where_ $condition $body))
    `(SQL.fromTable $source (sql_fields! ($source) fun $row => $body))
  | `(sql! [INSERT INTO $table:term VALUES $rows:term]) => `(SQL.insertRows $table $rows)
  | `(sql! [UPDATE $row:ident IN $table:term SET $change:term $[WHERE $predicate:term]?]) => do
    let predicate ← match predicate with
      | some p => pure p | none => `(SQL.param true)
    `(SQL.updateRows $table (sql_fields! ($table) fun $row => $change)
      (sql_fields! ($table) fun $row => $predicate))
  | `(sql! [DELETE FROM $row:ident IN $table:term $[WHERE $predicate:term]?]) => do
    let predicate ← match predicate with
      | some p => pure p | none => `(SQL.param true)
    `(SQL.deleteRows $table (sql_fields! ($table) fun $row => $predicate))

end LeanRel.SQL.Notation
