import LeanRel.Frontend.Core

namespace LeanRel.Frontend
open Lean Elab Term

declare_syntax_cat comprehension
syntax (name := compFor) "for " ident " in " term "; " comprehension : comprehension
syntax (name := compWhere) "where " term "; " comprehension : comprehension
syntax (name := compLet) "let " ident " := " term "; " comprehension : comprehension
syntax (name := compYield) "yield " term : comprehension
syntax (name := compYieldFrom) "yield* " term : comprehension

/-- Downstream libraries can add clauses by defining macros for `queryBody%`. -/
syntax (name := queryBody) "queryBody%{" comprehension "}" : term

declare_syntax_cat queryQualifier
syntax ident Parser.Term.leftArrow term : queryQualifier
syntax "let " ident " := " term : queryQualifier
syntax term : queryQualifier
declare_syntax_cat querySpec
syntax "{" comprehension "}" : querySpec
syntax "[" term " | " queryQualifier,* "]" : querySpec
syntax:max (name := queryTerm) "query%" querySpec : term
syntax (name := qualifierBody) "queryQualifier%[" queryQualifier "]" term : term

macro_rules
  | `(queryQualifier%[ $x:ident ← $src:term ] $body:term) =>
    `(Query.bind (ToQuery.toQuery $src) (fun $x => $body))
  | `(queryQualifier%[ let $x:ident := $v:term ] $body:term) => `(let $x := $v; $body)
  | `(queryQualifier%[ $p:term ] $body:term) => `(if $p then $body else Query.empty)

macro_rules
  | `(queryBody%{ for $x:ident in $src:term; $body:comprehension }) =>
    `(Query.bind (ToQuery.toQuery $src) (fun $x => queryBody%{ $body }))
  | `(queryBody%{ where $p:term; $body:comprehension }) =>
    `(if $p then queryBody%{ $body } else Query.empty)
  | `(queryBody%{ let $x:ident := $value:term; $body:comprehension }) =>
    `(let $x := $value; queryBody%{ $body })
  | `(queryBody%{ yield $value:term }) => `(Query.pure $value)
  | `(queryBody%{ yield* $value:term }) => `(ToQuery.toQuery $value)

/-- Shared expansion for the native and SQL entry points. Clauses still expand
through their public macro hooks, and all embedded expressions remain Lean terms. -/
def expandQuerySpec : TSyntax `querySpec → MacroM (TSyntax `term)
  | `(querySpec| { $body:comprehension }) => `(queryBody%{ $body })
  | `(querySpec| [ $value:term | $[$qualifiers:queryQualifier],* ]) => do
    let mut body ← `(Query.pure $value)
    for qualifier in qualifiers.reverse do
      body ← `(queryQualifier%[ $qualifier ] $body)
    return body
  | _ => Macro.throwUnsupported

/-- Elaborate native terms in their real Lean binder/expected-type context. -/
@[term_elab queryTerm]
def elabQuery : TermElab := fun stx expected => do
  let `(query% $body:querySpec) := stx | throwUnsupportedSyntax
  elabTerm (← liftMacroM (expandQuerySpec body)) expected

end LeanRel.Frontend
