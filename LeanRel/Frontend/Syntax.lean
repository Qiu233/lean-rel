import LeanRel.Frontend.Core
import LeanRel.Parser

namespace LeanRel.Frontend
open Lean Elab Term

declare_syntax_cat comprehension
syntax (name := compFor) &"for " ident (" : " term)? &" in " term "; " comprehension : comprehension
syntax (name := compWhere) &"where " term "; " comprehension : comprehension
syntax (name := compLet) &"let " ident " := " term "; " comprehension : comprehension
syntax (name := compYield) identDispatch(&"yield ") term : comprehension
syntax (name := compYieldFrom) "yield* " term : comprehension

/-- Downstream libraries can add clauses by defining macros for `queryBody%`. -/
syntax (name := queryBody) "queryBody%{" comprehension "}" : term

declare_syntax_cat queryQualifier
syntax ident (" : " term)? Parser.Term.leftArrow term : queryQualifier
syntax &"let " ident " := " term : queryQualifier
syntax (priority := low) term : queryQualifier
declare_syntax_cat querySpec
syntax "{" withoutForbidden(comprehension) "}" : querySpec
syntax "[" withoutForbidden(term " | " queryQualifier,*) "]" : querySpec
syntax:max (name := queryTerm) "query%" querySpec : term
syntax (name := qualifierBody) "queryQualifier%[" queryQualifier "]" term : term

private def queryLambda (x : Ident) (type : Option Term) (body : Term) : MacroM Term :=
  match type with
  | some type => `(fun ($x : $type) => $body)
  | none => `(fun $x => $body)

macro_rules
  | `(queryQualifier%[ $x:ident $[: $type:term]? ← $src:term ] $body:term) => do
    `(Query.bind (ToQuery.toQuery $src) $(← queryLambda x type body))
  | `(queryQualifier%[ let $x:ident := $v:term ] $body:term) => `(let $x := $v; $body)
  | `(queryQualifier%[ $p:term ] $body:term) => `(if $p then $body else Query.empty)

macro_rules
  | `(queryBody%{ for $x:ident $[: $type:term]? in $src:term; $body:comprehension }) => do
    `(Query.bind (ToQuery.toQuery $src) $(← queryLambda x type (← `(queryBody%{ $body }))))
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
