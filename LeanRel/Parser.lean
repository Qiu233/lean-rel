import Lean

namespace LeanRel
open Lean Parser PrettyPrinter

/-- Register a non-reserved keyword in the identifier dispatch table as well.
The default dispatch used by commands, terms, and trailing Pratt parsers does not
look up identifier text, so `&"keyword"` alone is insufficient there. -/
def identDispatch (p : Parser) : Parser :=
  { p with info := { p.info with firstTokens := p.info.firstTokens.merge (.tokens ["ident"]) } }

@[combinator_parenthesizer identDispatch]
def identDispatch.parenthesizer (p : Parenthesizer) : Parenthesizer := p

@[combinator_formatter identDispatch]
def identDispatch.formatter (p : Formatter) : Formatter := p

initialize register_parser_alias identDispatch

end LeanRel
