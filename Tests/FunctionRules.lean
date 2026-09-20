import LeanRel

namespace LeanRel.Tests.FunctionRules
open Frontend

schema FunctionRow "function_rows" {
  id : Int, text : String, number : Int, real : Float, optional : Option String
} key [id]

-- Opaque definitions make accidental unfolding unable to hide missing rules.
opaque nativeLower (s : String) : String := s.toLower
opaque fileOnlyUpper (s : String) : String := s.toUpper

namespace TextTranslations

attribute [scoped sql_function "LOWER" 1] nativeLower

@[scoped sql_function "UPPER" 1]
opaque nativeUpper (s : String) : String := s.toUpper

-- A scoped rule is active in its own namespace as well as when opened.
def insideNamespace := sql% [nativeLower r.text | r ← FunctionRow.table]

end TextTranslations
end LeanRel.Tests.FunctionRules

open LeanRel LeanRel.Frontend LeanRel.Tests.FunctionRules

-- Remains active at the end of this file, so the importer checks that local
-- entries are not serialized, rather than merely testing a section's `end`.
attribute [local sql_function "UPPER" 1] fileOnlyUpper

def LeanRel.Tests.FunctionRules.fileLocalSQL :=
  sql% [fileOnlyUpper r.text | r ← FunctionRow.table]
