import LeanRel.Compiler.SQL

/-! Common scalar translations, loaded by `import LeanRel` and activated with
`open LeanRel.SQL.Standard` or `open scoped LeanRel.SQL.Standard`.

These rules opt into database scalar semantics: case conversion follows the
database's locale, and integer/float operations retain its numeric limits.
Lean's case conversion is ASCII-only. `String.length` uses character length,
not byte length; SQLite's LENGTH stops at an embedded NUL.
-/
namespace LeanRel.SQL.Standard

attribute [scoped sql_function "LOWER" 1] String.toLower
attribute [scoped sql_function "UPPER" 1] String.toUpper
attribute [scoped sql_function "CONCAT" 2] String.append
attribute [scoped sql_function "CHAR_LENGTH" 1] String.length
attribute [scoped sql_function "ABS" 1] Int.natAbs Float.abs
attribute [scoped sql_function "SIGN" 1] Int.sign
attribute [scoped sql_function "COALESCE" 2] Option.getD

end LeanRel.SQL.Standard
