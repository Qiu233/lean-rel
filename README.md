# lean-rel

Native Lean queries and updates, with a SQL middle end that can also be used directly. The frontend is independent of SQL, and the SQL middle end connects to databases through a backend interface.

## Quick start

The project uses Lean 4.34.0, selected by `lean-toolchain`. A C compiler is required: [leanprover/leansqlite](https://github.com/leanprover/leansqlite/tree/v4.34.0) builds its bundled SQLite. From the repository root:

```sh
lake build
```

Save the following as `QuickStart.lean` in the repository root. It declares a schema, inserts records, runs a comprehension as SQL, and updates a view:

```lean
import LeanRel

open LeanRel LeanRel.Frontend LeanRel.SQL.Standard
open scoped LeanRel.SQL

schema Person "people" (
  id Int PRIMARY KEY,
  name String NOT NULL,
  age Int
)

def adultNames (minimum : Int) := sql% [
  p.name.toLower | p : Person ← table, p.age ≥ minimum]

def increaseAges := update% [
  {p with age := p.age + 1} | p : Person ← View.base table, p.age ≥ 18]

def main : IO Unit := do
  let connection ← Backend.SQLite.connect ":memory:"
  let create ← IO.ofExcept (SQL.CreateTable.ofTable (HasTable.schema Person))
  let rows : List Person := [⟨1, "Ada", 30⟩, ⟨2, "Bo", 16⟩, ⟨3, "Chen", 25⟩]
  let insert ← IO.ofExcept sql! [INSERT INTO @table Person _ VALUES rows]
  let _ ← IO.ofExcept (← connection.execute [.createTable create, insert])

  let names ← IO.ofExcept (← connection.query (α := String) (adultNames 18))
  IO.println s!"Adult names: {repr names}"

  let _ ← IO.ofExcept (← Compiler.executeUpdate connection increaseAges)
  let after ← IO.ofExcept (← (sql! [
    SELECT (p.name, p.age) FROM p IN @table Person _ ORDER BY [p.id.asc]
  ]).fetch connection)
  IO.println s!"After update: {repr after}"

#eval main
```

Run it with:

```sh
lake lean QuickStart.lean
```

The standard translation namespace makes `String.toLower` compile to SQL `LOWER`. `query%` builds requests for the native reference interpreter, `sql%` compiles frontend queries to SQL, and `sql!` constructs SQL directly.

The repository also includes a [demo](Main.lean) and [integration tests](Tests/Main.lean) that execute against SQLite:

```sh
lake exe lean-rel
lake test
```

The examples below continue from the imports and `Person` declaration in the quick start. Standard translations are enabled by default in these examples. The library API is still evolving.

## Schema: Lean records and metadata from one declaration

The `schema Person` command above generates:

- An ordinary `Person` structure, supporting field access, pattern matching, and record updates such as `{p with age := ...}`.
- `Codec Person` and `HasTable Person` instances. The ordinary function `table` obtains the default `Source Person` from its instance.
- A field container `Person.Columns F`, with fields such as `F Int` and `F String`. It is independent of SQL.
- Persistent elaborator metadata that remains available after importing a compiled module.

Declarations use SQL-style column lists and constraints, while field types are arbitrary Lean terms. Type aliases and custom `ColumnType`/`Codec` instances are supported. Built-in column mappings include `Int`, `Float`, `Bool`, `String`, `Array UInt8`, and `Option` of these types.

Nullability follows the Lean type: `String` is non-nullable, and `Option String` is nullable. An explicit `NOT NULL` is optional for non-nullable types and is rejected on nullable types. A primary key can follow a single column or use a table constraint such as `PRIMARY KEY (a, b)`. Only one primary key is allowed, and its columns must be non-nullable. Omitting it creates a source without a key; base views require a key for lens updates.

`table` is the exported name of `HasTable.table`. Its row type can be inferred from context; use `@table Person _` when it must be explicit. Lean synthesizes the instance argument represented by `_`. `HasTable.schema Person` obtains the `TableDef` from the same instance. A local `HasTable Person` instance can replace the default source without adding `Person.table` or `Person.schema` declarations.

The field name `table` is rejected, ignoring case, because `TABLE` is a reserved SQL word. `schema` is non-reserved in SQL:2023 and can be used as a field name. See the [SQL keyword comparison](https://www.postgresql.org/docs/current/sql-keywords-appendix.html).

Additional functional dependencies are configured on a source for relational lens validation and propagation:

```lean
schema Track "tracks" (
  album Int, track Int, rating Int,
  PRIMARY KEY (album, track)
)

def tracksSource := (@table Track _).withDependencies [⟨["track"], ["rating"]⟩]
def tracksView := View.base tracksSource
```

SQL includes functional dependencies, for example in feature T301 for grouped queries, but does not have this library's former `dependencies { ... }` table declaration clause. Dependencies implied by the primary key are derived automatically; `Source.withDependencies` adds further dependencies. See [MySQL's description of T301](https://dev.mysql.com/doc/dev/mysql-server/latest/group__AGGREGATE__CHECKS.html) and the [CREATE TABLE grammar](https://www.postgresql.org/docs/current/sql-createtable.html).

`HasTable.schema Person` is also an ordinary runtime value. `SQL.CreateTable.ofTable (HasTable.schema Person)` builds the SQL table definition. Additional functional dependencies are checked by native queries and lenses; they do not generate database constraints or triggers.

SQL type support is incomplete. Having `DECIMAL`, `DATE`, or `TIMESTAMP` in the middle end's AST does not yet provide the corresponding typed schema and codec. The [SQL type coverage notes](docs/sql-types.md) document these gaps and the current numeric width mappings.

## Comprehensions with Lean terms

```lean
def adults (minimum : Int) := query% [
  (p.name, p.age + 1) | p : Person ← table, p.age ≥ minimum]

def bonus (age : Int) : Int := if age ≥ 18 then age + 2 else age

def computed := query% [
  (p.name, bonus p.age) |
  p : Person ← table,
  let eligible := p.age ≥ 18,
  eligible]

def adultsSQL (minimum : Int) := sql% [
  (p.name, p.age + 1) | p : Person ← table, p.age ≥ minimum]
```

Generators accept `Source α`, `Query α`, ordinary `List α`, and `View α`. Both `←` and `<-` use Lean's arrow parser. Results, sources, `let` bindings, and predicates are native terms: Lean elaborates functions, closures, `match`, records, and existing macros.

The generator annotation `: Person` is optional. It can supply the row type to a polymorphic source, as in `p : Person ← table`. When the source or result context already determines the type, it can be omitted:

```lean
def allPeople : Query Person := query% [p | p ← table]
def knownSource := query% [p.name | p ← @table Person _]
```

Annotations become ordinary Lean lambda parameter types. Type inference is handled by Lean itself. Block queries and update comprehensions support the same optional annotations.

`query% [...]` produces a native `Query α`. `sql% [...]` consumes the same comprehension syntax and produces an independent `SQL.Query`. Both can appear directly as function arguments, and `query` remains available as an ordinary identifier. Existing queries and combinator expressions can also be compiled with forms such as `sql% adults minimum`.

`Query α` stores an executable request. Its `run : Database → Except String (List α)` supplies the reference semantics. Query bodies remain Lean programs, without a separate closed AST of frontend scalar expressions. The SQL adapter inspects the elaborated program; captured parameters are still evaluated and bound at runtime.

Query combinators include `map`, `filter`, `unionAll`, `distinct`, `sortBy`, `take`, `drop`, `count`, `sum`, `any`, `all`, `collect`, and `groupBy`:

```lean
def grouped := (Query.scan (@table Person _)).groupBy (fun p => p.age)
def groupedSQL := sql% grouped

def names := (query% [p.name | p : Person ← table]).collect
```

`collect` produces a collection value and supports correlated nested queries. The current SQL adapter uses nested collection expressions with JSON aggregation and decoding to retrieve the nested result in one query.

Comprehension clauses can be extended through macros:

```lean
syntax &"unless " term : queryQualifier
macro_rules
  | `(queryQualifier%[ unless $p:term ] $body:term) =>
    `(if $p then Query.empty else $body)
```

The block forms `query% { for p : Person in table; where ...; yield ... }` and `sql% { ... }` share the `queryBody%` extension point.

## Standard and custom scalar translations

`import LeanRel` loads the scoped rules in `LeanRel.SQL.Standard`. The quick start opens that namespace, enabling common scalar translations throughout the examples:

```lean
open LeanRel.SQL.Standard

def normalizedNames := sql% [(p.name.toLower, p.name.length) | p : Person ← table]
```

You can also use `open scoped LeanRel.SQL.Standard`, or restrict activation to one declaration with `open LeanRel.SQL.Standard in`. Importing `LeanRel` alone does not activate the rules, and an imported module's `open` does not propagate to its importers.

| Lean function | SQL translation |
| --- | --- |
| `String.toLower` / `String.toUpper` | `LOWER` / `UPPER` |
| `String.append` (`++`) | `CONCAT` |
| `String.length` | `CHAR_LENGTH`, rendered as `LENGTH` on SQLite |
| `Int.natAbs` / `Float.abs` | `ABS` |
| `Int.sign` | `SIGN` |
| `Option.getD` | `COALESCE` |

Custom translations use Lean's ordinary attribute scope syntax:

```lean
namespace MyTranslations
attribute [scoped sql_function "LOWER" 1] String.toLower

@[scoped sql_function "LOWER" 1]
def lowerName (name : String) : String := name.toLower
end MyTranslations

open LeanRel.SQL.Standard MyTranslations in
def customNames := sql% [lowerName p.name | p : Person ← table]

section
attribute [local sql_function "LOWER" 1] String.toLower
def localNames := sql% [p.name.toLower | p : Person ← table]
end
```

Scoped rules persist through `.olean` files and activate inside their namespace or when it is opened. Local rules follow Lean's section and namespace boundaries; a rule declared at the top level lasts until the end of the file and is not exported. Without a scope modifier, `[sql_function "LOWER" 1]` registers a global rule that activates on import. The most recently registered or activated rule for a function takes precedence, and leaving a local scope restores the outer rules.

The numeric argument specifies how many trailing function arguments are passed to SQL, excluding earlier implicit type parameters. The rules affect SQL compilation; native `query%` evaluation still calls the Lean function.

Standard translations opt into database scalar semantics. Lean 4.34.0 case conversion handles ASCII, while a database may convert more characters according to its locale. SQLite's `LENGTH` stops at an embedded NUL, and numeric operations retain database limits. See [Lean's string implementation](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/String/Modify.lean), [SQLite scalar functions](https://www.sqlite.org/lang_corefunc.html), and [PostgreSQL string functions](https://www.postgresql.org/docs/current/functions-string.html).

## The SQL middle end: reusable Lean definitions

The middle end can be used independently of the frontend compiler. `sql!` constructs SQL directly, with column types participating in Lean elaboration:

```lean
def eligible (minimum : Int) (p : Person.Columns SQL.Scalar) : SQL.Scalar Bool :=
  p.age >=. SQL.param minimum

def direct (minimum : Int) := sql! [
  SELECT (p.name, p.age + 1)
  FROM p IN @table Person _
  WHERE eligible minimum p
  ORDER BY [p.id.asc]]
```

`FROM p IN source` binds the generated field container. Field access, ordinary functions, tuples, and record updates reuse the schema's column names and types. `direct` has type `SQL.Plan (String × Int)`; `.fetch connection` executes it and decodes the result. `.query` and `.statement` expose the public AST, with coercions available when those types are expected.

DSL keywords remain ordinary Lean identifiers outside the DSL. Inside `sql!`, clause words delimit unparenthesized Lean terms; parentheses allow them as values, for example `LIMIT (LIMIT)` when a Lean parameter is named `LIMIT`.

Arithmetic uses Lean's `+ - * /`, and string concatenation uses `++`. Comparisons and logical operations use `==. !=. <. <=. >. >=. &&. ||.` to construct SQL expressions. Nullable comparisons retain `Option Bool`; `.isNull`, `.isNotNull`, and `.coalesce` provide explicit NULL operations.

Queries support typed `JOIN ... IN ... ON ...` sources, Lean projections and predicates, grouping, ordering, and pagination. Predicates, projections, ordering keys, and queries can be ordinary reusable definitions. Correlated subqueries use `.exists_`; composition shares an alias supply.

```lean
def birthdays := sql! [
  UPDATE p IN @table Person _
  SET {p with age := p.age + 1}
  WHERE eligible 18 p]

def removeChildren := sql! [DELETE FROM p IN @table Person _ WHERE p.age <. 18]

-- Returns Except String SQL.Statement, checking record encoding and keys.
def insertPeople (rows : List Person) := sql! [INSERT INTO @table Person _ VALUES rows]
```

Inserts reuse complete Lean records and schema column order. Updates derive changed assignments from record updates. These operations produce SQL DML directly, without relational lens propagation.

`sql! [...]` can appear as a function argument without extra parentheses:

```lean
def prepared := SQL.render .sqlite sql! [
  SELECT p.name FROM p IN @table Person _ WHERE eligible 18 p]
```

## The SQL middle end: SQL statement syntax

SQL-specific constructs can also be expressed directly and composed with existing terms:

```lean
def minimumAge : Int := 18
def predicate := sql_expr! [age >= ${minimumAge}]
def queryPart := sql_query! [
  SELECT name FROM @{HasTable.schema Person} WHERE @{predicate}]
def statement := sql! [
  WITH grown AS (@{queryPart}) SELECT name FROM grown ORDER BY name]
```

In this form, `sql!` returns `SQL.Statement`, `sql_query!` returns `SQL.Query`, and `sql_expr!` returns `SQL.Expr`. `${term}` encodes a bound parameter. `@{term}` splices the corresponding kind of AST; a `FROM` source can also splice a `TableDef`.

The syntax covers SELECT/DISTINCT, joins and outer joins, WHERE, GROUP BY/HAVING, ordering, pagination, set operations, correlated subqueries, CTEs and recursive CTEs, CASE, CAST, IN/EXISTS, window expressions, INSERT VALUES/SELECT, UPDATE, DELETE, RETURNING, table definitions and constraints, indexes, views, DROP TABLE, and transaction control ASTs. SQL function names can be used directly without registering each function in a fixed vocabulary.

Strings use Lean's double-quoted literals, and identifiers use Lean identifiers. Dynamic values should use parameter interpolation. DDL constants that cannot be bound are escaped by the renderer. This syntax preserves SQL structure, but does not statically prove that raw column names or grouping rules are valid. The public AST is also available for direct construction.

Applications using only the middle end can import `LeanRel.Schema` and `LeanRel.SQL.NativeSyntax`. [Tests/MiddleOnly.lean](Tests/MiddleOnly.lean) checks this dependency boundary and field/type errors.

## Relational lenses and updates

```lean
def people := View.base (@table Person _)
def adultsView := people.select (fun p => p.age ≥ 18)
def birthday := update% [
  {p with age := p.age + 1} | p ← people, p.age ≥ 18]
```

An update guard selects rows to change and preserves the others. A generator can also use `p : Person ← View.base table` directly. Each update comprehension currently binds one view; compose views first for updates involving multiple tables.

Views support base tables, selection, projection that retains the key, renaming, and natural joins with deletion policies. Projection recovers hidden fields from existing rows and requires defaults for new keys. Selection uses functional dependencies to revise hidden rows. A join requires shared fields to determine the right side; deletion defaults to the left side and can use `.right` or `.both`. Updates through views with overlapping source ownership are rejected.

```lean
-- Inside an IO do block:
-- let connection ← Backend.SQLite.connect ":memory:"
-- let _ ← IO.ofExcept (← Compiler.executeUpdate connection birthday)
```

`Compiler.executeUpdate` reads a consistent snapshot of the participating sources, computes the update in Lean, and generates DML that identifies rows by their keys. Before committing, a write transaction verifies the snapshot and expected affected row counts. Snapshot changes, including concurrent inserts, return a conflict; failures roll back the whole batch. Use `request.run database` to inspect changes locally, or `Compiler.applyUpdate` to apply an update against a supplied snapshot.

This is a partial lens implementation with runtime checks. It rejects changes that violate keys, functional dependencies, or selection predicates, and checks PutGet after successful propagation. Arbitrary Lean predicates do not automatically yield total lenses. [LeanRel/Lens/Laws.lean](LeanRel/Lens/Laws.lean) proves identity and composition laws for abstract total lenses; it does not prove all the concrete relational algorithms correct.

## Backend interface

Backends implement [`SQL.Connection`](LeanRel/SQL/Execute.lean). It accepts two functions:

- `render : SQL.Statement → Except String SQL.Prepared` translates the public SQL AST to SQL text and bound parameters, or reports an unsupported operation.
- `run : SQL.Batch → IO (Except String (List SQL.ResultSet))` executes the batch atomically, including snapshot checks and expected affected row counts.

A backend can supply its own implementations directly:

```lean
def customConnection
    (render : SQL.Statement → Except String SQL.Prepared)
    (run : SQL.Batch → IO (Except String (List SQL.ResultSet))) : SQL.Connection :=
  { render, run }
```

Query execution and lens updates use these functions. `SQL.Connection` does not require a backend name or a `Dialect` value. A new database driver can provide a renderer and batch runner without modifying the frontend or query compiler. Its runner must enforce the transaction and isolation contract described by `SQL.Batch`.

The shared `SQL.render` helper currently uses a closed `SQL.Dialect` enum containing SQLite, PostgreSQL, and MySQL. These are the bundled renderers, not a restriction on which backends can implement `SQL.Connection`. A custom backend can use a separate renderer. Extending the shared renderer to another dialect currently requires changing its implementation; its dialect rules are not yet an independently extensible interface.

SQLite execution uses native leansqlite bindings and a persistent connection, including for `:memory:` databases. A mutex serializes whole transactions, and lens writes use `BEGIN IMMEDIATE`. `Connection.execute` manages transactions, so transaction control statements should not be included in its batches.

SQLite has a connection driver and integration tests. PostgreSQL and MySQL currently have rendering tests, but no bundled connection drivers or live server tests.

## Current limitations

- Native queries can evaluate arbitrary well-typed pure Lean terms. SQL compilation supports terms it can unfold or translate through registered rules; it cannot reflect an opaque runtime `Query` closure back into SQL.
- The SQL adapter handles schema sources, projection, filtering, joins, union, ordering and pagination, aggregates, grouping, and nested collections. Ordinary `List` generators, arbitrary list consumers, direct compilation of `View.get`, and some correlated combinations requiring LATERAL are not yet supported. The reference interpreter can still evaluate them.
- Custom `[sql_function "SQL_NAME" n]` rules are responsible for preserving the intended semantics. The standard translations have the database behavior described above.
- The compiler checks arithmetic and comparison instances. Equality, deduplication, and grouping require corresponding `LawfulBEq` instances; ordering currently accepts standard `Ord` instances for Int, Nat, String, and Bool. Custom instances are not silently replaced by SQL defaults.
- SQL queries without explicit ordering need not follow native list traversal order. Queries preserve duplicates; lenses use keyed set semantics.
- Lean `Int` is unbounded. Database numbers, string ordering, and NULL have their own semantics. SQLite bindings check integer range; SQL arithmetic does not provide arbitrary-precision Lean integer semantics.
- Nested collections currently travel as JSON and do not support BLOB elements. Ordered nested collections are rejected on MySQL. The implementation does not yet have DSH's full shredding and optimization pipeline.
- SQL type and dialect coverage is incomplete. There is no migration system, incremental lens optimizer, or proof of semantic preservation for the entire SQL compiler.

Further details are in the [design notes](docs/design.md) and [SQL type coverage notes](docs/sql-types.md), currently written in Chinese.

## CI and releases

[CI](.github/workflows/lean_action_ci.yml) builds the library, demo, and test executable and runs `lake test` on pushes and pull requests. Tests include native SQLite integration through leansqlite.

To publish a version, update `version` in `lakefile.toml`, push the change to `master`, and manually run the [Release workflow](.github/workflows/release.yml) on `master` with the matching tag (for example, `v0.1.0`). It validates the version and tests, builds Lake archives for Linux x86-64, macOS x86-64/ARM64, and Windows x86-64, then creates the tag and GitHub Release. A retry can reuse a tag pointing to the same commit; a tag pointing elsewhere is rejected. Lake prefers these archives when the library is used as a dependency at a released revision.
