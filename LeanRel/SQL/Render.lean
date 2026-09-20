import LeanRel.SQL.Ast

namespace LeanRel.SQL

inductive Dialect where
  | postgresql | sqlite | mysql
  deriving Repr, BEq, Inhabited

structure Prepared where
  sql : String
  parameters : Array Value
  deriving Repr

private structure RenderState where
  parameters : Array Value := #[]
  ddl : Bool := false

private abbrev RenderM := StateT RenderState (Except String)

def quoteIdent (dialect : Dialect) (name : String) : String :=
  let q := if dialect == .mysql then "`" else "\""
  q ++ name.replace q (q ++ q) ++ q

private def ident (d : Dialect) (names : Ident) : RenderM String := do
  if names.isEmpty || names.any (fun n => n.isEmpty || n.contains '\x00') then
    throw "SQL identifier must be nonempty and contain no NUL"
  return String.intercalate "." (names.map (quoteIdent d))

private def names (d : Dialect) (ns : List String) : RenderM String :=
  return String.intercalate ", " (← ns.mapM fun n => ident d [n])

private def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

private def literal (d : Dialect) : Value → RenderM String
  | .null => pure "NULL"
  | .bool b => pure (if b then "TRUE" else "FALSE")
  | .int n => pure (toString n)
  | .real n => do
    if n.isNaN || n.isInf then throw "SQL real literals must be finite"
    pure (toString n)
  | .blob bytes =>
    let hex := String.ofList (bytes.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])
    pure (if d == .postgresql then s!"decode('{hex}', 'hex')" else s!"X'{hex}'")
  | .text s => do
    if s.contains '\x00' then throw "DDL text literals cannot contain NUL"
    match d with
    | .sqlite => pure ("'" ++ s.replace "'" "''" ++ "'")
    | .postgresql => pure ("E'" ++ (s.replace "\\" "\\\\").replace "'" "''" ++ "'")
    | .mysql =>
      let hex := String.ofList (s.toUTF8.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])
      pure ("CONVERT(X'" ++ hex ++ "' USING utf8mb4)")
  | _ => throw "SQL literals must be scalar"

private def parameter (d : Dialect) (v : Value) : RenderM String := do
  if (← get).ddl then return ← literal d v
  match v with
  | .record _ | .list _ => throw "SQL parameters must be scalar"
  | _ => pure ()
  modify fun s => {s with parameters := s.parameters.push v}
  let n := (← get).parameters.size
  return match d with
    | .postgresql => s!"${n}" | .sqlite => s!"?{n}" | .mysql => "?"

private def renderType (d : Dialect) : SqlType → String
  | .integer => "BIGINT" | .boolean => "BOOLEAN" | .text => "TEXT" | .real => "DOUBLE PRECISION"
  | .date => "DATE" | .timestamp => "TIMESTAMP"
  | .blob => if d == .postgresql then "BYTEA" else "BLOB"
  | .varchar n => s!"VARCHAR({n})" | .decimal p s => s!"DECIMAL({p}, {s})"

private def binOp : BinOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .and => "AND" | .or => "OR" | .concat => "||" | .like => "LIKE"
  | .nullSafeEq => "IS NOT DISTINCT FROM"

mutual
  private partial def expression (d : Dialect) : Expr → RenderM String
    | .column ns => ident d ns
    | .param v => parameter d v
    | .null => return "NULL"
    | .boolean b => return if b then "TRUE" else "FALSE"
    | .star none => return "*"
    | .star (some q) => return (← ident d [q]) ++ ".*"
    | .binary op a b => do
      let a ← expression d a
      let b ← expression d b
      if op == .concat && d == .mysql then return s!"CONCAT({a}, {b})"
      let op := if op == .nullSafeEq then
        match d with | .mysql => "<=>" | .sqlite => "IS" | .postgresql => "IS NOT DISTINCT FROM"
        else binOp op
      return s!"({a} {op} {b})"
    | .unary op a => do
      let a ← expression d a
      return match op with
        | .not => s!"(NOT {a})" | .negate => s!"(-{a})"
        | .isNull => s!"({a} IS NULL)" | .isNotNull => s!"({a} IS NOT NULL)"
    | .call name args distinct => do
      if name.isEmpty || !name.toList.all (fun c => c.isAlphanum || c == '_') then
        throw "invalid SQL function name"
      let args ← args.mapM (expression d)
      return name ++ "(" ++ (if distinct then "DISTINCT " else "") ++ String.intercalate ", " args ++ ")"
    | .caseWhen branches otherwise => do
      let branches ← branches.mapM fun (c, v) => return s!"WHEN {← expression d c} THEN {← expression d v}"
      return "(CASE " ++ String.intercalate " " branches ++ s!" ELSE {← expression d otherwise} END)"
    | .cast arg type => return s!"CAST({← expression d arg} AS {renderType d type})"
    | .scalar query => return s!"({← querySQL d query})"
    | .exists query => return s!"EXISTS ({← querySQL d query})"
    | .inQuery arg query => return s!"({← expression d arg} IN ({← querySQL d query}))"
    | .inList _ [] => return "FALSE"
    | .inList arg xs => do
      let arg ← expression d arg
      let xs ← xs.mapM (expression d)
      return s!"({arg} IN ({String.intercalate ", " xs}))"
    | .over fn partition order => do
      let fn ← expression d fn
      let p ← partition.mapM (expression d)
      let o ← ordering d order
      return fn ++ " OVER (" ++
        (if p.isEmpty then "" else "PARTITION BY " ++ String.intercalate ", " p) ++
        (if o.isEmpty then "" else (if p.isEmpty then "" else " ") ++ "ORDER BY " ++ o) ++ ")"
    | .collection child columns order => do
      if columns.isEmpty then throw "a nested collection needs result columns"
      if d == .mysql && !order.isEmpty then
        throw "ordered nested collections are not supported by the MySQL renderer"
      let child ← querySQL d child
      let table := "_leanrel_collection"
      let columns ← columns.mapM fun (name, nested) => do
        let c ← ident d [table, name]
        pure (if !nested then c else match d with
          | .sqlite => s!"json({c})" | .postgresql => s!"CAST({c} AS jsonb)" | .mysql => s!"CAST({c} AS JSON)")
      let order ← ordering d (order.map fun (name, desc) => (.column [table, name], desc))
      let ordered := if order.isEmpty then "" else " ORDER BY " ++ order
      let row := String.intercalate ", " columns
      let aggregate := match d with
        | .sqlite => s!"json_group_array(json_array({row}){ordered})"
        | .postgresql => s!"CAST(COALESCE(jsonb_agg(jsonb_build_array({row}){ordered}), '[]'::jsonb) AS TEXT)"
        | .mysql => s!"COALESCE(JSON_ARRAYAGG(JSON_ARRAY({row})), JSON_ARRAY())"
      return s!"(SELECT {aggregate} FROM ({child}) AS {quoteIdent d table})"
    | .collectionLength value => do
      let value ← expression d value
      return match d with
        | .sqlite => s!"json_array_length({value})"
        | .postgresql => s!"jsonb_array_length(CAST({value} AS jsonb))"
        | .mysql => s!"JSON_LENGTH({value})"
  private partial def sourceSQL (d : Dialect) : Source → RenderM String
    | .table ns alias => do
      let ns ← ident d ns
      let suffix ← match alias with
        | none => pure ""
        | some a => do pure (" AS " ++ (← ident d [a]))
      return ns ++ suffix
    | .subquery q alias lateral => do
      if lateral && d == .sqlite then throw "SQLite does not support LATERAL sources"
      return (if lateral then "LATERAL " else "") ++ s!"({← querySQL d q}) AS {← ident d [alias]}"
    | .join kind left right on => do
      if kind == .full && d == .mysql then throw "MySQL does not support FULL JOIN"
      if kind != .cross && on.isNone then throw "a non-CROSS JOIN needs an ON condition"
      if kind == .cross && on.isSome then throw "CROSS JOIN does not accept ON"
      let left ← sourceSQL d left
      let right ← sourceSQL d right
      let join := match kind with
        | .inner => "INNER" | .left => "LEFT" | .right => "RIGHT" | .full => "FULL" | .cross => "CROSS"
      let on ← match on with
        | none => pure ""
        | some e => do pure (" ON " ++ (← expression d e))
      return s!"({left} {join} JOIN {right}{on})"
  private partial def ordering (d : Dialect) (items : List (Expr × Bool)) : RenderM String := do
    let items ← items.mapM fun (e, desc) => return (← expression d e) ++ (if desc then " DESC" else " ASC")
    return String.intercalate ", " items
  private partial def projection (d : Dialect) (items : List (Expr × Option String)) : RenderM String := do
    if items.isEmpty then throw "SELECT requires at least one result column"
    let items ← items.mapM fun (e, alias) => do
      let e ← expression d e
      match alias with
      | none => return e
      | some a => return e ++ " AS " ++ (← ident d [a])
    return String.intercalate ", " items
  private partial def querySQL (d : Dialect) : Query → RenderM String
    | .select s => do
      let mut sql := "SELECT " ++ (if s.distinct then "DISTINCT " else "") ++ (← projection d s.columns)
      if let some f := s.from_ then sql := sql ++ " FROM " ++ (← sourceSQL d f)
      if let some p := s.where_ then sql := sql ++ " WHERE " ++ (← expression d p)
      if !s.groupBy.isEmpty then
        sql := sql ++ " GROUP BY " ++ String.intercalate ", " (← s.groupBy.mapM (expression d))
      if let some h := s.having then sql := sql ++ " HAVING " ++ (← expression d h)
      if !s.orderBy.isEmpty then sql := sql ++ " ORDER BY " ++ (← ordering d s.orderBy)
      if let some l := s.limit then sql := sql ++ s!" LIMIT {l}"
      if let some o := s.offset then
        if s.limit.isNone then
          sql := sql ++ (match d with | .sqlite => " LIMIT -1" | .mysql => " LIMIT 18446744073709551615" | _ => "")
        sql := sql ++ s!" OFFSET {o}"
      return sql
    | .set op all a b => do
      if all && op != .union && d == .sqlite then throw "SQLite does not support INTERSECT/EXCEPT ALL"
      let op := match op with | .union => "UNION" | .intersect => "INTERSECT" | .except => "EXCEPT"
      -- Wrapping operands preserves local ORDER/LIMIT and works on SQLite too.
      return s!"SELECT * FROM ({← querySQL d a}) AS {quoteIdent d "_set_l"} {op}" ++
        (if all then " ALL" else "") ++ s!" SELECT * FROM ({← querySQL d b}) AS {quoteIdent d "_set_r"}"
    | .with_ recursive bindings body => do
      if bindings.isEmpty then throw "WITH requires a binding"
      if (bindings.map Prod.fst).eraseDups.length != bindings.length then throw "duplicate CTE name"
      let bindings ← bindings.mapM fun (name, query) => return s!"{← ident d [name]} AS ({← querySQL d query})"
      return "WITH " ++ (if recursive then "RECURSIVE " else "") ++
        String.intercalate ", " bindings ++ " " ++ (← querySQL d body)
end

private def returningSQL (d : Dialect) (items : List (Expr × Option String)) : RenderM String := do
  if items.isEmpty then return ""
  if d == .mysql then throw "MySQL does not support DML RETURNING"
  return " RETURNING " ++ (← projection d items)

private def whereSQL (d : Dialect) (p : Option Expr) : RenderM String :=
  match p with | none => pure "" | some p => return " WHERE " ++ (← expression d p)

private def constraintSQL (d : Dialect) : Constraint → RenderM String
  | .primaryKey cs => return s!"PRIMARY KEY ({← names d cs})"
  | .unique cs => return s!"UNIQUE ({← names d cs})"
  | .foreignKey cs table target => return s!"FOREIGN KEY ({← names d cs}) REFERENCES {← ident d table} ({← names d target})"
  | .check p => return s!"CHECK ({← expression d p})"

private def statementSQL (d : Dialect) : Statement → RenderM String
  | .query q => querySQL d q
  | .insert table columns src ret => do
    if columns.isEmpty || columns.eraseDups.length != columns.length then throw "invalid INSERT columns"
    let head := s!"INSERT INTO {← ident d table} ({← names d columns}) "
    let body ← match src with
      | .query q => querySQL d q
      | .values rows => do
        if rows.isEmpty || rows.any (·.length != columns.length) then throw "INSERT row arity mismatch"
        let rows ← rows.mapM fun row => return "(" ++ String.intercalate ", " (← row.mapM (expression d)) ++ ")"
        pure ("VALUES " ++ String.intercalate ", " rows)
    return head ++ body ++ (← returningSQL d ret)
  | .update table assignments p ret alias => do
    if assignments.isEmpty || (assignments.map Prod.fst).eraseDups.length != assignments.length then
      throw "UPDATE needs non-duplicate assignments"
    let mut table ← ident d table
    if let some alias := alias then table := table ++ " AS " ++ (← ident d [alias])
    let sets ← assignments.mapM fun (n, e) => return s!"{← ident d [n]} = {← expression d e}"
    return s!"UPDATE {table} SET {String.intercalate ", " sets}{← whereSQL d p}{← returningSQL d ret}"
  | .delete table p ret alias => do
    let mut table ← ident d table
    if let some alias := alias then table := table ++ " AS " ++ (← ident d [alias])
    return s!"DELETE FROM {table}{← whereSQL d p}{← returningSQL d ret}"
  | .createTable t => do
    modify fun s => {s with ddl := true}
    if t.columns.isEmpty || (t.columns.map ColumnDef.name).eraseDups.length != t.columns.length then
      throw "CREATE TABLE needs non-duplicate columns"
    let columnNames := t.columns.map ColumnDef.name
    let mut primaryKeys := 0
    for constraint in t.constraints do
      let localColumns ← match constraint with
        | .primaryKey cs => do
          primaryKeys := primaryKeys + 1
          pure cs
        | .unique cs => pure cs
        | .foreignKey cs _ target => do
          if target.length != cs.length || target.isEmpty || target.eraseDups.length != target.length then
            throw "invalid foreign key target columns"
          pure cs
        | .check _ => pure []
      match constraint with
      | .check _ => pure ()
      | _ =>
        if localColumns.isEmpty || localColumns.eraseDups.length != localColumns.length ||
            !localColumns.all columnNames.contains then
          throw "constraint refers to empty, duplicate, or unknown columns"
    if primaryKeys > 1 then throw "CREATE TABLE allows one primary key"
    let table ← ident d t.name
    let cols ← t.columns.mapM fun c => do
      let defaultValue ← match c.defaultValue with
        | none => pure "" | some e => do pure (" DEFAULT (" ++ (← expression d e) ++ ")")
      return s!"{← ident d [c.name]} {renderType d c.type}" ++ (if c.nullable then "" else " NOT NULL") ++ defaultValue
    let cs ← t.constraints.mapM (constraintSQL d)
    return "CREATE TABLE " ++ (if t.ifNotExists then "IF NOT EXISTS " else "") ++ table ++
      " (" ++ String.intercalate ", " (cols ++ cs) ++ ")"
  | .createIndex name table cs unique => do
    if cs.isEmpty then throw "CREATE INDEX requires columns"
    return "CREATE " ++ (if unique then "UNIQUE " else "") ++ s!"INDEX {← ident d [name]} ON {← ident d table} ({← names d cs})"
  | .createView name q => do
    modify fun s => {s with ddl := true}
    return s!"CREATE VIEW {← ident d name} AS {← querySQL d q}"
  | .dropTable name ifExists => return "DROP TABLE " ++ (if ifExists then "IF EXISTS " else "") ++ (← ident d name)
  | .begin => return "BEGIN"
  | .commit => return "COMMIT"
  | .rollback => return "ROLLBACK"

def render (dialect : Dialect) (statement : Statement) : Except String Prepared := do
  let (sql, state) ← (statementSQL dialect statement).run {}
  return ⟨sql, state.parameters⟩

end LeanRel.SQL
