import LeanRel.SQL.Ast
import LeanRel.Parser

namespace LeanRel.SQL.Notation
open Lean Elab Term

declare_syntax_cat sqlExpr
declare_syntax_cat sqlQuery
declare_syntax_cat sqlSource
declare_syntax_cat sqlStmt
declare_syntax_cat sqlDirection
declare_syntax_cat sqlType
declare_syntax_cat sqlTableEntry
-- Prefer SQL literals and special forms over their identifier/function fallbacks.
syntax (priority := low) ident : sqlExpr
syntax num : sqlExpr
syntax str : sqlExpr
syntax identDispatch(&"NULL") : sqlExpr
syntax identDispatch(&"TRUE") : sqlExpr
syntax identDispatch(&"FALSE") : sqlExpr
syntax "*" : sqlExpr
syntax "${" term "}" : sqlExpr
syntax "@{" term "}" : sqlExpr
syntax "(" sqlExpr ")" : sqlExpr
syntax (priority := low) ident "(" sqlExpr,* ")" : sqlExpr
syntax (priority := low) ident "(" &"DISTINCT" sqlExpr,+ ")" : sqlExpr
syntax:70 sqlExpr:70 " * " sqlExpr:71 : sqlExpr
syntax:70 sqlExpr:70 " / " sqlExpr:71 : sqlExpr
syntax:70 sqlExpr:70 " % " sqlExpr:71 : sqlExpr
syntax:65 sqlExpr:65 " + " sqlExpr:66 : sqlExpr
syntax:65 sqlExpr:65 " - " sqlExpr:66 : sqlExpr
syntax:60 sqlExpr:60 " || " sqlExpr:61 : sqlExpr
syntax:50 sqlExpr:51 " = " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 " <> " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 " < " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 " <= " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 " > " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 " >= " sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 identDispatch(&"LIKE") sqlExpr:51 : sqlExpr
syntax:50 sqlExpr:51 identDispatch(&"IS") &"NULL" : sqlExpr
syntax:50 sqlExpr:51 identDispatch(&"IS") &"NOT" &"NULL" : sqlExpr
syntax:50 sqlExpr:51 identDispatch(&"IN") "(" sqlExpr,* ")" : sqlExpr
syntax:50 sqlExpr:51 identDispatch(&"IN") "(" sqlQuery ")" : sqlExpr
syntax:40 identDispatch(&"NOT") sqlExpr:40 : sqlExpr
syntax:35 sqlExpr:35 identDispatch(&"AND") sqlExpr:36 : sqlExpr
syntax:30 sqlExpr:30 identDispatch(&"OR") sqlExpr:31 : sqlExpr
syntax:75 "-" sqlExpr:75 : sqlExpr
syntax identDispatch(&"EXISTS") "(" sqlQuery ")" : sqlExpr
syntax "(" sqlQuery ")" : sqlExpr
syntax identDispatch(&"CASE") (&"WHEN" sqlExpr &"THEN" sqlExpr)+ &"ELSE" sqlExpr &"END" : sqlExpr
syntax identDispatch(&"CAST") "(" sqlExpr &"AS" sqlType ")" : sqlExpr
syntax identDispatch(&"ASC") : sqlDirection
syntax identDispatch(&"DESC") : sqlDirection
syntax sqlOrder := sqlExpr (sqlDirection)?
syntax sqlProjection := sqlExpr (&"AS" ident)?
syntax:80 sqlExpr:80 identDispatch(&"OVER") "(" (&"PARTITION" &"BY" sqlExpr,+)?
  (&"ORDER" &"BY" sqlOrder,+)? ")" : sqlExpr
syntax ident (&"AS" ident)? : sqlSource
syntax "(" sqlQuery ")" &"AS" ident : sqlSource
syntax "@{" term "}" (&"AS" ident)? : sqlSource
syntax:60 sqlSource:60 identDispatch(&"JOIN") sqlSource:61 &"ON" sqlExpr : sqlSource
syntax:60 sqlSource:60 identDispatch(&"LEFT") &"JOIN" sqlSource:61 &"ON" sqlExpr : sqlSource
syntax:60 sqlSource:60 identDispatch(&"RIGHT") &"JOIN" sqlSource:61 &"ON" sqlExpr : sqlSource
syntax:60 sqlSource:60 identDispatch(&"FULL") &"JOIN" sqlSource:61 &"ON" sqlExpr : sqlSource
syntax:60 sqlSource:60 identDispatch(&"CROSS") &"JOIN" sqlSource:61 : sqlSource
syntax identDispatch(&"SELECT") (&"DISTINCT")? sqlProjection,+ (&"FROM" sqlSource)?
  (&"WHERE" sqlExpr)? (&"GROUP" &"BY" sqlExpr,+)? (&"HAVING" sqlExpr)?
  (&"ORDER" &"BY" sqlOrder,+)? (&"LIMIT" num)? (&"OFFSET" num)? : sqlQuery
syntax:20 sqlQuery:20 identDispatch(&"UNION") sqlQuery:21 : sqlQuery
syntax:20 sqlQuery:20 identDispatch(&"UNION") &"ALL" sqlQuery:21 : sqlQuery
syntax:20 sqlQuery:20 identDispatch(&"EXCEPT") sqlQuery:21 : sqlQuery
syntax:25 sqlQuery:25 identDispatch(&"INTERSECT") sqlQuery:26 : sqlQuery
syntax sqlCTE := ident &"AS" "(" sqlQuery ")"
syntax identDispatch(&"WITH") (&"RECURSIVE")? sqlCTE,+ sqlQuery : sqlQuery
syntax "@{" term "}" : sqlQuery
syntax sqlQuery : sqlStmt
syntax sqlAssignment := ident "=" sqlExpr
syntax sqlValuesRow := "(" sqlExpr,* ")"
syntax identDispatch(&"INSERT") &"INTO" ident "(" ident,+ ")" &"VALUES" sqlValuesRow,+
  (&"RETURNING" sqlProjection,+)? : sqlStmt
syntax identDispatch(&"INSERT") &"INTO" ident "(" ident,+ ")" sqlQuery
  (&"RETURNING" sqlProjection,+)? : sqlStmt
syntax identDispatch(&"UPDATE") ident &"SET" sqlAssignment,+ (&"WHERE" sqlExpr)?
  (&"RETURNING" sqlProjection,+)? : sqlStmt
syntax identDispatch(&"DELETE") &"FROM" ident (&"WHERE" sqlExpr)? (&"RETURNING" sqlProjection,+)? : sqlStmt
syntax identDispatch(&"INTEGER") : sqlType
syntax identDispatch(&"BIGINT") : sqlType
syntax identDispatch(&"BOOLEAN") : sqlType
syntax identDispatch(&"TEXT") : sqlType
syntax identDispatch(&"REAL") : sqlType
syntax identDispatch(&"DATE") : sqlType
syntax identDispatch(&"TIMESTAMP") : sqlType
syntax identDispatch(&"BLOB") : sqlType
syntax identDispatch(&"VARCHAR") "(" num ")" : sqlType
syntax identDispatch(&"DECIMAL") "(" num "," num ")" : sqlType
syntax ident sqlType (&"NOT" &"NULL")? (&"DEFAULT" sqlExpr)? : sqlTableEntry
syntax identDispatch(&"PRIMARY") &"KEY" "(" ident,+ ")" : sqlTableEntry
syntax identDispatch(&"UNIQUE") "(" ident,+ ")" : sqlTableEntry
syntax identDispatch(&"FOREIGN") &"KEY" "(" ident,+ ")" &"REFERENCES" ident "(" ident,+ ")" : sqlTableEntry
syntax identDispatch(&"CHECK") "(" sqlExpr ")" : sqlTableEntry
syntax identDispatch(&"CREATE") &"TABLE" (&"IF" &"NOT" &"EXISTS")? ident "(" sqlTableEntry,+ ")" : sqlStmt
syntax identDispatch(&"CREATE") (&"UNIQUE")? &"INDEX" ident &"ON" ident "(" ident,+ ")" : sqlStmt
syntax identDispatch(&"CREATE") &"VIEW" ident &"AS" sqlQuery : sqlStmt
syntax identDispatch(&"DROP") &"TABLE" (&"IF" &"EXISTS")? ident : sqlStmt
syntax identDispatch(&"BEGIN") : sqlStmt
syntax identDispatch(&"COMMIT") : sqlStmt
syntax identDispatch(&"ROLLBACK") : sqlStmt
syntax:max (name := sqlStatementTerm) identDispatch(&"sql!") "[" withoutForbidden(sqlStmt) "]" : term
syntax:max (name := sqlQueryTerm) identDispatch(&"sql_query!") "[" withoutForbidden(sqlQuery) "]" : term
syntax:max (name := sqlExprTerm) identDispatch(&"sql_expr!") "[" withoutForbidden(sqlExpr) "]" : term

private def nameParts (n : Lean.Ident) : TSyntax `term := quote (n.getId.components.map Name.toString)
private def nameString (n : Lean.Ident) : TSyntax `term := quote n.getId.toString
private def optional (x : Option (TSyntax `term)) : MacroM (TSyntax `term) :=
  match x with | none => `(none) | some x => `(some $x)

private def typeTerm : TSyntax `sqlType → MacroM (TSyntax `term)
  | `(sqlType| INTEGER) | `(sqlType| BIGINT) => `(SqlType.integer)
  | `(sqlType| BOOLEAN) => `(SqlType.boolean)
  | `(sqlType| TEXT) => `(SqlType.text)
  | `(sqlType| REAL) => `(SqlType.real)
  | `(sqlType| DATE) => `(SqlType.date)
  | `(sqlType| TIMESTAMP) => `(SqlType.timestamp)
  | `(sqlType| BLOB) => `(SqlType.blob)
  | `(sqlType| VARCHAR($n:num)) => `(SqlType.varchar $n)
  | `(sqlType| DECIMAL($p:num, $s:num)) => `(SqlType.decimal $p $s)
  | _ => Macro.throwUnsupported

mutual
  private partial def exprTerm : TSyntax `sqlExpr → MacroM (TSyntax `term)
    | `(sqlExpr| $n:ident) => `(SQL.Expr.column $(nameParts n))
    | `(sqlExpr| $n:num) => `(SQL.Expr.param (Value.int (Int.ofNat $n)))
    | `(sqlExpr| $s:str) => `(SQL.Expr.param (Value.text $s))
    | `(sqlExpr| NULL) => `(SQL.Expr.null)
    | `(sqlExpr| TRUE) => `(SQL.Expr.boolean true)
    | `(sqlExpr| FALSE) => `(SQL.Expr.boolean false)
    | `(sqlExpr| *) => `(SQL.Expr.star none)
    | `(sqlExpr| ${ $t:term }) => `(SQL.Expr.param (Codec.encode $t))
    | `(sqlExpr| @{ $t:term }) => pure t
    | `(sqlExpr| ($e:sqlExpr)) => exprTerm e
    | `(sqlExpr| $fn:ident($[$args:sqlExpr],*)) => do
      let args ← args.mapM exprTerm
      `(SQL.Expr.call $(nameString fn) [$args,*] false)
    | `(sqlExpr| $fn:ident(DISTINCT $[$args:sqlExpr],*)) => do
      let args ← args.mapM exprTerm
      `(SQL.Expr.call $(nameString fn) [$args,*] true)
    | `(sqlExpr| $a:sqlExpr + $b:sqlExpr) => binary .add a b
    | `(sqlExpr| $a:sqlExpr - $b:sqlExpr) => binary .sub a b
    | `(sqlExpr| $a:sqlExpr * $b:sqlExpr) => binary .mul a b
    | `(sqlExpr| $a:sqlExpr / $b:sqlExpr) => binary .div a b
    | `(sqlExpr| $a:sqlExpr % $b:sqlExpr) => binary .mod a b
    | `(sqlExpr| $a:sqlExpr || $b:sqlExpr) => binary .concat a b
    | `(sqlExpr| $a:sqlExpr = $b:sqlExpr) => binary .eq a b
    | `(sqlExpr| $a:sqlExpr <> $b:sqlExpr) => binary .ne a b
    | `(sqlExpr| $a:sqlExpr < $b:sqlExpr) => binary .lt a b
    | `(sqlExpr| $a:sqlExpr <= $b:sqlExpr) => binary .le a b
    | `(sqlExpr| $a:sqlExpr > $b:sqlExpr) => binary .gt a b
    | `(sqlExpr| $a:sqlExpr >= $b:sqlExpr) => binary .ge a b
    | `(sqlExpr| $a:sqlExpr LIKE $b:sqlExpr) => binary .like a b
    | `(sqlExpr| $a:sqlExpr AND $b:sqlExpr) => binary .and a b
    | `(sqlExpr| $a:sqlExpr OR $b:sqlExpr) => binary .or a b
    | `(sqlExpr| NOT $a:sqlExpr) => do `(SQL.Expr.unary .not $(← exprTerm a))
    | `(sqlExpr| -$a:sqlExpr) => do `(SQL.Expr.unary .negate $(← exprTerm a))
    | `(sqlExpr| $a:sqlExpr IS NULL) => do `(SQL.Expr.unary .isNull $(← exprTerm a))
    | `(sqlExpr| $a:sqlExpr IS NOT NULL) => do `(SQL.Expr.unary .isNotNull $(← exprTerm a))
    | `(sqlExpr| $a:sqlExpr IN ($[$xs:sqlExpr],*)) => do
      let xs ← xs.mapM exprTerm
      `(SQL.Expr.inList $(← exprTerm a) [$xs,*])
    | `(sqlExpr| $a:sqlExpr IN ($q:sqlQuery)) => do `(SQL.Expr.inQuery $(← exprTerm a) $(← queryTerm q))
    | `(sqlExpr| EXISTS ($q:sqlQuery)) => do `(SQL.Expr.exists $(← queryTerm q))
    | `(sqlExpr| ($q:sqlQuery)) => do `(SQL.Expr.scalar $(← queryTerm q))
    | `(sqlExpr| CASE $[WHEN $ps:sqlExpr THEN $vs:sqlExpr]* ELSE $other:sqlExpr END) => do
      let branches ← (ps.zip vs).mapM fun (p, v) => do `(($(← exprTerm p), $(← exprTerm v)))
      `(SQL.Expr.caseWhen [$branches,*] $(← exprTerm other))
    | `(sqlExpr| CAST($e:sqlExpr AS $t:sqlType)) => do `(SQL.Expr.cast $(← exprTerm e) $(← typeTerm t))
    | `(sqlExpr| $e:sqlExpr OVER ($[PARTITION BY $[$ps:sqlExpr],*]? $[ORDER BY $[$os:sqlOrder],*]?)) => do
      let ps ← (ps.getD #[]).mapM exprTerm
      let os ← (os.getD #[]).mapM orderTerm
      `(SQL.Expr.over $(← exprTerm e) [$ps,*] [$os,*])
    | _ => Macro.throwUnsupported
  private partial def binary (op : BinOp) (a b : TSyntax `sqlExpr) : MacroM (TSyntax `term) := do
    let n := match op with
      | .eq => ``BinOp.eq | .ne => ``BinOp.ne | .lt => ``BinOp.lt | .le => ``BinOp.le
      | .gt => ``BinOp.gt | .ge => ``BinOp.ge | .add => ``BinOp.add | .sub => ``BinOp.sub
      | .mul => ``BinOp.mul | .div => ``BinOp.div | .mod => ``BinOp.mod | .and => ``BinOp.and
      | .or => ``BinOp.or | .concat => ``BinOp.concat | .like => ``BinOp.like | .nullSafeEq => ``BinOp.nullSafeEq
    `(SQL.Expr.binary $(mkIdent n) $(← exprTerm a) $(← exprTerm b))
  private partial def orderTerm : TSyntax ``sqlOrder → MacroM (TSyntax `term)
    | `(sqlOrder| $e:sqlExpr $[$dir:sqlDirection]?) => do
      let desc := dir.any fun d => d.raw[0].getAtomVal == "DESC"
      `(($(← exprTerm e), $(quote desc)))
    | _ => Macro.throwUnsupported
  private partial def projectionTerm : TSyntax ``sqlProjection → MacroM (TSyntax `term)
    | `(sqlProjection| $e:sqlExpr $[AS $alias:ident]?) => do
      `(($(← exprTerm e), $(← optional (alias.map nameString))))
    | _ => Macro.throwUnsupported
  private partial def sourceTerm : TSyntax `sqlSource → MacroM (TSyntax `term)
    | `(sqlSource| $n:ident $[AS $alias:ident]?) => do
      `(SQL.Source.table $(nameParts n) $(← optional (alias.map nameString)))
    | `(sqlSource| @{ $t:term } $[AS $alias:ident]?) => do
      `(SQL.Source.table [($t : TableDef).name] $(← optional (alias.map nameString)))
    | `(sqlSource| ($q:sqlQuery) AS $alias:ident) => do
      `(SQL.Source.subquery $(← queryTerm q) $(nameString alias) false)
    | `(sqlSource| $a:sqlSource JOIN $b:sqlSource ON $p:sqlExpr) => joinTerm ``JoinKind.inner a b (some p)
    | `(sqlSource| $a:sqlSource LEFT JOIN $b:sqlSource ON $p:sqlExpr) => joinTerm ``JoinKind.left a b (some p)
    | `(sqlSource| $a:sqlSource RIGHT JOIN $b:sqlSource ON $p:sqlExpr) => joinTerm ``JoinKind.right a b (some p)
    | `(sqlSource| $a:sqlSource FULL JOIN $b:sqlSource ON $p:sqlExpr) => joinTerm ``JoinKind.full a b (some p)
    | `(sqlSource| $a:sqlSource CROSS JOIN $b:sqlSource) => joinTerm ``JoinKind.cross a b none
    | _ => Macro.throwUnsupported
  private partial def joinTerm (kind : Name) (a b : TSyntax `sqlSource) (p : Option (TSyntax `sqlExpr)) :
      MacroM (TSyntax `term) := do
    let p ← p.mapM exprTerm
    `(SQL.Source.join $(mkIdent kind) $(← sourceTerm a) $(← sourceTerm b) $(← optional p))
  private partial def queryTerm : TSyntax `sqlQuery → MacroM (TSyntax `term)
    | `(sqlQuery| SELECT $[DISTINCT%$distinct]? $[$cols:sqlProjection],*
        $[FROM $src:sqlSource]? $[WHERE $p:sqlExpr]? $[GROUP BY $[$gs:sqlExpr],*]?
        $[HAVING $h:sqlExpr]? $[ORDER BY $[$os:sqlOrder],*]? $[LIMIT $lim:num]? $[OFFSET $off:num]?) => do
      let cols ← cols.mapM projectionTerm
      let src ← optional (← src.mapM sourceTerm)
      let p ← optional (← p.mapM exprTerm)
      let gs ← (gs.getD #[]).mapM exprTerm
      let h ← optional (← h.mapM exprTerm)
      let os ← (os.getD #[]).mapM orderTerm
      let lim ← optional (lim.map fun n => ⟨n.raw⟩)
      let off ← optional (off.map fun n => ⟨n.raw⟩)
      `(SQL.Query.select {
        columns := [$cols,*], distinct := $(quote distinct.isSome),
        from_ := $src, where_ := $p, groupBy := [$gs,*], having := $h,
        orderBy := [$os,*], limit := $lim, offset := $off})
    | `(sqlQuery| $a:sqlQuery UNION $b:sqlQuery) => do `(SQL.Query.set .union false $(← queryTerm a) $(← queryTerm b))
    | `(sqlQuery| $a:sqlQuery UNION ALL $b:sqlQuery) => do `(SQL.Query.set .union true $(← queryTerm a) $(← queryTerm b))
    | `(sqlQuery| $a:sqlQuery EXCEPT $b:sqlQuery) => do `(SQL.Query.set .except false $(← queryTerm a) $(← queryTerm b))
    | `(sqlQuery| $a:sqlQuery INTERSECT $b:sqlQuery) => do `(SQL.Query.set .intersect false $(← queryTerm a) $(← queryTerm b))
    | `(sqlQuery| WITH $[RECURSIVE%$recursiveFlag]? $[$bindings:sqlCTE],* $body:sqlQuery) => do
      let bindings ← bindings.mapM fun b => do
        let `(sqlCTE| $n:ident AS ($q:sqlQuery)) := b | Macro.throwUnsupported
        `(($(nameString n), $(← queryTerm q)))
      `(SQL.Query.with_ $(quote recursiveFlag.isSome) [$bindings,*] $(← queryTerm body))
    | `(sqlQuery| @{ $t:term }) => pure t
    | _ => Macro.throwUnsupported
end

private def returningTerm (items : Option (Array (TSyntax ``sqlProjection))) : MacroM (TSyntax `term) := do
  let items ← (items.getD #[]).mapM projectionTerm
  `([$items,*])

private def statementTerm : TSyntax `sqlStmt → MacroM (TSyntax `term)
  | `(sqlStmt| $q:sqlQuery) => do `(SQL.Statement.query $(← queryTerm q))
  | `(sqlStmt| INSERT INTO $table:ident ($[$cols:ident],*) VALUES $[$rows:sqlValuesRow],*
      $[RETURNING $[$ret:sqlProjection],*]?) => do
    let rows ← rows.mapM fun row => do
      let `(sqlValuesRow| ($[$xs:sqlExpr],*)) := row | Macro.throwUnsupported
      let xs ← xs.mapM exprTerm
      `([$xs,*])
    `(SQL.Statement.insert $(nameParts table) $(quote (cols.toList.map (·.getId.toString)))
      (.values [$rows,*]) $(← returningTerm ret))
  | `(sqlStmt| INSERT INTO $table:ident ($[$cols:ident],*) $q:sqlQuery $[RETURNING $[$ret:sqlProjection],*]?) => do
    `(SQL.Statement.insert $(nameParts table) $(quote (cols.toList.map (·.getId.toString)))
      (.query $(← queryTerm q)) $(← returningTerm ret))
  | `(sqlStmt| UPDATE $table:ident SET $[$sets:sqlAssignment],* $[WHERE $p:sqlExpr]?
      $[RETURNING $[$ret:sqlProjection],*]?) => do
    let sets ← sets.mapM fun s => do
      let `(sqlAssignment| $n:ident = $e:sqlExpr) := s | Macro.throwUnsupported
      `(($(nameString n), $(← exprTerm e)))
    `(SQL.Statement.update $(nameParts table) [$sets,*] $(← optional (← p.mapM exprTerm)) $(← returningTerm ret))
  | `(sqlStmt| DELETE FROM $table:ident $[WHERE $p:sqlExpr]? $[RETURNING $[$ret:sqlProjection],*]?) => do
    `(SQL.Statement.delete $(nameParts table) $(← optional (← p.mapM exprTerm)) $(← returningTerm ret))
  | `(sqlStmt| CREATE TABLE $[IF NOT EXISTS%$flag]? $table:ident ($[$entries:sqlTableEntry],*)) => do
    let mut cols := #[]
    let mut constraints := #[]
    for entry in entries do
      match entry with
      | `(sqlTableEntry| $n:ident $t:sqlType $[NOT NULL%$required]? $[DEFAULT $v:sqlExpr]?) =>
        cols := cols.push (← `({
          name := $(nameString n), type := $(← typeTerm t),
          nullable := $(quote required.isNone), defaultValue := $(← optional (← v.mapM exprTerm)) : ColumnDef}))
      | `(sqlTableEntry| PRIMARY KEY ($[$cs:ident],*)) =>
        constraints := constraints.push (← `(Constraint.primaryKey $(quote (cs.toList.map (·.getId.toString)))))
      | `(sqlTableEntry| UNIQUE ($[$cs:ident],*)) =>
        constraints := constraints.push (← `(Constraint.unique $(quote (cs.toList.map (·.getId.toString)))))
      | `(sqlTableEntry| FOREIGN KEY ($[$cs:ident],*) REFERENCES $target:ident ($[$ts:ident],*)) =>
        constraints := constraints.push (← `(Constraint.foreignKey $(quote (cs.toList.map (·.getId.toString)))
          $(nameParts target) $(quote (ts.toList.map (·.getId.toString)))))
      | `(sqlTableEntry| CHECK ($p:sqlExpr)) =>
        constraints := constraints.push (← `(Constraint.check $(← exprTerm p)))
      | _ => Macro.throwUnsupported
    `(SQL.Statement.createTable {
      name := $(nameParts table), columns := [$cols,*],
      constraints := [$constraints,*], ifNotExists := $(quote flag.isSome)})
  | `(sqlStmt| CREATE $[UNIQUE%$unique]? INDEX $name:ident ON $table:ident ($[$cols:ident],*)) => do
    `(SQL.Statement.createIndex $(nameString name) $(nameParts table)
      $(quote (cols.toList.map (·.getId.toString))) $(quote unique.isSome))
  | `(sqlStmt| CREATE VIEW $name:ident AS $q:sqlQuery) => do
    `(SQL.Statement.createView $(nameParts name) $(← queryTerm q))
  | `(sqlStmt| DROP TABLE $[IF EXISTS%$flag]? $name:ident) =>
    `(SQL.Statement.dropTable $(nameParts name) $(quote flag.isSome))
  | `(sqlStmt| BEGIN) => `(SQL.Statement.begin)
  | `(sqlStmt| COMMIT) => `(SQL.Statement.commit)
  | `(sqlStmt| ROLLBACK) => `(SQL.Statement.rollback)
  | _ => Macro.throwUnsupported

macro_rules
  | `(sql! [$s:sqlStmt]) => statementTerm s
  | `(sql_query! [$q:sqlQuery]) => queryTerm q
  | `(sql_expr! [$e:sqlExpr]) => exprTerm e

end LeanRel.SQL.Notation
