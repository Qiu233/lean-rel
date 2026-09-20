# lean-rel

Lean 原生 comprehension 查询／更新语言，以及可以独立使用的 SQL 中端。

这是一个可执行的实现，接口仍在演化。前端不依赖 SQL；SQL 中端不依赖具体数据库。SQLite 执行使用 [leanprover/leansqlite](https://github.com/leanprover/leansqlite/tree/v4.34.0) 的原生绑定，依赖已锁定到与 Lean 4.34.0 对应的版本。

```sh
lake build
lake exe lean-rel
lake exe lean-rel-tests
```

构建需要 C 编译器；leansqlite 会编译其自带的 SQLite。[Main.lean](Main.lean) 是完整示例，[Tests/Main.lean](Tests/Main.lean) 执行真实数据库测试。

## Schema：声明一次，同时得到原生类型和元数据

```lean
import LeanRel
open LeanRel LeanRel.Frontend
open scoped LeanRel.SQL

schema Person "people" {
  id : Int, name : String, age : Int
} key [id]
```

此 command 生成：

- 普通结构 `Person`，可以直接使用 `p.age`、模式匹配和 `{p with age := ...}`。
- `Codec Person`、`Person.schema : TableDef`、`Person.table : Source Person`。
- 通用字段容器 `Person.Columns F`，字段分别为 `F Int`、`F String` 等；它本身与 SQL 无关。
- 跨模块持久化的编译期元数据，供 elaborator 使用。

字段类型是 Lean term，可用类型别名，也可以扩展 `ColumnType`／`Codec`。内置 `Int`、`Float`、`Bool`、`String`、`Array UInt8` 和可空的 `Option` 类型。`key []` 可表示无键查询源；可更新的基本 view 要求键。

函数依赖也在 schema 中声明：

```lean
schema Track "tracks" {
  album : Int, track : Int, rating : Int
} key [album, track] dependencies { [track] -> [rating] }
```

元数据并不只存在于编译期：`.schema` 仍是普通运行时值；SQL 建表从 `SQL.CreateTable.ofTable Person.schema` 获得。一般函数依赖由 lens 验证，不自动变成数据库约束或触发器。

## 丰富前端：Lean term 构成的 comprehension

```lean
def adults (minimum : Int) := query% [
  (p.name, p.age + 1) | p ← Person.table, p.age ≥ minimum]

def bonus (age : Int) : Int := if age ≥ 18 then age + 2 else age

def computed := query% [
  (p.name, bonus p.age) |
  p ← Person.table,
  let eligible := p.age ≥ 18,
  eligible]

def adultsSQL (minimum : Int) := sql% [
  (p.name, p.age + 1) | p ← Person.table, p.age ≥ minimum]
```

生成器接受 `Source α`、`Query α`、普通 `List α` 和 `View α`。`←` 与 `<-` 使用同一个 Lean parser。结果、数据源、`let` 绑定、谓词都是原生 term；函数、闭包、`match`、记录和已有宏都由 Lean elaborator 处理。

`query% [...]` 产生原生 `Query α`；`sql% [...]` 使用相同的 comprehension，直接生成独立的 `SQL.Query`。两个入口都可直接作为函数实参，`query` 本身仍可用作普通标识符。已有查询定义或组合子表达式也可通过 `sql% adults minimum` 复用并下推。

`Query α` 是一个 baked 请求，`run : Database → Except String (List α)` 给出参考解释器。这里没有另造一套封闭的前端表达式 AST。SQL 适配器在 elaboration 时消费可见的 Lean 程序；捕获的参数仍在运行时计算、绑定。

`Query` 还提供 `map`、`filter`、`unionAll`、`distinct`、`sortBy`、`take`、`drop`、`count`、`sum`、`any`、`all`、`collect` 和 `groupBy`。例如：

```lean
def grouped := (Query.scan Person.table).groupBy (fun p => p.age)
def groupedSQL := sql% grouped

def names := (query% [p.name | p ← Person.table]).collect
```

`collect` 产生一个集合值，支持相关嵌套；SQL 适配器目前用嵌套集合表达式及 JSON 聚合／解码实现，没有逐行发查询。

Comprehension 的 clause 也可扩展，不必改中心 AST：

```lean
syntax "unless " term : queryQualifier
macro_rules
  | `(queryQualifier%[ unless $p:term ] $body:term) =>
    `(if $p then Query.empty else $body)
```

块语法同样提供 `query% { for p in Person.table; where ...; yield ... }` 和 `sql% { ... }`，共用 `queryBody%` 扩展点。

用带参数的 attribute 登记标量函数的 SQL 翻译：

```lean
attribute [sql_function "LOWER" 1] String.toLower

@[sql_function "LOWER" 1]
def lowerName (name : String) : String := name.toLower
```

这两种写法都登记全局规则，通过 `.olean` 持久化，导入声明规则的模块后即可用于 `sql%`。数值参数指定传给 SQL 函数的末尾实参数量，不包含前面的隐式类型参数。规则只影响 SQL 翻译，原生 `query%` 仍调用 Lean 函数。

## SQL 中端：复用 Lean 定义

中端不必经由前端编译器。下面的 `sql!` 直接构造 SQL，并让字段类型参与 Lean elaboration：

```lean
def eligible (minimum : Int) (p : Person.Columns SQL.Scalar) : SQL.Scalar Bool :=
  p.age >=. SQL.param minimum

def direct (minimum : Int) := sql! [
  SELECT (p.name, p.age + 1)
  FROM p IN Person.table
  WHERE eligible minimum p
  ORDER BY [p.id.asc]]
```

`FROM p IN source` 绑定 schema 自动生成的字段容器。用户直接写字段访问、普通函数、元组、记录更新；不重复声明列名与列类型。`direct` 的结果类型为 `SQL.Plan (String × Int)`，通过 `.fetch connection` 执行并解码；`.query`、`.statement` 可以取得公共 AST，也可在期望这些类型的位置自动转换。

算术复用 Lean 的 `+ - * /`，字符串拼接复用 `++`。比较和逻辑使用 `==. !=. <. <=. >. >=. &&. ||.`，因为它们构造 SQL 表达式，并不返回 Lean 的 `Bool`／`Prop`。可空比较的结果保留 `Option Bool`；`.isNull`／`.isNotNull`／`.coalesce` 提供显式 NULL 操作。

查询支持 typed source 的 `JOIN ... IN ... ON ...`、原生 term 投影、谓词、分组、排序和分页。谓词、投影、排序键和查询定义都可以放进普通函数复用。相关子查询用 `.exists_`；组合时共享别名生成器。

```lean
def birthdays := sql! [
  UPDATE p IN Person.table
  SET {p with age := p.age + 1}
  WHERE eligible 18 p]

def removeChildren := sql! [DELETE FROM p IN Person.table WHERE p.age <. 18]

-- rows : List Person；返回 Except String SQL.Statement，校验编码和键。
def insertPeople (rows : List Person) := sql! [INSERT INTO Person.table VALUES rows]
```

插入复用完整 Lean 记录和 schema 顺序；更新从记录更新生成有变化的赋值。它们直接生成 SQL DML，不经过 relational lens。

`sql! [...]` 使用 `syntax:max`，作为实参时不需要额外括号：

```lean
def prepared := SQL.render .sqlite sql! [
  SELECT p.name FROM p IN Person.table WHERE eligible 18 p]
```

## SQL 中端：接近 SQL 的完整语句构造入口

还可以直接表达 SQL 特有的结构，并拼接已有 term：

```lean
def minimumAge : Int := 18
def predicate := sql_expr! [age >= ${minimumAge}]
def queryPart := sql_query! [
  SELECT name FROM @{Person.schema} WHERE @{predicate}]
def statement := sql! [
  WITH grown AS (@{queryPart}) SELECT name FROM grown ORDER BY name]
```

这里 `sql!` 返回 `SQL.Statement`，`sql_query!` 返回 `SQL.Query`，`sql_expr!` 返回 `SQL.Expr`。`${term}` 编码为绑定参数；`@{term}` 拼接对应种类的 AST，FROM 位置也可拼接 `TableDef`。

当前语法覆盖 SELECT／DISTINCT、JOIN 与外连接、WHERE、GROUP BY／HAVING、ORDER BY、分页、集合运算、相关子查询、CTE／递归 CTE、CASE、CAST、IN／EXISTS、窗口表达式、INSERT VALUES／SELECT、UPDATE、DELETE、RETURNING、建表及约束、索引、视图、删表和事务控制 AST。函数调用可直接使用 SQL 函数名，不需要预先穷举函数集合。

字符串使用 Lean 的双引号字符串，标识符使用 Lean identifier。动态值应使用插值；DDL 中无法绑定的常量由各方言单独转义。此入口保留 SQL 的结构，不为原始列名、分组合法性提供完整的静态证明。高级特性也可直接组合 AST。

仅使用中端可以只导入 `LeanRel.Schema` 和 `LeanRel.SQL.NativeSyntax`；[Tests/MiddleOnly.lean](Tests/MiddleOnly.lean) 验证了这一依赖边界，并检查字段／类型错误。

## Relational lenses 与实际更新

```lean
def people := View.base Person.table
def adultsView := people.select (fun p => p.age ≥ 18)
def birthday := update [
  {p with age := p.age + 1} | p ← people, p.age ≥ 18]
```

`update` 中的 guard 只选择要修改的行，其余行保留。当前一次 comprehension 绑定一个 view；多表更新先组合 view。

提供基本表、selection、保留键的 projection、rename、带删除策略的 natural join。Projection 从旧数据恢复隐藏字段，新键必须提供默认值。Selection 根据函数依赖修订隐藏行。Join 要求共享字段能决定右侧，默认删除左侧，可显式选择 `.right`／`.both`；来源重叠的 self-join 更新被拒绝。

```lean
-- 以下放在 IO do 中：
-- let connection ← Backend.SQLite.connect ":memory:"
-- let _ ← IO.ofExcept (← Compiler.executeUpdate connection birthday)
```

`Compiler.executeUpdate` 读取所有相关 source 的一致快照，执行纯 Lean 更新逻辑，生成按键定位的 DML，并在一个写事务中检查读取快照和受影响行数后提交。快照变化，包括并发插入，返回冲突；出错回滚整个 batch。也可以使用 `request.run database` 查看变更，再用 `Compiler.applyUpdate` 提交指定快照。

这是使用运行时检查的部分 lens 实现：拒绝违反键／FD／selection predicate 的修改，并检查成功传播的 PutGet。它不是对任意 Lean 谓词自动推导出的 total lens。`LeanRel/Lens/Laws.lean` 证明了抽象 total lens 的恒等与复合规律；该证明不等于具体关系算法已经全部形式化证明。

## 后端及当前边界

`SQL.Connection` 由方言 renderer 和原子 batch runner 构成。SQLite 后端直接使用 leansqlite，复用原生连接；`:memory:` 在多次调用之间保留数据。连接内按整个事务加锁，lens 写事务使用 `BEGIN IMMEDIATE`。`Connection.execute` 自动管理事务，因此不要把 BEGIN／COMMIT 再作为 batch 中的语句执行。

PostgreSQL、SQLite、MySQL 有独立的参数占位符、引用／转义及能力检查。目前真实执行测试使用 SQLite；其他两种方言已测试渲染，尚未提供连接驱动或实际服务器测试。

当前需要明确保留的限制：

- 原生前端可运行任意合法的纯 Lean term，但 SQL 编译并非 Lean 通用求值器。可以展开的函数和已注册规则才能下推；黑盒运行时 `Query` 闭包不能重新反射成 SQL。
- SQL 适配器目前翻译 schema source、投影／过滤／join、集合并、排序分页、聚合、分组和嵌套集合。普通 List 生成器、任意 List 消费函数、直接对 `View.get` 的编译以及部分需要 LATERAL 的相关组合尚未实现；它们仍可在参考解释器执行。
- `[sql_function "SQL_NAME" n]` 可扩展标量函数规则。声明者负责保证语义对应，例如 Lean Unicode 小写转换与 SQLite 内置 LOWER 的适用范围不同。
- 编译器检查算术／比较实例，`BEq`、去重和分组需要对应的 `LawfulBEq`；排序目前接受标准 Int／Nat／String／Bool 的 `Ord`。自定义实例不会被默默替换为 SQL 默认运算。
- 未显式排序的 SQL 查询不保证与内存 List 的遍历顺序一致。查询保留重复项；lens 使用有键集合语义。
- Lean Int 没有位数上限，数据库数值、字符串排序、NULL 运算有各自语义。SQLite 绑定检查整数范围；SQL 算术不是无限精度 Lean Int 的完整实现。
- 嵌套集合目前经由 JSON 传递，不支持其中的 BLOB；MySQL 的有序嵌套集合会明确报能力错误。没有实现 DSH 的完整 shredding／优化流水线。
- 尚未覆盖 SQL 标准和各数据库扩展的全集，也没有迁移系统、增量 lens 优化或整个 SQL 编译器的语义保持证明。

设计取舍和研究对应见 [docs/design.md](docs/design.md)。
