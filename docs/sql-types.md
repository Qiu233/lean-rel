# SQL 类型支持

当前尚未完整支持 SQL 类型。需要分别看中端能否表达一个类型、schema 能否生成对应的 Lean 字段，以及后端能否正确编码、运算和解码。`SQL.SqlType` 中存在一个构造器，只说明第一层已有表示。

## 当前实现

| SQL 类型／类型族 | schema 的 Lean 类型 | 中端与执行情况 |
| --- | --- | --- |
| `BIGINT`、`INTEGER` | `Int` | typed schema、参数和结果均已支持；当前两种 SQL 拼写合并为 `.integer`，均渲染为 `BIGINT`，尚未保留宽度区别 |
| 浮点数 | `Float` | typed schema、参数和结果已支持；当前 `REAL` 语法使用 `.real`，渲染为 `DOUBLE PRECISION`，尚未区分单精度与双精度 |
| `BOOLEAN` | `Bool` | 已支持；SQLite 通过整数 0／1 编码，快照读取会还原布尔值 |
| `TEXT` | `String` | 已支持文本参数及结果 |
| `BLOB` | `Array UInt8` | 已支持；PostgreSQL renderer 使用 `BYTEA` |
| 可空列 | `Option α` | 已支持；schema 的空值性由 Lean 类型决定 |
| `VARCHAR(n)` | 尚无保存长度约束的专用映射 | 仅中端语法／AST／渲染；schema 的 `String` 生成 `TEXT` |
| `DECIMAL(p,s)` | 尚无精确十进制类型及 codec | 仅中端语法／AST／渲染；精度、scale 和精确值还没有贯穿 typed schema 与执行 |
| `DATE`、`TIMESTAMP` | 尚无专用映射 | 仅中端语法／AST／渲染；日期校验、时间精度和时区语义尚未接入 |
| `SMALLINT`、`CHAR`、`BINARY`、`VARBINARY`、LOB、bit string 等 | 未完整建模 | 部分可通过基础表示存储，但没有相应的完整 SQL 类型语法和语义 |
| `TIME`、带时区时间／时间戳、`INTERVAL` | 未接入 | 中端类型及 typed schema 都待实现 |
| SQL 数组、row／structured type、multiset | 未接入为数据库列类型 | 查询结果里的 `List`／记录已有 codec；这不等于支持 SQL 集合／复合列 |
| JSON、XML | 未接入为数据库列类型 | 嵌套查询当前用 JSON 传输结果；尚无对应的数据库列类型及操作体系 |
| domain、用户定义类型、数据库扩展类型 | 未接入 | 没有 SQL 类型名称到 Lean 表示的自动映射，也没有方言专属 codec |

对应实现见 [ScalarType／Codec／ColumnType](../LeanRel/Data.lean)、[SQL AST](../LeanRel/SQL/Ast.lean)、[SQL parser](../LeanRel/SQL/Syntax.lean)、[renderer](../LeanRel/SQL/Render.lean)和 [SQLite binding](../LeanRel/Backend/SQLite.lean)。`Nat` 有结果／参数 codec，但没有内置 `ColumnType Nat` instance。

`Int` 可以作为 `BIGINT` 的 Lean 表示。Lean 的 `Int` 不限位数，SQLite 的整数存储和绑定是有符号 64 位，因此现有 binding 会拒绝越界输入。浮点和精确十进制需要不同表示：`DECIMAL`／`NUMERIC` 的精确语义不能由 `Float` 保证。[PostgreSQL 数值类型](https://www.postgresql.org/docs/current/datatype-numeric.html)

SQLite 接受类型名称，并不意味着它实现了其他数据库相同的类型语义。例如 `VARCHAR(n)` 不会限制字符串长度，`DECIMAL` 使用 numeric affinity，日期时间可存成文本或数值，SQLite 没有独立的日期时间 storage class。[SQLite 类型系统](https://www.sqlite.org/datatype3.html)

## 为什么保留 Lean 类型

SQL 的内建类型构造器可以静态枚举，参数化类型可以递归表示；完整 SQL 类型世界则允许用户增加类型名称。标准包含 `CREATE DOMAIN` 和 `CREATE TYPE` 的复合类型形式。[CREATE DOMAIN](https://www.postgresql.org/docs/current/sql-createdomain.html)、[CREATE TYPE](https://www.postgresql.org/docs/current/sql-createtype.html)

因此，若输入任意 SQL 类型名称并要求自动生成 Lean 字段，仍需可扩展的名称解析和表示映射。这可以在编译期完成，不要求运行时维护一张表，但无法仅靠固定的内建类型分支覆盖。schema 目前保留 Lean term，复用 Lean 的类型定义、命名空间和 instance 解析。

现有 `ColumnType` 的扩展能力也有边界：新 Lean 类型可以映射到已有 `ScalarType` 并提供 codec；它还不能凭一个 instance 新增原生 SQL `DECIMAL`、domain 或数组列。要支持这些类型，需要一起扩展中间数据表示、SQL 类型描述、方言能力和后端编码。

后续优先补精确十进制、日期／时间／interval、长度及数值宽度；再处理递归复合类型和用户定义类型。每项都需要明确原生 Lean 运算、SQL 运算、NULL 和后端编码之间的对应关系。
