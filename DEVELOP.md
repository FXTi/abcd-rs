# abcd-rs 开发文档

ArkCompiler ABC 字节码工具链的 Rust 实现。

## 工作流

```
.abc 文件  →  解析  →  字节码解码  →  IR  →  反编译  →  源码
源码/IR    →  IR lowering  →  汇编  →  .abc 文件写入
```

## Crate 分工

### abcd-isa — 指令集架构

单条指令粒度的一切：

- Opcode 定义、格式、操作数类型（从 vendor isa.yaml 生成）
- 字节码解码：`decode_opcode()`、operand 提取（`get_vreg`/`get_imm64`/`get_id`）
- 字节码编码：`Emitter`（封装 vendor BytecodeEmitter）
- 反汇编：`format_instruction()`
- ISA 版本元数据：`current_version()`、`min_version()`、`version_by_api()`、`is_version_compatible()`

不负责决定"该用哪个 opcode"——只忠实编码调用者给它的任何 opcode。

### abcd-file — ABC 文件容器格式

.abc 二进制容器的读写：

- 文件解析：header、class、method、code、literal array、annotation、debug info、module record
- String table（MUTF-8 编码）
- Index section 解析（16-bit index → 32-bit offset）
- 版本条件化的文件布局差异（literal array 位置、proto index 等）
- 文件写入：AbcFileBuilder（待实现）

### abcd-ir — 中间表示

字节码与高级表示之间的桥梁：

- 解码指令表示：`Instruction`、`Operand`
- 表达式 AST：`Expr`（字面量、二元/一元运算、调用、成员访问等）
- 语句 AST：`Stmt`（if、while、for-in/of、try-catch、switch、return 等）
- 控制流图：`CFG`、`BasicBlock`
- IR lowering（待实现）：版本感知的 opcode 选择

### abcd-decompiler — 反编译器

IR → 源码的完整管线：

- 字节码解码（调用 abcd-isa）
- CFG 构建与结构化
- 表达式恢复
- JavaScript 源码输出

### abcd-cli — 命令行工具

用户界面：

- `info`：显示 .abc 文件元数据
- `disasm`：反汇编为可读文本
- `decompile`：反编译为 JavaScript

## 依赖图

```
abcd-isa
  ↑
  ├── abcd-file
  │     ↑
  │     └── abcd-decompiler ← abcd-cli
  │           ↑
  └── abcd-ir ┘
```

## 版本感知的分层设计

arkcompiler ISA 的 opcode 没有 per-opcode 版本标注。es2panda 在编译器语义层硬编码版本门控
（如 `SENDABLE_CLASS_MIN_SUPPORTED_API_VERSION = 11`）。

对我们来说，版本感知分布在三层：

| 层 | Crate | 职责 |
|---|---|---|
| 版本查询 | abcd-isa | 提供 `version_by_api()`、`is_version_compatible()` |
| 文件格式 | abcd-file | 版本条件化的 section 布局（header 结构、literal array 位置） |
| Opcode 选择 | abcd-ir | IR lowering 时根据目标 API level 选择 opcode |

## 当前状态

| Crate | 读/解码 | 写/编码 |
|---|---|---|
| abcd-isa | ✅ 解码 + 反汇编 | ✅ Emitter + 版本 API |
| abcd-file | ✅ 完整解析 | ❌ AbcFileBuilder 待实现 |
| abcd-ir | ✅ 指令/表达式/语句/CFG | ❌ IR lowering 待实现 |
| abcd-decompiler | ✅ 部分反编译 | — |
