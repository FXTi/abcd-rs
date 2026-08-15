# 总体架构

## 定位

abcd-rs 是 ArkCompiler ABC 字节码（`.abc`）的 Rust 工具链：**读、写、检查，以及基于 SSA IR 的分析与变换**。目标不是反编译器（第一代的 decompile 方向已移除），而是把"到 IR 层为止"的基础设施做坚实：任何人要在此之上做优化器、分析器、patch 工具或未来的反编译器，都能直接站在 IR 上。

## 仓库结构

```
abcd-rs/
├── design/                  # 本目录：设计文档
├── abcd-isa-sys/            # ISA FFI 层（Ruby 代码生成 + C++ bridge + bindgen）
├── abcd-isa/                # ISA safe Rust API（解码/编码/版本/分类）
├── abcd-file-sys/           # 容器格式 FFI 层（libpandafile + C bridge + bindgen）
├── abcd-file/               # 容器 safe Rust API（decode/encode/Builder）
└── abcd-ir/                 # SSA 中间表示（lift / opt / lower）
```

五个 crate，全部为库。依赖关系严格分层：

```
abcd-isa-sys ──▶ abcd-isa ──┐
                             ├──▶ abcd-file ──▶ abcd-ir
abcd-file-sys ───────────────┘
```

即：`abcd-ir` 依赖 `abcd-file` + `abcd-isa`；`abcd-file` 依赖 `abcd-file-sys` + `abcd-isa`；两个 `-sys` 是叶子。

## 数据流

```
.abc 字节
   │  abcd-file::decode          （依赖 abcd-isa 解码字节码）
   ▼
File（owned：classes / literal_arrays / entity_map / StringPool）
   │  abcd-ir::lift::lift_file
   ▼
Module（SSA IR：functions / insts / blocks / values）
   │  abcd-ir::opt::optimize_module
   ▼
Module（优化后）
   │  abcd-ir::lower::lower_function（每函数：regalloc → isel → layout）
   ▼
Bytecode 序列 + try blocks
   │  abcd-file::encode / Builder
   ▼
.abc 字节
```

关键不变量：**IR 保留所有元数据**（注解四类、debug info、try 区域、函数 kind、访问标志），为语义等价 round-trip 服务。字节级 round-trip 不是目标（builder 自行决定布局）。

## 版本感知的分层设计

arkcompiler 的 ISA 不携带 per-opcode 版本标注；es2panda 在编译器语义层硬编码门控（如 `SENDABLE_CLASS_MIN_SUPPORTED_API_VERSION = 11`）。我们把这个职责分到三层：

| 层 | Crate | 职责 |
|----|-------|------|
| 版本查询 | abcd-isa | `Version`：current/min/api 映射/兼容性/黑名单 |
| 文件布局 | abcd-file | 版本条件化的 section 布局（如 12.0.6.0 之前 literal array 索引在 header 中） |
| opcode 选择 | abcd-ir | lowering 时按目标 API level 选 opcode（见 ir.md） |

原则：`abcd-isa` 只忠实编码调用者给的 opcode，不做任何"该用哪个 opcode"的决策。

## 当前状态

| Crate | 读 | 写 | 备注 |
|-------|----|----|------|
| abcd-isa-sys | ✅ | ✅（Emitter FFI） | 由 Ruby 管线生成 |
| abcd-isa | ✅ | ✅ | 长跳转由 C++ emitter 自动扩宽 |
| abcd-file-sys | ✅ | ✅（Builder FFI） | ~170 个桥函数 |
| abcd-file | ✅ | ⚠️ | `encode()` 语义 roundtrip 已实现但被禁用（C++ dedup 崩溃，见 file-format.md 已知限制） |
| abcd-ir | ✅ lift | ✅ lower | 优化管线可用；若干近似实现（见 ir.md 已知缺口） |

## 参考样本

开发基准文件是 `modules.abc`（21.6MB，version 12.0.6.0，2035 类 / 29147 字面量数组 / 15738 行号程序 / 2 个索引头），不随仓库分发（`.gitignore` 的 `*.abc`）。
