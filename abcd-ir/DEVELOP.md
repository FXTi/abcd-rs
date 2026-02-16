# abcd-ir 开发文档

## 概述

abcd-ir 是字节码与高级表示之间的桥梁，提供双向转换能力：

- 字节码 → IR（lifting）：已实现，用于反编译
- IR → 字节码（lowering）：待实现，用于重编译/patch

## 当前模块

- `instruction` — 解码指令表示（`Instruction`、`Operand`、`TryBlockInfo`）
- `expr` — 表达式 AST（`Expr`）
- `stmt` — 语句 AST（`Stmt`）
- `cfg` — 控制流图（`CFG`、`BasicBlock`）

## IR Lowering 设计（待实现）

### 版本感知的 Opcode 选择

arkcompiler 的 `isa.yaml` 不包含 per-opcode 版本标注。es2panda 在编译器语义层
硬编码版本门控，例如：

```cpp
// es2panda/util/helpers.h
static constexpr int SENDABLE_CLASS_MIN_SUPPORTED_API_VERSION = 11;
static constexpr int SENDABLE_FUNCTION_MIN_SUPPORTED_API_VERSION = 12;
static constexpr int SUPER_CALL_OPT_MIN_SUPPORTED_API_VERSION = 18;
```

编译器在 emit 时根据 `targetApiVersion` 选择不同 opcode：

```cpp
// API >= 18 用优化版本，否则用通用版本
if (targetApiVersion >= SUPER_CALL_OPT_MIN_SUPPORTED_API_VERSION) {
    Emit<SuperCallOpt>(...);
} else {
    Emit<SuperCall>(...);
}
```

### 我们的分层

```
IR lowering (abcd-ir)          →  根据目标 API level 选择 opcode
  ↓
Emitter (abcd-isa)             →  把 opcode 编码成 bytes
  ↓
AbcFileBuilder (abcd-file)     →  把 bytes 打包进 .abc 容器
```

abcd-isa 提供版本查询 API，abcd-ir 的 lowering 阶段调用它来做决策：

```rust
// 伪代码
let target_version = abcd_isa::version_by_api(target_api_level);

// lowering 时选择 opcode
match ir_node {
    IR::SuperCall { .. } if target_api >= 18 => {
        emitter.emit_supercallopt(args);
    }
    IR::SuperCall { .. } => {
        emitter.emit_supercall(args);
    }
    // ...
}
```

abcd-isa 不需要知道"SuperCallOpt 只在 API 18+ 可用"——它只管忠实编码。
版本感知的 opcode 选择是 IR lowering 的职责。

### 设计要点

1. Lowering 接收目标 API level 作为参数
2. 通过 `abcd_isa::version_by_api()` 获取对应的 ISA 版本
3. 按语义特性（不是按 opcode）做版本分支
4. 输出 `abcd_isa::Emitter` 调用序列
5. 最终由 `abcd_file::AbcFileBuilder` 打包成 .abc 文件
