# abcd-ir

ArkCompiler ABC 字节码的 SSA 中间表示。

支持完整的 round-trip：从 ABC 字节码提升（lift）到 SSA IR，经过优化管线，再降低（lower）回 ABC 字节码，保持元数据保真。

## 架构总览

```
                        ┌─────────────────────────┐
                        │      Optimization        │
                        │  peephole → sccp → adce  │
                        │  → copyprop → peephole   │
                        │  → adce                  │
ABC Bytecode ──[Lift]──▶│      SSA IR (Module)     │──[Lower]──▶ ABC Bytecode
                        │                          │
                        │  analysis: domtree,      │
                        │  usedef, RPO, succs      │
                        └─────────────────────────┘
```

三大子系统：

| 子系统 | 目录 | 职责 |
|--------|------|------|
| **Lift** | `lift/` | 字节码 → SSA IR（CFG 构建 + Braun SSA） |
| **Opt** | `opt/` | 优化管线（SCCP、ADCE、Peephole、CopyProp） |
| **Lower** | `lower/` | SSA IR → 字节码（寄存器分配 + 指令选择 + 布局） |

## 核心数据结构

### Arena 索引模型

所有 IR 实体使用 `u32` 索引引用，存储在 `Module` 的 `Vec` arena 中：

```rust
Value(u32)    // SSA 值：%v_0, %v_1, ...
Block(u32)    // 基本块：%bb_0, %bb_1, ...
Inst(u32)     // 指令：%i_0, %i_1, ...
FuncId(u32)   // 函数：%fn_0, %fn_1, ...
StringId(u32) // 字符串：%s_0, %s_1, ...
ClassId(u32)  // 类：%cls_0, %cls_1, ...
```

每个索引类型提供 `INVALID`（`u32::MAX`）、`index()`、`from_index()`、`is_valid()` 方法。

### Module — 顶层容器

```rust
pub struct Module {
    // 文件级元数据
    pub version: Version,
    pub file_type: FileType,

    // 模块级数据
    pub classes: Vec<ClassData>,
    pub literal_arrays: Vec<LiteralArray>,
    pub module_data: Vec<ModuleData>,

    // 函数体 IR（arena 存储）
    pub functions: Vec<FunctionData>,
    pub insts: Vec<InstNode>,
    pub blocks: Vec<BasicBlockData>,
    pub values: Vec<ValueData>,

    // 共享资源
    pub strings: StringPool,
}
```

### FunctionData — 函数体

```rust
pub struct FunctionData {
    pub name: String,
    pub kind: FunctionKind,        // Function, Arrow, Generator, Async, ...
    pub param_count: u16,
    pub entry_block: Block,
    pub blocks: Vec<Block>,
    pub try_regions: Vec<TryRegion>,  // 异常处理区域
    pub annotations: IrAnnotations,
    pub debug: Option<FuncDebugInfo>,
    // ...
}
```

### InstData — 指令枚举

~70 个 variant，覆盖所有 JS/TS/ArkTS 操作：

| 类别 | 指令 |
|------|------|
| 字面量 | `LiteralUndefined`, `LiteralNull`, `LiteralBool`, `LiteralNumber`, `LiteralString`, `LiteralNaN`, `LiteralInfinity`, `LiteralHole` |
| 二元运算 | `BinaryOp { op, left, right }` — Add/Sub/Mul/Div/Mod/Exp/Eq/Less/Shl/BitAnd/In/InstanceOf 等 22 种 |
| 一元运算 | `UnaryOp { op, operand }` — Minus/BitNot/LogicalNot/Inc/Dec/TypeOf/ToNumber/Void 等 |
| 对象创建 | `CreateEmptyObject`, `CreateEmptyArray`, `CreateObjectWithBuffer`, `CreateArrayWithBuffer`, `CreateRegExp` |
| 属性访问 | `LoadProperty`, `StoreProperty`, `StoreOwnProperty`, `DeleteProperty`, `LoadSuperProperty`, `StoreSuperProperty` |
| 全局变量 | `LoadGlobalVar`, `StoreGlobalVar`, `TryLoadGlobalByName`, `TryStoreGlobalByName` |
| 词法变量 | `LoadLexVar`, `StoreLexVar`, `NewLexEnv`, `PopLexEnv` |
| 模块变量 | `LoadLocalModuleVar`, `LoadExternalModuleVar`, `StoreModuleVar`, `DynamicImport` |
| 函数定义 | `DefineFunc`, `DefineMethod`, `DefineClassWithBuffer` |
| 调用 | `Call { kind, callee, args }` — Call/CallThis/SuperCall/Apply 等 |
| 生成器/异步 | `CreateGeneratorObj`, `SuspendGenerator`, `ResumeGenerator`, `AsyncFunctionEnter`, `AsyncFunctionAwaitUncaught` 等 |
| 异常 | `Throw`, `ThrowIfNotObject`, `ThrowConstAssignment`, `ThrowUndefinedIfHole` 等 |
| 控制流 | `Branch`, `CondBranch`, `Return`, `Unreachable` |
| SSA | `Phi { entries: Vec<(Block, Value)> }` |

关键方法：
- `operands_mut()` — 返回所有 `Value` 操作数的可变引用
- `is_terminator()` — 是否为终结指令
- `is_phi()` — 是否为 Phi 节点
- `has_result()` — 是否产生结果值

### IrType — 双类型系统

```rust
pub enum IrType {
    Dynamic(DynType),  // JS/TS 动态类型（bitmask）
    Static(AbcType),   // ArkTS 静态类型
}
```

`DynType` 是 `u16` bitmask，支持 union/intersect/subset 操作：

```
EMPTY | UNDEFINED | NULL | BOOLEAN | NUMBER | STRING | BIGINT | SYMBOL | OBJECT | ENVIRONMENT
```

## 模块说明

### `entity.rs` — 类型化索引

用 `define_entity!` 宏定义所有索引类型。每个类型是 `u32` newtype，实现 `Copy`、`Eq`、`Hash`、`Display`。避免了 Rust 中 LLVM 风格指针继承树的生命周期问题。

### `types.rs` — 类型系统

`DynType` 的 bitmask 设计允许高效的类型格操作：

```rust
let ty = DynType::NUMBER.union(DynType::STRING);  // number | string
ty.can_be(DynType::NUMBER)  // true
ty.is_subset_of(DynType::ANY)  // true
```

### `inst.rs` — 指令定义

`InstData` 枚举的每个 variant 直接包含操作数（无间接指针）。`operands_mut()` 方法提供统一的可变操作数访问，使 `replace_uses_in_func` 从 ~80 行 match 简化为 4 行循环。

### `module.rs` — 模块容器

所有 IR 数据集中存储在 `Module` 的 arena 中。`StringPool` 提供字符串去重和 intern。`InstNode` 包装 `InstData` 并附加 result value、类型、所属 block 和源码位置。

### `builder.rs` — IR 构建器

```rust
let func = IRBuilder::create_function(&mut module, "foo", FunctionKind::Function, 2);
let mut b = IRBuilder::new(&mut module, func);

let bb0 = b.create_block();
b.set_insert_block(bb0);

let v0 = b.emit_val(InstData::LiteralNumber(42.0), IrType::Dynamic(DynType::NUMBER));
let v1 = b.emit_val(InstData::BinaryOp {
    op: BinOp::Add, left: v0, right: v0,
}, IrType::Dynamic(DynType::NUMBER));
b.emit_void(InstData::Return(Some(v1)));
```

### `display.rs` — IR 打印

`module.display_func(func_id)` 和 `module.display()` 输出可读的文本 IR：

```
function foo(2) {
  %bb_0:
    %v_0 = LiteralNumber 42.0
    %v_1 = LiteralString "hello"
    %v_2 = BinaryOp Add %v_0, %v_1
    CondBranch %v_2, %bb_1, %bb_2
  %bb_1:                           ; preds: %bb_0
    Return %v_0
  %bb_2:                           ; preds: %bb_0
    Return %v_1
}
```

### `verify.rs` — IR 验证

`verify_func` / `verify_module` 检查 IR 合法性：
- 每个块以终结指令结尾
- Phi 节点仅出现在块开头
- Phi 入口数量匹配前驱数量
- 入口块无前驱
- 值在使用前已定义
- 终结指令的后继引用有效块

### `analysis/` — 分析基础设施

**`analysis/mod.rs`** — CFG 工具函数：

| 函数 | 用途 |
|------|------|
| `compute_rpo(module, func_id)` | 计算逆后序（Reverse Post-Order） |
| `block_succs(module, block)` | 获取基本块的后继 |
| `inst_operands(data)` | 获取指令的所有 Value 操作数 |
| `replace_uses_in_func(module, func_id, old, new)` | 替换函数内所有 old → new 的使用 |

**`analysis/domtree.rs`** — Semi-NCA 支配树（Georgiadis 2005）：

```rust
let dom = DomTree::build(&module, func_id);
dom.idom(block)           // 直接支配者
dom.dominates(a, b)       // a 是否支配 b（自反）
```

迭代式 DFS 编号 → Lengauer-Tarjan 半支配者 → 路径压缩 → 深度计算。

**`analysis/usedef.rs`** — Use-def 链：

```rust
let ud = UseDef::build(&module, func_id);
ud.uses_of(val)    // 使用该值的所有指令
ud.use_count(val)  // 使用次数
ud.is_used(val)    // 是否被使用
```

按需构建（`HashMap<Value, Vec<Inst>>`），不需要时零开销。

### `lift/` — 字节码 → IR

**流程：**

```
ABC Method → [cfg.rs] CFG 构建 → [ssa.rs] Braun SSA → [translate.rs] 指令翻译 → FunctionData
```

**入口：**

```rust
let module = lift_file(&abc_file)?;                          // 提升整个文件
let func_id = lift_method(&abc_file, &method, &mut module)?; // 提升单个方法
```

**`lift/cfg.rs`** — 四阶段 CFG 构建：

1. **识别 leaders**：入口点、跳转目标、跳转后指令、catch handler 入口
2. **划分基本块**：按 leader 切分字节码序列
3. **计算后继**：跳转 → 目标块，条件跳转 → 目标 + fall-through
4. **异常边**：try block 覆盖的块添加 catch_succs

**`lift/ssa.rs`** — Braun SSA 构建（Braun et al. 2013）：

核心接口：
- `write_variable(reg, block, value)` — 在块中记录变量定义
- `read_variable(reg, block)` — 读取变量（自动插入 Phi）
- `seal_block(block)` — 标记块的所有前驱已知，完成未决 Phi

算法特点：
- 从字节码直接构建 SSA，无需中间 alloca/load/store 表示
- 内建 trivial phi 消除（所有操作数相同时直接替换）
- 使用 `RegOrAcc` 统一处理累加器和虚拟寄存器

**`lift/translate.rs`** — 字节码到 IR 指令的逐条翻译。

**`lift/resolve.rs`** — 字节码实体 ID 到 IR 实体 ID 的映射。

### `opt/` — 优化管线

**`FuncPass` trait：**

```rust
pub trait FuncPass {
    fn run(&self, module: &mut Module, func: FuncId) -> bool;  // 返回是否修改
}
```

**默认管线（`optimize_func`）：**

```
peephole → sccp → adce + cfg_simplify → copyprop → peephole → adce + cfg_simplify
```

**各 pass 说明：**

| Pass | 文件 | 算法 | 效果 |
|------|------|------|------|
| **Peephole** | `peephole.rs` | 局部常量折叠 | 折叠算术/比较运算、消除 identity 操作 |
| **SCCP** | `sccp.rs` | Wegman-Zadeck 1991 | 全局常量传播 + 不可达分支折叠 |
| **ADCE** | `dce.rs` | 反向标记-清除 | 删除无副作用的死指令 |
| **CFG Simplify** | `dce.rs` | 块合并 + 跳转消除 | 合并单前驱/单后继块、消除空跳转块、删除不可达块 |
| **CopyProp** | `copyprop.rs` | Trivial phi 消除 | 消除所有操作数相同的 Phi 节点 |
| **Inline** | `inline.rs` | 调用点内联 | 小函数内联（未启用，需手动调用） |

### `lower/` — IR → 字节码

**流程：**

```
FunctionData → [regalloc.rs] 寄存器分配 → [isel.rs] 指令选择 → [layout.rs] 布局 → ABC Bytecode
```

**入口：**

```rust
let result = lower_function(&module, func_id)?;
// result.bytecodes: Vec<Bytecode>
// result.ic_size: u16
// result.num_regs: u16
```

**`lower/regalloc.rs`** — SSA 弦图着色寄存器分配：

五个阶段：
1. **活跃性分析**：精确后向数据流，迭代至收敛
2. **干涉图构建**：从 live_out 反向扫描，SSA 保证弦图性质
3. **累加器偏好评分**：启发式决定值分配到 acc 还是寄存器
4. **MCS + 贪心着色**：Maximum Cardinality Search 排序 → 逆序贪心着色，保证最优着色数
5. **Boissinot SSA destruction**：同色 Phi 操作数直接 coalesce，异色插入并行 copy

累加器偏好评分规则：

| 条件 | 分数 |
|------|------|
| 指令结果（自然产生到 acc） | +2 |
| BinOp 左操作数（自然在 acc） | +2 |
| 作为寄存器操作数使用（call/store） | -3 |
| 使用次数 > 2（长生命周期） | -5 |

**`lower/isel.rs`** — 指令选择：

- **IC 槽分配**：per-function 计数器，属性访问/调用分配 2 槽，算术/全局分配 1 槽
- **累加器管理**：`ensure_acc()` 加载值到 acc，`val_reg()` 确保值在寄存器，`store_result()` 存储 acc 到目标寄存器
- **比较分支融合**：`CondBranch(IsTrue(Eq(a, b)))` → `Jeq(reg, label)`，支持 Eq/NotEq/StrictEq/StrictNotEq

**`lower/layout.rs`** — 块布局和跳转解析：

- RPO 顺序排列基本块
- fall-through 优化（省略不必要的跳转）
- 重建 try block（从 `TryRegion` + block offsets 计算指令索引）

## 关键算法

### Braun SSA 构建 vs Mem2Reg

传统方案（如 Hermes）从 AST 生成非 SSA IR（alloca/load/store），再通过 Mem2Reg 提升到 SSA。abcd-ir 从字节码出发，用 Braun 算法一步到位：

| | Braun（abcd-ir） | Mem2Reg（Hermes） |
|--|------------------|-------------------|
| 输入 | 字节码（已是寄存器形式） | AST |
| 中间表示 | 无 | alloca/load/store IR |
| Phi 插入 | 按需（read_variable 时） | 支配边界计算 |
| Trivial phi 消除 | 内建 | 需额外 pass |
| 复杂度 | O(n) | O(n) + 额外 pass |

### SSA 弦图着色 vs 线性扫描

SSA 程序的干涉图是弦图（chordal graph）。弦图的最优着色可以在多项式时间内求解：

1. **MCS 排序**：Maximum Cardinality Search 产生完美消除序列
2. **逆序贪心着色**：按 MCS 逆序分配颜色，保证最优着色数

对比线性扫描（Hermes）：线性扫描是近似算法，可能产生不必要的 spill。对于 ABC 字节码（寄存器字段 16 位，65536 个寄存器），最优着色 = 最少寄存器数 = 更小的栈帧。

### Boissinot SSA Destruction

Phi 消除策略：

1. 同色 Phi 操作数 → 直接 coalesce（零 copy）
2. 异色操作数 → 在前驱块末尾插入并行 copy
3. 并行 copy 解析 → 拓扑排序 + 环检测（用临时寄存器打破环）

对比 Hermes 的 "先插 Mov 再消除" 方案，Boissinot 方法产生更少的 copy 指令。

### IC 槽分配

Inline Cache 是 JS 引擎的运行时优化。IC 槽 ID 作为立即数编码在 ABC 指令操作数中。

分配策略：

| 指令类别 | 槽数量 | 示例 |
|----------|--------|------|
| 属性访问（by name/value/index） | 2 | `ldobjbyname`, `stobjbyvalue` |
| 函数调用 | 2 | `callarg0`-`callrange` |
| 迭代器 | 2 | `getiterator`, `closeiterator` |
| 算术/比较运算 | 1 | `add2`, `eq`, `less` |
| 全局变量 | 1 | `ldglobalvar`, `tryldglobalbyname` |
| 对象/数组创建 | 1 | `createemptyarray` |
| 函数/类定义 | 1 | `definefunc` |

### 比较分支融合

将分离的比较 + 条件跳转融合为单条指令：

```
// 融合前：
%v2 = BinaryOp Eq %v0, %v1
%v3 = IsTrue %v2
CondBranch %v3, %bb_true, %bb_false

// 融合后（字节码）：
jeq r1, label_true    // acc = %v0, r1 = %v1
```

支持 `Eq → Jeq`、`NotEq → Jne`、`StrictEq → Jstricteq`、`StrictNotEq → Jnstricteq`。

## 使用示例

### 提升整个 ABC 文件

```rust
use abcd_file::File;
use abcd_ir::lift::lift_file;

let file = File::parse(&bytes)?;
let module = lift_file(&file)?;

// 打印所有函数的 IR
println!("{}", module.display());
```

### 优化 + 降低

```rust
use abcd_ir::opt::optimize_module;
use abcd_ir::lower::lower_function;

optimize_module(&mut module);

for func_id in 0..module.functions.len() {
    let func_id = FuncId::from_index(func_id);
    if module.functions[func_id.index()].is_external {
        continue;
    }
    let result = lower_function(&module, func_id)?;
    // result.bytecodes, result.ic_size, result.num_regs
}
```

### 手动构建 IR

```rust
use abcd_ir::*;
use abcd_ir::builder::IRBuilder;

let mut module = Module::default();
let func = IRBuilder::create_function(&mut module, "add", FunctionKind::Function, 2);
let mut b = IRBuilder::new(&mut module, func);

let entry = b.create_block();
b.set_insert_block(entry);

let p0 = b.create_func_param(0, IrType::Dynamic(DynType::ANY));
let p1 = b.create_func_param(1, IrType::Dynamic(DynType::ANY));
let sum = b.emit_val(
    InstData::BinaryOp { op: BinOp::Add, left: p0, right: p1 },
    IrType::Dynamic(DynType::NUMBER),
);
b.emit_void(InstData::Return(Some(sum)));
```

### 验证 IR

```rust
use abcd_ir::verify::verify_module;

let errors = verify_module(&module);
for e in &errors {
    eprintln!("{}: {}", e.func, e.message);
}
assert!(errors.is_empty());
```

## 目录结构

```
abcd-ir/
├── Cargo.toml
└── src/
    ├── lib.rs          # 公共 API 和模块导出
    ├── entity.rs       # 类型化索引（Value, Block, Inst, ...）
    ├── types.rs        # 类型系统（IrType, DynType）
    ├── inst.rs         # 指令定义（InstData 枚举）
    ├── module.rs       # 顶层容器（Module, FunctionData, ...）
    ├── builder.rs      # IR 构建器 API
    ├── display.rs      # IR 文本打印
    ├── verify.rs       # IR 合法性验证
    ├── analysis/
    │   ├── mod.rs      # CFG 工具（RPO, succs, operands）
    │   ├── domtree.rs  # Semi-NCA 支配树
    │   └── usedef.rs   # Use-def 链
    ├── lift/
    │   ├── mod.rs      # 入口：lift_file, lift_method
    │   ├── cfg.rs      # CFG 构建
    │   ├── ssa.rs      # Braun SSA 构建
    │   ├── translate.rs # 字节码 → IR 翻译
    │   └── resolve.rs  # 实体 ID 解析
    ├── opt/
    │   ├── mod.rs      # FuncPass trait, 管线定义
    │   ├── peephole.rs # 常量折叠
    │   ├── sccp.rs     # 稀疏条件常量传播
    │   ├── dce.rs      # ADCE + CFG 简化
    │   ├── copyprop.rs # Copy 传播
    │   └── inline.rs   # 函数内联（未启用）
    └── lower/
        ├── mod.rs      # 入口：lower_function
        ├── regalloc.rs # SSA 弦图着色寄存器分配
        ├── isel.rs     # 指令选择 + IC 分配
        └── layout.rs   # 块布局 + 跳转解析

```

## 依赖

| Crate | 用途 |
|-------|------|
| `abcd-isa` | ArkCompiler 指令集定义（操作码、编码） |
| `abcd-file` | ABC 文件格式解析（File, Method, Bytecode） |
| `thiserror` | 错误类型派生 |

## 参考文献

- Braun, M., Buchwald, S., Hack, S., Leißa, R., Mallon, C., & Zwinkau, A. (2013). *Simple and Efficient Construction of Static Single Assignment Form*. CC 2013.
- Wegman, M. N., & Zadeck, F. K. (1991). *Constant Propagation with Conditional Branches*. ACM TOPLAS.
- Georgiadis, L. (2005). *Linear-Time Algorithms for Dominators and Related Problems*. PhD thesis.
- Boissinot, B., Darte, A., Rastello, F., de Dinechin, B. D., & Guillon, C. (2009). *Revisiting Out-of-SSA Translation for Correctness, Code Quality, and Efficiency*. CGO 2009.
- Hack, S. (2007). *Register Allocation for Programs in SSA Form*. PhD thesis, Universität Karlsruhe.
