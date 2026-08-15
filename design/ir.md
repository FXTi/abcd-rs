# SSA IR 设计（abcd-ir）

## 目标与原则

- **双向**：bytecode → IR（lift）与 IR → bytecode（lower）都是真实实现，不是占位。
- **SSA 全程**：lift 一步到位构造 SSA，优化在 SSA 上进行，lower 最后做 out-of-SSA。
- **保真**：类/函数/注解/debug/try 区域等元数据全保留，IR 与 `abcd_file::File` 语义等价。
- **arena 索引模型**：所有节点存于 `Module` 的 `Vec` arena，用类型化 `u32` 索引引用（`Value/Block/Inst/FuncId/StringId/ClassId`），无生命周期、无裸指针。

## 核心数据结构

```rust
pub struct Module {
    pub version: Version, pub file_type: FileType,
    pub classes: Vec<ClassData>,          // 类结构与字段，方法为 FuncId 引用
    pub literal_arrays: Vec<LiteralArray>, pub module_data: Vec<ModuleData>,
    pub functions: Vec<FunctionData>,     // 函数元数据 + 块列表 + try_regions
    pub insts: Vec<InstNode>,             // InstData + result + block + loc
    pub blocks: Vec<BasicBlockData>,      // phis / insts / preds
    pub values: Vec<ValueData>,           // def (Inst|FuncParam) + IrType
    pub strings: StringPool,
}
```

`InstData` 约 70 个 variant，覆盖 JS/TS/ArkTS 全谱（字面量、二元/一元、属性访问、全局/词法/模块变量、函数定义、调用、生成器/异步、异常、Phi、终结符）。三个单点方法：`operands_mut()` / `has_result()` / `is_terminator()`——所有 pass 与验证共用，杜绝重复列举。

## Lift（bytecode → SSA IR）

```
MethodBody ──▶ cfg.rs（leader 划分 + 异常边）──▶ ssa.rs（Braun SSA）──▶ translate.rs（逐条翻译）
```

- **CFG**：leader = 入口、跳转目标、跳转后继、terminator 后继、catch handler；条件跳转加 fall-through 边；try 区域与块区间求交加异常边。
- **SSA**：Braun 算法（*Simple and Efficient Construction of SSA Form*, 2013）。按翻译顺序 `read_variable` 时按需插 phi；块"sealed"前挂 incomplete phi，seal 时回填操作数；内建 trivial phi 消除。寄存器与累加器统一为 `RegOrAcc` 变量。
- **翻译**：`translate.rs` 覆盖全部 262 条指令（含 deprecated / callruntime / sendable 变体），实体 id 经 `entity_map` 解析为 interned 字符串；跳转目标经 `leader_to_block` 映射为 IR 块。
- **try 区域**：从原始 try_blocks 重建为 `TryRegion { try_blocks, catches }`，lowering 时再还原。

## 分析（analysis/）

- `compute_rpo` / `block_succs` / `inst_operands` / `replace_uses_in_func`：所有 pass 共享的 CFG 工具。
- `usedef`：按需构建 use-def 链。
- `domtree`：Semi-NCA 实现（当前**未接入管线**——Braun SSA 不需要支配边界，这是架构选择的结果。保留作为将来 GVN/PRE 等需要支配信息的 pass 的基础）。

## 优化（opt/）

管线（`optimize_func`）：`peephole → sccp → adce → cfg_simplify → copyprop → peephole → adce → cfg_simplify`

| Pass | 算法 | 说明 |
|------|------|------|
| Peephole | 局部常量折叠 | 算术/比较折叠、identity 消除 |
| Sccp | Wegman-Zadeck SCCP（1991） | CFG 边 + SSA 边双工作表，常量替换 + 死分支折叠 |
| Adce | 反向标记-清除 | 副作用/终结符为根，沿 use-def 传播 |
| CfgSimplify | 块合并/空跳转消除/不可达删除 | 与 ADCE 同文件 |
| CopyProp | trivial phi 消除 | 所有入边同值则替换 |
| Inline | 调用点克隆 | **未入默认管线**，手动调用 |

## Lower（SSA IR → bytecode）

```
regalloc.rs（五阶段）──▶ isel.rs（指令选择 + IC 槽）──▶ layout.rs（块布局 + 跳转/phi copy）
```

### 寄存器分配（`regalloc.rs`）

1. 精确后向数据流活跃性（phi 操作数记入前驱块的 use/out）。
2. 干涉图：从 live_out 反向扫描每块。
3. 累加器偏好评分：结果自然在 acc +2；BinOp 左操作数 +2；作寄存器操作数（call/store 实参）−3；使用次数 > 2 的长生命周期值 −5。
4. **MCS + 贪心着色**：SSA 干涉图是弦图，MCS 给出完美消除序，逆序贪心即最优着色（见文末论文）。
5. Boissinot out-of-SSA：同色 phi 操作数 coalesce，异色插入并行 copy，拓扑排序 + 环打破。

### 指令选择（`isel.rs`）

- IC 槽按函数计数分配：属性访问/调用/迭代器 2 槽，算术/全局/对象创建/函数定义 1 槽。
- 累加器管理三个原语：`ensure_acc`（lda）、`val_reg`（sta 到临时）、`store_result`（结果落寄存器）。
- **比较-分支融合**：`CondBranch(IsTrue(Eq(a,b)))` → `jeq r, label`（Eq/NotEq/StrictEq/StrictNotEq 四种）。
- 调用按 kind × 实参个数选择 callargN / callthisN / callrange 等。

### 布局（`layout.rs`）

RPO 排块 → phi copy 插到前驱终结符前 → 条件分支的 false 目标非后继时补显式 Jmp → 块引用解析为指令索引 → try 区域按最终偏移重建。

## 论文依据

| 论文 | 用于 |
|------|------|
| Braun et al., *Simple and Efficient Construction of SSA Form*, CC 2013 | lift/ssa.rs |
| Wegman & Zadeck, *Constant Propagation with Conditional Branches*, TOPLAS 1991 | opt/sccp.rs |
| Hack, *Register Allocation for Programs in SSA Form*, PhD 2007 | SSA 干涉图弦图性质 |
| Pereira & Palsberg, *Register Allocation via Coloring of Chordal Graphs*, APLAS 2005 | MCS 着色 |
| Boissinot et al., *Revisiting Out-of-SSA Translation*, CGO 2009 | phi 消除与并行 copy |

注意：**不引用** Lengauer-Tarjan / Georgiadis 支配树论文——Braun 算法使支配树不再是管线必需；`domtree.rs` 属于预留组件（见上文）。

## 已知缺口（诚实清单）

1. `lift` 未转换 `return_type` / `param_types`（`FunctionData` 里是 `None`/空）。
2. `val_reg()` 的 acc→寄存器搬运使用硬编码 `Reg(0xFFFE)` 作溢出槽，未做冲突管理。
3. `try_remove_trivial_phi` 只更新 defs 映射，未真正从 module 删除 phi 指令。
4. `isel` 若干近似：`BitNot → Not`、`Void → Ldundefined`、`ThrowConstAssignment` 用 dummy Reg(0)。
5. out-of-SSA 环打破未分配真实临时寄存器（≥2 节点的交换环会出错）。
6. `encode()` round-trip 因 C++ dedup 崩溃被禁用（见 file-format.md）。
