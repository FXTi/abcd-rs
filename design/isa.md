# ISA 层设计（abcd-isa-sys / abcd-isa）

## 三层结构

```
isa.yaml（268 条指令 / 332 个 opcode / 4 个前缀组，vendor 自上游）
        │  Ruby 代码生成（gen.rb + isapi.rb + pandafile_isapi.rb，ERB）
        ▼
生成的 C++ 头（opcode/format/flags 枚举、操作数解码内联、emitter 声明）
        │  cc 编译（isa_bridge.cpp + vendor bytecode_emitter.cpp）
        ▼
C bridge（isa_bridge.h：解码/分类/版本/有状态 Emitter）
        │  bindgen
        ▼
abcd-isa-sys（bindings.rs + 由 bytecode.rs.erb 生成的 Bytecode 枚举）
        │  safe 封装
        ▼
abcd-isa（decode / encode / Version）
```

## 代码生成

数据源 `vendor/isa/isa.yaml` 与上游逐字节一致，由 vendor-sync 体系锁定（见 vendor-sync.md）。`build.rs` 用 Ruby 驱动 7 个模板：

| 模板 | 产物 |
|------|------|
| `bytecode_instruction_enum_gen.h.erb` | Opcode/Format/Flags/Exceptions 枚举 |
| `bytecode_instruction-inl_gen.h.erb` | 操作数解码与分类内联（~11.5k 行） |
| `bytecode_emitter_{def,gen}_gen.h.erb` | emitter 方法声明/实现 |
| `file_format_version.h.erb` | 版本常量 + API 映射 |
| `isa_bridge_emit_dispatch.h.erb`（自研） | opcode → emitter 方法的分发 switch |
| `bytecode.rs.erb`（自研） | Rust `Bytecode` 枚举 + 构造器 + 解码 |

**自研模板的关键设计**（`bytecode.rs.erb`）：

- `Bytecode` 枚举**按 mnemonic 分组**而非按 opcode：`Mov` 合并 MOV_V4_V4 / MOV_V8_V8 / MOV_V16_V16，操作数带类型（`Reg`/`Imm`/`EntityId`/`Label`）。
- `representative_opcode()`：每组取最大格式的 opcode 作代表，用于 FFI 分类调用（同组性质相同，具体值无所谓）。
- 跳转指令的立即数在解码后解析为 `Label`（**指令索引**，不是字节偏移）；`set_label` / `jump_label_arg_index` 支撑重写。
- `insn::*` 模块为每个 mnemonic 生成类型化构造器（`insn::Jeq::new(Reg(0), Label(2))`）。

## 解码（abcd-isa/src/decoder.rs）

两遍算法：

1. **线性扫描**：读 opcode → 查大小 → `Bytecode::decode_one` 提取操作数；跳转的原始相对偏移暂存。前缀字节（≥ 251）占 2 字节 opcode，截断检测。
2. **跳转解析**：对每个跳转，`insn_offset + raw_imm` 得到目标字节偏移，`binary_search` 到指令边界 → 写入 `Label(target_index)`。非边界目标报 `InvalidJumpTarget`。

## 编码（abcd-isa/src/emitter.rs）

- `Label` 语义是输入切片中的**指令索引**（与解码输出一致，round-trip 幂等）。
- 两段映射：先收集所有跳转目标 → 为每个目标在 C++ emitter 里 `create_label`；按指令序发射，遇目标 `bind`，跳转操作数换成 C++ label id。
- C++ `BytecodeEmitter::Build()` 负责指令格式选择与长跳转扩宽（imm8→imm16→jCC 反转+远跳），Rust 侧不预测编码；发射后按实际字节重扫得到 per-instruction offset 表（try-block 元数据要用字节偏移）。

## 分类与版本

- 分类：`is_jump / can_throw / is_terminator / is_return_or_throw / is_suspend / is_range / is_throw_ex / has_flag`。opcode 级查询用零填充缓冲构造指令，避免依赖操作数字节。
- 版本：`Version`（四元组）提供 `current()`（24.0.0.0）、`min_supported()`、`for_api()`、`is_in_supported_range()`、`is_blocked()`（incompatible 黑名单），底层委托 vendor `file_format_version` 实现，不手工复制数据。

## 设计原则

1. **只编码，不决策**：`abcd-isa` 不知道"SuperCallOpt 只在 API 18+ 可用"这类语义；opcode 选择是 IR lowering 的职责。
2. **数据与代码同源**：ISA 事实只存在于 isa.yaml；Rust/C++ 两侧都由它生成，零手写镜像。
3. **FFI 边界最小化**：桥只做薄转发（`Inst::GetFormat` 等），解码逻辑留在 vendor 生成代码里。
