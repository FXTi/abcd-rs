# abcd-isa 开发文档

> 本文档面向 crate 维护者和贡献者，介绍 abcd-isa 的内部架构、构建管线和 API 设计。

本 crate 通过 arkcompiler 的 Ruby 代码生成管线 + C++ 桥接层，为 Rust 提供完整的 ArkCompiler 字节码指令集定义、解码、元数据查询、版本管理和字节码汇编能力。

原样拷贝（12 个）：

vendor/isa/gen.rb — runtime_core/isa/gen.rb
vendor/isa/isapi.rb — runtime_core/isa/isapi.rb
vendor/isa/combine.rb — runtime_core/isa/combine.rb
vendor/isa/isa.yaml — runtime_core/isa/isa.yaml
vendor/libpandafile/pandafile_isapi.rb — runtime_core/libpandafile/pandafile_isapi.rb
vendor/libpandafile/templates/bytecode_instruction_enum_gen.h.erb — 原始模板
vendor/libpandafile/templates/bytecode_instruction-inl_gen.h.erb — 原始模板
vendor/libpandafile/bytecode_emitter.h — 字节码汇编器基类（~132 行）
vendor/libpandafile/bytecode_emitter.cpp — 字节码汇编器实现（~293 行）
vendor/libpandafile/templates/bytecode_emitter_def_gen.h.erb — emitter 方法声明模板
vendor/libpandafile/templates/bytecode_emitter_gen.h.erb — emitter 方法实现模板
vendor/libpandafile/templates/file_format_version.h.erb — 版本常量模板

我们写的 shim / bridge 文件（9 个）：

bridge/shim/bytecode_instruction.h（~300 行 vs 原始 439 行）— 简化版，去掉了对 file.h、bit_helpers.h、securec.h、macros.h 的依赖，内联了 shim 宏（ASSERT、UNREACHABLE 等）、TypeHelperT 类型特征、panda_file::File 最小 stub（含 VERSION_SIZE），砍掉了 SAFE 模式的完整实现
bridge/shim/bytecode_instruction-inl.h（81 行 vs 原始 94 行）— 去掉了 #include "macros.h" 和一些 NOLINT 注释，功能上等价
bridge/shim/bytecode_emitter_shim.h — 提供 Span<T> 和 MinimumBitsToStore（emitter 依赖，原始来自 libpandabase）
bridge/shim/file_shim.h — 定义 PANDA_PUBLIC_API 宏（file_format_version.h 依赖）
bridge/shim/file.h — 重定向头文件，include bytecode_instruction.h + file_shim.h
bridge/shim/utils/const_value.h — 空 stub（file_format_version.h 的 include 依赖）
bridge/bytecode_emitter_wrapper.cpp — shim 注入 wrapper（先 include shim 再 include vendor .cpp，避免修改 vendor 文件）
templates/isa_bridge_emitter.h.erb — 自定义模板，生成 per-mnemonic C bridge emit 函数实现
templates/isa_bridge_emitter_decl.h.erb — 自定义模板，生成 per-mnemonic C bridge emit 函数声明（bindgen 用）

## 流水线总览

```
isa.yaml (ISA 数据源)
    │
    ▼
gen.rb + isapi.rb + pandafile_isapi.rb (Ruby 管线)
    │
    ├──► bytecode_instruction_enum_gen.h   (枚举: Opcode, Format, Flags, Exceptions)
    ├──► bytecode_instruction-inl_gen.h    (内联方法: decode, operand extraction, ~11577 行)
    ├──► isa_bridge_tables.h               (自定义元数据表: mnemonic, flags, exceptions, namespace, operands)
    ├──► bytecode_emitter_def_gen.h        (emitter 方法声明)
    ├──► bytecode_emitter_gen.h            (emitter 方法实现)
    ├──► file_format_version.h             (版本常量 + API 版本映射)
    ├──► isa_bridge_emitter.h              (per-mnemonic C bridge emit 函数实现)
    └──► isa_bridge_emitter_decl.h         (per-mnemonic C bridge emit 函数声明, bindgen 用)
            │
            ▼
    bytecode_instruction.h / -inl.h (简化版手写 C++ 基类, 含 shim)
    bytecode_emitter.h / .cpp (vendor 汇编器, 通过 wrapper.cpp 注入 shim)
            │
            ▼
    isa_bridge.h / isa_bridge.cpp (thin C wrapper, extern "C")
            │
            ▼
    build.rs: cc 编译 C++ → bindgen 生成 FFI bindings
            │
            ▼
    src/lib.rs (safe Rust API: 解码 + 元数据 + 版本 + 汇编器)
```

### 对比 arkcompiler 原始构建系统

```
isa.yaml + plugin ISA YAMLs
    │
    ▼
combine.rb (合并 core + plugin YAML)          ← IsaPostPlugins.cmake:14-30
    │
    ▼
gen.rb + isapi.rb + pandafile_isapi.rb        ← TemplateBasedGen.cmake:98-119 (panda_isa_gen)
    │                                            TemplateBasedGen.cmake:131-150 (panda_gen_file)
    ├──► bytecode_instruction_enum_gen.h
    ├──► bytecode_instruction-inl_gen.h
    ├──► bytecode_emitter_def_gen.h
    ├──► bytecode_emitter_gen.h
    └──► file_format_version.h
            │
            ▼
    bytecode_instruction.h / -inl.h (原始版, 依赖 libpandabase, libpandafile)
            │
            ▼
    直接在 C++ 项目中使用 (无需 C wrapper)
```

我们的差异：不走 CMake，用 Rust `build.rs` 驱动 Ruby；不用原始 C++ 头文件（依赖链太深），用简化版 + shim；额外写了 `isa_bridge_tables.h.erb` 模板导出 mnemonic/flags/exceptions 等元数据（原始管线中这些信息嵌在 `HasFlag` 的 switch 里，没有独立的静态表）。现在我们也生成 bytecode_emitter 和 file_format_version，与原始管线的差距进一步缩小——主要差异仅在于 shim 层和 C bridge 层。

---

## 第一步：Ruby 代码生成驱动 — gen.rb

arkcompiler 源码: `runtime_core/isa/gen.rb`

### 核心流程

命令行解析 (`gen.rb:64-78`)：

```ruby
optparser = OptionParser.new do |opts|
  opts.on('-t', '--template FILE', 'Template for file generation (required)')
  opts.on('-d', '--data FILE', 'Source data in YAML format (required)')
  opts.on('-o', '--output FILE', 'Output file (default is stdout)')
  opts.on('-r', '--require foo,bar,baz', Array, 'List of files to be required for generation')
end
```

YAML 加载 → JSON → OpenStruct（冻结）(`gen.rb:80-82`)：

```ruby
data = YAML.load_file(File.expand_path(options.data))
data = JSON.parse(data.to_json, object_class: OpenStruct).freeze
```

这一步把 YAML 的 Hash 转成 OpenStruct，使得模板中可以用 `data.groups` 而不是 `data['groups']`。`.freeze` 防止模板意外修改数据。

加载扩展脚本 + 回调 (`gen.rb:84-85`)：

```ruby
options&.require&.each { |r| require File.expand_path(r) } if options.require
Gen.on_require(data)
```

`Gen.on_require(data)` 是 `isapi.rb` 中定义的钩子（`gen.rb:38-40` 定义了空的默认实现），`isapi.rb` require 后会覆盖它，用 `Panda.wrap_data(data)` 初始化全局数据。

ERB 模板渲染 (`gen.rb:92-98`)：

```ruby
template = File.read(File.expand_path(options.template))
t = ERB.new(template, nil, '%-')
t.filename = options.template
output.write(t.result(create_sandbox))
```

`create_sandbox` 创建一个干净的 binding 环境，模板在其中求值。`'%-'` 启用 ERB 的 trim mode（`%` 行首标记 + `-` 尾部换行消除）。

### 我们的调用方式 (build.rs)

```rust
Command::new("ruby")
    .args([gen_rb, "-t", template, "-d", isa_yaml, "-r", requires, "-o", output])
    .status()
```

与 arkcompiler CMake 中 `panda_gen_file` (`TemplateBasedGen.cmake:131-150`) 的调用完全等价：

```cmake
COMMAND ${GENERATOR} --template ${ARG_TEMPLATE} --data ${ARG_DATAFILE}
        --output ${ARG_OUTPUTFILE} --require ${REQUIRE_STR}
```

---

## 第二步：ISA 数据 API — isapi.rb

arkcompiler 源码: `runtime_core/isa/isapi.rb` (~670 行)

这是整个管线的核心。它定义了 `Panda` 模块和 `Instruction`、`Format`、`Operand`、`OpcodeAssigner` 等类，所有 ERB 模板都通过这些 API 访问 ISA 数据。

### Panda 模块入口

`Panda.instructions` (`isapi.rb:566-572`) — 返回所有指令的有序数组：

```ruby
cached def instructions
  opcodes = OpcodeAssigner.new
  tmp_public = initialize_instructions(opcodes) { |ins| !ins.opcode_idx.nil? }
  tmp_private = initialize_instructions(opcodes) { |ins| ins.opcode_idx.nil? }
  tmp = tmp_public + tmp_private
  @instructions = tmp.sort_by(&:opcode_idx)
end
```

先处理 YAML 中已指定 `opcode_idx` 的指令（consume），再为未指定的自动分配（`yield_opcode`），最后按 `opcode_idx` 排序。

`Panda.formats` (`isapi.rb:587-589`)：

```ruby
def formats
  format_hash.values.uniq(&:pretty).sort_by(&:pretty)
end
```

`Panda.prefixes` (`isapi.rb:574-580`)：

```ruby
cached def prefixes
  opcodes = PrefixOpcodeAssigner.new
  tmp_public = initialize_prefixes(opcodes) { |p| !p.opcode_idx.nil? }
  tmp_private = initialize_prefixes(opcodes) { |p| p.opcode_idx.nil? }
  tmp = tmp_public + tmp_private
  @prefixes = tmp.sort_by(&:opcode_idx)
end
```

`Panda.properties` (`isapi.rb:529-534`) — 包含 YAML 定义的属性 + 3 个内置的 acc 属性：

```ruby
def properties
  @data.properties +
    [OpenStruct.new(tag: 'acc_none', ...),
     OpenStruct.new(tag: 'acc_read', ...),
     OpenStruct.new(tag: 'acc_write', ...)]
end
```

### Instruction 类

`mnemonic` (`isapi.rb:97-99`) — 签名的第一个词：

```ruby
def mnemonic
  sig.split(' ')[0]
end
```

例如 `"mov v1:out:any, v2:in:any"` → `"mov"`。

`opcode` (`isapi.rb:107-115`) — 唯一标识符（mnemonic + format）：

```ruby
def opcode
  mn = mnemonic.tr('.', '_')
  fmt = format.pretty
  fmt == 'none' ? mn : "#{mn}_#{fmt}"
end
```

例如 `"mov_v8_v8"`, `"ldundefined"`。这是 C++ enum 中的枚举名。

`opcode_idx` (`isapi.rb:143-149`) — 关键：opcode 数值编码：

```ruby
def opcode_idx
  if prefix
    dig(:opcode_idx) << 8 | prefix.opcode_idx
  else
    dig(:opcode_idx)
  end
end
```

- 非前缀指令：`opcode_idx` 就是字节码流中的第一个字节值（0x00-0xDC）。
- 前缀指令：`(sub_opcode << 8) | prefix_byte`。例如 prefix=0xFB, sub=0x01 → opcode_idx = 0x01FB = 507。

这个编码方式直接体现在生成的 `GetOpcode()` 中 (`bytecode_instruction-inl_gen.h.erb:381-388`)：

```cpp
inline typename BytecodeInst<Mode>::Opcode BytecodeInst<Mode>::GetOpcode() const {
    uint8_t primary = GetPrimaryOpcode();
    if (primary >= 251) {  // 0xFB = min prefix
        uint8_t secondary = GetSecondaryOpcode();
        return static_cast<BytecodeInst::Opcode>((secondary << 8U) | primary);
    }
    return static_cast<BytecodeInst::Opcode>(primary);
}
```

`primary` 是字节码流的第一个字节。如果 >= 251（即 0xFB/FC/FD/FE），说明是前缀指令，读第二个字节作为 secondary，编码为 `(secondary << 8) | primary`。

`format` (`isapi.rb:152-154`)：

```ruby
def format
  Panda.format_hash[dig(:format)]
end
```

`operands` (`isapi.rb:157-185`) — 解析签名字符串，提取操作数并关联编码信息：

```ruby
cached def operands
  return [] unless sig.include? ' '
  _, operands = sig.match(/(\S+) (.+)/).captures
  operands = operands.split(', ')
  ops_encoding = format.encoding
  # ... 解析每个操作数的 name, srcdst, type，关联 width 和 offset
end
```

`properties` (`isapi.rb:202-210`) — 指令属性列表（含自动推导的 acc_read/acc_write/acc_none）：

```ruby
cached def properties
  props = dig(:properties) || []
  add_props = []
  add_props << 'acc_write' if acc_write?
  add_props << 'acc_read' if acc_read?
  add_props << 'acc_none' if acc_none?
  props + add_props
end
```

`namespace` (`isapi.rb:267-269`)：

```ruby
def namespace
  dig(:namespace) || 'core'
end
```

### Format 类

`pretty` (`isapi.rb:318-320`) — 规范化格式名：

```ruby
cached def pretty
  name.sub('op_', '').gsub(/id[0-9]?/, 'id').gsub(/imm[0-9]?/, 'imm')
      .gsub(/v[0-9]?/, 'v').gsub(/_([0-9]+)/, '\1')
end
```

例如 `"pref_op_v1_4_v2_4"` → `"v4_v4"`。

`size` (`isapi.rb:326-332`) — 指令总字节数：

```ruby
cached def size
  bits = pretty.gsub(/[a-z]/, '').split('_').map(&:to_i).sum
  raise "Incorrect format name #{name}" if bits % 8 != 0
  opcode_bytes = prefixed? ? 2 : 1
  bits / 8 + opcode_bytes
end
```

从格式名中提取数字求和得到操作数总位数，加上 opcode 字节数（前缀指令 2 字节，非前缀 1 字节）。

`encoding` (`isapi.rb:334-349`) — 操作数编码映射（name → {offset, width}）：

```ruby
cached def encoding
  return {} if name.end_with?('_none')
  offset = prefixed? ? 16 : 8  # 前缀指令从 bit 16 开始，非前缀从 bit 8
  encoding = {}
  name.sub('pref_', '').sub('op_', '').split('_').each_slice(2).map do |name, width|
    op = OpenStruct.new
    op.name = name
    op.width = width.to_i
    op.offset = offset
    offset += op.width
    encoding[name] = op
  end
  encoding
end
```

### Operand 类

构造函数 (`isapi.rb:360-373`)：

```ruby
def initialize(name, srcdst, type, width = 0, offset = 0)
  @name = name.to_s.gsub(/[0-9]/, '').to_sym
  unless %i[v acc imm method_id type_id field_id string_id literalarray_id].include?(@name)
    raise "Incorrect operand #{name}"
  end
  @srcdst = srcdst.to_sym || :in
  @type = type
  @width = width
  @offset = offset
end
```

类型查询方法：

- `reg?` (`isapi.rb:375-377`): `@name == :v`
- `acc?` (`isapi.rb:379-381`): `@name == :acc`
- `imm?` (`isapi.rb:383-385`): `@name == :imm`
- `id?` (`isapi.rb:399-401`): `%i[method_id type_id field_id string_id literalarray_id].include?(@name)`
- `src?` (`isapi.rb:419-421`): `%i[inout in].include?(@srcdst)`
- `dst?` (`isapi.rb:415-417`): `%i[inout out].include?(@srcdst)`

### OpcodeAssigner 类

(`isapi.rb:482-510`) — 自动分配 opcode 值：

```ruby
def initialize
  @table = Hash.new { |h, k| h[k] = Set.new }
  @all_opcodes = Set.new(0..255)
end

def consume(item)          # 标记已占用的 opcode
  @table[prefix(item)] << item.opcode_idx
end

def yield_opcode(item)     # 分配 opcode
  return item.opcode_idx if item.opcode_idx
  choose_opcode(@table[prefix(item)])
end

def choose_opcode(occupied_opcodes)  # 选最小可用值
  (@all_opcodes - occupied_opcodes).min
end
```

每个 prefix 有独立的 0-255 命名空间。

---

## 第三步：PandaFile 扩展 — pandafile_isapi.rb

arkcompiler 源码: `runtime_core/libpandafile/pandafile_isapi.rb` (~82 行)

通过 `class_eval` 给 `Instruction` 和 `Operand` 类添加方法 (`pandafile_isapi.rb:18-45`)：

```ruby
Instruction.class_eval do
  def emitter_name        # "mov" → "Mov", "throw.ifnotobject" → "ThrowIfnotobject"
    mnemonic.split('.').map { |p| p == '64' ? 'Wide' : p.capitalize }.join
  end

  def each_operand        # 带类型索引的操作数迭代
    getters = {:reg? => 0, :imm? => 0, :id? => 0}
    operands.each do |op|
      key = getters.keys.find { |x| op.send(x) }
      yield op, getters[key]
      getters[key] += 1
    end
  end

  def jcmp?               # 条件跳转（非 zero 比较）
    jump? && conditional? && stripped_mnemonic[-1] != 'z'
  end

  def jcmpz?              # 条件跳转（zero 比较）
    jump? && conditional? && stripped_mnemonic[-1] == 'z'
  end
end
```

辅助函数 `insns_uniq_sort_fmts` (`pandafile_isapi.rb:79-81`)：

```ruby
def insns_uniq_sort_fmts
  Panda.instructions.uniq { |i| i.format.pretty }.sort_by { |insn| insn.format.pretty }
end
```

这个函数在 `bytecode_instruction-inl_gen.h.erb` 中大量使用，用于按格式去重生成 switch case。

---

## 第四步：YAML 合并 — combine.rb

arkcompiler 源码: `runtime_core/isa/combine.rb`

(`combine.rb:42-54`)：

```ruby
data = YAML.load_file(File.expand_path(options.data.first))
options.data.drop(1).each do |plugin_path|
  plugin_data = YAML.load_file(File.expand_path(plugin_path))
  instructions = data_instructions(plugin_data)
  raise 'Plugged in instructions must be prefixed' unless instructions.reject { |i| i['prefix'] }.empty?
  plugin_data.each_key do |attr|
    raise "Uknown data property: #{attr}" unless data.key?(attr)
    data[attr] += plugin_data[attr]
  end
end
```

关键约束：plugin 指令必须全部有 prefix。这保证了 core ISA 的 0x00-0xFA 命名空间不被 plugin 污染。

arkcompiler 的 CMake 集成 (`IsaPostPlugins.cmake:14-30`)：

```cmake
add_custom_command(OUTPUT ${ISA_FILE}
    COMMAND ${ISA_COMBINE} -d "${ISA_CORE_FILE},${ISA_PLUGIN_FILES_STR}" -o ${ISA_FILE}
    DEPENDS ${ISA_COMBINE} ${ISA_CORE_FILE} ${ISA_PLUGIN_FILES})
```

我们的处理：直接使用已合并的 `isa.yaml`（从 arkcompiler 复制），不需要运行 `combine.rb`。如果未来需要支持 plugin ISA，可以在 `build.rs` 中加一步 combine。

---

## 第五步：生成的 C++ 代码

### bytecode_instruction_enum_gen.h

arkcompiler 源码: `runtime_core/libpandafile/templates/bytecode_instruction_enum_gen.h.erb`

生成 4 个枚举，通过 `#include <bytecode_instruction_enum_gen.h>` 注入到 `BytecodeInst` 类内部 (`bytecode_instruction.h:226`)。

Format 枚举 (`enum_gen.h.erb:16-20`)：

```cpp
enum class Format : uint8_t {
% Panda::formats.each do |fmt|
    <%= fmt.pretty.upcase %>,
% end
};
```

生成约 80 种格式：`NONE`, `V4_V4`, `V8`, `IMM8`, `V4_V4_V4_V4`, `PREF_IMM16_V8`, ...

Opcode 枚举 (`enum_gen.h.erb:22-27`)：

```cpp
enum class Opcode {
% Panda::instructions.each do |i|
    <%= i.opcode.upcase %> = <%= i.opcode_idx %>,
% end
    LAST = <%= Panda::instructions.last().opcode.upcase %>
};
```

生成 326 个 opcode，值域：非前缀 0-220，前缀 251-11772。

Flags 枚举 (`enum_gen.h.erb:29-33`)：

```cpp
enum Flags : uint32_t {
% Panda::properties.each_with_index do |f, i|
    <%= f.tag.upcase %> = <%= format("0x%x", 1 << i) %>,
% end
};
```

Exceptions 枚举 (`enum_gen.h.erb:35-39`) — 同理。

### bytecode_instruction-inl_gen.h

arkcompiler 源码: `runtime_core/libpandafile/templates/bytecode_instruction-inl_gen.h.erb`

生成约 11577 行内联方法。关键方法：

`GetOpcode()` (`inl_gen.h.erb:381-388`) — 已在上文详述，编码为 `(secondary << 8) | primary`。

`HasId` / `HasVReg` / `HasImm` (`inl_gen.h.erb:17-71`) — 编译期查询：

```cpp
constexpr bool BytecodeInst<Mode>::HasId(Format format, size_t idx) {
    switch (format) {
% insns_uniq_sort_fmts.each do |i|
%   n = i.operands.count(&:id?)
%   next if n == 0
    case Format::<%= fmt.pretty.upcase %>:
        return idx < <%= n %>;
% end
    default: return false;
    }
}
```

`Size(Format)` (`inl_gen.h.erb:74-86`)：

```cpp
constexpr size_t BytecodeInst<Mode>::Size(Format format) {
    switch (format) {
% Panda::formats.each do |fmt|
    case Format::<%= fmt.pretty.upcase %>: {
        constexpr size_t SIZE = <%= fmt.size %>;
        return SIZE;
    }
% end
    }
}
```

`GetId<format, idx>()` (`inl_gen.h.erb:88-116`) — 编译期模板方法，按 format 和 idx 读取 ID 操作数：

```cpp
template <Format format, size_t idx>
inline BytecodeId BytecodeInst<Mode>::GetId() const {
    static_assert(HasId(format, idx), "...");
% insns_uniq_sort_fmts.each do |i|
%   id_ops = i.operands.select(&:id?)
%   next if id_ops.empty?
    if (format == Format::<%= fmt.pretty.upcase %>) {
        return BytecodeId(static_cast<uint32_t>(Read<<%= offsets[0] %>, <%= widths[0] %>>()));
    }
% end
}
```

`Read<offset, width>()` 是编译期位域读取，在 `bytecode_instruction-inl.h:50-63` 中实现。

`HasFlag` (`inl_gen.h.erb:428-442`) — 运行时属性查询，大 switch：

```cpp
inline bool BytecodeInst<Mode>::HasFlag(Flags flag) const {
    switch(GetOpcode()) {
% Panda::instructions.each do |i|
%   flags = i.real_properties.map {|prop| "Flags::" + prop.upcase}.join(' | ')
    case Opcode::<%= i.opcode.upcase %>:
        return ((<%= flags %>) & flag) == flag;
% end
    }
}
```

`operator<<` (`inl_gen.h.erb:503-538`) — 格式化输出，也是大 switch。

运行时操作数提取方法（`inl_gen.h.erb:200-380`）：

```cpp
// 运行时 GetVReg — 遍历所有 format 的大 switch
inline uint16_t BytecodeInst<Mode>::GetVReg(size_t idx) const {
    auto format = GetFormat();
    switch (format) {
% insns_uniq_sort_fmts.each do |i|
%   vreg_ops = i.operands.select(&:reg?)
%   next if vreg_ops.empty?
    case Format::<%= fmt.pretty.upcase %>:
        switch (idx) {
%     vreg_ops.each_with_index do |op, j|
        case <%= j %>: return static_cast<uint16_t>(Read<<%= op.offset %>, <%= op.width %>>());
%     end
        }
% end
    }
    UNREACHABLE();
}

// 运行时 GetImm64 — 同理，返回 int64_t
inline int64_t BytecodeInst<Mode>::GetImm64(size_t idx) const { ... }

// 运行时 GetId — 同理，返回 BytecodeId
inline BytecodeId BytecodeInst<Mode>::GetId(size_t idx) const { ... }
```

这些运行时方法是 C bridge 的核心依赖——bridge 层直接调用它们，避免了在 C 侧重新实现操作数解码逻辑。

---

## 第六步：C++ 基类 — bytecode_instruction.h

arkcompiler 原始文件: `runtime_core/libpandafile/bytecode_instruction.h` (439 行)
我们的简化版: `bridge/shim/bytecode_instruction.h` (295 行)

### 原始依赖链

原始文件依赖：

- `libpandabase/macros.h` → `ASSERT`, `UNREACHABLE`, `DEFAULT_COPY_SEMANTIC` 等宏
- `libpandabase/utils/bit_helpers.h` → `helpers::TypeHelperT` 类型特征
- `libpandafile/file.h` → `panda_file::File::EntityId`, `panda_file::File::Index`
- `securec.h` → `memcpy_s`（华为安全 C 库）
- `utils/logger.h` → `LOG` 宏

### 我们的 shim 替代

在简化版头文件顶部 (`bridge/shim/bytecode_instruction.h:20-39`)：

```cpp
// Shim macros replacing arkcompiler internals
#include <cassert>
#define ASSERT(x) assert(x)
#define ASSERT_PRINT(x, msg) assert(x)
#define UNREACHABLE() __builtin_unreachable()
#define UNREACHABLE_CONSTEXPR() __builtin_unreachable()
#define ALWAYS_INLINE __attribute__((always_inline))
#define DEFAULT_COPY_SEMANTIC(T) T(const T&) = default; T& operator=(const T&) = default
#define NO_MOVE_SEMANTIC(T) T(T&&) = delete; T& operator=(T&&) = delete
#define LOG(level, component) std::cerr

// C++20 bit_cast shim (generated code uses it)
template <typename To, typename From>
inline To bit_cast(const From& src) {
    static_assert(sizeof(To) == sizeof(From));
    To dst;
    std::memcpy(&dst, &src, sizeof(To));
    return dst;
}
```

`panda_file::File` 最小 stub (`bridge/shim/bytecode_instruction.h:43-53`)：

```cpp
namespace panda::panda_file {
class File {
public:
    using Index = uint16_t;
    struct EntityId {
        uint32_t offset;
        explicit constexpr EntityId(uint32_t v) : offset(v) {}
        uint32_t GetOffset() const { return offset; }
    };
};
}
```

`helpers::TypeHelperT` 内联 (`bridge/shim/bytecode_instruction.h:59-83`) — 从 `libpandabase/utils/bit_helpers.h` 提取：

```cpp
namespace panda::helpers {
template <size_t width>
struct UnsignedTypeHelper {
    using type = std::conditional_t<
        width <= 8, uint8_t,
        std::conditional_t<width <= 16, uint16_t,
            std::conditional_t<width <= 32, uint32_t,
                std::conditional_t<width <= 64, uint64_t, void>>>>;
};
template <size_t width, bool is_signed>
using TypeHelperT = ...;
}
```

### 核心类结构

`BytecodeInstMode` (原始 `bytecode_instruction.h:33`)：

```cpp
enum class BytecodeInstMode { FAST, SAFE };
```

我们只使用 `FAST` 模式（直接内存访问，无边界检查）。

`BytecodeId` (原始 `bytecode_instruction.h:38-84`)：

```cpp
class BytecodeId {
    uint32_t id_ {INVALID};
public:
    constexpr explicit BytecodeId(uint32_t id) : id_(id) {}
    uint32_t AsRawValue() const { return id_; }
    // ...
};
```

`BytecodeInstBase<FAST>` (原始 `bytecode_instruction.h:86-133`)：

```cpp
template <>
class BytecodeInstBase<BytecodeInstMode::FAST> {
protected:
    const uint8_t *GetPointer(int32_t offset) const { return pc_ + offset; }
    uint8_t ReadByte(size_t offset) const { return Read<uint8_t>(offset); }
    template <class T>
    T Read(size_t offset) const {
        using unaligned_type __attribute__((aligned(1))) = const T;
        return *reinterpret_cast<unaligned_type *>(GetPointer(offset));
    }
private:
    const uint8_t *pc_ {nullptr};
};
```

`pc_` 指向字节码流中当前指令的起始位置。所有读取都是相对于 `pc_` 的偏移。

`BytecodeInst` (原始 `bytecode_instruction.h:219-429`)：

```cpp
template <const BytecodeInstMode Mode = BytecodeInstMode::FAST>
class BytecodeInst : public BytecodeInstBase<Mode> {
public:
    #include <bytecode_instruction_enum_gen.h>    // 枚举注入

    Opcode GetOpcode() const;
    uint8_t GetPrimaryOpcode() const { return ReadByte(0); }  // 第一个字节
    uint8_t GetSecondaryOpcode() const;                        // 第二个字节（前缀指令）

    // 编译期模板方法
    template <Format format, size_t idx = 0> BytecodeId GetId() const;
    template <Format format, size_t idx = 0> uint16_t GetVReg() const;
    template <Format format, size_t idx = 0, bool is_signed = true> auto GetImm() const;

    // 运行时方法（内部是遍历所有 format 的大 switch）
    BytecodeId GetId(size_t idx) const;
    uint16_t GetVReg(size_t idx) const;
    int64_t GetImm64(size_t idx) const;

    // 元数据查询
    static constexpr Format GetFormat(Opcode);
    bool HasFlag(Flags) const;
    bool IsThrow(Exceptions) const;
    bool IsPrefixed() const;
    bool IsJumpInstruction() const;
    bool IsRangeInstruction() const;

    // 格式化输出
    friend ostream& operator<<(ostream&, BytecodeInst);
};
```

---

## 第七步：自定义 ERB 模板 — isa_bridge_tables.h.erb

arkcompiler 原始管线中，mnemonic、flags、exceptions 等元数据嵌在 `HasFlag`/`operator<<` 的大 switch 里，没有独立的静态查找表。为了让 C bridge 能高效查询这些信息，我们编写了自定义 ERB 模板 `templates/isa_bridge_tables.h.erb`，使用同一套 `Panda` API 生成纯 C 静态数组。

### 生成的表

| 表名 | 结构 | 用途 |
|------|------|------|
| `ISA_MNEMONIC_TABLE[]` | `{opcode, mnemonic}` | opcode → 助记符字符串 |
| `ISA_FLAGS_TABLE[]` | `{opcode, flags}` | opcode → 属性位掩码 |
| `ISA_EXCEPTIONS_TABLE[]` | `{opcode, exceptions}` | opcode → 异常类型位掩码 |
| `ISA_NAMESPACE_TABLE[]` | `{opcode, ns}` | opcode → 命名空间字符串 |
| `ISA_OPERANDS_TABLE[]` | `{opcode, num_operands, acc_read, acc_write, operands[8]}` | opcode → 操作数详情 |

### 属性位掩码生成

模板从所有指令的 `properties` 中收集去重排序，为每个属性分配一个 bit 位：

```ruby
<%
  all_props = {}
  Panda.instructions.each do |insn|
    insn.properties.each { |p| all_props[p] = true unless p.nil? || p.empty? }
  end
  prop_list = all_props.keys.sort
  prop_to_bit = {}
  prop_list.each_with_index { |p, i| prop_to_bit[p] = i }
-%>
<% prop_list.each_with_index do |tag, i| -%>
#define ISA_FLAG_<%= tag.upcase %> (1u << <%= i %>)
<% end -%>
```

生成的 `#define` 如：`ISA_FLAG_JUMP (1u << 0)`, `ISA_FLAG_CONDITIONAL (1u << 1)`, `ISA_FLAG_RETURN (1u << 3)` 等。

### 操作数详情表

每条指令最多 8 个操作数，每个操作数记录：

```c
struct IsaOperandInfo {
    uint8_t kind;      /* 0=reg, 1=imm, 2=id */
    uint8_t op_type;   /* 编码类型索引 (none=0, u1=1, i8=2, ..., any=14) */
    uint8_t bit_width; /* 操作数位宽 */
    uint8_t is_src;    /* 是否为源操作数 */
    uint8_t is_dst;    /* 是否为目标操作数 */
};
```

### 设计决策

为什么不直接用 C++ 生成代码中的 `HasFlag`/`operator<<`？

1. `HasFlag` 是实例方法，需要构造 `BytecodeInst` 对象才能调用，而我们需要纯 opcode → flags 的静态映射
2. `operator<<` 中的 mnemonic 嵌在 switch 里，无法作为字符串表索引
3. 独立的 C 数组支持二分查找，性能更好且不依赖 C++ 模板实例化

---

## 第八步：BytecodeEmitter Vendor 文件

arkcompiler 源码: `runtime_core/libpandafile/bytecode_emitter.h` + `bytecode_emitter.cpp`

BytecodeEmitter 是 arkcompiler 的字节码汇编器，与 BytecodeInstruction（解码器）互补。它负责编码指令、管理分支标签（Label）、在 Build 时修补跳转偏移。

### 核心类

`Label` — 分支目标标记，由 emitter 创建，绑定到字节码流中的某个位置。

`BytecodeEmitter` — 汇编器主类：

```cpp
class BytecodeEmitter {
public:
    enum class ErrorCode { SUCCESS, INTERNAL_ERROR, UNBOUND_LABELS };

    Label CreateLabel();
    void Bind(const Label& label);
    ErrorCode Build(std::vector<uint8_t>* output);

    // Per-mnemonic emit 方法（由 bytecode_emitter_gen.h 生成）
    // 例如: void Mov(uint8_t vd, uint8_t vs);
    //       void Jmp(const Label& target);
    //       void Ldundefined();
};
```

生成的 emit 方法由两个模板产生：
- `bytecode_emitter_def_gen.h.erb` — 方法声明（注入到类定义内）
- `bytecode_emitter_gen.h.erb` — 方法实现（编码逻辑，选择最优指令格式）

### Wrapper .cpp 模式

vendor 的 `bytecode_emitter.cpp` 依赖 `Span<T>` 和 `MinimumBitsToStore`（来自 libpandabase），但我们不想修改 vendor 文件。解决方案是 `bridge/bytecode_emitter_wrapper.cpp`：

```cpp
// 先 include shim，再 include 原始 cpp
#include "bytecode_emitter_shim.h"
#include "bytecode_emitter.cpp"  // 直接 include .cpp
```

这样 shim 中的 `Span<T>` 和 `MinimumBitsToStore` 在 vendor 代码编译前就已定义。

---

## 第九步：Emitter Shim 文件

### bytecode_emitter_shim.h

提供 emitter 依赖的两个 libpandabase 组件的最小实现：

```cpp
namespace panda {
template <typename T>
class Span {
public:
    Span(T* data, size_t size);
    template <typename U, size_t N> Span(std::array<U, N>& arr);
    template <typename U, size_t N> Span(const std::array<U, N>& arr);
    template <typename It> Span(It it, size_t size);  // 迭代器构造
    T& operator[](size_t idx);
    size_t size() const;
    Span SubSpan(size_t offset) const;
};
}

template <typename T>
constexpr size_t MinimumBitsToStore(T value);  // 计算存储 value 所需的最少位数
```

`Span<T>` 的迭代器构造函数是关键——emitter 内部用 `bytecode_.begin() + offset` 构造 Span。

### file_shim.h + file.h

`file_format_version.h` 依赖 `#include "file.h"` 和 `PANDA_PUBLIC_API` 宏。我们的策略：

- `bridge/shim/file_shim.h` — 只定义 `#define PANDA_PUBLIC_API`
- `bridge/shim/file.h` — 重定向，include `bytecode_instruction.h`（提供 `File::VERSION_SIZE`）+ `file_shim.h`
- `bridge/shim/utils/const_value.h` — 空 stub（`file_format_version.h` 的另一个 include 依赖）

`File::VERSION_SIZE = 4` 定义在 `bytecode_instruction.h` 的 `panda::panda_file::File` stub 中，与 `EntityId`、`Index` 共存。

---

## 第十步：自定义 ERB 模板 — isa_bridge_emitter.h.erb

为每个 mnemonic 生成一个 C bridge emit 函数，使 Rust 侧可以通过 FFI 调用汇编器。

### 模板逻辑

```ruby
Panda::instructions.group_by(&:mnemonic).each do |mnemonic, group|
  emitter_name = group.first.emitter_name   # "mov" → "Mov"
  is_jump = group.first.jump?
  signature = emitter_signature(group, is_jump)
  c_name = "isa_emit_" + mnemonic.tr('.', '_')
  # ...
end
```

对于跳转指令，C++ 侧的 `const Label&` 参数替换为 `uint32_t label_id`，bridge 内部通过 `e->labels[label_id]` 查找对应的 C++ Label 对象。

### 生成的函数签名模式

```c
// 无操作数
void isa_emit_ldundefined(IsaEmitter* e);

// 寄存器操作数
void isa_emit_mov(IsaEmitter* e, uint8_t vd, uint8_t vs);

// 跳转指令（Label → label_id）
void isa_emit_jmp(IsaEmitter* e, uint32_t label_id);

// 立即数 + 寄存器
void isa_emit_ldai(IsaEmitter* e, int32_t imm);
```

### 两个模板的分工

- `isa_bridge_emitter.h.erb` — 生成函数实现，include 在 `isa_bridge.cpp` 中（`extern "C"` 块内）
- `isa_bridge_emitter_decl.h.erb` — 生成函数声明，用于 bindgen wrapper header，使 Rust FFI 能看到这些函数

---

## 第十一步：C Bridge API 设计

`bridge/isa_bridge.h` + `bridge/isa_bridge.cpp`

### 设计原则

1. 纯 C 接口（`extern "C"`），便于 bindgen 生成 Rust FFI
2. 解码/元数据函数无状态，线程安全；Emitter 是有状态的
3. 字节流操作接受 `(const uint8_t* bytes, size_t len)` 对，与 Rust slice 自然映射
4. 错误用哨兵值表示（`0xFFFF` = 无效 opcode，`NULL` = 未知 mnemonic）

### API 分层

**解码层** — 委托给 `BytecodeInst<FAST>` 的生成方法：

```c
IsaOpcode isa_decode_opcode(const uint8_t* bytes, size_t len);  // → GetOpcode()
IsaFormat isa_get_format(IsaOpcode opcode);                      // → GetFormat(Opcode)
size_t    isa_get_size(IsaFormat format);                        // → Size(Format)
int       isa_is_prefixed(IsaOpcode opcode);                     // 检查低字节
```

**操作数提取层** — 委托给运行时方法：

```c
uint16_t isa_get_vreg(const uint8_t* bytes, size_t len, size_t idx);  // → GetVReg(idx)
int64_t  isa_get_imm64(const uint8_t* bytes, size_t len, size_t idx); // → GetImm64(idx)
uint32_t isa_get_id(const uint8_t* bytes, size_t len, size_t idx);    // → GetId(idx).AsRawValue()
int      isa_has_vreg(IsaFormat format, size_t idx);                   // → HasVReg(Format, idx)
int      isa_has_imm(IsaFormat format, size_t idx);                    // → HasImm(Format, idx)
int      isa_has_id(IsaFormat format, size_t idx);                     // → HasId(Format, idx)
```

**元数据层** — 查询自定义生成表（二分查找）：

```c
const char* isa_get_mnemonic(IsaOpcode opcode);     // ISA_MNEMONIC_TABLE
uint32_t    isa_get_flags(IsaOpcode opcode);         // ISA_FLAGS_TABLE
uint32_t    isa_get_exceptions(IsaOpcode opcode);    // ISA_EXCEPTIONS_TABLE
const char* isa_get_namespace(IsaOpcode opcode);     // ISA_NAMESPACE_TABLE
struct IsaOperandBrief isa_get_operand_info(IsaOpcode opcode);  // ISA_OPERANDS_TABLE
```

**分类辅助** — 基于 flags 或 opcode 编码的快捷查询：

```c
int isa_is_jump(IsaOpcode opcode);         // ISA_FLAG_JUMP
int isa_is_conditional(IsaOpcode opcode);  // ISA_FLAG_CONDITIONAL
int isa_is_return(IsaOpcode opcode);       // ISA_FLAG_RETURN
int isa_is_throw(IsaOpcode opcode);        // (opcode & 0xFF) == 0xFE (throw 是前缀)
int isa_is_range(IsaOpcode opcode);        // 委托 IsRangeInstruction()
```

### Opcode 编码注意事项

opcode 值的编码为 `(sub_opcode << 8) | prefix_byte`：

- 非前缀指令：值 = 第一个字节（0x00-0xDC），高 8 位为 0
- 前缀指令：低 8 位 = prefix byte（0xFB/FC/FD/FE），高 8 位 = sub-opcode

`isa_is_prefixed` 检查低字节而非高字节。`isa_is_throw` 直接检查 `(opcode & 0xFF) == 0xFE`，因为 throw 是一个前缀组（0xFE），不是 flags 中的属性。`isa_is_range` 需要重建字节序列后委托给 C++ 的 `IsRangeInstruction()`。

### 版本 API

```c
void isa_get_version(uint8_t out[4]);           // 当前 .abc 文件版本
void isa_get_min_version(uint8_t out[4]);       // 最低支持版本
size_t isa_get_api_version_count(void);         // api_version_map 条目数
int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]);  // API level → 文件版本
int isa_is_version_compatible(const uint8_t ver[4]);             // 版本兼容性检查
```

版本数据来自生成的 `file_format_version.h`，其中定义了 `panda::panda_file::version`、`minVersion` 和 `api_version_map`。

`isa_bridge.cpp` 中还实现了 `file_format_version.h` 声明但未定义的两个函数：`GetVersion()`（版本数组转字符串）和 `IsVersionLessOrEqual()`（版本比较）。

### 汇编器 API

```c
typedef struct IsaEmitter IsaEmitter;

IsaEmitter* isa_emitter_create(void);
void isa_emitter_destroy(IsaEmitter* e);

uint32_t isa_emitter_create_label(IsaEmitter* e);
void isa_emitter_bind(IsaEmitter* e, uint32_t label_id);

int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
// 返回值: 0=SUCCESS, 1=INTERNAL_ERROR, 2=UNBOUND_LABELS
void isa_emitter_free_buf(uint8_t* buf);

// Per-mnemonic emit 函数（由 isa_bridge_emitter.h.erb 生成，共 326 个）
// void isa_emit_mov(IsaEmitter* e, uint8_t vd, uint8_t vs);
// void isa_emit_jmp(IsaEmitter* e, uint32_t label_id);
// ...
```

`IsaEmitter` 内部结构：

```cpp
struct IsaEmitter {
    panda::BytecodeEmitter emitter;     // C++ 汇编器
    std::vector<panda::Label> labels;   // label_id → Label 映射
};
```

`isa_emitter_create_label` 返回 `labels` 数组的索引。跳转指令的 emit 函数接收 `label_id`，通过索引找到 Label 传给 C++ emitter。`isa_emitter_build` 调用 `emitter.Build()`，将结果拷贝到 `new[]` 分配的缓冲区，调用方通过 `isa_emitter_free_buf` 释放。

---

## 第十二步：Rust Safe API 设计

`src/lib.rs`

### 类型系统

```rust
/// Opcode 值 (u16)。非前缀 opcode 在 u8 范围内；前缀 = (sub << 8) | prefix_byte。
#[repr(transparent)]
pub struct Opcode(pub u16);

/// 指令格式，决定操作数布局。
#[repr(transparent)]
pub struct Format(pub u8);

/// 指令属性标志位。
pub struct OpcodeFlags(u32);

impl OpcodeFlags {
    pub const JUMP: OpcodeFlags = OpcodeFlags(1 << 0);
    pub const CONDITIONAL: OpcodeFlags = OpcodeFlags(1 << 1);
    pub const CALL: OpcodeFlags = OpcodeFlags(1 << 2);
    pub const RETURN: OpcodeFlags = OpcodeFlags(1 << 3);
    pub const THROW: OpcodeFlags = OpcodeFlags(1 << 4);
    pub const ACC_READ: OpcodeFlags = OpcodeFlags(1 << 7);
    pub const ACC_WRITE: OpcodeFlags = OpcodeFlags(1 << 8);
    // ...
}
```

`Opcode` 和 `Format` 使用 `#[repr(transparent)]` newtype 包装，保证与 C FFI 的 `uint16_t`/`uint8_t` 二进制兼容。`OpcodeFlags` 的 bit 位与 C bridge 的 `ISA_FLAG_*` 宏对应。

### 静态表初始化

使用 `LazyLock` 在首次访问时从 C bridge 构建完整的 opcode 表：

```rust
static ISA: LazyLock<IsaTable> = LazyLock::new(|| {
    // 遍历所有可能的 opcode 值
    let mut opcodes_to_check: Vec<u16> = (0..=0xFF).collect();
    for prefix in [0xFB, 0xFC, 0xFD, 0xFE] {
        for sub in 1..=0xFF {
            opcodes_to_check.push((sub << 8) | prefix);
        }
    }

    for opcode_val in opcodes_to_check {
        let mnemonic_ptr = unsafe { ffi::isa_get_mnemonic(opcode_val) };
        if mnemonic_ptr.is_null() { continue; }  // 跳过无效 opcode
        // ... 构建 OpcodeInfo，leak 字符串和切片获取 'static 生命周期
    }
});
```

遍历策略：先检查 0x00-0xFF（非前缀），再检查 4 个前缀组各 255 个 sub-opcode。`isa_get_mnemonic` 返回 `NULL` 表示该 opcode 不存在，跳过。

字符串和操作数切片通过 `Box` → leak 获取 `'static` 生命周期，`Box` 本身保存在 `IsaTable` 的 `_mnemonic_storage` / `_operand_storage` 中防止被释放。

### 公共 API

```rust
/// 查找表：opcode u16 值 → OpcodeInfo（按值排序，支持二分查找）
pub fn opcode_table() -> &'static [(u16, OpcodeInfo)];

/// 按 opcode 值查找 OpcodeInfo
pub fn lookup_opcode(value: u16) -> Option<&'static OpcodeInfo>;

/// 从字节流解码一条指令
pub fn decode_opcode(bytes: &[u8]) -> Option<(Opcode, &'static OpcodeInfo)>;

/// 提取虚拟寄存器操作数
pub fn get_vreg(bytes: &[u8], idx: usize) -> u16;

/// 提取有符号 64 位立即数操作数
pub fn get_imm64(bytes: &[u8], idx: usize) -> i64;

/// 提取实体 ID 操作数
pub fn get_id(bytes: &[u8], idx: usize) -> u32;

/// 格式化指令为可读字符串
pub fn format_instruction(bytes: &[u8]) -> String;
```

### OpcodeInfo 结构

```rust
pub struct OpcodeInfo {
    pub mnemonic: &'static str,           // 助记符
    pub format: Format,                    // 指令格式
    pub flags: OpcodeFlags,               // 属性标志
    pub is_prefixed: bool,                // 是否前缀指令
    pub operand_parts: &'static [OperandDesc],  // 操作数描述
}
```

### 与旧实现的 API 兼容性

旧实现中 `Opcode` 是 enum，新实现改为 newtype `Opcode(pub u16)`。下游代码需要将 `insn.opcode as u16` 改为 `insn.opcode.0`。其余 API（`opcode_table()`、`lookup_opcode()`、`OpcodeFlags` 等）保持兼容。

### 版本 API

```rust
/// .abc 文件版本 (4 字节: major.minor.patch.build)
pub struct AbcVersion(pub [u8; 4]);

pub fn current_version() -> AbcVersion;                    // 当前版本
pub fn min_version() -> AbcVersion;                        // 最低支持版本
pub fn version_by_api(api_level: u8) -> Option<AbcVersion>; // API level → 版本
pub fn is_version_compatible(ver: &AbcVersion) -> bool;    // 兼容性检查
```

`AbcVersion` 实现了 `Display`（格式化为 `"x.y.z.w"`）和 `Ord`（支持版本比较）。

### 汇编器 API

```rust
pub struct Emitter { ptr: *mut ffi::IsaEmitter }
pub struct EmitterLabel(pub u32);
pub enum EmitterError { InternalError, UnboundLabels }

impl Emitter {
    pub fn new() -> Self;
    pub fn as_ptr(&mut self) -> *mut ffi::IsaEmitter;  // 用于调用 ffi::isa_emit_*
    pub fn create_label(&mut self) -> EmitterLabel;
    pub fn bind(&mut self, label: EmitterLabel);
    pub fn build(&mut self) -> Result<Vec<u8>, EmitterError>;
}
```

`Emitter` 实现了 `Drop`（自动调用 `isa_emitter_destroy`）和 `Default`。

Per-mnemonic emit 函数通过 `ffi` 模块直接调用：

```rust
let mut e = Emitter::new();
let label = e.create_label();
unsafe { ffi::isa_emit_jmp(e.as_ptr(), label.0) };
e.bind(label);
unsafe { ffi::isa_emit_ldundefined(e.as_ptr()) };
let bytecode = e.build().expect("build failed");
```

`ffi` 模块是 `pub` 的，下游 crate 可以直接使用所有 per-mnemonic emit 函数。

---

## 目录结构

```
abcd-isa/
├── build.rs                    # 构建脚本：Ruby 生成 → cc 编译 → bindgen
├── Cargo.toml                  # 依赖：cc, bindgen
├── src/
│   └── lib.rs                  # Rust safe API: 解码 + 元数据 + 版本 + 汇编器
├── bridge/
│   ├── isa_bridge.h            # C wrapper 头文件（extern "C"）
│   ├── isa_bridge.cpp          # C wrapper 实现
│   ├── bytecode_emitter_wrapper.cpp  # shim 注入 wrapper
│   └── shim/
│       ├── bytecode_instruction.h      # 简化版 C++ 基类（含 shim 宏 + File stub）
│       ├── bytecode_instruction-inl.h  # 简化版内联方法
│       ├── bytecode_emitter_shim.h     # Span<T> + MinimumBitsToStore
│       ├── file_shim.h                 # PANDA_PUBLIC_API 宏
│       ├── file.h                      # 重定向头文件
│       └── utils/
│           └── const_value.h           # 空 stub
├── templates/
│   ├── isa_bridge_tables.h.erb         # 自定义 ERB 模板（元数据静态表）
│   ├── isa_bridge_emitter.h.erb        # 自定义 ERB 模板（emitter C bridge 实现）
│   └── isa_bridge_emitter_decl.h.erb   # 自定义 ERB 模板（emitter C bridge 声明）
├── vendor/
│   ├── isa/
│   │   ├── gen.rb              # arkcompiler: runtime_core/isa/gen.rb
│   │   ├── isapi.rb            # arkcompiler: runtime_core/isa/isapi.rb
│   │   ├── combine.rb          # arkcompiler: runtime_core/isa/combine.rb
│   │   └── isa.yaml            # arkcompiler: runtime_core/isa/isa.yaml (已合并 ecmascript plugin)
│   └── libpandafile/
│       ├── pandafile_isapi.rb           # arkcompiler: pandafile_isapi.rb
│       ├── bytecode_emitter.h           # arkcompiler: 汇编器基类
│       ├── bytecode_emitter.cpp         # arkcompiler: 汇编器实现
│       └── templates/
│           ├── bytecode_instruction_enum_gen.h.erb   # arkcompiler 原始模板
│           ├── bytecode_instruction-inl_gen.h.erb    # arkcompiler 原始模板
│           ├── bytecode_emitter_def_gen.h.erb        # arkcompiler 原始模板
│           ├── bytecode_emitter_gen.h.erb            # arkcompiler 原始模板
│           └── file_format_version.h.erb             # arkcompiler 原始模板
└── DEVELOP.md
```

## 构建依赖

- Ruby 2.5+（运行 gen.rb 代码生成）
- C++17 编译器（编译 bridge + 生成的头文件）
- `cc` crate（Rust 构建时编译 C++）
- `bindgen` crate（生成 Rust FFI 绑定）

## 数据统计

- 326 个 opcode：225 非前缀 (0x00-0xDC) + 101 前缀 (4 个前缀组)
- ~80 种指令格式
- 4 个前缀：`callruntime` (0xFB), `deprecated` (0xFC), `wide` (0xFD), `throw` (0xFE)
- Ruby 生成 8 个头文件：enum_gen, inl_gen, bridge_tables, emitter_def_gen, emitter_gen, file_format_version, bridge_emitter, bridge_emitter_decl
- C++ 编译 2 个源文件：isa_bridge.cpp + bytecode_emitter_wrapper.cpp
- C bridge 导出 30+ 静态函数 + 326 个 per-mnemonic emit 函数
- Rust API：解码/元数据/版本/汇编器，17 个测试
