# ABC 容器层设计（abcd-file-sys / abcd-file）

> 本文档取代原根目录的 `abcd-file.md`（内容已并入并更新）。

## 文件布局

头 8 字节 magic `PANDA\0\0\0`，之后是小端字段序列。以开发基准 `modules.abc` 为例：

| 偏移 | 字段 | 实例值 |
|------|------|--------|
| 0x00 | magic | `PANDA\0\0\0` |
| 0x08 | checksum（adler32，从 version 字段起算） | `0xC30BD6FF` |
| 0x0C | version | `12.0.6.0` |
| 0x10 | file_size | 21.6MB |
| 0x14/0x18 | foreign_off / foreign_size | 0 / 0 |
| 0x1C | num_classes | 2035 |
| 0x20 | class_idx_off | 60 |
| 0x24 | num_lnps | 15738 |
| 0x28 | lnp_idx_off | … |
| 0x2C | num_literalarrays | 29147 |
| 0x30 | literalarray_idx_off | … |
| 0x34 | num_indexes | 2 |
| 0x38 | index_section_off | … |

版本条件化：`12.0.6.0` 是 `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION`，即此版本前 header 里携带字面量数组索引，之后移入其他区段——读写两侧都按版本分支（vendor `ContainsLiteralArrayInHeader`）。

## 实体模型

- 所有实体以 32-bit offset 定位；方法内引用用 16-bit index，经 `IndexHeader`（class/method/field/proto 四张索引表）解析为 offset。
- 类/方法/字段/代码都是"ULEB128 前缀字段 + tag 序列"的紧凑编码；注解四类（compile-time / runtime / type / runtime-type）、debug info（行号程序 + 常量池）、模块数据（LiteralArray 编码的 import/export 记录）全部覆盖。

## FFI 设计（file_bridge.h / file_bridge.cpp）

- 纯 C 接口（opaque handle），每个 accessor 走 `open → use → close` 生命周期。
- 枚举一律回调（`int (*cb)(..., void *ctx)`，返回非 0 提前终止）。
- 错误用 sentinel：`UINT32_MAX` = 不存在、`0` = size_t 失败。
- 编译期防线：`static_assert` 锁死 vendor 假设（MAGIC_SIZE=8、LiteralTag/AnnotationValueType 字符编码、`Type::TypeId::U32 == 0x08`），vendor 变动在编译期爆炸而非运行时。
- 两遍 bindgen：`bindings.rs`（桥 API）+ `enum_bindings.rs`（vendor 枚举）。ACC_* 访问标志由 build.rs **从 vendor `modifiers.h` 自动提取名称**、值引用 vendor constexpr——名称可列、数值永远来自 vendor，杜绝手写镜像漂移。

## Builder

`AbcBuilder`（`ItemContainer` + `MemoryWriter`）按"添加各项 → finalize → 释放"组织：

- handle 表按类型分列（class/foreign_class/string/literal_array/method/field/code/debug/lnp/annotation/proto/…），tagged class handle 高位 `0x80000000` 区分 foreign。
- literal array 先 staging（平铺 `(tag, value)` 对），`finalize` 时 flush 进 `LiteralArrayItem`。
- `ItemContainer::ComputeLayout()` 决定布局：header → 类索引 → 索引区 → foreign → 主体 → 行号程序索引；checksum 在写出后回填。

## vendor 与 shim 策略

vendor（69 文件，与上游零 diff）+ 9 个 shim 替换重型依赖：

- `zlib.h`：内联 adler32（NMAX=5552 分批取模），免链接系统 zlib；
- `os/mem.h`：非拥有 `MapPtr`（调用方持有内存）；
- `pgo.h`：`ProfileOptimizer` 空实现（file_item_container 仅需类型）；
- `platform_compat.h`：MSVC 的 clz/ctz/popcount 等 constexpr 位运算内建；
- `vendor_fixups.h`：以 `-include` 强制注入上游构建系统提供的 4 个传递头，**不改 vendor 文件本身**。

构建管线：Ruby（gen.rb，需 Ruby ≥ 2.5）生成 `type.h` / `source_lang_enum.h` / `file_format_version.h` → cc 编译 14 个 vendor `.cpp` + bridge → bindgen。

## 已知限制

1. **`encode()` 语义 round-trip 被禁用**：`abc_builder_deduplicate` 在重编码已解码文件时于 C++ 侧崩溃（`abcd-file/tests/roundtrip.rs` 的 `encode_roundtrip` 标 `#[ignore]`）。修复方向：在 bridge 的 finalize 前自行实现等价去重，或绕开 `DeduplicateCodeAndDebugInfo`。
2. 字符串池不可直接枚举（需遍历实体间接收集）。
3. Builder 无法设置文件类型（dynamic/static），厂商代码缺失，默认 dynamic。
4. 字节级 round-trip 不可能（builder 自行决定布局），语义等价即可。
5. `ParamInfo::signature` 在 encode 时不保留（C++ 写侧限制）。
