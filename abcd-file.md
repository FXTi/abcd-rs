# abcd-file crate 设计参考

本文档汇总了对 `abcd-file-sys` FFI 层和 ABC 文件格式的研究成果，供后续开发 `abcd-file`（safe Rust 封装）时参考。

---

## ABC 文件格式概览

ABC（ArkCompiler Bytecode）是华为 ArkCompiler 的二进制字节码格式，源语言为 JavaScript / TypeScript / ArkTS。

### 文件头

- Magic: `PANDA\0\0\0`（8 字节）
- Checksum: u32（adler32）
- Version: [u8; 4]（当前 13.0.1.0，最低 0.0.0.2）
- File size: u32
- Foreign section: offset + size
- Class index: count + offset
- Literal array index: count + offset
- Line number program index: count + offset
- Index section: num_headers + offset

### 文件类型

- `FILE_DYNAMIC = 0`（JS/TS，绝大多数场景）
- `FILE_STATIC = 1`（ArkTS 静态模式）

### 实体寻址

- 所有实体通过 32-bit offset 定位
- 方法内的引用使用 16-bit index，通过 IndexHeader 映射到 offset

---

## ISA 特征

ABC 字节码 100% 面向 JavaScript/TypeScript，与 Java 字节码有根本差异：

- **动态类型**：`any`/`tagged` 类型，`ldundefined`, `ldhole`, `typeof`
- **原型链对象**：`createemptyobject`, `setobjectwithproto`, `ldobjbyvalue`, `ldobjbyname`
- **一等函数 + 闭包**：`definefunc`, `newlexenv`, `ldlexvar`, `stlexvar`, `poplexenv`
- **生成器/异步**：`creategeneratorobj`, `suspendgenerator`, `asyncfunctionenter`, `asyncfunctionawaituncaught`
- **ES 模块**：`ldmodulevar`, `stmodulevar`, `ldexternalmodulevar`, `dynamicimport`
- **JS 特有**：`stricteq`, `isin`, `createregexpwithliteral`, `gettemplateobject`, `callspread`

不适合用 Java 的 Jimple IR 作为中间表示。如需 IR，建议自定义或参考 Hermes IR / V8 Turbofan IR。

---

## abcd-file-sys API 清单

### 读取侧（Accessor 模式）

所有 accessor 遵循 `open(file, offset) → use → close` 生命周期。

#### 文件级

| 函数 | 说明 |
|------|------|
| `abc_file_open(data, len)` / `abc_file_close` | 打开/关闭文件 |
| `abc_file_version` / `abc_file_checksum` / `abc_file_size` | 文件元数据 |
| `abc_file_get_type` | 文件类型（0=dynamic, 1=static） |
| `abc_file_get_raw_data` | 原始字节指针 |
| `abc_file_num_classes` / `abc_file_class_offset` | 类索引 |
| `abc_file_num_literalarrays` / `abc_file_literalarray_offset` | 字面量数组索引 |
| `abc_file_num_index_headers` / `abc_file_get_index_header` | 索引头 |
| `abc_file_get_string(offset)` | 按 offset 读 MUTF-8 字符串 |
| `abc_file_get_class_id(name)` | 按名称查找类 |
| `abc_file_is_external(offset)` | 是否在 foreign section |
| `abc_resolve_method_index` / `abc_resolve_class_index` / `abc_resolve_field_index` / `abc_resolve_proto_index` | 16-bit index → offset |

#### 类

| 函数 | 说明 |
|------|------|
| `abc_class_open` / `abc_class_close` | 打开/关闭 |
| `abc_class_get_descriptor` / `abc_class_get_name` | 类名（MUTF-8 描述符） |
| `abc_class_super_class_off` | 父类 offset |
| `abc_class_access_flags` | 访问标志 |
| `abc_class_get_source_lang` | 源语言 |
| `abc_class_source_file_off` | 源文件 |
| `abc_class_num_fields` / `abc_class_num_methods` | 字段/方法数 |
| `abc_class_enumerate_methods` / `abc_class_enumerate_fields` | 枚举方法/字段 |
| `abc_class_enumerate_annotations` / `_runtime_annotations` / `_type_annotations` / `_runtime_type_annotations` | 4 种注解 |
| `abc_class_get_ifaces_number` / `abc_class_enumerate_interfaces` | 接口 |

#### 方法

| 函数 | 说明 |
|------|------|
| `abc_method_open` / `abc_method_close` | 打开/关闭 |
| `abc_method_name_off` / `abc_method_get_name` | 方法名 |
| `abc_method_class_idx` / `abc_method_proto_idx` | 类/Proto 索引（16-bit） |
| `abc_method_access_flags` | 访问标志 |
| `abc_method_code_off` | 代码 offset（UINT32_MAX = 无） |
| `abc_method_debug_info_off` | 调试信息 offset |
| `abc_method_get_source_lang` | 源语言 |
| `abc_method_enumerate_annotations` / `_runtime_annotations` / `_type_annotations` / `_runtime_type_annotations` | 4 种注解 |
| `abc_method_get_param_annotation_id` / `abc_method_get_runtime_param_annotation_id` | 参数注解 ID |
| `abc_method_get_numerical_annotation(field_id)` | 数值注解（icSize/parameterLength/funcName） |
| `abc_method_enumerate_types_in_proto` | Proto 内联类型枚举 |
| `abc_method_get_name_off_static` / `_class_id_static` / `_proto_id_static` | 无需 accessor 的快捷访问 |

#### 代码

| 函数 | 说明 |
|------|------|
| `abc_code_open` / `abc_code_close` | 打开/关闭 |
| `abc_code_num_vregs` / `abc_code_num_args` | 寄存器数/参数数 |
| `abc_code_code_size` / `abc_code_instructions` | 字节码大小/指针 |
| `abc_code_tries_size` | try 块数 |
| `abc_code_enumerate_try_blocks_full` | 枚举 try-catch（含 catch handler 信息） |

#### 字段

| 函数 | 说明 |
|------|------|
| `abc_field_open` / `abc_field_close` | 打开/关闭 |
| `abc_field_name_off` / `abc_field_type` / `abc_field_access_flags` | 基本属性 |
| `abc_field_get_value_i32` / `_i64` / `_f32` / `_f64` | 初始值（返回 1=有, 0=无） |
| `abc_field_enumerate_annotations` / `_runtime_annotations` / `_type_annotations` / `_runtime_type_annotations` | 4 种注解 |

#### Proto

| 函数 | 说明 |
|------|------|
| `abc_proto_open` / `abc_proto_close` | 打开/关闭 |
| `abc_proto_get_return_type` / `abc_proto_get_arg_type` | 返回类型/参数类型 |
| `abc_proto_get_reference_type` / `abc_proto_get_ref_num` | 引用类型 |
| `abc_proto_get_shorty` | Shorty 描述符 |
| `abc_proto_enumerate_types` | 枚举所有类型 |

#### 字面量数组

| 函数 | 说明 |
|------|------|
| `abc_literal_open` / `abc_literal_close` | 打开/关闭 |
| `abc_literal_count` | 数组数量 |
| `abc_literal_get_vals_num` / `_by_index` | 值数量 |
| `abc_literal_enumerate_vals` / `_by_index` | 枚举值（回调接收 `AbcLiteralVal`） |

`AbcLiteralVal` 结构：`{ tag: u8, union { u8/u16/u32/u64/f32/f64/bool }, str_data: *const u8, str_utf16_len: u32 }`

#### 模块

| 函数 | 说明 |
|------|------|
| `abc_module_open` / `abc_module_close` | 打开/关闭 |
| `abc_module_num_requests` / `abc_module_request_off` | 请求模块 |
| `abc_module_enumerate_records` | 枚举记录（tag + export_name_off + module_request_idx + import_name_off + local_name_off） |

ModuleTag 值：`REGULAR_IMPORT=1, NAMESPACE_IMPORT=2, LOCAL_EXPORT=3, INDIRECT_EXPORT=4, STAR_EXPORT=5`

#### 注解

| 函数 | 说明 |
|------|------|
| `abc_annotation_open` / `abc_annotation_close` | 打开/关闭 |
| `abc_annotation_class_off` / `abc_annotation_count` | 注解类/元素数 |
| `abc_annotation_get_element` | 获取元素（返回 `AbcAnnotationElem`） |
| `abc_annotation_get_array_element` | 获取数组元素 |

#### 调试信息

| 函数 | 说明 |
|------|------|
| `abc_debug_info_open` / `abc_debug_info_close` | 打开/关闭（文件级，非方法级） |
| `abc_debug_get_line_table(method_off)` | 行号表 |
| `abc_debug_get_column_table(method_off)` | 列号表 |
| `abc_debug_get_local_vars(method_off)` | 局部变量表 |
| `abc_debug_get_source_file(method_off)` | 源文件名 |
| `abc_debug_get_source_code(method_off)` | 源代码 |
| `abc_debug_get_parameter_info(method_off)` | 参数信息 |

#### 索引

| 函数 | 说明 |
|------|------|
| `abc_index_open(method_off)` / `abc_index_close` | 打开/关闭 |
| `abc_index_get_offset_by_id(16-bit id)` | 16-bit index → entity offset |
| `abc_index_get_function_kind` | FunctionKind |

---

### 写入侧（Builder 模式）

Builder 遵循：`new → 添加各项 → finalize → free` 流程。

#### 生命周期

| 函数 | 说明 |
|------|------|
| `abc_builder_new` / `abc_builder_free` | 创建/释放 |
| `abc_builder_set_api(version)` | 设置 API 版本（默认 12） |
| `abc_builder_finalize(out_len)` | 计算布局并输出字节（返回指针，builder 释放前有效） |
| `abc_builder_deduplicate` / `_code_and_debug_info` / `_annotations` | 去重 |

#### 字符串

| 函数 | 说明 |
|------|------|
| `abc_builder_add_string(str)` | 添加字符串，返回 handle |

#### 类

| 函数 | 说明 |
|------|------|
| `abc_builder_add_class(descriptor)` | 添加类，返回 handle |
| `abc_builder_add_foreign_class(descriptor)` | 添加外部类 |
| `abc_builder_add_global_class` | 添加 `L_GLOBAL;` 类 |
| `abc_builder_class_set_access_flags` / `_source_lang` / `_super_class` / `_source_file` | 类配置 |
| `abc_builder_class_add_interface` | 添加接口 |
| `abc_builder_class_add_annotation` / `_runtime_annotation` / `_type_annotation` / `_runtime_type_annotation` | 类注解 |

#### 字段

| 函数 | 说明 |
|------|------|
| `abc_builder_class_add_field(name, type_id, access_flags)` | 添加字段 |
| `abc_builder_class_add_field_ex(name, type_id, ref_class, access_flags)` | 添加字段（含引用类型） |
| `abc_builder_add_foreign_field` | 添加外部字段 |
| `abc_builder_field_set_value_i32` / `_i64` / `_f32` / `_f64` | 设置初始值 |
| `abc_builder_field_add_annotation` / `_runtime_annotation` / `_type_annotation` / `_runtime_type_annotation` | 字段注解 |

#### Proto

| 函数 | 说明 |
|------|------|
| `abc_builder_create_proto(ret_type, arg_types, num_args)` | 创建 Proto |
| `abc_builder_create_proto_ex(ret_type, ret_ref, arg_types, arg_refs, num_args)` | 创建 Proto（含引用类型） |

#### 方法

| 函数 | 说明 |
|------|------|
| `abc_builder_class_add_method_with_proto(name, proto, flags, code, code_size, vregs, args)` | 添加方法 |
| `abc_builder_add_foreign_method` | 添加外部方法 |
| `abc_builder_method_set_source_lang` / `_function_kind` / `_debug_info` / `_code` | 方法配置 |
| `abc_builder_method_add_annotation` / `_runtime_annotation` / `_type_annotation` / `_runtime_type_annotation` | 方法注解 |

#### 代码

| 函数 | 说明 |
|------|------|
| `abc_builder_create_code(insns, insns_size, num_vregs, num_args)` | 创建代码项 |
| `abc_builder_code_add_try_block(code, offset, length, catch_offset, catch_length, catch_type)` | 添加 try-catch |

#### 字面量数组

| 函数 | 说明 |
|------|------|
| `abc_builder_add_literal_array` | 创建字面量数组 |
| `abc_builder_literal_array_add_u8` / `_u16` / `_u32` / `_u64` / `_bool` / `_f32` / `_f64` | 添加值 |
| `abc_builder_literal_array_add_string(string_handle)` | 添加字符串引用 |
| `abc_builder_literal_array_add_method(method_handle)` | 添加方法引用 |
| `abc_builder_literal_array_add_literalarray(la_handle)` | 添加字面量数组引用 |

#### 调试信息

| 函数 | 说明 |
|------|------|
| `abc_builder_create_lnp` | 创建行号程序 |
| `abc_builder_lnp_emit_advance_pc` / `_advance_line` / `_column` / `_end` | 行号程序操作码 |
| `abc_builder_lnp_emit_start_local` / `_end_local` | 局部变量范围 |
| `abc_builder_lnp_emit_set_file` / `_set_source_code` | 源文件/代码 |
| `abc_builder_create_debug_info(lnp, params_num, line_start)` | 创建调试信息 |
| `abc_builder_debug_add_param(string_handle)` | 添加参数名 |

#### 注解

| 函数 | 说明 |
|------|------|
| `abc_builder_create_annotation(class_handle, elem_values, elem_names, num_elems)` | 创建注解 |
| `abc_builder_create_annotation_ex(class_handle, ...)` | 创建注解（含数组支持） |

---

## 模块 LiteralArray 编码格式

模块数据在 ABC 中以 LiteralArray 编码存储（来自 `ModuleRecordEmitter`）。

### 编码结构

```
[module_requests_count: INTEGER,
 request_string_1: STRING, request_string_2: STRING, ...,

 regular_import_count: INTEGER,
 local_name: STRING, import_name: STRING, module_idx: METHODAFFILIATE(u16), ...,

 namespace_import_count: INTEGER,
 local_name: STRING, module_idx: METHODAFFILIATE(u16), ...,

 local_export_count: INTEGER,
 local_name: STRING, export_name: STRING, ...,

 indirect_export_count: INTEGER,
 export_name: STRING, import_name: STRING, module_idx: METHODAFFILIATE(u16), ...,

 star_export_count: INTEGER,
 module_idx: METHODAFFILIATE(u16), ...]
```

### Tag 类型

- 计数字段：`LiteralTag::INTEGER`（u32）
- 字符串字段：`LiteralTag::STRING`
- 模块索引：`LiteralTag::METHODAFFILIATE`（u16）

### 读写对应

- 读取：`abc_module_open` → `abc_module_enumerate_records`（解析上述格式）
- 写入：`abc_builder_add_literal_array` → `abc_builder_literal_array_add_u32`（计数）+ `abc_builder_literal_array_add_string`（字符串）+ `abc_builder_literal_array_add_u16`（模块索引）

---

## 数值注解编码

数值注解是普通注解，使用特定字段名：

| 字段名 | 含义 |
|--------|------|
| `icSize` | IC（Inline Cache）槽位数 |
| `parameterLength` | 形参数量 |
| `funcName` | 函数名 |

读取：`abc_method_get_numerical_annotation(field_id)` — field_id 是字段名字符串的 offset
写入：用 `abc_builder_create_annotation` 创建普通注解，字段名设为上述值

---

## abcd-file crate 设计要点

### 定位

`abcd-file` 是 `abcd-file-sys` 的 safe Rust 封装，提供：
- 零拷贝读取 ABC 文件
- 类型安全的数据模型
- Builder 模式构建 ABC 文件
- 模块数据的高层封装

### 核心类型（建议）

```
AbcFile          — 文件句柄（持有 data 的生命周期）
AbcClass         — 类访问器
AbcMethod        — 方法访问器
AbcCode          — 代码访问器
AbcField         — 字段访问器
AbcProto         — Proto 访问器
AbcLiteralArray  — 字面量数组访问器
AbcModule        — 模块访问器（高层封装，内部解析 LiteralArray）
AbcAnnotation    — 注解访问器
AbcDebugInfo     — 调试信息提取器
AbcIndex         — 索引访问器
AbcBuilder       — 文件构建器
```

### 关键设计决策

1. **生命周期**：所有 accessor 借用 `AbcFile`，确保文件数据在 accessor 存活期间不被释放
2. **迭代器**：将回调枚举（`enumerate_*`）封装为 Rust 迭代器
3. **字符串**：MUTF-8 → Rust `&str` 转换，注意非标准 UTF-8 编码
4. **错误处理**：将 `UINT32_MAX` / `NULL` 返回值转为 `Option` 或 `Result`
5. **模块**：在 Rust 层封装模块 LiteralArray 的编解码，提供 `ModuleRecord` 高层类型
6. **Builder**：handle-based API 映射为类型安全的 builder pattern

### 已知限制

- 字符串池无法直接枚举，需通过遍历实体间接收集
- 文件类型（dynamic/static）在 builder 中无法设置（厂商代码缺失），默认 dynamic
- 字节级 round-trip 不可能（builder 自行决定布局），语义等价可行
