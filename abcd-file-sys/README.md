# abcd-file-sys

> This document is intended for crate maintainers and contributors, covering the internal architecture, build pipeline, and API design of abcd-file-sys.
> If you just want to use the file format API, see the higher-level [`abcd-file`](../abcd-file/README.md) crate.

This crate provides complete ArkCompiler `.abc` file format C FFI bindings for Rust, wrapping arkcompiler's `libpandafile` C++ library via a thin C bridge layer.

## Directory Structure

```
abcd-file-sys/
├── build.rs                           # Ruby codegen → cc compile → bindgen
├── Cargo.toml                         # links = "file_bridge"
├── src/
│   └── lib.rs                         # include!(bindings.rs) + integration tests
├── bridge/
│   ├── file_bridge.h                  # C wrapper header (extern "C", ~170 functions)
│   ├── file_bridge.cpp                # C wrapper implementation
│   └── shim/                          # Minimal shims (9 files, replacing heavy deps)
│       ├── vendor_fixups.h            # Force-included: <functional>, <iomanip>, <map>, "utils/hash.h"
│       ├── pgo.h                      # ProfileOptimizer stub (no-op)
│       ├── securec.h                  # Huawei secure C library shim (memcpy_s wrapper)
│       ├── platform_compat.h          # MSVC compat (ssize_t, __attribute__ stubs)
│       ├── zlib.h                     # Inline adler32 implementation (no system zlib needed)
│       ├── os/file.h                  # Empty stub
│       ├── os/filesystem.h            # Empty stub
│       ├── os/mem.h                   # Empty stub
│       └── utils/logger.h             # LOG macro → no-op
└── vendor/
    ├── isa/                           # ISA data + Ruby codegen engine (3 files)
    ├── libpandafile/                  # Core file format library (~50 files)
    │   ├── *.h / *.cpp                # Data accessors, file items, debug info, etc.
    │   ├── templates/                 # ERB templates (3 files)
    │   ├── *.rb / *.yaml             # Ruby codegen modules + type data
    │   └── file_format_version.cpp   # Version utilities (vendored from upstream)
    └── libpandabase/                  # Base headers + utf.cpp (~15 files)
```

### Vendor File Origins

69 files copied verbatim from arkcompiler runtime_core. All vendor files are kept identical to upstream (zero diff) to minimize sync burden.

4 missing transitive includes that the upstream build provides are injected via `vendor_fixups.h` (force-included with `-include` / `/FI`), avoiding any vendor file modifications.

`pgo.h` (ProfileOptimizer) is stubbed in `bridge/shim/` and shadowed via include path priority — the upstream version depends on runtime infrastructure we don't have.

9 custom shim files replace heavy upstream dependencies (logging, OS abstraction, secure C library, zlib) with minimal stubs or inline implementations.

## Build Pipeline Overview

```
isa.yaml / types.yaml (data sources)
    │
    ▼
gen.rb + per-template requires (Ruby pipeline)
    │
    ├──► source_lang_enum.h   (SourceLang enum: ECMASCRIPT, ARKTS, etc.)
    ├──► type.h               (Type class: TypeId enum + property queries)
    └──► file_format_version.h (version constants + API version mapping)
            │
            ▼
    vendor/libpandafile/*.cpp + vendor/libpandabase/utils/utf.cpp
    (14 vendor .cpp files, compiled directly)
            │
            ▼
    file_bridge.h / file_bridge.cpp (thin C wrapper, extern "C")
            │
            ▼
    build.rs: cc compiles C++ → bindgen generates FFI bindings
            │
            ▼
    src/lib.rs (include!(bindings.rs))
```

### Ruby Code Generation

Each template gets only the Ruby modules it needs (matching upstream's CMake approach):

| Template | Data | Requires | Module |
|----------|------|----------|--------|
| `source_lang_enum.h.erb` | `isa.yaml` | `plugin_options.rb` | `Common` |
| `type.h.erb` | `types.yaml` | `types.rb` | `PandaFile` |
| `file_format_version.h.erb` | `isa.yaml` | `isapi.rb, pandafile_isapi.rb` | `Panda` |

Ruby's `def` is last-writer-wins — each `.rb` file redefines `Gen.on_require(data)`, so the final definition must match the module the template uses. Per-template requires ensure this naturally.

### Comparison with arkcompiler's Original Build System

- Use Rust `build.rs` to drive Ruby instead of CMake/GN
- Vendor `.cpp` files compiled directly — no CMake target dependencies
- `vendor_fixups.h` force-include replaces upstream's transitive header propagation (PCH / CMake target includes)
- `-DSUPPORT_KNOWN_EXCEPTION` enables C++ exception path in `THROW_IF` macro, avoiding dependency on upstream's `LOG(FATAL)` infrastructure
- `-DNDEBUG` eliminates C++ debug assertion runtime dependencies
- `bridge/shim/zlib.h` provides inline `adler32` — no system zlib linkage needed

## C Bridge API Design

`bridge/file_bridge.h` + `bridge/file_bridge.cpp` (~170 exported functions)

Design principles:
1. Pure C interface (`extern "C"`) — `file_bridge.h` only includes `<stddef.h>` + `<stdint.h>`, all types are opaque
2. Open/close lifecycle for each accessor type — caller owns the handle
3. Callback-based enumeration (`int (*cb)(..., void *ctx)`) — return 0 to continue, non-zero to stop
4. Errors use sentinel values (`UINT32_MAX` = not found, `0` = failure for size_t returns)

### File Handle

```c
AbcFileHandle *abc_file_open(const uint8_t *data, size_t len);
void            abc_file_close(AbcFileHandle *f);
uint32_t        abc_file_num_classes(const AbcFileHandle *f);
uint32_t        abc_file_class_offset(const AbcFileHandle *f, uint32_t idx);
size_t          abc_file_get_string(const AbcFileHandle *f, uint32_t offset, char *buf, size_t buf_len);
int             abc_file_validate_checksum(const AbcFileHandle *f);
// ... header access, index resolution, string metadata
```

### Data Accessors (open/close pattern)

| Accessor | Prefix | Wraps |
|----------|--------|-------|
| `AbcClassAccessor` | `abc_class_*` | `ClassDataAccessor` |
| `AbcMethodAccessor` | `abc_method_*` | `MethodDataAccessor` |
| `AbcFieldAccessor` | `abc_field_*` | `FieldDataAccessor` |
| `AbcCodeAccessor` | `abc_code_*` | `CodeDataAccessor` |
| `AbcProtoAccessor` | `abc_proto_*` | `ProtoDataAccessor` |
| `AbcLiteralAccessor` | `abc_literal_*` | `LiteralDataAccessor` |
| `AbcModuleAccessor` | `abc_module_*` | `ModuleDataAccessor` |
| `AbcAnnotationAccessor` | `abc_annotation_*` | `AnnotationDataAccessor` |
| `AbcDebugInfo` | `abc_debug_*` | `DebugInfoExtractor` |

### Builder (ABC file generation)

```c
AbcBuilder     *abc_builder_new(void);
void            abc_builder_free(AbcBuilder *b);
uint32_t        abc_builder_add_class(AbcBuilder *b, const char *descriptor);
uint32_t        abc_builder_class_add_method(AbcBuilder *b, uint32_t class_handle, ...);
const uint8_t  *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len);
// ... strings, fields, literals, protos, annotations, debug info, try-catch
```

The builder wraps `ItemContainer` + `FileWriter` (memory-backed). `abc_builder_finalize` computes layout and returns a pointer to the serialized `.abc` bytes (valid until builder is freed).

### Version Utilities

```c
void abc_get_current_version(uint8_t out[4]);
void abc_get_min_version(uint8_t out[4]);
int  abc_is_version_less_or_equal(const uint8_t current[4], const uint8_t target[4]);
```

Delegates to upstream's `file_format_version.cpp` (`IsVersionLessOrEqual`), avoiding manual reimplementation.

### Literal Value Conversion

The bridge converts C++ `std::variant<bool, void*, uint8_t, uint16_t, uint32_t, uint64_t, float, double, StringData>` to a C union via `std::visit`, dispatching on the variant's active type rather than `LiteralTag` values. This means adding new tags upstream (with existing types) requires zero bridge changes.

## Build Dependencies

- Ruby 2.5+ (runs gen.rb code generation)
- C++17 compiler (compiles bridge + vendor sources)
- `cc` crate (compiles C++ during Rust build)
- `bindgen` crate (generates Rust FFI bindings)

## Statistics

- 69 vendor files (all identical to upstream)
- 9 shim files
- 14 vendor `.cpp` files + 1 bridge `.cpp` compiled
- Ruby generates 3 header files
- C bridge exports ~170 functions across 10 accessor types + builder
