# abcd-file-sys

> This document is intended for crate maintainers and contributors, covering the internal architecture, build pipeline, and API design of abcd-file-sys.
> If you just want to use the file format API, see the higher-level [`abcd-file`](../abcd-file/README.md) crate.

This crate provides ArkCompiler `.abc` file format C FFI bindings for Rust, wrapping arkcompiler's `libpandafile` C++ library via a thin C bridge layer. It exposes two generated artifacts through `src/lib.rs`:

- `bindings.rs` — raw `abc_*` FFI functions, produced by bindgen from `bridge/file_bridge.h` (allowlists `abc_.*` functions, `Abc.*` types, `ABC_.*` vars).
- `enum_bindings.rs` — vendor constants extracted directly from vendor C++ headers (a second bindgen pass over a build.rs-generated header), so Rust references vendor values instead of hand-maintained mirrors: `ABC_ACC_*` access flags (names auto-extracted from `modifiers.h`, values referencing the vendor constexprs) and the vendor enum classes `LiteralTag`, `ModuleTag`, `FunctionKind`, `SourceLang`, `Type::TypeId`, `MethodHandleType`.

## Directory Structure

```
abcd-file-sys/
├── build.rs                           # Ruby codegen → enums header → cc compile → bindgen ×2
├── Cargo.toml                         # (no `links` key; dependents use the crate directly)
├── src/
│   └── lib.rs                         # include!(bindings.rs) + include!(enum_bindings.rs)
│                                      # + Rust safe-type wrappers (FileType, AnnotationValueType, …)
│                                      # + in-crate integration tests
├── bridge/
│   ├── file_bridge.h                  # C wrapper header (extern "C", ~240 functions)
│   ├── file_bridge.cpp                # C wrapper implementation
│   └── shim/                          # Minimal shims (10 files, replacing heavy deps)
│       ├── vendor_fixups.h            # Force-included: missing transitive includes
│       ├── isa.h                      # Minimal ISA facade for vendored code that includes it
│       ├── pgo.h                      # ProfileOptimizer stub (no-op)
│       ├── securec.h                  # Huawei secure C library shim (memcpy_s wrapper)
│       ├── platform_compat.h          # MSVC compat (force-included with /FI on Windows)
│       ├── zlib.h                     # Inline adler32 implementation (no system zlib needed)
│       ├── os/file.h                  # Empty stub
│       ├── os/filesystem.h            # Empty stub
│       ├── os/mem.h                   # Non-owning os::mem::MapViewOfFile-style stub
│       └── utils/logger.h             # LOG macro shim — see "Logger shim" below
└── arkcompiler_runtime_core/          # git submodule (upstream, pinned; read-only)
    ├── isa/                           # gen.rb + isapi.rb + isa.yaml (Ruby codegen engine)
    ├── assembler/                     # annotation value type validation headers
    ├── libpandafile/                  # Core file format library
    │   ├── *.h / *.cpp                # Data accessors, file items, debug info
    │   ├── templates/                 # ERB templates
    │   └── *.rb / *.yaml              # Ruby codegen modules + type data
    ├── templates/plugin_options.rb    # Common codegen options module
    └── libpandabase/                  # include/libpandabase/** + utils/utf.cpp
```

### Upstream code: a pinned git submodule

The upstream repo
([openharmony/arkcompiler_runtime_core](https://github.com/openharmony/arkcompiler_runtime_core))
is a **git submodule at the crate root** (`abcd-file-sys/arkcompiler_runtime_core`),
pinned to a proven upstream commit. **Never edit inside the submodule** —
local adaptation lives in `bridge/shim/` only. After cloning, run
`git submodule update --init`. See `../design/vendor-sync.md` for the pin
policy and the weekly upstream tag radar.

Missing transitive includes that the upstream build provides are injected via
`vendor_fixups.h` (force-included with `-include` / `/FI`), avoiding any
upstream file modifications.

`pgo.h` (ProfileOptimizer) is stubbed in `bridge/shim/` and shadowed via
include path priority — the upstream version depends on runtime
infrastructure we don't have.

The full upstream subtree is present, but `build.rs` compiles only the
translation units the bridge needs (the same set as the old vendored
subset): the `libpandafile` data accessors / item container / writer,
`libpandabase/utils/utf.cpp`, and `bridge/file_bridge.cpp`. Excluded on
purpose: `file_reader.cpp` (legacy-tree drift — it calls
`MethodParamItem::AddRuntimeAnnotation`, which legacy `file_items.h` never
declares; the consistent implementation lives in `static_core/libarkfile`),
plus `file.cpp`, `pgo.cpp`, and `method_handle_data_accessor.cpp` (runtime
machinery the bridge never used).

## Build Pipeline Overview

```
isa.yaml / types.yaml (data sources)
    │
    ▼
gen.rb + per-template requires (Ruby pipeline, 3 invocations)
    │
    ├──► source_lang_enum.h   (SourceLang enum: ECMASCRIPT, ARKTS, ...)
    ├──► type.h               (Type class: TypeId enum + property queries)
    └──► file_format_version.h (version constants + API version mapping)
            │
            ▼
build.rs Phase 1b: file_bridge_enums.h — ACC_* names parsed from
modifiers.h, values referenced from vendor headers (no hand mirrors)
            │
            ▼
cc compiles the bridge + the upstream translation units it needs:
the libpandafile accessor/container/writer .cpp set (see above),
libpandabase/utils/utf.cpp + bridge/file_bridge.cpp
            │
            ▼
bindgen pass 1: bridge/file_bridge.h → bindings.rs
bindgen pass 2: file_bridge_enums.h → enum_bindings.rs
            │
            ▼
src/lib.rs (include! both artifacts)
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

- Use Rust `build.rs` to drive Ruby instead of CMake/GN.
- Vendor `.cpp` files compiled directly — no CMake target dependencies.
- `vendor_fixups.h` force-include replaces upstream's transitive header propagation (PCH / CMake target includes).
- `-DSUPPORT_KNOWN_EXCEPTION` enables the C++ exception path in the `THROW_IF` macro, avoiding dependency on upstream's `LOG(FATAL)` infrastructure.
- `-DNDEBUG` eliminates C++ debug assertion runtime dependencies.
- `bridge/shim/zlib.h` provides inline `adler32` (byte-equivalent to the reference implementation) — no system zlib linkage needed.

### Logger shim (intentional semantic change — keep documented)

`bridge/shim/utils/logger.h` makes vendored `LOG(FATAL)` print to `std::cerr` and CONTINUE instead of aborting (vendor-audit ruling #A4: a data-path failure must not kill the host process). Vendored FATAL sites (e.g. `line_number_program.h`, `debug_info_extractor.cpp`) thus degrade to print-and-continue. This is a deliberate weakening for embedding safety; on any future vendor sync, do NOT re-arm it without a maintainer decision.

## C Bridge API Design

`bridge/file_bridge.h` + `bridge/file_bridge.cpp` (~240 exported functions)

Design principles:

1. Pure C interface (`extern "C"`) — `file_bridge.h` only includes `<stddef.h>` + `<stdint.h>`; all types are opaque.
2. Open/close lifecycle for each accessor type — caller owns the handle.
3. **Every entry point is exception-guarded**: each `extern "C"` function body is wrapped in `try { … } catch (…)`, converting C++ exceptions (bad_alloc, vendored aborts reachable through allocation paths) to sentinel returns (audit findings #11/#12; ~270 guarded sites).
4. Callback-based enumeration — see the early-stop contract below.
5. Sentinel conventions:
   - `UINT32_MAX` — not found / absent (offsets, indices).
   - `SIZE_MAX` — failure of UTF-16 string queries; **zero is a valid empty string**. Query with `buf=nullptr` to size the buffer.
   - Boolean-style queries return 1/0 (`abc_is_version_less_or_equal`, `abc_contains_literal_array_in_header`, `abc_method_is_external`, …).
   - Builder handles are `uint32_t` indices; the high bit `0x80000000` tags foreign (external) class/method/field handles.

### Callback early-stop contract

`int`-returning enumeration callbacks imply early stop, but it is honored ONLY where the function's doc says so — currently the debug-info family (`abc_debug_get_line_table` / `_get_column_table` / `_get_local_vars` / `_get_parameter_info` / `_get_method_list`) and `abc_param_annotations_enumerate`. Everywhere else (all `*_enumerate_*annotations` sites, `abc_class_enumerate_interfaces`, `abc_method_enumerate_types_in_proto`, `abc_code_enumerate_try_blocks_full`) the callback's return is discarded: the vendored plain `Enumerate*` accessors deliver all items and cannot stop early (upstream models early stop as separate `*WithEarlyStop` functions, which this bridge does not wrap). The Rust wrappers always collect-all. The authoritative statement lives in `file_bridge.h` at the callback typedefs (audit finding #15).

### File Handle

```c
AbcFileHandle *abc_file_open(const uint8_t *data, size_t len);   // header file_size <= len enforced
void           abc_file_close(AbcFileHandle *f);
const char    *abc_file_open_error(void);  // thread-local reason for the last failed open
uint32_t       abc_file_num_classes(const AbcFileHandle *f);
size_t         abc_file_get_string_utf16(const AbcFileHandle *f, uint32_t offset,
                                         uint16_t *buf, size_t buf_len);  // SIZE_MAX on error
int            abc_file_validate_checksum(const AbcFileHandle *f);
// ... header access, index resolution, string metadata
```

`abc_file_open` copies the input into a 16-byte-padded buffer (protects the fixed-width overreads in vendored accessors) and rejects headers whose declared `file_size` exceeds the actual length (audit finding #3).

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
| `AbcIndexAccessor` | `abc_index_*` | `IndexAccessor` (index-region re-derivation, with the bounds check vendor lacks) |

### Tolerant literal-array enumeration

The vendored `LiteralDataAccessor::EnumerateLiteralVals` aborts on `LiteralTag` 0x00 (`TAGVALUE`/`INTEGER_8` — a legal 1-byte integer literal in real 12.x files, audit finding #A1) and on unknown tags. The bridge therefore walks `[tag][value]` pairs itself: tag 0x00 is treated as a 1-byte integer, every read is bounds-checked, unknown/truncated items stop enumeration (never abort), and every tag literal is pinned to the vendored `LiteralTag` enum with a `static_assert` (audit finding #13). Typed arrays (`ARRAY_U1`…`ARRAY_STRING`) deliver their array-data offset through the callback like every other value.

### Builder (ABC file generation)

```c
AbcBuilder     *abc_builder_new(void);
void            abc_builder_free(AbcBuilder *b);
uint32_t        abc_builder_add_class(AbcBuilder *b, const char *descriptor);
uint32_t        abc_builder_class_add_method_with_proto(AbcBuilder *b, uint32_t class_handle,
                                                        const char *name, uint32_t proto_handle, ...);
int             abc_builder_relocate_code_id(AbcBuilder *b, uint32_t method_handle,
                                             uint32_t byte_offset, uint32_t operand,
                                             enum AbcCodeEntityKind kind, uint32_t target_handle);
const uint8_t  *abc_builder_finalize_with_code_ids(AbcBuilder *b, uint32_t *out_len,
                                                   AbcCodeIdUpdater updater);
// ... strings, fields, literals, protos, annotations, debug info, try-catch
```

The builder wraps `ItemContainer` + a memory-backed writer. `finalize` computes the layout, applies deferred code-id relocations through the caller-supplied ISA updater (so file-sys never duplicates ISA encoding rules), writes the file, and backfills the adler32 checksum over `[version..end]` (the memory writer performs no checksum counting, unlike upstream `FileWriter` — audit finding #A8). A second `finalize` on the same builder is idempotent: literal-item staging is flushed with replace semantics and relocation patching overwrites the operand field (see the field comments in `file_bridge.cpp` and `abcd-file/tests/double_finalize.rs`).

Per-builder API policy: each builder stores its own (api, sub_api) and a `BuilderVersionScope` activates it under a mutex around every version-sensitive vendored call, so interleaved/concurrent builders never inherit each other's settings (upstream keeps these as process globals). Select the policy before creating any items.

### Version Utilities

```c
void abc_get_current_version(uint8_t out[4]);
void abc_get_min_version(uint8_t out[4]);
int  abc_is_version_less_or_equal(const uint8_t current[4], const uint8_t target[4]);
int  abc_contains_literal_array_in_header(const uint8_t ver[4]);
```

Delegates to upstream's `file_format_version.cpp`, avoiding manual reimplementation. (Some version helpers are unused inside this repo but remain part of the published surface — the dead-surface policy is a maintainer decision, not a cleanup list.)

## Build Dependencies

- Ruby 2.5+ (runs gen.rb code generation)
- C++17 compiler (compiles bridge + vendor sources)
- `cc` crate (compiles C++ during Rust build)
- `bindgen` crate (generates Rust FFI bindings)

## Statistics

- Upstream code: `arkcompiler_runtime_core` submodule (pinned; read-only) + 10 shim files
- C++ sources compiled: the bridge-needed libpandafile `.cpp` set + libpandabase `utf.cpp` + `file_bridge.cpp`
- Ruby generates 3 headers; build.rs generates `file_bridge_enums.h`
- 2 bindgen passes: `bindings.rs` (C bridge API) + `enum_bindings.rs` (vendor constants)
- C bridge exports ~240 functions across 10 accessor types + index accessor + builder

## Publishing

This crate is publish-*shaped* but unpublished. Note that `cargo package` /
`cargo publish` would now drag the full `arkcompiler_runtime_core` submodule
(hundreds of MB) into the `.crate`. If publishing ever happens, the strategy
needs an `exclude` for the submodule plus pre-generated sources (vendoring the
generated headers + the few compiled C++ files into the package). Registered
decision — no action for now.
