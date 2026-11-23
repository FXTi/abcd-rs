# abcd-file-sys

> This document is intended for crate maintainers and contributors, covering the internal architecture, build pipeline, and API design of `abcd-file-sys`.
> If you just want to use the file format API, see the higher-level [`abcd-file`](../abcd-file/README.md) crate.

This crate provides ArkCompiler `.abc` file format C FFI bindings for Rust, wrapping `arkcompiler_runtime_core`'s `libpandafile` C++ library via a thin C bridge layer and pre-generated Rust bindings. It exposes two pre-generated artifacts through `src/lib.rs`:

- `src/generated/bindings.rs` — raw `abc_*` FFI functions, opaque handle structs, callbacks, and `ABC_*` constants generated offline by `scripts/vendor-gen.py` from `bridge/file_bridge.h`.
- `src/generated/enum_bindings.rs` — upstream constants extracted offline by `scripts/vendor-gen.py` directly from `vendor/` headers (`ABC_ACC_*` access flags from `modifiers.h`, plus `LiteralTag`, `ModuleTag`, `FunctionKind`, `SourceLang`, `Type::TypeId`, and `MethodHandleType`), bidirectional-locked at C++ compile time by 109 `static_assert`s in `vendor/generated/file_bridge_enum_checks.h`.

## Directory Structure

```
abcd-file-sys/
├── build.rs                           # Pure cc::Build compiling libpandafile + file_bridge.cpp
├── Cargo.toml                         # Depends only on `cc` at build time (zero bindgen/Ruby)
├── src/
│   ├── lib.rs                         # Re-exports src/generated/{bindings,enum_bindings}.rs
│   │                                  # + safe-type wrappers (FileType, AnnotationValueType, …)
│   │                                  # + in-crate integration tests
│   └── generated/
│       ├── bindings.rs                # Pre-generated C FFI bindings for file_bridge.h
│       └── enum_bindings.rs           # Pre-generated vendor enum & access-flag constants
└── bridge/
    ├── file_bridge.h                  # C wrapper header (extern "C", ~186 functions)
    ├── file_bridge.cpp                # C wrapper implementation + static_assert enum checks
    └── shim/                          # Crate-local shims
        ├── vendor_fixups.h            # Force-included (-include / /FI): missing transitive includes
        └── isa.h                      # Minimal ISA facade for vendored headers that include it

../vendor/                             # Shared workspace vendor snapshot & shims
├── UPSTREAM.toml                      # Upstream tag, commit SHA, and per-file SHA-256 manifest
├── arkcompiler_runtime_core/          # Curated upstream snapshot (isa, libpandafile, libpandabase, ...)
├── generated/                         # Pre-generated upstream C++ headers + file_bridge_enum_checks.h
└── shim/                              # Shared C++ shims
    ├── platform_compat.h              # MSVC compat (force-included with /FI on Windows)
    ├── pgo.h                          # ProfileOptimizer no-op stub
    ├── securec.h                      # Huawei secure C library shim (memcpy_s / memset_s)
    ├── zlib.h                         # Inline Adler-32 implementation (no system zlib needed)
    ├── os/{file.h,filesystem.h,mem.h} # Lightweight OS/memory stubs
    └── utils/logger.h                 # Non-aborting LOG macro shim — see "Logger shim" below
```

### Upstream code: curated `vendor/` snapshot

Upstream sources from [`openharmony/arkcompiler_runtime_core`](https://github.com/openharmony/arkcompiler_runtime_core) live in [`../vendor/arkcompiler_runtime_core/`](../vendor/arkcompiler_runtime_core) (336 files, `1.8 MB`, test directories stripped) and are cryptographically pinned by per-file SHA-256 in [`../vendor/UPSTREAM.toml`](../vendor/UPSTREAM.toml). **Never edit inside `vendor/arkcompiler_runtime_core/`** — CI (`vendor-verify`) rejects any hash drift or stray file. Local adaptation lives in `../vendor/shim/` and `bridge/shim/` only. See [`../design/vendor-sync.md`](../design/vendor-sync.md).

Missing transitive includes that the upstream CMake/GN build provides are injected via `bridge/shim/vendor_fixups.h` (force-included with `-include` / `/FI`), avoiding any upstream file modifications.

`pgo.h` (`ProfileOptimizer`) is stubbed in `../vendor/shim/pgo.h` and shadowed via include-path priority — the upstream version depends on runtime infrastructure we do not build.

`build.rs` compiles only the translation units the bridge needs: the `libpandafile` data accessors / item container / writer, `libpandabase/utils/utf.cpp`, and `bridge/file_bridge.cpp`. Excluded on purpose: `file_reader.cpp` (legacy-tree drift — it calls `MethodParamItem::AddRuntimeAnnotation`, which legacy `file_items.h` never declares; the consistent implementation lives in `static_core/libarkfile`), plus `file.cpp`, `pgo.cpp`, and `method_handle_data_accessor.cpp` (unused runtime machinery).

## Build Pipeline Overview

### 1. Offline generation (`python3 scripts/vendor-gen.py codegen`, verified in CI by `vendor-verify`)

```
vendor/arkcompiler_runtime_core/{isa/isa.yaml, libpandafile/types.yaml, ...}
    │
    ├──► Ruby (gen.rb + per-template requires)
    │       ├──► vendor/generated/source_lang_enum.h
    │       ├──► vendor/generated/type.h
    │       ├──► vendor/generated/file_format_version.h
    │       ├──► vendor/generated/bytecode_instruction_enum_gen.h
    │       ├──► vendor/generated/bytecode_instruction-inl_gen.h
    │       ├──► vendor/generated/isa_constants_gen.h
    │       └──► vendor/generated/ark_version.h
    │
    ├──► Vendor C++ header enum/constexpr extractor
    │       ├──► src/generated/enum_bindings.rs (+ rustfmt)
    │       └──► vendor/generated/file_bridge_enum_checks.h (109 C++17 static_asserts)
    │
    └──► C99 header parser on bridge/file_bridge.h
            └──► src/generated/bindings.rs (+ rustfmt)
```

### 2. Ordinary `cargo build` (`build.rs`)

`build.rs` runs only `cc::Build` to compile the C++17 bridge and `libpandafile` translation units. `bridge/file_bridge.cpp` includes `file_bridge_enum_checks.h`, proving at C++ compile time on every target OS/architecture that every constant in `src/generated/enum_bindings.rs` equals the exact upstream C++ enum/constexpr value — without invoking `bindgen` or `libclang` over C++17 STL headers.

### Logger shim (intentional semantic change — keep documented)

`../vendor/shim/utils/logger.h` makes vendored `LOG(FATAL)` print to `std::cerr` and CONTINUE instead of aborting (vendor-audit ruling #A4: a data-path failure must not kill the host process). Vendored FATAL sites (e.g. `line_number_program.h`, `debug_info_extractor.cpp`) thus degrade to print-and-continue. This is a deliberate weakening for embedding safety; on any future vendor sync, do NOT re-arm it without a maintainer decision.

## C Bridge API Design

`bridge/file_bridge.h` + `bridge/file_bridge.cpp` (~186 exported functions)

Design principles:

1. Pure C99 interface (`extern "C"`) — `file_bridge.h` only includes `<stddef.h>` + `<stdint.h>`; all handle types are opaque.
2. Open/close lifecycle for each accessor type — caller owns the handle.
3. **Every entry point is exception-guarded**: each `extern "C"` function body is wrapped in `try { … } catch (…)`, converting C++ exceptions (`bad_alloc`, vendored `THROW_IF` exceptions) to sentinel returns (audit findings #11/#12).
4. Callback-based enumeration — see the early-stop contract below.
5. Sentinel conventions:
   - `UINT32_MAX` — not found / absent (offsets, indices).
   - `SIZE_MAX` — failure of UTF-16 string queries; **zero is a valid empty string**. Query with `buf=nullptr` to size the buffer.
   - Boolean-style queries return 1/0 (`abc_file_validate_checksum`, `abc_file_is_external`, `abc_builder_set_file_version`, …).
   - Builder handles are `uint32_t` indices; the high bit `0x80000000` tags foreign (external) class/method/field handles.

### Callback early-stop contract

`int`-returning enumeration callbacks imply early stop, but it is honored ONLY where the function's doc says so — currently the debug-info family (`abc_debug_get_line_table` / `_get_column_table` / `_get_local_vars` / `_get_parameter_info`) and `abc_param_annotations_enumerate`. Everywhere else (all 12 `abc_{class,method,field}_enumerate_{,runtime_,type_,runtime_type_}annotations` sites and `abc_code_enumerate_try_blocks_full`) the callback's return is discarded: the vendored plain `Enumerate*` accessors deliver all items and cannot stop early (upstream models early stop as separate `*WithEarlyStop` functions, which this bridge does not wrap). The Rust wrappers always collect-all. The authoritative statement lives in `file_bridge.h` at the callback typedefs (audit finding #15).

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

The vendored `LiteralDataAccessor::EnumerateLiteralVals` aborts on `LiteralTag` `0x00` (`TAGVALUE`/`INTEGER_8` — a legal 1-byte integer literal in real 12.x files, audit finding #A1) and on unknown tags. The bridge therefore walks `[tag][value]` pairs itself: tag `0x00` is treated as a 1-byte integer, every read is bounds-checked, unknown/truncated items stop enumeration (never abort), and every tag literal is pinned to the vendored `LiteralTag` enum with a `static_assert` (audit finding #13). Typed arrays (`ARRAY_U1`…`ARRAY_STRING`) deliver their array-data offset through the callback like every other value.

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

The builder wraps `ItemContainer` + a memory-backed writer. `finalize` computes the layout, applies deferred code-id relocations through the caller-supplied ISA updater (so `abcd-file-sys` never duplicates ISA encoding rules), writes the file, and backfills the Adler-32 checksum over `[version..end]` (the memory writer performs no checksum counting, unlike upstream `FileWriter` — audit finding #A8). A second `finalize` on the same builder is idempotent: literal-item staging is flushed with replace semantics and relocation patching overwrites the operand field (see `abcd-file/tests/integration/double_finalize.rs`).

Per-builder API policy: each builder stores its own `(api, sub_api)` and a `BuilderVersionScope` activates it under a mutex around every version-sensitive vendored call, so interleaved/concurrent builders never inherit each other's settings (upstream keeps these as process globals). Select the policy (`abc_builder_set_api` or `abc_builder_set_file_version`) before creating any items.

## Build Dependencies

- **Ordinary `cargo build` / `cargo test`**: C++17 compiler + `cc` crate only.
- **Offline binding regeneration (`scripts/vendor-gen.py`)**: Python 3 + Ruby 2.5+ + `rustfmt`.

## Statistics

- Upstream code: shared `vendor/arkcompiler_runtime_core/` snapshot (336 files, `1.8 MB`) + 8 shared shims in `vendor/shim/` + 2 crate-local shims in `bridge/shim/`
- C++ sources compiled: 16 `libpandafile` `.cpp` files + `libpandabase/utils/utf.cpp` + `bridge/file_bridge.cpp`
- Pre-generated bindings: `src/generated/bindings.rs` + `src/generated/enum_bindings.rs` + 109 `static_assert` checks in `vendor/generated/file_bridge_enum_checks.h`
- C bridge exports ~186 functions across 10 accessor types + index accessor + builder + vendor-name pins

## Publishing

This crate is unpublished; its `build.rs` references the shared workspace `../vendor/` directory (`1.8 MB`). If standalone crates.io publishing is ever desired, staging `vendor/` inside the crate package at release time is straightforward since all codegen artifacts are already pre-generated and submodule-free.
