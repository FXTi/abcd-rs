# abcd-file-sys

Low-level C FFI bindings over ArkCompiler's `libpandafile` C++17 container reader and `ItemContainer` writer for `.abc` bytecode files. Downstream workspace crates should depend on the safe [`abcd-file`](../abcd-file/README.md) wrapper rather than calling raw `abcd-file-sys` FFI symbols directly.

## Purpose & Layering Contract

`abcd-file-sys` sits at the bottom of the workspace container stack with zero `abcd-*` dependencies (`cc` at build time only). Its layering contract is strictly mechanical:

- Expose the pure C99 `extern "C"` bridge (`bridge/file_bridge.h`, `abc_*`) over vendored `libpandafile` data accessors, `DebugInfoExtractor`, `ItemContainer`, and memory-backed `.abc` serialization.
- Re-export two offline-generated Rust binding modules through `src/lib.rs`: `src/generated/bindings.rs` (parsed from `bridge/file_bridge.h`) and `src/generated/enum_bindings.rs` (extracted from `vendor/` C++ headers and verified at C++ compile time by `vendor/generated/file_bridge_enum_checks.h`), alongside `#[repr(u8)]` tag wrappers (`FileType`, `AnnotationValueType`, `MethodHandleType`).
- Confine raw pointers, C++ exceptions, and manual handle lifecycles to this crate while delegating ISA instruction encoding/relocation callbacks (`AbcCodeIdUpdater`) to higher layers so `abcd-file-sys` never duplicates ISA rules.

## Architecture / Module Map

`abcd-file-sys` uses the offline pre-generated `vendor/` pipeline: `python3 scripts/vendor-gen.py codegen` regenerates C++ headers and Rust FFI bindings ahead of time, while `cargo build` invokes only `cc::Build` over committed C++17 and Rust sources (no `bindgen`, `libclang`, or Ruby required at build time).

| Path | Responsibility |
|------|----------------|
| `build.rs` | Pure `cc::Build` compiling 16 `libpandafile` `.cpp` units, `libpandabase/utils/utf.cpp`, and `bridge/file_bridge.cpp` with `-DSUPPORT_KNOWN_EXCEPTION` |
| `bridge/file_bridge.h` / `.cpp` | Pure C99 `extern "C"` interface (~190 functions): padded file handle, 10 open/close accessors (`class`, `method`, `field`, `code`, `proto`, `literal`, `module`, `annotation`, `debug`, `index`), tolerant and checked literal-array walkers, and `AbcBuilder` |
| `bridge/shim/` | Crate-local headers (`vendor_fixups.h` force-included via `-include`/`/FI`, plus minimal `isa.h` facade), paired with shared shims in `../vendor/shim/` (`logger.h`, `zlib.h`, `securec.h`, `pgo.h`, `os/*`) |
| `src/generated/bindings.rs` | Offline-generated Rust `extern "C"` declarations, opaque handle structs, callback typedefs, and `ABC_*` constants from `bridge/file_bridge.h` |
| `src/generated/enum_bindings.rs` | Offline-generated `ABC_ACC_*` modifier masks and upstream `LiteralTag`, `ModuleTag`, `FunctionKind`, `SourceLang`, `Type::TypeId`, and `MethodHandleType` constants locked by C++17 `static_assert`s |
| `src/lib.rs` | Crate root re-exporting generated FFI symbols, `TryFrom<u8>` wrappers (`FileType`, `AnnotationValueType`), and raw-bridge unit tests |

## Key Invariants

- **Immutable SHA-256 `vendor/` snapshot**: Upstream files under `../vendor/arkcompiler_runtime_core/` are read-only and verified against `../vendor/UPSTREAM.toml` (plus reproducible codegen output) by `python3 scripts/vendor-gen.py verify`. All local C++ adaptations live in `../vendor/shim/` and `bridge/shim/`.
- **Silent, non-aborting FFI exception firewall**: Every `extern "C"` entry point wraps C++ execution in `try { ... } catch (...)` and translates `FileAccessException`, `std::bad_alloc`, and vendored `LOG(FATAL)` / `LOG_IF(..., FATAL)` (which throw `std::runtime_error` under `SUPPORT_KNOWN_EXCEPTION` via `../vendor/shim/utils/logger.h`) into sentinel return values (`NULL`, `-1`, `UINT32_MAX`, `SIZE_MAX`) with zero host `stderr` output.
- **Bounds-checked untrusted input**: `abc_file_open` enforces `header.file_size <= len` and zero-pads the backing buffer by 16 bytes against fixed-width LEB128 reads; annotation array reads clamp counts against payload spans; `abc_literal_enumerate_vals` tolerates truncated header-table items while `abc_literal_enumerate_vals_checked` enforces strict structural validation for offset-referenced literal arrays.
- **Isolated, idempotent `AbcBuilder`**: Each builder scopes its `(api, sub_api)` version policy under an internal mutex (`BuilderVersionScope`), stages literal/module/LNP items so layout order never corrupts string offsets, supports 8-/16-/32-/64-bit scalar and entity annotation arrays, and computes the header Adler-32 checksum on every `finalize`.

Design references: [`../design/file-format.md`](../design/file-format.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust
use abcd_file_sys::{
    abc_builder_add_global_class, abc_builder_finalize, abc_builder_free, abc_builder_new,
    abc_builder_set_api, abc_file_close, abc_file_num_classes, abc_file_open,
    abc_file_validate_checksum,
};

unsafe {
    let b = abc_builder_new();
    assert!(!b.is_null());
    abc_builder_set_api(b, 12, c"beta1".as_ptr());
    assert_ne!(abc_builder_add_global_class(b), u32::MAX);

    let mut len = 0u32;
    let ptr = abc_builder_finalize(b, &mut len);
    assert!(!ptr.is_null() && len > 0);
    let bytes = std::slice::from_raw_parts(ptr, len as usize).to_vec();
    abc_builder_free(b);

    let f = abc_file_open(bytes.as_ptr(), bytes.len());
    assert!(!f.is_null());
    assert_eq!(abc_file_validate_checksum(f), 1);
    assert_eq!(abc_file_num_classes(f), 1);
    abc_file_close(f);
}
```

## Verification

Run local build, test, lint, and documentation checks without Docker:

```sh
./scripts/test-local.sh crate abcd-file-sys
python3 scripts/vendor-gen.py verify
cargo test -p abcd-file-sys -p abcd-file
cargo clippy -p abcd-file-sys -p abcd-file --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-file-sys -p abcd-file --no-deps
```

After modifying `bridge/file_bridge.h`, regenerate and verify offline bindings via `python3 scripts/vendor-gen.py codegen && python3 scripts/vendor-gen.py verify`.
