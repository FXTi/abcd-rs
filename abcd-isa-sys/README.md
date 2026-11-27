# abcd-isa-sys

Low-level C99 FFI oracle bindings for the vendored C++17 ArkCompiler bytecode ISA (`24.0.0.0`). Production workspace crates depend solely on pure-Rust [`abcd-isa`](../abcd-isa/README.md); `abcd-isa-sys` is linked only as a `[dev-dependencies]` differential verification oracle in `abcd-isa` integration tests.

## Purpose & Layering Contract

`abcd-isa-sys` sits at the bottom of the workspace dependency graph with zero runtime Rust crate dependencies (`cc` at build time only). Its layering contract is strictly mechanical:

- Expose the 34-function C99 `extern "C"` bridge (`isa_*`) over the vendored C++17 `BytecodeInst`, `BytecodeEmitter`, and `file_format_version` implementations.
- Confine raw pointers and C++ interop to this crate so [`abcd-isa`](../abcd-isa/README.md) runs in 100% pure Safe Rust (`#![forbid(unsafe_code)]`) with zero C++ toolchain requirement in production builds while remaining exhaustively cross-checked against upstream C++ in `cargo test`.

## Architecture / Module Map

`abcd-isa-sys` follows the Route A pre-generated `vendor/` snapshot pipeline: Ruby ERB templates and C99 header parsing run **offline** via `scripts/vendor-gen.py`, while `cargo test` invokes `cc::Build` over committed C++17 and Rust files with zero external build-time codegen tools.

| Path | Responsibility |
|------|----------------|
| `build.rs` | Pure `cc::Build` script compiling 3 C++17 translation units (`bridge/isa_bridge.cpp`, `../vendor/arkcompiler_runtime_core/libpandafile/file_format_version.cpp`, and `bytecode_emitter.cpp`) with `-DNDEBUG` and `-DSUPPORT_KNOWN_EXCEPTION` |
| `bridge/isa_bridge.h` / `.cpp` | Pure C99 `extern "C"` bridge (34 functions): stateless opcode/format/size queries, operand extractors, `isa_update_id` in-place patching, classification predicates, `.abc` version queries, and stateful `IsaEmitter` |
| `bridge/shim/file.h` | Force-included `LIBPANDAFILE_FILE_H` stub isolating standalone ISA compilation from OS/filesystem container headers, paired with release-checked `Span<T>` and `memcpy_s` shims in `../vendor/shim/` |
| `bridge/generated/` | Pre-generated C++ tables from `templates/*.erb`: `isa_bridge_emit_dispatch.h` (width-checked generic emitter switch) and `isa_bridge_valid_opcode.h` (assigned-opcode lookup) |
| `src/generated/bindings.rs` | Pre-generated Rust `extern "C"` declarations and `ISA_*` sentinel constants parsed offline from C99 `bridge/isa_bridge.h` |
| `src/lib.rs` | Crate root re-exporting `bindings.rs`, plus raw-FFI unit tests covering null-pointer guards, unbound-label sentinels, classification flags, and version queries |

## Key Invariants

- **Immutable SHA-256 `vendor/` snapshot**: Upstream sources under `../vendor/arkcompiler_runtime_core/` are strictly read-only and verified hash-for-hash against `../vendor/UPSTREAM.toml` alongside byte-identical codegen reproduction by `python3 scripts/vendor-gen.py verify` in CI (`vendor-verify`). Local C++ adaptations live exclusively in `../vendor/shim/` and `bridge/shim/file.h`.
- **Pre-validated opcodes, null guards, zero FFI abort or unwind**: Under `-DNDEBUG`, upstream `Inst::GetFormat()` reaches `UNREACHABLE()` (`std::abort()`) on unassigned opcodes. Every opcode-derived entry point pre-validates via `isa_opcode_is_valid`, checks nullable pointers before dereference, uses `new (std::nothrow)` for allocation, and wraps C++ execution in `try/catch (...)` to return sentinel codes (`0`, `0xFF`, `ISA_EMIT_*`, `ISA_BUILD_*`) instead of aborting or unwinding across `extern "C"`.
- **Storage-width checking before emission**: `isa_emitter_emit` range-checks every scalar operand against its encoded signed/unsigned bit width before calling `BytecodeEmitter`, returning `ISA_EMIT_OPERAND_OUT_OF_RANGE` rather than silently truncating.

Design references: [`../design/isa.md`](../design/isa.md), [`../design/isa-compat.md`](../design/isa-compat.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust
use abcd_isa_sys::{isa_get_version, isa_opcode_is_valid};

let mut ver = [0u8; 4];
unsafe {
    isa_get_version(ver.as_mut_ptr());
    assert_eq!(ver, [24, 0, 0, 0]);
    assert_eq!(isa_opcode_is_valid(0x00), 1);
}
```

## Verification

Run local unit, integration, lint, and documentation checks without Docker:

```sh
./scripts/test-local.sh crate abcd-isa-sys
cargo test -p abcd-isa-sys -p abcd-isa
cargo clippy -p abcd-isa-sys -p abcd-isa --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-isa-sys -p abcd-isa --no-deps
```

After editing `bridge/isa_bridge.h` or `templates/*.erb`, regenerate and verify offline bindings via `python3 scripts/vendor-gen.py codegen && python3 scripts/vendor-gen.py verify`.
