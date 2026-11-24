# abcd-isa-sys

Low-level C FFI bindings and offline-generated Rust instruction model for the ArkCompiler bytecode ISA (`24.0.0.0`). Downstream workspace crates should depend on the safe [`abcd-isa`](../abcd-isa/README.md) wrapper rather than calling raw `abcd-isa-sys` FFI symbols directly.

## Purpose & Layering Contract

`abcd-isa-sys` sits at the bottom of the workspace dependency graph with zero `abcd-*` dependencies (`bitflags` at runtime, `cc` at build time). Its layering contract is strictly mechanical:

- Expose the 34-function C99 `extern "C"` bridge (`isa_*`) over the vendored C++17 `BytecodeInst`, `BytecodeEmitter`, and `file_format_version` implementations.
- Provide the offline-generated mnemonic-grouped `Bytecode` enum, operand types (`Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`), per-mnemonic constructors (`insn::*`), and classification bitflags (`BytecodeFlags`, `ExceptionType`).
- Confine raw pointers and C++ interop to this crate so [`abcd-isa`](../abcd-isa/README.md) can expose a 100% safe decoding, encoding, relocation, and version API to `abcd-file` and higher layers.

## Architecture / Module Map

`abcd-isa-sys` follows the Route A pre-generated `vendor/` snapshot pipeline: Ruby ERB templates and C99 header parsing run **offline** via `scripts/vendor-gen.py`, while ordinary `cargo build` runs invoke only `cc::Build` over committed C++17 and Rust files with zero external build-time codegen tools.

| Path | Responsibility |
|------|----------------|
| `build.rs` | Pure `cc::Build` script compiling 3 C++17 translation units (`bridge/isa_bridge.cpp`, `../vendor/arkcompiler_runtime_core/libpandafile/file_format_version.cpp`, and `bytecode_emitter.cpp`) with `-DNDEBUG` |
| `bridge/isa_bridge.h` / `.cpp` | Pure C99 `extern "C"` bridge (34 functions): stateless opcode/format/size queries, operand extractors, `isa_update_id` in-place patching, classification predicates, `.abc` version queries, and stateful `IsaEmitter` |
| `bridge/shim/file.h` | Force-included `LIBPANDAFILE_FILE_H` stub isolating standalone ISA compilation from OS/filesystem container headers, paired with shared shims in `../vendor/shim/` |
| `bridge/generated/` | Pre-generated C++ tables from `templates/*.erb`: `isa_bridge_emit_dispatch.h` (width-checked generic emitter switch) and `isa_bridge_valid_opcode.h` (assigned-opcode lookup) |
| `src/generated/bindings.rs` | Pre-generated Rust `extern "C"` declarations and `ISA_*` sentinel constants parsed offline from C99 `bridge/isa_bridge.h` |
| `src/generated/bytecode.rs` | Pre-generated Rust `Bytecode` enum (268 mnemonics covering 332 opcodes across unprefixed + `callruntime`/`deprecated`/`wide`/`throw` prefixes), `insn` constructors, and operand/flag views from `templates/bytecode.rs.erb` |
| `src/lib.rs` | Crate root re-exporting `bindings.rs` and `bytecode.rs`, plus raw-FFI unit tests covering unbound-label sentinels, classification flags, and version queries |

## Key Invariants

- **Immutable SHA-256 `vendor/` snapshot**: Upstream sources under `../vendor/arkcompiler_runtime_core/` are strictly read-only and verified hash-for-hash against `../vendor/UPSTREAM.toml` alongside byte-identical codegen reproduction by `python3 scripts/vendor-gen.py verify` in CI (`vendor-verify`). Local C++ adaptations live exclusively in `../vendor/shim/` and `bridge/shim/file.h`.
- **Pre-validated opcodes, zero FFI abort or unwind**: Under `-DNDEBUG`, upstream `Inst::GetFormat()` reaches `UNREACHABLE()` (`std::abort()`) on unassigned opcodes. Every opcode-derived entry point pre-validates via `isa_opcode_is_valid`, and all 34 C entry points wrap C++ execution in `try/catch (...)` to return sentinel codes (`0`, `0xFF`, `ISA_EMIT_*`, `ISA_BUILD_*`) instead of aborting or unwinding across `extern "C"`.
- **Storage-width checking before emission**: `isa_emitter_emit` range-checks every scalar operand against its encoded signed/unsigned bit width before calling `BytecodeEmitter`, returning `ISA_EMIT_OPERAND_OUT_OF_RANGE` rather than silently truncating.
- **Single source of ISA truth**: Opcode encodings, property/exception bitflags (`30` `BytecodeFlags`, `14` `ExceptionType` masks), and API-to-version tables derive directly from `isa.yaml` and `file_format_version` with zero hand-written mirrors.

Design references: [`../design/isa.md`](../design/isa.md), [`../design/isa-compat.md`](../design/isa-compat.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust
use abcd_isa_sys::{
    Bytecode, BytecodeFlags, EntityId, EntityKind, Imm, Label, Operand, Reg, insn,
};

let load_str: Bytecode = insn::LdaStr::new(EntityId(7));
assert_eq!(load_str.mnemonic(), "lda.str");
assert!(load_str.has_flag(BytecodeFlags::STRING_ID) && load_str.can_throw());
assert_eq!(
    load_str.entity_operands(),
    vec![(EntityKind::StringId, EntityId(7))]
);

let call: Bytecode = insn::Callthisrange::new(Imm(0), Imm(2), Reg(4));
assert!(call.is_range());
assert_eq!(
    call.operands(),
    vec![Operand::Imm(0), Operand::Imm(2), Operand::Reg(4)]
);

let jump: Bytecode = insn::Jmp::new(Label(0));
assert!(jump.is_jump() && jump.is_terminator());
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
