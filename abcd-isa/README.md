# abcd-isa

Safe Rust API for the ArkCompiler bytecode instruction set (`0.0.0.2` legacy and `9.0.0.0`..`24.0.0.0` second-generation `.abc` formats), providing pure-Rust bytecode decoding, deterministic Fenwick-tree branch-relaxation encoding, zero-allocation entity operand relocation, and `.abc` format version queries.

## Purpose & Layering Contract

`abcd-isa` is the safe instruction-set boundary above [`abcd-isa-sys`](../abcd-isa-sys/README.md) and below `abcd-file` (`Cargo.toml` depends only on `abcd-isa-sys` and `thiserror`):

- Executes `decode`, `decode_legacy`, `encode`, `relocate_entity_id`, and all `Bytecode` classification/operand queries in 100% pure Safe Rust (`#[forbid(unsafe_code)]`); `unsafe` is confined solely to `src/version.rs` with explicit `// SAFETY:` invariants, and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]` is enforced across non-test code.
- Re-exports the generated `Bytecode` model (`Bytecode`, `Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`, `insn`, `BytecodeFlags`, `ExceptionType`) and validates pure-Rust codec parity against the vendored C++ implementation in differential integration tests.
- Implements mechanical instruction encoding and decoding only: `.abc` container layout and constant-pool offset resolution belong to `abcd-file`, while semantic opcode selection and SSA lifting/lowering belong to `abcd-lift` and `abcd-lower`.

## Architecture / Module Map

| Module | Public Surface | Responsibility |
|--------|----------------|----------------|
| `src/lib.rs` | Crate root & re-exports | Re-exports `Bytecode`, operand newtypes/views (`Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`), `insn` constructors, and `const fn` classification flags |
| `src/decoder.rs` | `decode`, `DecodeError` | Pure-Rust two-pass modern decoder (`9.0.0.0`..`24.0.0.0`): `Bytecode::decode_modern` scan into `(Bytecode, u32)` followed by `i128`-checked binary-search jump resolution into `Label(insn_index)` |
| `src/legacy.rs`, `src/legacy_table.rs` | `decode_legacy` | Pure-Rust translator for pre-2022-08-18 OpenHarmony 3.0/3.1 format `0.0.0.2` bytecode (`0xff`-prefixed ECMAScript opcodes, direct 32-bit string offsets, synthesized `Imm(0)` IC slots) into `Bytecode` (`tools/gen_legacy_table.py`) |
| `src/emitter.rs` | `encode`, `EncodeError` | Pure-Rust deterministic encoder (`N20`): pre-packs narrowest non-jump formats and relaxes all 17 jump mnemonics via an `O(N + J log N)` Fenwick tree (`imm8` -> `imm16` -> `imm32` or inverted-branch + `jmp.32` trampoline) |
| `src/relocation.rs` | `relocate_entity_id`, `RelocationError` | Pure-Rust zero-allocation in-place entity-ID slot patcher via `modern_entity_id_slot`, paired with `Bytecode::entity_operands_inline()` and `Bytecode::operands_inline()` |
| `src/version.rs` | `Version` | Queries 4-byte `.abc` format versions via `file_format_version`: `current()` (`24.0.0.0`), `min_supported()`, `for_api()`, `for_api_sub()`, `is_in_supported_range()`, `is_blocked()`, and `incompatible_versions()` |

## Key Invariants

- **Deterministic Fenwick branch relaxation (`N20`, #43)**: `encode` uses zero `HashMap`/`HashSet` state and zero call-stack recursion, supporting `> 32 KiB` forward and backward branches across all 17 jump mnemonics while always preserving `offsets.len() == instructions.len()`.
- **Instruction-indexed `Label` round-trip symmetry**: `decode`, `decode_legacy`, and `encode` represent jump targets as `Label(u32)` instruction indices rather than raw byte offsets (`DecodeError::InvalidJumpTarget` / `EncodeError::LabelOutOfBounds` on invalid targets).
- **C++ differential oracle parity (Decision D1)**: Integration tests exhaustively verify pure-Rust `decode`, `relocate_entity_id`, classification bitmasks, and format selection across all `0..=0xFFFF` opcodes and operand width boundaries against the vendored C++ `isa_bridge` / `BytecodeEmitter`.
- **No silent truncation or partial mutation**: `encode` rejects out-of-width operands with `EncodeError::OperandOutOfRange`, `relocate_entity_id` checks width before writing in place, and malformed inputs always return typed `Result` errors without panicking.

Design references: [`../design/isa.md`](../design/isa.md), [`../design/isa-compat.md`](../design/isa-compat.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust
use abcd_isa::{
    Bytecode, EntityId, EntityKind, Label, Version, decode, encode, insn, relocate_entity_id,
};

let program: Vec<Bytecode> = vec![
    insn::LdaStr::new(EntityId(1)),
    insn::Jmp::new(Label(3)),
    insn::Ldundefined::new(),
    insn::Return::new(),
];

let (mut bytes, offsets) = encode(&program).unwrap();
assert_eq!(offsets.len(), program.len());

// Patch the first instruction's entity-ID operand (ordinal 0) in place:
relocate_entity_id(&mut bytes[offsets[0] as usize..], 0, EntityId(42)).unwrap();

let decoded = decode(&bytes).unwrap();
assert_eq!(
    decoded[0].0.entity_operands(),
    vec![(EntityKind::StringId, EntityId(42))]
);
assert_eq!(decoded[1].0, Bytecode::Jmp(Label(3)));
assert!(Version::new(12, 0, 6, 0).is_in_supported_range());
```

## Verification

Run local unit, integration, differential oracle, lint, and documentation checks without Docker:

```sh
./scripts/test-local.sh crate abcd-isa
cargo test -p abcd-isa
cargo clippy -p abcd-isa --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-isa --no-deps
```
