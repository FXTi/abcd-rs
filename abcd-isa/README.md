# abcd-isa

Safe Rust API for the ArkCompiler bytecode instruction set (`0.0.0.2` legacy and `9.0.0.0`..`24.0.0.0` second-generation `.abc` formats), providing bytecode decoding, label-indexed encoding with automatic jump widening, in-place entity operand relocation, and file format version queries.

## Purpose & Layering Contract

`abcd-isa` is the safe instruction-set boundary above [`abcd-isa-sys`](../abcd-isa-sys/README.md) and below `abcd-file` (`Cargo.toml` depends only on `abcd-isa-sys` and `thiserror`):

- Confines all `unsafe` FFI calls internally behind documented `// SAFETY:` invariants and enforces `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`.
- Re-exports the generated `Bytecode` data model (`Bytecode`, `Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`, `insn`, `BytecodeFlags`, `ExceptionType`) alongside fallible `decode`, `decode_legacy`, `encode`, `relocate_entity_id`, and `Version` APIs.
- Implements mechanical instruction encoding and decoding only: `.abc` container layout and constant-pool offset resolution belong to `abcd-file`, while semantic opcode selection and SSA lifting/lowering belong to `abcd-lift` and `abcd-lower`.

## Architecture / Module Map

| Module | Public Surface | Responsibility |
|--------|----------------|----------------|
| `src/lib.rs` | Crate root & re-exports | Re-exports `Bytecode`, operand newtypes/views (`Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`), `insn` constructors, and classification flags |
| `src/decoder.rs` | `decode`, `DecodeError` | Two-pass modern decoder (`9.0.0.0`..`24.0.0.0`): linear opcode/size/operand scan followed by `i128`-checked relative jump resolution into `Label(insn_index)` via binary search |
| `src/legacy.rs`, `src/legacy_table.rs` | `decode_legacy` | Translates pre-2022-08-18 OpenHarmony 3.0/3.1 format `0.0.0.2` bytecode (`0xff`-prefixed ECMAScript opcodes, direct 32-bit string offsets, synthesized `Imm(0)` IC slots) into the unified `Bytecode` enum (`tools/gen_legacy_table.py`) |
| `src/emitter.rs` | `encode`, `EncodeError` | Validates `Label` bounds, binds jump targets in C++ `BytecodeEmitter` (automatic narrow/wide format selection and short/far jump widening), and re-scans emitted bytes to return `(Vec<u8>, Vec<u32>)` instruction offsets |
| `src/relocation.rs` | `relocate_entity_id`, `RelocationError` | Patches an instruction's `n`-th entity-ID operand in place via `isa_update_id` and verifies round-trip width fit, paired with `Bytecode::entity_operands()` and `Bytecode::operands()` |
| `src/version.rs` | `Version` | Queries 4-byte `.abc` format versions: `current()` (`24.0.0.0`), `min_supported()`, `for_api()`, `for_api_sub()`, `is_in_supported_range()`, `is_blocked()`, and `incompatible_versions()` |

## Key Invariants

- **Instruction-indexed `Label` round-trip symmetry**: `decode`, `decode_legacy`, and `encode` all represent jump targets as `Label(u32)` instruction indices rather than raw byte offsets. Off-boundary decoded jumps fail with `DecodeError::InvalidJumpTarget`; out-of-range encoded labels fail with `EncodeError::LabelOutOfBounds`.
- **Monotonic second-generation decoding + zero-overhead legacy path**: Upstream `24.0.0.0` `isa.yaml` strictly extends `9.0.0.0`, `11.0.2.0`, and `12.0.6.0` with zero opcode renumbering, while `decode_legacy` is entered only when gated by the caller on `0.0.0.2` headers.
- **No silent truncation or partial buffer mutation**: `encode` rejects out-of-width scalar operands with `EncodeError::OperandOutOfRange`, and `relocate_entity_id` stages edits in a scratch buffer so `RelocationError::IdOutOfRange` or `MissingOperand` leaves caller bytes unchanged.
- **Total fallibility on untrusted inputs**: Truncated prefixes/instructions, unassigned opcodes, and unmapped legacy opcodes always return typed `DecodeError` values without panicking or aborting.

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
assert!(matches!(decoded[1].0, Bytecode::Jmp(Label(3))));
assert!(Version::new(12, 0, 6, 0).is_in_supported_range());
```

## Verification

Run local unit, integration, lint, and documentation checks without Docker:

```sh
./scripts/test-local.sh crate abcd-isa
cargo test -p abcd-isa-sys -p abcd-isa
cargo clippy -p abcd-isa-sys -p abcd-isa --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-isa-sys -p abcd-isa --no-deps
```
