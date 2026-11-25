# ISA & Bytecode Layer (`abcd-isa-sys`, `abcd-isa`)

The ISA layer provides safe, deterministic, table-driven decoding, encoding, operand inspection, and entity-ID relocation for ArkCompiler bytecode streams without hand-coding opcode tables.

---

## 1. Code Generation & FFI Architecture (`abcd-isa-sys`)

- **Authoritative Upstream Source**: Opcode definitions, instruction formats, prefixes (`wide.*`, `deprecated.*`, `callruntime.*`, `throw.*`), and property/exception flags derive directly from `vendor/arkcompiler_runtime_core/isa/isa.yaml` via `python3 scripts/vendor-gen.py codegen` (`vendor-sync.md`).
- **Hermetic Pre-Generated Tables**: Pre-generated C++ headers (`vendor/generated/`, `abcd-isa-sys/bridge/generated/`) and pure-Rust ISA codec/classification tables (`abcd-isa-sys/src/generated/`) are checked into Git and verified byte-for-byte in Tier-1 CI (`vendor-verify`), requiring zero Ruby or `bindgen`/`libclang` during `cargo build`.
- **Pure-Rust Hot Path + C++ Differential Oracle**:
  - `abcd-isa-sys` generates 100% pure-Rust `const fn` instruction classification (`BytecodeFlags`, `ExceptionType`), modern `24.0.0.0` `decode_modern`, `(byte_offset, byte_width)` `modern_entity_id_slot` lookup, and `classify_for_encode` format-selection & jump-inversion tables directly from `isa.yaml`.
  - `isa_bridge.cpp` wraps `file_format_version.cpp` (format/API version queries) and retains upstream `BytecodeInst` / `BytecodeEmitter` C99 entrypoints as an automated **differential test oracle** verifying bit-for-bit parity across all `246` ISA opcodes.

---

## 2. Safe Rust API (`abcd-isa`)

- **`Bytecode` Enum**: Strongly typed `Copy + Eq + Hash` instruction representation (`Reg`, `Imm`, `EntityId`, `Label`) covering all modern opcodes (`9.0.0.0`–`24.0.0.0`), with stack-allocated inline operand accessors (`entity_operands_inline`, `operands_inline`) for zero-allocation hot loops.
- **Modern & Legacy Decoders (100% Safe Rust)**:
  - `abcd_isa::decode(&[u8])`: Pure-Rust table-driven decoder for modern `9.0.0.0`–`24.0.0.0` instruction streams, returning `(Bytecode, byte_offset)` pairs and resolving PC-relative jump offsets into instruction-index `Label`s via binary search.
  - `abcd_isa::decode_legacy(&[u8])`: Pure-Rust table-driven translator for legacy `0.0.0.2` (OpenHarmony 3.0/3.1) instruction streams (`src/legacy_table.rs`) into canonical `Bytecode` variants (`ADR-08`).
- **Linear Branch-Relaxation Encoder & Zero-Alloc Relocation (100% Safe Rust)**:
  - `abcd_isa::encode(&[Bytecode])`: Deterministic (`N20`), zero-FFI encoder using Fenwick-tree (`O(N + J log N)`) monotone branch relaxation. Automatically selects minimal operand widths, widens jumps (`imm8` → `imm16` → `imm32`), and synthesizes inverted-condition short jump + `jmp.32` trampolines (`7` or `8` bytes) for all `14` `imm16`-capped conditional jump mnemonics (including `jstricteq*` / `jnstricteq*` and `jeq*` / `jne*`) when displacements exceed `±32 KiB`, returning exact logical instruction byte offsets in a single pass.
  - `abcd_isa::relocate_entity_id`: Pure-Rust zero-allocation in-place patcher for `8`/`16`/`32`-bit entity-ID operands (`StringId`, `MethodId`, `LiteralArrayId`, `TypeId`, `FieldId`) after `libpandafile` assigns final `IndexSection` slots.
