# ISA & Bytecode Layer (`abcd-isa-sys`, `abcd-isa`)

The ISA layer provides safe, table-driven decoding, encoding, operand inspection, and entity-ID relocation for ArkCompiler bytecode streams without hand-coding opcode tables.

---

## 1. Code Generation & FFI Architecture (`abcd-isa-sys`)

- **Authoritative Upstream Source**: Opcode definitions, instruction formats, prefixes (`wide.*`, `deprecated.*`, `callruntime.*`, `throw.*`), and property flags (`jump`, `conditional`, `ic_slot`, `jit_ic_slot`, `entity_id` roles) derive directly from `vendor/arkcompiler_runtime_core/isa/isa.yaml` via `python3 scripts/vendor-gen.py codegen` (`vendor-sync.md`).
- **Hermetic `cc::Build` Compilation**: Pre-generated C++ headers (`vendor/generated/`, `abcd-isa-sys/bridge/generated/`) and Rust tables (`abcd-isa-sys/src/generated/`, `abcd-isa/src/generated/`) are checked into Git and verified in Tier-1 CI (`vendor-verify`), requiring zero Ruby or `bindgen`/`libclang` during `cargo build`.
- **Minimal C99 Bridge**: `isa_bridge.cpp` wraps upstream `BytecodeEmitter` (handling jump-offset relaxation and width selection) and `file_format_version.cpp` (supported format/API version tables) behind exception-free C99 entrypoints.

---

## 2. Safe Rust API (`abcd-isa`)

- **`Bytecode` Enum**: Strongly typed instruction representation (`Reg`, `Imm`, `EntityId`, `JumpTarget`) covering all `246` modern opcodes (`9.0.0.0`–`24.0.0.0`).
- **Modern & Legacy Decoders**:
  - `abcd_isa::decode(&[u8])`: Decodes modern `9.0.0.0`–`24.0.0.0` instruction streams, returning `(Bytecode, byte_offset)` pairs and resolving PC-relative jump offsets into instruction-index `JumpTarget`s.
  - `abcd_isa::decode_legacy(&[u8])`: Translates legacy `0.0.0.2` (OpenHarmony 3.2/4.0 pre-freeze) instruction streams (`src/legacy_table.rs`) into canonical `Bytecode` variants (`ADR-08`).
- **Encoder & Relocation**:
  - `abcd_isa::encode(&[Bytecode])`: Emits binary instruction bytes and post-relaxation instruction byte offsets via `BytecodeEmitter`.
  - `abcd_isa::relocate_entity_id`: Patches per-method `16`-bit entity index operands (`StringId`, `MethodId`, `LiteralarrayId`) in encoded code buffers after `libpandafile` assigns final `IndexSection` slots.
- **Metadata Queries**: Generated helpers (`is_jump`, `is_terminator`, `has_ic_slot`, `entity_operands`, `mnemonic`) keep upstream `isa.yaml` properties authoritative across `abcd-file`, `abcd-lift`, and `abcd-lower`.
