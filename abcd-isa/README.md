# abcd-isa

Safe Rust API for the ArkCompiler bytecode instruction set. Provides bytecode decoding (modern and legacy `0.0.0.2`), encoding with automatic jump widening, entity operand relocation, and `.abc` format version queries.

All public types are safe — `unsafe` is confined to internal FFI calls into [`abcd-isa-sys`](../abcd-isa-sys/README.md).

## Decoding

```rust,no_run
use abcd_isa::{Bytecode, decode};

let bytecode: &[u8] = &[0x64, 0x65]; // ldundefined; returnundefined
let decoded: Vec<(Bytecode, u32)> = decode(bytecode).unwrap();

for (insn, byte_offset) in &decoded {
    println!("{byte_offset:#x}: {insn}");
}
```

`decode` returns `(Bytecode, byte_offset)` pairs and resolves relative jump immediates into `Label(target_insn_index)` indices into the returned `Vec`. For pre-2022-08-18 OpenHarmony 3.0/3.1 `.abc` files (header version `0.0.0.2`), `decode_legacy` translates the legacy `0xff`-prefixed opcode encoding into the same `Bytecode` enum.

## Encoding

```rust
use abcd_isa::{Bytecode, Label, encode, insn};

let program: Vec<Bytecode> = vec![
    insn::Jmp::new(Label(2)).into(),
    insn::Ldundefined::new().into(),
    insn::Returnundefined::new().into(),
];
let (bytes, offsets): (Vec<u8>, Vec<u32>) = encode(&program).unwrap();
assert_eq!(offsets.len(), program.len());
```

`Label` values in jump instructions are instruction indices into `program`. `encode` delegates format selection and short/long jump widening to the vendored C++ `BytecodeEmitter` and returns both the encoded byte buffer and each instruction's starting byte offset.

## Entity operand relocation

`relocate_entity_id(&mut insn_bytes, id_ordinal, EntityId(new_id))` patches an instruction's `n`-th entity-ID operand in place — used by `abcd-file` during container layout finalization so container code never duplicates ISA operand bit widths.

## Version

```rust
use abcd_isa::Version;

let v = Version::current();
println!("ISA version: {v}"); // "24.0.0.0"

let file_ver = Version::new(12, 0, 6, 0);
assert!(file_ver.is_in_supported_range());
assert!(!file_ver.is_blocked());

if let Some(v) = Version::for_api(12) {
    println!("API 12 -> file version {v}");
}
```

## Re-exported Types

From `abcd-isa-sys`: `Bytecode`, `Reg`, `Imm`, `EntityId`, `EntityKind`, `Label`, `Operand`, `insn` (per-mnemonic constructors), `BytecodeFlags`, `ExceptionType`.
