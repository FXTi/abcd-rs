# abcd-isa

Safe Rust API for the ArkCompiler bytecode instruction set. Provides bytecode decoding, encoding, and version management.

All public types are safe — `unsafe` is only used in internal FFI calls. The underlying C FFI bindings are provided by `abcd-isa-sys`, which generally does not need to be used directly.

## Decoding

```rust
use abcd_isa::{decode, Bytecode};

let bytecode: &[u8] = &[/* raw .abc method body */];
let instructions: Vec<Bytecode> = decode(bytecode).unwrap();

for insn in &instructions {
    println!("{insn}");
}
```

`decode` resolves jump offsets into `Label` indices pointing at the target instruction in the returned `Vec`.

## Encoding

```rust
use abcd_isa::{encode, insn, Label};

let program: Vec<Bytecode> = vec![
    insn::Jmp::new(Label(2)).into(),
    insn::Ldundefined::new().into(),
    insn::Returnundefined::new().into(),
];
let bytes = encode(&program).unwrap();
```

`Label` values in jump instructions are interpreted as instruction indices into the slice.

## Version

```rust
use abcd_isa::Version;

let v = Version::current();
println!("ISA version: {v}");  // e.g. "13.0.1.0"

let file_ver = Version::new(12, 0, 6, 0);
assert!(file_ver.is_in_supported_range());
assert!(!file_ver.is_blocked());

// Look up file version by API level
if let Some(v) = Version::for_api(12) {
    println!("API 12 -> file version {v}");
}
```

## Re-exported Types

From `abcd-isa-sys`: `Bytecode`, `Reg`, `Imm`, `EntityId`, `Label`, `insn` (per-mnemonic constructors), `BytecodeFlag`, `ExceptionType`.
