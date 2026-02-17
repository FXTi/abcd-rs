# abcd-isa

Safe Rust API for the ArkCompiler bytecode instruction set. Provides opcode metadata queries, bytecode decoding/encoding, and version management.

All public types are safe — `unsafe` is only used in internal FFI calls. The underlying C FFI bindings are provided by `abcd-isa-sys`, which generally does not need to be used directly.

## Quick Start

### Decoding Bytecode

```rust
use abcd_isa::{decode, DecodeError};

let bytecode = [0x62, 0x01, 0x00]; // mov v1, v0
match decode(&bytecode) {
    Ok((opcode, info)) => {
        println!("{}", opcode);           // "mov"
        println!("size: {}", info.size()); // 3
        println!("flags: {:?}", info.flags());
    }
    Err(DecodeError::EmptyInput) => println!("empty"),
    Err(DecodeError::InvalidOpcode) => println!("invalid"),
}
```

### Using Inst to Extract Operands

```rust
use abcd_isa::Inst;

let bytecode = [0x62, 0x01, 0x00]; // mov v1, v0
if let Some(inst) = Inst::decode(&bytecode) {
    println!("{inst}");                    // Display: "mov v1, v0"
    println!("size: {}", inst.size());     // 3

    // Operand extraction (bounds-checked, returns None on out-of-bounds)
    if let Some(dst) = inst.vreg(0) {
        println!("dst register: v{dst}");  // v1
    }
    // Classification queries
    println!("can throw: {}", inst.can_throw());
    println!("is terminator: {}", inst.is_terminator());
}
```

### Querying Opcode Metadata

```rust
use abcd_isa::{lookup, opcode_table, OpcodeFlags};

// Look up by raw opcode value
if let Some(info) = lookup(0x62) {
    println!("{}: {} bytes", info.mnemonic(), info.size());
    println!("namespace: {}", info.namespace());
    println!("acc read: {}, acc write: {}", info.is_acc_read(), info.is_acc_write());
}

// Iterate all opcodes
for info in opcode_table() {
    let flags = info.flags();
    if flags.contains(OpcodeFlags::JUMP | OpcodeFlags::CONDITIONAL) {
        println!("{}: conditional jump", info.mnemonic());
    }
}
```

### Operand Layout Analysis

```rust
use abcd_isa::{opcode_table, OperandKind};

for info in opcode_table() {
    let ops: Vec<_> = info.operands().collect();
    if ops.is_empty() { continue; }

    print!("{:20} ({} bytes): ", info.mnemonic(), info.size());
    for (i, op) in ops.iter().enumerate() {
        if i > 0 { print!(", "); }
        let kind = match op.kind() {
            OperandKind::Reg => "reg",
            OperandKind::Imm => "imm",
            OperandKind::Id  => "id",
        };
        print!("{kind}{}@byte{}", op.bit_width(), op.byte_offset());
        if op.is_dst() { print!("[dst]"); }
        if op.is_src() { print!("[src]"); }
    }
    println!();
}
```

### Bytecode Assembly

```rust
use abcd_isa::{Emitter, EmitterError, decode};

let mut e = Emitter::new();

// Simple instructions
e.ldundefined();
e.ldnull();

// With operands
e.mov(0, 1);   // mov v0, v1
e.ldai(42);     // ldai 42

// Branching
let target = e.label();
e.jmp(target);
e.ldundefined();
e.bind(target);
e.returnundefined();

// Build
match e.build() {
    Ok(bytecode) => {
        println!("assembled {} bytes", bytecode.len());
        let (op, _) = decode(&bytecode).unwrap();
        assert_eq!(op.mnemonic(), "ldundefined");
    }
    Err(EmitterError::UnboundLabels) => println!("unbound labels"),
    Err(EmitterError::InternalError) => println!("internal error"),
}
```

### Version Management

```rust
use abcd_isa::{current_version, min_version, version_by_api, is_version_compatible};

let ver = current_version();
let min = min_version();
println!("ISA version: {ver}, min supported: {min}");
assert!(is_version_compatible(&ver));

// Look up file version by API level
if let Some(v) = version_by_api(12) {
    println!("API 12 -> file version {v}");
}
```

### OpcodeFlags Bit Operations

```rust
use abcd_isa::OpcodeFlags;

let jump_and_cond = OpcodeFlags::JUMP | OpcodeFlags::CONDITIONAL;
let flags = info.flags();
if flags.contains(jump_and_cond) {
    println!("conditional jump");
}

let masked = flags & OpcodeFlags::JUMP;
let inverted = !flags;
let combined = flags.union(OpcodeFlags::RETURN);
let raw: u32 = flags.raw();
```

### Linear Scan Disassembler

```rust
use abcd_isa::{Inst, OpcodeFlags};

fn disassemble(bytecode: &[u8]) {
    let mut offset = 0usize;
    while offset < bytecode.len() {
        match Inst::decode(&bytecode[offset..]) {
            Some(inst) => {
                let info = inst.info();
                print!("{offset:#06x}: {inst}");

                if info.flags().contains(OpcodeFlags::JUMP) {
                    if let Some(imm) = inst.imm64(0) {
                        let target = offset as i64 + imm;
                        print!("  ; -> {target:#x}");
                    }
                }
                if info.is_acc_read() { print!(" [acc:R]"); }
                if info.is_acc_write() { print!(" [acc:W]"); }
                println!();

                offset += inst.size();
            }
            None => {
                println!("{offset:#06x}: <invalid> {:#04x}", bytecode[offset]);
                offset += 1;
            }
        }
    }
}
```

### Bytecode Patching

```rust
use abcd_isa::update_id;

// Modify the idx-th entity ID operand in an instruction
let mut bytecode = vec![0x60, 0x00, 0x00, 0x00, 0x00];
update_id(&mut bytecode, 42, 0);
```

### Prefix Queries

```rust
use abcd_isa::{min_prefix_opcode, prefix_count, prefix_opcode_at, is_primary_opcode_valid};

let min = min_prefix_opcode();  // 251 (0xFB)
println!("{} prefix groups:", prefix_count());
for i in 0..prefix_count() {
    println!("  prefix byte: {:#04x}", prefix_opcode_at(i));
}
assert!(is_primary_opcode_valid(0x00)); // ldundefined
```

## Public API Reference

### Types

| Type | Description |
|------|-------------|
| `Opcode` | Opcode value (u16 newtype), implements `Display` (prints mnemonic) |
| `Format` | Instruction format (u8 newtype) |
| `OpcodeFlags` | Property bitmask, supports `BitOr`/`BitAnd`/`Not` |
| `Exceptions` | Exception type bitmask, same ops |
| `OperandKind` | Operand kind: `Reg`, `Imm`, `Id` |
| `OperandDesc` | Operand description (kind, width, offset, flags) |
| `OpcodeInfo` | Lightweight metadata handle (`Copy`, O(1) access) |
| `OperandIter` | Operand iterator (`ExactSizeIterator`) |
| `DecodeError` | Decode error: `EmptyInput`, `InvalidOpcode` |
| `Inst<'a>` | Decoded instruction reference with operand extraction |
| `AbcVersion` | .abc file version (4 bytes), implements `Ord`/`Display` |
| `EmitterError` | Assembly error: `InternalError`, `UnboundLabels` |
| `Label` | Branch target handle |
| `Emitter` | Bytecode assembler, implements `Drop`/`Default` |

### Free Functions

| Function | Signature |
|----------|-----------|
| `decode` | `(bytes: &[u8]) -> Result<(Opcode, OpcodeInfo), DecodeError>` |
| `lookup` | `(value: u16) -> Option<OpcodeInfo>` |
| `opcode_count` | `() -> usize` |
| `opcode_table` | `() -> impl Iterator<Item = OpcodeInfo>` |
| `min_prefix_opcode` | `() -> u8` |
| `prefix_count` | `() -> usize` |
| `prefix_opcode_at` | `(idx: usize) -> u8` |
| `is_primary_opcode_valid` | `(primary: u8) -> bool` |
| `update_id` | `(bytes: &mut [u8], new_id: u32, idx: u32)` |
| `current_version` | `() -> AbcVersion` |
| `min_version` | `() -> AbcVersion` |
| `version_by_api` | `(api_level: u8) -> Option<AbcVersion>` |
| `is_version_compatible` | `(ver: &AbcVersion) -> bool` |
| `api_version_count` | `() -> usize` |

### OpcodeInfo Methods

| Method | Return Type | Description |
|--------|-------------|-------------|
| `opcode()` | `Opcode` | Raw opcode value |
| `mnemonic()` | `&'static str` | Mnemonic |
| `format()` | `Format` | Instruction format |
| `size()` | `usize` | Instruction byte count |
| `flags()` | `OpcodeFlags` | Property flags |
| `exceptions()` | `Exceptions` | Exception flags |
| `namespace()` | `&'static str` | Namespace |
| `is_prefixed()` | `bool` | Whether it's a two-byte opcode |
| `is_range()` | `bool` | Whether it's a range instruction |
| `is_suspend()` | `bool` | Whether it's a suspend instruction |
| `is_acc_read()` | `bool` | Whether it reads the accumulator |
| `is_acc_write()` | `bool` | Whether it writes the accumulator |
| `operands()` | `OperandIter` | Operand iterator |

### Inst Methods

| Method | Return Type | Description |
|--------|-------------|-------------|
| `decode(bytes)` | `Option<Inst>` | Decode from byte stream |
| `opcode()` | `Opcode` | Opcode value |
| `info()` | `OpcodeInfo` | Metadata handle |
| `size()` | `usize` | Instruction byte count |
| `bytes()` | `&[u8]` | Raw bytes |
| `vreg(idx)` | `Option<u16>` | Register operand |
| `imm64(idx)` | `Option<i64>` | 64-bit immediate |
| `id(idx)` | `Option<u32>` | Entity ID |
| `imm_data(idx)` | `Option<i64>` | Sign-aware immediate |
| `imm_count()` | `usize` | Number of immediates |
| `literal_index()` | `Option<usize>` | Literal array index |
| `last_vreg()` | `Option<u64>` | Last register |
| `range_last_reg_idx()` | `Option<u64>` | Range last register index |
| `can_throw()` | `bool` | Whether it may throw |
| `is_terminator()` | `bool` | Whether it's a terminator |
| `is_return_or_throw()` | `bool` | Whether it's return/throw |
| `is_id_match_flag(idx, flag)` | `bool` | ID type match |
| `format_string()` | `String` | Format as string |

## Design Notes

- `OpcodeInfo` is a `Copy` u16 index handle; all accessors read C static tables directly (O(1)), no heap allocation
- `decode()` obtains the table index in a single step via `isa_decode_index()`, avoiding the two-step overhead of decoding the opcode then looking it up
- `Inst` holds a byte slice reference + `OpcodeInfo`; operand extraction delegates to upstream C++ generated code via FFI
- `Emitter`'s per-mnemonic methods are auto-generated by build.rs from bindings.rs, staying in sync with ISA changes automatically
- `OpcodeFlags`/`Exceptions` constants are likewise auto-generated by build.rs from `ISA_FLAG_*`/`ISA_EXC_*`

> For internal architecture, build pipeline, C++ base class, shim strategy, and other implementation details, see [`abcd-isa-sys/README.md`](../abcd-isa-sys/README.md).
