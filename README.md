# abcd-rs

[![CI](https://github.com/FXTi/abcd-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/FXTi/abcd-rs/actions/workflows/ci.yml)
[![codecov](https://codecov.io/github/FXTi/abcd-rs/graph/badge.svg)](https://codecov.io/github/FXTi/abcd-rs)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Rust toolkit for ArkCompiler bytecode (`.abc`) files — read, write, inspect, and optimize via an SSA intermediate representation.

## Workspace layout

| Crate | Description |
|-------|-------------|
| [`abcd-isa-sys`](abcd-isa-sys) | C FFI bindings for the bytecode ISA (Ruby codegen + C++ bridge + bindgen) |
| [`abcd-isa`](abcd-isa) | Safe Rust API: bytecode decode/encode, versions, per-mnemonic constructors |
| [`abcd-file-sys`](abcd-file-sys) | C FFI bindings for the `.abc` container format (libpandafile) |
| [`abcd-file`](abcd-file) | Safe Rust API: read / write / inspect ABC files |
| [`abcd-ir`](abcd-ir) | SSA intermediate representation: lift (bytecode → IR), optimize, lower (IR → bytecode) |

```
.abc file ──decode──▶ abcd-isa ──▶ abcd-file ──lift──▶ abcd-ir (SSA)
                                                        │ opt / lower
.abc file ◀──encode── abcd-isa ◀─ abcd-file ◀──────────┘
```

## Quick start

```rust
use abcd_file::{decode, File};

let data = std::fs::read("input.abc")?;
let file = decode(&data)?;
for (desc, class) in &file.classes {
    println!("{desc:?}: {} methods", class.methods.len());
}
```

## IR

`abcd-ir` provides the full SSA round-trip:

- **Lift**: CFG construction → Braun SSA → instruction translation
- **Optimize**: peephole → SCCP → ADCE → copy propagation
- **Lower**: chordal-graph register allocation (MCS coloring + Boissinot out-of-SSA) → instruction selection → layout

See [`abcd-ir/README.md`](abcd-ir/README.md) for the design document and references.

## License

Apache-2.0. Vendor files under `*/vendor/` are verbatim copies of
[OpenHarmony arkcompiler](https://gitee.com/openharmony/arkcompiler_runtime_core)
(also Apache-2.0) and are kept in sync by CI.
