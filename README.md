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
| [`abcd-lift`](abcd-lift) | Lifter: decode → IR (`abcd_file::File` → `abcd_ir::Module`) |
| [`abcd-ir`](abcd-ir) | The SSA intermediate representation: module/function graphs, op taxonomy, effects, type lattice, verifier |
| [`abcd-opt`](abcd-opt) | Optimization passes on the IR (IR → IR): peephole, SCCP, ADCE + CFG simplify, copyprop, inline |
| [`abcd-lower`](abcd-lower) | Lowering: IR → ArkCompiler bytecode (`abcd_ir::Module` → `abcd_file::MethodBody`) |

```
.abc file ──decode──▶ abcd-file ──lift──▶ abcd-ir (SSA) ──opt──▶ abcd-ir
       (abcd-file-sys / abcd-isa underneath)              │
.abc file ◀──encode── abcd-file ◀──lower──────────────────┘
```

Layering: **lift = decode→IR**, **opt = IR→IR**, **lower = IR→file**.
`abcd-ir` and `abcd-opt` are format-independent — they never depend on
the container/ISA crates; only `abcd-lift` and `abcd-lower` straddle the
boundary.

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

`abcd-ir` is the SSA intermediate representation; the pipeline around it
provides the full round-trip:

- **Lift** (`abcd-lift`): CFG construction → Braun SSA → instruction translation
- **Optimize** (`abcd-opt`): peephole → SCCP → ADCE → copy propagation (inline is opt-in)
- **Lower** (`abcd-lower`): chordal-graph register allocation (MCS coloring + Boissinot out-of-SSA) → instruction selection → layout

See [`abcd-ir/README.md`](abcd-ir/README.md) for the IR module map.

## Design

Architecture and design decisions are documented in [`design/`](design/README.md):

- [Overview](design/overview.md) — layering, data flow, version-aware design
- [ISA](design/isa.md) — code generation pipeline, bytecode decode/encode
- [File format](design/file-format.md) — ABC container, FFI bridge, builder
- [IR](design/ir.md) — SSA lift/optimize/lower, register allocation, references
- [IR v0.2](design/ir-v0.2.md) — the implemented IR design (as of P4, `abcd-ir` IS this IR; v0.1 deleted)
- [Vendor sync](design/vendor-sync.md) — submodule pin policy + upstream tag radar
- [CI/CD](design/ci.md) — jobs rationale, release policy

## Cloning

The `-sys` crates vendor upstream as **git submodules** at the crate roots —
clone with them:

```sh
git clone --recurse-submodules https://github.com/FXTi/abcd-rs.git
# or, in an existing clone:
git submodule update --init
```

Building without the submodules fails in `build.rs` (the C++ bridge sources
live under `abcd-isa-sys/arkcompiler_runtime_core/` and
`abcd-file-sys/arkcompiler_runtime_core/`).

## License

Apache-2.0. The `arkcompiler_runtime_core` submodules pull in
[OpenHarmony arkcompiler runtime_core](https://github.com/openharmony/arkcompiler_runtime_core)
(also Apache-2.0), pinned to a proven upstream commit and tracked by a weekly
CI tag radar.
