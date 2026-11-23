# abcd-rs

[![CI](https://github.com/FXTi/abcd-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/FXTi/abcd-rs/actions/workflows/ci.yml)
[![codecov](https://codecov.io/github/FXTi/abcd-rs/graph/badge.svg)](https://codecov.io/github/FXTi/abcd-rs)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Rust toolkit for ArkCompiler bytecode (`.abc`) files and OpenHarmony application containers (`.hap`, `.hsp`, `.app`, `.hqf`) — decode, assemble/disassemble, optimize, analyze, taint-track, and decompile via a format-independent SSA intermediate representation.

## Workspace layout

| Crate | Description |
|-------|-------------|
| [`abcd-isa-sys`](abcd-isa-sys) | C FFI bindings for the bytecode ISA (Ruby codegen + C++ bridge + bindgen) |
| [`abcd-isa`](abcd-isa) | Safe Rust API: bytecode decode/encode (including legacy `0.0.0.2`), entity relocation, versions |
| [`abcd-file-sys`](abcd-file-sys) | C FFI bindings for the `.abc` container format (`libpandafile` accessors + builder) |
| [`abcd-file`](abcd-file) | Safe Rust API: read / write / inspect `.abc` files + `ark_disasm`-compatible `pandasm` text disassembler/assembler |
| [`abcd-hap`](abcd-hap) | Pure-Rust in-memory reader for OpenHarmony `.hap` / `.hsp` / `.app` / `.hqf` ZIP containers |
| [`abcd-ir`](abcd-ir) | Format-independent SSA IR: module/class/function arenas, 88-op taxonomy, effects table, type lattice, verifier |
| [`abcd-lift`](abcd-lift) | Lifter: container → IR (`abcd_file::File` → `abcd_ir::Module`, CFG + Braun SSA + `--merge-abc` metadata) |
| [`abcd-opt`](abcd-opt) | SSA optimization passes (`IR → IR`): peephole, SCCP, ADCE + CFG simplify, copyprop, opt-in inliner |
| [`abcd-lower`](abcd-lower) | Lowering: IR → bytecode (`abcd_ir::Module` → `abcd_file::MethodBody`, chordal MCS regalloc + `acc-as-cache` isel) |
| [`abcd-analysis`](abcd-analysis) | Format-independent analysis infra: dominators, loops, region structuring, IFDS skeleton, alias ladder (rungs 0–2 PTA), call graph |
| [`abcd-taint`](abcd-taint) | Interprocedural IFDS taint analysis: access-path facts, summary registry, callback gap propagation, prototype resolution |
| [`abcd-decompile`](abcd-decompile) | Bytecode → JS/TS decompiler on the lifted SSA IR (expression recovery, pattern-independent structuring, precedence-exact emission) |
| [`abcd-cli`](abcd-cli) | The `abcd` CLI binary (`extract`, `info`, `dis`, `asm`, `decompile`, `rewrite`, `analyze`, `taint`) |

*(The root `abcd-rs` Cargo package is a non-published container for the cross-crate integration and corpus suites under [`tests/`](tests).)*

```
.hap/.hsp/.app/.hqf ──abcd-hap──▶ .abc bytes ◀──pandasm dis/asm──▶ .pa text
                                      │  ▲
                         decode       ▼  │       encode
                                  abcd-file  (abcd-file-sys / abcd-isa underneath)
                                      │  ▲
                           lift       ▼  │       lower
                                  abcd-ir (SSA) ──opt──▶ abcd-ir
                                      │
                                      ▼
                                abcd-analysis
                                  ├──▶ abcd-taint     ──▶ taint report
                                  └──▶ abcd-decompile ──▶ .js / .ts source
```

Layering invariant: **`abcd-ir`**, **`abcd-opt`**, **`abcd-analysis`**, **`abcd-taint`**, and **`abcd-decompile`** are strictly format-independent — their library `[dependencies]` never reference `abcd-file` or `abcd-isa`. Only **`abcd-lift`** and **`abcd-lower`** bridge between the container layer and the IR.

## Quick start

### CLI (`abcd`)

```sh
cargo run -p abcd-cli -- info modules.abc --verify
cargo run -p abcd-cli -- extract app.hap -o extracted/
cargo run -p abcd-cli -- dis modules.abc -o modules.pa
cargo run -p abcd-cli -- decompile app.hap --module entry -o entry.js
cargo run -p abcd-cli -- rewrite input.abc --opt --check -o opt.abc
cargo run -p abcd-cli -- analyze input.abc --callgraph --dominators
cargo run -p abcd-cli -- taint input.abc --config taint.toml
```

### Library API

```rust,no_run
use abcd_file::{File, decode};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let data = std::fs::read("input.abc")?;
    let file: File = decode(&data)?;
    for (desc_id, class) in &file.classes {
        let desc = file.strings.resolve(*desc_id).unwrap_or("<invalid>");
        println!("{desc}: {} methods", class.methods.len());
    }
    Ok(())
}
```

## Design documentation

Architecture, format research, and subsystem designs live in [`design/`](design/README.md):

- [Overview](design/overview.md) — 13-crate architecture, dependency graph, data flow, compatibility matrix
- [ISA](design/isa.md) & [ISA Compatibility](design/isa-compat.md) — Ruby codegen, bytecode decode/encode, legacy `0.0.0.2` support
- [File Format](design/file-format.md) & [HAP Containers](design/abcd-hap-research.md) — `.abc` container layout, `--merge-abc` records, FFI bridge, ZIP container reader
- [IR v0.2](design/ir-v0.2.md) & [IR Background](design/ir.md) — SSA IR specification, frame-slot call contract, T1–T10 taint invariants, lift/opt/lower algorithms
- [Analysis Strategy](design/analysis-strategy.md) — IFDS solver, rungs 0–2 alias/PTA ladder, summary & callback-gap model
- [Decompiler](design/decompile.md) — Stages A/B/C expression recovery, region structuring, and JS/TS emission
- [Vendor Sync](design/vendor-sync.md) & [CI/CD](design/ci.md) — submodule pin policy, tag radar, and the 19-job CI pipeline

## Cloning

The `-sys` crates vendor upstream `arkcompiler_runtime_core` as **git submodules** at the crate roots:

```sh
git clone --recurse-submodules https://github.com/FXTi/abcd-rs.git
# or, in an existing clone:
git submodule update --init
```

Building requires **Ruby 2.5+** and a **C++17** toolchain (`build.rs` runs upstream's `isa.yaml` codegen and compiles the C++ bridges under `abcd-isa-sys/arkcompiler_runtime_core/` and `abcd-file-sys/arkcompiler_runtime_core/`).

**Windows contributors:** upstream's full tree contains NTFS-reserved filenames under `static_core/` test directories. Configure Git before initializing submodules and use the same sparse-checkout cone as CI:

```powershell
git config --global core.protectNTFS false
git config --global core.longpaths true
foreach ($sm in "abcd-isa-sys/arkcompiler_runtime_core", "abcd-file-sys/arkcompiler_runtime_core") {
  $sha = (git ls-tree HEAD $sm) -split '\s+' | Select-Object -Index 2
  $url = git config -f .gitmodules "submodule.$sm.url"
  git clone --depth 1 --filter=blob:none --sparse $url $sm
  git -C $sm sparse-checkout set --cone isa libpandafile libpandabase assembler templates platforms
  git -C $sm fetch --depth 1 origin $sha
  git -C $sm checkout -f $sha
}
```

## License

Apache-2.0. The `arkcompiler_runtime_core` submodules pull in [OpenHarmony `arkcompiler_runtime_core`](https://github.com/openharmony/arkcompiler_runtime_core) (also Apache-2.0), pinned to a proven upstream commit.
