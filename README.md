# abcd-rs

A high-performance Rust toolkit for inspecting, disassembling, assembling, optimizing, rewriting, statically analyzing, and decompiling OpenHarmony / HarmonyOS NEXT ArkCompiler (`.abc`) bytecode and application packages (`.hap`, `.hsp`, `.app`, `.hqf`).

---

## Features

- **Container & `.abc` Codec (`abcd-hap`, `abcd-file`, `abcd-isa`)**:
  - 100% pure Safe Rust readers (`#![forbid(unsafe_code)]`) for `.hap`/`.hsp`/`.app`/`.hqf` packages and `.abc` containers (`60B` dynamic `0.0.0.2`/`0.0.0.3`/`9.0.0.0`–`24.0.0.0` + `64B`/`72B` static `0.0.0.5`/`0.0.0.6`/`0.1.0.7`), with zero-copy `Arc<[u8]>` `MethodCode::Span`, `DecodeMode::{Strict, Forensic}`, relocated `encode`, and C++ differential reader oracles.
  - Byte-identical `.pa` disassembler (`abcd dis`, `5,517/5,517` vs. upstream `ark_disasm`) and semantic `.pa` assembler (`abcd asm`).
- **Format-Independent `94`-Op SSA IR & Rewriter (`abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`)**:
  - Flat-arena `SymbolTable` & `HashTable`-backed `ConstPool`, bit-identical parallel Braun SSA lifting, `Effects`-driven optimization (`Peephole`, `SCCP`, `ADCE` + `CfgSimplify`, `CopyProp`, intra-module `inline`), Hack–Grund–Goos dominance-tree SSA coloring + Boissinot CSSA coalescing, streaming batched `rewrite_file_owned`, and per-method `u16` entity compaction.
- **Interprocedural Static & Taint Analysis (`abcd-analysis`, `abcd-taint`)**:
  - Iterative Semi-NCA dominators, cursor-driven IFDS tabulation with shared `IfdsResult` CSR, `3`-rung alias & `k=1` whole-module pointer analysis (`PTA`) with sparse `Rung2Tables` and on-the-fly call-graph co-evolution, zero-clone `PreparedModule` + steady-state `while (*)` Stage/FA/ArkUI lifecycle synthesis, and curated `@ohos.*` / `@kit.*` security rules.
- **JS / TS & ArkUI Decompiler (`abcd-decompile`)**:
  - Three-stage expression, control-flow, and state-machine (`function*`, `async`, `async*`, `yield*`, `for await..of`) recovery (`1,149/1,149` corpus dream gate, `2,680/2,685` `test262` dream gate) with deduplicated instruction-weight batching, `--split-modules` multi-file bundle recovery, and `--arkui` `@Component struct` reconstruction.

---

## Workspace Crates

| Crate | Description |
| :--- | :--- |
| [`abcd-isa-sys`](abcd-isa-sys/README.md) | Vendored C++17 `BytecodeInst` / `BytecodeEmitter` C99 differential-oracle FFI bridge |
| [`abcd-isa`](abcd-isa/README.md) | Pure-Rust `Bytecode` enum, modern & legacy `0.0.0.2` decoders, Fenwick encoder, relocation, and `Version` |
| [`abcd-file-sys`](abcd-file-sys/README.md) | Exception-guarded C99 FFI bridge over vendored `libpandafile` (`AbcBuilder` writer + differential reader oracle) |
| [`abcd-file`](abcd-file/README.md) | Pure-Rust zero-copy `.abc` reader (`Strict`/`Forensic`), `encode`, flat-arena `StringPool`, and `pandasm` `.pa` layer |
| [`abcd-hap`](abcd-hap/README.md) | Pure-Rust `.hap` / `.hsp` / `.app` / `.hqf` container & manifest reader |
| [`abcd-ir`](abcd-ir/README.md) | Format-independent `94`-op SSA IR, Semi-NCA `DomTree`, `Effects`, `Ty`, `FrameSlots`, and verifier |
| [`abcd-lift`](abcd-lift/README.md) | `abcd_file::File` → `abcd_ir::Module` lifter |
| [`abcd-opt`](abcd-opt/README.md) | SSA optimization passes (`Peephole`, `SCCP`, `ADCE`, `CopyProp`, `inline`) |
| [`abcd-lower`](abcd-lower/README.md) | `abcd_ir::Module` → `abcd_file::File` dominance-tree CSSA register allocator & bytecode lowerer |
| [`abcd-analysis`](abcd-analysis/README.md) | IFDS solver, Rung `0`–`2` alias/PTA, call graph, class hierarchy, and OHOS module/lifecycle linker |
| [`abcd-taint`](abcd-taint/README.md) | Access-path IFDS taint analyzer, callback-gap summaries, and OpenHarmony (`ohos`) preset |
| [`abcd-decompile`](abcd-decompile/README.md) | Bytecode → JS/TS decompiler (Ramsey labeled-block structuring, `--split-modules`, `--arkui`) |
| [`abcd-cli`](abcd-cli/README.md) | Unified `abcd` command-line binary |

---

## Building & Quick Start

Requires a stable Rust toolchain (`1.88+`, Edition 2024) and a standard host C++17 compiler (`clang++`, `g++`, or MSVC)—no Git submodules, Ruby, `bindgen`, or `libclang` are needed at build time.

```sh
cargo build --release -p abcd-cli

# Inspect or disassemble an .abc file or .hap/.app package directly
./target/release/abcd info app.hap
./target/release/abcd dis app.hap --module entry -o entry.pa

# Decompile a merged bundle into a source tree with ArkUI @Component sugar
./target/release/abcd decompile app.hap --split-modules --arkui -o out_src/

# Run cross-module OpenHarmony taint analysis
./target/release/abcd taint app.hap --all --link-modules --preset ohos --json

# Optimize and rewrite bytecode with post-encode verification
./target/release/abcd rewrite input.abc --opt --check -o optimized.abc
```

---

## Testing & Documentation

Local verification runs natively with **zero Docker / OrbStack dependency**:

```sh
./scripts/test-local.sh quick    # Fast fmt + clippy + unit tests (<5s incremental)
./scripts/test-local.sh full     # Full L1 static gates + synthetic workspace suite (<15s)
./scripts/test-local.sh all      # Full L1 + local corpus suites when exports/ is present
```

Cross-OS builds (`6` 64-bit + `3` 32-bit targets), nightly Rust/C++ `ASan+UBSan` and `TSan` sanitizer gates, `llvm-cov` coverage, and Docker-backed `ark_js_vm` / `es2abc` oracle comparisons run across the **`27`-job CI pipeline** (`.github/workflows/ci.yml`).

- [**Architecture & Design Index (`design/README.md`)**](design/README.md)
- [**Engineering Standards (`design/standards.md`)**](design/standards.md) & [**Design Decisions (`design/decisions.md`)**](design/decisions.md)
- [**Contributor & Agent Guide (`AGENTS.md`)**](AGENTS.md)

## License

Apache-2.0.
