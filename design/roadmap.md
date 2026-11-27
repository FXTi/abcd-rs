# Project Roadmap

## Shipped Foundation

- **Vendored Container & ISA Stack (`abcd-isa-sys`, `abcd-isa`, `abcd-file-sys`, `abcd-file`, `abcd-hap`)**:
  - Hermetic `vendor/arkcompiler_runtime_core/` snapshot (`OpenHarmony-v7.0-Release`) verified by `vendor/UPSTREAM.toml` SHA-256 and `109` compile-time C++17 `static_assert` enum locks—zero Git submodules, zero `bindgen`/`libclang`, zero build-time Ruby.
  - 100% pure Safe Rust (`.abc` reader `#49`, modern/legacy ISA codec `#91`, DWARF/LNP decoder `#44`, and ZIP/HAP unpacker `#46`) across `60B` dynamic (`0.0.0.2`, `0.0.0.3`, `9.0.0.0`–`24.0.0.0`) and `64B`/`72B` static (`0.0.0.5`, `0.0.0.6`, `0.1.0.7`) containers with `DecodeMode::{Strict, Forensic}`, lazy `Arc<[u8]>` `MethodCode::Span`, C++ differential reader oracles, relocated `encode`, and byte-identical `abcd dis` (`5,517/5,517` vs. `ark_disasm`).
- **Format-Independent `94`-Op SSA IR & Rewriter (`abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`)**:
  - Flat-arena `SymbolTable` & `HashTable`-backed `ConstPool` (`#72`), bit-identical parallel Braun SSA lifting (`#84`), `Effects`-derived optimization (`Peephole`, `Sccp`, `Adce` + `CfgSimplify`, `CopyProp`, `inline`), Hack–Grund–Goos + CSSA register allocation (`#93`), streaming batched `rewrite_file_owned` (`#84`), per-method `u16` entity compaction, and full `--merge-abc` + `242/242` modern wild `.hap` rewrite gates (`1,149/1,149` × 3 variants + `2,685/2,685` `test262` VM oracle).
- **Static Analysis, IFDS Taint & Decompiler (`abcd-analysis`, `abcd-taint`, `abcd-decompile`, `abcd-cli`)**:
  - Iterative Semi-NCA dominators (`#92`), Ramsey forward labeled-block region structuring (`#95`), cursor-driven IFDS tabulation with shared `IfdsResult` CSR (`#78`), Rung `0` / `0.5` / `1` / `2` (`k=1` root-cone-sliced PTA with sparse `Rung2Tables` and `PackedCtx`, `#78`, `#84`) precision ladder, zero-clone `PreparedModule` + `EntryPlan` steady-state `while (*)` OHOS lifecycle harness (`#71`, `#94`), and sub-3-GiB `300k`-function `@ohos.*`/`@kit.*` taint engine.
  - Three-stage JS/TS decompiler (`1,149/1,149` dream gate, `2,680/2,685` `test262` dream gate, `64/64` wild recompile gate) with deduplicated instruction-weight batching (`#84`), `--split-modules`, and `--arkui` V1 sugar, exposed through the unified `abcd` CLI (`--jobs`, `--timings`, `--forensic`) and gated by a `27`-job CI pipeline.

---

## Active Deep-Water Milestones (`#35` – `#36`, `#39`)

1. **[#39](https://github.com/FXTi/abcd-rs/issues/39) — FFI Upfront Validation & Exception-Boundary Cleanup**:
   - Pre-validate `RESTART_LOCAL` LNP opcodes and index-section limits before C++ entry, eliminate `~FatalLogStream() noexcept(false)` destructor throws in `vendor/shim/utils/logger.h`, prune uncompiled `assembler/` snapshot files, and trim redundant `try/catch` frames on pure ISA queries.
2. **[#35](https://github.com/FXTi/abcd-rs/issues/35) — Decompiler Readability, Destructuring & ArkUI V2 Recovery**:
   - Improve variable naming, destructuring/optional-chaining/short-circuit idioms, TS type recovery, and ArkUI V2 (`@ComponentV2`, `@Local`, `@Param`, `@Once`, `@Event`, `@Monitor`, `@ObservedV2`/`@Trace`) declarative reconstruction in `abcd-decompile`.
3. **[#36](https://github.com/FXTi/abcd-rs/issues/36) — ArkTS 1.2 Static Bytecode (`0.1.0.7` / `ets2panda`) Support**:
   - Extend container/ISA decoding, `abcd-ir` static calling-convention & typed operations, `abcd-lift`, `abcd-analysis`/`abcd-taint`, and `abcd-decompile` to support statically typed ArkTS 1.2 `.abc` modules alongside dynamic ArkTS 1.1 / ECMAScript.

---

## Post-Deep-Water Horizon

- **Interactive Inspection Surfaces (`abcd-mcp` / `abcd-gui`)**: Expose stabilized IR, cross-module call graphs, taint paths, and split/ArkUI decompilation views to AI agents (MCP) and interactive desktop workflows once `#33`–`#36` settle.
