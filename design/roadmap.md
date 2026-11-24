# Project Roadmap

## Shipped Foundation

- **Vendored Container & ISA Stack (`abcd-isa-sys`, `abcd-isa`, `abcd-file-sys`, `abcd-file`, `abcd-hap`)**:
  - Hermetic `vendor/arkcompiler_runtime_core/` snapshot (`OpenHarmony-v7.0-Release`) verified by `vendor/UPSTREAM.toml` SHA-256 and `109` compile-time C++17 `static_assert` enum locks—zero Git submodules, zero `bindgen`/`libclang`, zero build-time Ruby.
  - Full `.abc` `decode`/`encode` across `9.0.0.0`–`24.0.0.0`, legacy `0.0.0.2` decoding, byte-identical `abcd dis` (`5,517/5,517` vs. `ark_disasm`), semantic `abcd asm` round-trip, and pure-Rust `.hap`/`.hsp`/`.app`/`.hqf` extraction.
- **Format-Independent `88`-Op SSA IR & Rewriter (`abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`)**:
  - Braun SSA lifting, `Effects`-derived optimization (`Peephole`, `Sccp`, `Adce` + `CfgSimplify`, `CopyProp`, `inline`), chordal MCS register allocation, `acc`-as-cache lowering, per-method `u16` entity compaction, and full `--merge-abc` + `242/242` modern wild `.hap` rewrite gates (`1,149/1,149` × 3 variants + `2,684/2,685` `test262` VM oracle).
- **Static Analysis, IFDS Taint & Decompiler (`abcd-analysis`, `abcd-taint`, `abcd-decompile`, `abcd-cli`)**:
  - Iterative CHK dominators, Euler intervals, pattern-independent region structuring, IFDS tabulation solver, Rung `0`/`1`/`2` (`k=1` whole-module PTA) precision ladder, cross-module `ModuleLinkTable`, Stage/FA/ArkUI lifecycle harness, and `@ohos.*`/`@kit.*` taint preset.
  - Three-stage JS/TS decompiler (`1,149/1,149` dream gate, `2,676/2,685` `test262` dream gate, `64/64` wild recompile gate) with `--split-modules` and `--arkui` V1 sugar, exposed through the unified `abcd` CLI and gated by a `26`-job CI pipeline.

---

## Active Deep-Water Milestones (`#33` – `#36`)

1. **[#33](https://github.com/FXTi/abcd-rs/issues/33) — Throughput, Algorithmic Scaling & Peak RSS Optimization**:
   - Profile and reduce wall-clock latency and peak/steady RSS across `decode`, `lift`, `lower`, `decompile`, and whole-container `pta`/`taint` on commercial `20+ MB` `modules.abc` (`58,000+` functions) and multi-`.abc` `.hap`/`.app` bundles.
   - Eliminate residual super-linear lookups, excessive intermediate allocations, and tune arena/allocator memory retention.
2. **[#34](https://github.com/FXTi/abcd-rs/issues/34) — Whole-Program Pointer Analysis & Interprocedural Taint Precision**:
   - Close class-instance construction (`new Foo()` receiver & field sensitivity), prototype-chain inheritance dispatch, async/generator promise/iterator value channels, and multi-ability/IPC dataflows in `abcd-analysis` and `abcd-taint`.
3. **[#35](https://github.com/FXTi/abcd-rs/issues/35) — Decompiler Readability, Destructuring & ArkUI V2 Recovery**:
   - Improve variable naming, destructuring/optional-chaining/short-circuit idioms, TS type recovery, and ArkUI V2 (`@ComponentV2`, `@Local`, `@Param`, `@Once`, `@Event`, `@Monitor`, `@ObservedV2`/`@Trace`) declarative reconstruction in `abcd-decompile`.
4. **[#36](https://github.com/FXTi/abcd-rs/issues/36) — ArkTS 1.2 Static Bytecode (`0.1.0.7` / `ets2panda`) Support**:
   - Extend container/ISA decoding, `abcd-ir` static calling-convention & typed operations, `abcd-lift`, `abcd-analysis`/`abcd-taint`, and `abcd-decompile` to support statically typed ArkTS 1.2 `.abc` modules alongside dynamic ArkTS 1.1 / ECMAScript.

---

## Post-Deep-Water Horizon

- **Interactive Inspection Surfaces (`abcd-mcp` / `abcd-gui`)**: Expose stabilized IR, cross-module call graphs, taint paths, and split/ArkUI decompilation views to AI agents (MCP) and interactive desktop workflows once `#33`–`#36` settle.
