# `abcd-rs` Architecture & Design Documentation

Authoritative architecture specifications, engineering standards, and design decisions for the `abcd-rs` ArkCompiler bytecode toolkit.

> **Repository Documentation Rule**: `design/` contains **only** active as-built specifications and binding engineering guidance. Historical investigation logs, benchmark comparisons, and debugging narratives live in GitHub Issues and Commit Messages.

---

## Governance & Engineering Rules

- [**Project Engineering Standards (`standards.md`)**](standards.md) — Layering ring, zero input-depth recursion, linear scaling, bit-exact determinism, error honesty, C++ FFI firewall bounds, and zero-Docker local testing.
- [**Architecture Decisions & `N*` Registry (`decisions.md`)**](decisions.md) — Canonical `ADR-01`–`ADR-12` rulings, quick lookup for `N*` source-comment tags, and retired legacy rulings.
- [**Agent & Contributor Guide (`../AGENTS.md`)**](../AGENTS.md) — Crate ownership table, multi-agent Git coordination, and `./scripts/test-local.sh` commands.

## Architecture & Subsystem Specifications

- [**Architecture Overview (`overview.md`)**](overview.md) — 13-crate dependency graph, pipeline data flow, and supported `.abc` format versions (`0.0.0.2`, `9.0.0.0`–`24.0.0.0`, and static ArkTS 1.2 `0.1.0.7`).
- [**Roadmap (`roadmap.md`)**](roadmap.md) — Shipped capabilities and active `#33`–`#36` deep-water milestones.
- [**ISA & Bytecode Layer (`isa.md`)**](isa.md) & [**ISA Compatibility (`isa-compat.md`)**](isa-compat.md) — Vendored `isa.yaml` codegen, typed `Bytecode` stream codec, entity relocation, and legacy `0.0.0.2` / static `0.1.0.7` version handling.
- [**`.abc` File Format Layer (`file-format.md`)**](file-format.md) — `libpandafile` FFI bridge (`abcd-file-sys`), `File` container model (`abcd-file`), dual-bucket MUTF-8 strings, nested literal/module/annotation relocation, and `pandasm` `.pa` text disassembler/assembler.
- [**OpenHarmony Containers (`hap-container.md`)**](hap-container.md) — Pure-Rust `.hap` / `.hsp` / `.app` / `.hqf` ZIP reader (`abcd-hap`), signing-block tolerance, and multi-module discovery.
- [**SSA IR & Lift/Opt/Lower Pipeline (`ir.md`)**](ir.md) — Format-independent `94`-op SSA IR (`abcd-ir`), Braun SSA lifter (`abcd-lift`), `Effects`-driven optimization passes (`abcd-opt`), and chordal register allocation + `acc`-as-cache lowering (`abcd-lower`).
- [**Static Analysis & Taint Engine (`analysis.md`)**](analysis.md) — Iterative CHK dominators, region structuring, monotone dataflow, IFDS solver, Rung `0`/`1`/`2` alias & `k=1` PTA ladder, cross-module ES linking (`abcd-analysis`), and OpenHarmony taint analysis (`abcd-taint`).
- [**Decompiler (`decompile.md`)**](decompile.md) — Three-stage JS/TS decompiler (`abcd-decompile`), generator/`async`/`for await` state-machine folds, `--split-modules` bundle recovery, and `--arkui` declarative `@Component struct` sugar.
- [**Command-Line Interface (`cli.md`)**](cli.md) — Unified `abcd` binary (`abcd-cli`), container auto-detection, exit codes, TOML taint configuration, and allocator policy.
- [**CI & Verification Architecture (`ci.md`)**](ci.md) — `27`-job GitHub Actions pipeline, self-cleaning divergence ledgers, and local zero-Docker verification.
- [**Vendor Snapshot Maintenance (`vendor-sync.md`)**](vendor-sync.md) — Managing `vendor/arkcompiler_runtime_core/`, `vendor/UPSTREAM.toml`, and `scripts/vendor-gen.py`.
