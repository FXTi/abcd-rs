# abcd-rs Design Documentation

Architecture, format specifications, research surveys, and verification records for the `abcd-rs` ArkCompiler bytecode toolkit.

## Core Architecture & Subsystem Specs (Evergreen)

| Document | Scope |
|----------|-------|
| [overview.md](overview.md) | 13-crate workspace architecture, strict dependency layering, data flow, and version compatibility |
| [isa.md](isa.md) | ISA layer (`abcd-isa-sys` / `abcd-isa`): Ruby codegen, `Bytecode` model, modern + legacy `0.0.0.2` decode, encode, relocation |
| [isa-compat.md](isa-compat.md) | Cross-version opcode compatibility matrix (`0.0.0.2`, `9.0.0.0` .. `24.0.0.0`) |
| [file-format.md](file-format.md) | `.abc` container layer (`abcd-file-sys` / `abcd-file`): layout, `--merge-abc` fields, FFI bridge, `Builder`, `pandasm` |
| [abcd-hap-research.md](abcd-hap-research.md) | OpenHarmony `.hap` / `.hsp` / `.app` / `.hqf` container format research and `abcd-hap` reader design |
| [ir-v0.2.md](ir-v0.2.md) | Format-independent SSA IR (`abcd-ir`): 88-op taxonomy, `Effects`, `[func][new.target][this]` frame model, T1–T10 taint contract |
| [ir.md](ir.md) | Lift / Opt / Lower algorithms (Braun SSA, SCCP, Effects-ADCE, chordal MCS register allocation, Boissinot out-of-SSA) |
| [analysis-strategy.md](analysis-strategy.md) | Static analysis & taint architecture (`abcd-analysis` / `abcd-taint`): IFDS solver, rungs 0–2 PTA ladder, summaries & callback gaps |
| [decompile.md](decompile.md) | Decompiler architecture (`abcd-decompile`): expression recovery, pattern-independent structuring, JS/TS emission & oracle gates |
| [cli-plan.md](cli-plan.md) | `abcd` CLI command surface, container sniffing, exit-code contract, and `taint.toml` configuration |
| [vendor-sync.md](vendor-sync.md) | Curated `vendor/` snapshot (`OpenHarmony-v7.0-Release`), offline codegen (`scripts/vendor-gen.py`), and upstream tag radar |
| [ci.md](ci.md) | 20-job CI pipeline (`vendor-verify` + 32-bit / 3-OS build matrix + corpus & VM oracle gates) |
| [roadmap.md](roadmap.md) | Project milestones, architectural invariants, and engineering working agreements |

## Reference Surveys & Historical Records

- **External framework surveys**:
  - [hermes-ir-survey.md](hermes-ir-survey.md) — Meta Hermes IR survey informing `abcd-ir` v0.2
  - [flowdroid/](flowdroid/) (`heros.md`, `soot-infoflow.md`, `driver-and-callgraph.md`, `summaries.md`) — FlowDroid / Heros source study informing `abcd-analysis` and `abcd-taint`
  - [arkanalyzer/](arkanalyzer/) (`core-ir.md`, `callgraph-and-pta.md`, `dataflow-and-checkers.md`, `gaps-and-lessons.md`) — OpenHarmony ArkAnalyzer source study
- **Engineering audits, investigations & campaign logs**:
  - [vendor-audit.md](vendor-audit.md), [bridge-vendor-isolation.md](bridge-vendor-isolation.md), [review-isa-file.md](review-isa-file.md) — FFI/vendor safety audits and findings ledger
  - [n62-literal-array-dedup-divergence.md](n62-literal-array-dedup-divergence.md) — literal-array deduplication investigation
  - [wild-gate-evaluation.md](wild-gate-evaluation.md), [wild-smoke-report.md](wild-smoke-report.md), [test262-expansion-plan.md](test262-expansion-plan.md) — wild OHOS and `test262` gate designs
  - [test-coverage-audit.md](test-coverage-audit.md), [ci-rework-plan.md](ci-rework-plan.md), [test-plan.md](test-plan.md), [agent-roadmap.md](agent-roadmap.md) — historical audit snapshots and task registries

## End-to-end pipeline

```
.hap/.hsp/.app/.hqf ──▶ abcd-hap ──▶ .abc bytes ◀──pandasm──▶ .pa text
                                         │  ▲
                               decode    ▼  │    encode
                                     abcd-file (abcd-file-sys + abcd-isa)
                                         │  ▲
                                 lift    ▼  │    lower
                                     abcd-ir (SSA) ──abcd-opt──▶ abcd-ir
                                         │
                                         ▼
                                   abcd-analysis (CFG / Regions / IFDS / PTA)
                                     ├──▶ abcd-taint     ──▶ taint flows
                                     └──▶ abcd-decompile ──▶ .js / .ts
```
