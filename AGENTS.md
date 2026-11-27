# Agent & Contributor Guide (`abcd-rs`)

This file defines the day-to-day workflow, crate ownership boundaries, and verification rules for contributors and coding agents working in `abcd-rs`.

For binding architectural rules and historical design rulings, read:
- [`design/standards.md`](design/standards.md) — Project-wide engineering & architectural standards
- [`design/decisions.md`](design/decisions.md) — Canonical design decisions & `N*` invariant registry
- [`design/README.md`](design/README.md) — Subsystem architecture specifications

---

## 1. Repository & Documentation Scope

- **Design & Guidance Only**: Only active architecture specifications (`design/*.md`), engineering standards (`AGENTS.md`, `design/standards.md`, `design/decisions.md`), and concise crate guides (`*/README.md`) belong in the repository.
- **No Dev Diaries or External Notes**: Never commit phase logs, investigation scratchpads, or third-party engine study notes into the repository. Record investigation context, alternatives considered, and benchmark deltas in **GitHub Issues** and **Commit Messages**.
- **Zero Binary Test Blobs**: Never commit `.abc`, `.hap`, `.hsp`, or `.app` binary fixtures. Synthesize L1 unit/integration fixtures programmatically (`abcd_file::Builder`, IR builders, in-memory ZIP builders).

---

## 2. Crate Ownership & Dependency Ring

| Layer | Crates | Allowed Workspace Dependencies |
| :--- | :--- | :--- |
| **FFI & Container Base** | `abcd-isa-sys`, `abcd-isa`, `abcd-file-sys`, `abcd-file`, `abcd-hap` | `abcd-isa` → *(none — `abcd-isa-sys` in `[dev-dependencies]` only)*; `abcd-file` → `abcd-file-sys`, `abcd-isa`; `abcd-hap` → *(none)* |
| **Semantic SSA IR** | `abcd-ir` | *(none — zero internal workspace dependencies)* |
| **IR Passes & Analysis** | `abcd-opt`, `abcd-analysis`, `abcd-taint`, `abcd-decompile` | `abcd-opt`, `abcd-analysis` → `abcd-ir`; `abcd-taint`, `abcd-decompile` → `abcd-ir`, `abcd-analysis` |
| **Format Converters** | `abcd-lift`, `abcd-lower` | `abcd-lift` → `abcd-file`, `abcd-ir`, `abcd-isa`; `abcd-lower` → `abcd-ir`, `abcd-file`, `abcd-isa` |
| **CLI & Integration** | `abcd-cli`, root `abcd-rs` (`tests/*`) | Top-level consumers; `abcd-cli` is the **only** crate permitted to set `#[global_allocator]` |

### Multi-Agent Coordination Rule
- **Sub-crate threads (`ABCD · abcd-<name>`)** own code, unit/integration tests, and `README.md` strictly inside their assigned crate directory (`abcd-<name>/**`). Sub-crate threads must **never** run mutating `git` commands (`commit`, `checkout`, `restore`, `clean`, `push`).
- **Coordinator thread (`ABCD 主线程`)** exclusively owns root files (`Cargo.toml`, `README.md`, `AGENTS.md`, `design/**`, `tests/**`, `scripts/**`, `.github/**`) and serializes all Git/GitHub operations and CI checks.
- **Fix at the Right Architectural Layer (Coordinator Cross-Crate Routing Duty)**: Because sub-crate threads are strictly confined to `abcd-<name>/**`, pushing a cross-cutting bug, precision gap, or scaling bottleneck solely onto a downstream consumer (`abcd-taint`, `abcd-decompile`, `abcd-cli`) structurally pressures that worker into building local workarounds or shadow analyses. Whenever diagnosis shows a symptom originates in an upstream layer (`abcd-file`, `abcd-lift`, `abcd-ir`, `abcd-opt`, `abcd-analysis`), the Coordinator (`ABCD 主线程`) **must** intercept immediately and route the fix—or file a dedicated issue—in the canonical owning upstream crate (`design/standards.md` §2.5). Sub-crate threads that uncover an upstream root cause must stop and report the boundary mismatch to the Coordinator rather than papering over it locally.
- **T3 Code Dispatch Protocol**:
  - **Crate implementation waves**: Always dispatch per-crate tasks to the persistent `ABCD · abcd-<name>` threads via `t3_thread_list` → `t3_thread_send` (pass `freshContext: true` across major milestone boundaries when accumulated thread history is stale/heavy) followed by `t3_thread_wait` + `t3_thread_read`. This preserves a clean 1-thread-per-crate sidebar, live `running` status in T3 Code, and `full-access` command permissions.
  - **Cross-provider / multi-model blind reviews**: Dispatch read-only review agents via `delegate_task` (`orchestrator_capabilities` → `delegate_task`).
  - **Ban on provider-internal `invoke_subagent` under T3 Code**: Never spawn ACP `invoke_subagent` workers in T3 Code — `creationSource: "provider"` subagents neither expose a T3 `latestRunId` (rendering as `idle` in the UI) nor inherit T3 `full-access` command permissions.

---

## 3. Mandatory Engineering Invariants

1. **Absolute Ban on Recursion (Zero Direct, Mutual, or Derived-Trait Recursion)**: Never write direct call-stack recursion, mutual function-call cycles, or compiler-derived recursive traits (`Drop`, `Clone`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Debug`) on recursive types anywhere in `abcd-rs` (Rust crates, C/C++ bridges/shims, and `scripts/*.py`). Always use explicit heap workstacks with cycle guards, enforced by `unconditional_recursion = "deny"`, `tests/zero_recursion_gate.rs`, and `256 KiB`-stack regression tests.
2. **Bit-Exact Determinism (`N20`)**: Never iterate `HashMap` or `HashSet` directly to assign IDs, emit bytecodes/constants/relocations, or order reports. Use dense index order, bitsets, insertion-ordered tables, or explicit sorting.
3. **Error Honesty & Zero Panics**:
   - Non-test library code enforces `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`. Malformed untrusted inputs must return typed `Result::Err`, never panic or abort.
   - Never introduce an `Unsupported*` error variant to paper over an unimplemented or buggy internal path unless upstream `arkcompiler_runtime_core` / `ets_runtime` / `es2panda` itself leaves the construct unimplemented or invalid.
   - Library crates (including C++ bridges and `vendor/shim/`) must **never** write to `stdout` or `stderr`.
4. **Read-Only Vendor Snapshot**: Never hand-edit `vendor/arkcompiler_runtime_core/` or `**/generated/*`. Manage upstream updates and FFI/ISA code generation solely via `python3 scripts/vendor-gen.py {sync|codegen|verify}`.
5. **Module Cohesion, File Granularity & Test Placement (`design/standards.md` §1.4)**:
   - Grounded in the `W = 800`-line (`~46 KiB`) single-read window, keep non-exempt `.rs` files within **`~2,400` lines (`3W` target)** and strictly below **`4,000` lines (`5W` refactoring ceiling)** by splitting along cohesive subsystem/pass boundaries (never mechanical `part1.rs` / `part2.rs` slices). Flat exhaustive ~200-opcode `match` tables (`op.rs`, `verify.rs`, `translate.rs`, `isel.rs`) are exempt for production code.
   - Keep small, foundational unit tests (`≤ ~300–400` lines) inline (`#[cfg(test)] mod tests`) next to the implementation when total file length stays `≤ ~2,400` lines; once tests grow larger or span multiple themes, extract and split them **by topic** (`foo/tests/<topic>.rs` or `tests/integration/<topic>.rs`) rather than growing monolithic `tests.rs` files. When adding a new subsystem to a crate, create a dedicated submodule file instead of appending hundreds of lines to an already large file.

---

## 4. Local Verification & CI Policy

- **Absolute Ban on Local Docker / OrbStack**: Never invoke `docker` or `orbctl` on the local developer machine. Cross-OS builds, 32-bit targets, `ASan` / `UBSan` / `TSan` sanitizers, coverage, and Docker-backed `ark_js_vm` / `es2abc` oracle comparisons run exclusively on GitHub Actions CI (`27` jobs).
- **Standard Local Gate Runner**:
  ```sh
  ./scripts/test-local.sh quick    # fmt + clippy + fast unit tests (<5s incremental)
  ./scripts/test-local.sh full     # fmt + clippy + rustdoc (-D warnings) + vendor-verify + workspace L1 tests (<15s)
  ./scripts/test-local.sh corpus   # host-native #[ignore] corpus suites when exports/ / modules.abc exist locally
  ./scripts/test-local.sh all      # full + corpus (zero Docker)
  ```
