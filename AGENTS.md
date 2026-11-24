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
| **FFI & Container Base** | `abcd-isa-sys`, `abcd-isa`, `abcd-file-sys`, `abcd-file`, `abcd-hap` | `abcd-isa` → `abcd-isa-sys`; `abcd-file` → `abcd-file-sys`, `abcd-isa`; `abcd-hap` → *(none)* |
| **Semantic SSA IR** | `abcd-ir` | *(none — zero internal workspace dependencies)* |
| **IR Passes & Analysis** | `abcd-opt`, `abcd-analysis`, `abcd-taint`, `abcd-decompile` | `abcd-opt`, `abcd-analysis` → `abcd-ir`; `abcd-taint`, `abcd-decompile` → `abcd-ir`, `abcd-analysis` |
| **Format Converters** | `abcd-lift`, `abcd-lower` | `abcd-lift` → `abcd-file`, `abcd-ir`, `abcd-isa`; `abcd-lower` → `abcd-ir`, `abcd-analysis`, `abcd-file`, `abcd-isa` |
| **CLI & Integration** | `abcd-cli`, root `abcd-rs` (`tests/*`) | Top-level consumers; `abcd-cli` is the **only** crate permitted to set `#[global_allocator]` |

### Multi-Agent Coordination Rule
- **Sub-crate threads** own code, unit/integration tests, and `README.md` strictly inside their assigned crate directory (`abcd-<name>/**`). Sub-crate threads must **never** run mutating `git` commands (`commit`, `checkout`, `restore`, `clean`, `push`).
- **Coordinator thread** exclusively owns root files (`Cargo.toml`, `README.md`, `AGENTS.md`, `design/**`, `tests/**`, `scripts/**`, `.github/**`) and serializes all Git/GitHub operations and CI checks.

---

## 3. Mandatory Engineering Invariants

1. **Zero Input-Depth Recursion**: Never write call-stack recursion bounded by input size or nesting depth (CFG/dominator/region walks, AST folds/printers, literal/annotation graphs, call/alias chains, nested containers). Always use explicit heap workstacks with cycle guards and `256 KiB`-stack regression tests.
2. **Bit-Exact Determinism (`N20`)**: Never iterate `HashMap` or `HashSet` directly to assign IDs, emit bytecodes/constants/relocations, or order reports. Use dense index order, bitsets, insertion-ordered tables, or explicit sorting.
3. **Error Honesty & Zero Panics**:
   - Non-test library code enforces `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`. Malformed untrusted inputs must return typed `Result::Err`, never panic or abort.
   - Never introduce an `Unsupported*` error variant to paper over an unimplemented or buggy internal path unless upstream `arkcompiler_runtime_core` / `ets_runtime` / `es2panda` itself leaves the construct unimplemented or invalid.
   - Library crates (including C++ bridges and `vendor/shim/`) must **never** write to `stdout` or `stderr`.
4. **Read-Only Vendor Snapshot**: Never hand-edit `vendor/arkcompiler_runtime_core/` or `**/generated/*`. Manage upstream updates and FFI/ISA code generation solely via `python3 scripts/vendor-gen.py {sync|codegen|verify}`.

---

## 4. Local Verification & CI Policy

- **Absolute Ban on Local Docker / OrbStack**: Never invoke `docker` or `orbctl` on the local developer machine. Cross-OS builds, 32-bit targets, `ASan` / `UBSan` / `TSan` sanitizers, coverage, and Docker-backed `ark_js_vm` / `es2abc` oracle comparisons run exclusively on GitHub Actions CI (`28` jobs).
- **Standard Local Gate Runner**:
  ```sh
  ./scripts/test-local.sh quick    # fmt + clippy + fast unit tests (<5s incremental)
  ./scripts/test-local.sh full     # fmt + clippy + rustdoc (-D warnings) + vendor-verify + workspace L1 tests (<15s)
  ./scripts/test-local.sh corpus   # host-native #[ignore] corpus suites when exports/ / modules.abc exist locally
  ./scripts/test-local.sh all      # full + corpus (zero Docker)
  ```
