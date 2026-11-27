# Project-Wide Engineering & Architectural Standards

This document establishes the binding architectural, algorithmic, safety, and testing standards across all 13 crates of `abcd-rs`. Every pull request, issue implementation, and automated agent change must comply with these rules.

---

## 1. Repository, Module & Documentation Hygiene

1. **Evergreen Design & Guidance Only**:
   - Tracked Markdown files consist solely of root `README.md`, `AGENTS.md`, subsystem specifications and policies under `design/*.md`, and concise crate `README.md`s.
   - External competitor/prior-art reading notes, pre-implementation brainstorms, and chronological phase diaries (`MEMORY.md`, `d-P*`/`t-P*` campaign logs) are **strictly excluded** from the repository.
   - Design rationale for individual changes, benchmark tables, and debugging timelines belong in **GitHub Issues** and **Commit Messages**.
2. **Crate `README.md` Standard**:
   - Each crate `README.md` stays concise (~50–140 lines) and follows five sections: **(1) Purpose & Layering Contract**, **(2) Architecture / Module Map**, **(3) Key Invariants** (linking to [`decisions.md`](decisions.md)), **(4) Compiling Quick Start**, and **(5) Verification** (`./scripts/test-local.sh`).
3. **Rustdoc Zero-Warning Gate**:
   - Public items in enforced crates carry doc comments (`#![deny(missing_docs)]`), and `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps` must pass with zero broken intra-doc links.
4. **Module Cohesion, File Granularity & Test Organization**:
   - **Cohesion-First Decomposition**: Organize source files around a single cohesive pass, data structure, or subsystem—never split mechanically by line numbers (`part1.rs`, `part2.rs`).
   - **Tool-Window Granularity Thresholds (`W = 800` lines / `~46 KiB` single-read window)**:
     - **`≤ 2,400` lines (`3W`) — Target Span**: Non-exempt production and test `.rs` files should stay within `~2,400` lines so a reviewer or coding agent can read the entire module in one parallel batch without partial-slice blind spots.
     - **`4,000` lines (`5W`) — Structural Refactoring Ceiling**: Any non-exempt `.rs` file exceeding `4,000` lines must be split along cohesive subsystem or topic boundaries to eliminate cross-file context blowup and multi-thousand-line edit stalls.
     - **Flat Exhaustive Dispatch Exemption**: Single-pass files whose length comes from exhaustive `match` arms over the ~200+ Panda/IR opcodes or wire tags (e.g., `abcd-ir/src/op.rs`, `abcd-ir/src/verify.rs`, `abcd-lift/src/translate.rs`, `abcd-lower/src/isel.rs`) are exempt from line-count splitting so Rust's exhaustiveness checks and side-by-side opcode audits remain in one place.
   - **Topic- & Scale-Driven Unit Test Placement**:
     - **Small foundational unit tests stay inline**: Concise tests (`≤ ~300–400` lines) exercising local data-structure invariants or low-level helpers belong inline (`#[cfg(test)] mod tests`) at the bottom of the implementation file for immediate co-located readability, provided the total file stays within `~2,400` lines.
     - **Large or multi-theme suites are externalized by topic**: Once unit tests grow substantial (`> ~400` lines or pushing the host file past `~2,400` lines) or span distinct functional themes, extract them into topic-organized sibling modules (`foo/tests.rs`, `foo/tests/<topic>.rs`, or `tests/integration/<topic>.rs`)—never accumulate monolithic `4,000+`-line catch-all `tests.rs` files either.

---

## 2. Layering & Library Purity

1. **Strict One-Way Dependency Ring**:
   - `abcd-isa` has **zero** internal workspace runtime dependencies (`#![forbid(unsafe_code)]`; `abcd-isa-sys` is linked solely under `[dev-dependencies]` for C++ differential oracle tests).
   - `abcd-ir` has **zero** internal workspace dependencies and **zero** container/ISA concepts (no file byte offsets, no ULEB/register width encodings, no raw pool indices), owning canonical CFG traversal (`block_succs`, `inst_succs`, `compute_rpo`, `ExceptionHandlerMap`) and Semi-NCA `DomTree`.
   - `abcd-opt` and `abcd-analysis` depend **only** on `abcd-ir` in `[dependencies]`; `abcd-lower` depends **only** on `abcd-ir`, `abcd-file`, and `abcd-isa` (never `abcd-analysis`).
   - `abcd-taint` and `abcd-decompile` depend **only** on `abcd-ir` and `abcd-analysis` in `[dependencies]` (decompiler region/try structuring lives in `abcd-decompile::structure::regions`).
   - Container/bytecode crates (`abcd-file`, `abcd-isa`, `abcd-hap`) may be pulled by IR/analysis crates **only** under `[dev-dependencies]` for integration tests.
2. **Global Allocator Isolation**:
   - Library crates (`abcd-isa*`, `abcd-file*`, `abcd-hap`, `abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`, `abcd-analysis`, `abcd-taint`, `abcd-decompile`) **never** declare `#[global_allocator]`.
   - Only final binary crates (`abcd-cli`) configure a global allocator in `main.rs`.
3. **Silent Library Stdio**:
   - No library crate—and no C/C++ translation unit or shim linked into `abcd-isa-sys` or `abcd-file-sys`—may write to `stdout` or `stderr`. Only `abcd-cli` owns terminal and `--json` output streams (`0` = success, `1` = CLI/user error, `2` = input/processing error).
4. **Single-Point IR Queries**:
   - Passes, analyses, verifiers, and emitters must query instruction semantics through canonical single-point methods on [`abcd_ir::Op`] (`operands`, `operands_mut`, `effects`, `has_result`, `is_terminator`, `arity`) rather than maintaining ad-hoc opcode match lists that silently drift when `Op` evolves.

---

## 3. Algorithmic Complexity, Stack Safety & Memory Discipline

1. **Absolute Workspace-Wide Ban on Recursion**:
   - Real-world obfuscated/bundled `.abc` files and `test262` fixtures exceed 500+ levels of CFG, expression, literal-array, annotation, and try/catch nesting; thread stacks on Windows, musl, and worker pools can be as small as 256 KiB–1 MiB.
   - **Rule**: Zero direct call-stack recursion, zero mutual function-call cycles, and zero compiler-derived recursive traits (`Drop`, `Clone`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Debug`) on recursive types are permitted anywhere in `abcd-rs` (`abcd-*/src/**/*.rs`, `abcd-*-sys/bridge/**`, `vendor/shim/**`, and `scripts/*.py`).
   - Use explicit heap-allocated workstacks (`Vec<Frame>`) paired with visited/active cycle guards, enforced statically by `[workspace.lints.rust] unconditional_recursion = "deny"` and `tests/zero_recursion_gate.rs` (iterative Tarjan SCC over intra-crate call and type-containment graphs), plus `256 KiB` small-stack regression tests (`std::thread::Builder::new().stack_size(256 * 1024)`).
2. **Linear / Near-Linear Scaling**:
   - Commercial `--merge-abc` bundles exceed `20+ MB`, `58,000+` functions, and `94,000+` symbols.
   - **Rule**: Never scan module-wide tables (`O(|Module|)`) inside per-function, per-block, or per-instruction loops. Pre-index module tables once (`O(|Module|)`), and use dense `Vec` / flat `BitSet` storage indexed by newtype IDs (`BlockId`, `ValueId`, `InstId`, `FuncId`) on hot paths.
3. **Bounded Memory Amplification & Streaming Emission**:
   - Avoid cloning whole `File` or `Module` structures unnecessarily; prefer borrowing slices, compact `u32` arena IDs, and streaming large outputs (`pandasm`, JS/TS emission, JSON reports) directly to `impl std::io::Write` or pre-sized buffers.

---

## 4. Bit-Exact Determinism (`N20` Standard)

1. **Deterministic Byte & Text Output**:
   - Given identical input bytes, every crate entrypoint (`decode`, `encode`, `dis`, `asm`, `lift`, `optimize`, `lower`, `decompile`, `analyze`, `taint`) must produce **bit-for-bit identical** output across repeated runs, operating systems, architectures, and random `RandomState` seeds.
2. **No Unordered Map Iteration in Output Paths**:
   - Never iterate over `std::collections::{HashMap, HashSet}` to assign `Sym`/`ConstId`/`FuncId`/`BlockId`/`ValueId` indices, emit instructions or literal arrays, schedule worklists, or order user-visible diagnostics.
   - When hash lookups are used for deduplication, maintain an accompanying `Vec` in insertion order, use `BTreeMap`/`BTreeSet`, or sort keys explicitly (`sort_unstable`) before emission.

---

## 5. Error Honesty & Untrusted-Input Safety

1. **Anti-Workaround Rule (No Fake `Unsupported*` Rulings)**:
   - Never turn an uninvestigated format detail or a fixable implementation bug into a hard `Error::Unsupported*` variant.
   - A hard `Unsupported*` rejection is permitted **only** when grounded in concrete upstream citations (`arkcompiler_runtime_core`, `arkcompiler_ets_runtime`, `es2panda`/`ets2panda`) proving that the construct is unimplemented, fatal, or unencodable upstream (e.g., dead fused compare-branch opcodes or `0.0.0.2` binary writer output).
2. **Zero Panics on Untrusted Data**:
   - Every `.abc`, `.pa`, `.hap`, `.hsp`, `.app`, and `.hqf` input is treated as potentially adversarial.
   - Non-test code enforces `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`. Integer narrowing (`u32` → `u16`, `usize` → `u32`), slice indexing on wire offsets, and ULEB128 reads must be checked and return typed `thiserror` errors on overflow or truncation.
3. **Explicit Fallback & Soundness Floor**:
   - **`abcd-decompile`**: Any IR construct that cannot be faithfully rendered as source syntax must produce an explicit `Expr::Fallback` / `Stmt::Fallback` marker counted in `DecompileStats` and gated by self-cleaning corpus ledgers—never silently dropped or miscompiled.
   - **`abcd-analysis` / `abcd-taint`**: Unresolved dynamic calls (`CallTargets::UnknownCallees`), recursion-depth cuts, or PTA step-budget exhaustion must degrade loudly to a sound conservative floor (`Rung0` local def-chain / over-approximate flow), never silently dropping taint or call edges.

---

## 6. Vendor Snapshot & C++ FFI Firewall

1. **Immutable Upstream Snapshot**:
   - `vendor/arkcompiler_runtime_core/` pins an exact upstream release (`vendor/UPSTREAM.toml`) verified by per-file SHA-256 in Tier-1 CI (`python3 scripts/vendor-gen.py verify`).
   - Rust FFI declarations (`ffi_bindings.rs`), ISA tables, and the `109` C++17 `static_assert` enum checks (`file_bridge_enum_checks.h`) are generated deterministically by `scripts/vendor-gen.py codegen`—zero `bindgen`/`libclang` and zero build-time Ruby.
2. **C99 Exception & Bounds Firewall**:
   - Every `extern "C"` entrypoint in `abcd-file-sys` (and allocating/STL entrypoints in `abcd-isa-sys`, while pure `noexcept` lookup queries validate opcodes directly) catches all C++ exceptions (`SUPPORT_KNOWN_EXCEPTION` + `LogVoidify::operator&` throw conversion in `vendor/shim/utils/logger.h`, never throwing from a destructor, plus silent `ABORT_AND_UNREACHABLE`/`CHECK` shims) before crossing into Rust.
   - Header table spans (`file_size`, `foreign`, `classes`, `lnps`, `literalarrays`, `indexes`) and 4-byte index-table alignments are validated in 64-bit arithmetic before constructing `panda_file::File`.
   - Never call raw `strlen` or `strcmp` on `.abc` string bytes; bound every string read by both its declared MUTF-8 length prefix and the file payload span (`bounded_cstr_len`).
   - Clamp every wire-declared element count against remaining payload bytes before allocating buffers (`>= 1` byte per element) to prevent crafted multi-gigabyte OOM panics.

---

## 7. Testing Tiers & Zero-Container Local Workflow

1. **Local vs. CI Responsibility Split**:
   - **Local hosts never run OrbStack or Docker.** Developers and agents run `./scripts/test-local.sh {quick|full|corpus|all}` natively.
   - **GitHub Actions CI (`27` jobs)** owns the 6-OS 64-bit matrix, 3-target 32-bit matrix (including QEMU `armv7`), `ASan + UBSan` and `TSan` sanitizer gates (Rust + C++), `llvm-cov` coverage, `cargo-deny`, and all Docker-backed `ark_js_vm` / `es2abc` / Node execution gates.
   - Cross-platform CI lanes compile and test the entire workspace (`cargo test --workspace`), ensuring `abcd-cli` and `mimalloc` stay green across Linux, macOS, Windows MSVC/ARM64, and 32-bit targets.
2. **Self-Cleaning Divergence Ledgers**:
   - Every ledger under `scripts/*-divergences.json` enforces **two-way assertions**: an unlisted failure breaks CI, and a listed entry that starts passing **also** breaks CI until removed from the ledger.
