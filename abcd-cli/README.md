# abcd-cli

Unified command-line interface (`abcd`) for the `abcd-rs` ArkCompiler bytecode toolkit.

## 1. Purpose & Input Contract

`abcd-cli` is a thin orchestration binary sitting atop `abcd-hap`, `abcd-file`, `abcd-lift`, `abcd-opt`, `abcd-lower`, `abcd-analysis`, `abcd-taint`, and `abcd-decompile`:

- **Automatic format sniffing ([`src/input.rs`](src/input.rs))**: every bytecode-consuming subcommand (`info`, `dis`, `decompile`, `rewrite`, `analyze`, `taint`) accepts both standalone `.abc` files (`PANDA\0\0\0`) and OpenHarmony ZIP containers (`.hap`, `.hsp`, `.app`, `.hqf`, `PK\x03\x04` / `PK\x05\x06` unpacked in memory via `abcd_hap::abc_modules`).
- **Explicit multi-module disambiguation**: single-module `.hap`/`.hsp`/`.hqf` archives run directly; multi-module `.app` bundles and per-ability `.hap`s never pick an arbitrary module silently and require `--module <NAME>` or `--all` (colliding package names—matched case-insensitively for APFS/NTFS safety while preserving original case—disambiguate deterministically as `<module>__<entry-stem>`).
- **Path-traversal & Windows device containment**: container-supplied module names (Stage `module.json` `module.name` and FA `config.json` `module.distro.moduleName`) are sanitized deterministically into inert single path segments so read-only commands (`info`, `analyze`, `taint`) never fail on quirky manifests while writer commands (`extract` using `create_new(true)`, `--all`, `--split-modules`) reject traversal segments, backslashes, control/Windows-forbidden chars, trailing dots/spaces, and Windows reserved device stems (`CON`, `AUX`, `COM0`..`COM9`, `LPT0`..`LPT9`, `CONIN$`, `CONOUT$`).

## 2. Subcommand Reference

| Subcommand | Synopsis | Pipeline & Key Flags |
|------------|----------|----------------------|
| `extract` | `abcd extract <container> [-o <dir>] [--force]` | Unpacks `<module>.abc` and `<module>.module.json` from a container; preflight-rejects existing targets without `--force`. |
| `info` | `abcd info [--verify] [--json] [--module <name> \| --all] <input>` | Reports header version, file type (`dynamic`/`static`/`invalid`), checksum, entity counts, and optional full decode verification (`--verify`). |
| `dis` | `abcd dis [-o <path>] [--module <name> \| --all] <input>` | Disassembles `.abc` to pandasm `.pa` raw bytes (`ADR-11`, byte-for-byte identical to upstream `ark_disasm`). |
| `asm` | `abcd asm [-o <out.abc>] [--version <M.m.p.b>] [--check] <input.pa>` | Assembles pandasm `.pa` text into `.abc` with optional format version override and `--check` re-decode self-check. |
| `decompile` | `abcd decompile [-o <path>] [--split-modules] [--arkui] [--ts] [--line-anchors] [--call-entry] [--module <name> \| --all] <input>` | Decompiles pre-opt SSA IR to JS, TypeScript annotations (`--ts`), `--merge-abc` multi-file trees (`--split-modules`), and ArkUI `@Component struct` / `build()` views (`--arkui`). |
| `rewrite` | `abcd rewrite [-o <path>] [--opt] [--check] [--module <name> \| --all] <input>` | Rewrites `.abc` through `decode → lift → verify → [opt] → lower → encode` with optional `--opt` passes and `--check` (`re-decode → re-lift → re-verify`) verification. |
| `analyze` | `abcd analyze [--callgraph] [--dominators] [--pta] [--alias-rung <0\|1\|2>] [--pta-budget <steps>] [--json] [--module <name> \| --all] <input>` | Emits IR arena summaries, call-graph resolution histograms, Rung-2 pointer-analysis telemetry (`--pta` / `--pta-budget`, including `root_sliced`), per-site targets (`--callgraph`), and RPO immediate-dominator trees (`--dominators`). |
| `taint` | `abcd taint [--preset ohos] [--config <taint.toml>] [--link-modules] [--alias-rung <0\|1\|2>] [--pta-budget <steps>] [--json] [--module <name> \| --all] <input>` | Runs interprocedural IFDS taint analysis with the built-in OpenHarmony rule pack (`--preset ohos`), custom TOML configs (`--config`), alias/PTA controls (`pta_root_sliced`, `ohos_lifecycle`), and cross-`.abc` linking (`--link-modules`). |

## 3. Exit Codes, Stdio Discipline & Global Allocator

Full specification in [`../design/cli.md`](../design/cli.md), [`../design/standards.md`](../design/standards.md), and [`../design/decisions.md`](../design/decisions.md):

- **`0` — Success**: primary artifacts (`.pa`, `.js`/`.ts`/`.ets`, `.abc`, aligned text, or `--json` object/array) are written strictly to `stdout` or `-o <path>` with zero diagnostic chatter on `stdout` (`BrokenPipe` on `stdout` exits `0` cleanly without panicking).
- **`1` — User / Invocation Error**: invalid CLI flags (`clap` parse errors remapped from `2` to `1`, conflicting `--pta` / `--pta-budget` with `--alias-rung < 2`, or unsupported `asm --version`), unreadable inputs, undisambiguated multi-module containers, existing `extract` targets without `--force`, unparseable `.pa` text, or invalid `taint.toml` / `--preset` arguments (`stderr`).
- **`2` — Tool / Processing Error**: corrupt `.abc`/ZIP inputs, unsafe container module names, `decode`/`lift`/`verify`/`lower`/`encode` failures, I/O write errors, or `--verify`/`--check` failures (`stderr`; writer commands are all-or-nothing and never emit partial files).
- **Binary-only `mimalloc` (`ADR-12`)**: `abcd-cli` ([`src/main.rs`](src/main.rs)) is the **only** crate in the workspace that sets `#[global_allocator]` (`mimalloc::MiMalloc` across Linux, macOS, and Windows MSVC); all library crates stay allocator-neutral and silent on stdio.
- **Determinism & zero panics (`N20`)**: `#![cfg_attr(not(test), deny(clippy::unwrap_used))]` enforced across library modules (`#![deny(clippy::unwrap_used)]` in `main.rs`) with bit-exact deterministic output.

## 4. Quick Start & `taint.toml` Schema

```sh
# Inspect and verify every module in an OpenHarmony .app bundle as JSON
abcd info --all --verify --json bundle.app

# Reconstruct a --merge-abc HAP into a multi-file ArkUI source tree
abcd decompile app.hap --split-modules --arkui -o out_src/

# Run whole-application cross-module OpenHarmony taint analysis
abcd taint bundle.app --all --link-modules --preset ohos --json
```

`abcd taint --config <taint.toml>` parses a strict (`#[serde(deny_unknown_fields)]`) TOML document ([`src/taint_config.rs`](src/taint_config.rs)) mapping to `abcd_taint::TaintConfig` (combine with `--preset ohos` or `preset = "ohos"` to layer custom rules onto built-in OpenHarmony sources/sinks):

```toml
# Optional engine toggles (shown with defaults):
# preset = "ohos"
builtin_summaries = true
seed_all_functions = true
follow_returns_past_seeds = true
native_identity = true
ohos_lifecycle = true
max_field_chain = 5
alias_rung = 2        # 0 = local def-chain, 1 = demand alias, 2 = k=1 Andersen PTA
# pta_step_budget = 250000

[[sources]]
kind = "function_params"   # or "global_load", "call_return", "module_import"
name = "func_main_0"       # "*" matches every function; optional `params = [3, 4]`

[[sources]]
kind = "module_import"
specifier = "@ohos.deviceInfo"

[[sinks]]
kind = "call"
name = "console.log"       # bare global ("print") or qualified ("@ohos.hilog.info")

[[extra_summaries]]
name = "passthrough"
arity = 1                  # optional; omit for variadic; optional `callback_param = 0`
exclusive = false
flows = [{ from = "param:0", to = "return" }, { from = "any_param_from:1", to = "return" }]
alias_flows = []
clears = []
```

## 5. Verification

```sh
./scripts/test-local.sh crate abcd-cli
cargo test -p abcd-cli
cargo clippy -p abcd-cli --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-cli --no-deps
```
