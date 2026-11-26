# Command-Line Interface (`abcd-cli`)

`abcd-cli` provides the single unified `abcd` binary exposing every layer of `abcd-rs` with automatic `.abc` vs. OpenHarmony container (`.hap`, `.hsp`, `.app`, `.hqf`) input detection.

---

## 1. Shared Input & Container Layer

Every bytecode-consuming subcommand (`info`, `dis`, `decompile`, `rewrite`, `analyze`, `taint`) shares a single input loader (`abcd-cli/src/input.rs`):

1. **Magic-Byte Sniffing**:
   - `PANDA\0\0\0` → decoded directly as a standalone `.abc` file.
   - `PK\x03\x04` / `PK\x05\x06` → unpacked in memory via `abcd_hap::abc_modules`.
2. **Multi-Module Disambiguation**:
   - Single-module `.hap`/`.hsp`/`.hqf` inputs run directly without extra flags.
   - Multi-module containers (`.app` bundles or per-ability `.hap`s) **never** pick an arbitrary module silently: the user must pass either `--module <NAME>` or `--all` (disambiguated as `<module>__<entry-stem>` when multiple `.abc` entries share a package).

---

## 2. Subcommand Surface

| Subcommand | Pipeline | Key Options |
| :--- | :--- | :--- |
| `abcd extract` | `abcd-hap::unpack` | `-o <dir>`, `--force` (safe Zip-Slip sanitized extraction of `.abc` + manifests) |
| `abcd info` | `abcd-file` header / full `decode` | `--verify` (full decode check), `--json`, `--module` / `--all` |
| `abcd dis` | `decode` → `pandasm::emit_file` | `-o <path>`, `--module` / `--all` (byte-identical to upstream `ark_disasm`) |
| `abcd asm` | `pandasm::parse_file_with_version` → `encode` | `-o <out.abc>`, `--version <M.m.p.b>`, `--check` (readback verification) |
| `abcd decompile` | `decode` → `lift_file` → `abcd-decompile` | `-o <path>`, `--split-modules` (`--merge-abc` source tree), `--arkui` (`@Component struct` sugar), `--ts`, `--line-anchors`, `--call-entry`, `--module` / `--all` |
| `abcd rewrite` | `decode` → `lift_file` → `verify` → `[opt]` → `rewrite_file` → `encode` | `-o <path>`, `--opt`, `--check` (re-decode + re-lift + re-verify), `--module` / `--all` |
| `abcd analyze` | `decode` → `lift_file` → `abcd-analysis` | `--callgraph`, `--dominators`, `--pta` (Rung 2, exposes `root_sliced`), `--alias-rung`, `--pta-budget`, `--json`, `--module` / `--all` |
| `abcd taint` | `decode` → `lift_file` → `[merge_ir_modules]` → `run_taint` | `--preset ohos` or `--config <taint.toml>` (`any_param_from:N` variadic flows), `--link-modules` (cross-`.abc` linking), `--json` (`pta_root_sliced`, `ohos_lifecycle`), `--module` / `--all` |

---

## 3. Exit Codes, Path Containment & Stream Discipline

- **`0` — Success**: Primary output (`.pa`, `.js`/`.ts`, JSON report, info summary) is written to `stdout` (or `-o <path>`). Closed downstream pipes (`BrokenPipe`, e.g. `| head`) terminate cleanly with `0` rather than panicking. Zero diagnostic chatter is written to `stdout`.
- **`1` — User / Invocation Error**: Invalid or contradictory CLI arguments (`analyze --pta` with `--alias-rung < 2`, `asm --version 0.0.0.2`), missing input paths, un-disambiguated multi-module container without `--module`/`--all`, or malformed `taint.toml` (`serde` `deny_unknown_fields`); human-readable error printed to `stderr`.
- **`2` — Input / Processing Error**: Corrupt `.abc`/ZIP input, empty container (`PK\x05\x06` with zero `.abc` entries), unsafe/Windows-reserved output paths (`CON`, `NUL`, `COM0..9`, `LPT0..9`, trailing dots/spaces), decode/lift/verify/lower/encode error, or `--verify`/`--check` failure; diagnostic printed to `stderr`.
- **Case-Folded Output Disambiguation**: Multi-module container extraction and `--split-modules` source emission deduplicate collision keys case-insensitively (`to_ascii_lowercase()`) while preserving display casing, preventing silent overwrites on APFS and NTFS.

---

## 4. Global Allocator Policy

`abcd-cli` (`src/main.rs`) is the **sole** crate in the workspace that installs `#[global_allocator]` (`mimalloc::MiMalloc`), providing fast multi-threaded allocation across Linux (glibc & musl), macOS, and Windows MSVC while keeping all library crates allocator-neutral for downstream Rust embedders.
