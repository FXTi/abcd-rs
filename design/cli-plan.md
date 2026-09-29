# abcd CLI plan — external command-line surface

Status: P1 LANDED (2026-09-28): `abcd` binary (abcd-cli) ships extract /
info / dis / decompile; `dis` is byte-identical to ark_disasm over the full
5517-fixture corpus (gate: tests/file-isa/pandasm_dis.rs, empty ledger).
All six §6 points ruled 2026-09-28 (see §6).

## 1. Why now

Every pipeline stage has a stable public entry point (`abcd_file::decode`,
`abcd_isa::encode/decode`, `abcd_lift::lift_file`, `abcd_opt::optimize_module`,
`abcd_lower::lower_function*`, `abcd_taint::run_taint`,
`abcd_decompile::decompile_module`), and abcd-hap now supplies container
extraction. What is missing is a user-facing binary. Today the only way to use
the toolkit is as a library or through the test harness.

The workspace already declares `clap = { version = "4", features = ["derive"] }`
in `[workspace.dependencies]` (currently unused — reserved for this).

## 2. Command inventory (what the toolkit can honestly ship)

| Command | Capability source | Direction | Notes |
|---|---|---|---|
| `abcd extract` | abcd-hap | .hap/.hsp/.app/.hqf → .abc file(s) + module.json | First real consumer of abcd-hap. (Ruled name: `extract`, not `unpack`.) |
| `abcd info` | abcd-file | .abc → header/entity summary | readelf-style: format version, counts (classes/methods/strings/literal arrays), index regions. `--verify` = full decode + structural checks, exit code carries the verdict. |
| `abcd dis` | abcd-file + abcd-isa | .abc → pandasm text | Backed by the 4,557,285-instruction 0-mismatch corpus evidence. Options: whole file / single method / raw byte offsets. **Ruled 2026-09-28: output must be BYTE-IDENTICAL to upstream ark_disasm — see §4.1.** |
| `abcd asm` | abcd-isa + abcd-file | pandasm text → .abc | The round-trip direction of `dis`. A **writer** — phase 2. |
| `abcd rewrite` | file→lift→opt→lower→file | .abc → rewritten .abc | Identity or optimizing rewrite (normalization, future instrumentation hook). A **writer** — phase 2. |
| `abcd decompile` | abcd-decompile | .abc → .js | EmitOptions surfaced as flags (`--line-anchors`, `--ts`, entry-call toggle). |
| `abcd analyze` | abcd-analysis | .abc → callgraph/dominator/region reports | Needs an output format decision (text tree vs `--json`). |
| `abcd taint` | abcd-taint | .abc + source/sink config → findings | TaintConfig has sources/sinks/builtin_summaries/seed flags; CLI needs a small config file format (TOML/JSON) or repeated flags. |

Non-goals (explicitly out): packing containers (we are unpack-only by design),
signing, any VM execution (the oracle stays a test-side docker concern), an
interactive REPL.

## 3. Architecture

### 3.1 One binary, subcommands

`abcd <command> [args]` — git-style. Rationale:

- The input layer is shared by every command (see §3.2); one binary keeps it
  in one place.
- One install, one `--help` tree to discover.
- Binary size is irrelevant here (static Rust binary, all crates linked either
  way).

The alternative (per-tool binaries `abcd-dis`, `abcd-asm`, …) multiplies the
install/distribution story and duplicates plumbing for no user benefit.
Busybox-style argv[0] aliases can be added later for free if anyone wants them.

### 3.2 Shared input layer (the important part)

Every command that takes bytecode accepts **both** a bare `.abc` and a
container (`.hap`/`.hsp`/`.app`/`.hqf`), sniffed by magic bytes
(`PK\x03\x04` ⇒ abcd-hap; otherwise ⇒ abcd-file):

- bare abc → one implicit module.
- container with exactly one module → that module.
- container with several modules (an `.app`) → **hard error listing the
  modules** unless `--module <name>` or `--all` is given. No silent picking
  (hard-errors-over-warnings rule).

For commands that output per-module artifacts (`decompile`, `dis`), `--all`
produces `<out-dir>/<module-name>.{js,pa}` using the container provenance names.

### 3.3 Crate placement

New workspace member **`abcd-cli`** (bin crate, `[[bin]] name = "abcd"`,
publish = false for now). The root package stays the cross-crate test
container (publish=false, empty lib) — mixing the CLI into it would blur its
role, and a separate crate keeps the dependency graph honest (abcd-cli depends
on everything; nothing depends on abcd-cli).

### 3.4 Output and error conventions

- Human-readable text on stdout by default; `--json` on `info`, `analyze`,
  `taint` (the machine-consumable ones). `dis`/`decompile`/`asm`/`rewrite`
  output the artifact itself (text or .abc) to stdout or `--out`.
- Diagnostics on stderr, exit codes: 0 ok, 1 user error (bad args, unreadable
  input), 2 analysis/tool error (decode failure, taint crash-free error).
- No panics on data anywhere (repo rule); every fallible step returns
  structured errors through clap's error channel.

## 4. Phasing

**P1 — read-only tools (zero writer risk):**
`extract`, `info` (+`--verify`), `dis`, `decompile`.
These only read abc / write text. They exercise abcd-hap in production shape.

**P2 — writers:**
`asm`, `rewrite`. These emit .abc files; they lean on the existing
pandasm/VM oracle evidence, and each gets a round-trip self-check flag
(`--check`: re-decode the emitted bytes before writing).

**P3 — analysis surface:**
`analyze`, `taint`. Needs the report-format design (what a SinkHit looks like
in JSON, how paths are rendered). Also the config-file question for taint.

Each phase lands behind the same red-first + synthesized-fixture testing
discipline as abcd-hap.

### 4.1 The pandasm text layer (scope correction, 2026-09-28)

`dis`/`asm` are **not** pure wiring: abcd-isa's decoder/emitter handle the
*binary* instruction stream; the pandasm **text** parser lives only in the
test harness (`tests/file-isa/main.rs: parse_pandasm`) and a whole-file text
emitter (banner sections, `.record`/`.function` declarations, layout) does
not exist at all. Both commands therefore require a new library layer:

- `abcd-isa` (or a small `abcd-pa` crate): `.pa` whole-file **emitter** and
  **parser** (the parser promoted from test code).
- **Fidelity ruling (maintainer, 2026-09-28)**: the pandasm layer in general
  needs *same format, same semantics* — normalization-level equality is
  enough wherever the text is an intermediate (asm input, round-trips).
  **Exception: `abcd dis` itself must be BYTE-IDENTICAL to upstream
  `ark_disasm`.** Enforced by a per-push byte-diff gate over the corpus
  (image-provided reference .pa files already exist), with any intentional
  divergence going through the self-cleaning ledger pattern (N72 option B),
  not silent tolerance.
- Effort note: the banner/record/annotation layout is the new surface; the
  instruction rendering core already exists in canonical form in the test
  harness (`our_canonical`), so this is a lift-and-harden, not a from-scratch
  format implementation.

## 5. Testing strategy (consistent with the repo's zero-binary-fixture rule)

- **CLI-arg unit tests**: clap `try_parse_from` coverage per subcommand.
- **Golden-output tests on synthesized abc**: build tiny abc files in-test
  with `abcd_file::Builder` (precedent: the N74 pin tests already synthesize
  files this way), run the command's core fn, compare stdout. No binary
  fixtures in the repo.
- **Container input tests**: reuse the abcd-hap synthesized-ZIP builder
  pattern to feed `info`/`dis` via .hap input.
- **Opt-in corpus smoke (phase 2 of the image, optional)**: run
  `abcd info --verify` over the exported corpus in CI like the existing
  corpus gates — but only if the maintainer wants CLI-level corpus coverage;
  the library-level gates already exist.

## 6. Decision points for the maintainer — ALL RULED 2026-09-28

1. **Single `abcd` binary with subcommands** — RULED: yes.
2. **New `abcd-cli` crate** — RULED: yes (root package stays the test
   container).
3. **Phase 1 scope** — RULED: extract / info / dis / decompile.
4. **Command names** — RULED: `extract` (not `unpack`), `dis`/`asm` short
   forms.
5. **Distribution** — RULED: local `cargo install --path abcd-cli` for now;
   crates.io / GitHub releases deferred.
6. **`taint` config** — RULED: TOML file (phase 3).

Additional fidelity ruling in §4.1: `dis` byte-identical to ark_disasm.
