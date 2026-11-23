# abcd-cli

Command-line interface (`abcd`) for the `abcd-rs` ArkCompiler bytecode toolkit.

Every bytecode-consuming subcommand accepts either a bare `.abc` file or an OpenHarmony application container (`.hap`, `.hsp`, `.app`, `.hqf`), sniffed by magic bytes (`PANDA\0\0\0` vs `PK\x03\x04` / `PK\x05\x06`). Multi-module containers (e.g. `.app` bundles or FA-model multi-ability `.hap`s) require an explicit `--module <NAME>` or `--all`.

## Subcommands

| Command | Synopsis | Description |
|---------|----------|-------------|
| `extract` | `abcd extract <container> [-o <dir>] [--force]` | Extract `.abc` module(s) and `module.json` / `config.json` / `patch.json` from a container |
| `info` | `abcd info [--verify] [--json] [--module <name> \| --all] <input>` | Print header version, file type, class/method/literal counts, and optional full decode verification |
| `dis` | `abcd dis [-o <path>] [--module <name> \| --all] <input>` | Disassemble `.abc` to pandasm `.pa` text (byte-identical to upstream `ark_disasm`) |
| `asm` | `abcd asm [-o <out.abc>] [--version M.m.p.b] [--check] <input.pa>` | Assemble pandasm `.pa` text into `.abc` |
| `decompile` | `abcd decompile [-o <path>] [--ts] [--line-anchors] [--call-entry] [--module <name> \| --all] <input>` | Decompile bytecode to readable JavaScript (or TypeScript-annotated output on ≤11-format files) |
| `rewrite` | `abcd rewrite [-o <path>] [--opt] [--check] [--module <name> \| --all] <input>` | Rewrite bytecode through `decode → lift → [opt] → lower → encode` |
| `analyze` | `abcd analyze [--callgraph] [--dominators] [--json] [--module <name> \| --all] <input>` | Static analysis report over the lifted SSA IR (call-graph resolution histogram, per-site targets, dominator trees) |
| `taint` | `abcd taint --config <taint.toml> [--json] [--module <name> \| --all] <input>` | Interprocedural IFDS taint analysis driven by a TOML source/sink/summary configuration |

## Exit codes & output conventions

- `0` — success (results written to `stdout` or `-o <path>`).
- `1` — user error (invalid CLI flags, missing files, ambiguous multi-module selection, invalid TOML config; diagnostics on `stderr`).
- `2` — tool error (corrupt `.abc`/container input, decode/lift/lower/encode failure, `--verify` or `--check` rejection; diagnostics on `stderr`).

## Taint configuration (`taint.toml`)

`abcd taint --config <path>` parses a strict (`deny_unknown_fields`) TOML configuration mapping directly to `abcd_taint::TaintConfig`:

```toml
# Optional engine toggles (shown with defaults):
builtin_summaries = true
seed_all_functions = true
follow_returns_past_seeds = true
native_identity = true
max_field_chain = 5
alias_rung = 2   # 0 = local def-chain, 1 = on-demand alias, 2 = whole-module k=1 PTA

[[sources]]
kind = "function_params"
name = "func_main_0"   # "*" matches every function
# params = [3, 4]      # optional parameter slot indices; omit for all slots

[[sources]]
kind = "global_load"
name = "TAINT"

[[sinks]]
kind = "call"
name = "console.log"   # bare global ("print") or qualified ("console.log")

[[extra_summaries]]
name = "passthrough"
arity = 1
exclusive = false
flows = [{ from = "param:0", to = "return" }]
alias_flows = []
clears = []
```

## Allocator

`abcd-cli` is the only crate in the workspace that sets `#[global_allocator]` (`mimalloc` across all target platforms); library crates never install a global allocator.

## License

Apache-2.0.
