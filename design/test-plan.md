# Test plan — isa & file foundation (tests first)

Status: active. Complements design/vendor-audit.md (§3 findings, §4
compatibility matrix) and design/ir.md (v0.2 boundary).

## Principles

1. **Tests first, fixes derived**: every item-type/version gap gets a
   failing test before implementation changes; each fix lands as one
   commit with its regression test (existing working agreement).
2. **Scattered tests before round-trips**: round-trip is the composition
   of many unit behaviors — pin the units first, then compose.
3. **Corpus is generated, never committed**: `.abc` outputs are
   gitignored. Corpus comes from compiling open-source ES6-style sources
   with upstream es2abc toolchains (multiple arkcompiler releases) — and
   from OpenHarmony preinstalled-app assets where the maintainer provides
   them locally. **Never dump hap/app binaries into the repo** (Huawei
   distribution restrictions); record their origin in the ledger instead.

## Corpus pipeline (`scripts/gen-corpus.sh`)

- Sources: `scripts/corpus-src/*.js|ts` — 11 small ES6 programs covering
  classes/inheritance, closures/rest/arrows, generators/async, modules,
  object/array literals, literal taxonomy, try/catch/finally, typed
  ArkTS constructs, control flow, unicode strings, global/lexical scopes.
- Run with `ES2ABC=/path/to/es2abc` from any arkcompiler release
  (OpenHarmony 3.2 → 9.0.0.0, 4.0/4.1 → 11.0.2.0/12.0.6.0, master →
  24.0.0.0) to stamp each version family.
- The header `version` written by the toolchain is authoritative; the
  script does not pass API flags.

### Corpus ledger (versions × sources × origin)

| File version | Expected from | Status |
|--------------|---------------|--------|
| 9.0.0.0 | OpenHarmony 3.2 es2abc | not yet generated |
| 11.0.2.0 | OpenHarmony 4.0 es2abc | not yet generated |
| 12.0.6.0 | OpenHarmony 4.1 es2abc + modules.abc (device stock, local only) | modules.abc available locally |
| 12.0.2.0 | our own builder | covered by existing tests |
| 24.0.0.0 | master es2abc | not yet generated |

## Scattered test matrix (each group = one test file)

| # | Group | Contents | Version targets |
|---|-------|----------|-----------------|
| A | foreign items | foreign class/field/method encode+decode, tagged handles | 12.0.2.0 (builder) |
| B | try/catch | multi-catch, catch-all, nested try, handler code ranges | 12.0.2.0 |
| C | module records | all 5 ModuleTag kinds (regular/namespace/local/indirect/star) | 12.0.2.0 + corpus modules.abc |
| D | annotations | Method/Enum/MethodHandle/nested Annotation/literal-array element/void/string-nullptr + every array tag K..@ | 12.0.2.0 + corpus |
| E | debug info | column table, local vars, params, start_local_extended, source code | 12.0.2.0 |
| F | literal arrays | nested references, every LiteralTag, typed array segments | 12.0.2.0 + corpus |
| G | strings | empty, max ULEB length, embedded NUL, astral plane, MUTF-8 C0 80 | 12.0.2.0 |
| H | malformed | per-item truncation and bad tags for class/method/field/code/debug/annotation/proto/literal/module | any |
| I | protos/signatures | 9/11 shorty read + reference types; 12+/24 assert absence (format fact #A7) | corpus |
| J | isa opcode coverage | every opcode decodes on a 12.0.6.0 corpus (modules.abc full-method disassembly + per-opcode counter assertions) | 12.0.6.0 |

## isa compatibility facts (prerequisite)

- Diff `isa.yaml` 24.0.0.0 against the 4.0/4.1 release copies:
  opcodes added/removed/renumbered, format changes, prefix layout.
  Deliverable: `design/isa-compat.md` with the fact table, and a
  generated "12 file opcodes ⊆ 24 table?" assertion.
- Known so far: 24 added `callthis*withname` (0xdd–0xe1) and the wide
  variants (0x14 prefix); 12 files never contain them. Whether 12 has
  opcodes absent from 24 is unverified.

## Order of execution

1. corpus pipeline + ledger (this commit).
2. `design/isa-compat.md` (12 vs 24 isa.yaml diff).
3. Group J (isa opcode coverage on modules.abc) — first big real-data test.
4. Groups A–I, each test file first (expected red), then fix, then green.
5. Four-version matrix green + 12/24 round-trip + CI.
