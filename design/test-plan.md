# Test plan — isa & file foundation (tests first)

Status: scattered groups A–J delivered and green; corpus pipeline **deferred
by decision** (2026-08) — see "Corpus status" below. Complements
design/vendor-audit.md (§3 findings, §4 compatibility matrix) and
design/ir.md (v0.2 boundary).

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

**Corpus status: deferred.** The upstream source set is identified
(ets_frontend `es2panda/test`: 3252 js/ts files; runtime_core
`libabckit/tests` 242, `static_core/plugins` 134, `disassembler/tests` 74,
`abc2program/tests` 14; upstream also ships a test262 harness with
skiplists), but toolchain availability and source-set choice need a
separate discussion. Until then the repo carries a placeholder pipeline
and the scattered tests carry the load:

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
| 9.0.0.0 | OpenHarmony 3.2 es2abc | deferred |
| 11.0.2.0 | OpenHarmony 4.0 es2abc | deferred |
| 12.0.6.0 | OpenHarmony 4.1 es2abc + modules.abc (device stock, local only) | modules.abc available locally |
| 12.0.2.0 | our own builder | covered by existing tests |
| 24.0.0.0 | master es2abc | deferred |

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
| I | protos/signatures | 12+/24 shorty absence asserted (real corpus + builder); 9/11 shorty *read* needs real 9/11 files | 12.0.6.0 done; 9/11 deferred |
| J | isa opcode coverage | every opcode decodes on a 12.0.6.0 corpus (modules.abc full-method disassembly + per-opcode counter assertions) | 12.0.6.0 |

## isa compatibility facts (delivered)

- Diffed `isa.yaml` 24.0.0.0 against the OpenHarmony 4.0/4.1/5.0 release
  copies. Result: 9.0.0.0, 11.0.2.0, and 12.0.6.0 are all strict subsets
  of 24.0.0.0 with zero opcode renumbering and identical prefixes; 24 only
  adds 9 instructions (callthis*withname, supercallforwardallargs, 2
  sendable). Full table: `design/isa-compat.md`.
- Empirical confirmation: Group J decodes stock modules.abc (12.0.6.0)
  fully with the 24 table — 2,946,777 instructions, zero unknown opcodes.

## Order of execution (as delivered)

1. Groups A–I, each test file first (expected red), then fix, then green:
   A foreign items (533fc95), B try/catch (053e179), C module records
   (c1faf88), D annotations (a0012a7), E debug info (206dbf5), F literal
   arrays (4294de7), G strings (0228fe2), H malformed items (25dafc5);
   I split: 12-side assertion folded into the Group J corpus test.
2. `design/isa-compat.md` — 9/11/12 ⊆ 24 with zero renumbering (2e0008c).
3. Group J opcode coverage on modules.abc, `#[ignore]`d in CI (2e0008c).
4. Full workspace green under CI `RUSTFLAGS="-D warnings"` (39522f7).
5. Deferred (corpus decision): four-version read matrix for 9/11,
   generated-corpus ledger fill-in, corpus build-plan document.
