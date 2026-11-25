# Architecture Decisions & Canonical Invariant Registry

This document is the single authoritative registry of `abcd-rs`'s architectural decisions (`ADR-01`–`ADR-15`), historical `N*` invariant tags referenced in source comments, and retired legacy rulings.

---

## 1. Active Architectural Decisions (`ADR-01` – `ADR-15`)

### ADR-01 — Container-Independent, Dialect-Aware SSA IR
- **Ruling**: `abcd-ir` contains zero `.abc` file offsets, entity pool indices, ULEB immediates, or register-width opcode variants (`N46`, `N52`). At the same time, `Module` / `ClassData` / `FunctionData` explicitly model language dialect and calling-convention semantics (`SourceLang`, dynamic ECMAScript `0.0.0.2` & `9.0.0.0`–`24.0.0.0` vs. static ArkTS 1.2 `0.1.0.7`) so IR consumers never guess calling conventions from missing container annotations.
- **Crates**: `abcd-ir`, `abcd-lift`, `abcd-lower`.

### ADR-02 — Single-Point `Op` Semantics & Derived Effects (`N48`, `N50`)
- **Ruling**: `abcd_ir::Op` is a closed semantic enum (`88` variants). Every pass, verifier rule, expression recoverer, and taint transfer function queries `Op::operands()`, `Op::effects()`, `Op::has_result()`, and `Op::is_terminator()`. Dead-code elimination (`abcd-opt::dce`) derives root liveness strictly from `Op::effects()` (`writes`, `may_throw`, `may_call`), recognizing that `TryGetGlobal` (`ldglobalvar` / `tryldglobalbyname`) invokes prototype getters on slow paths and is **not** pure.
- **Crates**: `abcd-ir`, `abcd-opt`, `abcd-analysis`, `abcd-decompile`.

### ADR-03 — Accumulator-as-Cache Lowering (`B4`)
- **Ruling**: `abcd-lower`'s chordal register allocator assigns a virtual register home to every live SSA value and reserves up to 5 low scratch registers (`v0..v255`) for `lda`/`sta` (`op_v_8`) traffic plus a contiguous low-register call window for `*range` calls (`S2`). The physical accumulator (`acc`) is **never** a register-allocation color; `AccContent` tracks physical accumulator state purely during instruction selection to elide provably redundant `lda` loads.
- **Crates**: `abcd-lower`.

### ADR-04 — First-Class Exceptional CFG & Conservative Handler Joins (`N10`, `N11`, `N13`, `N21`, `N27`, `N38`, `N45`, `N64`)
- **Ruling**:
  1. Every `(protected block → catch handler)` pair is materialized in `Block.preds` as `EdgeKind::Exceptional` alongside structured `TryRegion` tables (`N11`). Reachability for dead-block elimination uses exception-augmented successors so handlers are never swept as dead code, while RPO layout places handlers after normal blocks (`N10`).
  2. Catch handler entry seeds `acc` with `ValueDef::ExceptionParam(handler)` (`N13`, matching VM `SET_ACC(exception)`).
  3. **Zero copies on exception edges (`N21`)**: VM exception dispatch jumps directly to the handler PC without executing edge trampolines; `abcd-lower` coalesces handler-phi incoming slots and rejects any residual exception-edge copy with `LowerError::HandlerEdgeCopies`.
  4. **Dominance & constant propagation (`N27`, `N38`, `N45`, `N64`)**: Cross-block SSA dominance holds over Normal-reachable edges (ignoring unreachable Normal predecessors, `N64`), reachable zero-predecessor phis are invalid (`N27`), and handler phis joining distinct values across exception edges are forced to `Bottom` in `SCCP` (`N38`) because an instruction mid-block may throw before updating a register.
- **Crates**: `abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`, `abcd-analysis`, `abcd-decompile`.

### ADR-05 — Vendored Frame-Slot Calling Convention (`N66`, `N67`)
- **Ruling**: Dynamic ECMAScript functions receive leading implicit parameter slots `[func][new.target][this]` (`H = 3` under the `0xF` default, or the subset declared by `L_ESCallTypeAnnotation;`), followed by explicit source formals at `params[H..]`. `ldthis` binds to the `this`-role parameter slot (`N67`). Static ArkTS methods (`SourceLang::ArkTs` / static ABI) carry `H = 0` implicit JS slots (`abcd_ir::frame`).
- **Crates**: `abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-analysis`, `abcd-taint`, `abcd-decompile`.

### ADR-06 — Vendor Operand Order & ECMA-262 Numeric Semantics (`N36`–`N42`, `N65`, `N68`, `N72-C4`)
- **Ruling**:
  - `Op::BinaryOp` and `Op::Compare` store `left = acc, right = vreg`, whereas ArkCompiler `*2` opcodes evaluate `vreg OP acc` (`right OP left` in IR field names, `N36`); constant folders (`abcd-opt`) and expression recovery (`abcd-decompile`) swap accordingly.
  - Constant folding preserves `-0.0` sign bits (`N37`, never emitting `ldai 0` for `-0.0`), never coerces `null`/`undefined` to `0.0` in comparisons (`N38`/`N41`), maps `Bytecode::Not` to bitwise `~` (`UnOp::BitNot`, `N39`), evaluates `===` on `f64` via IEEE-754 equality (`NaN !== NaN`, `-0.0 === +0.0`, `N40`), and wraps bitwise/shift operands with ECMA-262 `ToInt32`/`ToUint32` (`N42`).
  - Opcode-distinct runtime semantics stay distinct in IR: `DeleteProp` (`v0=obj, acc=key`, `N65`), `StoreOwnProp*` vs. `StoreProp` (`N60`), `TryStoreGlobal` vs. `StoreGlobal` vs. lexical `StoreGlobalRecord` (`N61`, `N72-C4`), `DefineSendableClass` vs. `DefineClass` (`N53`), `CallKind::{Apply, SuperSpread, SuperForwardAllArgs}` (`N57`, `N58`), `AllocArray` vs. `AllocObject` (`N59`), and accumulator-carried `AwaitUncaught`/`AsyncResolve`/`AsyncReject` (`N68`).
- **Crates**: `abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`, `abcd-decompile`.

### ADR-07 — Hard-Error Boundary for Unimplemented Upstream Opcodes (`N51`, Fused Branches)
- **Ruling**: Only opcodes that have **zero upstream VM semantics and zero compiler producers** are rejected with `LiftError`:
  1. `ldthisbyname` / `stthisbyname` / `ldthisbyvalue` / `stthisbyvalue` (`LiftError::UnsupportedThisByAccess`, `N51` — never emitted by `es2panda`, zero occurrences across corpus and wild apps).
  2. The 14 fused compare-and-branch opcodes (`jeq*`, `jne*`, `jstricteq*`, `jnstricteq*`, `jeqnull*`, `jequndefined*`, `jstricteqz*` — `LiftError::UnsupportedFusedCompareBranch`; `isa.yaml` specifies `pc += imm` with no comparison, the C++ interpreter `FATAL`s all 24 widths, and the assembly interpreter `NOP`-skips them). `abcd-lower` exclusively emits unfused `cmp + jnez`/`jeqz`.
  3. Super-property access by integer index (`LiftError::UnsupportedSuperByIndex` — no opcode exists in `isa.yaml`).
- **Crates**: `abcd-lift`, `abcd-lower`.

### ADR-08 — Full Read/Lift/Analyze/Decompile Support for Legacy `0.0.0.2` Bytecode
- **Ruling**: `abcd-isa::decode_legacy` translates OpenHarmony 3.2/4.0 (`0.0.0.2`, API 9 pre-freeze) opcodes into `Bytecode::Deprecated*` variants, and `abcd-lift` lifts every legacy opcode—including `deprecated.defineclasswithbuffer` (`v1 = lexenv`, `v2 = proto` per `interpreter_assembly.cpp:4624-4648`)—into canonical `abcd-ir`, unlocking `abcd info`, `dis`, `decompile`, `analyze`, and `taint` on 100% of wild legacy `.hap` packages. Because upstream `libpandafile`'s writer only targets modern format versions (`9.0.0.0`+), `abcd_file::encode` returns `Error::UnsupportedOutputVersion(0.0.0.2)` when asked to emit raw `0.0.0.2` bytes directly.
- **Crates**: `abcd-isa`, `abcd-file`, `abcd-lift`.

### ADR-09 — Dual-Bucket Lossless MUTF-8 Strings & Content-Keyed Literal Dedup (`N62`, `N72`, `N75`, `D3`)
- **Ruling**:
  - `abcd_file::StringPool` and `abcd_ir::SymbolTable` normalize both 6-byte CESU-8 (`es2abc`/`ets2panda` surrogate pairs) and 4-byte UTF-8 astral sequences (plus `C0 80` NUL) into deduplicated `Arc<str>` UTF-8 entries, reserving the raw-bytes side bucket (`RawMutf8`, `N72`) strictly for unpaired UTF-16 lone surrogates or ill-formed wire sequences (rendered as `\uXXXX` escapes by `abcd-decompile`, `N75`).
  - On emission (`encode` and `pandasm`), all lossless strings serialize through a single unified MUTF-8 encoder (`es2abc`-canonical 6-byte CESU-8 for `U+10000..=U+10FFFF`, `C0 80` for `U+0000`, and a zero-allocation `Cow::Borrowed` slice fast path for ASCII/BMP strings without `0x00`), achieving 100% byte-identity with `es2abc` and `ark_disasm`.
  - During IR lowering/rewriting, identical `LiteralArray` shapes deduplicate by structural content (`N62`), an intentional size-reducing equivalence verified by the `ark_js_vm` oracle.
- **Crates**: `abcd-file`, `abcd-ir`, `abcd-lift`, `abcd-lower`, `abcd-decompile`.

### ADR-10 — Structural Container Relocation & Per-Method `u16` Entity Compaction (`N55`, `N56`, `N71`, `N73`, `#32`, `#38`)
- **Ruling**:
  - Every offset-bearing `Type::U32` field emitted by `es2abc` (`_ESModuleRecord` / `moduleRecordIdx`, `moduleRequestPhaseIdx` `N56`, `_ESScopeNamesRecord` / `scopeNames`, `typeSummaryOffset`, and `jsonFileContent`), every nested `LiteralValue::LiteralArray` inside class/method/annotation literal arrays, and all 8/16/32/64-bit annotation scalar & array elements are decoded structurally and relocated via two-pass `Builder` handles on `encode`.
  - Corrupted debug-info line programs fail loudly with `Error::DebugInfoExtraction` (`N55`) rather than silently dropping a file's debug region.
  - `abcd-lower` assigns 8-bit IC slots before 16-bit slots (`N71`), records recomputed `MethodBody::ic_size` so `encode` updates `_ESSlotNumberAnnotation` (`N73`, preventing VM `SIGSEGV`), and compacts module-wide `u32` entity IDs into per-method `u16` index slots (`LowerError::EntityIndexOverflow` only if a single method exceeds `65,536` distinct entities of one kind).
- **Crates**: `abcd-file-sys`, `abcd-file`, `abcd-lower`.

### ADR-11 — `pandasm` Disassembly & Assembly Fidelity (`q-P8`, `N84`)
- **Ruling**: `abcd dis` (`abcd_file::pandasm::emit_file`) is gated per-push to be **byte-for-byte identical** to upstream `ark_disasm` across all `5,517` corpus fixtures (`scripts/pandasm-dis-divergences.json` = 0 rows), faithfully reproducing upstream record ordering, float formatting (`N84`), and raw MUTF-8 bytes. `abcd asm` (`pandasm::parse_file`) round-trips binary semantics across `5,517/5,517` fixtures.
- **Crates**: `abcd-file`, `abcd-cli`.

### ADR-12 — Binary-Only Global Allocator Policy
- **Ruling**: `abcd-cli` sets `mimalloc` (`#[global_allocator]`) across target platforms for fast multi-threaded arena allocation on macOS, Windows MSVC, and Linux; library crates never install a global allocator. Arena page-purge tuning or platform-specific allocator adjustments are governed by empirical multi-module RSS benchmarks (`#33`).
- **Crates**: `abcd-cli`.

### ADR-13 — Pure-Rust Table-Driven Modern ISA Codec & Fenwick Branch Relaxation (`D1`, `#43`, `#47`)
- **Ruling**: Modern `9.0.0.0`–`24.0.0.0` `abcd_isa::decode`, `relocate_entity_id`, and `encode` run in 100% Safe Rust over `isa.yaml`-generated tables (`abcd-isa-sys/src/generated/`), using deterministic (`N20`) `O(N + J log N)` Fenwick-tree branch relaxation and inverted-branch + `jmp.32` trampolines across all 17 jump mnemonics when displacements exceed `±32 KiB`. Vendored C++ `BytecodeInst` and `BytecodeEmitter` in `isa_bridge.cpp` are retained strictly as automated differential test oracles.
- **Crates**: `abcd-isa-sys`, `abcd-isa`.

### ADR-14 — Pure-Rust Bounded LNP Decoder, Opt-In `EncodeOptions` Verification & Explicit `Dialect` (`D2`, `D4`, `D6`, `#44`, `#47`)
- **Ruling**:
  1. Both `abcd_file::decode` and `inspect_summary` extract method debug info and line/column/local-variable tables through a single bounded pure-Rust DWARF/LNP state machine over `&data[..size]` (retaining C++ `DebugInfoExtractor` solely as a differential test oracle), and `encode` commits every `line_table` row via `EmitSpecialOpcode` (`R1-H1`).
  2. `abcd_file::encode` defaults to `EncodeOptions { verify: false }` so production rewrites do not pay a redundant full re-decode pass, while `encode_with_options(file, EncodeOptions { verify: true })` provides built-in round-trip verification (`D4`).
  3. Container dialect is modeled explicitly via `Dialect::{DynamicModern, DynamicLegacy, Static}` (`D6`), preventing `0.1.0.x` static ArkTS 1.2 containers from falling into dynamic `24.0.0.0` ISA decoders or `version <= 12.0.6.0` header-literal heuristics; full pure-Rust `.abc` container reading (#49) and cross-layer `EntityRef` offset decoupling (#50) are tracked separately.
- **Crates**: `abcd-file-sys`, `abcd-file`.

### ADR-15 — Mandatory IEEE CRC-32 & Decompression-Bomb `Limits` in `abcd-hap` (`D5`, `#46`)
- **Ruling**: `abcd-hap` verifies pure-Rust IEEE 802.3 CRC-32 (`Error::CrcMismatch`) on every `STORED` and `DEFLATE` entry read, enforces configurable per-entry and cumulative decompression `Limits` (`512 MiB` / `2 GiB` defaults plus RFC 1951 `1032×` DEFLATE ratio pre-checks) prior to allocation, skips resource-only nested `.hap`/`.hsp` siblings inside `.app` bundles cleanly, and bounds EOCD candidate walks (`MAX_EOCD_CANDIDATES = 64`).
- **Crates**: `abcd-hap`.

---

## 2. Quick Lookup of Code-Referenced `N*` Tags

| Tag | Summary |
| :--- | :--- |
| `S1` / `N2` | Method identity is file `method_offset` → `FuncId`, never method name string |
| `S2` | Reserved low-register (`v0..v255`) range-call window + 5-slot `lda`/`sta` scratch block |
| `B4` | Accumulator-as-cache (`AccContent`) replacing register-coloring of `acc` |
| `N10` / `N11` / `N18` | RPO places catch handlers after entry; DCE/reachability uses exception-augmented CFG |
| `N13` / `N21` | Catch entry seeds `acc` with `ExceptionParam`; zero phi copies permitted on exception edges |
| `N15` / `N53` | Class `.length` (`count`) preserved; `DefineSendableClass` kept distinct from `DefineClass` |
| `N20` | Bit-exact determinism across hash seeds, runs, and platforms |
| `N23` / `N27` | Branch folding prunes dead phi inputs; zero-predecessor phis on reachable blocks are verifier errors |
| `N36`–`N42` | Vendor `vreg OP acc` order (`N36`), `-0.0` bits (`N37`), handler-phi `Bottom` & nullish `==` (`N38`/`N41`), bitwise `not` (`N39`), IEEE `===` (`N40`), modular `ToInt32` (`N42`) |
| `N45` / `N64` | Normal-edge SSA dominance check excluding unreachable Normal predecessors |
| `N46` / `N52` | IR stores table-local `ClassId`/`ConstId`/`FuncId`/`Sym`, never raw file offsets |
| `N48` / `N50` | `Op::effects()` single source of truth; `TryGetGlobal` may invoke getters and throw |
| `N51` | `ldthisby*` / `stthisby*` rejected with `LiftError::UnsupportedThisByAccess` |
| `N55` / `N56` | Loud `DebugInfoExtraction` error on corrupt LNP; `moduleRequestPhaseIdx` guard before `_ESModuleRecord` |
| `N57`–`N61` | Distinct `CallKind::{Apply, SuperSpread, SuperForwardAllArgs}`, `AllocArray`, `StoreOwnProp*`, `TryStoreGlobal` |
| `N62` | Accepted content-keyed `LiteralArray` deduplication during rewrite |
| `N65` | `delobjprop` operand roles: `v0 = object`, `acc = key` |
| `N66` / `N67` | Vendored `[func][new.target][this]` frame-slot convention (`abcd_ir::frame`) |
| `N68`–`N70` | Async `acc` value modeling + `async`/`for await..of` state-machine folds |
| `N71` / `N73` | 8-bit-first IC slot assignment + `_ESSlotNumberAnnotation` sync on `encode` |
| `N72` / `N75` | Lossless lone-surrogate MUTF-8 side table + `\uXXXX` decompiler escaping |
| `N74` / `N76`–`N80` | `test262` & wild-corpus decompiler structuring, `late_decl_fold`, tower de-absorption, loop-cut `try`, `effective_kind` async detection |
| `N81` / `N83` | C++ bridge prefix+span bounded string reads (`N81`) and payload-clamped array counts (`N83`) |
| `N82` | Inliner pre-validates block-terminal calls before mutating caller CFG |
| `N84` | `pandasm` `%g` float formatter strips trailing zeros only when a decimal point is present |

---

## 3. Retired & Overturned Historical Workarounds

The following early K3 hard-error rulings were overturned after upstream verification and root-cause fixes:

1. **`NestedLiteralArrayInAnnotation` (`c-COV W5`, overturned in `#32`)**: Previously blamed the vendored C++ writer and rejected nested `LiteralValue::LiteralArray` inside annotations; fixed via two-pass `LiteralArray` handle creation in `abcd-file::encode`.
2. **`Error::TypeSummaryOffset` (`N8`, overturned in `#38`)**: Previously stored `typeSummaryOffset` opaquely and refused `encode` on 77 wild OHOS apps; replaced by structural `FieldValue::LiteralArrayRef` decoding and nested literal-array relocation.
3. **`LiftError::UnsupportedDeprecatedDefineClassWithBuffer` (`N54`, overturned in `#38`)**: Previously blocked `lift`/`decompile`/`analyze`/`taint` on 20 legacy OHOS 3.2/4.0 modules; replaced by vendor-grounded `Op::DefineClass` lifting (`v1 = lexenv`, `v2 = proto`).
4. **`Error::UnsupportedAnnotationArrayType` (overturned in `#38`)**: Previously rejected 64-bit (`I64`/`U64`/`F64`) annotation array elements on `encode`; fixed by widening `AbcAnnotationElemDefEx` across `abcd-file-sys` and `abcd-file`.
5. **Raw `std::cerr` `logger.h` Shim & `scripts/remote-test.sh` (`dabai` + local Docker, retired in `#38`)**: Replaced by silent non-fatal C++ logging + exception-throwing `LOG(FATAL)` in `vendor/shim/utils/logger.h`, zero-OrbStack `./scripts/test-local.sh`, and full-workspace cross-platform CI.
