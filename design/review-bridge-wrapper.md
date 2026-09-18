# Quality Review: bridge & wrapper layers (Phase 0)

Scope: `abcd-isa-sys` / `abcd-isa` / `abcd-file-sys` / `abcd-file` — the FFI
bridge and safe wrapper layers. Vendor files themselves are out of scope
(zero-diff contract), but vendor behavior reachable through our bridge is in
scope.

Method: 4 parallel read-only audit workers (kimi-coding/k3) covering (A)
isa-sys+isa, (B) file-sys bridge, (C) abcd-file wrapper, (D) cross-cutting
mechanical checks. **Every finding below was independently re-verified by the
orchestrator against the code**; the four P0 input-handling claims were
additionally proven at runtime with `abcd-isa/examples/audit_probe.rs`
(kept in-tree as evidence).

Severity: **P0** correctness/safety (abort, UB, silent data corruption,
data-path panic) · **P1** rule violation (hand mirrors, layering, missing
guards, sentinel contract) or material doc-vs-code mismatch · **P2** design
quality / dead code / test gaps.

Status: `open` = reported, awaiting maintainer triage.

## Summary

| Severity | Count | Headline |
|----------|-------|----------|
| P0 | 10 | input-driven abort, silent truncation, OOB read, silent data loss ×5, data-path panic |
| P1 | 22 | isa bridge 0/59 guards, builder family ~76 unguarded, unpinned hand tables, sentinel contracts, layering |
| P2 | ~40 | dead FFI surface (108/324), doc drift, test gaps, robustness residue |

Runtime probe evidence (`cargo run -p abcd-isa --example audit_probe --offline <mode>`):

| Probe | Result |
|-------|--------|
| `invalid-opcode` (`decode(&[0xE2])`) | **exit 134 (SIGABRT)** "This line should be unreachable" — finding #1 confirmed |
| `invalid-prefixed` (`decode(&[0xFB,0xFF])`) | **exit 134 (SIGABRT)** — finding #1 confirmed on prefixed path |
| `emit-drop` (`encode(Ldlexvar(Imm(300), Imm(0)))`) | returned `Ok` with operand **silently truncated to 44** — finding #2 confirmed |

---

## P0 findings

### 1 (P0) — decode aborts the process on unassigned opcodes

`abcd-isa/src/decoder.rs:51` calls `isa_get_size_by_opcode` → vendor
`GetFormat(Opcode)` whose `default:` falls into `UNREACHABLE()`
(vendor template `bytecode_instruction-inl_gen.h.erb:414-425`). Under
`-DNDEBUG` (build.rs:95) `UNREACHABLE()` = `std::cerr + std::abort()`
(vendor macros.h:135-142,223). Any byte 0xE2–0xFA, or a prefix byte with an
unassigned sub-opcode, kills the process. Consequences:

- `DecodeError::InvalidOpcode` is **unreachable code** (decoder.rs:52,62):
  `Size` never returns 0 for a valid opcode, and an opcode that reaches
  `decode_one` always matches.
- `abcd-file` decodes untrusted `.abc` through this path → real DoS.
- Existing test `decode_errors.rs:9-22` is named `decode_invalid_opcode` but
  actually exercises `Truncated`; a true invalid-opcode test cannot be
  written today because it would abort the test process.

Runtime proof: probes above, both paths exit 134.
Fix: bridge pre-validates before calling `GetFormat` — primary byte via
`isa_is_primary_opcode_valid` and sub-opcode against the vendored
`isa_information.last_*_opcode_idx` ranges — returning 0 size for invalid
(reviving `DecodeError::InvalidOpcode`); alternatively add a non-aborting
lookup to the bridge. Add regression tests for 0xE2 and `[0xFB,0xFF]`.

### 2 (P0) — encode silently truncates out-of-range operands at the FFI dispatch

`isa_emitter_emit` dispatch (generated from
`templates/isa_bridge_emit_dispatch.h.erb`) casts each `int64_t` arg to the
storage width (`static_cast<uint8_t/uint16_t>`) before calling the vendor
emitter, so an out-of-range operand is **truncated, not rejected**. The
"no matching format → silent drop" branch in the generated emitter is
unreachable in practice (the truncated value always fits the widest format).
`encode()` returns `Ok` with corrupted bytecode.

Runtime proof: `Ldlexvar(Imm(300), Imm(0))` encodes as `Ldlexvar(Imm(44), Imm(0))` (300 & 0xFF), `Ok` returned. Register operands share the same cast path.
Fix: Rust-side range validation in `emit_args`/dispatch generation (compare
against each mnemonic's max operand width from isa.yaml) and/or make the
dispatch return a new error code on truncation; add `EncodeError::OperandOutOfRange`
plus regression tests. Related hardening: `emitter.rs:132-141` offsets scan
silently `break`s on size==0 — assert `offsets.len() == instructions.len()`.

### 3 (P0) — `abc_file_open` never checks `header->file_size ≤ len`

`file_bridge.cpp:391-421` validates magic only. The bridge's own
`ValidateChecksum` (:197-207) computes `adler32` over `file_size` bytes;
vendor `Span`s are constructed from the declared `file_size`
(vendor file.h:186-216) and `Span::SubSpan` bounds-checks only via ASSERT
(vendor span.h:178-189), which `-DNDEBUG` removes. A header declaring
`file_size = 4GB` makes class-index reads walk past the `len+16` padded
buffer — heap OOB read on malformed input. Note the bridge already has the
correct check elsewhere (`GetFileType`, :254 `actual_size != header->file_size`)
— it was never applied on open (review-isa-file #7 added magic validation
only).
Fix: reject `file_size > len` in `abc_file_open` (distinct `g_open_error`
reason); optionally add a one-time header section-bounds sanity check.
Regression test: header with inflated `file_size` must fail open, not crash.

### 4 (P0) — tolerant literal enumerator silently drops typed-array values

`file_bridge.cpp:1886-1900`: the `ARRAY_U1…ARRAY_STRING` case sets `out` and
`return`s **without calling `cb`** — while vendor
(`literal_data_accessor-inl.h:94-115`) delivers one value (the array-data
offset) and then stops. Every typed-array literal decodes to nothing: silent
data loss on real static/ArkTS content. No test covers ARRAY_* decode
(Group F covered scalars only).
Fix: call `cb(&out, ctx)` before the `return`; add a typed-array literal
regression test.

### 5 (P0) — `encode_debug_info` collapses local-variable scopes

`abcd-file/src/encode.rs:1816-1828`: `lv.start`/`lv.end` are never used;
each local is emitted as `start_local` immediately followed by `end_local`
at the current LNP position. The decode side carefully converts byte offsets
to instruction indices (decode.rs:1383-1386) and `tests/debug_info.rs:90`
asserts `end != start` — the data exists and is destroyed on write-back.
No roundtrip test covers local vars (roundtrip.rs builds only a line table).
Fix: `advance_pc` to `index_to_offset(lv.start)` before `start_local`, and
to `lv.end` before `end_local`; add local-var scope roundtrip test.

### 6 (P0) — unresolvable annotation references silently encode as `Scalar(0)`

`abcd-file/src/encode.rs:1484-1496,1529`: when a Method/Enum/MethodHandle
annotation reference cannot be resolved to a builder handle, the encoder
writes `(b'E'|b'F'|b'J', Scalar(0))`. Foreign members are never in
`EntityHandles` (decode surfaces foreign classes as empty shells;
`tests/foreign_items.rs:30-38` pins that foreign items are not class
members), so an annotation referencing a foreign field/method — a pattern
the test suite itself builds — silently corrupts on roundtrip, and the
final readback validation (encode.rs:1321) cannot catch it (0 decodes fine).
Same disease in the literal-array path (encode.rs:1846-1890): unresolvable
Method/Getter/Setter falls back to writing the **source file offset** into
the new file's different layout.
Fix: make these paths return `Error` (no silent fallbacks); long-term the
model needs foreign-member entities.

### 7 (P0) — entity annotation array elements (`X/Y/Z/@`) encode as 0

`abcd-file/src/encode.rs:1607`: `annotation_array_elem_to_handle`'s
`_ => 0` arm receives `Method{..}`/`Enum{..}`/`Annotation`/`MethodHandle`
values (produced by decode for `ArrayMethod`/`ArrayEnum`/`ArrayAnnotation`/
`ArrayMethodHandle` elements) and writes 0 for each.
`tests/annotation_all_types.rs:195-216` has decode-only coverage, so the
loss is invisible today.
Fix: resolve each element through `entities` and emit `EntityArray`;
error on failure. Same root as #6.

### 8 (P0) — nested literal-array references use model indices as builder handles

`abcd-file/src/encode.rs:1691,1940`: `LiteralValue::LiteralArray(idx)` is
encoded via `LiteralArrayHandle(idx.0)`. But annotation-embedded literal
arrays (`ann_la_*`, created during class configuration, :1532-1539) consume
the low handle numbers **before** `literal_handles` is created (:1251), so
whenever `ann_la_counter > 0` every nested reference points at the wrong
array. Orchestrator-verified against creation order.
Fix: resolve through `literal_handles[idx.0]` in both
`encode_literal_value` and `encode_literal_value_simple`; add a roundtrip
test with annotation-embedded LA + nested LA coexisting.

### 9 (P0) — `CString::new(...).expect` panics on embedded-NUL strings

`abcd-file/src/encode.rs:138` and ~9 more sites (:118,146,152,244,268,310,
331,346,415): strings decoded from MUTF-8 can legitimately contain U+0000
(encoded `C0 80`; `tests/string_boundaries.rs:96` proves decode produces
`"a\0b"`). Re-encoding such a file panics on the data path. All string tests
are decode-only, so this was never exercised.
Fix: bridge gains a (ptr,len) string API, or Rust converts UTF-8 → MUTF-8
before calling; at minimum replace `expect` with `Error`. Regression:
decode→encode a method named `"a\0b"`.

### 10 (P0) — `abc_annotation_array_read` writes past the stack value for unchecked `element_size`

`file_bridge.cpp:2156`: `memcpy(&val, elem.data(), element_size)` into an
8-byte `uint64_t`; header documents 1/2/4/8 but nothing enforces it. C-ABI
footgun — **not reachable from the safe Rust layer** (sizes are computed
internally as 1/2/4/8), so downgraded to P1 in remediation priority but
listed here for completeness of the input-safety picture.
Fix: whitelist-check `element_size` at entry; also drop or use the decoded
ULEB count `cnt` (:2147, currently unused).

---

## P1 findings

### 11 (P1) — `isa_bridge.cpp`: zero exception guards on all ~40 entry points

Mechanically verified: no `try`/`catch` in the file. Allocation paths
(`isa_emitter_create/:329`, `create_label/:339`, `build/:350-364`,
`isa_format_*`/:167-205 `ostringstream`, `isa_get_version_by_api_sub`/:321
`std::string`) can throw `bad_alloc` across the FFI → terminate. Rule:
every `extern "C"` entry must convert exceptions to sentinels.
Fix: wrap every entry (macro like the file bridge's pattern).

### 12 (P1) — `file_bridge.cpp`: the whole `abc_builder_*` write family (~76 functions) is unguarded

Read side (~189 functions) has guards; builder side only
`set_file_version`/:2489, `relocate_code_id`/:3400,
`finalize_with_code_ids`/:3441 do. `CreateItem`/`ComputeLayout`/
`DeduplicateItems` allocate (bad_alloc) and can reach vendor `UNREACHABLE`
(e.g. `IndexItem::GetItemType`, vendor file_item_container.cpp:1059) →
abort. `abc_builder_finalize` delegates to the guarded
`finalize_with_code_ids` — **ruling: acceptable as-is** (no form-only guard
needed).
Fix: wrap the family; regression: malformed builder usage must return
failure, not abort.

### 13 (P1) — tolerant enumerator's tag→width table is an unpinned hand mirror

`file_bridge.cpp:1832-1902`: values verified **correct** against vendored
`LiteralTag` (literal_data_accessor.h:33-66), but none of the file's
`static_assert`s reference `LiteralTag` — an upstream renumber compiles
clean and corrupts silently. Violates "mirrors must be compile-time pinned".
Fix: one `static_assert` per case value.

### 14 (P1) — sentinel contract violations

- `abc_method_get_name_utf16` (file_bridge.cpp:1383-1395) returns 0 for
  failure **and** for a valid empty name; the UTF-16 convention is
  `SIZE_MAX`=failure (see :516-529). Header silent.
- ISA version APIs use `0=success/1=not found` (isa_bridge.h:142-143,157-158)
  — a third convention beside `SIZE_MAX` and `-1`.
- `abc_is_version_less_or_equal`/`abc_contains_literal_array_in_header`
  return `-1` on exception while headers document 1/0 — in C, `-1` is true.
- `abcd-file/src/file.rs:9` `ABSENT = u32::MAX` hand-mirrors the bridge
  sentinel without a source comment, and many sites use raw `u32::MAX`
  literals instead (encode.rs:394,1113,1518,1525; decode.rs:693,1575).

### 15 (P1) — callback early-stop contract is broken

`int`-returning callbacks imply early stop, but only the debug family
honors it (:2213,2228,2247,2278,2289). All 12 annotation enumeration
sites, `enumerate_interfaces`(:998), `enumerate_types_in_proto`(:1251), and
`enumerate_try_blocks_full`(:1492) discard the return — including one
typedef (`AbcEntityIdCb`) with both behaviors. README.md:103 claims a
uniform convention. Headers document neither. Rust today never relies on
early stop (collect-all), so this is contract debt, not live corruption.

### 16 (P1) — layering violations in the safe wrapper

- `decode.rs:551-578` `resolve_foreign_entity_name` reads `off+4` raw bytes
  ("foreign item name_off lives at item+4") — format layout knowledge that
  belongs in the bridge; and the `off + 4` itself is unchecked (overflow →
  debug panic / release wraparound) — `read_u32_at`'s internal check can't
  help because the addition already happened (:570).
- `decode.rs:1471-1482` `read_class_name` uses the raw-byte
  `abc_class_get_name` + `to_string_lossy` (astral/NUL corrupt) while
  `read_method_name` uses the lossless UTF-16 path and the class descriptor
  is already read losslessly via `read_string(f, class_id)`.
  Fix: use `read_string(f, class_id)` or add `abc_class_get_name_utf16`.
- `file.rs:20-22` `unsafe impl Send/Sync for AbcFile` — justification
  ("read-only after open") doesn't hold (accessors are stateful cursors,
  see decode.rs:677-730 workaround) and nothing needs the impls
  (crate-private, single-threaded decode). Fix: delete.

### 17 (P1) — param annotations are undecodable

Bridge exposes `abc_method_get_param_annotation_id`/
`get_runtime_param_annotation_id` (file_bridge.h:216-217); the Builder has 8
`method_param_add_*` APIs; the model and decode have **nothing** (grep: zero
callers). Files carrying param annotations lose them on roundtrip.
Fix: extend the model (param-level annotations) or declare the limitation.

### 18 (P1) — data-path panics beyond finding #9

- `encode.rs:977,1017,1621,2028` — 4× `expect("dangling StringId")` on a
  fully-`pub` model (hand-built models can mix pools).
- `encode.rs:1592-1598` — `panic!` on I64/U64/F64 annotation array
  elements (preflight exists but the error path is untested; conversion
  should be a single `Result` path).

### 19 (P1) — hand mirrors in the Rust layer (rule: reference, don't copy)

- `abcd-isa/src/emitter.rs:7` `ISA_EMIT_UNKNOWN_OPCODE = -3` (bindgen
  exports the same constant; also raw `0` literals at :108/:119).
- `abcd-file/src/encode.rs:1465-1542` hand-written annotation tag chars
  (`b'1'…b'#'`) — `abcd-file-sys::AnnotationValueType` discriminants exist.
- `abcd-file/src/annotation.rs:11-21` `MethodHandleType` mirrors vendor
  `enum class MethodHandleType` (file_items.h:1749-1759) — not exported by
  bindgen, unpinned.
- (acceptable-but-weak) `abcd-file-sys/src/lib.rs` `AnnotationValueType`
  mirror — pinned transitively by the C++ static_asserts; add a comment
  stating the dependency.

### 20 (P1) — `abcd-isa-sys/README.md` is wholesale stale (19 confirmed items)

Nonexistent templates (`isa_bridge_tables.h.erb`, `isa_bridge_emitter{,_decl}.h.erb`),
removed mechanisms (`links`, `DEP_ISA_BRIDGE_BINDINGS_RS`, `ISA_*_TABLE`
static tables, 326 per-mnemonic emit functions), nonexistent APIs
(`isa_decode_index`, `isa_prefix_count`, `isa_prefix_opcode_at`,
`isa_is_id_match_flag`, wrong `isa_is_range/is_suspend` signatures, wrong
`void isa_emitter_bind`), wrong counts (230+102 → real 226+106; "22 vendor
files" → 23; "3 shims" → 5; "2 C++ sources" → 3; "8 headers" → 7+1),
self-contradictory opcode ranges (0xDC vs 0xE1). The real templates
(`bytecode.rs.erb`, `isa_bridge_emit_dispatch.h.erb`) are never mentioned.
Fix: rewrite the README from current build.rs/isa_bridge.h.
Companion: `abcd-file-sys/README.md` claims a `links` key (absent) and is
internally inconsistent on shim count (9 vs actual 10); its "Literal Value
Conversion" section describes the dead `literal_val_to_c`.

### 21 (P1) — logger shim silently weakens `LOG(FATAL)` without documentation

`bridge/shim/utils/logger.h:16-18`: `LOG(FATAL)` = `std::cerr` (not abort).
Vendor FATAL sites (`line_number_program.h:170`, `debug_info_extractor.cpp:119`)
thus print-and-continue. This is intentional (vendor-audit #A4) but
`abcd-file-sys/README.md:28` calls it "LOG macro → no-op" and the
"Comparison" section never mentions the semantic change. Re-arming risk on
future vendor sync must stay documented.

### 22 (P1) — cross-crate duplicate vendor files have no CI consistency protection

14 byte-identical duplicates (isa.yaml, isapi.rb, gen.rb, pandafile_isapi.rb,
file_format_version.{h.erb,cpp}, 8 libpandabase headers) — verified
identical today, but `common-files-consistency` only diffs `vendor-sync.rb`
+ 3 shims, and the daily sync updates each crate independently → drift
window. Fix: extend the CI job to the full duplicate list.
Related: both bridges compile the same `file_format_version.cpp` and expose
overlapping version APIs (abc side's 4 version helpers are dead in-repo) —
policy decision: keep the duplication (crates are independent units) or
extract.

### 23 (P1) — assorted missing bounds checks in the bridge

- `abc_class_get_interface_id` (:987-993) — idx unchecked (vendor ASSERT-only).
- literal by-index trio (:1917-1950) — `get_array_id`/`get_vals_num_by_index`/
  `enumerate_vals_by_index` unchecked, while `abc_literal_resolve_index`
  (:1955) does check.
- `abc_method_handle_read` (:2167-2185) — `sp.Size() < 6` rejects a legal
  2-byte handle at file end; `type` 0-8 not validated.
- `resolve_entity_by_tag` fallback (:3159-3163,3171-3173) — contradicts its
  own #B1 comment ("never fall back to raw handle indices"): failed entity
  resolution writes the raw handle as a scalar.

---

## P2 findings (condensed; full evidence in worker reports)

**Robustness/semantics**
- LNP parser (`line_number_program.h:200-204`) reads unbounded until
  `END_SEQUENCE`; truncated LNP yields garbage rows — bounded in practice by
  the 16-byte open padding, so P2 with a note that finding #3 must be fixed
  first. No upstream length guarantee exists (debug_data_accessor-inl.h:67-73).
- `abc_builder_finalize` twice on one builder duplicates literal items and
  re-applies code relocations (`literal_items_staging`/`code_id_relocations`
  never cleared; `lnp_staging` is — inconsistent).
- `component_type_from_tag` default silently maps unknown tags to U32;
  builder accepts any annotation tag char unchecked.
- `CheckFileVersion` stub is no-op; unsupported versions pass silently.
- `for_api_sub` on unknown API returns `Some(current)` (upstream default
  branch), inconsistent with `for_api`'s `None`; doc understates it; test
  only asserts no-panic.
- `isa_format_instruction` reads `bytes[1]` before length check on a
  1-byte prefixed buffer (latent; currently uncalled).
- `inst_from_opcode` `buf[16]` has no `static_assert` against the max
  format size (currently 11 bytes — fine).
- `decode.rs` `c.type_idx as u16` truncates malformed catch indices;
  try-block `start` OOB maps to byte 0 (`unwrap_or(0)`); AVT `Array('H')`
  elements decode to empty (unverified whether vendor emits `'H'`).
- `module.rs` ignores phase records (NeedEmitPhaseRecord INTEGER_8 side
  array) — model limitation, undocumented.
- `decode_literal_arrays` opens one accessor at `offsets[0]` — if that open
  fails, all arrays silently decode empty; nested references to off-table
  arrays keep raw offsets (model promises table indices).
- `abc_debug_info_open` failure silently turns all debug info into `None`;
  annotation element read failures silently drop elements.
- `EntityHandles::resolve_*` falls back to name lookup on unknown non-zero
  offset (can bind the wrong same-named method).
- `decode.rs:231-235` `matches!` filter is currently exhaustive-by-construction
  (keep as forward guard, comment it); `decode_proto_types` dead `strings`
  param; `file.rs:31` `CStr::from_ptr` without null check; `file.rs:73`
  `data.len() as i32` truncation >2GiB.
- `Type::from_descriptor` missing `"void"` (Display/parse asymmetry) and
  hand-mirrors the pandasm primitive table without a source comment.

**Dead surface (orchestrator-corrected counts)**
- 108/324 in-repo-unused exports: isa 25 (bytes-based classification family,
  `isa_format_*`, `isa_get_imm_count`, `isa_get_literal_index`,
  `isa_get_last_vreg`, `isa_get_range_last_reg_idx`, `isa_is_id_*`,
  `isa_get_api_version_count`, …), abc 83 (incl. the whole `abc_module_*`
  family, 4 dead version helpers, `*_static` quick-access family,
  annotation-count getters, `abc_builder_literal_array_add_f32/f64`).
  Worker D's raw list had 14 function-pointer false positives (the
  `collect_offsets_*` family) — corrected here. **Ruling**: crates are
  publish-shaped; in-repo-unused ≠ deletable. Treat as a public-surface
  policy decision, not a cleanup task.
- `literal_val_to_c` (file_bridge.cpp:1776) is genuinely dead — delete.

**Docs/tests hygiene**
- `abcd-file/README.md`: 6 material drifts (classes key type,
  `type_descriptor` field, AnnotationValue variant shapes, Known-Limitations
  contradicting the implementation, re-export list naming Reg/Imm/EntityId/
  Label, LiteralValue/typed-array descriptions).
- `abcd-isa/README.md`: decode/encode examples have wrong types.
- `.DS_Store` files tracked in two crates; `securec.h` returns `int` not
  `errno_t`; `vendor-sync.rb` metadata parse failure silently disables
  dirty-checking; `build.rs` bindgen allowlist misses are silent (add a
  post-generation grep check); `emitter.rs:67-71` null-check comment wrong
  (`new` throws), `:93` `debug_assert` swallows bind failure in release.
- Test gaps (each = one future regression): true invalid-opcode decode
  (blocked by #1), operand-out-of-range encode (blocked by #2), typed-array
  literal decode (#4), local-var scope roundtrip (#5), foreign-member
  annotation roundtrip (#6/#7), nested-LA + ann-LA coexistence (#8),
  embedded-NUL encode (#9), `UnsupportedAnnotationArrayType` error path,
  v24 index-region literal collection, foreign/is_external encode
  roundtrip, `method_add_param`/`method_param_add_*`, both dedup variants,
  double-finalize behavior.

---

## Verified-good (no action)

Label semantics identical on both sides; `relocate_entity_id` patch-then-
verify leaves buffers unchanged on all failure paths; EntityKind covers all
id roles present in isa.yaml; BytecodeFlags/ExceptionType bit values are
same-source-generated on both sides; prefix threshold is zero-hardcoded;
emit dispatch label-is-last-operand assumption verified against all jumps;
decoder prefix-truncation and jump-boundary handling; emitter Guard RAII;
`abc_file_open` padded copy (+16) effective against 4/5-byte overreads;
HandleGuard pairing on every decode path including error early-returns;
`AbcIndexAccessor` re-derivation is vendor-equivalent **and** adds the
bounds check vendor lacks (#B2 stays fixed); BuilderVersionScope covers all
version-sensitive entry points; `0x80000000` handle tagging consistent;
checksum backfill range matches `ValidateChecksum`/`FileWriter` semantics;
shim `adler32` byte-equivalent to reference (NMAX=5552 proof re-derived);
`os/mem.h` non-owning semantics match `File::base_` expectations and member
destruction order is correct; `pgo.h`/`timers.h` stubs signature-exact;
proto #B3 workaround semantically correct; annotation char tables are
`static_assert`-pinned (unlike LiteralTag, finding #13); literal `LiteralTag`
discriminants in `abcd-file` reference `sys::` constants; decode proto path
avoids the `EnumerateTypes` cursor trap; module-record layout matches vendor
emitter; annotation category collapse is the documented contract; try/catch
callback slice is null-safe.

## Rulings on worker questions

1. `abc_file_open`'s inner `catch (const std::exception&)` (:414) — counts as
   guarded (outer `catch (...)` still wraps); no change needed.
2. `abc_builder_finalize` delegation — acceptable without its own guard.
3. Dead FFI surface — policy decision (see above), not a delete list.
4. LNP unbounded parse — P2 (bounded by open padding); no upstream bounds
   exist; fix alongside #3.
5. Vendor duplicate files — add them to `common-files-consistency` (finding #22).
6. `AnnotationValueType` Rust mirror — acceptable (transitively pinned);
   add a dependency comment.
7. `AVT::Array('H')` and module phase records — unverified against real
   files; document as known limitations, do not guess.
8. Header section-bounds sanity check beyond `file_size` — deferred to
   maintainer decision (design trade-off; vendor trusts them upstream).

## Proposed remediation order (Phase 0.5; each = one commit + regression)

1. #1 invalid-opcode abort (decode safety) — bridge pre-validation.
2. #2 operand truncation (encode safety) — range validation + error.
3. #3 `file_size > len` (open safety) + #10 element_size whitelist.
4. #4 ARRAY_* cb drop, #5 debug scopes, #8 nested LA handles.
5. #6/#7 annotation silent zeros → hard errors; #9 NUL strings.
6. #11/#12 FFI guards (isa bridge + builder family).
7. #13 LiteralTag static_asserts, #14 sentinels, #16 layering quick wins.
8. P1 sweep (#15 callback docs, #17 param annotations decision, #18 panics,
   #19 mirrors, #20/#21 README rewrites, #22 CI).
9. P2 sweep (dead `literal_val_to_c`, staging clears, docs, test gaps).
