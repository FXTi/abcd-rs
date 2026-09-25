# Vendor-Knowledge Isolation & Export-Path Optimality Audit (q-P3)

Date: 2026-09-25 · Worker: q-P3 (read-only analysis) · Extends q-P1
(`design/bridge-surface-analysis.md`, esp. its §5 capability tables, which this
audit re-verified where cheap and uses as the capability menu).

Scope: `abcd-isa-sys`, `abcd-file-sys` (bridge C++, build.rs, templates, shims)
and their Rust consumers (`abcd-isa`, `abcd-file`); `abcd-ir/src/frame.rs` is
included because the task names it. Lift/lower ISA knowledge is out of scope
(IR is ISA-agnostic by design; lift/lower legitimately touch ISA details).
Vendor = both `*/arkcompiler_runtime_core` submodule checkouts, verified pinned
at `OpenHarmony-v7.0-Release` (`4fba38e`, `git submodule status`). The
workspace also carries `arkcompiler/arkcompiler_runtime_core-master/` — note
its vintage: its `isa.yaml` declares version `13.0.1.0` / api_version_map to
API 20, i.e. it is an **older master than the v7.0 pin** (v7.0 declares
`24.0.0.0` / API 24, diff `isa/isa.yaml` between the trees). All "master
snapshot" comparisons below are against that older tree and are labelled as
such.

## A. Isolation audit

### A.1 FFI boundary shape

**What crosses the ABI: opaque handles + primitives + our-own PODs only. No
vendor-layout struct crosses the boundary.**

`abcd-isa-sys/bridge/isa_bridge.h` (188 lines):

| Kind | Items | Class |
|---|---|---|
| Opaque handles | `IsaEmitter` (isa_bridge.h:164) | our-own, stable |
| Our-own constants | `ISA_NO_LITERAL_INDEX`, `ISA_EMIT_*`, `ISA_BUILD_*` (isa_bridge.h:6-20) | our-own ABI contract, stable |
| Everything else | `uint8_t/uint16_t/uint32_t/int64_t/size_t` scalars, `uint8_t[4]` version arrays, raw byte pointers | primitives |

The 4-byte version array width is pinned against the vendor by
`static_assert(File::VERSION_SIZE == 4)` (isa_bridge.cpp:29).

`abcd-file-sys/bridge/file_bridge.h` (823 lines):

| Kind | Items | Class |
|---|---|---|
| Opaque handles | `AbcFileHandle`, `AbcProtoAccessor`, `AbcClassAccessor`, `AbcMethodAccessor`, `AbcCodeAccessor`, `AbcFieldAccessor`, `AbcLiteralAccessor`, `AbcModuleAccessor`, `AbcAnnotationAccessor`, `AbcDebugInfo`, `AbcIndexAccessor`, `AbcBuilder` (12 total) | our-own, stable |
| Our-own PODs by value/pointer | `AbcIndexHeader` (h:105, dead export only), `AbcTryBlockInfo`/`AbcCatchBlockInfo` (h:298-307), `AbcLiteralVal`+`AbcLiteralData` union (h:370-387), `AbcAnnotationElem`/`AbcAnnotationArrayVal` (h:446-458), `AbcLineEntry`/`AbcColumnEntry`/`AbcLocalVarInfo`/`AbcParamInfo` (h:497-535), `AbcModuleRecordDef` (h:608), `AbcProtoParam` (h:644), `AbcAnnotationElemDef`/`AbcAnnotationElemDefEx` (h:737-754), `AbcCatchBlockDef` (h:702) | our-own, stable |
| Our-own enum | `AbcCodeEntityKind` (h:671-674, explicitly "not ABC on-disk values") | our-own |
| Callback typedefs | `AbcAnnotationCb`, `AbcEntityIdCb`, `AbcMethodOffsetCb`, `AbcFieldOffsetCb`, `AbcParamAnnotationCb`, `AbcProtoTypeCb`, `AbcProtoTypeExCb`, `AbcLiteralValCb`, `AbcModuleRecordCb`, `AbcTryBlockFullCb`, `AbcLineEntryCb`, `AbcColumnEntryCb`, `AbcLocalVarCb`, `AbcParamInfoCb`, `AbcCodeIdUpdater` | fn pointers over the above PODs |

The handle tagging convention (`0x80000000` high bit = foreign,
file_bridge.cpp:2551,2669,3907,3925,3939,3947,4014) is a **bridge-internal**
encoding, documented at file_bridge.h:660; it never appears in Rust as a
literal (Rust sees opaque `u32` handles) and is not vendor knowledge.

Vendor-layout knowledge stays on the C++ side where it belongs:
`reinterpret_cast<const File::Header*>` (file_bridge.cpp:410, 253), vendor
`Span`s, `helpers::Read`, leb128 — all inside the bridge TU.

**Bindgen channels** (verified against build.rs):

- abcd-isa-sys/build.rs:191-193 — functions `isa_.*`, types `Isa.*`, vars
  `ISA_.*` over `isa_bridge.h` only. No vendor header is parsed.
- abcd-file-sys/build.rs:195-201 — `abc_.*`/`Abc.*`/`ABC_.*` over
  `file_bridge.h` only (pure C header, no vendor include).
- abcd-file-sys/build.rs:210-244 (enum pass) — parses the *generated*
  `file_bridge_enums.h` (built by `generate_enums_header`,
  build.rs:283-328), which `#include`s vendor headers and re-exports ACC_*
  **values by referencing the vendor constexpr** (`ABC_x = panda::x`, names
  auto-extracted from `modifiers.h` by regex, build.rs:290-294) plus six
  vendor enum classes (`LiteralTag`, `ModuleTag`, `FunctionKind`,
  `SourceLang`, `Type::TypeId`, `MethodHandleType`) as `constified_enum`
  constants. **Values are re-derived from vendor code at every build; only
  names are listed.** This is the model constant surface.

### A.2 Rust-side leak sweep

Method: grep for hex/binary literals, numeric comparisons, `as u8/u32` casts
on tags, hardcoded descriptors/offsets across `abcd-file/src/*.rs`,
`abcd-isa/src/*.rs`, plus `abcd-ir/src/frame.rs`; then read every hit in
context. Classes: **(a)** bindgen-derived at build = fine; **(b)** hardcoded
but pinned (static_assert or test against vendor) = acceptable; **(c)**
hardcoded and unpinned = leak.

**Class (a) — bindgen-derived (the bulk; verified file by file):**

- `abcd-file/src/types.rs` — `AccessFlags` bitflags (types.rs:9-34), `TypeId`
  (218-233), `SourceLang` (261-267), `FunctionKind` (286-296): **every**
  discriminant is `sys::ABC_ACC_*` / `sys::Type_TypeId_*` /
  `sys::SourceLang_*` / `sys::FunctionKind_*`. Zero literals.
- `abcd-file/src/literal.rs:11-42, 44-80` — all 31 `LiteralTag` variants and
  the `TryFrom<u8>` table are `sys::LiteralTag_*`. The one numeric in a
  comment (literal.rs:97, "tag 0x00") is comment-only.
- `abcd-file/src/annotation.rs:13-45` — `MethodHandleType` from
  `sys::MethodHandleType_*`, including the `is_field_op` boundary
  (`<= sys::MethodHandleType_GET_INSTANCE`, annotation.rs:44).
- `abcd-file/src/decode.rs:654-677` — module record tags matched against
  `sys::ModuleTag_*`. `decode.rs:1132-1330` — annotation tag dispatch via
  `sys::AnnotationValueType` (see (b) below for that enum's own pin).
  Field-value width dispatch keys on bindgen `TypeId` (decode.rs:777-816).
- `abcd-isa/src/version.rs` — **no version tuple is hardcoded anywhere**;
  current/min/api-map/incompatible-set are all runtime FFI queries
  (version.rs:61-131).
- `abcd-isa-sys/templates/bytecode.rs.erb` — the whole `Bytecode` enum,
  opcodes, operand roles, `EntityKind` are generated from the vendor's own
  `isa.yaml` at build time (abcd-isa-sys/build.rs:99-106).

**Class (b) — hardcoded but pinned:**

- `abcd-file-sys/src/lib.rs:18-34` — `FileType` mirror (`-1/0/1`). Pinned by
  `static_assert`s against `panda_file::PandaFileType`,
  file_bridge.cpp:42-44. A repin that renumbers fails the C++ build loudly.
- `abcd-file-sys/src/lib.rs:46-88` — `AnnotationValueType` char mirror
  (`b'1'`..`b'@'`). The values come from vendor *functions*
  (`pandasm::Value::GetTypeAsChar`/`GetArrayTypeAsChar`), so bindgen cannot
  extract them; instead 40 `static_assert`s (file_bridge.cpp:48-87) pin every
  char. Correct mechanism choice; pinned.
- Bridge-side hardcoded tag bytes in the tolerant literal enumerator
  (file_bridge.cpp:1886-1979) — each of the 30 tags is pinned by a
  `static_assert` against the vendor enum immediately above
  (file_bridge.cpp:1851-1880, "#13: pin every tag literal…"). Renumber =
  compile error.
- `abcd-file/tests/file_type.rs:34-42` — hand-crafts `{0,1,0,7}` +
  `"PANDA\0\0\0"`: a **deliberate tripwire** for the vendor `STATIC_VERSION`
  semantics (updated by 4d586cb). Test pins are the intended class-(b)
  mechanism for on-disk byte sequences.
- Test-code vendor values in `abcd-file-sys/src/lib.rs` `#[cfg(test)]`
  (e.g. `0xa0` = returnundefined :160, proto `0x0d` = TAGGED :162/:207,
  `0x0001` = ACC_PUBLIC :168, tag `0x0b` = ARRAY_U8 :379/:401) — these are
  the empirical pins themselves; a vendor change breaks the test loudly.
  Acceptable; using the bindgen constants there would be more
  self-documenting but is cosmetic (see V-I9).

**Class (c) — hardcoded and unpinned (the leaks):**

1. **Record/field name strings** (abcd-file/src/decode.rs:549-576):
   `ES_MODULE_RECORD_DESCRIPTOR = "L_ESModuleRecord;"` (:549),
   `ES_SCOPE_NAMES_RECORD_DESCRIPTOR = "L_ESScopeNamesRecord;"` (:552),
   `MODULE_REQUEST_PHASE_FIELD = "moduleRequestPhaseIdx"` (:562),
   `TYPE_SUMMARY_OFFSET_FIELD = "typeSummaryOffset"` (:576). Well-documented
   with vendor citations, **but the same strings exist as vendor constants in
   the pinned tree** (`libpandafile/util/collect_util.h:40-44`,
   `libpandabase/.../const_value.h:25` — verified present at 4fba38e) and
   nothing pins our copies against them. A rename upstream would silently
   disable module-record/scope-names detection (decode falls through to
   generic field handling, no error). → **V-I1**.
2. **abcd-ir/src/frame.rs callType bits** (frame.rs:91-93 `0b1000/0b0010/
   0b0001`; the `0xF` default :45-49; mirrored in function.rs:213-216). The
   cited source (`method_literal.h:59-62`, `method_literal.cpp:51`) lives in
   **arkcompiler_ets_runtime**, verified *absent* from both vendored
   runtime_core checkouts (`find` for `method_literal*` in both submodules:
   empty; present at `arkcompiler/arkcompiler_ets_runtime-master/ecmascript/
   jspandafile/method_literal.h`). So this knowledge can never be
   bindgen/static_assert-pinned against the vendor pin — and conversely a
   runtime_core repin cannot stale it; only an es2abc/ets_runtime change
   could. The bits are file-format semantics produced by es2panda. Class (c)
   within the strict rubric, but structurally unavoidable from this vendor
   tree. → **V-I2**.
3. **`ModuleData::from_literal_values`** (abcd-file/src/module.rs:86-149,
   called from model.rs:250): a hand-rolled Rust re-read of the vendor
   module-blob **section order** (regular→namespace→local→indirect→star)
   over the *tagged pandasm-level* representation. The same order knowledge
   lives in the bridge writer as `SECTION_ORDER` (file_bridge.cpp:2887-2892)
   and in the vendor reader (`module_data_accessor-inl.h:34-62`). Rust side
   is unpinned except behaviorally (abcd-file/tests/module_records.rs). Real
   on-disk blobs take the bridge path (decode.rs:587-682), so exposure is
   the pandasm-text compatibility path only. → **V-I3** (minor).

Not leaks, checked and cleared: `abcd-file/src/encode.rs:36` (`0xC0,0x80`
MUTF-8 NUL encoding — encoding rule, documented); `u32::MAX`/`ABSENT`
sentinels (file.rs:9 — our own); `decode_annotation_array_elements` element
sizes 1/2/4/8 keyed on the pinned `AnnotationValueType` (decode.rs:1361-1381);
`abcd-lower/src/regalloc.rs:145` `TEMP_REG_BASE = 0xfff0` (our allocation
choice within the vendor u16 vreg space; lift/lower, out of scope);
`abcd-ir/src/effects.rs:51` `0x3F` (our own bitset).

### A.3 The v7.0 repin retrospective (the measured leak list)

History (`git log`): `eb8c9da` moved both gitlinks master(`7303d5c2`) →
`OpenHarmony-v7.0-Release`(`4fba38e`); PR #20 merged as `c6e41cc`; the only
code fix was **`4d586cb`** touching `abcd-file-sys/bridge/file_bridge.cpp`
(+7/-2) and a test comment (`abcd-file/tests/file_type.rs`).

**What actually broke: exactly one function, inside the bridge.** The ported
`GetFileType` referenced master-only constants `File::FILE_TYPE_OFFSET`,
`File::FILE_TYPE_STATIC_FLAG`, `File::OLD_STATIC_VERSION` that v7.0 deleted
(today: file_bridge.cpp:247-260, using `File::STATIC_VERSION`
symbolically). Verified against the trees: v7.0 `libpandafile/file.h:62` =
`{0,1,0,7}`; the workspace (older) master snapshot = `{0,0,0,6}`; both use
the single-equality scheme in `file.cpp:677-704`, so the symbolic reference
is repin-safe in both directions.

Three properties of that break are the empirical verdict on the isolation
architecture:

1. **The leak was already inside the bridge** (the C++ seam), not in Rust.
   Rust needed **zero** changes for the repin.
2. **It failed loudly** (missing constants = compile error), not silently.
   The fix was to reference the *surviving* vendor constant by name.
3. The other v7.0 differences named in the 4d586cb message (pandasm dedup
   pass, ParseInt ERANGE, LNP NeedsEmit filter) were non-issues precisely
   because no bridge code referenced them.

**Cross-check — current tree vs v7.0↔master divergence surface** (diffed
`libpandafile/`, `isa/`, `assembler/annotation.h` between the pin and the
workspace master snapshot; accessor headers — class/method/code/field/proto/
literal/module/debug/index — are **byte-identical**; `modifiers.h` identical;
`annotation.h` identical):

| Divergence | Referenced by us? | Exposure |
|---|---|---|
| `File::STATIC_VERSION` value | yes, symbolically (file_bridge.cpp:255) | none — follows the pin |
| `isa.yaml` grew (opcodes `0xdd-0xe1`, version 24.0.0.0, API 24) | consumed via codegen (build.rs:19-106) | none — tables regenerate |
| `file_item_container.h/.cpp` API reshuffle (`SetBytecodeVersion`, `ComputeLayout*` split, `GetIndexDependencies` signature) | container API called throughout the builder; `GetIndexDependencies` **not** called (grep: only `AddIndexDependency`, file_bridge.cpp:3217,3254,4039 — present in both) | compile-loud |
| `ParamAnnotationsItem` ctor: v7.0 collects `param.GetAnnotations()` unconditionally (v7.0 file_items.cpp:424-431); the (older) master snapshot branches on `is_runtime_annotations` (master file_items.cpp:480-484) | yes — all four `abc_builder_method_param_add_*` stage via `AddAnnotation` (file_bridge.cpp:3787-3838) and `abc_builder_method_seal_param_annotations` (:3839-3850) relies on the v7.0 collection semantics | **watch item** — if a future pin branches the ctor, the runtime bucket silently empties; pinned behaviorally by `runtime_only_bucket_seals_as_runtime` (abcd-file/tests/param_annotations.rs:147). → V-I4 |
| `StringItem::GetUtf16Len` return type (`uint32_t` vs `size_t`) | only in DEAD exports (`abc_file_get_string_utf16_len`, file_bridge.cpp:629) | compile-loud; q-P1 already recommends deleting |

## B. Export-path optimality

Axes: (a) robustness against vendor version drift, (b) runtime performance.
Menu from q-P1 §5's 37 rows; only rows where a real choice existed are
assessed.

| # | Capability | Paths available | Path taken | Verdict |
|---|---|---|---|---|
| 1 | Literal-array enumeration | vendor `LiteralDataAccessor::EnumerateLiteralVals` / hand-rolled | **Hand-rolled tolerant rewrite** (file_bridge.cpp:1882-1981) because the vendor walker aborts on tag `0x00` (audit #A1) — a correctness forcing function, not a preference | **Optimal.** Drift: 30 tag static_asserts (:1851-1880) make any renumber a compile error. Perf: same single pass as vendor, plus bounds checks |
| 2 | MethodHandle items | compile vendor `method_handle_data_accessor.cpp` / hand-rolled | Hand-rolled (file_bridge.cpp:2269-2287); vendor TU excluded (build.rs:99-104) | **Optimal.** The vendor TU is a 3-line ctor ([u8 type][uleb offset], verified identical: vendor `method_handle_data_accessor.cpp:24-26`); compiling it buys nothing and drags its deps. `MethodHandleType` values are bindgen-derived on the Rust side (annotation.rs:13-22), so the enum half is drift-proof; the 2-field layout is test-pinned |
| 3 | FunctionKind from access flags | wrap vendor `IndexAccessor` / bounded re-derivation | **Re-derivation** (file_bridge.cpp:2427-2435) because vendor's ctor indexes `GetIndexHeaders()[header_index]` unchecked (audit #B2 — UB on malformed input) | **Optimal.** `FUNCTION_KIND_MASK`/`FLAG_WIDTH` are referenced *symbolically* (vendor constants, file_items.h:138-140) — name-reference drift-safe; robustness strictly dominates (the vendor path is a correctness bug for us); perf equal |
| 4 | File type (static/dynamic) | vendor `GetFileType` in `file.cpp` (excluded TU) / runtime version detection / port | **Ported into the bridge** (file_bridge.cpp:247-260), referencing `File::STATIC_VERSION` by name | **Optimal.** Runtime version detection would be *wrong*: static-ness is a producer-era property, not derivable from the version tuple semantics we choose. The port survived the v7.0 repin loudly (compile break on deleted names, fixed 4d586cb) and is now name-referenced; test tripwire file_type.rs:34-42 |
| 5 | ISA classification (jump/throw/terminator/range/suspend/flags) | per-query FFI into vendor generated methods / generated Rust tables from `isa.yaml` | **Per-query FFI** (`isa_is_jump_opcode` family, isa_bridge.cpp:251-322; called per instruction from `Bytecode::is_jump` etc., bytecode.rs.erb:239-284; hot in lift CFG construction, abcd-lift/src/cfg.rs:54,64,108,120) | **Suboptimal — consider change.** Drift robustness is *equal* on both paths (both derive from the same `isa.yaml`; the template already computes `jump?` at codegen for `decode_one`, bytecode.rs.erb:430). Performance favors generated `const` tables: zero FFI per query. No in-tree benchmark quantifies the FFI cost (no `benches/` anywhere) — perf impact **unverified**, but the call is on the per-instruction hot path. → V-I7 |
| 6 | ISA operand extraction in decode | per-operand FFI (`isa_get_vreg`/`isa_get_imm64`/`isa_get_id`/`isa_get_imm_data`, bytecode.rs.erb:447-454) / generated pure-Rust extraction | Per-operand FFI (3-7 FFI calls per decoded instruction, plus `isa_get_opcode`+`isa_get_size_by_opcode` per instruction, decoder.rs:49-51) | **Acceptable, watch.** Same reasoning as #5 with a stronger correctness caveat: operand *byte layout* logic is vendor code today; baking it into the template copies more vendor logic into our codegen (the template is ours, the data is isa.yaml's — the width rules come from the yaml format specs, so it is derivable). Bigger refactor than #5; do #5 first |
| 7 | Constant surface (ACC_*, tags, TypeId, SourceLang, FunctionKind, MethodHandleType) | copy constants into Rust / bindgen from vendor headers / accessor functions | **Bindgen direct** (build.rs:210-244 + generated `file_bridge_enums.h`, :283-328) | **Optimal.** Values re-derived from vendor every build; ACC_* *names* auto-extracted from `modifiers.h` so even additions appear automatically. The two mirrors that bindgen can't reach (`FileType`, `AnnotationValueType`) are static_assert-pinned (file_bridge.cpp:42-87) — correct fallback mechanism |
| 8 | Module-record blob read | vendor `ModuleDataAccessor` / hand-rolled | **Vendor accessor** (`abc_module_enumerate_records` → `EnumerateModuleRecord`, file_bridge.cpp:2081-2092) | **Optimal** (read side). The *write* side hardcodes `SECTION_ORDER` (file_bridge.cpp:2887-2892) — matches the vendor reader order (`module_data_accessor-inl.h:34-62`) and the enum declaration order; section order is layout knowledge a static_assert can't express, pinned behaviorally by module roundtrip tests (module_records.rs, real_module_abc.rs). Acceptable |
| 9 | Module-request-phase blobs | vendor accessor / hand-rolled | **Hand-rolled** (file_bridge.cpp:2111-2127) | **Optimal by necessity.** The runtime reader lives in ets_runtime (`module_data_extractor.cpp` `ModuleLazyImportFlagAccessor`), **not in the vendored repo** — there is no vendor path to wrap. Layout documented at file_bridge.cpp:2102-2110 and module.rs:29-47; test-pinned (module_record_phase_field.rs) |
| 10 | ParamAnnotationsItem read | vendor reader / hand-rolled | **Hand-rolled** (file_bridge.cpp:1288-1308) | **Optimal by necessity** — no upstream reader exists (`ParamAnnotationsItem` is write-only; layout from `file_items.cpp:449`, verified identical in the master snapshot, :476-496). Test-pinned (param_annotations.rs). Write side: see V-I4 |
| 11 | Version constants/maps | bindgen / copied arrays / FFI runtime queries | **FFI queries** (`isa_get_version` family, isa_bridge.cpp:506-590) over the generated `file_format_version.h` maps | **Optimal.** The api_version_map/incompatible sets are runtime data (`std::map`/`std::set` in generated headers) — bindgen cannot surface them; FFI is the only channel. Cold path; perf irrelevant. Rust side holds zero version literals (version.rs) |
| 12 | Validity guard for vendor `GetFormat` NDEBUG-abort | patch vendor / pre-validate with generated table | **Generated table** (`isa_bridge_valid_opcode.h.erb` from `isa.yaml`, build.rs:90-97; guards every opcode-derived entry, isa_bridge.cpp:12-22) | **Optimal.** Same-source codegen (drift-proof by construction), O(1) switch, no vendor edit (vendor-sync.md principle 2) |
| 13 | `BytecodeFlags`/`ExceptionType` Rust bitflags | bindgen / generated mirror | **Generated mirror** (bytecode.rs.erb:60-84) replicating the vendor template's `1 << i` scheme (vendor `bytecode_instruction_enum_gen.h.erb:31-39`) | **Acceptable.** Both sides derive from the same `isa.yaml` property list with the same formula — consistent by shared-source construction; divergence requires upstream changing its *template*, not just the yaml. Only behaviorally pinned (JUMP/RETURN, abcd-isa/tests/bytecode.rs:88-100). Cheap hardening available (generated static_assert per flag). → V-I5 |

## C. Findings register + recommendations

| # | Finding | Evidence | Class | Recommendation |
|---|---|---|---|---|
| V-I1 | Four vendor name strings copied into Rust (`L_ESModuleRecord;`, `L_ESScopeNamesRecord;`, `moduleRequestPhaseIdx`, `typeSummaryOffset`); the same strings exist as vendor constants in the pinned tree; unpinned | abcd-file/src/decode.rs:549,552,562,576; vendor collect_util.h:40-44, const_value.h:25 | (c) leak, low severity | **Fix before next repin (cheap):** add a `static_assert`-style check in file_bridge.cpp — e.g. a `static_assert` on `std::string_view` equality against `collect_util.h`'s constants (header is includable; `util/` is not compiled but headers are reachable), or export them as bridge constants and compare in a sys test |
| V-I2 | es2abc frame-slot bit layout (`0b1000/0b0010/0b0001`, `0xF` default) hardcoded in abcd-ir; source header is in ets_runtime, **not** in the vendored repo — no pin is possible against the vendor pin | abcd-ir/src/frame.rs:91-93, 45-49, function.rs:213-216; `method_literal.h` absent from both submodules, present at arkcompiler/arkcompiler_ets_runtime-master/ecmascript/jspandafile/method_literal.h | (c) by necessity, low | **Accept + document** (already thoroughly documented in frame.rs). Optional: a comment-level note that the bit layout is es2panda/ets_runtime contract, not runtime_core; re-validate only when the es2abc frontend baseline moves |
| V-I3 | `ModuleData::from_literal_values` re-implements the vendor module-blob section order in Rust (tagged pandasm path only) | abcd-file/src/module.rs:86-149, caller model.rs:250; order source module_data_accessor-inl.h:34-62 | (c), low | **Accept + document** (behaviorally pinned by module_records.rs); if the tagged path ever matters for real files, route it through the bridge like decode_module_data_at does |
| V-I4 | Param-annotation staging assumes v7.0 `ParamAnnotationsItem` ctor semantics (all four `abc_builder_method_param_add_*` stage into `AddAnnotation`; seal relies on the ctor collecting `GetAnnotations()` unconditionally). A future pin whose ctor branches on `is_runtime_annotations` would silently empty the runtime bucket | file_bridge.cpp:3787-3838 (staging), 3839-3850 (seal); v7.0 file_items.cpp:424-431; master-snapshot branch at file_items.cpp:480-484 | pinned-by-test, watch | **Watch at next repin:** re-diff `ParamAnnotationsItem`'s ctor; if it branches, stage runtime annotations via `MethodParamItem::AddRuntimeAnnotation` when the vendor API exists (v7.0 lacks it — that's why `file_reader.cpp` is excluded, build.rs:91-95). Tripwire already exists: param_annotations.rs:147 `runtime_only_bucket_seals_as_runtime` |
| V-I5 | `BytecodeFlags`/`ExceptionType` mirror the vendor template's `1 << i` scheme with no cross-check between the two generators | bytecode.rs.erb:60-84 vs vendor bytecode_instruction_enum_gen.h.erb:31-39 | shared-source construction, weak pin | **Accept** (divergence requires a vendor *template* scheme change); optional hardening: emit one static_assert per flag into isa_bridge.cpp from the same template run |
| V-I6 | `FileType`/`AnnotationValueType` mirrors in the sys crate | abcd-file-sys/src/lib.rs:18-22, 46-88; pins file_bridge.cpp:42-44, 48-87 | (b) pinned | **Accept.** Optional: allowlist `panda::panda_file::PandaFileType` in the enum bindgen pass and drop the `FileType` mirror; the char-valued `AnnotationValueType` cannot be bindgen'd (values come from functions) — the static_assert pin is the right mechanism there |
| V-I7 | Per-query FFI for ISA classification on the lift hot path; codegen tables from `isa.yaml` would be equally drift-robust and faster | bytecode.rs.erb:239-284; abcd-lift/src/cfg.rs:54,64,108,120; precedent: isa_bridge_valid_opcode.h.erb | perf, unverified (no benches in tree) | **Consider change** (not blocking): generate `const` classification tables in bytecode.rs.erb; measure first — no benchmark exists, so quantify before/after |
| V-I8 | `design/vendor-sync.md` §3 still describes the pin as master `7303d5c2` and cites "v7.0-Release fails to build" as a hypothetical — stale since PR #20 merged the v7.0 port | design/vendor-sync.md:17-25, 73-76 vs `git submodule status` = 4fba38e | doc drift | **Fix now** (one paragraph): the pin is v7.0-Release; record 4d586cb as the measured porting cost |
| V-I9 | Sys-crate tests hardcode vendor values that have bindgen names (`0xa0` returnundefined, `0x0d` TAGGED, `0x0001` ACC_PUBLIC, `0x0b` ARRAY_U8) | abcd-file-sys/src/lib.rs:160,162,168,207,379 | test pins (functionally fine) | **Accept** (tests are the pins); cosmetic: use `sys::Type_TypeId_TAGGED` etc. for self-documentation |

### Verdict

**The isolation architecture is sound, and it is now empirically validated.**
The v7.0 repin (PR #20) is the natural experiment: the measured leak list is
exactly one item, it was already inside the bridge C++ seam, it failed loudly
at compile time, and the Rust stack required zero changes (§A.3). The FFI
boundary passes only opaque handles, primitives, and our-own PODs — no
vendor-layout struct crosses (§A.1). Every tag/flag/type enum value in Rust
is either bindgen-re-derived at build or static_assert-pinned in the bridge;
the sweep found **2 genuine class-(c) leaks** (V-I1 name strings, V-I2 frame
bits — the latter structurally un-pinnable from this vendor repo) plus one
minor (V-I3). One export path is **suboptimal-consider-change** (V-I7,
per-query classification FFI — performance axis only, unverified without a
benchmark); every other deliberate non-standard choice is optimal or
optimal-by-necessity (§B).

**Before the NEXT vendor repin, in priority order:**

1. V-I1: pin the four vendor name strings (static_assert or bridge-exported
   constants) — the only unpinned vendor knowledge reachable from a
   runtime_core repin.
2. V-I4: add "diff `ParamAnnotationsItem` ctor + `MethodParamItem` runtime
   API" to the repin checklist; the existing test tripwire converts a silent
   behavior change into a red build anyway.
3. Land the q-P1 dead-surface deletion first if planned: several dead exports
   reference drifting vendor APIs (`GetUtf16Len` etc.) — deleting them shrinks
   the surface the next repin must keep compiling.
4. V-I8: refresh design/vendor-sync.md §3 so the next repin starts from
   accurate docs.
5. Optional: V-I5 hardening (generated flag static_asserts), V-I7 measurement.

*Evidence limitations (explicitly flagged):* (1) the workspace
`arkcompiler/arkcompiler_runtime_core-master` snapshot is an **older master**
than the v7.0 pin (isa.yaml 13.0.1.0/API≤20 vs 24.0.0.0/API24) — "differs
from master" statements are against that tree, not current upstream master;
the V-I4 master-side ctor shape in particular may already have changed again
upstream, which is exactly why it is a repin-time check rather than a fix-now;
(2) no object-level `nm` verification (inherited from q-P1); (3) V-I7's
performance claim is structural (FFI on a per-instruction path), not
benchmarked — no benchmark harness exists in the workspace; (4) the
untagged-blob layouts (module request phase, MethodHandle) are pinned by
tests and cross-repo doc citations, not by static_assert — no stronger
mechanism exists for serialization layouts.

## Orchestrator verification (2026-09-25, before landing)

- **V-I1 exact**: the four strings are at decode.rs:549/552/562/576 as
  claimed; vendor counterparts exist in the pinned tree
  (collect_util.h:40-44, const_value.h:25-27 — note vendor's
  `MODULE_REQUEST_PAHSE_IDX` carries an upstream typo, and the vendor
  descriptor constants lack our `L` prefix — the pin mechanism must
  account for both).
- **Repin retrospective exact**: `eb8c9da` (gitlink move) / `c6e41cc` (PR
  #20 merge) / `4d586cb` (GetFileType port) all in history; v7.0
  `File::STATIC_VERSION = {0,1,0,7}` at libpandafile/file.h:62 — exact.
- **V-I2 exact**: `method_literal*` absent from both submodules, present at
  `arkcompiler/arkcompiler_ets_runtime-master/ecmascript/jspandafile/`.
- **V-I4 exact**: v7.0 `ParamAnnotationsItem` ctor (file_items.cpp:424-431)
  collects `param.GetAnnotations()` unconditionally before branching on
  `is_runtime_annotations`.
- **V-I7 mechanism exact**: `bytecode.rs.erb:239/244` emit per-query FFI
  (`isa_is_jump_opcode` etc.); `abcd-lift/src/cfg.rs:54,108` call
  `is_jump()` — the hot-path claim is structural but real. No benchmark
  exists (confirmed: no `benches/` in the workspace).
- **Vintage claim exact**: v7.0 isa.yaml `version: 24.0.0.0` vs the
  workspace master snapshot's `13.0.1.0` — the snapshot predates the pin.
