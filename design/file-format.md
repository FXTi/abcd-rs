# `.abc` File Format Layer (`abcd-file-sys`, `abcd-file`)

The file-format layer decodes `.abc` binary containers into a self-contained Rust model (`abcd_file::File`), re-encodes `File` back into relocated `.abc` bytes (`abcd_file::encode` / `encode_with_options`), and provides a lossless `pandasm` (`.pa`) text disassembler and assembler.

---

## 1. Vendored C++ Bridge & Safety Firewall (`abcd-file-sys`)

`abcd-file-sys` compiles the reader, `ItemContainer` writer, literal/annotation accessors, and differential-oracle `DebugInfoExtractor` from `vendor/arkcompiler_runtime_core/libpandafile/` behind a narrow C99 API (`bridge/file_bridge.h`):

1. **Exception & `LOG(FATAL)` Firewall**: Compiled with `SUPPORT_KNOWN_EXCEPTION`; `vendor/shim/utils/logger.h` and `bridge/shim/vendor_fixups.h` silence non-fatal vendor logs (zero `stdout`/`stderr` pollution) and convert `LOG(FATAL, ...)` / `CHECK` / `UNREACHABLE` into catchable C++ exceptions (`LogVoidify::operator&`) so every `abc_*` C99 entrypoint returns clean error codes on malformed inputs.
2. **60-Byte Header & Span-Clamped Bounds (`R1-C1`, `N81`, `N83`)**: `validate_abc_header` verifies `file_size >= 60`, `file_size <= buf_len`, and 64-bit overflow + 4-byte alignment across all 5 index-table header pairs before constructing `panda_file::File`. String conversions validate both the declared MUTF-8 prefix and buffer bounds (`bounded_cstr_len`), and try/catch, annotation, and literal array readers clamp wire counts before allocating buffers.
3. **Compile-Time ABI Lock & LNP Staging**: `vendor/generated/file_bridge_enum_checks.h` asserts `109` C++17 `static_assert`s tying Rust `enum_bindings.rs` discriminants directly to upstream C++ headers on every build, `abc_builder_lnp_emit_special_opcode` stages exact DWARF special opcodes (with automatic `ADVANCE_PC`/`ADVANCE_LINE` + `EmitSpecialOpcode(0, 0)` fallback), and a bridge mutex isolates upstream's process-global API-version statics across concurrent `Builder` instances.

---

## 2. Container Model, Pure-Rust Hot Paths & Relocation Invariants (`abcd-file`)

- **Explicit Container `Dialect` (`ADR-14`, `D6`)**: `Dialect::{DynamicModern, DynamicLegacy, Static}` classifies `(FileType, Version)` explicitly (`File::dialect`, `FileSummary::dialect`), gating `decode`, `inspect_summary(..., true)`, `encode`, and `pandasm` so static ArkTS 1.2 (`0.1.0.x`) containers are never misrouted into dynamic `24.0.0.0` ISA decoders or `version <= 12.0.6.0` header-literal rules (while still permitting container-header inspection via `inspect_summary(..., false)`).
- **Unified Lossless MUTF-8 `StringPool` & Offset Memoization (`ADR-09`, `D3`)**:
  - `decode` slices validated `(utf16_len, bytes)` `StringItem`s directly from `&data[..size]` with an `offset → StringId` cache (zero per-string FFI calls or UTF-16 round-trips).
  - Both 6-byte CESU-8 and 4-byte UTF-8 astral sequences (plus `C0 80` NUL) normalize into canonical `Arc<str>` UTF-8 entries, reserving `RawMutf8` strictly for unpaired lone surrogates. All wire emission (`encode` and `pandasm`) routes through `string_pool::mutf8_encode_cow` (`es2abc`-canonical 6-byte CESU-8 + `C0 80`, with zero-allocation `Cow::Borrowed` fast path for ASCII/BMP strings without `0x00`).
- **Unified Bounded Pure-Rust DWARF/LNP Decoder & Lossless Emission (`ADR-14`, `D2`, `R1-H1`)**:
  - Both `decode()` and `inspect_summary()` share a single Safe Rust bounded DWARF/LNP state machine over `&data[..size]` (preserving `ProcessBegin()` row-0 semantics and `N55` `Error::DebugInfoExtraction` diagnostics), verified differentially against `abc_debug_info_open`.
  - `encode` interleaves `line_table` (`lnp_emit_special_opcode`), `column_table`, and `local_vars` in ascending PC order to preserve 100% of debug rows across round-trips, and exposes `EncodeOptions { verify: bool }` (`encode` defaults to `verify: false`; `encode_with_options` enables re-decode verification).
- **Structural Field-Blob & Offset Relocation (`ADR-10`)**:
  Upstream `es2abc` stores file offsets inside five `Type::U32` class fields, all of which `abcd-file` decodes structurally rather than leaving raw offsets to dangle on rewrite:
  1. `typeSummaryOffset` → `FieldValue::LiteralArrayRef` (or `I32(0)` when `0`);
  2. `moduleRequestPhaseIdx` → `FieldValue::ModuleRequestPhase`;
  3. `_ESModuleRecord` / `moduleRecordIdx` → `FieldValue::ModuleData`;
  4. `_ESScopeNamesRecord` / `scopeNames` → `FieldValue::LiteralArrayRef`;
  5. `jsonFileContent` → `FieldValue::JsonFileContent` (relocated string reference).
- **Two-Pass Nested `LiteralArray` & Full-Width Annotation Encoding**:
  - `decode` traverses method index regions, `scopeNames`, `typeSummaryOffset`, and annotation-embedded literal arrays iteratively (`collect_nested_literal_array_offsets`) with checked literal-tag enumeration (`R1-H6`) to recover every transitive `LiteralValue::LiteralArray` target—essential on `13.0.1.0+` / `24.0.0.0` where the header literal-array table is empty.
  - `encode` pre-allocates `LiteralArrayItem` handles before populating nested `LiteralValue::LiteralArray` elements, indexes `StringId` handles via dense `Vec<Option<StringHandle>>`, and supports all scalar and `8`/`16`/`32`/`64`-bit (`I64`, `U64`, `F64`) annotation array elements.
- **Code Entity Relocation & IC-Slot Sync**:
  - Method bytecodes retain `(EntityKind, raw_idx) → source_offset` mappings (`MethodBody::entity_offsets`), registered via `abc_builder_relocate_code_id` (using stack-inline `entity_operands_inline`) and patched after `ItemContainer::ComputeLayout`.
  - When `MethodBody::ic_size` is set by `abcd-lower`, `encode` updates `_ESSlotNumberAnnotation` (`N73`) to match the lowered instruction stream's exact IC slot count.

---

## 3. `pandasm` Text Disassembler & Assembler (`src/pandasm/`)

- **`pandasm::emit_file` (`abcd dis`)**: Produces `.pa` byte streams **byte-for-byte identical** to upstream `libstdc++`-built `ark_disasm` across all `5,517` corpus fixtures (`ADR-11`), faithfully matching record/literal ordering (`sim::U32Set` backed by GCC `libstdc++`'s exact `__prime_list` through `u32::MAX`, `R1-H4`), label naming, `%g`/scientific float formatting (`N84`), and raw MUTF-8 bytes.
- **`pandasm::parse_file_with_version` (`abcd asm`)**: Parses `.pa` text back into `abcd_file::File` in `O(N)` `# STRING` scanning with `BTreeSet`-backed multi-line quote-continuation resolution (`R1-H3`) for binary emission via `encode`, verified across `modules.abc` and all `5,517` corpus fixtures.
