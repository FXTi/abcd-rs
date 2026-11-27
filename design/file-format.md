# `.abc` File Format Layer (`abcd-file-sys`, `abcd-file`)

The file-format layer decodes `.abc` binary containers into a self-contained Rust model (`abcd_file::File`), re-encodes `File` back into relocated `.abc` bytes (`abcd_file::encode` / `encode_with_options`), and provides a lossless `pandasm` (`.pa`) text disassembler and assembler.

---

## 1. Pure-Rust Container Reader (`abcd-file`) & Vendored C++ Writer/Oracle (`abcd-file-sys`)

1. **100% Safe Rust Zero-Copy `.abc` Reader (`abcd-file`, `ADR-23`, `#49`)**:
   - All production `.abc` reading, header/checksum validation (`adler32_abc`), index-region resolution, `Class`/`Method`/`Field`/`Proto`/`Code` item decoding, `Annotation`/`LiteralArray`/`ModuleData` parsing, bounded DWARF/LNP debug extraction, and `inspect_summary` run in **100% Safe Rust (`#![forbid(unsafe_code)]`)** with zero C++ FFI calls on the read/inspect/analyze/decompile hot path.
   - Supports Dynamic `60`-byte headers (`0.0.0.2`, `0.0.0.3`, `9.0.0.0`–`24.0.0.0`) and Static `64`-byte (`0.0.0.5`) / `72`-byte (`0.0.0.6`, `0.1.0.7`) headers, `DecodeMode::{Strict, Forensic}` with structured `DecodeDiagnostics`, `Arc<[u8]>`-backed lazy `MethodCode::Span(MethodSpan)` alongside `MethodCode::Decoded(Vec<Bytecode>)`, and binary-searched `MethodEntities`.
2. **Vendored C++ Writer & Differential Oracle (`abcd-file-sys`)**:
   - `abcd-file-sys` compiles `ItemContainer` (`AbcBuilder` write path in `encode.rs`) and differential-oracle reader/LNP accessors from `vendor/arkcompiler_runtime_core/libpandafile/` behind a narrow C99 API (`bridge/file_bridge.h`) with `SUPPORT_KNOWN_EXCEPTION`, silent non-fatal logging, exception-firewall `LOG(FATAL)` conversion, `validate_abc_header` bounds checks (`R1-C1`, `N81`, `N83`), and `109` compile-time C++17 `static_assert` enum locks.

---

## 2. Container Model, Pure-Rust Hot Paths & Relocation Invariants (`abcd-file`)

- **Explicit Container `Dialect` (`ADR-14`, `D6`)**: `Dialect::{DynamicModern, DynamicLegacy, Static}` classifies `(FileType, Version)` explicitly (`File::dialect`, `FileSummary::dialect`), gating `decode`, `inspect_summary(..., true)`, `encode`, and `pandasm` so static ArkTS 1.2 (`0.1.0.x`) containers are never misrouted into dynamic `24.0.0.0` ISA decoders or `version <= 12.0.6.0` header-literal rules (while still permitting container-header inspection via `inspect_summary(..., false)`).
- **Flat-Arena Lossless MUTF-8 `StringPool` & SipHash Indexing (`ADR-09`, `ADR-23`, `#72`, `#77`)**:
  - `StringPool` packs UTF-8 display text into a single `Arc<Arena>` (`text: String`, `offs: Vec<u32>`, ascending `cold: Vec<Cold>` for lone-surrogate raw MUTF-8 bytes) paired with a droppable `hashbrown::HashTable<u32>` + `RandomState` index (`drop_index()`) and checked `< u32::MAX` capacity/offset bounds (`SummaryStrings` likewise uses `RandomState`-seeded `HashTable<u32>`).
  - Both 6-byte CESU-8 and 4-byte UTF-8 astral sequences (plus `C0 80` NUL) normalize into canonical lossless UTF-8 entries, reserving `cold` raw MUTF-8 strictly for unpaired lone surrogates. All wire emission (`encode` and `pandasm`) routes through `string_pool::mutf8_encode_cow` (`es2abc`-canonical 6-byte CESU-8 + `C0 80`, with zero-allocation `Cow::Borrowed` fast path for ASCII/BMP strings without `0x00`).
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
- **Code Entity Relocation & IC-Slot Sync (`#50`, `ADR-18`)**:
  - Method bytecodes map `(EntityKind, raw_idx) → EntityRef` (`MethodBody::entities`, resolved at decode time into typed `StringId`, `MethodIdx`, and `LiteralArrayIdx` handles, with optional `source_offset` provenance preserved solely for `ark_disasm` `.pa` emission), while `CatchBlock::type_class` carries `Option<StringId>`. During `encode`, `EntityRef` relocates directly against dense `Builder` handle vectors via `abc_builder_relocate_code_id` without consulting source-offset maps.
  - When `MethodBody::ic_size` is set by `abcd-lower`, `encode` updates `_ESSlotNumberAnnotation` (`N73`) to match the lowered instruction stream's exact IC slot count.

---

## 3. `pandasm` Text Disassembler & Assembler (`src/pandasm/`)

- **`pandasm::emit_file` (`abcd dis`)**: Produces `.pa` byte streams **byte-for-byte identical** to upstream `libstdc++`-built `ark_disasm` across all `5,517` corpus fixtures (`ADR-11`), faithfully matching record/literal ordering (`sim::U32Set` backed by GCC `libstdc++`'s exact `__prime_list` through `u32::MAX`, `R1-H4`), label naming, `%g`/scientific float formatting (`N84`), and raw MUTF-8 bytes.
- **`pandasm::parse_file_with_version` (`abcd asm`)**: Parses `.pa` text back into `abcd_file::File` in `O(N)` `# STRING` scanning with `BTreeSet`-backed multi-line quote-continuation resolution (`R1-H3`) for binary emission via `encode`, verified across `modules.abc` and all `5,517` corpus fixtures.
