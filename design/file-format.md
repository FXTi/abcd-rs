# `.abc` File Format Layer (`abcd-file-sys`, `abcd-file`)

The file-format layer decodes `.abc` binary containers into a self-contained Rust model (`abcd_file::File`), re-encodes `File` back into relocated `.abc` bytes (`abcd_file::encode`), and provides a lossless `pandasm` (`.pa`) text disassembler and assembler.

---

## 1. Vendored C++ Bridge & Safety Firewall (`abcd-file-sys`)

`abcd-file-sys` compiles the reader, `ItemContainer` writer, debug-info extractor, and literal/annotation accessors from `vendor/arkcompiler_runtime_core/libpandafile/` behind a narrow C99 API (`bridge/file_bridge.h`):

1. **Exception & `LOG(FATAL)` Firewall**: Compiled with `SUPPORT_KNOWN_EXCEPTION`; `vendor/shim/utils/logger.h` silences non-fatal vendor logs (zero `stderr` pollution) and converts `LOG(FATAL, ...)` into catchable C++ exceptions so every `abc_*` C99 entrypoint returns clean error codes on malformed inputs.
2. **Span-Clamped Reads (`N81`, `N83`)**: String conversions validate both the declared MUTF-8 byte/UTF-16 prefix and the file buffer bounds (`bounded_cstr_len`, never raw `strlen`/`strcmp`), and annotation/literal array readers clamp element counts against remaining payload bytes before allocating buffers.
3. **Compile-Time ABI Lock**: `vendor/generated/file_bridge_enum_checks.h` asserts `109` C++17 `static_assert`s tying Rust `enum_bindings.rs` discriminants directly to upstream C++ headers on every build, and a bridge mutex isolates upstream's process-global API-version statics across concurrent `Builder` instances.

---

## 2. Container Model & Relocation Invariants (`abcd-file`)

- **Dual-Bucket Lossless MUTF-8 `StringPool` (`ADR-09`)**: Valid UTF-8 strings intern into deduplicated `&str` storage, while lone-surrogate MUTF-8 wire sequences retain their exact raw bytes in a side map so round-trip `encode` and `pandasm` preserve every byte losslessly.
- **Structural Field-Blob & Offset Relocation (`ADR-10`)**:
  Upstream `es2abc` stores file offsets inside five `Type::U32` class fields, all of which `abcd-file` decodes structurally rather than leaving raw offsets to dangle on rewrite:
  1. `typeSummaryOffset` → `FieldValue::LiteralArrayRef` (or `I32(0)` when `0`);
  2. `moduleRequestPhaseIdx` → `FieldValue::ModuleRequestPhase`;
  3. `_ESModuleRecord` / `moduleRecordIdx` → `FieldValue::ModuleData`;
  4. `_ESScopeNamesRecord` / `scopeNames` → `FieldValue::LiteralArrayRef`;
  5. `jsonFileContent` → `FieldValue::JsonFileContent` (relocated string reference).
- **Two-Pass Nested `LiteralArray` & Full-Width Annotation Encoding**:
  - `decode` traverses method index regions, `scopeNames`, `typeSummaryOffset`, and annotation-embedded literal arrays iteratively (`collect_nested_literal_array_offsets`) to recover every transitive `LiteralValue::LiteralArray` target—essential on `13.0.1.0+` / `24.0.0.0` where the header literal-array table is empty.
  - `encode` pre-allocates `LiteralArrayItem` handles before populating nested `LiteralValue::LiteralArray` elements and supports all scalar and `8`/`16`/`32`/`64`-bit (`I64`, `U64`, `F64`) annotation array elements.
- **Code Entity Relocation & IC-Slot Sync**:
  - Method bytecodes retain `(EntityKind, raw_idx) → source_offset` mappings (`MethodBody::entity_offsets`), registered via `abc_builder_relocate_code_id` and patched after `ItemContainer::ComputeLayout`.
  - When `MethodBody::ic_size` is set by `abcd-lower`, `encode` updates `_ESSlotNumberAnnotation` (`N73`) to match the lowered instruction stream's exact IC slot count.

---

## 3. `pandasm` Text Disassembler & Assembler (`src/pandasm/`)

- **`pandasm::emit_file` (`abcd dis`)**: Produces `.pa` byte streams **byte-for-byte identical** to upstream `ark_disasm` across all `5,517` corpus fixtures (`ADR-11`), faithfully matching record/literal ordering (`sim::U32Set` for `13.x`/`24.x`), label naming, `%g`/scientific float formatting (`N84`), and raw MUTF-8 bytes.
- **`pandasm::parse_file_with_version` (`abcd asm`)**: Parses `.pa` text back into `abcd_file::File` for binary emission via `encode`, verified across all `5,517` corpus fixtures.
