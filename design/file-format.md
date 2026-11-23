# ABC Container Layer Design (`abcd-file-sys` / `abcd-file`)

## File layout

The first 8 bytes are the magic `PANDA\0\0\0`, followed by a little-endian header (`File::Header`, 60 bytes). Using `modules.abc` (`12.0.6.0`) as a concrete example:

| Offset | Field | Example (`modules.abc`) |
|--------|-------|-------------------------|
| `0x00` | `magic` | `PANDA\0\0\0` |
| `0x08` | `checksum` (Adler-32 over `[0x0C..file_size]`) | `0xC30BD6FF` |
| `0x0C` | `version` | `12.0.6.0` |
| `0x10` | `file_size` | 21.6 MB |
| `0x14` / `0x18` | `foreign_off` / `foreign_size` | `0` / `0` |
| `0x1C` / `0x20` | `num_classes` / `class_idx_off` | `2035` / `60` |
| `0x24` / `0x28` | `num_lnps` / `lnp_idx_off` | `15738` / … |
| `0x2C` / `0x30` | `num_literalarrays` / `literalarray_idx_off` | `29147` / … |
| `0x34` / `0x38` | `num_indexes` / `index_section_off` | `2` / … |

Version conditioning: `12.0.6.0` is `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION`. On `<= 12.0.6.0` the header carries the literal-array table (including untagged module/phase blobs, which `abcd-file` filters out of `File::literal_arrays` while recording raw slots in `File::literal_array_header_offsets` for `pandasm` byte-identity). On `13.x+` / `24.x` (`num_literalarrays == u32::MAX`), literal arrays are discovered from method index regions, `scopeNames` fields, and transitive nested `LiteralValue::LiteralArray` references.

## Entity & `u32` metadata field model

- Entities live at 32-bit file offsets; bytecode instructions inside a method reference 16-bit region indices resolved via `IndexHeader` into `MethodBody::entity_offsets`.
- Every `Type::U32` field initial value emitted by `es2abc` (both standalone single-module records and `--merge-abc` per-record classes) is modeled structurally in `FieldValue`:
  1. `typeSummaryOffset` → `FieldValue::TypeSummaryOffset(u32)` (legacy 4.x–5.x nested offset; decoded opaquely, rejected on `encode`).
  2. `moduleRequestPhaseIdx` → `FieldValue::ModuleRequestPhase(ModuleRequestPhase)` (untagged lazy-import `u8` flags; re-emitted and relocated on `encode`).
  3. `L_ESModuleRecord;` or `moduleRecordIdx` → `FieldValue::ModuleData(ModuleData)` (untagged `ModuleDataAccessor` blob; excluded from tagged literal-array decoding and relocated on `encode`).
  4. `L_ESScopeNamesRecord;` or `scopeNames` → `FieldValue::LiteralArrayRef(u32)` (tagged literal array collected on `13.x+` and relocated on `encode`).
  5. `jsonFileContent` → `FieldValue::JsonFileContent { source_offset, content: StringId }` (`StringItem` offset for `--merge-abc` JSON modules; re-emitted via `ScalarValueItem(StringItem*)` on `encode`).
- **MUTF-8 lone surrogates (`StringPool` raw-byte bucket)**: strings that have no lossless UTF-8 `String` representation intern directly by their canonical MUTF-8 byte slice inside `File::strings` (`raw_mutf8()` / `to_mutf8_bytes()`), so `encode` and `pandasm` round-trip colliding lone-surrogate sequences and BMP Private Use Area (`U+E000..=U+F8FF`) strings losslessly without in-band sentinels or side tables.

## Pandasm disassembler & assembler (`abcd-file/src/pandasm/`)

`pandasm::emit_file` reproduces upstream `ark_disasm` output byte-for-byte across all 5,517 corpus fixtures (matching `libstdc++` `unordered_set` bucket order on `13.x`/`24.x` literal collection and header-slot order on `<= 12.0.6.0`). `pandasm::parse_file_with_version` parses `.pa` text back into `File` for assembly via `encode`.

## FFI bridge & vendor snapshot strategy (`abcd-file-sys`)

- Upstream `arkcompiler_runtime_core` C++ sources live in the shared, read-only `vendor/arkcompiler_runtime_core/` snapshot (`OpenHarmony-v7.0-Release`, verified by per-file SHA-256 in `vendor/UPSTREAM.toml`), paired with shared shims in `vendor/shim/` (`platform_compat.h`, `securec.h`, `pgo.h`, inline Adler-32 `zlib.h`, non-aborting `logger.h`, `os/*`) and crate-local `bridge/shim/{vendor_fixups.h, isa.h}`.
- `scripts/vendor-gen.py` pre-generates the 7 Ruby C++ headers (`source_lang_enum.h`, `type.h`, `file_format_version.h`, plus 4 assembler/ISA headers), `src/generated/bindings.rs`, `src/generated/enum_bindings.rs`, and `vendor/generated/file_bridge_enum_checks.h` (`109` C++17 `static_assert`s checked during every `cc::Build` run, with zero build-time Ruby or `bindgen`).
- Every string read in `file_bridge.cpp` is strictly bounded by the file span and tag-declared UTF-16 unit count (`bounded_cstr_len` + `convert_string_utf16_bounded`, closing N81), and annotation array counts are clamped to remaining payload bytes (closing N83).

## Known limitations

1. **API-24 annotation category consolidation**: upstream's `ItemContainer` writer emits only `ANNOTATION`; `encode` folds all four decoded retention buckets into `compile_time` (pinned by `abcd-file/tests/annotation_categories.rs`).
2. `FileType` on newly built files defaults to `Dynamic` (upstream `ItemContainer` exposes no static-mode toggle).
3. `ParamInfo::signature` is not preserved during `encode` (upstream `DebugInfoItem` writer limitation).
