# Quality Review: isa and file layers

Scope: `abcd-isa-sys` / `abcd-isa` / `abcd-file-sys` / `abcd-file`.
Method: full read-through of both layers (Rust, bridge C++, build scripts, generated-code templates) plus targeted empirical probes. IR layer is reviewed separately in a later round.

Severity: **P0** blocks phase-1 acceptance · **P1** correctness · **P2** robustness/docs.

Status: `open` = reported, awaiting triage · `fixed` = landed with a regression test.

## Summary table

| # | Sev | Finding | Status |
|---|-----|---------|--------|
| 1 | P0 | `decode()` constructs `ClassDataAccessor` on foreign classes; vendor throws across the FFI → SIGABRT. Real files always contain foreign classes. | open |
| 2 | P0 | Primitive-typed fields fail to decode: `abc_field_type` returns field-encoding values that are absent from `entity_map` → `Malformed`. | open |
| 3 | P0 | `encode()` round-trip disabled: C++ `abc_builder_deduplicate` crashes on re-encoded files. | open |
| 4 | P1 | `abc_file_get_type` is stubbed to always return Dynamic; static files are misreported. | open |
| 5 | P1 | MUTF-8 → `String` uses `to_string_lossy`; NUL/surrogate/astral characters corrupt to U+FFFD. | open |
| 6 | P1 | `encode()` keys `method_handles`/`field_handles` by name; same-named methods across classes collide (common in real JS). | open |
| 7 | P1 | `abc_file_open` never validates magic/checksum; garbage input reaches accessors. | open |
| 8 | P1 | Bridge `extern "C"` functions have no exception guards; any `FileAccessException` crosses the FFI → SIGABRT. | open |
| 9 | P1 | Annotation categories collapse to ANNOTATION on write (upstream API-24 behavior) — accepted, but must be the documented round-trip contract. | open |
| 10 | P2 | `File::GetClassId` is a linear scan; class hash table APIs are stubs. | open |
| 11 | P2 | `decode()` eagerly extracts all debug info even when the caller does not need it. | open |
| 12 | P2 | Unused workspace dependencies (clap/serde/serde_yaml/memmap2/env_logger/log) left over from the removed CLI. | open |
| 13 | P2 | Stale README claims: both `-sys` READMEs reference the removed `links` key; isa-sys README documents a dead `DEP_ISA_BRIDGE_BINDINGS_RS` mechanism. | open |
| 14 | P2 | C API footguns: `abc_builder_class_add_field` with REFERENCE type hits a C++ assert; `abc_builder_literal_array_add_method` requires prior method registration. | open |
| 15 | P2 | `Error::Open` carries no C++-side reason. | open |

## Findings with evidence

### 1 (P0) — foreign classes crash decode

`decode()` opens every class offset with `abc_class_open`. Vendored `ClassDataAccessor` assumes non-external classes (`ASSERT(!panda_file.IsExternal(class_id))`, compiled out under `-DNDEBUG`) and then reads string bytes as class fields; on a foreign class item (a bare `StringItem`) `ThrowIfWithCheck` fires and throws `FileAccessException` (we build with `-DSUPPORT_KNOWN_EXCEPTION`). The exception crosses the `extern "C"` boundary → `Rust cannot catch foreign exceptions` → SIGABRT.

**Probe**: a builder-produced file containing one `add_foreign_class("LExternal;")` + one global class aborts decode with SIGABRT.

**Fix**: skip external offsets in the class loop (`abc_file_is_external` first) — matching how vendor code guards accessor construction. Add a regression test with a foreign class present.

### 2 (P0) — primitive fields fail to decode

`decode_field_at` resolves `abc_field_type` (the accessor's `GetType()`, i.e. `type_off_`) through `entity_map`. For primitive types that offset is the *field encoding* (a small integer like 0x0C), which is never present in `entity_map` (built only from class/method/field entity offsets) → `Error::Malformed { field: "field_type" }`.

**Probe**: builder file with `class_add_field(..., Type::I32, ...)` → `decode` returns `missing required field_type in field "count"`.

**Fix**: use the vendored `Type::GetTypeFromFieldEncoding` (static) to classify primitive vs reference; only resolve references through `entity_map`. Add field tests (primitive + reference + initial value).

### 3 (P0) — encode round-trip disabled

`encode()` works, but the semantic-round-trip guarantee is broken by `abc_builder_deduplicate` crashing in C++ when re-encoding decoded files (specifically `DeduplicateCodeAndDebugInfo`). `encode_roundtrip` is `#[ignore]`d.

**Fix directions**: implement equivalent dedup before finalize inside the bridge, or bypass `DeduplicateCodeAndDebugInfo` (keep the other two dedups). This is the largest single item; schedule it last among the P0s.

### 4 (P1) — file type stub

`GetFileType` in `file_bridge.cpp` (the merged `file_impl.cpp` replacement) unconditionally returns `FILE_DYNAMIC`. `File::file_type` therefore reports every file as Dynamic.

**Fix**: port the vendored `GetFileType` logic (magic + version + content discrimination) from upstream `file_impl.cpp`.

### 5 (P1) — MUTF-8 lossy conversion

`read_string` (Rust) copies bytes then `to_string_lossy()`. MUTF-8 encodes NUL as 0xC0 0x80 and uses surrogate-pair/astral sequences that are not valid UTF-8 → all of them silently become U+FFFD. Entity names and string literals in HarmonyOS apps are frequently non-BMP.

**Fix**: convert via the vendored `utf.cpp` (`MUtf8ToUtf16*`) — expose a bridge function returning UTF-16, decode to `String` in Rust.

### 6 (P1) — handle maps keyed by name

`encode()` stores `method_handles`/`field_handles` keyed by `StringId` name only; a literal-array method reference or annotation Method/Enum value then resolves to the *last* same-named member across all classes — silently wrong for files with duplicate method names.

**Fix**: key by `(class_descriptor, name)` (or keep an offset→handle map built alongside `entity_map`).

### 7 (P1) — open() does not validate

`abc_file_open` only checks length ≥ header size; magic and checksum are never checked, so arbitrary bytes reach the accessors (UB or exceptions on first use). Checksum validation exists (`abc_file_validate_checksum`) but is never called by `decode`.

**Fix**: validate magic on open (fail fast with a distinct error); optionally validate checksum in `decode`.

### 8 (P1) — exceptions crossing the FFI

With `-DSUPPORT_KNOWN_EXCEPTION`, every `helpers::THROW_IF` path throws; none of the ~170 bridge functions wrap bodies in `catch (...)`. Finding 1 is one instance; any malformed/corrupt input can trigger others.

**Fix**: a macro-based guard on every bridge entry converting exceptions to sentinel errors (or a single `catch (...)` in `abc_file_open` plus per-accessor guards).

### 9 (P1) — annotation categories collapse on write

Upstream API-24 writers emit only the ANNOTATION category; our four-way builder API maps into the single vector. Accepted as the contract (documented in design/file-format.md), but the round-trip acceptance test must assert the *documented* behavior (runtime/type buckets fold into compile-time), not byte equality with legacy files.

### 10–15 (P2)

- **10**: `GetClassId` linear scan + hash-table stubs (`CalcFilenameHash` → 0). Fine for current usage; either document or implement the hash table.
- **11**: `DebugInfoExtractor` extraction is eager and file-wide in `decode()`; measurable on 20MB+ files.
- **12**: workspace deps `clap/serde/serde_yaml/memmap2/env_logger/log` are unused after the CLI removal.
- **13**: README/architecture claims: both `-sys` READMEs mention `links = ...`; isa-sys "Cargo Metadata" section describes the removed `DEP_ISA_BRIDGE_BINDINGS_RS` flow.
- **14**: bridge C API footguns (REFERENCE via `class_add_field`, literal-method ordering). Rust callers avoid them; add debug_asserts/docs or harden the bridge.
- **15**: `Error::Open` should carry the C++ reason (magic/version/parse failure).

## Verification gaps (tests to add with the fixes)

| Area | Missing today |
|------|---------------|
| Fields | decode/round-trip with primitive and reference fields, initial values |
| Foreign classes | decode a file containing foreign classes (built-ins) |
| Static file type | any static-mode fixture |
| MUTF-8 | non-ASCII / astral / embedded-NUL strings through entity names and literals |
| Annotations | four-category round-trip per target (class/method/field) |
| Try/catch | lift → lower symmetry of try regions |
| Real-file smoke | `modules.abc` decode is not in CI (not distributed) — add a local-only smoke script |

## Proposed fix ordering

1. #1 + #2 (decode usability) — small, unblock everything downstream.
2. #8 (FFI exception guard) — systemic safety before more probing.
3. #7 (open validation).
4. #4 (file type), #5 (MUTF-8), #6 (handle keys).
5. #3 (encode dedup) — largest; last among P0/P1.
6. P2 sweep (#10–15) with doc updates.
