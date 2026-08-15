# ABC Container Layer Design (abcd-file-sys / abcd-file)

## File layout

The first 8 bytes are the magic `PANDA\0\0\0`, followed by a little-endian field sequence. Using the development baseline `modules.abc` as an example:

| Offset | Field | Sample value |
|--------|-------|--------------|
| 0x00 | magic | `PANDA\0\0\0` |
| 0x08 | checksum (adler32, computed from the version field onward) | `0xC30BD6FF` |
| 0x0C | version | `12.0.6.0` |
| 0x10 | file_size | 21.6MB |
| 0x14/0x18 | foreign_off / foreign_size | 0 / 0 |
| 0x1C | num_classes | 2035 |
| 0x20 | class_idx_off | 60 |
| 0x24 | num_lnps | 15738 |
| 0x28 | lnp_idx_off | … |
| 0x2C | num_literalarrays | 29147 |
| 0x30 | literalarray_idx_off | … |
| 0x34 | num_indexes | 2 |
| 0x38 | index_section_off | … |

Version conditioning: `12.0.6.0` is `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION` — before that version the header carries the literal-array index, after it the index moves elsewhere. Both sides branch on the version (vendored `ContainsLiteralArrayInHeader`).

## Entity model

- All entities are located by 32-bit offsets; references inside methods use 16-bit indices resolved through `IndexHeader` (class/method/field/proto index tables) to offsets.
- Classes/methods/fields/code are "ULEB128 prefix fields + tag sequences"; four annotation categories (compile-time / runtime / type / runtime-type), debug info (line-number program + constant pool), and module data (import/export records encoded as a literal array) are all covered.

## FFI design (file_bridge.h / file_bridge.cpp)

- Pure C interface (opaque handles); each accessor follows an `open → use → close` lifecycle.
- Enumeration is callback-based (`int (*cb)(..., void *ctx)`, non-zero stops early).
- Errors use sentinels: `UINT32_MAX` = absent, `0` = size_t failure.
- Compile-time guardrails: `static_assert`s pin vendor assumptions (MAGIC_SIZE=8, LiteralTag/AnnotationValueType char encodings, `Type::TypeId::U32 == 0x08`) so vendor changes explode at compile time instead of runtime.
- Two bindgen passes: `bindings.rs` (bridge API) + `enum_bindings.rs` (vendor enums). The ACC_* access flags are extracted by build.rs **by name from the vendored `modifiers.h`** with values referencing vendor constexprs — names are listed, values always come from vendor code, eliminating hand-written mirror drift.

## Builder

`AbcBuilder` (`ItemContainer` + `MemoryWriter`) follows "add items → finalize → free":

- Handle tables per item kind (class/foreign_class/string/literal_array/method/field/code/debug/lnp/annotation/proto/…); tagged class handles use the high bit `0x80000000` for foreign classes.
- Literal arrays stage flat `(tag, value)` pairs, flushed into `LiteralArrayItem` at finalize.
- `ItemContainer::ComputeLayout()` decides the layout: header → class index → index section → foreign → body → line-number-program index; the checksum is back-filled after writing.

## Vendor and shim strategy

Vendor (73 files, zero diff against upstream) + 10 shims replacing heavy dependencies:

- `zlib.h`: inline adler32 (NMAX=5552 batch modulus), no system zlib link;
- `os/mem.h`: non-owning `MapPtr` (the caller owns the memory);
- `pgo.h`: no-op `ProfileOptimizer` (file_item_container only needs the type);
- `platform_compat.h`: constexpr clz/ctz/popcount etc. bit builtins for MSVC;
- `vendor_fixups.h`: force-injected (`-include`) transitive headers that the upstream build system provides — **vendor files themselves are never modified**;
- `libpandabase/utils/timers.h`: **vendored zero-diff** (EVENT constants + inline `ScopeTimer`); upstream `timers.cpp` depends on `nlohmann/json` and `os::file::File` write support, which we do not bring in — the bridge provides definitions for the two static members instead (no-op function pointers, equivalent to upstream's `TimerStartDoNothing` defaults).

Build pipeline: Ruby (gen.rb, needs Ruby ≥ 2.5) generates `type.h` / `source_lang_enum.h` / `file_format_version.h` → cc compiles the 13 vendored libpandafile `.cpp` files + `utf.cpp` + the bridge → bindgen.

## Known limitations

1. **`encode()` semantic round-trip is disabled**: `abc_builder_deduplicate` crashes on the C++ side when re-encoding decoded files (`encode_roundtrip` in `abcd-file/tests/roundtrip.rs` is `#[ignore]`d). Fix directions: implement equivalent dedup before finalize in the bridge, or bypass `DeduplicateCodeAndDebugInfo`.
2. **Annotation categories were consolidated upstream at API 24**: the upstream writer now only emits the `ANNOTATION` category (the tag enum and the reader keep all four categories for legacy files). The bridge maps its four annotation APIs onto the single vector — encode folds runtime/type annotations into the compile-time bucket, matching upstream es2panda behavior.
3. The string pool cannot be enumerated directly (collected indirectly by walking entities).
4. The builder cannot set the file type (dynamic/static); the vendor code is missing it, defaults to dynamic.
5. Byte-level round-trip is impossible (the builder decides its own layout); semantic equivalence is the goal.
6. `ParamInfo::signature` is not preserved during encode (C++ writer limitation).
