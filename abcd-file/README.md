# abcd-file

Safe Rust API for the ArkCompiler bytecode container format (`.abc`). Provides eager decoding, semantic re-encoding, programmatic construction via `Builder`, and an `ark_disasm`-compatible `pandasm` text disassembler and assembler.

All public types are safe, owned structs with no lifetimes. `unsafe` is confined to internal FFI calls into [`abcd-file-sys`](../abcd-file-sys/README.md).

## Decoding

```rust,no_run
use abcd_file::{File, decode};

let data = std::fs::read("input.abc").unwrap();
let file: File = decode(&data).unwrap();

println!("version: {}", file.version);
println!("classes: {}", file.classes.len());

for (descriptor, class) in &file.classes {
    let descriptor = file.strings.resolve(*descriptor).unwrap();
    println!(
        "{descriptor} ({} methods, {} fields)",
        class.methods.len(),
        class.fields.len()
    );
    for method in &class.methods {
        if let Some(ref body) = method.body {
            let name = file.strings.resolve(method.name).unwrap();
            println!("  {name} — {} instructions", body.bytecodes.len());
        }
    }
}
```

## Encoding (semantic roundtrip) & Pandasm text

```rust,no_run
use abcd_file::{decode, encode, pandasm};

let original = std::fs::read("input.abc").unwrap();
let file = decode(&original).unwrap();

// Re-encode to .abc (relocates offsets, recomputes layout & Adler-32 checksum):
let rewritten = encode(&file).unwrap();

// Disassemble to ark_disasm-compatible .pa text and assemble back:
let pa_bytes = pandasm::emit_file(&file, "input.abc");
let reparsed = pandasm::parse_file_with_version(&pa_bytes, file.version).unwrap();
# let _ = (rewritten, reparsed);
```

## Programmatic Builder

```rust
use abcd_file::{AccessFlags, Builder, SourceLang, Type};

let mut b = Builder::new();
b.set_api(12, "beta1");
let cls = b.add_global_class();
b.class_set_source_lang(cls, SourceLang::EcmaScript);
let proto = b.create_proto(Type::Tagged, &[]);
let m = b.class_add_method(
    cls,
    "func_main_0",
    proto,
    AccessFlags::PUBLIC | AccessFlags::STATIC,
    &[0x65], // returnundefined
    0,
    0,
);
b.method_set_source_lang(m, SourceLang::EcmaScript);
b.deduplicate();
let abc_bytes = b.finalize().unwrap();
assert!(!abc_bytes.is_empty());
```

## `File` Structure

| Field | Type | Description |
|-------|------|-------------|
| `version` | `Version` | ABC file version (`0.0.0.2`, `9.0.0.0` .. `24.0.0.0`) |
| `checksum` | `u32` | Header Adler-32 checksum |
| `size` | `u32` | Header-declared file size in bytes |
| `file_type` | `FileType` | `Dynamic` (JS/TS), `Static` (ArkTS `0.1.x`), or `Invalid` |
| `strings` | `StringPool` | Interned string pool (`StringId` keys) |
| `classes` | `BTreeMap<StringId, Class>` | Classes keyed by interned descriptor (e.g. `"L_GLOBAL;"`) |
| `literal_arrays` | `Vec<LiteralArray>` | Decoded tagged literal arrays (header table + index-referenced + `scopeNames` + nested arrays) |
| `literal_array_offsets` | `HashMap<u32, u32>` | Source-file literal-array offset → `literal_arrays` index |
| `literal_array_header_offsets` | `Vec<u32>` | Raw header literal-array table on `<= 12.0.6.0` (including excluded module/phase blob slots, for `pandasm` byte-identity) |
| `entity_map` | `HashMap<u32, StringId>` | Source-file entity offset → interned name/descriptor |
| `string_raw_bytes` | `HashMap<String, Box<[u8]>>` | Original MUTF-8 bytes for lone-surrogate strings with no lossless UTF-8 form (re-emitted verbatim by `encode`) |

Convenience methods on `File`:

- `class_by_str(&str) -> Option<&Class>` — look up a class by descriptor string
- `all_methods()` — flat iterator over `(StringId, &Method)` across all classes
- `resolve_entity(offset) -> Option<StringId>` / `resolve_entity_str(offset) -> Option<&str>` — resolve a bytecode entity offset
- `decode_module(index) -> Result<ModuleData, Error>` — parse a tagged pandasm-style module literal array

## Classes, Methods, Fields & `--merge-abc` Records

- `Class` carries `descriptor`, `name`, `access_flags: AccessFlags`, `source_lang`, `source_file`, `is_external`, `super_class`, `interfaces`, `methods: Vec<Method>`, `fields: Vec<Field>`, and `annotations: Annotations`.
- `Method` carries `offset: u32` (unique method identity in the file), `access_flags`, `function_kind: FunctionKind` (`None`, `Function`, `NcFunction`, `GeneratorFunction`, `AsyncFunction`, `AsyncGeneratorFunction`, `AsyncNcFunction`, `ConcurrentFunction`, `SendableFunction`), `return_type`, `arg_types`, `body: Option<MethodBody>`, `annotations`, `param_annotations`, and `debug: Option<MethodDebugInfo>`. `Method` also implements `HasAccessFlags` (`is_public()`, `is_static()`, `is_constructor()`, …).
- `Field` carries `offset: u32`, `field_type: Type`, `access_flags: AccessFlags`, `is_external`, `initial_value: Option<FieldValue>`, and `annotations`.

`FieldValue` models both scalar values and source-offset-bearing metadata fields (standalone single-module records as well as `--merge-abc` per-record fields):

- Scalars: `I32(i32)`, `I64(i64)`, `F32(f32)`, `F64(f64)`
- `ModuleData(ModuleData)` — untagged `ModuleDataAccessor` blob on `L_ESModuleRecord;` or `--merge-abc` `moduleRecordIdx`; relocated automatically on `encode`. Inspect `md.requests` via `file.strings.resolve(req_sid)` and `md.records` (`ModuleRecord::{RegularImport, NamespaceImport, LocalExport, IndirectExport, StarExport}`).
- `LiteralArrayRef(u32)` — tagged scope-names literal-array reference on `L_ESScopeNamesRecord;` or `--merge-abc` `scopeNames`; resolved via `file.literal_array_offsets` and relocated on `encode`.
- `ModuleRequestPhase(ModuleRequestPhase)` — untagged lazy-import flag blob on `moduleRequestPhaseIdx`; relocated on `encode`.
- `JsonFileContent { source_offset: u32, content: StringId }` — `--merge-abc` `jsonFileContent` string reference; relocated via `ScalarValueItem(StringItem*)` on `encode`.
- `TypeSummaryOffset(u32)` — legacy 4.x–5.x `typeSummaryOffset` nested offset; modeled opaquely on decode and rejected loudly by `encode` (relocation unsupported).

## Annotations, Literal Arrays & Debug Info

- `Annotations` preserves four retention buckets on decode (`compile_time`, `runtime`, `compile_time_type`, `runtime_type`); `encode` folds them into the single API-24 `ANNOTATION` list per the upstream writer contract.
- `LiteralArray` holds typed `LiteralValue` items (primitives, `String`, method offsets, `LiteralArray(LiteralArrayIdx)` nested indices, and typed arrays `ArrayU1`..`ArrayString`).
- `MethodDebugInfo` provides `source_file`, `source_code`, instruction-indexed `line_table` and `column_table`, `local_vars`, and `params`.

## Known Limitations

- Byte-identical `.abc` round-tripping is not a goal (`ItemContainer` computes its own layout and Adler-32 checksum); semantic equivalence is preserved, and `MethodBody::ic_size` re-synchronizes `_ESSlotNumberAnnotation` when lowered bodies change IC-slot counts.
- `ParamInfo::signature` is not preserved during `encode` (upstream C++ `DebugInfoItem` writer limitation).
