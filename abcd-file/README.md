# abcd-file

Safe Rust API for the ArkCompiler bytecode file format. Provides reading, writing, and inspection of `.abc` files.

All public types are safe, owned structs with no lifetimes. `unsafe` is confined to internal FFI calls into `abcd-file-sys`, which generally does not need to be used directly.

## Decoding

```rust
use abcd_file::{decode, File};

let data: &[u8] = &[/* raw .abc bytes */];
let file: File = decode(data).unwrap();

println!("version: {}", file.version);
println!("classes: {}", file.classes.len());

for (descriptor, class) in &file.classes {
    let descriptor = file.strings.resolve(*descriptor).unwrap();
    println!("{descriptor} ({} methods, {} fields)", class.methods.len(), class.fields.len());
    for method in &class.methods {
        if let Some(ref body) = method.body {
            let name = file.strings.resolve(method.name).unwrap();
            println!("  {name} — {} instructions", body.bytecodes.len());
        }
    }
}
```

## Encoding (roundtrip)

```rust
use abcd_file::{decode, encode};

let original: &[u8] = &[/* raw .abc bytes */];
let file = decode(original).unwrap();
let output = encode(&file).unwrap();
// `output` is a valid .abc file — checksums differ but semantics are preserved.
```

## Builder

Construct `.abc` files programmatically:

```rust
use abcd_file::{Builder, Type, AccessFlags};

let mut b = Builder::new();
let cls = b.add_global_class();
let proto = b.create_proto(Type::Void, &[]);
let _method = b.class_add_method(
    cls, "func_main_0", proto,
    AccessFlags::PUBLIC | AccessFlags::STATIC,
    &[/* encoded bytecode */], 0, 0,
);
b.deduplicate();
let abc_bytes = b.finalize().unwrap();
```

## File Structure

`decode` returns a `File` with:

| Field | Type | Description |
|-------|------|-------------|
| `version` | `Version` | ABC file version (e.g. 13.0.1.0) |
| `checksum` | `u32` | Adler-32 checksum |
| `size` | `u32` | File size in bytes |
| `file_type` | `FileType` | `Dynamic` (JS/TS) or `Static` (ArkTS) |
| `strings` | `StringPool` | String interner — all string data lives here |
| `classes` | `BTreeMap<StringId, Class>` | Classes keyed by interned descriptor (e.g. `"L_GLOBAL;"`) |
| `literal_arrays` | `Vec<LiteralArray>` | Literal arrays indexed by position |
| `literal_array_offsets` | `HashMap<u32, u32>` | Source-file literal-array offset → decoded table index |
| `entity_map` | `HashMap<u32, StringId>` | Entity offset → interned name/descriptor |

Navigation methods on `File`:

- `class(descriptor: StringId)` / `class_by_str(&str)` — look up a class by descriptor
- `all_methods()` — flat iterator over `(StringId, &Method)` pairs
- `resolve_entity(offset)` → `Option<StringId>` / `resolve_entity_str(offset)` → `Option<&str>` — resolve a bytecode entity offset to its name/descriptor
- `literal_array(index)` — get a literal array by index
- `decode_module(index)` — decode ES module data from a literal array

## Classes, Methods, Fields

Each `Class` contains `methods: Vec<Method>`, `fields: Vec<Field>`, and `annotations: Annotations`. Convenience lookups: `method_by_name()`, `field_by_name()`, `super_class_in(&file)`.

`Method` carries `body: Option<MethodBody>` (bytecodes + try-catch blocks), `debug: Option<MethodDebugInfo>`, `return_type: Option<Type>` / `arg_types: Vec<Type>`, `param_annotations`, and annotations. The `offset` field is the file's unique method identity — names are not unique across classes.

`Field` has `field_type: Type`, optional `initial_value`, and annotations.

All three types expose access flag helpers (`is_public()`, `is_static()`, `is_abstract()`, etc.) derived from `AccessFlags`.

## Annotations

Annotations are grouped by retention policy in the `Annotations` struct:

```rust
pub struct Annotations {
    pub compile_time: Vec<Annotation>,       // discarded after compilation
    pub runtime: Vec<Annotation>,            // available via reflection
    pub compile_time_type: Vec<Annotation>,  // type annotations (compile-time)
    pub runtime_type: Vec<Annotation>,       // type annotations (runtime)
}
```

Each `Annotation` has a `class_descriptor: StringId` and `elements: Vec<AnnotationElem>`. Element values are fully typed via `AnnotationValue`:

- Primitives: `Bool`, `I8`/`U8`, `I16`/`U16`, `I32`/`U32`, `I64`/`U64`, `F32`/`F64`
- Interned strings: `String(StringId)`, `Record(StringId)` (class descriptor)
- Resolved references: `Method { name: StringId, offset: u32 }`, `Enum { name: StringId, offset: u32 }` — name plus the item offset in the source file (the unique entity identity)
- Resolved compound values: `Annotation(Box<Annotation>)` (nested annotation), `MethodHandle(ResolvedMethodHandle)`, `LiteralArray(Vec<LiteralValue>)`
- Special: `Void`, `StringNullptr`, `Array { tag: u8, values: Vec<AnnotationValue> }` (`tag` preserves the original element-type tag)

## Literal Arrays & Modules

`LiteralArray` holds `values: Vec<LiteralValue>`. Literal values include:

- Primitives: `Bool`, `Integer8(u8)` (the 12.x `TAGVALUE`/`INTEGER_8` tag), `Integer(u32)`, `Float(f32)`, `Double(f64)`
- `String(StringId)` / `EtsImplements(StringId)` — interned content
- Method references: `Method(u32)`, `GeneratorMethod(u32)`, `AsyncGeneratorMethod(u32)`, `Getter(u32)`, `Setter(u32)` — entity offsets, resolve via `File::resolve_entity_str()`
- `MethodAffiliate(u16)`, `Accessor(u8)`, `BuiltinTypeIndex(u8)`, `NullValue(u8)`
- Nested arrays: `LiteralArray(LiteralArrayIdx)`, `LiteralBufferIndex(LiteralArrayIdx)` — indices into `File::literal_arrays`
- Typed arrays: `ArrayU1(LiteralArrayIdx)`, `ArrayU8`, `ArrayI8`, `ArrayU16`, `ArrayI16`, `ArrayU32`, `ArrayI32`, `ArrayU64`, `ArrayI64`, `ArrayF32`, `ArrayF64`, `ArrayString` — each an index into `File::literal_arrays` holding the element payload

ES module data is encoded as a special literal array. Decode it with:

```rust
let module: ModuleData = file.decode_module(literal_array_index).unwrap();
for req in &module.requests {
    println!("imports from: {req}");
}
for record in &module.records {
    // ModuleRecord::RegularImport, NamespaceImport, LocalExport, etc.
}
```

## Debug Info

`MethodDebugInfo` provides source mapping and local variable information:

- `source_file` / `source_code` — original source
- `line_table: Vec<LineEntry>` — instruction index → line number
- `column_table: Vec<ColumnEntry>` — instruction index → column number
- `local_vars: Vec<LocalVarInfo>` — variable name, type, register, scope range
- `params: Vec<ParamInfo>` — parameter names and signatures

## Types

| Type | Description |
|------|-------------|
| `Type` | Resolved type: `Void`, `Bool`, `I32`, `F64`, `Reference(StringId)`, etc. |
| `AccessFlags` | Bitflags: `PUBLIC`, `STATIC`, `FINAL`, `ABSTRACT`, `SYNTHETIC`, etc. |
| `SourceLang` | `EcmaScript`, `JavaScript`, `TypeScript`, `ArkTs`, `PandaAssembly` |
| `FunctionKind` | `Function`, `AsyncFunction`, `GeneratorFunction`, `ConcurrentFunction`, etc. |

## Re-exported Types

From `abcd-isa`: `Version`, `Bytecode`, `DecodeError` (operand newtypes `Reg`/`Imm`/`EntityId`/`Label` are used with `MethodBody::bytecodes` and come from the `abcd-isa` crate directly).

From `abcd-file-sys`: `FileType`.

From `string_interner`: `StringPool`, `StringId`.

The crate also re-exports its own public model (`model::*`), `decode`, `file_type`, and the builder surface (`Builder`, `encode`, handle types, `CodeEntity`, `CatchBlockDef`, `ModuleRecordDef`, …) — see `src/lib.rs` for the exact list.

## Known Limitations

- Byte-level roundtrip is not possible — the builder computes its own layout, so checksums and offsets will differ. Semantic equivalence is preserved.
- `LiteralValue` method-reference variants (`Method`, `GeneratorMethod`, `Getter`, `Setter`, …) store source-file entity offsets; use `File::resolve_entity_str()` to look them up. On encode, entity references written into literal arrays relocate automatically to the new file's layout.
- `ParamInfo::signature` is not preserved during encode (C++ writer limitation).
