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
    println!("{descriptor} ({} methods, {} fields)", class.methods.len(), class.fields.len());
    for method in &class.methods {
        if let Some(ref body) = method.body {
            println!("  {} — {} instructions", method.name, body.bytecodes.len());
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
| `classes` | `BTreeMap<String, Class>` | Classes keyed by descriptor (e.g. `"L_GLOBAL;"`) |
| `literal_arrays` | `Vec<LiteralArray>` | Literal arrays indexed by position |
| `entity_map` | `HashMap<u32, String>` | Entity offset → name/descriptor |

Navigation methods on `File`:

- `class(descriptor)` — look up a class by descriptor
- `all_methods()` — flat iterator over `(class_descriptor, &Method)` pairs
- `resolve_entity(offset)` — resolve a bytecode `EntityId` to its name/descriptor
- `literal_array(index)` — get a literal array by index
- `decode_module(index)` — decode ES module data from a literal array

## Classes, Methods, Fields

Each `Class` contains `methods: Vec<Method>`, `fields: Vec<Field>`, and `annotations: Annotations`. Convenience lookups: `method_by_name()`, `field_by_name()`, `super_class_in(&file)`.

`Method` carries `body: Option<MethodBody>` (bytecodes + try-catch blocks), `debug: Option<MethodDebugInfo>`, typed `arg_types`/`return_type`, and annotations.

`Field` has `type_descriptor` (raw descriptor string), optional `initial_value`, and annotations.

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

Each `Annotation` has a `class_descriptor` and `elements: Vec<AnnotationElem>`. Element values are fully typed via `AnnotationValue`:

- Primitives: `Bool`, `I8`/`U8`, `I16`/`U16`, `I32`/`U32`, `I64`/`U64`, `F32`/`F64`
- Resolved references: `String(String)`, `Record(String)`, `Method(String)`, `Enum(String)`
- Unresolved entity offsets: `Annotation(u32)`, `MethodHandle(u32)`, `LiteralArray(u32)` — resolve via `File::resolve_entity()`
- Special: `Void`, `StringNullptr`, `Array { tag, count, entity_offset }`

## Literal Arrays & Modules

`LiteralArray` holds `values: Vec<LiteralValue>`. Literal values include:

- Primitives: `Bool`, `Integer`, `Float`, `Double`
- `String(String)` — decoded MUTF-8 content
- Method references: `Method(u32)`, `GeneratorMethod(u32)`, `Getter(u32)`, `Setter(u32)` — entity offsets, resolve via `File::resolve_entity()`
- `MethodAffiliate(u16)`, `Accessor(u8)`, `LiteralArray(u32)`, `LiteralBufferIndex(u32)`
- Typed arrays: `ArrayU1(u32)`, `ArrayI8(u32)`, ..., `ArrayString(u32)` — entity offsets to array data

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
| `Type` | Resolved type: `Void`, `Bool`, `I32`, `F64`, `Reference(String)`, etc. |
| `AccessFlags` | Bitflags: `PUBLIC`, `STATIC`, `FINAL`, `ABSTRACT`, `SYNTHETIC`, etc. |
| `SourceLang` | `EcmaScript`, `JavaScript`, `TypeScript`, `ArkTs`, `PandaAssembly` |
| `FunctionKind` | `Function`, `AsyncFunction`, `GeneratorFunction`, `ConcurrentFunction`, etc. |

## Re-exported Types

From `abcd-isa`: `Version`, `Bytecode`, `DecodeError`, `Reg`, `Imm`, `EntityId`, `Label`.

From `abcd-file-sys`: `FileType`.

## Known Limitations

- Byte-level roundtrip is not possible — the builder computes its own layout, so checksums and offsets will differ. Semantic equivalence is preserved.
- `AnnotationValue::Annotation`, `MethodHandle`, and `LiteralArray` variants store raw entity offsets that are not automatically resolved during decode. Use `File::resolve_entity()` to look them up.
- `LiteralValue` method variants (`Method`, `Getter`, `Setter`, etc.) also store raw entity offsets.
- `ParamInfo::signature` is not preserved during encode (C++ writer limitation).
