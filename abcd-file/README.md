# abcd-file

Safe Rust API for the ArkCompiler bytecode container format (`.abc`), providing eager decoding into an owned semantic model, offset-relocating re-encoding, programmatic `.abc` construction via `Builder`, and an `ark_disasm`-compatible `pandasm` text disassembler and assembler.

## Purpose & Layering Contract

`abcd-file` sits above [`abcd-file-sys`](../abcd-file-sys/README.md) and [`abcd-isa`](../abcd-isa/README.md), and below `abcd-lift`, `abcd-lower`, and `abcd-cli`:

- Confines all `unsafe` FFI calls internally behind RAII guards and documented invariants, exposing lifetime-free owned Rust data structures (`File`, `Class`, `Method`, `Field`, `Annotation`, `LiteralArray`, `ModuleData`) and typed `Error` diagnostics (`#![cfg_attr(not(test), deny(clippy::unwrap_used))]`).
- Owns `.abc` container concerns: string-pool interning (including lossless raw MUTF-8 lone-surrogate preservation), index-region entity resolution, module/scope/phase/JSON/type-summary metadata decoding and relocation, annotation and literal-array graphs, debug line/column/local-var tables, and Adler-32 finalization.
- Delegates instruction-level decoding, encoding, and in-place operand patching to `abcd-isa`, while leaving SSA IR lifting, type recovery, and lowering to `abcd-lift` and `abcd-lower`.

## Architecture / Module Map

| Module | Public Surface | Responsibility |
|--------|----------------|----------------|
| `src/lib.rs`, `src/model.rs` | `File`, `Class`, `Method`, `Field`, `FieldValue`, `Annotation*` | Core owned container model, entity lookup helpers, and record/field metadata constants |
| `src/decode.rs` | `decode` | Eager fallible `.abc` reader (`0.0.0.2` legacy and `9.0.0.0`..`24.0.0.0`), resolving strings, classes, methods, fields, annotations, debug info, and transitive literal-array graphs via iterative workstacks |
| `src/encode.rs` | `encode`, `Builder`, `AnnotationElemDefEx`, `ModuleRecordDef` | Semantic `File -> Vec<u8>` re-encoder and handle-based `Builder`: relocates code entity IDs, module/phase/JSON/scope/type-summary field references, and nested literal arrays (`_ESSlotNumberAnnotation` synced from `MethodBody::ic_size`) |
| `src/pandasm/` | `emit_file`, `parse_file`, `parse_file_with_version`, `ParseError` | `ark_disasm`-compatible `.pa` text emitter and assembler (literals, module arrays, records, methods, catch blocks, and escaped MUTF-8 strings) |
| `src/string_pool.rs` | `StringPool`, `StringId` | Deduplicated dual-bucket string pool supporting both valid UTF-8 and raw MUTF-8 byte sequences (e.g. unpaired UTF-16 surrogates) |
| `src/literal.rs`, `src/module.rs` | `LiteralArray`, `LiteralValue`, `ModuleData`, `ModuleRecord` | Tagged literal-array items (including nested `LiteralArrayIdx` references) and ECMAScript import/export module records |
| `src/code.rs`, `src/debug.rs`, `src/types.rs`, `src/error.rs` | `TryBlock`, `MethodDebugInfo`, `Type`, `AccessFlags`, `FunctionKind`, `SourceLang`, `Error` | Exception-handler ranges, instruction-indexed debug tables, descriptor/flag types, and structured container errors |

## Key Invariants

- **Full offset relocation on `encode`**: Byte-identical `.abc` output is not a goal (`ItemContainer` computes fresh item offsets and Adler-32 checksums), so every offset-bearing construct is modeled structurally and relocated on `encode`: bytecode `EntityId` operands, `FieldValue::ModuleData`, `FieldValue::ModuleRequestPhase`, `FieldValue::JsonFileContent`, `FieldValue::LiteralArrayRef` (`scopeNames`, `_ESScopeNamesRecord`, and non-zero `typeSummaryOffset`), annotation entity/array/literal-array values (including 64-bit `I64`/`U64`/`F64` arrays), and arbitrarily nested or cyclic `LiteralValue::LiteralArray(LiteralArrayIdx)` graphs.
- **Loud errors, zero silent drops**: Corrupt headers, out-of-bounds or mistyped entity offsets, unreadable MUTF-8 strings, truncated annotation arrays, and broken `DebugInfoExtractor` line-number programs return typed `Err(Error::*)` values without panicking, aborting, or writing to `stderr`.
- **Iterative graph traversal**: Nested annotations and nested/cyclic literal-array graphs are decoded, validated, and encoded with explicit heap workstacks so pathological nesting depths cannot overflow the call stack.
- **Format-span fidelity**: `0.0.0.2` files decode through `abcd_isa::decode_legacy`, `<= 12.0.6.0` header literal tables preserve slot ordering in `literal_array_header_offsets` for `pandasm` parity, and `13.x`..`24.0.0.0` index-referenced, annotation-embedded, scope-names, and type-summary literal arrays are collected transitively.

Note: Upstream `DebugInfoItem` does not serialize `ParamInfo::signature` on `encode` (`ParamInfo::name` round-trips).

Design references: [`../design/file-format.md`](../design/file-format.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust,no_run
use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode, encode, pandasm};

// 1. Decode an existing .abc file, re-encode with full relocation, and emit pandasm text:
let raw = std::fs::read("input.abc")?;
let file = decode(&raw)?;
let rewritten = encode(&file)?;
let pa_text = pandasm::emit_file(&file, "input.abc");
let reparsed = pandasm::parse_file_with_version(&pa_text, file.version)?;
assert_eq!(file.classes.len(), reparsed.classes.len());

// 2. Construct a minimal .abc file programmatically with Builder:
let mut b = Builder::new();
b.set_api(12, "beta1");
let cls = b.add_global_class();
b.class_set_source_lang(cls, SourceLang::EcmaScript);
let proto = b.create_proto(Type::Tagged, &[]);
let main_fn = b.class_add_method(
    cls,
    "func_main_0",
    proto,
    AccessFlags::PUBLIC | AccessFlags::STATIC,
    &[0x65], // returnundefined
    0,
    0,
);
b.method_set_source_lang(main_fn, SourceLang::EcmaScript);
b.deduplicate();
let built_bytes = b.finalize()?;
assert_eq!(decode(&built_bytes)?.classes.len(), 1);
# let _ = rewritten;
# Ok::<(), abcd_file::Error>(())
```

## Verification

Run local unit, integration, lint, and documentation checks without Docker:

```sh
./scripts/test-local.sh crate abcd-file
cargo test -p abcd-isa-sys -p abcd-file-sys -p abcd-file
cargo clippy -p abcd-isa-sys -p abcd-file-sys -p abcd-file --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-file-sys -p abcd-file --no-deps
```
