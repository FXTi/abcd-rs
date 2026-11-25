# abcd-file

Safe Rust API for the ArkCompiler bytecode container format (`.abc`), providing eager decoding into an owned semantic model, low-RSS streaming inspection, offset-relocating re-encoding, programmatic `.abc` construction via `Builder`, and an `ark_disasm`-compatible `pandasm` text disassembler and assembler.

## Purpose & Layering Contract

`abcd-file` sits above [`abcd-file-sys`](../abcd-file-sys/README.md) and [`abcd-isa`](../abcd-isa/README.md), and below `abcd-lift`, `abcd-lower`, and `abcd-cli`:

- Confines all `unsafe` FFI calls internally behind RAII guards and documented `// SAFETY:` invariants (`unsafe_op_in_unsafe_fn = "forbid"`, `clippy::undocumented_unsafe_blocks = "deny"`), exposing lifetime-free owned Rust data structures (`File`, `Class`, `Method`, `Field`, `Annotation`, `LiteralArray`, `ModuleData`) and typed `Error` diagnostics (`#![cfg_attr(not(test), deny(clippy::unwrap_used))]`).
- Owns `.abc` container concerns: unified 6-byte CESU-8 / MUTF-8 string-pool interning (including lossless raw MUTF-8 lone-surrogate preservation), container [`Dialect`] gating (`DynamicModern`, `DynamicLegacy`, `Static`), index-region entity resolution, module/scope/phase/JSON/type-summary metadata decoding and relocation, annotation and literal-array graphs, pure-Rust bounded DWARF / `LineNumberProgram` debug decoding and multi-row emission, and Adler-32 finalization.
- Delegates instruction-level decoding, encoding, and in-place operand patching to `abcd-isa`, while leaving SSA IR lifting, type recovery, and lowering to `abcd-lift` and `abcd-lower`.

## Architecture / Module Map

| Module | Public Surface | Responsibility |
|--------|----------------|----------------|
| `src/lib.rs`, `src/model.rs` | `File`, `Class`, `Method`, `Field`, `FieldValue`, `Annotation*` | Core owned container model (`File::dialect()`), entity lookup helpers, and record/field metadata constants |
| `src/decode.rs` | `decode`, `inspect_summary`, `inspect_summary_zeropadded`, `FileSummary`, `VerifySummary` | Eager fallible `.abc` reader (`0.0.0.2` legacy and `9.0.0.0`..`24.0.0.0` dynamic; rejects `0.1.0.7` static on bytecode decode/verify while reporting `Dialect::Static` metadata in `inspect_summary(..., false)`) and low-RSS streaming summary/verifier (`FileSummary::dialect()`), resolving strings, classes, methods, fields, annotations, debug info, and transitive literal-array graphs via iterative workstacks |
| `src/encode.rs` | `encode`, `encode_with_options`, `EncodeOptions`, `Builder`, `AnnotationElemDefEx`, `ModuleRecordDef` | Semantic `File -> Vec<u8>` re-encoder (with optional post-finalize self-check via `EncodeOptions::verify`) and handle-based `Builder`: relocates code entity IDs, module/phase/JSON/scope/type-summary field references, interleaved DWARF line/column/local-var programs, and nested literal arrays (`_ESSlotNumberAnnotation` synced from `MethodBody::ic_size`) |
| `src/pandasm/` | `emit_file`, `emit_file_to_writer`, `parse_file`, `parse_file_with_version`, `ParseError` | Streaming `ark_disasm`-compatible `.pa` text emitter (256-entry `libstdc++` `__prime_list` bucket simulation) and assembler (literals, module arrays, records, methods, catch blocks, multiline quote-bearing strings, and 6-byte CESU-8 / MUTF-8 strings) |
| `src/string_pool.rs` | `StringPool`, `StringId` | Deduplicated dual-bucket string pool supporting valid UTF-8 (with zero-copy MUTF-8 encoding fast path and 6-byte CESU-8 astral pairs) and raw MUTF-8 byte sequences (e.g. unpaired UTF-16 surrogates) |
| `src/literal.rs`, `src/module.rs` | `LiteralArray`, `LiteralValue`, `ModuleData`, `ModuleRecord` | Strictly bounds-checked tagged literal-array items (including nested `LiteralArrayIdx` references) and ECMAScript import/export module records |
| `src/code.rs`, `src/debug.rs`, `src/types.rs`, `src/error.rs` | `TryBlock`, `MethodDebugInfo`, `Dialect`, `Type`, `AccessFlags`, `FunctionKind`, `SourceLang`, `Error` | Exact instruction-boundary exception-handler ranges, pure-Rust bounded DWARF/LNP debug tables, container dialect/descriptor/flag types, and structured container errors |

## Key Invariants

- **Full offset relocation on `encode`**: Byte-identical `.abc` output is not a goal (`ItemContainer` computes fresh item offsets and Adler-32 checksums), so every offset-bearing construct is modeled structurally and relocated on `encode`: bytecode `EntityId` operands, `FieldValue::ModuleData`, `FieldValue::ModuleRequestPhase`, `FieldValue::JsonFileContent`, `FieldValue::LiteralArrayRef` (`scopeNames`, `_ESScopeNamesRecord`, and non-zero `typeSummaryOffset`), annotation entity/array/literal-array values (including 64-bit `I64`/`U64`/`F64` arrays), interleaved `MethodDebugInfo` line/column/local-var tables, and arbitrarily nested or cyclic `LiteralValue::LiteralArray(LiteralArrayIdx)` graphs.
- **Pure-Rust bounded DWARF / LNP decoding (`D2`)**: Both `decode` and `inspect_summary` decode `DebugInfoItem` parameter signatures and `LineNumberProgramItem` opcodes directly from validated `.abc` byte slices in Rust without opening C++ `DebugInfoExtractor`, eliminating whole-file eager C++ debug-table materialization and `LOG(FATAL)` abort surfaces.
- **Unified MUTF-8 / CESU-8 string codec (`D3`)**: Astral scalar values (`U+10000..=U+10FFFF`) are uniformly encoded as 6-byte CESU-8 surrogate pairs (`ED A0..AF 80..BF ED B0..BF 80..BF`) and embedded NUL (`U+0000`) as `C0 80` across `Builder`, `encode`, `decode`, and `pandasm`, while unpaired UTF-16 surrogates round-trip losslessly via `StringPool`'s raw MUTF-8 bucket.
- **Loud errors, zero silent drops**: Corrupt headers, static `0.1.0.7` containers passed to dynamic entry points, duplicate class descriptors, unknown `SourceLang` / `FunctionKind` / `LiteralTag` discriminants, mid-instruction or out-of-bounds try/catch spans, unreadable MUTF-8 strings, truncated annotation/literal arrays, and malformed line-number programs return typed `Err(Error::*)` values without panicking, aborting, or writing to `stdout`/`stderr`.
- **Iterative graph traversal**: Nested annotations and nested/cyclic literal-array graphs are decoded, validated, and encoded with explicit heap workstacks so pathological nesting depths cannot overflow a `256 KiB` call stack.

Note: Upstream `DebugInfoItem` does not serialize `ParamInfo::signature` on `encode` (`ParamInfo::name` round-trips, and `ParamInfo::signature` is reconstructed from the method's `ProtoItem` / class descriptor on `decode`); upstream `ItemContainer` (`ClassItem`, `MethodItem`, `FieldItem`) also folds runtime/type annotation attachment helpers into a single `ANNOTATION` list on serialization.

Design references: [`../design/file-format.md`](../design/file-format.md), [`../design/vendor-sync.md`](../design/vendor-sync.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust,no_run
use abcd_file::{
    AccessFlags, Builder, EncodeOptions, SourceLang, Type, decode, encode_with_options, pandasm,
};

// 1. Decode an existing .abc file, re-encode with full relocation, and emit pandasm text:
let raw = std::fs::read("input.abc")?;
let file = decode(&raw)?;
let rewritten = encode_with_options(&file, EncodeOptions::default())?;
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

Run local unit, integration, lint, documentation, and optional corpus checks without Docker:

```sh
cargo fmt --check -p abcd-file
cargo clippy -p abcd-file --all-targets -- -D warnings
ABCD_CORPUS_ROOT=/nonexistent cargo test -p abcd-file
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p abcd-file
cargo test -p abcd-file --release -- --ignored
```
