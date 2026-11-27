# abcd-file

Safe Rust API for the ArkCompiler bytecode container format (`.abc`), providing 100% pure Safe Rust zero-copy container reading (eager or lazy `MethodSpan`, strict or forensic mode), low-RSS streaming inspection, offset-relocating re-encoding, programmatic `.abc` construction via `Builder`, and an `ark_disasm`-compatible `pandasm` text disassembler and assembler.

## Purpose & Layering Contract

`abcd-file` sits above [`abcd-file-sys`](../abcd-file-sys/README.md) and [`abcd-isa`](../abcd-isa/README.md), and below `abcd-lift`, `abcd-lower`, and `abcd-cli`:

- Implements the entire `.abc` container reader, header/Adler-32 validator, DWARF/LNP debug decoder, flat-arena `StringPool`, semantic `File -> Vec<u8>` encoder, and `pandasm` emitter/assembler in 100% pure Safe Rust (`#![forbid(unsafe_code)]` / `#![deny(unsafe_code)]`), confining `unsafe` FFI calls solely to the `Builder` writer bridge in `src/encode/builder.rs` (`#![cfg_attr(not(test), deny(clippy::unwrap_used))]`).
- Owns `.abc` container concerns: unified 6-byte CESU-8 / MUTF-8 flat-arena string interning (`#72`, `#77`, including lossless raw MUTF-8 lone-surrogate preservation and droppable SipHash lookup indices), container [`Dialect`] gating across dynamic (`0.0.0.2`, `0.0.0.3`, `9.0.0.0`..`24.0.0.0`, 60B header) and static (`0.0.0.5` 64B, `0.0.0.6` 72B, `0.1.0.7` 72B/60B) headers (`#49`), index-region entity resolution, module/scope/phase/JSON/type-summary metadata decoding and relocation, annotation and literal-array graphs, pure-Rust bounded DWARF / `LineNumberProgram` debug decoding and multi-row emission, and Adler-32 validation/finalization.
- Delegates instruction-level decoding, encoding, and in-place operand patching to `abcd-isa`, while leaving SSA IR lifting, type recovery, and lowering to `abcd-lift` and `abcd-lower`.

## Architecture / Module Map

| Module | Public Surface | Responsibility |
|--------|----------------|----------------|
| `src/lib.rs`, `src/model.rs` | `File`, `Class`, `Method`, `MethodBody`, `MethodCode`, `MethodSpan`, `MethodEntities`, `Field`, `FieldValue`, `EntityRef`, `MethodIdx`, `FieldIdx`, `LiteralArrayIdx`, `Annotation*` | Core owned container model (`File::dialect()`), dual-mode eager `MethodCode::Decoded` vs. zero-copy `MethodCode::Span(MethodSpan)` bodies (`MethodBody::bytecodes()`, `MethodBody::insn_count()`), compact sorted `(EntityKind, u32) -> EntityRef` tables (`MethodEntities`), and lookup helpers (`File::method_by_idx`, `File::field_by_idx`, `File::literal_array_by_offset`) |
| `src/file.rs`, `src/decode/` (`mod.rs`, `items.rs`, `summary.rs`) | `decode`, `decode_arc`, `decode_lazy`, `decode_with_options`, `DecodeMode`, `DecodeOptions`, `DecodeDiagnostic`, `DecodeDiagnostics`, `inspect_summary`, `inspect_summary_zeropadded`, `file_type`, `adler32_abc`, `validate_checksum`, `FileSummary`, `VerifySummary` | Pure Safe Rust `.abc` container reader (`#49`), split across multi-pass orchestration & literal/annotation handle rewriting (`decode/mod.rs`), owned class/method/code/field/annotation item decoders (`decode/items.rs`), and low-RSS SipHash-keyed `SummaryStrings` streaming inspection (`decode/summary.rs`, `#77`) |
| `src/encode/` (`mod.rs`, `builder.rs`) | `encode`, `encode_with_options`, `EncodeOptions`, `Builder`, `AnnotationElemDefEx`, `ModuleRecordDef` | Pure Safe Rust semantic `File -> Vec<u8>` re-encoder (`encode/mod.rs`, streaming transiently over `MethodBody::bytecodes()` so `decode_lazy` models encode bit-identically without upfront materialization) and handle-based FFI `Builder` (`encode/builder.rs`) |
| `src/pandasm/` (`mod.rs`, `insn_ctor.rs`, `parse/{mod.rs, scan.rs, build.rs}`) | `emit_file`, `emit_file_to_writer`, `parse_file`, `parse_file_with_version`, `ParseError` | Pure Safe Rust streaming `ark_disasm`-compatible `.pa` text emitter (`pandasm/mod.rs`) and `.pa` assembler (`parse/scan.rs` string-oracle lexer & section/token scanners, `parse/mod.rs` section parser, `parse/build.rs` semantic model & ISA builder) |
| `src/string_pool.rs` | `StringPool`, `StringId`, `StringPoolOverflow` | Flat-arena (`Arc<Arena>`) string pool (`#72`, `#77`) storing contiguous UTF-8 text + sorted cold raw MUTF-8 lone-surrogate entries, with droppable `RandomState`-keyed `hashbrown::HashTable<u32>` dedup indices (`drop_index`, `has_index`, `lossy_ids`, `try_*`) |
| `src/literal.rs`, `src/module.rs` | `LiteralArray`, `LiteralValue`, `ModuleData`, `ModuleRecord` | Pure Safe Rust bounds-checked tagged literal-array items (`ARRAY_U1`..`ARRAY_STRING`, dense `MethodIdx` / `LiteralArrayIdx` handles, optional `source_offset` provenance) and ECMAScript module records |
| `src/code.rs`, `src/debug.rs`, `src/types.rs`, `src/error.rs` | `TryBlock`, `CatchBlock`, `MethodDebugInfo`, `Dialect`, `Type`, `AccessFlags`, `FunctionKind`, `SourceLang`, `Error` | Exact instruction-boundary exception-handler ranges (`CatchBlock::type_class: Option<StringId>`), pure-Rust row-bounded DWARF/LNP debug tables, container dialect/descriptor/flag types, and structured container errors |

## Key Invariants

- **100% Pure Safe Rust Container Reader & Dual-Mode `MethodCode` (`#49`)**: `src/file.rs`, `src/decode/`, `src/literal.rs`, `src/debug.rs`, `src/string_pool.rs`, and `src/pandasm/` forbid `unsafe_code` and never invoke C++ `abc_file_open*` reader FFI handles. `decode_lazy(Arc<[u8]>)` runs the identical single-pass `Strict` ISA/jump-target/entity/try-catch validation scan as `decode`, then retains compact `MethodCode::Span(MethodSpan)` slices over the shared `Arc<[u8]>` and sorted `MethodEntities` vectors — yielding 100% byte-identical `encode` and `pandasm::emit_file` output without materializing whole-file `Vec<Bytecode>` allocations upfront.
- **`DecodeMode::{Strict, Forensic}`**: `Strict` mode fails loudly on any malformed header, item, string, bytecode, jump target, try/catch boundary, annotation, literal array, or debug table. `Forensic` mode (`decode_with_options`) records structured `DecodeDiagnostic` entries (including Adler-32 checksum mismatches, corrupt debug/LNP streams, malformed annotations/literal arrays, and broken method bodies) while recovering all intact classes and methods.
- **Flat-Arena `StringPool` & SipHash DoS Hardening (`#72`, `#77`)**: `StringPool` packs all valid UTF-8 strings into one contiguous `String` + `offs: Vec<u32>` inside `Arc<Arena>` (plus binary-searched `cold: Vec<Cold>` for lone-surrogate MUTF-8 sequences, normalizing valid MUTF-8 inputs onto the UTF-8 path per `R2-M9`) and guards `< u32::MAX` bounds (`StringPoolOverflow`). Both `StringPool` and `SummaryStrings` key `hashbrown::HashTable<u32>` with `std::hash::RandomState` (SipHash), and `StringPool::drop_index()` frees lookup tables post-decode while keeping `get` / `get_raw_mutf8` total via length-prefiltered arena scans.
- **Offset-decoupled semantic handles & full relocation on `encode` (`#50`)**: Cross-entity references use dense semantic handles (`EntityRef`, `MethodIdx`, `FieldIdx`, `LiteralArrayIdx`, `CatchBlock::type_class: Option<StringId>`), with optional `source_offset: Option<u32>` provenance preserved solely for byte-exact `pandasm` disassembly. Every offset-bearing construct is relocated on `encode`.
- **Zero recursion & iterative traits**: Nested annotations (both scalar `Annotation` and `ArrayAnnotation`), `Annotation` / `AnnotationElem` / `AnnotationValue` `Drop` / `Clone` / `PartialEq` / `Debug` implementations, and nested/cyclic literal-array graphs use explicit heap workstacks so pathological nesting depths cannot overflow a `256 KiB` call stack.

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
