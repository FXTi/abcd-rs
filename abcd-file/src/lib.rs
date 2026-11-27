//! Safe Rust API for the ArkCompiler bytecode file format.
//!
//! This crate reads, writes, and inspects `.abc` (ArkCompiler Bytecode) files
//! used by HarmonyOS / OpenHarmony for JavaScript, TypeScript, and ArkTS.
//!
//! # Quick Start
//!
//! ```no_run
//! use abcd_file::{decode, encode, File};
//!
//! // Decode
//! let data: Vec<u8> = std::fs::read("input.abc").unwrap();
//! let file: File = decode(&data).unwrap();
//!
//! for (desc_id, class) in &file.classes {
//!     let desc = file.strings.resolve(*desc_id).unwrap();
//!     println!("{desc}: {} methods", class.methods.len());
//! }
//!
//! // Re-encode (semantic roundtrip)
//! let output = encode(&file).unwrap();
//! std::fs::write("output.abc", &output).unwrap();
//! ```
//!
//! # Core Types
//!
//! - [`File`] / [`Dialect`] — fully-decoded ABC file, container dialect classification (`DynamicModern`, `DynamicLegacy`, `Static`), classes, and literal arrays
//! - [`EntityRef`] / [`MethodIdx`] / [`FieldIdx`] / [`LiteralArrayIdx`] — container-independent dense entity handles decoupling model consumers from raw `.abc` file offsets
//! - [`Class`] / [`Method`] / [`Field`] — class hierarchy with access flags and annotations
//! - [`MethodBody`] / [`MethodCode`] / [`MethodSpan`] / [`MethodEntities`] — dual-mode eager or zero-copy lazy bytecode bodies and compact sorted `(EntityKind, u32) -> EntityRef` tables
//! - [`DecodeMode`] / [`DecodeOptions`] / [`DecodeDiagnostic`] / [`decode_arc`] / [`decode_lazy`] / [`decode_with_options`] — strict vs. forensic container decoding and zero-copy lazy method spans
//! - [`Annotations`] / [`AnnotationValue`] — four retention policies, fully-typed values
//! - [`LiteralArray`] / [`LiteralValue`] — literal data (strings, methods, typed arrays)
//! - [`ModuleData`] / [`ModuleRecord`] — ES module import/export declarations
//! - [`MethodDebugInfo`] — source mapping, local variables, and parameter info decoded via a pure-Rust bounded DWARF/LNP state machine
//! - [`StringPool`] / [`StringPoolOverflow`] — flat-arena lossless MUTF-8 / UTF-8 string interner with droppable SipHash lookup indices (`drop_index`) and canonical `es2abc` MUTF-8 emission
//! - [`EncodeOptions`] / [`encode_with_options`] / [`Builder`] — configurable re-encoding and programmatic ABC file construction
//!
//! # Safety
//!
//! All public types are safe, owned structs with no lifetimes.
//! The `.abc` container reader, header/checksum validator, DWARF/LNP decoder,
//! `StringPool`, and `pandasm` emitter/assembler are 100% pure Safe Rust
//! (`#![forbid(unsafe_code)]`); `unsafe` is confined solely to the `Builder`
//! FFI writer bridge in `src/encode/builder.rs` calling [`abcd_file_sys`].

#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub use abcd_file_sys::FileType;
pub use abcd_isa::Version;

pub mod string_pool;
pub use string_pool::{StringId, StringPool, StringPoolOverflow};

mod error;
pub use error::Error;

mod types;
pub use types::{AccessFlags, Dialect, FunctionKind, HasAccessFlags, SourceLang, Type};

mod model;
pub use model::*;

mod decode;
pub use decode::{
    DecodeDiagnostic, DecodeDiagnostics, DecodeMode, DecodeOptions, FileSummary, VerifySummary,
    decode, decode_arc, decode_lazy, decode_with_options, inspect_summary,
    inspect_summary_zeropadded,
};
// V-I1 vendor-name pins: compared against the vendor's own constants by
// tests/file-sys-file/main.rs (via the bridge's abc_vendor_* exports) or
// behaviorally pinned in tests/module_record_fields.rs.
pub use decode::{
    ES_MODULE_RECORD_DESCRIPTOR, ES_SCOPE_NAMES_RECORD_DESCRIPTOR, JSON_FILE_CONTENT_FIELD,
    MODULE_RECORD_IDX_FIELD, MODULE_REQUEST_PHASE_FIELD, SCOPE_NAMES_FIELD,
    TYPE_SUMMARY_OFFSET_FIELD,
};

// Internal modules (data types re-exported via model).
mod annotation;
mod code;
mod debug;
pub(crate) mod file;
pub use file::{adler32_abc, file_type, validate_checksum};
mod literal;
mod module;

pub mod pandasm;

mod encode;
pub use encode::{
    AnnotationElemDef, AnnotationElemDefEx, AnnotationElemValue, AnnotationHandle, Builder,
    CatchBlockDef, ClassHandle, CodeEntity, CodeHandle, DebugInfoHandle, EncodeOptions,
    FieldHandle, LiteralArrayHandle, LnpHandle, MethodHandle, MethodHandleItemHandle,
    ModuleRecordDef, ParamHandle, ProtoHandle, StringHandle, encode, encode_with_options,
};
