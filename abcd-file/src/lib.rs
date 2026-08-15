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
//! - [`File`] — fully-decoded ABC file with classes, literal arrays, and entity map
//! - [`Class`] / [`Method`] / [`Field`] — class hierarchy with access flags and annotations
//! - [`MethodBody`] — decoded bytecodes ([`Bytecode`]) and try-catch blocks
//! - [`Annotations`] / [`AnnotationValue`] — four retention policies, fully-typed values
//! - [`LiteralArray`] / [`LiteralValue`] — literal data (strings, methods, typed arrays)
//! - [`ModuleData`] / [`ModuleRecord`] — ES module import/export declarations
//! - [`MethodDebugInfo`] — source mapping, local variables, parameter info
//! - [`Builder`] — programmatic ABC file construction via handle-based API
//!
//! # Safety
//!
//! All public types are safe, owned structs with no lifetimes.
//! `unsafe` is confined to internal FFI calls into [`abcd_file_sys`].

pub use abcd_file_sys::FileType;
pub use abcd_isa::Version;
pub use string_interner::{DefaultStringInterner as StringPool, DefaultSymbol as StringId};

mod error;
pub use error::Error;

mod types;
pub use types::{AccessFlags, FunctionKind, HasAccessFlags, SourceLang, Type};

mod model;
pub use model::*;

mod decode;
pub use decode::decode;

// Internal modules (data types re-exported via model).
mod annotation;
mod code;
mod debug;
pub(crate) mod file;
mod literal;
mod module;

mod encode;
pub use encode::{Builder, encode};
