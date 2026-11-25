//! In-memory, unpack-only reader for OpenHarmony application containers
//! (`.hap`, `.hsp`, `.app`, `.hqf`).
//!
//! Every container in scope is a plain ZIP archive with HarmonyOS-mandated
//! entry names (see `design/hap-container.md`). This crate implements a
//! hand-written central-directory ZIP reader for the restricted dialect the
//! OpenHarmony packing tools produce: no spanned archives, no encryption, no
//! ZIP64, methods {STORED, DEFLATE} only.
//!
//! # Design rules
//!
//! - **Total on arbitrary bytes.** Every index computation goes through
//!   checked slice access and bounded iterative walks; `open()`/`read()` never
//!   panic or recurse on hostile input.
//! - **In-memory only.** Entry names are lookup keys, never filesystem paths,
//!   so no Zip Slip machinery is needed inside the unpacker.
//! - **Zero-copy where possible.** Valid UTF-8 central-directory names borrow
//!   directly into the input buffer (`Cow::Borrowed`), and top-level `STORED`
//!   entries are returned as borrowed slices (`EntryData::Borrowed`).
//! - **Mandatory IEEE CRC-32 & decompression-bomb guards.** Every entry read
//!   verifies its IEEE 802.3 CRC-32 checksum against the central directory and
//!   enforces configurable [`Limits`] alongside the RFC 1951 `1032×` DEFLATE
//!   compression-ratio ceiling before allocation.
//!
//! # Quick start
//!
//! ```no_run
//! let bytes: Vec<u8> = std::fs::read("entry.hap").unwrap();
//! let modules = abcd_hap::abc_modules(&bytes).unwrap();
//! for module in &modules {
//!     println!("{}: {} bytes", module.entry_name, module.data.as_slice().len());
//! }
//! ```

#![forbid(unsafe_code)]
#![deny(missing_docs)]

mod container;
mod error;
mod zip;

pub use container::{
    AbcModule, CONFIG_JSON, Container, MAX_CONTAINER_DEPTH, MODULE_ABC, MODULE_JSON, PATCH_JSON,
    abc_modules, abc_modules_with_limits,
};
pub use error::Error;
pub use zip::{
    Compression, EntryData, EntryMeta, Limits, METHOD_DEFLATE, METHOD_STORED, ZipArchive,
};
