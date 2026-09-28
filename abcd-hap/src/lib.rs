//! In-memory, unpack-only reader for OpenHarmony application containers
//! (`.hap`, `.hsp`, `.app`, `.hqf`).
//!
//! Every container in scope is a plain ZIP archive with HarmonyOS-mandated
//! entry names (see `design/abcd-hap-research.md`). This crate implements a
//! hand-written central-directory ZIP reader for the restricted dialect the
//! OpenHarmony packing tools produce: no spanned archives, no encryption, no
//! ZIP64, methods {STORED, DEFLATE} only.
//!
//! # Design rules
//!
//! - **Total on arbitrary bytes.** Every index computation goes through
//!   checked slice access; `open()`/`read()` never panic on hostile input.
//! - **In-memory only.** Entry names are lookup keys, never filesystem paths,
//!   so no Zip Slip machinery is needed.
//! - **Zero-copy where possible.** STORED entries are returned as borrowed
//!   slices into the caller's buffer; DEFLATE entries are inflated into an
//!   owned `Vec<u8>`.
//! - **No CRC check by default** (the abc payload has its own integrity
//!   story); data is returned regardless of CRC mismatches.
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

mod container;
mod error;
mod zip;

pub use container::{
    AbcModule, CONFIG_JSON, Container, MAX_CONTAINER_DEPTH, MODULE_ABC, MODULE_JSON, PATCH_JSON,
    abc_modules,
};
pub use error::Error;
pub use zip::{Compression, EntryData, EntryMeta, METHOD_DEFLATE, METHOD_STORED, ZipArchive};
