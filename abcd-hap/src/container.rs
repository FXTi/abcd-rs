//! Container sniffing (`.hap` / `.hsp` / `.hqf` vs `.app`) and the
//! `abc_modules` extraction entry point.
//!
//! Classification is driven by the *entry set*, never by file extension:
//!
//! - an archive with an `ets/modules.abc` entry is a module container
//!   (`.hap` / `.hsp` / `.hqf`);
//! - otherwise an archive with nested `*.hap` / `*.hsp` entries is an
//!   application package (`.app`);
//! - anything else carries no extractable bytecode.

use crate::Error;
use crate::zip::{Compression, EntryData, ZipArchive};

/// Fixed path of the Ark bytecode entry inside a module container.
pub const MODULE_ABC: &str = "ets/modules.abc";
/// Stage-model module manifest.
pub const MODULE_JSON: &str = "module.json";
/// FA-model (legacy) module manifest.
pub const CONFIG_JSON: &str = "config.json";
/// Quick-fix (hot patch) manifest.
pub const PATCH_JSON: &str = "patch.json";

/// Maximum container nesting depth: `.app` (1) containing `.hap` / `.hsp`
/// (2). Deeper nesting is not recursed into.
pub const MAX_CONTAINER_DEPTH: usize = 2;

/// A sniffed container, classified by entry set rather than file extension.
#[derive(Clone, Debug)]
pub enum Container<'a> {
    /// `.hap` / `.hsp` / `.hqf`: a single-module archive carrying
    /// `ets/modules.abc`.
    Module(ZipArchive<'a>),
    /// `.app`: an outer archive with nested `*.hap` / `*.hsp` entries.
    App {
        /// The outer archive.
        outer: ZipArchive<'a>,
        /// Names of nested module entries, in archive order.
        modules: Vec<String>,
    },
}

impl<'a> Container<'a> {
    /// Open and classify an in-memory container.
    pub fn sniff(bytes: &'a [u8]) -> Result<Self, Error> {
        Self::from_archive(ZipArchive::open(bytes)?)
    }

    /// Classify an already-open archive.
    pub fn from_archive(archive: ZipArchive<'a>) -> Result<Self, Error> {
        if archive.entry(MODULE_ABC).is_some() {
            return Ok(Container::Module(archive));
        }
        let modules = nested_module_names(&archive);
        if !modules.is_empty() {
            return Ok(Container::App {
                outer: archive,
                modules,
            });
        }
        Err(Error::NoAbcEntry)
    }
}

/// Names of nested `*.hap` / `*.hsp` entries, in archive order.
fn nested_module_names(archive: &ZipArchive<'_>) -> Vec<String> {
    archive
        .entries()
        .filter(|e| {
            let lower = e.name.to_ascii_lowercase();
            lower.ends_with(".hap") || lower.ends_with(".hsp")
        })
        .map(|e| e.name.clone())
        .collect()
}

/// One extracted `ets/modules.abc` payload with provenance metadata.
#[derive(Clone, Debug)]
pub struct AbcModule<'a> {
    /// Bytecode payload, ready for an `abcd_file`-style `&[u8]` consumer.
    pub data: EntryData<'a>,
    /// Entry name the payload was read from (normally `ets/modules.abc`).
    pub entry_name: String,
    /// How the payload was stored in its container. For STORED payloads the
    /// absolute data offset is exposed as an alignment hint (relative to the
    /// archive the entry was read from — the *nested* archive for `.app`
    /// modules).
    pub compression: Compression,
    /// Raw `module.json` (Stage) or `config.json` (FA) bytes, if present.
    pub module_json: Option<EntryData<'a>>,
    /// Raw `patch.json` bytes, present for `.hqf` quick-fix containers.
    pub patch_json: Option<EntryData<'a>>,
    /// Provenance chain of nested entry names from outermost to innermost
    /// (empty for a top-level module container). E.g. `["entry.hap"]` for a
    /// module extracted from `entry.hap` inside an `.app`.
    pub container_path: Vec<String>,
}

impl<'a> AbcModule<'a> {
    /// Lift into an `'static` module by owning all payloads (used when the
    /// backing bytes of a nested container do not outlive the call).
    fn into_static(self) -> AbcModule<'static> {
        AbcModule {
            data: self.data.into_static(),
            entry_name: self.entry_name,
            compression: self.compression,
            module_json: self.module_json.map(EntryData::into_static),
            patch_json: self.patch_json.map(EntryData::into_static),
            container_path: self.container_path,
        }
    }
}

/// Read an entry if present, `Ok(None)` otherwise.
fn read_optional<'a>(archive: &ZipArchive<'a>, name: &str) -> Result<Option<EntryData<'a>>, Error> {
    match archive.entry(name) {
        Some(meta) => Ok(Some(archive.read_entry(meta)?)),
        None => Ok(None),
    }
}

/// Force owned payloads when extracting from a nested container whose
/// backing bytes are dropped on return.
fn coerce<'a>(data: EntryData<'a>, force_owned: bool) -> EntryData<'a> {
    if force_owned {
        EntryData::Owned(data.into_owned())
    } else {
        data
    }
}

/// Extract the single module of a module container.
fn extract_module<'a>(
    archive: &ZipArchive<'a>,
    container_path: Vec<String>,
    force_owned: bool,
) -> Result<AbcModule<'a>, Error> {
    let meta = archive.entry(MODULE_ABC).ok_or(Error::NoAbcEntry)?;
    let data = archive.read_entry(meta)?;
    let compression = archive.entry_compression(meta)?;
    let module_json = match read_optional(archive, MODULE_JSON)? {
        Some(json) => Some(json),
        None => read_optional(archive, CONFIG_JSON)?,
    };
    let patch_json = read_optional(archive, PATCH_JSON)?;
    Ok(AbcModule {
        data: coerce(data, force_owned),
        entry_name: meta.name.clone(),
        compression,
        module_json: module_json.map(|d| coerce(d, force_owned)),
        patch_json: patch_json.map(|d| coerce(d, force_owned)),
        container_path,
    })
}

/// Recurse into a nested container. All payloads are owned, so the results
/// are `'static` and slot into any output vector regardless of the backing
/// bytes' lifetime.
fn collect_nested<'a>(
    bytes: &[u8],
    depth: usize,
    path: &mut Vec<String>,
    out: &mut Vec<AbcModule<'a>>,
) -> Result<(), Error> {
    if depth > MAX_CONTAINER_DEPTH {
        return Ok(());
    }
    match Container::sniff(bytes)? {
        Container::Module(archive) => {
            out.push(extract_module(&archive, path.clone(), true)?.into_static());
        }
        Container::App { outer, modules } => {
            for name in &modules {
                let nested = outer.read(name)?.into_owned();
                path.push(name.clone());
                collect_nested(&nested, depth + 1, path, out)?;
                path.pop();
            }
        }
    }
    Ok(())
}

/// Extract every Ark bytecode module from an in-memory container.
///
/// - `.hap` / `.hsp` / `.hqf`: returns the single `ets/modules.abc`.
/// - `.app`: reads each nested `*.hap` / `*.hsp` entry (inflating as
///   needed — nested modules are DEFLATED by the upstream packer), re-parses
///   it, and flattens the results with provenance. Nesting deeper than
///   [`MAX_CONTAINER_DEPTH`] is not recursed into.
///
/// Data from nested containers is always owned; top-level STORED entries are
/// zero-copy borrows of `bytes`. Returns [`Error::NoAbcEntry`] when the
/// container yields no bytecode at all.
pub fn abc_modules(bytes: &[u8]) -> Result<Vec<AbcModule<'_>>, Error> {
    let mut out = Vec::new();
    match Container::sniff(bytes)? {
        Container::Module(archive) => {
            out.push(extract_module(&archive, Vec::new(), false)?);
        }
        Container::App { outer, modules } => {
            for name in &modules {
                let nested = outer.read(name)?.into_owned();
                let mut path = vec![name.clone()];
                collect_nested(&nested, 2, &mut path, &mut out)?;
            }
        }
    }
    if out.is_empty() {
        return Err(Error::NoAbcEntry);
    }
    Ok(out)
}
