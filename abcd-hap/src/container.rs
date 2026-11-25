//! Container sniffing (`.hap` / `.hsp` / `.hqf` vs `.app`) and the
//! `abc_modules` / `abc_modules_with_limits` extraction entry points.
//!
//! Classification is driven by the *entry set*, never by file extension:
//!
//! - an archive with any `.abc` entry is a module container
//!   (`.hap` / `.hsp` / `.hqf`). `ets/modules.abc` is the first-class entry
//!   when present; otherwise per-ability bytecode (`ets/**/*.abc`) or FA-era
//!   `assets/js/**/*.abc` entries are just as valid — any `.abc` path counts,
//!   the path itself is the module's identity;
//! - otherwise an archive with nested `*.hap` / `*.hsp` entries is an
//!   application package (`.app`);
//! - anything else carries no extractable bytecode.

use crate::Error;
use crate::zip::{Compression, EntryData, EntryMeta, Limits, ZipArchive};

/// Fixed path of the first-class Ark bytecode entry inside a module
/// container. When present it is always extracted first; any other `.abc`
/// entries follow in central-directory order.
pub const MODULE_ABC: &str = "ets/modules.abc";
/// Stage-model module manifest.
pub const MODULE_JSON: &str = "module.json";
/// FA-model (legacy) module manifest.
pub const CONFIG_JSON: &str = "config.json";
/// Quick-fix (hot patch) manifest.
pub const PATCH_JSON: &str = "patch.json";

/// Maximum container nesting depth: `.app` (1) containing `.hap` / `.hsp`
/// (2). Deeper nesting is not traversed, using an explicit iterative heap
/// workstack with zero call-stack recursion.
pub const MAX_CONTAINER_DEPTH: usize = 2;

/// A sniffed container, classified by entry set rather than file extension.
#[derive(Clone, Debug)]
pub enum Container<'a> {
    /// `.hap` / `.hsp` / `.hqf`: an archive carrying at least one `.abc`
    /// entry (`ets/modules.abc`, per-ability `ets/**/*.abc`, FA-era
    /// `assets/js/**/*.abc`, or any other `.abc` path).
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
        if archive.entries().any(|e| is_abc_name(&e.name)) {
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

/// Allocation-free ASCII case-insensitive extension match.
fn has_ascii_ext_ignore_case(name: &str, ext: &[u8]) -> bool {
    let bytes = name.as_bytes();
    bytes.len() >= ext.len() && bytes[bytes.len() - ext.len()..].eq_ignore_ascii_case(ext)
}

/// Entry-name predicate for Ark bytecode: the extension is matched
/// case-insensitively without allocating; the rest of the path is unrestricted.
fn is_abc_name(name: &str) -> bool {
    has_ascii_ext_ignore_case(name, b".abc")
}

/// Entry-name predicate for nested module containers inside an `.app`.
fn is_nested_module_name(name: &str) -> bool {
    has_ascii_ext_ignore_case(name, b".hap") || has_ascii_ext_ignore_case(name, b".hsp")
}

/// Metas of all `.abc` entries: `ets/modules.abc` first when present, the
/// rest in central-directory order.
fn abc_entry_metas<'m, 'a>(archive: &'m ZipArchive<'a>) -> Vec<&'m EntryMeta<'a>> {
    let mut metas: Vec<&EntryMeta<'a>> =
        archive.entries().filter(|e| is_abc_name(&e.name)).collect();
    // Stable sort: modules.abc to the front, CD order preserved otherwise.
    metas.sort_by_key(|e| usize::from(e.name.as_ref() != MODULE_ABC));
    metas
}

/// Names of nested `*.hap` / `*.hsp` entries, in archive order.
fn nested_module_names(archive: &ZipArchive<'_>) -> Vec<String> {
    archive
        .entries()
        .filter(|e| is_nested_module_name(&e.name))
        .map(|e| e.name.as_ref().to_owned())
        .collect()
}

/// One extracted Ark bytecode payload with provenance metadata.
#[derive(Clone, Debug)]
pub struct AbcModule<'a> {
    /// Bytecode payload, ready for an `abcd_file`-style `&[u8]` consumer.
    pub data: EntryData<'a>,
    /// Entry name the payload was read from — the module's identity
    /// (`ets/modules.abc` for the first-class entry, otherwise the full
    /// per-ability path such as `ets/Application/AbilityStage.abc`).
    pub entry_name: String,
    /// How the payload was stored in its container. For STORED payloads the
    /// absolute data offset is exposed as an alignment hint (relative to the
    /// archive the entry was read from — the *nested* archive for `.app`
    /// modules).
    pub compression: Compression,
    /// Raw `module.json` (Stage) or `config.json` (FA) bytes, if present.
    /// The manifest is container-level: when a container yields several
    /// modules, each of them carries a copy.
    pub module_json: Option<EntryData<'a>>,
    /// Raw `patch.json` bytes, present for `.hqf` quick-fix containers.
    pub patch_json: Option<EntryData<'a>>,
    /// Provenance chain of nested entry names from outermost to innermost
    /// (empty for a top-level module container). E.g. `["entry.hap"]` for a
    /// module extracted from `entry.hap` inside an `.app`.
    pub container_path: Vec<String>,
}

impl AbcModule<'_> {
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

/// Read one entry against both `limits.max_entry_bytes` and the running
/// `remaining_total` budget, deducting its uncompressed byte length on success.
fn read_checked<'a>(
    archive: &ZipArchive<'a>,
    meta: &EntryMeta<'_>,
    limits: Limits,
    remaining_total: &mut u64,
) -> Result<EntryData<'a>, Error> {
    let step_limits = Limits {
        max_entry_bytes: limits.max_entry_bytes,
        max_total_bytes: *remaining_total,
    };
    let data = archive.read_entry_with_limits(meta, step_limits)?;
    *remaining_total = remaining_total.saturating_sub(data.as_slice().len() as u64);
    Ok(data)
}

/// Read a named entry against the running `Limits` budget.
fn read_named_checked<'a>(
    archive: &ZipArchive<'a>,
    name: &str,
    limits: Limits,
    remaining_total: &mut u64,
) -> Result<EntryData<'a>, Error> {
    let meta = archive
        .entry(name)
        .ok_or_else(|| Error::EntryNotFound(name.to_string()))?;
    read_checked(archive, meta, limits, remaining_total)
}

/// Read an optional entry if present, `Ok(None)` otherwise.
fn read_optional_checked<'a>(
    archive: &ZipArchive<'a>,
    name: &str,
    limits: Limits,
    remaining_total: &mut u64,
) -> Result<Option<EntryData<'a>>, Error> {
    match archive.entry(name) {
        Some(meta) => Ok(Some(read_checked(archive, meta, limits, remaining_total)?)),
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

/// Extract every `.abc` entry of a module container as its own module
/// (`ets/modules.abc` first, then the rest in central-directory order). The
/// container-level manifests are read once and shared by all modules.
fn extract_modules<'a>(
    archive: &ZipArchive<'a>,
    container_path: Vec<String>,
    force_owned: bool,
    limits: Limits,
    remaining_total: &mut u64,
) -> Result<Vec<AbcModule<'a>>, Error> {
    let module_json = match read_optional_checked(archive, MODULE_JSON, limits, remaining_total)? {
        Some(json) => Some(json),
        None => read_optional_checked(archive, CONFIG_JSON, limits, remaining_total)?,
    };
    let patch_json = read_optional_checked(archive, PATCH_JSON, limits, remaining_total)?;
    let metas = abc_entry_metas(archive);
    let mut out = Vec::with_capacity(metas.len());
    for (idx, meta) in metas.into_iter().enumerate() {
        let data = read_checked(archive, meta, limits, remaining_total)?;
        let compression = archive.entry_compression(meta)?;
        // Additional owned manifest clones (beyond the first module in a
        // nested container) allocate heap copies and are charged to the
        // cumulative total budget.
        if force_owned && idx > 0 {
            let extra_manifest_bytes = module_json
                .as_ref()
                .map_or(0u64, |d| d.as_slice().len() as u64)
                .saturating_add(
                    patch_json
                        .as_ref()
                        .map_or(0u64, |d| d.as_slice().len() as u64),
                );
            if extra_manifest_bytes > *remaining_total {
                return Err(Error::EntryTooLarge {
                    name: meta.name.as_ref().to_owned(),
                });
            }
            *remaining_total -= extra_manifest_bytes;
        }
        out.push(AbcModule {
            data: coerce(data, force_owned),
            entry_name: meta.name.as_ref().to_owned(),
            compression,
            module_json: module_json.clone().map(|d| coerce(d, force_owned)),
            patch_json: patch_json.clone().map(|d| coerce(d, force_owned)),
            container_path: container_path.clone(),
        });
    }
    Ok(out)
}

/// Heap workstack frame for iterative nested container traversal (zero
/// call-stack recursion).
struct PendingContainer {
    bytes: Vec<u8>,
    depth: usize,
    path: Vec<String>,
}

/// Extract every Ark bytecode module from an in-memory container under
/// [`Limits::DEFAULT`].
///
/// - `.hap` / `.hsp` / `.hqf`: one module per `.abc` entry —
///   `ets/modules.abc` first when present, then the remaining entries in
///   central-directory order (per-ability `ets/**/*.abc`, FA-era
///   `assets/js/**/*.abc`, or any other `.abc` path; the entry name is the
///   module's identity).
/// - `.app`: reads each nested `*.hap` / `*.hsp` entry via an explicit
///   iterative heap workstack bounded by [`MAX_CONTAINER_DEPTH`], skipping
///   valid resource-only nested archives that carry zero `.abc` entries while
///   propagating corrupt archive errors.
///
/// Data from nested containers is always owned; top-level STORED entries are
/// zero-copy borrows of `bytes`. Returns [`Error::NoAbcEntry`] when the
/// entire container yields zero `.abc` modules.
pub fn abc_modules(bytes: &[u8]) -> Result<Vec<AbcModule<'_>>, Error> {
    abc_modules_with_limits(bytes, Limits::DEFAULT)
}

/// Extract every Ark bytecode module from an in-memory container under custom
/// resource [`Limits`].
///
/// Enforces `limits.max_entry_bytes` on each entry and tracks cumulative
/// extracted/inflated bytes across the outer archive and all nested
/// `.hap` / `.hsp` archives against `limits.max_total_bytes`.
pub fn abc_modules_with_limits(bytes: &[u8], limits: Limits) -> Result<Vec<AbcModule<'_>>, Error> {
    let mut remaining_total = limits.max_total_bytes;
    let mut out = Vec::new();
    match Container::sniff(bytes)? {
        Container::Module(archive) => {
            out.extend(extract_modules(
                &archive,
                Vec::new(),
                false,
                limits,
                &mut remaining_total,
            )?);
        }
        Container::App { outer, modules } => {
            let mut workstack: Vec<PendingContainer> = Vec::new();
            for top_name in modules {
                let nested_bytes =
                    read_named_checked(&outer, &top_name, limits, &mut remaining_total)?
                        .into_owned();
                workstack.push(PendingContainer {
                    bytes: nested_bytes,
                    depth: 2,
                    path: vec![top_name],
                });
                while let Some(item) = workstack.pop() {
                    if item.depth > MAX_CONTAINER_DEPTH {
                        continue;
                    }
                    let sniffed = match Container::sniff(&item.bytes) {
                        Ok(container) => container,
                        // Resource-only or native-only nested .hsp/.hap modules
                        // inside an .app bundle carry no .abc entries; skip them
                        // cleanly while propagating real archive corruption.
                        Err(Error::NoAbcEntry) => continue,
                        Err(err) => return Err(err),
                    };
                    match sniffed {
                        Container::Module(archive) => {
                            // Per-element push (not extend): each module is
                            // coerced to 'static individually against the
                            // invariant &mut Vec element lifetime.
                            for m in extract_modules(
                                &archive,
                                item.path,
                                true,
                                limits,
                                &mut remaining_total,
                            )? {
                                out.push(m.into_static());
                            }
                        }
                        Container::App {
                            outer: inner_outer,
                            modules: inner_modules,
                        } => {
                            if item.depth < MAX_CONTAINER_DEPTH {
                                let mut children = Vec::with_capacity(inner_modules.len());
                                for child_name in inner_modules {
                                    let child_bytes = read_named_checked(
                                        &inner_outer,
                                        &child_name,
                                        limits,
                                        &mut remaining_total,
                                    )?
                                    .into_owned();
                                    let mut child_path = item.path.clone();
                                    child_path.push(child_name);
                                    children.push(PendingContainer {
                                        bytes: child_bytes,
                                        depth: item.depth + 1,
                                        path: child_path,
                                    });
                                }
                                for child in children.into_iter().rev() {
                                    workstack.push(child);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if out.is_empty() {
        return Err(Error::NoAbcEntry);
    }
    Ok(out)
}
