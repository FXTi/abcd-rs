//! Pure Safe Rust `.abc` decoder (`decode`, `decode_arc`, `decode_lazy`,
//! `decode_with_options`) and low-RSS streaming inspector (`inspect_summary`,
//! `inspect_summary_zeropadded`) (`#49`, `#72`, `#77`).

#![forbid(unsafe_code)]

mod items;
mod summary;

pub use summary::{FileSummary, VerifySummary, inspect_summary, inspect_summary_zeropadded};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use abcd_file_sys as sys;

use crate::error::Error;
use crate::file::{AbcReader, RawClass, RawField, RawMethod, StringItemCache};
use crate::literal::{decode_literal_array_values, walk_raw_literal_array};
use crate::model::*;
use crate::types::{AccessFlags, Dialect, FunctionKind, SourceLang};
use crate::{StringId, StringPool};

use items::{
    decode_annotation_list, decode_field_item, decode_method_item, read_class_descriptor_cached,
};
use summary::CompactU32Set;

pub(super) const ABSENT: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Public DecodeMode, DecodeOptions, & DecodeDiagnostics (`#49`)
// ---------------------------------------------------------------------------

/// Error-handling policy for `.abc` decoding (`#49`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum DecodeMode {
    /// Fail loudly on any corrupt header, debug/LNP table, annotation, literal
    /// array, or method body (default; mandatory for `rewrite` / `verify`).
    #[default]
    Strict,
    /// Best-effort recovery for packed/hardened/stripped `.abc` samples:
    /// records checksum mismatches, corrupt LNP tables, broken annotations or
    /// literal arrays, and malformed decoy method bodies into
    /// [`DecodeDiagnostics`] while continuing to decode all healthy items.
    Forensic,
}

/// Configuration for [`decode_with_options`] (`#49`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct DecodeOptions {
    pub mode: DecodeMode,
    /// When `true`, validates each method's instruction stream, try/catch PCs,
    /// and entity/literal-array operands in a single streaming pass, then drops
    /// the temporary `Vec<Bytecode>` and stores a compact zero-copy
    /// [`MethodCode::Span`] referencing the input `Arc<[u8]>`.
    pub lazy_code: bool,
}

/// Structured diagnostic emitted in [`DecodeMode::Forensic`] when a corrupt
/// region is skipped or degraded (`#49`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodeDiagnostic {
    pub kind: &'static str,
    pub offset: Option<u32>,
    pub message: String,
}

/// Ordered list of forensic decode diagnostics (`N20`-deterministic).
pub type DecodeDiagnostics = Vec<DecodeDiagnostic>;

// ---------------------------------------------------------------------------
// Vendor Metadata Name Constants (`V-I1`)
// ---------------------------------------------------------------------------

/// Descriptor of the record class whose u32 fields reference module-record blobs.
pub const ES_MODULE_RECORD_DESCRIPTOR: &str = "L_ESModuleRecord;";
/// Descriptor of the record class whose u32 fields reference scope-names literal arrays.
pub const ES_SCOPE_NAMES_RECORD_DESCRIPTOR: &str = "L_ESScopeNamesRecord;";
/// Name of the u32 field on a `--merge-abc` module record class referencing `ModuleData`.
pub const MODULE_RECORD_IDX_FIELD: &str = "moduleRecordIdx";
/// Name of the u32 field on a `--merge-abc` module record class referencing scope names.
pub const SCOPE_NAMES_FIELD: &str = "scopeNames";
/// Name of the u32 field on a `--merge-abc` JSON module record class referencing JSON text.
pub const JSON_FILE_CONTENT_FIELD: &str = "jsonFileContent";
/// Name of the u32 field referencing a `ModuleLazyImportFlagAccessor` phase blob.
pub const MODULE_REQUEST_PHASE_FIELD: &str = "moduleRequestPhaseIdx";
/// Name of the u32 field referencing a tagged type-summary literal array when non-zero.
pub const TYPE_SUMMARY_OFFSET_FIELD: &str = "typeSummaryOffset";

// ---------------------------------------------------------------------------
// Dialect & Flag Helpers
// ---------------------------------------------------------------------------

#[inline]
pub(super) fn decode_source_lang(raw: Option<u8>) -> Result<SourceLang, Error> {
    match raw {
        None | Some(u8::MAX) => Ok(SourceLang::PandaAssembly),
        Some(v) => SourceLang::try_from(v),
    }
}

/// Decode the 8-bit `panda_file::FunctionKind` stored in `access_flags_` bits `8..15`.
#[inline]
pub(super) fn decode_function_kind_from_flags(raw_flags: u32) -> Result<FunctionKind, Error> {
    let raw = ((raw_flags >> 8) & 0xFF) as u8;
    if let Ok(kind) = FunctionKind::try_from(raw) {
        return Ok(kind);
    }
    let sendable = sys::FunctionKind_SENDABLE_FUNCTION;
    if (raw & !0x07) == sendable {
        let base = raw & 0x07;
        if base == sys::FunctionKind_FUNCTION {
            return Ok(FunctionKind::SendableFunction);
        }
        if base != sys::FunctionKind_CONCURRENT_FUNCTION
            && let Ok(kind) = FunctionKind::try_from(base)
        {
            return Ok(kind);
        }
    }
    Err(Error::UnknownFunctionKind(raw))
}

#[inline]
pub(super) fn check_supported_dialect(
    file_type: sys::FileType,
    version: abcd_isa::Version,
) -> Result<Dialect, Error> {
    match Dialect::from_header(file_type, version) {
        Some(Dialect::Static) | None => Err(Error::Malformed {
            field: "file_type",
            context: format!("static .abc container (version {version}) is not supported"),
        }),
        Some(d) => Ok(d),
    }
}

/// Legacy (`0.0.0.2`) literal-array global table `(num_literalarrays, literalarray_idx_off)`.
pub(super) fn legacy_literalarray_table(data: &[u8]) -> Option<(u32, u32)> {
    let read = |off: usize| -> Option<u32> {
        let bytes: [u8; 4] = data.get(off..off.checked_add(4)?)?.try_into().ok()?;
        Some(u32::from_le_bytes(bytes))
    };
    let count = read(44)?;
    let table_off = read(48)?;
    let byte_len = count.checked_mul(4)?;
    let end = usize::try_from(table_off.checked_add(byte_len)?).ok()?;
    if end > data.len() {
        return None;
    }
    Some((count, table_off))
}

// ---------------------------------------------------------------------------
// Public `decode*` Entry Points
// ---------------------------------------------------------------------------

/// Decode an `.abc` file from raw bytes in [`DecodeMode::Strict`] with eager
/// [`MethodCode::Decoded`] instruction vectors.
pub fn decode(data: &[u8]) -> Result<File, Error> {
    let opts = DecodeOptions {
        mode: DecodeMode::Strict,
        lazy_code: false,
    };
    let (file, _) = decode_core(data, None, &opts)?;
    Ok(file)
}

/// Decode an `.abc` file from a shared `Arc<[u8]>` in [`DecodeMode::Strict`]
/// with eager [`MethodCode::Decoded`] instruction vectors (`#49`).
pub fn decode_arc(data: Arc<[u8]>) -> Result<File, Error> {
    let opts = DecodeOptions {
        mode: DecodeMode::Strict,
        lazy_code: false,
    };
    let (file, _) = decode_core(&data, Some(&data), &opts)?;
    Ok(file)
}

/// Decode an `.abc` file from a shared `Arc<[u8]>` in [`DecodeMode::Strict`]
/// with lazy zero-copy [`MethodCode::Span`] method bodies (`#49`).
///
/// Performs full single-pass ISA, try/catch PC, entity-operand, and debug
/// validation identical to [`decode`], then drops each method's temporary
/// `Vec<Bytecode>` immediately.
pub fn decode_lazy(data: Arc<[u8]>) -> Result<File, Error> {
    let opts = DecodeOptions {
        mode: DecodeMode::Strict,
        lazy_code: true,
    };
    let (file, _) = decode_core(&data, Some(&data), &opts)?;
    Ok(file)
}

/// Decode an `.abc` file under explicit [`DecodeOptions`], returning the
/// decoded [`File`] and any [`DecodeDiagnostics`] recorded in
/// [`DecodeMode::Forensic`] (`#49`).
pub fn decode_with_options(
    data: Arc<[u8]>,
    opts: &DecodeOptions,
) -> Result<(File, DecodeDiagnostics), Error> {
    decode_core(&data, Some(&data), opts)
}

// ---------------------------------------------------------------------------
// Core Pure-Rust Container Decoder
// ---------------------------------------------------------------------------

pub(super) struct RawEntityOp {
    kind: abcd_isa::EntityKind,
    raw_id: u32,
    mnemonic: &'static str,
}

pub(super) struct RawLegacyBufOp {
    global_idx: i64,
    mnemonic: &'static str,
}

pub(super) struct PendingMethodOps {
    method_off: u32,
    entity_ops: Vec<RawEntityOp>,
    legacy_buf_ops: Vec<RawLegacyBufOp>,
}

struct StagedClass<'a> {
    class_off: u32,
    descriptor: StringId,
    descriptor_str: String,
    is_external: bool,
    raw_cls: Option<RawClass<'a>>,
    raw_fields: Vec<RawField>,
    raw_methods: Vec<RawMethod>,
}

fn decode_core(
    data: &[u8],
    backing: Option<&Arc<[u8]>>,
    opts: &DecodeOptions,
) -> Result<(File, DecodeDiagnostics), Error> {
    let forensic = opts.mode == DecodeMode::Forensic;
    let mut diagnostics = DecodeDiagnostics::new();

    let reader = AbcReader::open(data)?;
    let version = reader.version();
    let file_type = reader.file_type();
    let dialect = check_supported_dialect(file_type, version)?;
    let legacy = dialect == Dialect::DynamicLegacy;

    if forensic {
        let expected_crc = reader.checksum();
        let computed_crc = reader.compute_checksum();
        if expected_crc != computed_crc {
            diagnostics.push(DecodeDiagnostic {
                kind: "checksum",
                offset: Some(8),
                message: format!(
                    "header Adler-32 checksum mismatch: expected {expected_crc:#010x}, computed {computed_crc:#010x}"
                ),
            });
        }
    }

    let legacy_lit_table = if legacy {
        legacy_literalarray_table(reader.bytes())
    } else {
        None
    };
    let checksum = reader.checksum();
    let size = reader.file_size();

    let owned_backing_storage: Option<Arc<[u8]>> = if opts.lazy_code && backing.is_none() {
        Some(Arc::from(reader.bytes()))
    } else {
        None
    };
    let lazy_backing: Option<&Arc<[u8]>> = if opts.lazy_code {
        backing.or(owned_backing_storage.as_ref())
    } else {
        None
    };

    let mut strings = StringPool::new();
    let mut str_cache = StringItemCache::new();

    // Pass 1: class/method/field header scan building `entity_map` and caching
    // parsed `RawClass` / `RawField` / `RawMethod` descriptors.
    let mut entity_map: HashMap<u32, StringId> = HashMap::new();
    let num_classes = reader.num_classes();
    let mut staged_classes = Vec::with_capacity(num_classes.min((size / 4) as usize));

    for i in 0..num_classes {
        let class_off = reader.class_off_by_idx(i).unwrap_or(ABSENT);
        if class_off == ABSENT {
            let err = Error::InvalidOffset(class_off);
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "class",
                    offset: None,
                    message: err.to_string(),
                });
                continue;
            }
            return Err(err);
        }
        if reader.is_external(class_off) {
            if let Some(sid) = str_cache.intern_lossy(&reader, class_off, &mut strings) {
                entity_map.insert(class_off, sid);
                staged_classes.push(StagedClass {
                    class_off,
                    descriptor: sid,
                    descriptor_str: String::new(),
                    is_external: true,
                    raw_cls: None,
                    raw_fields: Vec::new(),
                    raw_methods: Vec::new(),
                });
            }
            continue;
        }

        let Some(raw_cls) = reader.open_class(class_off) else {
            let err = Error::InvalidOffset(class_off);
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "class",
                    offset: Some(class_off),
                    message: err.to_string(),
                });
                continue;
            }
            return Err(err);
        };

        let Some((desc_sid, descriptor_str)) =
            read_class_descriptor_cached(&reader, class_off, &mut str_cache, &mut strings)
        else {
            continue;
        };
        entity_map.insert(class_off, desc_sid);

        let (raw_fields, raw_methods) = match reader.enumerate_class_members(&raw_cls) {
            Ok(pair) => pair,
            Err(()) => {
                let err = Error::Malformed {
                    field: "class_members",
                    context: format!("class_members enumeration failed at offset {class_off:#x}"),
                };
                if forensic {
                    diagnostics.push(DecodeDiagnostic {
                        kind: "class",
                        offset: Some(class_off),
                        message: err.to_string(),
                    });
                    continue;
                }
                return Err(err);
            }
        };

        // Match Pass-1 interning order: methods first, then fields.
        for m in &raw_methods {
            if let Some(sid) = str_cache.intern_method_name(&reader, m.name_off, &mut strings) {
                entity_map.insert(m.offset, sid);
            }
        }
        for fl in &raw_fields {
            if fl.name_off != ABSENT
                && let Some(sid) = str_cache.intern_lossy(&reader, fl.name_off, &mut strings)
            {
                entity_map.insert(fl.offset, sid);
            }
        }

        staged_classes.push(StagedClass {
            class_off,
            descriptor: desc_sid,
            descriptor_str,
            is_external: false,
            raw_cls: Some(raw_cls),
            raw_fields,
            raw_methods,
        });
    }

    // Pass 2: materialize `Class`, `Method`, `Field`, `Annotations`, and `MethodDebugInfo`.
    let mut classes: BTreeMap<StringId, Class> = BTreeMap::new();
    let mut pending_ops_by_class: BTreeMap<StringId, Vec<Option<PendingMethodOps>>> =
        BTreeMap::new();
    let mut module_data_offsets: HashSet<u32> = HashSet::new();
    let mut scope_names_offsets: HashSet<u32> = HashSet::new();
    let mut phase_blob_offsets: HashSet<u32> = HashSet::new();
    let mut ann_visiting: HashSet<u32> = HashSet::new();

    for staged in staged_classes {
        if classes.contains_key(&staged.descriptor) {
            let dup = strings.resolve(staged.descriptor).unwrap_or("?").to_owned();
            let err = Error::Malformed {
                field: "class",
                context: format!("duplicate class descriptor {dup:?}"),
            };
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "class",
                    offset: Some(staged.class_off),
                    message: err.to_string(),
                });
                continue;
            }
            return Err(err);
        }

        if staged.is_external && staged.raw_cls.is_none() {
            classes.insert(
                staged.descriptor,
                Class {
                    descriptor: staged.descriptor,
                    name: staged.descriptor,
                    access_flags: AccessFlags::empty(),
                    source_lang: SourceLang::PandaAssembly,
                    source_file: None,
                    is_external: true,
                    super_class: None,
                    interfaces: Vec::new(),
                    methods: Vec::new(),
                    fields: Vec::new(),
                    annotations: Annotations::default(),
                },
            );
            pending_ops_by_class.insert(staged.descriptor, Vec::new());
            continue;
        }

        let Some(raw_cls) = staged.raw_cls else {
            continue;
        };

        let name = match str_cache.intern_utf8(&reader, staged.class_off, &mut strings) {
            Some(sid) => sid,
            None => {
                let err = Error::Malformed {
                    field: "name",
                    context: format!("class {}", staged.descriptor_str),
                };
                if forensic {
                    diagnostics.push(DecodeDiagnostic {
                        kind: "class",
                        offset: Some(staged.class_off),
                        message: err.to_string(),
                    });
                    continue;
                }
                return Err(err);
            }
        };

        let source_lang = match decode_source_lang(raw_cls.source_lang) {
            Ok(lang) => lang,
            Err(err) => {
                if forensic {
                    diagnostics.push(DecodeDiagnostic {
                        kind: "class",
                        offset: Some(staged.class_off),
                        message: err.to_string(),
                    });
                    SourceLang::PandaAssembly
                } else {
                    return Err(err);
                }
            }
        };

        let mut methods = Vec::with_capacity(staged.raw_methods.len());
        let mut cls_method_ops = Vec::with_capacity(staged.raw_methods.len());
        for raw_m in &staged.raw_methods {
            match decode_method_item(
                &reader,
                raw_m,
                staged.class_off,
                raw_cls.source_file_off,
                dialect,
                lazy_backing,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            ) {
                Ok((m, m_ops)) => {
                    methods.push(m);
                    cls_method_ops.push(m_ops);
                }
                Err(err) => {
                    if forensic {
                        diagnostics.push(DecodeDiagnostic {
                            kind: "method",
                            offset: Some(raw_m.offset),
                            message: err.to_string(),
                        });
                    } else {
                        return Err(err);
                    }
                }
            }
        }

        let mut fields = Vec::with_capacity(staged.raw_fields.len());
        for raw_f in &staged.raw_fields {
            match decode_field_item(
                &reader,
                raw_f,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
                &staged.descriptor_str,
                &mut module_data_offsets,
                &mut scope_names_offsets,
                &mut phase_blob_offsets,
            ) {
                Ok(fl) => fields.push(fl),
                Err(err) => {
                    if forensic {
                        diagnostics.push(DecodeDiagnostic {
                            kind: "field",
                            offset: Some(raw_f.offset),
                            message: err.to_string(),
                        });
                    } else {
                        return Err(err);
                    }
                }
            }
        }

        let annotations = Annotations {
            compile_time: decode_annotation_list(
                &reader,
                &raw_cls.annotations,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            )?,
            runtime: decode_annotation_list(
                &reader,
                &raw_cls.runtime_annotations,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            )?,
            compile_time_type: decode_annotation_list(
                &reader,
                &raw_cls.type_annotations,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            )?,
            runtime_type: decode_annotation_list(
                &reader,
                &raw_cls.runtime_type_annotations,
                forensic,
                &mut diagnostics,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            )?,
        };

        let source_file = raw_cls
            .source_file_off
            .and_then(|sf_off| str_cache.intern_utf8(&reader, sf_off, &mut strings));
        let access_flags = AccessFlags::from_bits_truncate(raw_cls.access_flags);
        let super_class = raw_cls
            .super_class_off
            .and_then(|off| entity_map.get(&off).copied());
        let interfaces = (0..raw_cls.ifaces_count)
            .filter_map(|idx| {
                let off = raw_cls.interface_class_off(&reader, idx)?;
                entity_map.get(&off).copied()
            })
            .collect();

        classes.insert(
            staged.descriptor,
            Class {
                descriptor: staged.descriptor,
                name,
                access_flags,
                source_lang,
                source_file,
                is_external: false,
                super_class,
                interfaces,
                methods,
                fields,
                annotations,
            },
        );
        pending_ops_by_class.insert(staged.descriptor, cls_method_ops);
    }

    // Assign dense 0-based `MethodIdx` / `FieldIdx` tables in `classes` BTreeMap order.
    let mut method_offset_to_idx: HashMap<u32, MethodIdx> = HashMap::new();
    for (idx, (_, m)) in classes
        .iter()
        .flat_map(|(&d, c)| c.methods.iter().map(move |m| (d, m)))
        .enumerate()
    {
        if m.offset != 0 {
            method_offset_to_idx
                .entry(m.offset)
                .or_insert(MethodIdx(idx as u32));
        }
    }
    let mut field_offset_to_idx: HashMap<u32, FieldIdx> = HashMap::new();
    for (idx, (_, fl)) in classes
        .iter()
        .flat_map(|(&d, c)| c.fields.iter().map(move |fl| (d, fl)))
        .enumerate()
    {
        if fl.offset != 0 {
            field_offset_to_idx
                .entry(fl.offset)
                .or_insert(FieldIdx(idx as u32));
        }
    }

    // Pass 3: resolve bytecode entity operands in `classes` BTreeMap order
    // (using the compact `PendingMethodOps` extracted during Pass 2 so lazy
    // `MethodCode::Span` never re-decodes instructions!).
    let mut pending_code_lit_refs: Vec<(usize, u32, u32)> = Vec::new();
    let mut flat_idx = 0usize;
    let file_slice = reader.bytes();

    for (&cls_desc, class) in &mut classes {
        let cls_ops = pending_ops_by_class.remove(&cls_desc).unwrap_or_default();
        for (method, ops_opt) in class.methods.iter_mut().zip(cls_ops.into_iter()) {
            let cur_flat = flat_idx;
            flat_idx += 1;
            let (Some(body), Some(ops)) = (&mut method.body, ops_opt) else {
                continue;
            };
            let mut body_corrupt = false;
            for op in ops.entity_ops {
                use abcd_isa::EntityKind;
                let invalid = || Error::Malformed {
                    field: "bytecode entity reference",
                    context: format!(
                        "{} in method {:#x}: {:?} index {}",
                        op.mnemonic, ops.method_off, op.kind, op.raw_id
                    ),
                };
                let resolved_off: Result<u32, Error> = if legacy {
                    match op.kind {
                        EntityKind::StringId => {
                            if op.raw_id == 0 || (op.raw_id as usize) >= data.len() {
                                Err(invalid())
                            } else {
                                Ok(op.raw_id)
                            }
                        }
                        EntityKind::MethodId => u16::try_from(op.raw_id)
                            .ok()
                            .and_then(|idx| reader.resolve_method_index(ops.method_off, idx))
                            .ok_or_else(invalid),
                        EntityKind::LiteralarrayId => {
                            let Some((count, table_off)) = legacy_lit_table else {
                                if forensic {
                                    diagnostics.push(DecodeDiagnostic {
                                        kind: "bytecode_entity",
                                        offset: Some(ops.method_off),
                                        message: invalid().to_string(),
                                    });
                                    body_corrupt = true;
                                    break;
                                }
                                return Err(invalid());
                            };
                            if op.raw_id >= count {
                                Err(invalid())
                            } else {
                                op.raw_id
                                    .checked_mul(4)
                                    .and_then(|n| table_off.checked_add(n))
                                    .and_then(|entry| usize::try_from(entry).ok())
                                    .and_then(|entry| {
                                        entry
                                            .checked_add(4)
                                            .and_then(|end| file_slice.get(entry..end))
                                    })
                                    .and_then(|s| <[u8; 4]>::try_from(s).ok())
                                    .map(u32::from_le_bytes)
                                    .filter(|&off| off != 0 && (off as usize) < data.len())
                                    .ok_or_else(invalid)
                            }
                        }
                    }
                } else {
                    u16::try_from(op.raw_id)
                        .ok()
                        .and_then(|idx| reader.resolve_method_index(ops.method_off, idx))
                        .ok_or_else(invalid)
                };

                let offset = match resolved_off {
                    Ok(o) => o,
                    Err(err) => {
                        if forensic {
                            diagnostics.push(DecodeDiagnostic {
                                kind: "bytecode_entity",
                                offset: Some(ops.method_off),
                                message: err.to_string(),
                            });
                            body_corrupt = true;
                            break;
                        }
                        return Err(err);
                    }
                };

                match op.kind {
                    EntityKind::LiteralarrayId => {
                        pending_code_lit_refs.push((cur_flat, op.raw_id, offset));
                    }
                    EntityKind::StringId => {
                        let sid = match entity_map.get(&offset).copied() {
                            Some(sid) => sid,
                            None => match str_cache.intern_lossy(&reader, offset, &mut strings) {
                                Some(sid) => {
                                    entity_map.insert(offset, sid);
                                    sid
                                }
                                None => {
                                    let err = invalid();
                                    if forensic {
                                        diagnostics.push(DecodeDiagnostic {
                                            kind: "bytecode_entity",
                                            offset: Some(ops.method_off),
                                            message: err.to_string(),
                                        });
                                        body_corrupt = true;
                                        break;
                                    }
                                    return Err(err);
                                }
                            },
                        };
                        body.entities.insert(
                            (op.kind, op.raw_id),
                            EntityRef::string_with_offset(sid, offset),
                        );
                    }
                    EntityKind::MethodId => {
                        let eref = if let Some(&midx) = method_offset_to_idx.get(&offset) {
                            EntityRef::Method(midx)
                        } else {
                            let name = match entity_map.get(&offset).copied() {
                                Some(sid) => sid,
                                None => {
                                    let resolved_name = reader.open_method(offset).and_then(|rm| {
                                        str_cache.intern_method_name(
                                            &reader,
                                            rm.name_off,
                                            &mut strings,
                                        )
                                    });
                                    match resolved_name {
                                        Some(sid) => {
                                            entity_map.insert(offset, sid);
                                            sid
                                        }
                                        None => {
                                            let err = invalid();
                                            if forensic {
                                                diagnostics.push(DecodeDiagnostic {
                                                    kind: "bytecode_entity",
                                                    offset: Some(ops.method_off),
                                                    message: err.to_string(),
                                                });
                                                body_corrupt = true;
                                                break;
                                            }
                                            return Err(err);
                                        }
                                    }
                                }
                            };
                            EntityRef::ExternalMethod {
                                name,
                                source_offset: offset,
                            }
                        };
                        body.entities.insert((op.kind, op.raw_id), eref);
                    }
                }
            }

            if !body_corrupt && legacy {
                for bop in ops.legacy_buf_ops {
                    let invalid = || Error::Malformed {
                        field: "legacy literal-array reference",
                        context: format!(
                            "{} in method {:#x}: global index {}",
                            bop.mnemonic, ops.method_off, bop.global_idx
                        ),
                    };
                    let res = u32::try_from(bop.global_idx)
                        .ok()
                        .and_then(|idx| {
                            let (count, table_off) = legacy_lit_table?;
                            if idx >= count {
                                return None;
                            }
                            let pos = usize::try_from(idx.checked_mul(4)?.checked_add(table_off)?)
                                .ok()?;
                            let bytes: [u8; 4] =
                                file_slice.get(pos..pos.checked_add(4)?)?.try_into().ok()?;
                            let off = u32::from_le_bytes(bytes);
                            (off != 0 && (off as usize) < data.len()).then_some((idx, off))
                        })
                        .ok_or_else(invalid);
                    match res {
                        Ok((idx, off)) => {
                            pending_code_lit_refs.push((cur_flat, idx, off));
                        }
                        Err(err) => {
                            if forensic {
                                diagnostics.push(DecodeDiagnostic {
                                    kind: "bytecode_entity",
                                    offset: Some(ops.method_off),
                                    message: err.to_string(),
                                });
                                body_corrupt = true;
                                break;
                            }
                            return Err(err);
                        }
                    }
                }
            }

            if body_corrupt {
                method.body = None;
            }
        }
    }

    // --- literal arrays ---
    let mut referenced_literal_offsets: HashSet<u32> = pending_code_lit_refs
        .iter()
        .map(|&(_, _, off)| off)
        .chain(scope_names_offsets.iter().copied())
        .collect();
    collect_annotation_nested_literal_offsets(
        &reader,
        &classes,
        size,
        &module_data_offsets,
        &phase_blob_offsets,
        &mut referenced_literal_offsets,
    );
    let (literal_arrays, literal_array_offsets, literal_array_header_offsets) =
        decode_literal_arrays(
            &reader,
            size,
            forensic,
            &mut diagnostics,
            &mut strings,
            &mut str_cache,
            &referenced_literal_offsets,
            &module_data_offsets,
            &phase_blob_offsets,
            &method_offset_to_idx,
        )?;

    // Finalize bytecode literal-array operands, field `LiteralArrayRef`s, and
    // annotation method/field/literal-array indices.
    {
        let mut methods_mut: Vec<&mut Method> = classes
            .values_mut()
            .flat_map(|c| c.methods.iter_mut())
            .collect();
        for (fidx, raw_id, off) in pending_code_lit_refs {
            let table_idx = literal_array_offsets.get(&off).copied().unwrap_or(ABSENT);
            if let Some(m) = methods_mut.get_mut(fidx)
                && let Some(body) = m.body.as_mut()
            {
                body.entities.insert(
                    (abcd_isa::EntityKind::LiteralarrayId, raw_id),
                    EntityRef::LiteralArray(LiteralArrayIdx(table_idx)),
                );
            }
        }
    }
    for class in classes.values_mut() {
        for field in &mut class.fields {
            if let Some(FieldValue::LiteralArrayRef {
                index,
                source_offset: Some(off),
            }) = &mut field.initial_value
            {
                let table_idx = literal_array_offsets.get(off).copied().unwrap_or(ABSENT);
                *index = LiteralArrayIdx(table_idx);
            }
        }
    }
    rewrite_annotation_refs(
        &mut classes,
        &literal_array_offsets,
        literal_arrays.len(),
        &literal_array_header_offsets,
        &method_offset_to_idx,
        &field_offset_to_idx,
    );

    Ok((
        File {
            version,
            checksum,
            size,
            file_type,
            strings,
            classes,
            literal_arrays,
            literal_array_header_offsets,
        },
        diagnostics,
    ))
}

// Transitive Literal-Array Discovery & Dense Handle Rewriting
// ---------------------------------------------------------------------------

pub(super) trait U32OffsetSet {
    fn contains_offset(&self, off: u32) -> bool;
}

impl U32OffsetSet for HashSet<u32> {
    #[inline]
    fn contains_offset(&self, off: u32) -> bool {
        self.contains(&off)
    }
}

impl U32OffsetSet for CompactU32Set {
    #[inline]
    fn contains_offset(&self, off: u32) -> bool {
        self.contains(off)
    }
}

pub(super) fn is_plausible_literal_array_offset<S: U32OffsetSet>(
    off: u32,
    header_size: u32,
    file_size: u32,
    module_data_offsets: &S,
    phase_blob_offsets: &S,
) -> bool {
    off != ABSENT
        && off >= header_size
        && u64::from(off) + 4 <= u64::from(file_size)
        && !module_data_offsets.contains_offset(off)
        && !phase_blob_offsets.contains_offset(off)
}

fn push_annotations_imm<'a>(anns: &'a Annotations, stack: &mut Vec<&'a AnnotationValue>) {
    for ann in anns
        .compile_time
        .iter()
        .chain(anns.runtime.iter())
        .chain(anns.compile_time_type.iter())
        .chain(anns.runtime_type.iter())
    {
        for elem in &ann.elements {
            stack.push(&elem.value);
        }
    }
}

fn collect_annotation_nested_literal_offsets(
    reader: &AbcReader<'_>,
    classes: &BTreeMap<StringId, Class>,
    file_size: u32,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
    out: &mut HashSet<u32>,
) {
    let header_size = reader.header_size();
    let is_valid_lit_array = |cand: u32| -> bool {
        is_plausible_literal_array_offset(
            cand,
            header_size,
            file_size,
            module_data_offsets,
            phase_blob_offsets,
        ) && walk_raw_literal_array(reader, cand, |_| Ok(())).is_ok()
    };

    let mut stack: Vec<&AnnotationValue> = Vec::new();
    for class in classes.values() {
        push_annotations_imm(&class.annotations, &mut stack);
        for method in &class.methods {
            push_annotations_imm(&method.annotations, &mut stack);
            for anns in method
                .param_annotations
                .compile_time
                .iter()
                .chain(method.param_annotations.runtime.iter())
            {
                for ann in anns {
                    for elem in &ann.elements {
                        stack.push(&elem.value);
                    }
                }
            }
        }
        for field in &class.fields {
            push_annotations_imm(&field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    match item {
                        LiteralValue::LiteralArray(idx)
                            if is_plausible_literal_array_offset(
                                idx.0,
                                header_size,
                                file_size,
                                module_data_offsets,
                                phase_blob_offsets,
                            ) =>
                        {
                            out.insert(idx.0);
                        }
                        LiteralValue::LiteralBufferIndex(idx) if is_valid_lit_array(idx.0) => {
                            out.insert(idx.0);
                        }
                        _ => {}
                    }
                }
            }
            AnnotationValue::Annotation(inner) => {
                for elem in &inner.elements {
                    stack.push(&elem.value);
                }
            }
            AnnotationValue::Array { values, .. } => {
                for item in values {
                    stack.push(item);
                }
            }
            _ => {}
        }
    }
}

fn rewrite_literal_item_refs(
    v: &mut LiteralValue,
    offset_to_index: &HashMap<u32, u32>,
    array_count: usize,
    header_offsets: &[u32],
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
) {
    if let Some(midx) = v.method_idx_mut() {
        *midx = method_offset_to_idx
            .get(&midx.0)
            .copied()
            .unwrap_or(MethodIdx(ABSENT));
        return;
    }
    match v {
        LiteralValue::LiteralArray(idx) => {
            if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                idx.0 = table_idx;
            } else if (idx.0 as usize) < array_count {
                idx.0 = ABSENT;
            }
        }
        LiteralValue::LiteralBufferIndex(idx) => {
            if let Some(&hdr_off) = header_offsets.get(idx.0 as usize)
                && let Some(&table_idx) = offset_to_index.get(&hdr_off)
            {
                idx.0 = table_idx;
            } else if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                idx.0 = table_idx;
            }
        }
        _ => {}
    }
}

fn push_annotations_mut<'a>(anns: &'a mut Annotations, stack: &mut Vec<&'a mut AnnotationValue>) {
    for ann in anns
        .compile_time
        .iter_mut()
        .chain(anns.runtime.iter_mut())
        .chain(anns.compile_time_type.iter_mut())
        .chain(anns.runtime_type.iter_mut())
    {
        for elem in &mut ann.elements {
            stack.push(&mut elem.value);
        }
    }
}

fn rewrite_annotation_refs(
    classes: &mut BTreeMap<StringId, Class>,
    offset_to_index: &HashMap<u32, u32>,
    literal_array_count: usize,
    header_offsets: &[u32],
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
    field_offset_to_idx: &HashMap<u32, FieldIdx>,
) {
    let mut stack: Vec<&mut AnnotationValue> = Vec::new();
    for class in classes.values_mut() {
        push_annotations_mut(&mut class.annotations, &mut stack);
        for method in &mut class.methods {
            push_annotations_mut(&mut method.annotations, &mut stack);
            for anns in method
                .param_annotations
                .compile_time
                .iter_mut()
                .chain(method.param_annotations.runtime.iter_mut())
            {
                for ann in anns {
                    for elem in &mut ann.elements {
                        stack.push(&mut elem.value);
                    }
                }
            }
        }
        for field in &mut class.fields {
            push_annotations_mut(&mut field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::Method { method, offset, .. } => {
                *method = method_offset_to_idx.get(offset).copied();
            }
            AnnotationValue::Enum { field, offset, .. } => {
                *field = field_offset_to_idx.get(offset).copied();
            }
            AnnotationValue::MethodHandle(mh) => {
                if mh.handle_type.is_field_op() {
                    mh.target_field = field_offset_to_idx.get(&mh.entity_offset).copied();
                } else {
                    mh.target_method = method_offset_to_idx.get(&mh.entity_offset).copied();
                }
            }
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    rewrite_literal_item_refs(
                        item,
                        offset_to_index,
                        literal_array_count,
                        header_offsets,
                        method_offset_to_idx,
                    );
                }
            }
            AnnotationValue::Annotation(inner) => {
                for elem in &mut inner.elements {
                    stack.push(&mut elem.value);
                }
            }
            AnnotationValue::Array { values, .. } => {
                for item in values {
                    stack.push(item);
                }
            }
            _ => {}
        }
    }
}

type LiteralArrayTable = (Vec<LiteralArray>, HashMap<u32, u32>, Vec<u32>);

#[expect(
    clippy::too_many_arguments,
    reason = "literal-array table builder threads forensic diagnostics, offset sets, and string cache"
)]
fn decode_literal_arrays(
    reader: &AbcReader<'_>,
    file_size: u32,
    forensic: bool,
    diagnostics: &mut DecodeDiagnostics,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    referenced_offsets: &HashSet<u32>,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
) -> Result<LiteralArrayTable, Error> {
    let mut header_offsets = Vec::new();
    let mut offsets = Vec::new();
    let mut seen = CompactU32Set::default();

    for off in reader.literal_array_offsets() {
        if off != ABSENT {
            header_offsets.push(off);
        }
        if off != ABSENT
            && !module_data_offsets.contains(&off)
            && !phase_blob_offsets.contains(&off)
            && seen.insert(off)
        {
            offsets.push(off);
        }
    }

    let mut referenced: Vec<u32> = referenced_offsets
        .iter()
        .copied()
        .filter(|&off| {
            off != ABSENT
                && !seen.contains(off)
                && !module_data_offsets.contains(&off)
                && !phase_blob_offsets.contains(&off)
        })
        .collect();
    referenced.sort_unstable();
    for off in referenced {
        if seen.insert(off) {
            offsets.push(off);
        }
    }
    if offsets.is_empty() {
        return Ok((Vec::new(), HashMap::new(), header_offsets));
    }

    let mut offset_to_index: HashMap<u32, u32> = HashMap::with_capacity(offsets.len());
    for (i, &off) in offsets.iter().enumerate() {
        offset_to_index.insert(off, i as u32);
    }

    let header_size = reader.header_size();
    let mut arrays: Vec<LiteralArray> = Vec::with_capacity(offsets.len());
    let mut decoded = 0usize;
    while decoded < offsets.len() {
        let mut nested: Vec<u32> = Vec::new();
        for &off in &offsets[decoded..] {
            let values = match decode_literal_array_values(reader, off, strings, str_cache) {
                Ok(v) => v,
                Err(err) => {
                    if forensic {
                        diagnostics.push(DecodeDiagnostic {
                            kind: "literal_array",
                            offset: Some(off),
                            message: err.to_string(),
                        });
                        Vec::new()
                    } else {
                        return Err(err);
                    }
                }
            };
            for value in &values {
                match value {
                    LiteralValue::LiteralArray(idx)
                        if is_plausible_literal_array_offset(
                            idx.0,
                            header_size,
                            file_size,
                            module_data_offsets,
                            phase_blob_offsets,
                        ) && !seen.contains(idx.0) =>
                    {
                        nested.push(idx.0);
                    }
                    LiteralValue::LiteralBufferIndex(idx)
                        if is_plausible_literal_array_offset(
                            idx.0,
                            header_size,
                            file_size,
                            module_data_offsets,
                            phase_blob_offsets,
                        ) && !seen.contains(idx.0)
                            && walk_raw_literal_array(reader, idx.0, |_| Ok(())).is_ok() =>
                    {
                        nested.push(idx.0);
                    }
                    _ => {}
                }
            }
            arrays.push(LiteralArray::with_source_offset(off, values));
        }
        decoded = offsets.len();
        nested.sort_unstable();
        nested.dedup();
        for off in nested {
            if seen.insert(off) {
                offset_to_index.insert(off, offsets.len() as u32);
                offsets.push(off);
            }
        }
    }

    let array_count = arrays.len();
    for arr in &mut arrays {
        for v in &mut arr.values {
            rewrite_literal_item_refs(
                v,
                &offset_to_index,
                array_count,
                &header_offsets,
                method_offset_to_idx,
            );
        }
    }
    Ok((arrays, offset_to_index, header_offsets))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_literalarray_table_rejects_32bit_overflows() {
        let mut buf = vec![0u8; 128];
        let set_header = |buf: &mut [u8], count: u32, table_off: u32| {
            buf[44..48].copy_from_slice(&count.to_le_bytes());
            buf[48..52].copy_from_slice(&table_off.to_le_bytes());
        };

        set_header(&mut buf, 2, 60);
        assert_eq!(legacy_literalarray_table(&buf), Some((2, 60)));

        for (count, table_off) in [
            (u32::MAX, u32::MAX),
            (u32::MAX, 60),
            (0x4000_0000, 0),
            (0x4000_0001, 60),
            (1, u32::MAX),
            (1, u32::MAX - 2),
            (0, u32::MAX),
            (0x2000_0001, 0x8000_0000),
        ] {
            set_header(&mut buf, count, table_off);
            assert_eq!(
                legacy_literalarray_table(&buf),
                None,
                "expected None for count={count:#x}, table_off={table_off:#x}"
            );
        }
    }
}
