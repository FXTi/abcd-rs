//! Eagerly-decoded, fully-owned representation of an ABC file.
//!
//! Call [`decode`] to parse raw bytes into a [`File`] struct.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::{CStr, c_void};

use abcd_file_sys as sys;

use crate::code::{CatchBlock, TryBlock};
use crate::debug::{ColumnEntry, LineEntry, LocalVarInfo, ParamInfo};
use crate::error::Error;
use crate::file::{ABSENT, is_external, read_string};
use crate::model::*;
use crate::types::{AccessFlags, FunctionKind, SourceLang, Type, TypeId};
use crate::{StringId, StringPool};

// ---------------------------------------------------------------------------
// RAII guard for C handles
// ---------------------------------------------------------------------------

/// Calls a closure on drop. Used to ensure C handles are closed.
struct HandleGuard<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for HandleGuard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

// ---------------------------------------------------------------------------
// decode()
// ---------------------------------------------------------------------------

/// Decode an ABC file from raw bytes into a fully-owned [`File`].
pub fn decode(data: &[u8]) -> Result<File, Error> {
    use crate::file::AbcFile;

    let abc = AbcFile::open(data)?;
    let f = abc.raw;
    let version = abc.version();
    let checksum = abc.checksum();
    let size = abc.size();
    let file_type = crate::file::file_type(data);

    let mut strings = StringPool::new();

    // Open debug info (file-level, lives for entire decode).
    let debug_raw = unsafe { sys::abc_debug_info_open(f) };
    let _debug_guard = if debug_raw.is_null() {
        None
    } else {
        Some(HandleGuard(Some(move || unsafe {
            sys::abc_debug_info_close(debug_raw)
        })))
    };

    // Build entity_map: offset → interned descriptor/name.
    let mut entity_map = HashMap::new();
    let num_classes = unsafe { sys::abc_file_num_classes(f) };
    for i in 0..num_classes {
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == ABSENT {
            continue;
        }
        if is_external(f, class_off) {
            // A foreign-class item is just a string item (no methods/fields):
            // read its descriptor directly instead of building an accessor,
            // which upstream only supports for non-external classes.
            if let Some(desc) = read_string(f, class_off) {
                let sid = strings.get_or_intern(&desc);
                entity_map.insert(class_off, sid);
            }
            continue;
        }
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            continue;
        }
        let _cg = HandleGuard(Some(|| unsafe { sys::abc_class_close(cr) }));

        if let Some(desc) = read_class_descriptor(f, cr) {
            let sid = strings.get_or_intern(&desc);
            entity_map.insert(unsafe { sys::abc_class_get_class_id(cr) }, sid);
        }
        for off in collect_offsets_void(cr, sys::abc_class_enumerate_methods) {
            let mr = unsafe { sys::abc_method_open(f, off) };
            if mr.is_null() {
                continue;
            }
            let _mg = HandleGuard(Some(|| unsafe { sys::abc_method_close(mr) }));
            if let Some(name) = read_method_name(mr) {
                let sid = strings.get_or_intern(&name);
                entity_map.insert(unsafe { sys::abc_method_get_method_id(mr) }, sid);
            }
        }
        for off in collect_offsets_void(cr, sys::abc_class_enumerate_fields) {
            let fr = unsafe { sys::abc_field_open(f, off) };
            if fr.is_null() {
                continue;
            }
            let _fg = HandleGuard(Some(|| unsafe { sys::abc_field_close(fr) }));
            let name_off = unsafe { sys::abc_field_name_off(fr) };
            if name_off != ABSENT
                && let Some(name) = read_string(f, name_off)
            {
                let sid = strings.get_or_intern(&name);
                entity_map.insert(unsafe { sys::abc_field_get_field_id(fr) }, sid);
            }
        }
    }

    // --- classes ---
    let mut classes = BTreeMap::new();
    // Source offsets of module-record blobs (`_ESModuleRecord` field values)
    // and scope-names literal arrays (`_ESScopeNamesRecord` field values).
    // The former must be excluded from tagged literal-array decoding; the
    // latter must be included even when no header table lists them (13.x+).
    let mut module_data_offsets: HashSet<u32> = HashSet::new();
    let mut scope_names_offsets: HashSet<u32> = HashSet::new();
    // Untagged module-request-phase blobs (`moduleRequestPhaseIdx` field
    // values): excluded from tagged literal-array decoding, like module blobs.
    let mut phase_blob_offsets: HashSet<u32> = HashSet::new();
    for i in 0..num_classes {
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == ABSENT {
            continue;
        }
        if is_external(f, class_off) {
            // Foreign classes carry only a descriptor: surface them as
            // minimal Class entries so super_class references resolve.
            if let Some(desc_str) = read_string(f, class_off) {
                let descriptor = strings.get_or_intern(&desc_str);
                classes.insert(
                    descriptor,
                    Class {
                        descriptor,
                        name: descriptor,
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
            }
            continue;
        }
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            continue;
        }
        let _cg = HandleGuard(Some(|| unsafe { sys::abc_class_close(cr) }));

        let descriptor_str = match read_class_descriptor(f, cr) {
            Some(d) => d,
            None => continue,
        };
        let descriptor = strings.get_or_intern(&descriptor_str);

        let name_str = read_class_name(f, cr).ok_or_else(|| Error::Malformed {
            field: "name",
            context: format!("class {descriptor_str}"),
        })?;
        let name = strings.get_or_intern(&name_str);

        let methods: Result<Vec<_>, _> = collect_offsets_void(cr, sys::abc_class_enumerate_methods)
            .into_iter()
            .map(|off| decode_method_at(f, off, debug_raw, &entity_map, &mut strings))
            .collect();
        let methods = methods?;

        let fields: Result<Vec<_>, _> = collect_offsets_void(cr, sys::abc_class_enumerate_fields)
            .into_iter()
            .map(|off| {
                decode_field_at(
                    f,
                    off,
                    &entity_map,
                    &mut strings,
                    &descriptor_str,
                    &mut module_data_offsets,
                    &mut scope_names_offsets,
                    &mut phase_blob_offsets,
                )
            })
            .collect();
        let fields = fields?;

        let annotations = decode_class_annotations(f, cr, &entity_map, &mut strings)?;

        classes.insert(
            descriptor,
            Class {
                descriptor,
                name,
                access_flags: AccessFlags::from_bits_truncate(unsafe {
                    sys::abc_class_access_flags(cr)
                }),
                source_lang: SourceLang::try_from(unsafe { sys::abc_class_get_source_lang(cr) })
                    .unwrap_or(SourceLang::PandaAssembly),
                source_file: {
                    let off = unsafe { sys::abc_class_source_file_off(cr) };
                    if off == ABSENT {
                        None
                    } else {
                        read_string(f, off).map(|s| strings.get_or_intern(&s))
                    }
                },
                is_external: is_external(f, unsafe { sys::abc_class_get_class_id(cr) }),
                super_class: {
                    let off = unsafe { sys::abc_class_super_class_off(cr) };
                    if off == 0 || off == ABSENT {
                        None
                    } else {
                        entity_map.get(&off).copied()
                    }
                },
                interfaces: {
                    let n = unsafe { sys::abc_class_get_ifaces_number(cr) };
                    (0..n)
                        .filter_map(|i| {
                            let off = unsafe { sys::abc_class_get_interface_id(cr, i) };
                            entity_map.get(&off).copied()
                        })
                        .collect()
                },
                methods,
                fields,
                annotations,
            },
        );
    }

    // Resolve encoded string/method indices while the source file is open.
    // An index only has meaning in its owning method's index region; it must
    // never be used directly as a key in the file-wide offset/name map.
    for method in classes.values_mut().flat_map(|class| &mut class.methods) {
        let Some(body) = &mut method.body else {
            continue;
        };
        for bytecode in &body.bytecodes {
            for (kind, id) in bytecode.entity_operands() {
                use abcd_isa::EntityKind;
                if !matches!(
                    kind,
                    EntityKind::StringId | EntityKind::MethodId | EntityKind::LiteralarrayId
                ) {
                    continue;
                }
                let invalid = || Error::Malformed {
                    field: "bytecode entity reference",
                    context: format!(
                        "{} in method {:#x}: {:?} index {}",
                        bytecode.mnemonic(),
                        method.offset,
                        kind,
                        id.0
                    ),
                };
                let index = u16::try_from(id.0).map_err(|_| invalid())?;
                let offset = unsafe { sys::abc_resolve_offset_by_index(f, method.offset, index) };
                if offset == ABSENT {
                    return Err(invalid());
                }
                body.entity_offsets.insert((kind, id.0), offset);
                if kind == EntityKind::LiteralarrayId {
                    continue;
                }
                if entity_map.contains_key(&offset) {
                    continue;
                }
                let name = if kind == EntityKind::StringId {
                    read_string(f, offset)
                } else {
                    let accessor = unsafe { sys::abc_method_open(f, offset) };
                    if accessor.is_null() {
                        return Err(invalid());
                    }
                    let _guard = HandleGuard(Some(|| unsafe { sys::abc_method_close(accessor) }));
                    read_method_name(accessor)
                }
                .ok_or_else(invalid)?;
                entity_map.insert(offset, strings.get_or_intern(&name));
            }
        }
    }

    // --- literal arrays ---
    // API13/24 no longer expose a usable header count. Collect literal-array
    // offsets reached through method index regions so they can be decoded on
    // demand alongside legacy table entries. Scope-names blobs
    // (`_ESScopeNamesRecord` field values) are ordinary tagged literal arrays
    // reachable only through those fields on 13.x+, so collect them too.
    let referenced_literal_offsets: HashSet<u32> = classes
        .values()
        .flat_map(|class| class.methods.iter())
        .flat_map(|method| method.body.iter())
        .flat_map(|body| body.entity_offsets.iter())
        .filter_map(|((kind, _), offset)| {
            (kind == &abcd_isa::EntityKind::LiteralarrayId).then_some(*offset)
        })
        .chain(scope_names_offsets.iter().copied())
        .collect();
    let (literal_arrays, literal_array_offsets) = decode_literal_arrays(
        f,
        &mut strings,
        &referenced_literal_offsets,
        &module_data_offsets,
        &phase_blob_offsets,
    );

    Ok(File {
        version,
        checksum,
        size,
        file_type,
        strings,
        classes,
        literal_arrays,
        literal_array_offsets,
        entity_map,
    })
}

// ---------------------------------------------------------------------------
// Internal decode helpers
// ---------------------------------------------------------------------------

fn decode_method_at(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    debug_raw: *mut sys::AbcDebugInfo,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<Method, Error> {
    let mr = unsafe { sys::abc_method_open(f as *mut _, method_off) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(method_off));
    }
    let _mg = HandleGuard(Some(|| unsafe { sys::abc_method_close(mr) }));

    let method_id = unsafe { sys::abc_method_get_method_id(mr) };

    let name_str = read_method_name(mr).ok_or_else(|| Error::Malformed {
        field: "name",
        context: format!("method at offset {method_id:#x}"),
    })?;
    let name = strings.get_or_intern(&name_str);

    let function_kind = {
        let ia = unsafe { sys::abc_index_open(f, method_id) };
        if ia.is_null() {
            FunctionKind::None
        } else {
            let _ig = HandleGuard(Some(|| unsafe { sys::abc_index_close(ia) }));
            FunctionKind::try_from(unsafe { sys::abc_index_get_function_kind(ia) })
                .unwrap_or(FunctionKind::None)
        }
    };

    let (body, byte_offsets) = {
        let code_off = unsafe { sys::abc_method_code_off(mr) };
        if code_off == ABSENT {
            (None, Vec::new())
        } else {
            let (b, bo) = decode_code_at(f, method_off, code_off)?;
            (Some(b), bo)
        }
    };

    let (return_type, arg_types) = {
        let has_valid = unsafe { sys::abc_method_has_valid_proto(mr) } != 0;
        if !has_valid {
            (None, Vec::new())
        } else {
            let proto_id = unsafe { sys::abc_method_get_proto_id(mr) };
            if proto_id == ABSENT {
                (None, Vec::new())
            } else {
                let (rt, at) = decode_proto_types(f, proto_id, entity_map, strings)?;
                (Some(rt), at)
            }
        }
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(mr, sys::abc_method_enumerate_annotations),
            entity_map,
            strings,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(mr, sys::abc_method_enumerate_runtime_annotations),
            entity_map,
            strings,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(mr, sys::abc_method_enumerate_type_annotations),
            entity_map,
            strings,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(mr, sys::abc_method_enumerate_runtime_type_annotations),
            entity_map,
            strings,
        )?,
    };

    let debug = if debug_raw.is_null() {
        None
    } else {
        Some(read_debug_info(
            debug_raw,
            method_id,
            &byte_offsets,
            strings,
        ))
    };

    let param_annotations = decode_param_annotations(f, mr, arg_types.len(), entity_map, strings)?;

    Ok(Method {
        name,
        offset: method_off,
        access_flags: AccessFlags::from_bits_truncate(unsafe { sys::abc_method_access_flags(mr) }),
        function_kind,
        source_lang: SourceLang::try_from(unsafe { sys::abc_method_get_source_lang(mr) })
            .unwrap_or(SourceLang::PandaAssembly),
        is_external: is_external(f, method_id),
        return_type,
        arg_types,
        body,
        annotations,
        param_annotations,
        debug,
    })
}

/// Decode per-parameter annotations for a method.
///
/// Each ParamAnnotationsItem enumerates (param_idx, annotation_off) pairs;
/// the annotations are decoded individually and grouped by parameter index.
/// Buckets are sized to the method's parameter count (or the highest seen
/// index + 1 when that exceeds the proto's arity), with empty Vecs for
/// unannotated parameters. A method without the item leaves its bucket
/// empty.
fn decode_param_annotations(
    f: *const sys::AbcFileHandle,
    mr: *mut sys::AbcMethodAccessor,
    num_params: usize,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<ParamAnnotations, Error> {
    let mut result = ParamAnnotations::default();
    for (is_runtime, item_off) in [
        (false, unsafe {
            sys::abc_method_get_param_annotation_id(mr)
        }),
        (true, unsafe {
            sys::abc_method_get_runtime_param_annotation_id(mr)
        }),
    ] {
        if item_off == ABSENT {
            continue;
        }
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn cb(param_idx: u32, annotation_off: u32, ctx: *mut c_void) -> i32 {
            let pairs = unsafe { &mut *(ctx as *mut Vec<(u32, u32)>) };
            pairs.push((param_idx, annotation_off));
            0
        }
        let rc = unsafe {
            sys::abc_param_annotations_enumerate(
                f,
                item_off,
                Some(cb),
                &mut pairs as *mut Vec<(u32, u32)> as *mut c_void,
            )
        };
        if rc != 0 {
            return Err(Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            });
        }
        if pairs.is_empty() {
            continue;
        }
        let bucket = if is_runtime {
            &mut result.runtime
        } else {
            &mut result.compile_time
        };
        let len = num_params.max(
            pairs
                .iter()
                .map(|&(i, _)| i as usize + 1)
                .max()
                .unwrap_or(0),
        );
        bucket.resize(len, Vec::new());
        for (idx, off) in pairs {
            let anns = decode_annotation_list(f, &[off], entity_map, strings)?;
            bucket[idx as usize].extend(anns);
        }
    }
    Ok(result)
}

/// Descriptor of the record class whose u32 fields reference module-record
/// blobs (upstream name `_ESModuleRecord`: abc2program/common/
/// abc_file_utils.h `ES_MODULE_RECORD`; collection policy:
/// libpandafile/util/collect_util.h `ES_MODULE_RECORD`).
const ES_MODULE_RECORD_DESCRIPTOR: &str = "L_ESModuleRecord;";
/// Descriptor of the record class whose u32 fields reference scope-names
/// literal arrays (upstream `_ESScopeNamesRecord`, same sources).
const ES_SCOPE_NAMES_RECORD_DESCRIPTOR: &str = "L_ESScopeNamesRecord;";

/// Name of the u32 field whose value is the file offset of an untagged
/// module-request-phase blob (one u8 lazy-import flag per module request).
/// Matched by NAME, not by class: upstream's merge-abc mode emits the field
/// on the module's own record (es2panda emitter.cpp
/// `Emitter::AddModuleRequestPhaseRecord` IsMergeAbc branch), and the
/// vendored runtime/disassembler key on the name too
/// (js_pandafile.cpp:217 `LAZY_IMPORT`, disassembler.cpp:1007
/// `MODULE_REQUEST_PAHSE_IDX`).
const MODULE_REQUEST_PHASE_FIELD: &str = "moduleRequestPhaseIdx";

/// Name of the upstream-DEAD module-record field whose value is a NESTED
/// file offset — it points to a literal array whose elements are
/// themselves offsets (arkcompiler_runtime_core
/// docs/changelogs/2022-08-18-isa-changelog.md item 5; name from vendored
/// libpandabase/utils/const_value.h:25 `TYPE_SUMMARY_FIELD_NAME`). No
/// producer (es2panda never emits it), no runtime consumer
/// (`TYPE_SUMMARY_OFFSET_NOT_FOUND` is a dead constant), the disassembler
/// excludes it (disassembler.cpp:1009), and the corpus has zero
/// occurrences. Our relocation machinery has no support for the nested
/// indirection, so decode is a HARD ERROR on the name alone (N8,
/// maintainer ruling 2026-09-20) — never a warning, never a silent raw
/// `FieldValue::I32` pass-through that a rewrite would leave dangling.
const TYPE_SUMMARY_OFFSET_FIELD: &str = "typeSummaryOffset";

/// Decode a module-record blob through the vendored ModuleDataAccessor.
///
/// Layout (module_data_accessor.cpp ctor + module_data_accessor-inl.h
/// `EnumerateModuleRecord`): `[u32 item count]` (skipped by the accessor),
/// `[u32 num_module_requests][u32 request string offset]*`, then per-tag
/// sections (count + entries) in vendored order REGULAR_IMPORT,
/// NAMESPACE_IMPORT, LOCAL_EXPORT, INDIRECT_EXPORT, STAR_EXPORT. All name
/// fields are string entity offsets. Unreadable strings and unknown tags
/// are hard errors — module data is never silently dropped.
fn decode_module_data_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut StringPool,
) -> Result<ModuleData, Error> {
    fn intern_string_at(
        f: *const sys::AbcFileHandle,
        off: u32,
        strings: &mut StringPool,
    ) -> Result<StringId, Error> {
        let s = read_string(f, off).ok_or(Error::InvalidString(off))?;
        Ok(strings.get_or_intern(&s))
    }

    let mr = unsafe { sys::abc_module_open(f, offset) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(offset));
    }
    let _mg = HandleGuard(Some(|| unsafe { sys::abc_module_close(mr) }));

    let num_requests = unsafe { sys::abc_module_num_requests(mr) };
    let mut requests = Vec::with_capacity(num_requests as usize);
    for i in 0..num_requests {
        let off = unsafe { sys::abc_module_request_off(mr, i) };
        if off == ABSENT {
            return Err(Error::InvalidString(off));
        }
        requests.push(intern_string_at(f, off, strings)?);
    }

    // The bridge callback cannot fail (no early stop), so collect raw
    // offsets first and resolve strings afterwards, where `?` works.
    struct RawRecord {
        tag: u8,
        export_off: u32,
        request_idx: u32,
        import_off: u32,
        local_off: u32,
    }
    unsafe extern "C" fn collect_record(
        tag: u8,
        export_off: u32,
        request_idx: u32,
        import_off: u32,
        local_off: u32,
        ctx: *mut c_void,
    ) {
        unsafe { &mut *(ctx as *mut Vec<RawRecord>) }.push(RawRecord {
            tag,
            export_off,
            request_idx,
            import_off,
            local_off,
        });
    }
    let mut raw: Vec<RawRecord> = Vec::new();
    unsafe {
        sys::abc_module_enumerate_records(
            mr,
            Some(collect_record),
            &mut raw as *mut Vec<RawRecord> as *mut c_void,
        )
    };

    let mut records = Vec::with_capacity(raw.len());
    for rec in raw {
        let record = match rec.tag {
            t if t == sys::ModuleTag_REGULAR_IMPORT => ModuleRecord::RegularImport {
                local_name: intern_string_at(f, rec.local_off, strings)?,
                import_name: intern_string_at(f, rec.import_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_NAMESPACE_IMPORT => ModuleRecord::NamespaceImport {
                local_name: intern_string_at(f, rec.local_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_LOCAL_EXPORT => ModuleRecord::LocalExport {
                local_name: intern_string_at(f, rec.local_off, strings)?,
                export_name: intern_string_at(f, rec.export_off, strings)?,
            },
            t if t == sys::ModuleTag_INDIRECT_EXPORT => ModuleRecord::IndirectExport {
                export_name: intern_string_at(f, rec.export_off, strings)?,
                import_name: intern_string_at(f, rec.import_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_STAR_EXPORT => ModuleRecord::StarExport {
                module_request_idx: rec.request_idx,
            },
            other => {
                return Err(Error::ModuleData(format!(
                    "unknown module record tag {other:#x} in blob at {offset:#x}"
                )));
            }
        };
        records.push(record);
    }

    Ok(ModuleData {
        source_offset: offset,
        requests,
        records,
    })
}

/// Layout (vendored runtime reader `ModuleLazyImportFlagAccessor`,
/// ecmascript/module/module_data_extractor.cpp:178-189): `[u32 item count]`
/// (written by the literal-array item itself) then one raw u8 per module
/// request — UNtagged, unlike a normal literal array.
fn decode_module_request_phase_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
) -> Result<crate::ModuleRequestPhase, Error> {
    let mut flags: Vec<u8> = Vec::new();
    unsafe extern "C" fn collect(flag: u8, ctx: *mut c_void) {
        unsafe { &mut *(ctx as *mut Vec<u8>) }.push(flag);
    }
    let n = unsafe {
        sys::abc_module_request_phase_read(
            f,
            offset,
            Some(collect),
            &mut flags as *mut Vec<u8> as *mut c_void,
        )
    };
    if n < 0 {
        return Err(Error::ModuleData(format!(
            "module-request-phase blob at {offset:#x} is unreadable"
        )));
    }
    Ok(crate::ModuleRequestPhase {
        source_offset: offset,
        flags,
    })
}

fn decode_field_at(
    f: *const sys::AbcFileHandle,
    field_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    class_descriptor: &str,
    module_data_offsets: &mut HashSet<u32>,
    scope_names_offsets: &mut HashSet<u32>,
    phase_blob_offsets: &mut HashSet<u32>,
) -> Result<Field, Error> {
    let fr = unsafe { sys::abc_field_open(f as *mut _, field_off) };
    if fr.is_null() {
        return Err(Error::InvalidOffset(field_off));
    }
    let _fg = HandleGuard(Some(|| unsafe { sys::abc_field_close(fr) }));

    let field_id = unsafe { sys::abc_field_get_field_id(fr) };

    let name_off = unsafe { sys::abc_field_name_off(fr) };
    let name = if name_off == ABSENT {
        return Err(Error::Malformed {
            field: "name",
            context: format!("field at offset {field_id:#x}"),
        });
    } else {
        let s = read_string(f, name_off).ok_or_else(|| Error::Malformed {
            field: "name",
            context: format!("field at offset {field_id:#x}"),
        })?;
        strings.get_or_intern(&s)
    };

    // `abc_field_type` returns the type entity offset. For primitive types the
    // vendor class-index entry is a PrimitiveTypeItem whose "offset" is the
    // field encoding (a small integer), not a file offset — classify via the
    // vendored GetTypeFromFieldEncoding instead of the entity_map.
    let type_raw = unsafe { sys::abc_field_type(fr) };
    let type_id = TypeId::try_from(unsafe { sys::abc_field_type_id(fr) })?;
    let field_type = if type_id == TypeId::Reference {
        let type_sid = entity_map
            .get(&type_raw)
            .copied()
            .ok_or_else(|| Error::Malformed {
                field: "field_type",
                context: format!("field {:?}", strings.resolve(name).unwrap_or("?")),
            })?;
        Type::Reference(type_sid)
    } else {
        Type::from_raw(type_id, None)?
    };

    // The vendor GetValue<T> does std::get<T-width> on the variant, so probing
    // getters in the wrong width throws std::bad_variant_access across the FFI
    // (and silently misreads float bit patterns as ints). Dispatch on the
    // field's type id instead.
    let initial_value = match type_id {
        TypeId::U1
        | TypeId::I8
        | TypeId::U8
        | TypeId::I16
        | TypeId::U16
        | TypeId::I32
        | TypeId::U32
        | TypeId::Tagged => {
            let mut v = 0i32;
            if unsafe { sys::abc_field_get_value_i32(fr, &mut v) } != 0 {
                Some(FieldValue::I32(v))
            } else {
                None
            }
        }
        TypeId::I64 | TypeId::U64 => {
            let mut v = 0i64;
            if unsafe { sys::abc_field_get_value_i64(fr, &mut v) } != 0 {
                Some(FieldValue::I64(v))
            } else {
                None
            }
        }
        TypeId::F32 => {
            let mut v = 0.0f32;
            if unsafe { sys::abc_field_get_value_f32(fr, &mut v) } != 0 {
                Some(FieldValue::F32(v))
            } else {
                None
            }
        }
        TypeId::F64 => {
            let mut v = 0.0f64;
            if unsafe { sys::abc_field_get_value_f64(fr, &mut v) } != 0 {
                Some(FieldValue::F64(v))
            } else {
                None
            }
        }
        TypeId::Void | TypeId::Reference => None,
    };

    // Module-record classes (upstream names: abc2program/common/
    // abc_file_utils.h ES_MODULE_RECORD / ES_SCOPE_NAMES_RECORD). Their u32
    // field values are SOURCE-FILE OFFSETS, not scalars:
    // - `_ESModuleRecord` → untagged ModuleDataAccessor blob; decode it
    //   structurally so encode can re-emit and relocate it.
    // - `_ESScopeNamesRecord` → ordinary tagged literal array; keep a
    //   reference so encode rewires the field to the re-emitted array, and
    //   collect the offset for literal-array decoding (13.x+ has no header
    //   table entry for it).
    let initial_value = match (class_descriptor, type_id, initial_value) {
        // N8: `typeSummaryOffset` (any class, any type, valued or not) is a
        // hard error — see TYPE_SUMMARY_OFFSET_FIELD. This arm must come
        // FIRST: upstream attaches the field to the module record itself,
        // so the `_ESModuleRecord` catch-all u32 arm below would otherwise
        // win and mis-route the nested offset into the module-data blob
        // decoder.
        (_, _, _) if strings.resolve(name) == Some(TYPE_SUMMARY_OFFSET_FIELD) => {
            return Err(Error::TypeSummaryOffset {
                class_descriptor: class_descriptor.to_owned(),
                field_off,
            });
        }
        (ES_MODULE_RECORD_DESCRIPTOR, TypeId::U32, Some(FieldValue::I32(off))) => {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            let data = decode_module_data_at(f, offset, strings).map_err(|e| {
                Error::ModuleData(format!("{class_descriptor} field at {field_off:#x}: {e}"))
            })?;
            module_data_offsets.insert(offset);
            Some(FieldValue::ModuleData(data))
        }
        (ES_SCOPE_NAMES_RECORD_DESCRIPTOR, TypeId::U32, Some(FieldValue::I32(off))) => {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            scope_names_offsets.insert(offset);
            Some(FieldValue::LiteralArrayRef(offset))
        }
        // `moduleRequestPhaseIdx` u32 fields (any class — merge-abc emits
        // them on the module's own record) reference untagged
        // module-request-phase blobs by file offset; decode structurally so
        // encode can re-emit and relocate (same dangling-offset class as
        // _ESModuleRecord/_ESScopeNamesRecord).
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(MODULE_REQUEST_PHASE_FIELD) =>
        {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            let phase = decode_module_request_phase_at(f, offset).map_err(|e| {
                Error::ModuleData(format!(
                    "{class_descriptor} moduleRequestPhaseIdx field at {field_off:#x}: {e}"
                ))
            })?;
            phase_blob_offsets.insert(offset);
            Some(FieldValue::ModuleRequestPhase(phase))
        }
        (_, _, value) => value,
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(fr, sys::abc_field_enumerate_annotations),
            entity_map,
            strings,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(fr, sys::abc_field_enumerate_runtime_annotations),
            entity_map,
            strings,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(fr, sys::abc_field_enumerate_type_annotations),
            entity_map,
            strings,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(fr, sys::abc_field_enumerate_runtime_type_annotations),
            entity_map,
            strings,
        )?,
    };

    Ok(Field {
        name,
        offset: field_off,
        field_type,
        access_flags: AccessFlags::from_bits_truncate(unsafe { sys::abc_field_access_flags(fr) }),
        is_external: is_external(f, field_id),
        initial_value,
        annotations,
    })
}

/// Resolve the interned name of an entity offset. Falls back to reading the
/// name directly from a foreign field/method item via the bridge (which
/// bounds-checks the item+4 name_off read against the header-declared
/// foreign region and file size) when the entity_map has no entry — foreign
/// members are not class members and never enter the entity_map (test
/// group A).
fn resolve_foreign_entity_name(
    f: *const sys::AbcFileHandle,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    off: u32,
) -> StringId {
    if let Some(&sid) = entity_map.get(&off) {
        return sid;
    }
    let name_off = unsafe { sys::abc_foreign_item_name_off(f, off) };
    if name_off == ABSENT {
        return strings.get_or_intern("");
    }
    match read_string(f, name_off) {
        Some(name) => strings.get_or_intern(&name),
        None => strings.get_or_intern(""),
    }
}

/// Returns `(MethodBody, byte_offsets)` where `byte_offsets[i]` is the byte
/// offset of instruction `i` in the raw bytecode.  The table is needed by
/// `read_debug_info` to convert debug byte-offsets to instruction indices.
fn decode_code_at(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    code_off: u32,
) -> Result<(MethodBody, Vec<u32>), Error> {
    let cr = unsafe { sys::abc_code_open(f as *mut _, code_off) };
    if cr.is_null() {
        return Err(Error::InvalidOffset(code_off));
    }
    let _cg = HandleGuard(Some(|| unsafe { sys::abc_code_close(cr) }));

    let raw_insns = {
        let ptr = unsafe { sys::abc_code_instructions(cr) };
        let len = unsafe { sys::abc_code_code_size(cr) } as usize;
        if ptr.is_null() || len == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    };
    let decoded = abcd_isa::decode(raw_insns).map_err(|source| Error::BytecodeDecode {
        method_offset: method_off,
        source,
    })?;

    // Split into instructions and a byte-offset table for try-block conversion.
    let (bytecodes, byte_offsets): (Vec<_>, Vec<_>) = decoded.into_iter().unzip();
    let code_byte_len = raw_insns.len() as u32;

    // Convert a byte offset to an instruction index.
    // If the offset equals code_byte_len (one past the end), return bytecodes.len().
    let offset_to_index = |off: u32| -> u32 {
        if off == code_byte_len {
            bytecodes.len() as u32
        } else {
            byte_offsets.binary_search(&off).unwrap_or_else(|i| i) as u32
        }
    };

    let try_blocks = collect_try_blocks(f, method_off, cr)
        .into_iter()
        .map(|tb| {
            let start = offset_to_index(tb.start);
            let end = offset_to_index(tb.start + tb.len);
            TryBlock {
                start,
                len: end - start,
                catches: tb
                    .catches
                    .into_iter()
                    .map(|cb| {
                        let handler = offset_to_index(cb.handler);
                        let handler_end = offset_to_index(cb.handler + cb.len);
                        CatchBlock {
                            type_idx: cb.type_idx,
                            handler,
                            len: handler_end - handler,
                        }
                    })
                    .collect(),
            }
        })
        .collect();

    let num_vregs = unsafe { sys::abc_code_num_vregs(cr) };
    let num_args = unsafe { sys::abc_code_num_args(cr) };

    Ok((
        MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            entity_offsets: HashMap::new(),
            try_blocks,
        },
        byte_offsets,
    ))
}

fn decode_proto_types(
    f: *const sys::AbcFileHandle,
    proto_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<(Type, Vec<Type>), Error> {
    let pr = unsafe { sys::abc_proto_open(f as *mut _, proto_off) };
    if pr.is_null() {
        return Err(Error::InvalidOffset(proto_off));
    }
    let _pg = HandleGuard(Some(|| unsafe { sys::abc_proto_close(pr) }));

    let ref_num = unsafe { sys::abc_proto_get_ref_num(pr) };
    let ref_descs: Vec<Option<StringId>> = (0..ref_num)
        .map(|i| {
            let off = unsafe { sys::abc_proto_get_reference_type(pr, i) };
            if off == u32::MAX {
                None
            } else {
                entity_map.get(&off).copied()
            }
        })
        .collect();
    let mut ref_iter = ref_descs.into_iter();

    let mut resolve = |raw: TypeId, ctx: &str| -> Result<Type, Error> {
        if raw == TypeId::Reference {
            let desc = ref_iter.next().flatten().ok_or_else(|| Error::Malformed {
                field: "reference_type",
                context: ctx.to_string(),
            })?;
            Ok(Type::Reference(desc))
        } else {
            Type::from_raw(raw, None)
        }
    };

    let raw_ret = TypeId::try_from(unsafe { sys::abc_proto_get_return_type(pr) })?;
    let return_type = resolve(raw_ret, "return type")?;

    let num_args = unsafe { sys::abc_proto_num_args(pr) };
    let arg_types = (0..num_args)
        .map(|i| {
            let raw = TypeId::try_from(unsafe { sys::abc_proto_get_arg_type(pr, i) })?;
            resolve(raw, &format!("arg {i}"))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Suppress unused variable warning — strings is reserved for future use
    // when reference type descriptors need interning at this level.
    let _ = strings;

    Ok((return_type, arg_types))
}

fn decode_class_annotations(
    f: *const sys::AbcFileHandle,
    cr: *mut sys::AbcClassAccessor,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<Annotations, Error> {
    Ok(Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(cr, sys::abc_class_enumerate_annotations),
            entity_map,
            strings,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(cr, sys::abc_class_enumerate_runtime_annotations),
            entity_map,
            strings,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(cr, sys::abc_class_enumerate_type_annotations),
            entity_map,
            strings,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(cr, sys::abc_class_enumerate_runtime_type_annotations),
            entity_map,
            strings,
        )?,
    })
}

fn decode_annotation_list(
    f: *const sys::AbcFileHandle,
    offsets: &[u32],
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<Vec<Annotation>, Error> {
    use sys::AnnotationValueType as AVT;

    offsets
        .iter()
        .map(|&off| {
            let ar = unsafe { sys::abc_annotation_open(f as *mut _, off) };
            if ar.is_null() {
                return Err(Error::InvalidOffset(off));
            }
            let _ag = HandleGuard(Some(|| unsafe { sys::abc_annotation_close(ar) }));

            let class_off = unsafe { sys::abc_annotation_class_off(ar) };
            let class_descriptor =
                entity_map
                    .get(&class_off)
                    .copied()
                    .ok_or_else(|| Error::Malformed {
                        field: "class_descriptor",
                        context: format!("annotation at offset {off:#x}"),
                    })?;

            let count = unsafe { sys::abc_annotation_count(ar) };
            let elements = (0..count)
                .filter_map(|idx| {
                    let mut out = sys::AbcAnnotationElem {
                        name_off: 0,
                        tag: 0,
                        value: 0,
                    };
                    let rc = unsafe { sys::abc_annotation_get_element(ar, idx, &mut out) };
                    if rc != 0 {
                        return None;
                    }
                    let name_str = read_string(f, out.name_off)?;
                    let name = strings.get_or_intern(&name_str);
                    let tag = AVT::try_from(out.tag).unwrap_or(AVT::Unknown);
                    let value = match tag {
                        AVT::U1 => AnnotationValue::Bool(out.value != 0),
                        AVT::I8 => AnnotationValue::I8(out.value as i8),
                        AVT::U8 => AnnotationValue::U8(out.value as u8),
                        AVT::I16 => AnnotationValue::I16(out.value as i16),
                        AVT::U16 => AnnotationValue::U16(out.value as u16),
                        AVT::I32 => AnnotationValue::I32(out.value as i32),
                        AVT::U32 => AnnotationValue::U32(out.value),
                        AVT::I64 => {
                            let mut v = 0i64;
                            if unsafe { sys::abc_annotation_get_value_i64(ar, idx, &mut v) } == 0 {
                                AnnotationValue::I64(v)
                            } else {
                                return None;
                            }
                        }
                        AVT::U64 => {
                            let mut v = 0u64;
                            if unsafe { sys::abc_annotation_get_value_u64(ar, idx, &mut v) } == 0 {
                                AnnotationValue::U64(v)
                            } else {
                                return None;
                            }
                        }
                        AVT::F32 => AnnotationValue::F32(f32::from_bits(out.value)),
                        AVT::F64 => {
                            let mut v = 0.0f64;
                            if unsafe { sys::abc_annotation_get_value_f64(ar, idx, &mut v) } == 0 {
                                AnnotationValue::F64(v)
                            } else {
                                return None;
                            }
                        }
                        AVT::String => {
                            let s = read_string(f, out.value).unwrap_or_default();
                            let sid = strings.get_or_intern(&s);
                            AnnotationValue::String(sid)
                        }
                        AVT::Record => {
                            let sid = entity_map
                                .get(&out.value)
                                .copied()
                                .unwrap_or_else(|| strings.get_or_intern(""));
                            AnnotationValue::Record(sid)
                        }
                        AVT::Method => {
                            let sid =
                                resolve_foreign_entity_name(f, entity_map, strings, out.value);
                            AnnotationValue::Method {
                                name: sid,
                                offset: out.value,
                            }
                        }
                        AVT::Enum => {
                            let sid =
                                resolve_foreign_entity_name(f, entity_map, strings, out.value);
                            AnnotationValue::Enum {
                                name: sid,
                                offset: out.value,
                            }
                        }
                        AVT::Annotation => {
                            // Recursively resolve nested annotation.
                            match decode_annotation_list(f, &[out.value], entity_map, strings) {
                                Ok(mut list) if !list.is_empty() => {
                                    AnnotationValue::Annotation(Box::new(list.remove(0)))
                                }
                                _ => {
                                    // Fallback: if resolution fails, store as Void.
                                    AnnotationValue::Void
                                }
                            }
                        }
                        AVT::MethodHandle => {
                            let mut handle_type_raw = 0u8;
                            let mut entity_off = 0u32;
                            let rc = unsafe {
                                sys::abc_method_handle_read(
                                    f as *mut _,
                                    out.value,
                                    &mut handle_type_raw,
                                    &mut entity_off,
                                )
                            };
                            if rc == 0 {
                                if let Some(ht) = MethodHandleType::from_u8(handle_type_raw) {
                                    let entity = entity_map
                                        .get(&entity_off)
                                        .copied()
                                        .unwrap_or_else(|| strings.get_or_intern(""));
                                    AnnotationValue::MethodHandle(ResolvedMethodHandle {
                                        handle_type: ht,
                                        entity,
                                        entity_offset: entity_off,
                                    })
                                } else {
                                    AnnotationValue::Void
                                }
                            } else {
                                AnnotationValue::Void
                            }
                        }
                        AVT::LiteralArray => {
                            // '#' is the SCALAR literal-array tag in the
                            // vendored data model: pandasm GetCharAsType maps
                            // '#' to Type::LITERALARRAY and GetArrayTypeAsChar
                            // has no literal-array case (arrays of literal
                            // arrays are not representable upstream). The
                            // element value IS the literal array's offset
                            // (vendored disassembler reads it via
                            // GetScalarValue, disassembler.cpp:569-574).
                            // Trying the array interpretation first reads the
                            // target array's own item count as an array
                            // length — pure misparse (F-new-2 evidence).
                            let values = decode_literal_array_at(f, out.value, strings);
                            AnnotationValue::LiteralArray(values)
                        }
                        AVT::Void => AnnotationValue::Void,
                        AVT::StringNullptr => AnnotationValue::StringNullptr,
                        AVT::Array
                        | AVT::ArrayU1
                        | AVT::ArrayI8
                        | AVT::ArrayU8
                        | AVT::ArrayI16
                        | AVT::ArrayU16
                        | AVT::ArrayI32
                        | AVT::ArrayU32
                        | AVT::ArrayI64
                        | AVT::ArrayU64
                        | AVT::ArrayF32
                        | AVT::ArrayF64
                        | AVT::ArrayString
                        | AVT::ArrayRecord
                        | AVT::ArrayMethod
                        | AVT::ArrayEnum
                        | AVT::ArrayAnnotation
                        | AVT::ArrayMethodHandle => {
                            let mut arr = sys::AbcAnnotationArrayVal {
                                count: 0,
                                entity_off: 0,
                            };
                            if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) }
                                == 0
                            {
                                let values = decode_annotation_array_elements(
                                    f,
                                    out.tag,
                                    arr.count,
                                    arr.entity_off,
                                    entity_map,
                                    strings,
                                );
                                AnnotationValue::Array {
                                    tag: out.tag,
                                    values,
                                }
                            } else {
                                AnnotationValue::U32(out.value)
                            }
                        }
                        AVT::Unknown => AnnotationValue::U32(out.value),
                    };
                    Some(AnnotationElem { name, value })
                })
                .collect();

            Ok(Annotation {
                class_descriptor,
                elements,
            })
        })
        .collect()
}

/// Resolve annotation array elements at the given entity offset.
///
/// The `tag` determines element type and size; raw values are read via the
/// C bridge `abc_annotation_array_read` and converted to `AnnotationValue`.
fn decode_annotation_array_elements(
    f: *const sys::AbcFileHandle,
    tag: u8,
    count: u32,
    entity_offset: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Vec<AnnotationValue> {
    use sys::AnnotationValueType as AVT;

    if count == 0 {
        return Vec::new();
    }

    // Determine element size from the array tag.
    let element_size: u32 = match AVT::try_from(tag) {
        Ok(AVT::ArrayU1 | AVT::ArrayI8 | AVT::ArrayU8) => 1,
        Ok(AVT::ArrayI16 | AVT::ArrayU16) => 2,
        Ok(
            AVT::ArrayI32
            | AVT::ArrayU32
            | AVT::ArrayF32
            | AVT::ArrayString
            | AVT::ArrayRecord
            | AVT::ArrayMethod
            | AVT::ArrayEnum
            | AVT::ArrayAnnotation
            | AVT::ArrayMethodHandle
            | AVT::LiteralArray,
        ) => 4,
        Ok(AVT::ArrayI64 | AVT::ArrayU64 | AVT::ArrayF64) => 8,
        _ => return Vec::new(),
    };

    let mut raw_values = vec![0u64; count as usize];
    let n = unsafe {
        sys::abc_annotation_array_read(
            f,
            entity_offset,
            element_size,
            count,
            raw_values.as_mut_ptr(),
            count,
        )
    };
    if n < 0 {
        return Vec::new();
    }
    let n = n as usize;

    // Convert raw values to AnnotationValue based on element tag.
    raw_values[..n]
        .iter()
        .map(|&raw| match AVT::try_from(tag) {
            Ok(AVT::ArrayU1) => AnnotationValue::Bool(raw != 0),
            Ok(AVT::ArrayI8) => AnnotationValue::I8(raw as i8),
            Ok(AVT::ArrayU8) => AnnotationValue::U8(raw as u8),
            Ok(AVT::ArrayI16) => AnnotationValue::I16(raw as i16),
            Ok(AVT::ArrayU16) => AnnotationValue::U16(raw as u16),
            Ok(AVT::ArrayI32) => AnnotationValue::I32(raw as i32),
            Ok(AVT::ArrayU32) => AnnotationValue::U32(raw as u32),
            Ok(AVT::ArrayI64) => AnnotationValue::I64(raw as i64),
            Ok(AVT::ArrayU64) => AnnotationValue::U64(raw),
            Ok(AVT::ArrayF32) => AnnotationValue::F32(f32::from_bits(raw as u32)),
            Ok(AVT::ArrayF64) => AnnotationValue::F64(f64::from_bits(raw)),
            Ok(AVT::ArrayString) => {
                let s = read_string(f, raw as u32).unwrap_or_default();
                AnnotationValue::String(strings.get_or_intern(&s))
            }
            Ok(AVT::ArrayRecord) => {
                let sid = entity_map
                    .get(&(raw as u32))
                    .copied()
                    .unwrap_or_else(|| strings.get_or_intern(""));
                AnnotationValue::Record(sid)
            }
            Ok(AVT::ArrayMethod) => {
                let sid = resolve_foreign_entity_name(f, entity_map, strings, raw as u32);
                AnnotationValue::Method {
                    name: sid,
                    offset: raw as u32,
                }
            }
            Ok(AVT::ArrayEnum) => {
                let sid = resolve_foreign_entity_name(f, entity_map, strings, raw as u32);
                AnnotationValue::Enum {
                    name: sid,
                    offset: raw as u32,
                }
            }
            Ok(AVT::ArrayAnnotation) => {
                match decode_annotation_list(f, &[raw as u32], entity_map, strings) {
                    Ok(mut list) if !list.is_empty() => {
                        AnnotationValue::Annotation(Box::new(list.remove(0)))
                    }
                    _ => AnnotationValue::Void,
                }
            }
            Ok(AVT::LiteralArray) => {
                AnnotationValue::LiteralArray(decode_literal_array_at(f, raw as u32, strings))
            }
            Ok(AVT::ArrayMethodHandle) => {
                let mut handle_type_raw = 0u8;
                let mut entity_off = 0u32;
                let rc = unsafe {
                    sys::abc_method_handle_read(
                        f as *mut _,
                        raw as u32,
                        &mut handle_type_raw,
                        &mut entity_off,
                    )
                };
                if rc == 0 {
                    if let Some(ht) = MethodHandleType::from_u8(handle_type_raw) {
                        let entity = entity_map
                            .get(&entity_off)
                            .copied()
                            .unwrap_or_else(|| strings.get_or_intern(""));
                        AnnotationValue::MethodHandle(ResolvedMethodHandle {
                            handle_type: ht,
                            entity,
                            entity_offset: entity_off,
                        })
                    } else {
                        AnnotationValue::Void
                    }
                } else {
                    AnnotationValue::Void
                }
            }
            _ => AnnotationValue::U32(raw as u32),
        })
        .collect()
}

/// Decode a single literal array at the given entity offset.
fn decode_literal_array_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut StringPool,
) -> Vec<crate::LiteralValue> {
    // We need a valid literal accessor handle for the panda_file reference.
    // The EnumerateLiteralVals overload reads from the given offset directly.
    let lr = unsafe { sys::abc_literal_open(f, offset) };
    if lr.is_null() {
        return Vec::new();
    }
    let _lg = HandleGuard(Some(|| unsafe { sys::abc_literal_close(lr) }));

    let mut ctx = crate::literal::LiteralCollectCtx {
        file: f,
        strings: strings as *mut StringPool,
        values: Vec::new(),
    };
    unsafe {
        sys::abc_literal_enumerate_vals(
            lr,
            offset,
            Some(crate::literal::collect_literal_val_cb),
            &mut ctx as *mut crate::literal::LiteralCollectCtx as *mut c_void,
        );
    }
    ctx.values
}

fn decode_literal_arrays(
    f: *const sys::AbcFileHandle,
    strings: &mut StringPool,
    referenced_offsets: &HashSet<u32>,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
) -> (Vec<LiteralArray>, HashMap<u32, u32>) {
    let n = unsafe { sys::abc_file_num_literalarrays(f) };
    let mut offsets = Vec::new();
    if n != 0 {
        for i in 0..n {
            let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
            // Module-record and module-request-phase blobs ride the legacy
            // header table on <=12.x but are NOT tagged literal arrays; they
            // are modeled structurally (FieldValue::ModuleData /
            // FieldValue::ModuleRequestPhase) and must never be decoded here.
            if off != ABSENT
                && !module_data_offsets.contains(&off)
                && !phase_blob_offsets.contains(&off)
            {
                offsets.push(off);
            }
        }
    }
    // N20: `referenced_offsets` is a HashSet — iterating it directly would
    // append the extras in hash order, permuting the decoded literal-array
    // table (and every LiteralarrayId table index derived from it) between
    // runs. Sort the candidates so the table order is canonical.
    let mut referenced: Vec<u32> = referenced_offsets
        .iter()
        .copied()
        .filter(|&off| {
            off != ABSENT
                && !offsets.contains(&off)
                && !module_data_offsets.contains(&off)
                && !phase_blob_offsets.contains(&off)
        })
        .collect();
    referenced.sort_unstable();
    offsets.extend(referenced);
    if offsets.is_empty() {
        return (Vec::new(), HashMap::new());
    }

    // Collect file offsets first so nested LiteralArray references (which
    // store the referenced array's file offset) can be rewritten to table
    // indices — the model's documented semantic.
    let mut offset_to_index: HashMap<u32, u32> = HashMap::new();
    for (i, &off) in offsets.iter().enumerate() {
        offset_to_index.insert(off, i as u32);
    }

    let first_off = offsets[0];
    let lr = unsafe { sys::abc_literal_open(f, first_off) };
    if lr.is_null() {
        return (Vec::new(), offset_to_index);
    }
    let _lg = HandleGuard(Some(|| unsafe { sys::abc_literal_close(lr) }));

    // Nested-reference recovery (v2-P1a): a LITERALARRAY payload holds the
    // target array's FILE OFFSET, and class buffers (sendable classes on
    // 13.x/24.x) reference arrays registered nowhere — not in the header
    // table and not in any method index region. Recover them transitively:
    // `offsets` doubles as the worklist, and an offset is registered in
    // `offset_to_index` BEFORE its array is decoded, so reference cycles
    // terminate and every offset is decoded at most once per table entry.
    // Newly discovered offsets are appended in sorted batches, keeping the
    // table order deterministic (N20). The module-record / request-phase
    // exclusions apply to nested candidates exactly as to table entries:
    // those blobs are untagged and must never be decoded here (a reference
    // to one stays a raw offset, the pre-existing representation).
    let mut arrays: Vec<LiteralArray> = Vec::with_capacity(offsets.len());
    let mut decoded = 0usize;
    while decoded < offsets.len() {
        let mut nested: Vec<u32> = Vec::new();
        for &off in &offsets[decoded..] {
            let mut ctx = crate::literal::LiteralCollectCtx {
                file: f,
                strings: strings as *mut StringPool,
                values: Vec::new(),
            };
            unsafe {
                sys::abc_literal_enumerate_vals(
                    lr,
                    off,
                    Some(crate::literal::collect_literal_val_cb),
                    &mut ctx as *mut crate::literal::LiteralCollectCtx as *mut c_void,
                );
            }
            for value in &ctx.values {
                if let LiteralValue::LiteralArray(idx) = value {
                    let target = idx.0;
                    if target != ABSENT
                        && !offset_to_index.contains_key(&target)
                        && !module_data_offsets.contains(&target)
                        && !phase_blob_offsets.contains(&target)
                    {
                        nested.push(target);
                    }
                }
            }
            arrays.push(LiteralArray { values: ctx.values });
        }
        decoded = offsets.len();
        nested.sort_unstable();
        nested.dedup();
        for off in nested {
            offset_to_index.insert(off, offsets.len() as u32);
            offsets.push(off);
        }
    }

    // Rewrite nested references (file offset → table index).
    for arr in &mut arrays {
        for v in &mut arr.values {
            if let LiteralValue::LiteralArray(idx) = v {
                if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                    idx.0 = table_idx;
                }
            }
        }
    }
    (arrays, offset_to_index)
}

/// Intermediate struct for collecting debug info strings before interning.
struct RawLocalVarInfo {
    name: String,
    type_name: String,
    type_signature: String,
    reg_number: i32,
    start: u32,
    end: u32,
}

struct RawParamInfo {
    name: String,
    signature: String,
}

fn read_debug_info(
    debug_raw: *mut sys::AbcDebugInfo,
    method_off: u32,
    byte_offsets: &[u32],
    strings: &mut StringPool,
) -> MethodDebugInfo {
    // Convert a raw byte offset to an instruction index using the byte_offsets
    // table produced by decode_code_at.  Falls back to identity when the table
    // is empty (no bytecode).
    let to_index = |off: u32| -> u32 {
        if byte_offsets.is_empty() {
            return off;
        }
        byte_offsets.binary_search(&off).unwrap_or_else(|i| i) as u32
    };

    let source_file = {
        let ptr = unsafe { sys::abc_debug_get_source_file(debug_raw, method_off) };
        if ptr.is_null() {
            None
        } else {
            let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy();
            Some(strings.get_or_intern(s.as_ref()))
        }
    };
    let source_code = {
        let ptr = unsafe { sys::abc_debug_get_source_code(debug_raw, method_off) };
        if ptr.is_null() {
            None
        } else {
            let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy();
            Some(strings.get_or_intern(s.as_ref()))
        }
    };

    // Collect raw byte-offset entries, then convert to instruction indices.
    let mut line_table: Vec<LineEntry> = {
        let mut result = Vec::new();
        unsafe extern "C" fn cb(entry: *const sys::AbcLineEntry, ctx: *mut c_void) -> i32 {
            let vec = unsafe { &mut *(ctx as *mut Vec<LineEntry>) };
            let e = unsafe { &*entry };
            vec.push(LineEntry {
                index: e.offset,
                line: e.line,
            });
            0
        }
        unsafe {
            sys::abc_debug_get_line_table(
                debug_raw,
                method_off,
                Some(cb),
                &mut result as *mut Vec<LineEntry> as *mut c_void,
            );
        }
        result
    };
    for entry in &mut line_table {
        entry.index = to_index(entry.index);
    }

    let mut column_table: Vec<ColumnEntry> = {
        let mut result = Vec::new();
        unsafe extern "C" fn cb(entry: *const sys::AbcColumnEntry, ctx: *mut c_void) -> i32 {
            let vec = unsafe { &mut *(ctx as *mut Vec<ColumnEntry>) };
            let e = unsafe { &*entry };
            vec.push(ColumnEntry {
                index: e.offset,
                column: e.column,
            });
            0
        }
        unsafe {
            sys::abc_debug_get_column_table(
                debug_raw,
                method_off,
                Some(cb),
                &mut result as *mut Vec<ColumnEntry> as *mut c_void,
            );
        }
        result
    };
    for entry in &mut column_table {
        entry.index = to_index(entry.index);
    }

    // Collect raw local var info first (with owned Strings), then intern.
    let mut raw_local_vars: Vec<RawLocalVarInfo> = {
        let mut result = Vec::new();
        unsafe extern "C" fn cb(info: *const sys::AbcLocalVarInfo, ctx: *mut c_void) -> i32 {
            let vec = unsafe { &mut *(ctx as *mut Vec<RawLocalVarInfo>) };
            let i = unsafe { &*info };
            let name = if i.name.is_null() {
                String::new()
            } else {
                unsafe { CStr::from_ptr(i.name) }
                    .to_string_lossy()
                    .into_owned()
            };
            let type_name = if i.type_.is_null() {
                String::new()
            } else {
                unsafe { CStr::from_ptr(i.type_) }
                    .to_string_lossy()
                    .into_owned()
            };
            let type_signature = if i.type_signature.is_null() {
                String::new()
            } else {
                unsafe { CStr::from_ptr(i.type_signature) }
                    .to_string_lossy()
                    .into_owned()
            };
            vec.push(RawLocalVarInfo {
                name,
                type_name,
                type_signature,
                reg_number: i.reg_number,
                start: i.start_offset,
                end: i.end_offset,
            });
            0
        }
        unsafe {
            sys::abc_debug_get_local_vars(
                debug_raw,
                method_off,
                Some(cb),
                &mut result as *mut Vec<RawLocalVarInfo> as *mut c_void,
            );
        }
        result
    };
    for var in &mut raw_local_vars {
        var.start = to_index(var.start);
        var.end = to_index(var.end);
    }
    let local_vars: Vec<LocalVarInfo> = raw_local_vars
        .into_iter()
        .map(|rv| LocalVarInfo {
            name: strings.get_or_intern(&rv.name),
            type_name: strings.get_or_intern(&rv.type_name),
            type_signature: strings.get_or_intern(&rv.type_signature),
            reg_number: rv.reg_number,
            start: rv.start,
            end: rv.end,
        })
        .collect();

    // Collect raw param info first, then intern.
    let raw_params: Vec<RawParamInfo> = {
        let mut result = Vec::new();
        unsafe extern "C" fn cb(info: *const sys::AbcParamInfo, ctx: *mut c_void) -> i32 {
            let vec = unsafe { &mut *(ctx as *mut Vec<RawParamInfo>) };
            let i = unsafe { &*info };
            let name = if i.name.is_null() {
                String::new()
            } else {
                unsafe { CStr::from_ptr(i.name) }
                    .to_string_lossy()
                    .into_owned()
            };
            let signature = if i.signature.is_null() {
                String::new()
            } else {
                unsafe { CStr::from_ptr(i.signature) }
                    .to_string_lossy()
                    .into_owned()
            };
            vec.push(RawParamInfo { name, signature });
            0
        }
        unsafe {
            sys::abc_debug_get_parameter_info(
                debug_raw,
                method_off,
                Some(cb),
                &mut result as *mut Vec<RawParamInfo> as *mut c_void,
            );
        }
        result
    };
    let params: Vec<ParamInfo> = raw_params
        .into_iter()
        .map(|rp| ParamInfo {
            name: strings.get_or_intern(&rp.name),
            signature: strings.get_or_intern(&rp.signature),
        })
        .collect();

    MethodDebugInfo {
        source_file,
        source_code,
        line_table,
        column_table,
        local_vars,
        params,
    }
}

// ---------------------------------------------------------------------------
// FFI helper: read strings from C accessors
// ---------------------------------------------------------------------------

fn read_class_descriptor(
    f: *const sys::AbcFileHandle,
    cr: *const sys::AbcClassAccessor,
) -> Option<String> {
    let class_id = unsafe { sys::abc_class_get_class_id(cr) };
    // The class item starts with its descriptor string; go through the
    // lossless string reader instead of the raw MUTF-8 pointer.
    read_string(f, class_id).or_else(|| {
        let ptr = unsafe { sys::abc_class_get_descriptor(cr) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr as *const _) };
        Some(cstr.to_string_lossy().into_owned())
    })
}

fn read_class_name(
    f: *const sys::AbcFileHandle,
    cr: *const sys::AbcClassAccessor,
) -> Option<String> {
    // The class item's name is its descriptor string; read it through the
    // lossless MUTF-8 path (same source as read_class_descriptor) instead of
    // the raw-byte abc_class_get_name view, which corrupts embedded NULs
    // (C0 80) and astral characters.
    let class_id = unsafe { sys::abc_class_get_class_id(cr) };
    read_string(f, class_id)
}

fn read_method_name(mr: *const sys::AbcMethodAccessor) -> Option<String> {
    // Lossless: MUTF-8 -> UTF-16 via the bridge (the raw C-string view
    // corrupts embedded NULs encoded as C0 80 — test group G).
    let units = unsafe { sys::abc_method_get_name_utf16(mr, std::ptr::null_mut(), 0) };
    if units == 0 {
        return None;
    }
    let mut buf = vec![0u16; units as usize];
    unsafe {
        sys::abc_method_get_name_utf16(mr, buf.as_mut_ptr(), buf.len());
    }
    String::from_utf16(&buf).ok()
}

// ---------------------------------------------------------------------------
// FFI helper: collect offsets via callbacks
// ---------------------------------------------------------------------------

/// Collect u32 offsets from a void-returning enumerate callback.
fn collect_offsets_void<T>(
    raw: *mut T,
    enumerate: unsafe extern "C" fn(
        *mut T,
        Option<unsafe extern "C" fn(u32, *mut c_void)>,
        *mut c_void,
    ),
) -> Vec<u32> {
    let mut result = Vec::new();
    unsafe extern "C" fn cb(offset: u32, ctx: *mut c_void) {
        let vec = unsafe { &mut *(ctx as *mut Vec<u32>) };
        vec.push(offset);
    }
    unsafe { enumerate(raw, Some(cb), &mut result as *mut Vec<u32> as *mut c_void) };
    result
}

/// Collect u32 offsets from an int-returning enumerate callback.
fn collect_offsets_int<T>(
    raw: *mut T,
    enumerate: unsafe extern "C" fn(
        *mut T,
        Option<unsafe extern "C" fn(u32, *mut c_void) -> i32>,
        *mut c_void,
    ),
) -> Vec<u32> {
    let mut result = Vec::new();
    unsafe extern "C" fn cb(offset: u32, ctx: *mut c_void) -> i32 {
        let vec = unsafe { &mut *(ctx as *mut Vec<u32>) };
        vec.push(offset);
        0
    }
    unsafe { enumerate(raw, Some(cb), &mut result as *mut Vec<u32> as *mut c_void) };
    result
}

/// Collect try-blocks from a code accessor. Typed catch entries store a
/// region class *index* in the file; decode resolves it to the class entity
/// offset so the model carries entity identity (catch-all stays UINT32_MAX).
fn collect_try_blocks(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    cr: *mut sys::AbcCodeAccessor,
) -> Vec<TryBlock> {
    struct Ctx {
        f: *const sys::AbcFileHandle,
        method_off: u32,
        blocks: Vec<TryBlock>,
    }
    let mut ctx = Ctx {
        f,
        method_off,
        blocks: Vec::new(),
    };
    unsafe extern "C" fn cb(
        try_info: *const sys::AbcTryBlockInfo,
        catches: *const sys::AbcCatchBlockInfo,
        ctx_raw: *mut c_void,
    ) -> i32 {
        let ctx = unsafe { &mut *(ctx_raw as *mut Ctx) };
        let info = unsafe { &*try_info };
        let catch_slice = if info.num_catches > 0 {
            unsafe { std::slice::from_raw_parts(catches, info.num_catches as usize) }
        } else {
            &[]
        };
        ctx.blocks.push(TryBlock {
            start: info.start_pc,
            len: info.length,
            catches: catch_slice
                .iter()
                .map(|c| CatchBlock {
                    type_idx: if c.type_idx == u32::MAX {
                        u32::MAX
                    } else {
                        unsafe {
                            sys::abc_resolve_class_index(ctx.f, ctx.method_off, c.type_idx as u16)
                        }
                    },
                    handler: c.handler_pc,
                    len: c.code_size,
                })
                .collect(),
        });
        0
    }
    unsafe {
        sys::abc_code_enumerate_try_blocks_full(cr, Some(cb), &mut ctx as *mut Ctx as *mut c_void);
    }
    ctx.blocks
}
