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
    // Legacy ISA gate: files written by the pre-2022-08-18 toolchain
    // (OpenHarmony 3.0/3.1-era, header version 0.0.0.2 — seen in the wild on
    // 3.2/4.0 devices) use the old opcode numbering (0xff-prefixed ecma
    // instructions) and old operand encoding (32-bit string file offsets,
    // 16-bit global literal-array indices). Their bytecode is decoded via
    // abcd_isa::decode_legacy and their entity operands resolved with legacy
    // rules below.
    let legacy = version == abcd_isa::Version::new(0, 0, 0, 2);
    let legacy_lit_table = if legacy {
        legacy_literalarray_table(data)
    } else {
        None
    };
    let checksum = abc.checksum();
    let size = abc.size();
    let file_type = crate::file::file_type(data);

    let mut strings = StringPool::new();

    // Open debug info (file-level, lives for entire decode).
    //
    // N55 (second half): a null handle means the vendored extractor
    // THREW during construction — e.g. a debug item whose line program
    // never SET_FILEs in a class without a source-file record leaves
    // `file_ = File::EntityId(0)`, and reading it hits
    // `GetSpanFromId`'s `ThrowIfWithCheck(..., INVALID_FILE_OFFSET)`
    // (vendored file.h:186-193 via debug_info_extractor.cpp:252's
    // `value_or(File::EntityId(0))` and line_number_program.h
    // `LineProgramState::GetFile`); the bridge swallows the exception
    // and returns nullptr (file_bridge.cpp `abc_debug_info_open`). A
    // file with NO debug items never throws (the extractor skips
    // methods without a debug_info_id), so null is never benign.
    // Previously decode treated null as "no debug info" — silently
    // dropping the WHOLE file's debug region. Per the N55 ruling that
    // is now a hard error, never silent.
    let debug_raw = unsafe { sys::abc_debug_info_open(f) };
    if debug_raw.is_null() {
        return Err(Error::DebugInfoExtraction);
    }
    let _debug_guard = HandleGuard(Some(move || unsafe {
        sys::abc_debug_info_close(debug_raw)
    }));

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
            if let Some(sid) = crate::file::intern_string(f, class_off, &mut strings) {
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
                && let Some(sid) = crate::file::intern_string(f, name_off, &mut strings)
            {
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
            if let Some(descriptor) = crate::file::intern_string(f, class_off, &mut strings) {
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
            .map(|off| decode_method_at(f, off, debug_raw, &entity_map, &mut strings, legacy))
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
                // Vacuous today: EntityKind is generated with exactly these
                // three variants (abcd-isa-sys templates/bytecode.rs.erb
                // collects every `id?` operand role). Future-proofing
                // against ISA-template growth, not a reachable filter.
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
                if legacy {
                    // Legacy (0.0.0.2) operand encoding: string operands are
                    // direct 32-bit file offsets (the string index region did
                    // not exist yet); method operands are 16-bit indices into
                    // the method's index region (same layout as today);
                    // literal-array operands are 16-bit indices into the
                    // header's global literal-array table (deprecated by the
                    // 2022-08-18 refactoring).
                    let offset = match kind {
                        EntityKind::StringId => {
                            let off = id.0;
                            if off == 0 || off as usize >= data.len() {
                                return Err(invalid());
                            }
                            off
                        }
                        EntityKind::MethodId => {
                            let index = u16::try_from(id.0).map_err(|_| invalid())?;
                            let offset = unsafe {
                                sys::abc_resolve_offset_by_index(f, method.offset, index)
                            };
                            if offset == ABSENT {
                                return Err(invalid());
                            }
                            offset
                        }
                        EntityKind::LiteralarrayId => {
                            // Unreachable by construction: no legacy opcode
                            // decodes to a variant with a LiteralarrayId
                            // entity operand (abcd-isa/src/legacy_table.rs
                            // maps the create*withbuffer family to the
                            // Imm-only Deprecated* variants); legacy
                            // literal-array references arrive through the
                            // blob pass below instead. Kept for symmetry
                            // with the modern arm.
                            let Some((count, table_off)) = legacy_lit_table else {
                                return Err(invalid());
                            };
                            if id.0 >= count {
                                return Err(invalid());
                            }
                            let bytes: [u8; 4] =
                                id.0.checked_mul(4)
                                    .and_then(|n| table_off.checked_add(n))
                                    .and_then(|entry| usize::try_from(entry).ok())
                                    .and_then(|entry| {
                                        entry.checked_add(4).and_then(|end| data.get(entry..end))
                                    })
                                    .and_then(|s| s.try_into().ok())
                                    .ok_or_else(invalid)?;
                            let off = u32::from_le_bytes(bytes);
                            if off == 0 || off as usize >= data.len() {
                                return Err(invalid());
                            }
                            off
                        }
                    };
                    body.entity_offsets.insert((kind, id.0), offset);
                    if kind == EntityKind::LiteralarrayId || entity_map.contains_key(&offset) {
                        continue;
                    }
                    if kind == EntityKind::StringId {
                        let sid = crate::file::intern_string(f, offset, &mut strings)
                            .ok_or_else(invalid)?;
                        entity_map.insert(offset, sid);
                        continue;
                    }
                    let name = {
                        let accessor = unsafe { sys::abc_method_open(f, offset) };
                        if accessor.is_null() {
                            return Err(invalid());
                        }
                        let _guard =
                            HandleGuard(Some(|| unsafe { sys::abc_method_close(accessor) }));
                        read_method_name(accessor)
                    }
                    .ok_or_else(invalid)?;
                    entity_map.insert(offset, strings.get_or_intern(&name));
                    continue;
                }
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
                if kind == EntityKind::StringId {
                    let sid =
                        crate::file::intern_string(f, offset, &mut strings).ok_or_else(invalid)?;
                    entity_map.insert(offset, sid);
                    continue;
                }
                let name = {
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

    // Legacy (0.0.0.2): the create*withbuffer family carries the literal
    // array as a plain 16-bit immediate (a global index into the header
    // table), not as a typed id operand, so the entity_operands pass above
    // never sees it. Collect those references here so the literal arrays
    // enter the model exactly like modern ones.
    if legacy {
        for method in classes.values_mut().flat_map(|class| &mut class.methods) {
            let Some(body) = &mut method.body else {
                continue;
            };
            for bytecode in &body.bytecodes {
                use abcd_isa::Bytecode as B;
                let global_idx = match bytecode {
                    B::DeprecatedCreateobjectwithbuffer(abcd_isa::Imm(i))
                    | B::DeprecatedCreatearraywithbuffer(abcd_isa::Imm(i))
                    | B::DeprecatedCreateobjecthavingmethod(abcd_isa::Imm(i))
                    | B::DeprecatedDefineclasswithbuffer(_, abcd_isa::Imm(i), _, _, _) => *i,
                    _ => continue,
                };
                let invalid = || Error::Malformed {
                    field: "legacy literal-array reference",
                    context: format!(
                        "{} in method {:#x}: global index {global_idx}",
                        bytecode.mnemonic(),
                        method.offset,
                    ),
                };
                let Ok(idx) = u32::try_from(global_idx) else {
                    return Err(invalid());
                };
                let Some((count, table_off)) = legacy_lit_table else {
                    return Err(invalid());
                };
                if idx >= count {
                    return Err(invalid());
                }
                let bytes: [u8; 4] = idx
                    .checked_mul(4)
                    .and_then(|n| table_off.checked_add(n))
                    .and_then(|entry| usize::try_from(entry).ok())
                    .and_then(|entry| entry.checked_add(4).and_then(|end| data.get(entry..end)))
                    .and_then(|s| s.try_into().ok())
                    .ok_or_else(invalid)?;
                let off = u32::from_le_bytes(bytes);
                if off == 0 || off as usize >= data.len() {
                    return Err(invalid());
                }
                body.entity_offsets
                    .insert((abcd_isa::EntityKind::LiteralarrayId, idx), off);
            }
        }
    }

    // --- literal arrays ---
    // API13/24 no longer expose a usable header count. Collect literal-array
    // offsets reached through method index regions so they can be decoded on
    // demand alongside legacy table entries. Scope-names blobs
    // (`_ESScopeNamesRecord` field values) and nested `LiteralTag::LiteralArray`
    // targets inside annotation-embedded literal arrays (`L_ESTypeAnnotation;`
    // `_TypeOfInstruction`, etc.) are ordinary tagged literal arrays that may
    // be reachable only through those references, so seed them too.
    let mut referenced_literal_offsets: HashSet<u32> = classes
        .values()
        .flat_map(|class| class.methods.iter())
        .flat_map(|method| method.body.iter())
        .flat_map(|body| body.entity_offsets.iter())
        .filter_map(|((kind, _), offset)| {
            (kind == &abcd_isa::EntityKind::LiteralarrayId).then_some(*offset)
        })
        .chain(scope_names_offsets.iter().copied())
        .collect();
    collect_annotation_nested_literal_offsets(
        &classes,
        size,
        &module_data_offsets,
        &phase_blob_offsets,
        &mut referenced_literal_offsets,
    );
    let (literal_arrays, literal_array_offsets, literal_array_header_offsets) =
        decode_literal_arrays(
            f,
            size,
            &mut strings,
            &referenced_literal_offsets,
            &module_data_offsets,
            &phase_blob_offsets,
        )?;
    rewrite_annotation_nested_literal_refs(
        &mut classes,
        &literal_array_offsets,
        literal_arrays.len(),
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
        literal_array_header_offsets,
        entity_map,
    })
}

// ---------------------------------------------------------------------------
// Internal decode helpers
// ---------------------------------------------------------------------------

/// Legacy (0.0.0.2) literal-array global table: `(num_literalarrays,
/// literalarray_idx_off)` read from the file header (`File::Header` field
/// layout is unchanged since 3.1: u32 fields start at offset 16, these two
/// are the 8th and 9th). Returns `None` if the header is truncated.
fn legacy_literalarray_table(data: &[u8]) -> Option<(u32, u32)> {
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

fn decode_method_at(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    debug_raw: *mut sys::AbcDebugInfo,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    legacy: bool,
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
            let (b, bo) = decode_code_at(f, method_off, code_off, legacy)?;
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

    // N55: attach a debug record ONLY when the method structurally has
    // a debug info item (its own index entry, read via the method
    // accessor — independent of the extractor). Previously EVERY method
    // got `Some(..)` whenever the file-level extractor opened, and the
    // extractor's ""-for-missing answers (vendored
    // DebugInfoExtractor::GetSourceFile/GetSourceCode,
    // debug_info_extractor.cpp:318-333) were wrapped in `Some`,
    // inventing `debug: Some(source_file: Some(""))` for methods that
    // have no debug info at all.
    let has_debug_item = unsafe { sys::abc_method_debug_info_off(mr) } != ABSENT;
    let debug = if debug_raw.is_null() || !has_debug_item {
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
        let max_end = pairs
            .iter()
            .try_fold(0usize, |acc, &(i, _)| {
                i.checked_add(1)
                    .and_then(|n| usize::try_from(n).ok())
                    .map(|n| acc.max(n))
            })
            .ok_or_else(|| Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            })?;
        let len = num_params.max(max_end);
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
/// PIN STATUS (V-I1): the only in-cone vendor constant is private
/// (collect_util.h:40) and the public one (abc_file_utils.h) sits outside
/// the CI sparse cone, so no bridge export exists — this stays behaviorally
/// pinned by the module-record tests. The other three names are pinned via
/// `abc_vendor_*` exports (vendor_name_pins.rs).
pub const ES_MODULE_RECORD_DESCRIPTOR: &str = "L_ESModuleRecord;";
/// Descriptor of the record class whose u32 fields reference scope-names
/// literal arrays (upstream `_ESScopeNamesRecord`, same sources).
pub const ES_SCOPE_NAMES_RECORD_DESCRIPTOR: &str = "L_ESScopeNamesRecord;";

/// Name of the u32 field on a `--merge-abc` module record class whose value is
/// the file offset of an untagged `ModuleDataAccessor` blob (upstream
/// `es2panda` `Emitter::AddModuleRecord` `IsMergeAbc` branch; `abc2program`
/// `abc_field_processor.cpp` `MODULE_RECORD_IDX`; `libpandafile`
/// `collect_util.h` `MODULE_RECORD_IDX`).
pub const MODULE_RECORD_IDX_FIELD: &str = "moduleRecordIdx";

/// Name of the u32 field on a `--merge-abc` module record class whose value is
/// the file offset of a tagged scope-names literal array (vendored
/// `libpandabase/utils/const_value.h` `ark::SCOPE_NAMES`; `disassembler.cpp`
/// `GetMetadataFieldValue`; `abc_field_processor.cpp` `SCOPE_NAMES`).
pub const SCOPE_NAMES_FIELD: &str = "scopeNames";

/// Name of the u32 field on a `--merge-abc` JSON module record class whose
/// value is the file offset of the `StringItem` holding the JSON text
/// (`es2panda` `Emitter::GenJsonContentRecord`; `ecmascript/jspandafile`
/// `JSPandaFile::JSON_FILE_CONTENT`; `abc_field_processor.cpp`
/// `JSON_FILE_CONTENT`).
pub const JSON_FILE_CONTENT_FIELD: &str = "jsonFileContent";

/// Name of the u32 field whose value is the file offset of an untagged
/// module-request-phase blob (one u8 lazy-import flag per module request).
/// Matched by NAME, not by class: upstream's merge-abc mode emits the field
/// on the module's own record (es2panda emitter.cpp
/// `Emitter::AddModuleRequestPhaseRecord` IsMergeAbc branch), and the
/// vendored runtime/disassembler key on the name too
/// (js_pandafile.cpp:217 `LAZY_IMPORT`, disassembler.cpp:1007
/// `MODULE_REQUEST_PAHSE_IDX`).
pub const MODULE_REQUEST_PHASE_FIELD: &str = "moduleRequestPhaseIdx";

/// Name of the field whose non-zero value is the file offset of a tagged
/// `LiteralArray` whose elements include nested `LiteralTag::LITERALARRAY`
/// (`0x18`) references to per-type literal arrays (`arkcompiler_runtime_core`
/// 2022-08-18 ISA changelog item 5; `TYPE_SUMMARY_FIELD_NAME` in vendored
/// `libpandabase/utils/const_value.h`). OpenHarmony 4.x–5.x `es2abc` emits
/// the field on AbilityStage/Application and module records.
///
/// A zero wire value (`TYPE_SUMMARY_OFFSET_NOT_FOUND`) decodes as
/// [`FieldValue::I32`]`(0)`; a non-zero offset is validated as a well-formed
/// tagged literal array, seeded into `scope_names_offsets` so both the
/// summary array and its transitively nested type arrays enter
/// [`File::literal_arrays`], and modeled as [`FieldValue::LiteralArrayRef`]
/// for full relocation on `encode`.
pub const TYPE_SUMMARY_OFFSET_FIELD: &str = "typeSummaryOffset";

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

// Each argument is a distinct decode-context facet (the three offset
// sets are independent discovery channels); a bundling struct would
// only rename the plumbing.
#[allow(clippy::too_many_arguments)]
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
        crate::file::intern_string(f, name_off, strings).ok_or_else(|| Error::Malformed {
            field: "name",
            context: format!("field at offset {field_id:#x}"),
        })?
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
        // A valued u32 field named `typeSummaryOffset` (any class — wild es2abc
        // 4.x–5.x hangs it on AbilityStage/Application and module records)
        // carries either `0` (`TYPE_SUMMARY_OFFSET_NOT_FOUND` sentinel) or the
        // offset of a tagged summary literal array whose `0x18` entries point
        // at per-type literal arrays. This arm must come FIRST so the
        // `_ESModuleRecord` catch-all u32 arm below never mis-routes it into
        // the untagged module-data blob decoder.
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(TYPE_SUMMARY_OFFSET_FIELD) =>
        {
            // Bit-cast, not try_from: the wire value is a u32 and the
            // bridge ABI reads it through an i32 out-param, so offsets
            // above 0x7fff_ffff arrive negative — preserve the bits.
            let offset = off as u32;
            if offset == 0 {
                Some(FieldValue::I32(0))
            } else {
                if entity_map.contains_key(&offset)
                    || unsafe {
                        sys::abc_literal_enumerate_vals_checked(
                            f,
                            offset,
                            None,
                            std::ptr::null_mut(),
                        )
                    } != 0
                {
                    return Err(Error::InvalidOffset(offset));
                }
                scope_names_offsets.insert(offset);
                Some(FieldValue::LiteralArrayRef(offset))
            }
        }
        // `moduleRequestPhaseIdx` u32 fields (any class — merge-abc emits
        // them on the module's own record) reference untagged
        // module-request-phase blobs by file offset; decode structurally so
        // encode can re-emit and relocate (same dangling-offset class as
        // _ESModuleRecord/_ESScopeNamesRecord). This name guard must come
        // BEFORE the `_ESModuleRecord` catch-all u32 arm below (N56):
        // merge-abc hangs the phase field on the module record itself, and
        // the catch-all would otherwise mis-route the phase-blob offset
        // into the module-data blob decoder (hard `invalid entity offset`,
        // whole file undecodable).
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
        (desc, TypeId::U32, Some(FieldValue::I32(off)))
            if desc == ES_MODULE_RECORD_DESCRIPTOR
                || strings.resolve(name) == Some(MODULE_RECORD_IDX_FIELD) =>
        {
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
        (desc, TypeId::U32, Some(FieldValue::I32(off)))
            if desc == ES_SCOPE_NAMES_RECORD_DESCRIPTOR
                || strings.resolve(name) == Some(SCOPE_NAMES_FIELD) =>
        {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            scope_names_offsets.insert(offset);
            Some(FieldValue::LiteralArrayRef(offset))
        }
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(JSON_FILE_CONTENT_FIELD) =>
        {
            let offset = off as u32;
            if offset == 0 {
                return Err(Error::InvalidString(0));
            }
            let content = crate::file::intern_string(f, offset, strings)
                .ok_or(Error::InvalidString(offset))?;
            Some(FieldValue::JsonFileContent {
                source_offset: offset,
                content,
            })
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
    legacy: bool,
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
    let decoded = if legacy {
        abcd_isa::decode_legacy(raw_insns)
    } else {
        abcd_isa::decode(raw_insns)
    }
    .map_err(|source| Error::BytecodeDecode {
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
            let end_pc = tb
                .start
                .checked_add(tb.len)
                .ok_or_else(|| Error::Malformed {
                    field: "try_block",
                    context: format!("method at offset {method_off:#x}: try span overflow"),
                })?;
            let start = offset_to_index(tb.start);
            let end = offset_to_index(end_pc);
            let catches = tb
                .catches
                .into_iter()
                .map(|cb| {
                    let handler_end_pc =
                        cb.handler
                            .checked_add(cb.len)
                            .ok_or_else(|| Error::Malformed {
                                field: "catch_block",
                                context: format!(
                                    "method at offset {method_off:#x}: catch span overflow"
                                ),
                            })?;
                    let handler = offset_to_index(cb.handler);
                    let handler_end = offset_to_index(handler_end_pc);
                    Ok(CatchBlock {
                        type_idx: cb.type_idx,
                        handler,
                        len: handler_end.saturating_sub(handler),
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?;
            Ok(TryBlock {
                start,
                len: end.saturating_sub(start),
                catches,
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let num_vregs = unsafe { sys::abc_code_num_vregs(cr) };
    let num_args = unsafe { sys::abc_code_num_args(cr) };

    Ok((
        MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            entity_offsets: HashMap::new(),
            try_blocks,
            // Decoded bodies keep the source file's SlotNumber annotation
            // verbatim on re-encode (byte identity); only lowered bodies
            // carry a recomputed count (model.rs `ic_size` doc, N73).
            ic_size: None,
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
    offsets
        .iter()
        .map(|&off| decode_annotation_at(f, off, entity_map, strings))
        .collect()
}

/// RAII wrapper for an open `AbcAnnotationAccessor` stored in an explicit
/// iterative decode frame.
struct OpenAnnotation(*mut sys::AbcAnnotationAccessor);

impl Drop for OpenAnnotation {
    fn drop(&mut self) {
        if !self.0.is_null() {
            unsafe { sys::abc_annotation_close(self.0) };
        }
    }
}

enum PendingAnnSlot {
    Scalar {
        name: StringId,
    },
    Array {
        name: StringId,
        tag: u8,
        remaining: std::vec::IntoIter<u32>,
        decoded: Vec<AnnotationValue>,
    },
}

struct AnnDecodeFrame {
    off: u32,
    ar: OpenAnnotation,
    class_descriptor: StringId,
    count: u32,
    next_idx: u32,
    elements: Vec<AnnotationElem>,
    pending: Option<PendingAnnSlot>,
}

fn open_ann_frame(
    f: *const sys::AbcFileHandle,
    off: u32,
    entity_map: &HashMap<u32, StringId>,
    visiting: &mut HashSet<u32>,
) -> Result<AnnDecodeFrame, Error> {
    if !visiting.insert(off) {
        return Err(Error::Malformed {
            field: "nested annotation",
            context: format!("cyclic annotation reference at offset {off:#x}"),
        });
    }
    let ar = unsafe { sys::abc_annotation_open(f as *mut _, off) };
    if ar.is_null() {
        visiting.remove(&off);
        return Err(Error::InvalidOffset(off));
    }
    let ar = OpenAnnotation(ar);

    let class_off = unsafe { sys::abc_annotation_class_off(ar.0) };
    let Some(class_descriptor) = entity_map.get(&class_off).copied() else {
        visiting.remove(&off);
        return Err(Error::Malformed {
            field: "class_descriptor",
            context: format!("annotation at offset {off:#x}"),
        });
    };

    let count = unsafe { sys::abc_annotation_count(ar.0) };
    Ok(AnnDecodeFrame {
        off,
        ar,
        class_descriptor,
        count,
        next_idx: 0,
        elements: Vec::with_capacity(count as usize),
        pending: None,
    })
}

/// Decode one annotation tree rooted at `root_off` using an explicit
/// iterative workstack and active-path cycle detection.
fn decode_annotation_at(
    f: *const sys::AbcFileHandle,
    root_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<Annotation, Error> {
    use sys::AnnotationValueType as AVT;

    let mut visiting: HashSet<u32> = HashSet::new();
    let mut stack: Vec<AnnDecodeFrame> =
        vec![open_ann_frame(f, root_off, entity_map, &mut visiting)?];
    let mut completed: Option<Annotation> = None;

    while let Some(frame) = stack.last_mut() {
        if let Some(child_ann) = completed.take() {
            match frame.pending.take() {
                Some(PendingAnnSlot::Scalar { name }) => {
                    frame.elements.push(AnnotationElem {
                        name,
                        value: AnnotationValue::Annotation(Box::new(child_ann)),
                    });
                }
                Some(PendingAnnSlot::Array {
                    name,
                    tag,
                    mut remaining,
                    mut decoded,
                }) => {
                    decoded.push(AnnotationValue::Annotation(Box::new(child_ann)));
                    if let Some(next_off) = remaining.next() {
                        frame.pending = Some(PendingAnnSlot::Array {
                            name,
                            tag,
                            remaining,
                            decoded,
                        });
                        let child = open_ann_frame(f, next_off, entity_map, &mut visiting)?;
                        stack.push(child);
                        continue;
                    }
                    frame.elements.push(AnnotationElem {
                        name,
                        value: AnnotationValue::Array {
                            tag,
                            values: decoded,
                        },
                    });
                }
                None => {}
            }
        }

        let mut next_child: Option<AnnDecodeFrame> = None;
        while frame.next_idx < frame.count {
            let idx = frame.next_idx;
            frame.next_idx += 1;
            let off = frame.off;
            let ar = frame.ar.0;

            let mut out = sys::AbcAnnotationElem {
                name_off: 0,
                tag: 0,
                value: 0,
            };
            // Loud-error convention: every element-read failure below is a
            // hard error (malformed input), never a silent skip/fallback.
            let rc = unsafe { sys::abc_annotation_get_element(ar, idx, &mut out) };
            if rc != 0 {
                return Err(Error::Malformed {
                    field: "annotation element",
                    context: format!("annotation at offset {off:#x}, element {idx}"),
                });
            }
            let name_str =
                read_string(f, out.name_off).ok_or(Error::InvalidString(out.name_off))?;
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
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::U64 => {
                    let mut v = 0u64;
                    if unsafe { sys::abc_annotation_get_value_u64(ar, idx, &mut v) } == 0 {
                        AnnotationValue::U64(v)
                    } else {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::F32 => AnnotationValue::F32(f32::from_bits(out.value)),
                AVT::F64 => {
                    let mut v = 0.0f64;
                    if unsafe { sys::abc_annotation_get_value_f64(ar, idx, &mut v) } == 0 {
                        AnnotationValue::F64(v)
                    } else {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::String => {
                    let s = read_string(f, out.value).ok_or(Error::InvalidString(out.value))?;
                    let sid = strings.get_or_intern(&s);
                    AnnotationValue::String(sid)
                }
                AVT::Record => {
                    let sid = entity_map
                        .get(&out.value)
                        .copied()
                        .ok_or(Error::InvalidOffset(out.value))?;
                    AnnotationValue::Record(sid)
                }
                AVT::Method => {
                    let sid = resolve_foreign_entity_name(f, entity_map, strings, out.value);
                    AnnotationValue::Method {
                        name: sid,
                        offset: out.value,
                    }
                }
                AVT::Enum => {
                    let sid = resolve_foreign_entity_name(f, entity_map, strings, out.value);
                    AnnotationValue::Enum {
                        name: sid,
                        offset: out.value,
                    }
                }
                AVT::Annotation => {
                    frame.pending = Some(PendingAnnSlot::Scalar { name });
                    next_child = Some(open_ann_frame(f, out.value, entity_map, &mut visiting)?);
                    break;
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
                    if rc != 0 {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let ht = MethodHandleType::from_u8(handle_type_raw).ok_or_else(|| {
                        Error::Malformed {
                            field: "method_handle_type",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx}: unknown handle type {handle_type_raw:#x}"
                            ),
                        }
                    })?;
                    let entity = entity_map
                        .get(&entity_off)
                        .copied()
                        .unwrap_or_else(|| strings.get_or_intern(""));
                    AnnotationValue::MethodHandle(ResolvedMethodHandle {
                        handle_type: ht,
                        entity,
                        entity_offset: entity_off,
                    })
                }
                AVT::LiteralArray => {
                    // '#' is the SCALAR literal-array tag in the vendored data
                    // model (GetScalarValue, disassembler.cpp:569-574).
                    let values = decode_literal_array_at(f, out.value, strings)?;
                    AnnotationValue::LiteralArray(values)
                }
                AVT::Void => AnnotationValue::Void,
                AVT::StringNullptr => AnnotationValue::StringNullptr,
                AVT::ArrayAnnotation => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let (_, raw_values) =
                        read_annotation_array_raw(f, out.tag, arr.count, arr.entity_off)?;
                    let mut offsets_iter = raw_values
                        .into_iter()
                        .map(|v| v as u32)
                        .collect::<Vec<_>>()
                        .into_iter();
                    if let Some(first_off) = offsets_iter.next() {
                        frame.pending = Some(PendingAnnSlot::Array {
                            name,
                            tag: out.tag,
                            decoded: Vec::with_capacity(offsets_iter.len().saturating_add(1)),
                            remaining: offsets_iter,
                        });
                        next_child = Some(open_ann_frame(f, first_off, entity_map, &mut visiting)?);
                        break;
                    }
                    AnnotationValue::Array {
                        tag: out.tag,
                        values: Vec::new(),
                    }
                }
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
                | AVT::ArrayMethodHandle => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let values = decode_annotation_array_elements(
                        f,
                        out.tag,
                        arr.count,
                        arr.entity_off,
                        entity_map,
                        strings,
                    )?;
                    AnnotationValue::Array {
                        tag: out.tag,
                        values,
                    }
                }
                AVT::Unknown => AnnotationValue::U32(out.value),
            };
            frame.elements.push(AnnotationElem { name, value });
        }

        if let Some(child) = next_child {
            stack.push(child);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        visiting.remove(&finished.off);
        let ann = Annotation {
            class_descriptor: finished.class_descriptor,
            elements: finished.elements,
        };
        if stack.is_empty() {
            return Ok(ann);
        }
        completed = Some(ann);
    }

    Err(Error::Malformed {
        field: "nested annotation",
        context: format!("annotation at offset {root_off:#x}"),
    })
}

/// Read the raw element words of an annotation array at `entity_offset`,
/// validating the tag's element width and payload span.
fn read_annotation_array_raw(
    f: *const sys::AbcFileHandle,
    tag: u8,
    count: u32,
    entity_offset: u32,
) -> Result<(sys::AnnotationValueType, Vec<u64>), Error> {
    use sys::AnnotationValueType as AVT;

    let avt = AVT::try_from(tag);
    let (avt, element_size): (AVT, u32) = match avt {
        Ok(t @ (AVT::ArrayU1 | AVT::ArrayI8 | AVT::ArrayU8)) => (t, 1),
        Ok(t @ (AVT::ArrayI16 | AVT::ArrayU16)) => (t, 2),
        Ok(
            t @ (AVT::ArrayI32
            | AVT::ArrayU32
            | AVT::ArrayF32
            | AVT::ArrayString
            | AVT::ArrayRecord
            | AVT::ArrayMethod
            | AVT::ArrayEnum
            | AVT::ArrayAnnotation
            | AVT::ArrayMethodHandle
            | AVT::LiteralArray),
        ) => (t, 4),
        Ok(t @ (AVT::ArrayI64 | AVT::ArrayU64 | AVT::ArrayF64)) => (t, 8),
        _ => {
            return Err(Error::Malformed {
                field: "annotation array element tag",
                context: format!(
                    "annotation array at offset {entity_offset:#x}: tag {tag:#x} has no defined element size"
                ),
            });
        }
    };

    if count == 0 {
        return Ok((avt, Vec::new()));
    }

    let file_size = unsafe { sys::abc_file_size(f) };
    let max_by_span = file_size.saturating_sub(entity_offset) / element_size;
    let alloc_count = count.min(max_by_span);
    let alloc_len = usize::try_from(alloc_count).map_err(|_| Error::Malformed {
        field: "annotation array data",
        context: format!("annotation array at offset {entity_offset:#x}"),
    })?;
    let mut raw_values = Vec::new();
    raw_values
        .try_reserve_exact(alloc_len)
        .map_err(|_| Error::Malformed {
            field: "annotation array data",
            context: format!("annotation array at offset {entity_offset:#x}"),
        })?;
    raw_values.resize(alloc_len, 0u64);
    let n = unsafe {
        sys::abc_annotation_array_read(
            f,
            entity_offset,
            element_size,
            count,
            raw_values.as_mut_ptr(),
            alloc_count,
        )
    };
    if n < 0 {
        return Err(Error::Malformed {
            field: "annotation array data",
            context: format!("annotation array at offset {entity_offset:#x}"),
        });
    }
    let n_u32 = n as u32;
    if n_u32 < count {
        return Err(Error::Malformed {
            field: "annotation array data",
            context: format!(
                "annotation array at offset {entity_offset:#x}: declared {count} elements, {n_u32} readable"
            ),
        });
    }
    raw_values.truncate(n_u32 as usize);
    Ok((avt, raw_values))
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
) -> Result<Vec<AnnotationValue>, Error> {
    use sys::AnnotationValueType as AVT;

    let (avt, raw_values) = read_annotation_array_raw(f, tag, count, entity_offset)?;

    raw_values
        .into_iter()
        .map(|raw| -> Result<AnnotationValue, Error> {
            let value = match avt {
                AVT::ArrayU1 => AnnotationValue::Bool(raw != 0),
                AVT::ArrayI8 => AnnotationValue::I8(raw as i8),
                AVT::ArrayU8 => AnnotationValue::U8(raw as u8),
                AVT::ArrayI16 => AnnotationValue::I16(raw as i16),
                AVT::ArrayU16 => AnnotationValue::U16(raw as u16),
                AVT::ArrayI32 => AnnotationValue::I32(raw as i32),
                AVT::ArrayU32 => AnnotationValue::U32(raw as u32),
                AVT::ArrayI64 => AnnotationValue::I64(raw as i64),
                AVT::ArrayU64 => AnnotationValue::U64(raw),
                AVT::ArrayF32 => AnnotationValue::F32(f32::from_bits(raw as u32)),
                AVT::ArrayF64 => AnnotationValue::F64(f64::from_bits(raw)),
                AVT::ArrayString => {
                    let s = read_string(f, raw as u32).ok_or(Error::InvalidString(raw as u32))?;
                    AnnotationValue::String(strings.get_or_intern(&s))
                }
                AVT::ArrayRecord => {
                    let sid = entity_map
                        .get(&(raw as u32))
                        .copied()
                        .ok_or(Error::InvalidOffset(raw as u32))?;
                    AnnotationValue::Record(sid)
                }
                AVT::ArrayMethod => {
                    let sid = resolve_foreign_entity_name(f, entity_map, strings, raw as u32);
                    AnnotationValue::Method {
                        name: sid,
                        offset: raw as u32,
                    }
                }
                AVT::ArrayEnum => {
                    let sid = resolve_foreign_entity_name(f, entity_map, strings, raw as u32);
                    AnnotationValue::Enum {
                        name: sid,
                        offset: raw as u32,
                    }
                }
                AVT::ArrayAnnotation => {
                    let nested = decode_annotation_at(f, raw as u32, entity_map, strings)?;
                    AnnotationValue::Annotation(Box::new(nested))
                }
                AVT::LiteralArray => {
                    AnnotationValue::LiteralArray(decode_literal_array_at(f, raw as u32, strings)?)
                }
                AVT::ArrayMethodHandle => {
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
                    if rc != 0 {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation array at offset {entity_offset:#x}"),
                        });
                    }
                    let ht = MethodHandleType::from_u8(handle_type_raw).ok_or_else(|| {
                        Error::Malformed {
                            field: "method_handle_type",
                            context: format!(
                                "annotation array at offset {entity_offset:#x}: unknown handle type {handle_type_raw:#x}"
                            ),
                        }
                    })?;
                    let entity = entity_map
                        .get(&entity_off)
                        .copied()
                        .unwrap_or_else(|| strings.get_or_intern(""));
                    AnnotationValue::MethodHandle(ResolvedMethodHandle {
                        handle_type: ht,
                        entity,
                        entity_offset: entity_off,
                    })
                }
                _ => {
                    return Err(Error::Malformed {
                        field: "annotation array element tag",
                        context: format!(
                            "annotation array at offset {entity_offset:#x}: tag {tag:#x} has no value conversion"
                        ),
                    });
                }
            };
            Ok(value)
        })
        .collect()
}

/// Decode a single literal array at the given entity offset, strictly
/// validating that `offset` points at a well-formed tagged literal array.
fn decode_literal_array_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut StringPool,
) -> Result<Vec<crate::LiteralValue>, Error> {
    // N72: annotation-embedded literal arrays are compile-time metadata;
    // their strings intern plain (no raw-bytes capture — NULL side
    // table), exactly the pre-N72 behavior on this path.
    let mut ctx = crate::literal::LiteralCollectCtx {
        file: f,
        strings: strings as *mut StringPool,
        values: Vec::new(),
    };
    let rc = unsafe {
        sys::abc_literal_enumerate_vals_checked(
            f,
            offset,
            Some(crate::literal::collect_literal_val_cb),
            &mut ctx as *mut crate::literal::LiteralCollectCtx as *mut c_void,
        )
    };
    if rc != 0 {
        return Err(Error::InvalidOffset(offset));
    }
    Ok(ctx.values)
}

/// Minimum byte offset past the 60-byte `panda_file::File::Header` where a
/// 4-byte `num_lit` count header of a tagged literal array can reside,
/// excluding untagged module-record and module-request-phase blobs.
fn is_plausible_literal_array_offset(
    off: u32,
    file_size: u32,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
) -> bool {
    const HEADER_SIZE: u32 = 60;
    off != ABSENT
        && off >= HEADER_SIZE
        && u64::from(off) + 4 <= u64::from(file_size)
        && !module_data_offsets.contains(&off)
        && !phase_blob_offsets.contains(&off)
}

/// Seed `out` with plausible nested `LiteralValue::LiteralArray` offsets found
/// inside any `AnnotationValue::LiteralArray` across the file, using an
/// explicit iterative workstack.
fn collect_annotation_nested_literal_offsets(
    classes: &BTreeMap<StringId, Class>,
    file_size: u32,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
    out: &mut HashSet<u32>,
) {
    fn push_annotations<'a>(anns: &'a Annotations, stack: &mut Vec<&'a AnnotationValue>) {
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

    let mut stack: Vec<&AnnotationValue> = Vec::new();
    for class in classes.values() {
        push_annotations(&class.annotations, &mut stack);
        for method in &class.methods {
            push_annotations(&method.annotations, &mut stack);
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
            push_annotations(&field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    if let LiteralValue::LiteralArray(idx) = item
                        && is_plausible_literal_array_offset(
                            idx.0,
                            file_size,
                            module_data_offsets,
                            phase_blob_offsets,
                        )
                    {
                        out.insert(idx.0);
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

/// Rewrite nested `LiteralValue::LiteralArray` offsets inside every
/// `AnnotationValue::LiteralArray` to `File::literal_arrays` table indices
/// using an explicit iterative workstack. Unresolvable raw offsets that would
/// otherwise alias `< literal_array_count` are replaced with `ABSENT` so
/// relocation fails loudly on `encode`.
fn rewrite_annotation_nested_literal_refs(
    classes: &mut BTreeMap<StringId, Class>,
    offset_to_index: &HashMap<u32, u32>,
    literal_array_count: usize,
) {
    fn push_annotations<'a>(anns: &'a mut Annotations, stack: &mut Vec<&'a mut AnnotationValue>) {
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

    let mut stack: Vec<&mut AnnotationValue> = Vec::new();
    for class in classes.values_mut() {
        push_annotations(&mut class.annotations, &mut stack);
        for method in &mut class.methods {
            push_annotations(&mut method.annotations, &mut stack);
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
            push_annotations(&mut field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    if let LiteralValue::LiteralArray(idx) = item {
                        if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                            idx.0 = table_idx;
                        } else if (idx.0 as usize) < literal_array_count {
                            idx.0 = ABSENT;
                        }
                    }
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

/// The literal-array table decode result: the decoded arrays, the
/// file-offset → table-index map, and the raw header offsets (kept for
/// the pandasm emitter's byte-identity with upstream ark_disasm).
type LiteralArrayTable = (Vec<LiteralArray>, HashMap<u32, u32>, Vec<u32>);

fn decode_literal_arrays(
    f: *const sys::AbcFileHandle,
    file_size: u32,
    strings: &mut StringPool,
    referenced_offsets: &HashSet<u32>,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
) -> Result<LiteralArrayTable, Error> {
    let n = unsafe { sys::abc_file_num_literalarrays(f) };
    // The raw header table, unfiltered: the pandasm emitter's byte-identity
    // with upstream ark_disasm needs the original header positions of the
    // module/phase blobs that the decoded table excludes.
    let mut header_offsets = Vec::new();
    let mut offsets = Vec::new();
    if n != 0 {
        for i in 0..n {
            let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
            if off != ABSENT {
                header_offsets.push(off);
            }
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
        return Ok((Vec::new(), HashMap::new(), header_offsets));
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
        // Loud-error convention: `offsets` is non-empty (guarded above), so
        // returning Ok here would hand the caller a POPULATED offset map over
        // an EMPTY array table — every mapped LiteralarrayId would index a
        // nonexistent table entry (silent structural inconsistency). A header
        // table entry that does not parse as a literal array is malformed
        // input: hard error, like every other accessor-open failure in this
        // file.
        return Err(Error::InvalidOffset(first_off));
    }
    let _lg = HandleGuard(Some(|| unsafe { sys::abc_literal_close(lr) }));

    // Nested-reference recovery (v2-P1a): a LITERALARRAY payload holds the
    // target array's FILE OFFSET, and class buffers (sendable classes on
    // 13.x/24.x) as well as type annotations (`L_ESTypeAnnotation;`)
    // reference arrays registered nowhere — not in the header table and not
    // in any method index region. Recover them transitively: `offsets`
    // doubles as the worklist, and an offset is registered in
    // `offset_to_index` BEFORE its array is decoded, so reference cycles
    // terminate and every offset is decoded at most once per table entry.
    // Newly discovered offsets are appended in sorted batches, keeping the
    // table order deterministic (N20).
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
                    if is_plausible_literal_array_offset(
                        target,
                        file_size,
                        module_data_offsets,
                        phase_blob_offsets,
                    ) && !offset_to_index.contains_key(&target)
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
    let array_count = arrays.len();
    for arr in &mut arrays {
        for v in &mut arr.values {
            if let LiteralValue::LiteralArray(idx) = v {
                if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                    idx.0 = table_idx;
                } else if (idx.0 as usize) < array_count {
                    idx.0 = ABSENT;
                }
            }
        }
    }
    Ok((arrays, offset_to_index, header_offsets))
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

    // N55: the vendored extractor answers "" for MISSING entries
    // (DebugInfoExtractor::GetSourceFile/GetSourceCode,
    // debug_info_extractor.cpp:318-333) — "" is the vendor's
    // "no value", not a value. Map it to `None` instead of wrapping it
    // in `Some` (the old behavior invented `source_file: Some("")`
    // for methods with no recorded file; encode already treats empty
    // debug strings as no content, 980ec16). Null (bridge catch) maps
    // to `None` too.
    let source_file = {
        let ptr = unsafe { sys::abc_debug_get_source_file(debug_raw, method_off) };
        if ptr.is_null() {
            None
        } else {
            let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy();
            if s.is_empty() {
                None
            } else {
                Some(strings.get_or_intern(s.as_ref()))
            }
        }
    };
    let source_code = {
        let ptr = unsafe { sys::abc_debug_get_source_code(debug_raw, method_off) };
        if ptr.is_null() {
            None
        } else {
            let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy();
            if s.is_empty() {
                None
            } else {
                Some(strings.get_or_intern(s.as_ref()))
            }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Arm: annotation-array payload read failure (bridge
    /// `abc_annotation_array_read` returning < 0). This is unreachable
    /// through the public `decode` path: the caller's
    /// `abc_annotation_get_array_element` has already read the same span and
    /// ULEB count successfully, so the re-read here cannot fail for
    /// deterministic bytes. The arm is still loud (never a silent empty
    /// array); exercise it by calling the decoder directly with a dangling
    /// array offset.
    #[test]
    fn annotation_array_data_read_failure_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");
        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        // Tag 'Q' = ArrayU32 (element size 4); the offset dangles past EOF.
        let result = decode_annotation_array_elements(
            abc.raw,
            b'Q',
            1,
            0xFFFF_FF00,
            &entity_map,
            &mut strings,
        );
        assert!(
            matches!(
                result,
                Err(Error::Malformed {
                    field: "annotation array data",
                    ..
                })
            ),
            "expected Malformed/annotation array data, got: {result:?}"
        );
    }

    /// Arm: a literal array as an annotation ARRAY element ('#' inside the
    /// array-element converter). Upstream cannot represent arrays of
    /// literal arrays (pandasm `GetArrayTypeAsChar` has no '#' case), so no
    /// producer emits this and the public `decode` path never routes '#'
    /// here (the element dispatch treats '#' as the SCALAR literal-array
    /// tag). Drive the converter directly over a crafted payload.
    #[test]
    fn literal_array_as_array_element_decodes() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        // An array element whose payload is `[uleb 1][u32 string_off]` —
        // the exact layout the '#' arm reads.
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let la = b.add_literal_array("la");
        b.literal_array_add_integer(la, 7);
        let mut data = b.finalize().expect("finalize");

        // The literal array's source offset, learned through a decode.
        let file = decode(&data).expect("decode");
        let la_off = file
            .literal_array_offsets
            .iter()
            .find_map(|(&off, &idx)| (idx == 0).then_some(off))
            .expect("literal array offset");

        // Find the annotation array payload: the string item offset of
        // "probe_s" preceded by the uleb count byte 0x01.
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        // Rewrite the element to hold the literal array's offset.
        data[payload_pos as usize + 1..payload_pos as usize + 5]
            .copy_from_slice(&la_off.to_le_bytes());

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        let result = decode_annotation_array_elements(
            abc.raw,
            b'#',
            1,
            payload_pos,
            &entity_map,
            &mut strings,
        )
        .expect("literal-array element must decode");
        assert_eq!(result.len(), 1);
        match &result[0] {
            AnnotationValue::LiteralArray(values) => {
                assert_eq!(values, &vec![crate::LiteralValue::Integer(7)]);
            }
            other => panic!("expected LiteralArray element, got {other:?}"),
        }
    }

    /// Arm: the '#' array-element converter propagates a dangling nested
    /// literal array loudly (the `?` inside the `Ok(AVT::LiteralArray)`
    /// arm). Same unreachable-through-decode reasoning as its sibling test
    /// above ('#' is the SCALAR literal-array tag in the element dispatch):
    /// drive the converter directly with a payload whose element dangles.
    #[test]
    fn literal_array_array_element_dangling_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let mut data = b.finalize().expect("finalize");

        // Find the array payload (`[uleb 1][u32 string_off]`) and rewrite
        // the element to dangle past the declared file size.
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;
        let bogus = 0xFFFF_FF00u32;
        data[payload_pos as usize + 1..payload_pos as usize + 5]
            .copy_from_slice(&bogus.to_le_bytes());

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        let result = decode_annotation_array_elements(
            abc.raw,
            b'#',
            1,
            payload_pos,
            &entity_map,
            &mut strings,
        );
        assert!(
            matches!(result, Err(Error::InvalidOffset(o)) if o == bogus),
            "expected InvalidOffset({bogus:#x}), got: {result:?}"
        );
    }

    /// Arm: a declared element count that overruns the array's data span is
    /// a hard error, never a silent truncation (the bridge clamps the read
    /// to what the span holds and yields the short count). Reaching this
    /// through the public `decode` path would require the array payload to
    /// sit at the declared file end with every later-decoded item below it
    /// — the builder's item order never produces that — so drive the
    /// converter directly with an inflated count over a valid payload.
    #[test]
    fn annotation_array_short_read_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");

        // Find the array payload (`[uleb 1][u32 string_off]`).
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        // Tag 'Q' = ArrayU32 (4-byte elements). The declared count vastly
        // overruns the span between the payload and the declared file end,
        // so the bridge yields fewer elements than declared.
        let result = decode_annotation_array_elements(
            abc.raw,
            b'Q',
            0xFFFF,
            payload_pos,
            &entity_map,
            &mut strings,
        );
        assert!(
            matches!(
                result,
                Err(Error::Malformed {
                    field: "annotation array data",
                    ..
                })
            ),
            "expected Malformed/annotation array data, got: {result:?}"
        );
    }

    #[test]
    fn legacy_literalarray_table_rejects_32bit_overflows() {
        let mut buf = vec![0u8; 128];
        let set_header = |buf: &mut [u8], count: u32, table_off: u32| {
            buf[44..48].copy_from_slice(&count.to_le_bytes());
            buf[48..52].copy_from_slice(&table_off.to_le_bytes());
        };

        // Valid table inside the buffer succeeds.
        set_header(&mut buf, 2, 60);
        assert_eq!(legacy_literalarray_table(&buf), Some((2, 60)));

        // Every 32-bit `u32`/`usize` overflow or out-of-bounds combination
        // returns `None` without panicking.
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

    #[test]
    fn annotation_array_32bit_overflowing_counts_are_hard_errors() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V',
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");

        let mut pat = vec![(7u8 << 1) | 1];
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        for bad_count in [0x4000_0001u32, u32::MAX] {
            let result = decode_annotation_array_elements(
                abc.raw,
                b'Q',
                bad_count,
                payload_pos,
                &entity_map,
                &mut strings,
            );
            assert!(
                matches!(
                    result,
                    Err(Error::Malformed {
                        field: "annotation array data",
                        ..
                    })
                ),
                "expected Malformed for count {bad_count:#x}, got: {result:?}"
            );
        }
    }
}
