//! Eagerly-decoded, fully-owned representation of an ABC file.
//!
//! Call [`decode`] to parse raw bytes into a [`File`] struct.

use std::collections::{BTreeMap, HashMap};
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

        let name_str = read_class_name(cr).ok_or_else(|| Error::Malformed {
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
            .map(|off| decode_field_at(f, off, &entity_map, &mut strings))
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

    // --- literal arrays ---
    let literal_arrays = decode_literal_arrays(f, &mut strings);

    Ok(File {
        version,
        checksum,
        size,
        file_type,
        strings,
        classes,
        literal_arrays,
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
            let (b, bo) = decode_code_at(f, method_off, code_off);
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
        debug,
    })
}

fn decode_field_at(
    f: *const sys::AbcFileHandle,
    field_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
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
/// name directly from a foreign field/method item (both store name_off as
/// the u32 at item+4) when the offset is in the file's foreign region and
/// the entity_map has no entry — foreign members are not class members and
/// never enter the entity_map (test group A).
fn resolve_foreign_entity_name(
    f: *const sys::AbcFileHandle,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    off: u32,
) -> StringId {
    if let Some(&sid) = entity_map.get(&off) {
        return sid;
    }
    let foreign_off = unsafe { sys::abc_file_foreign_off(f) };
    let foreign_size = unsafe { sys::abc_file_foreign_size(f) };
    if foreign_size == 0 || off < foreign_off || off >= foreign_off.saturating_add(foreign_size) {
        return strings.get_or_intern("");
    }
    let name_off = read_u32_at(f, off + 4).unwrap_or(ABSENT);
    if name_off == ABSENT {
        return strings.get_or_intern("");
    }
    match read_string(f, name_off) {
        Some(name) => strings.get_or_intern(&name),
        None => strings.get_or_intern(""),
    }
}

/// Read a little-endian u32 at an arbitrary file offset with bounds checks.
fn read_u32_at(f: *const sys::AbcFileHandle, off: u32) -> Option<u32> {
    let base = unsafe { sys::abc_file_get_raw_data(f) };
    if base.is_null() {
        return None;
    }
    let size = unsafe { sys::abc_file_size(f) };
    if off.checked_add(4)? > size {
        return None;
    }
    // SAFETY: base..base+size is the padded file buffer; off..off+4 in bounds.
    let bytes = unsafe { std::slice::from_raw_parts(base.add(off as usize), 4) };
    Some(u32::from_le_bytes(bytes.try_into().unwrap()))
}

/// Returns `(MethodBody, byte_offsets)` where `byte_offsets[i]` is the byte
/// offset of instruction `i` in the raw bytecode.  The table is needed by
/// `read_debug_info` to convert debug byte-offsets to instruction indices.
fn decode_code_at(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    code_off: u32,
) -> (MethodBody, Vec<u32>) {
    let cr = unsafe { sys::abc_code_open(f as *mut _, code_off) };
    if cr.is_null() {
        return (
            MethodBody {
                num_vregs: 0,
                num_args: 0,
                bytecodes: Vec::new(),
                try_blocks: Vec::new(),
            },
            Vec::new(),
        );
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
    let decoded = abcd_isa::decode(raw_insns).unwrap_or_default();

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

    (
        MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            try_blocks,
        },
        byte_offsets,
    )
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
                            // '#' is both a scalar and an array component
                            // tag: try the array interpretation first, fall
                            // back to a scalar literal-array reference.
                            let mut arr = sys::AbcAnnotationArrayVal {
                                count: 0,
                                entity_off: 0,
                            };
                            if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) }
                                == 0
                            {
                                AnnotationValue::Array {
                                    tag: b'#',
                                    values: decode_annotation_array_elements(
                                        f,
                                        b'#',
                                        arr.count,
                                        arr.entity_off,
                                        entity_map,
                                        strings,
                                    ),
                                }
                            } else {
                                let values = decode_literal_array_at(f, out.value, strings);
                                AnnotationValue::LiteralArray(values)
                            }
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
) -> Vec<LiteralArray> {
    let n = unsafe { sys::abc_file_num_literalarrays(f) };
    if n == 0 {
        return Vec::new();
    }

    // Collect file offsets first so nested LiteralArray references (which
    // store the referenced array's file offset) can be rewritten to table
    // indices — the model's documented semantic.
    let mut offset_to_index: HashMap<u32, u32> = HashMap::new();
    for i in 0..n {
        let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
        if off != ABSENT {
            offset_to_index.insert(off, i);
        }
    }

    let first_off = unsafe { sys::abc_file_literalarray_offset(f, 0) };
    if first_off == ABSENT {
        return Vec::new();
    }
    let lr = unsafe { sys::abc_literal_open(f, first_off) };
    if lr.is_null() {
        return Vec::new();
    }
    let _lg = HandleGuard(Some(|| unsafe { sys::abc_literal_close(lr) }));

    let mut arrays: Vec<LiteralArray> = (0..n)
        .filter_map(|i| {
            let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
            if off == ABSENT {
                return None;
            }

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
            Some(LiteralArray { values: ctx.values })
        })
        .collect();

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
    arrays
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

fn read_class_name(cr: *const sys::AbcClassAccessor) -> Option<String> {
    let len = unsafe { sys::abc_class_get_name(cr, std::ptr::null_mut(), 0) };
    if len == 0 {
        return None;
    }
    let mut buf = vec![0u8; len + 1];
    unsafe {
        sys::abc_class_get_name(cr, buf.as_mut_ptr() as *mut _, buf.len());
    }
    let cstr = CStr::from_bytes_until_nul(&buf).ok()?;
    Some(cstr.to_string_lossy().into_owned())
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
