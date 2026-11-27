//! Semantic [`File`] → `.abc` byte re-encoder and [`Builder`] module root.

#![deny(unsafe_code)]

#[allow(unsafe_code, reason = "Builder wraps the C99 abcd-file-sys writer FFI")]
mod builder;

pub use builder::{
    AnnotationElemDef, AnnotationElemDefEx, AnnotationElemValue, AnnotationHandle, Builder,
    CatchBlockDef, ClassHandle, CodeEntity, CodeHandle, DebugInfoHandle, FieldHandle,
    LiteralArrayHandle, LnpHandle, MethodHandle, MethodHandleItemHandle, ModuleRecordDef,
    ParamHandle, ProtoHandle, StringHandle,
};

use std::collections::HashMap;
use std::ffi::CString;

use abcd_file_sys as sys;

use crate::annotation::AnnotationValue;
use crate::error::Error;
use crate::literal::LiteralTag;
use crate::model::*;
use crate::types::{FunctionKind, Type};
use crate::{StringId, StringPool};

/// Configuration options for [`encode_with_options`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EncodeOptions {
    /// When `true`, run [`crate::inspect_summary`] (`verify = true`) over the
    /// finalized `.abc` bytes before returning them, mapping any failure to
    /// [`Error::FinalizeValidation`]. Defaults to `false`.
    pub verify: bool,
}

/// Handles of encoded methods/fields, resolvable by dense [`MethodIdx`] /
/// [`FieldIdx`] first, then non-zero source-file offset, and finally by name
/// when both index and offset are absent (`None` and `offset == 0` on
/// hand-built models).
#[derive(Default)]
struct EntityHandles {
    methods_by_idx: Vec<MethodHandle>,
    methods_by_offset: HashMap<u32, MethodHandle>,
    methods_by_name: HashMap<StringId, MethodHandle>,
    fields_by_idx: Vec<FieldHandle>,
    fields_by_offset: HashMap<u32, FieldHandle>,
    fields_by_name: HashMap<StringId, FieldHandle>,
}

impl EntityHandles {
    fn insert_method(&mut self, m: &Method, h: MethodHandle) {
        self.methods_by_idx.push(h);
        self.methods_by_name.insert(m.name, h);
        if m.offset != 0 {
            self.methods_by_offset.insert(m.offset, h);
        }
    }

    fn insert_field(&mut self, f: &Field, h: FieldHandle) {
        self.fields_by_idx.push(h);
        self.fields_by_name.insert(f.name, h);
        if f.offset != 0 {
            self.fields_by_offset.insert(f.offset, h);
        }
    }

    /// Resolve a method reference: dense [`MethodIdx`] takes precedence; if
    /// `None`, a non-zero `offset` resolves via `methods_by_offset`, and the
    /// name map is consulted ONLY when `method.is_none() && offset == 0`.
    fn resolve_method(
        &self,
        name: StringId,
        method: Option<MethodIdx>,
        offset: u32,
    ) -> Option<MethodHandle> {
        if let Some(idx) = method {
            return self.methods_by_idx.get(idx.index()).copied();
        }
        if offset != 0 {
            return self.methods_by_offset.get(&offset).copied();
        }
        self.methods_by_name.get(&name).copied()
    }

    /// Resolve a field reference (see [`Self::resolve_method`]).
    fn resolve_field(
        &self,
        name: StringId,
        field: Option<FieldIdx>,
        offset: u32,
    ) -> Option<FieldHandle> {
        if let Some(idx) = field {
            return self.fields_by_idx.get(idx.index()).copied();
        }
        if offset != 0 {
            return self.fields_by_offset.get(&offset).copied();
        }
        self.fields_by_name.get(&name).copied()
    }
}

/// Encode a decoded [`File`] back to ABC bytes using [`EncodeOptions::default`].
///
/// Source entity operands are resolved through each method body's index map
/// and relocated after the upstream writer assigns new indices. Pass
/// [`EncodeOptions { verify: true }`](EncodeOptions) to [`encode_with_options`]
/// when post-finalize readback verification is desired.
///
/// Note: `ParamInfo::signature` is derived from method prototypes on decode and
/// is not stored separately in `DebugInfoItem`.
pub fn encode(file: &File) -> Result<Vec<u8>, Error> {
    encode_with_options(file, EncodeOptions::default())
}

/// Encode a decoded [`File`] back to ABC bytes with explicit [`EncodeOptions`].
pub fn encode_with_options(file: &File, options: EncodeOptions) -> Result<Vec<u8>, Error> {
    if file.file_type != crate::FileType::Dynamic {
        return Err(Error::Malformed {
            field: "file_type",
            context: format!(
                "cannot encode {:?} file as dynamic ArkTS/JS bytecode",
                file.file_type
            ),
        });
    }
    validate_annotation_arrays(file)?;
    validate_literal_array_graph(&file.literal_arrays)?;
    let mut b = Builder::new();
    b.set_file_version(file.version)?;
    let pool = &file.strings;

    let rcstr = |id: StringId| -> Result<CString, Error> {
        let bytes = pool.to_mutf8_bytes(id).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {id:?} in file"),
        })?;
        Builder::mutf8_cstr(&bytes)
    };

    // Dense `StringId::index() -> Option<StringHandle>` table (zero hashing).
    let mut string_handles: Vec<Option<StringHandle>> = vec![None; pool.len()];

    // --- Create classes (foreign first, then normal) ---
    let mut class_handles: HashMap<StringId, ClassHandle> = HashMap::new();
    let mut entities = EntityHandles::default();
    let mut code_references = Vec::new();
    let mut deferred_field_values: Vec<(FieldHandle, &FieldValue)> = Vec::new();
    let mut deferred_ann_las: Vec<(LiteralArrayHandle, Vec<LiteralValue>)> = Vec::new();
    let mut ann_la_counter: u32 = 0;

    // First pass: foreign classes
    for (&desc, cls) in &file.classes {
        if cls.is_external {
            let h = b.add_foreign_class_cstr(&rcstr(desc)?);
            class_handles.insert(desc, h);
        }
    }
    // Second pass: normal classes
    for (&desc, cls) in &file.classes {
        if !cls.is_external {
            let h = if pool.as_str(desc) == Some("L_GLOBAL;") {
                b.add_global_class()
            } else {
                b.add_class_cstr(&rcstr(desc)?)
            };
            class_handles.insert(desc, h);
        }
    }

    let resolve_class_id = |b: &mut Builder,
                            map: &mut HashMap<StringId, ClassHandle>,
                            pool: &StringPool,
                            desc: StringId|
     -> Result<ClassHandle, Error> {
        if let Some(&h) = map.get(&desc) {
            return Ok(h);
        }
        let bytes = pool.to_mutf8_bytes(desc).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {desc:?} for class descriptor"),
        })?;
        let h = b.add_foreign_class_cstr(&Builder::mutf8_cstr(&bytes)?);
        map.insert(desc, h);
        Ok(h)
    };

    // --- Configure each class ---
    for (&desc, cls) in &file.classes {
        let cls_h = class_handles
            .get(&desc)
            .copied()
            .ok_or_else(|| Error::Malformed {
                field: "class_descriptor",
                context: format!("missing class handle for {desc:?}"),
            })?;

        b.class_set_access_flags(cls_h, cls.access_flags);
        b.class_set_source_lang(cls_h, cls.source_lang);

        let class_has_source_file = cls
            .source_file
            .is_some_and(|sf| !pool.resolve(sf).unwrap_or("").is_empty());
        if let Some(sf) = cls.source_file {
            let sh = get_or_add_string_id(&mut b, &mut string_handles, pool, sf)?;
            b.class_set_source_file(cls_h, sh);
        }
        if let Some(sup) = cls.super_class {
            let sup_h = resolve_class_id(&mut b, &mut class_handles, pool, sup)?;
            b.class_set_super_class(cls_h, sup_h);
        }
        for &iface in &cls.interfaces {
            let iface_h = resolve_class_id(&mut b, &mut class_handles, pool, iface)?;
            b.class_add_interface(cls_h, iface_h);
        }

        // --- Methods ---
        for method in &cls.methods {
            let method_name_cstr = rcstr(method.name)?;
            let ret_type = method.return_type.unwrap_or(Type::Void);
            let ret_class = if let Type::Reference(d) = ret_type {
                Some(resolve_class_id(&mut b, &mut class_handles, pool, d)?)
            } else {
                None
            };
            let arg_classes: Vec<Option<ClassHandle>> = method
                .arg_types
                .iter()
                .map(|t| {
                    if let Type::Reference(d) = t {
                        resolve_class_id(&mut b, &mut class_handles, pool, *d).map(Some)
                    } else {
                        Ok(None)
                    }
                })
                .collect::<Result<_, Error>>()?;

            let proto = b.create_proto_ex(&ret_type, ret_class, &method.arg_types, &arg_classes);

            let method_h = if method.is_external {
                b.add_foreign_method_cstr(cls_h, &method_name_cstr, proto, method.access_flags)
            } else {
                let (code_bytes, byte_offsets, method_entity_ops) =
                    if let Some(ref body) = method.body {
                        let bcs = body.bytecodes();
                        let (cb, offs) = abcd_isa::encode(&bcs)
                            .map_err(|e| Error::BytecodeEncode(e.to_string()))?;
                        let mut ops_out = Vec::new();
                        for (instruction, &byte_offset) in bcs.iter().zip(&offs) {
                            let (ops, len) = instruction.entity_operands_inline();
                            for (ordinal, &(kind, id)) in ops[..len].iter().enumerate() {
                                ops_out.push((byte_offset, ordinal as u32, kind, id.0));
                            }
                        }
                        (cb, offs, ops_out)
                    } else {
                        (Vec::new(), Vec::new(), Vec::new())
                    };

                let (num_vregs, num_args) = method
                    .body
                    .as_ref()
                    .map_or((0, method.arg_types.len() as u32), |b| {
                        (b.num_vregs, b.num_args)
                    });

                let has_try_blocks = method
                    .body
                    .as_ref()
                    .is_some_and(|b| !b.try_blocks.is_empty());

                let inline_code = if has_try_blocks { &[][..] } else { &code_bytes };
                let m_h = b.class_add_method_cstr(
                    cls_h,
                    &method_name_cstr,
                    proto,
                    method.access_flags,
                    inline_code,
                    num_vregs,
                    num_args,
                );

                // Try blocks (strictly validated against instruction indices).
                if let Some(ref body) = method.body
                    && !body.try_blocks.is_empty()
                {
                    let code_byte_len = code_bytes.len() as u32;
                    let method_label = pool.resolve(method.name).unwrap_or("<method>");
                    let checked_pc = |idx: u32, field: &'static str| -> Result<u32, Error> {
                        let i = idx as usize;
                        if let Some(&off) = byte_offsets.get(i) {
                            Ok(off)
                        } else if i == byte_offsets.len() {
                            Ok(code_byte_len)
                        } else {
                            Err(Error::Malformed {
                                field,
                                context: format!(
                                    "method {method_label}: instruction index {idx} out of bounds (insn count {})",
                                    byte_offsets.len()
                                ),
                            })
                        }
                    };
                    let code_h = b.create_code(&code_bytes, num_vregs, num_args);
                    for tb in &body.try_blocks {
                        let tb_end =
                            tb.start
                                .checked_add(tb.len)
                                .ok_or_else(|| Error::Malformed {
                                    field: "try_block",
                                    context: format!("method {method_label}: try span overflow"),
                                })?;
                        let start_pc = checked_pc(tb.start, "try_block")?;
                        let end_pc = checked_pc(tb_end, "try_block")?;
                        let catches: Vec<CatchBlockDef> = tb
                            .catches
                            .iter()
                            .map(|cb| {
                                let type_class = match cb.type_class {
                                    None => None,
                                    Some(desc_sid) => Some(resolve_class_id(
                                        &mut b,
                                        &mut class_handles,
                                        pool,
                                        desc_sid,
                                    )?),
                                };
                                let cb_end = cb.handler.checked_add(cb.len).ok_or_else(|| {
                                    Error::Malformed {
                                        field: "catch_block",
                                        context: format!(
                                            "method {method_label}: catch span overflow"
                                        ),
                                    }
                                })?;
                                let handler_pc = checked_pc(cb.handler, "catch_block")?;
                                let handler_end_pc = checked_pc(cb_end, "catch_block")?;
                                Ok(CatchBlockDef {
                                    type_class,
                                    handler_pc,
                                    code_size: handler_end_pc.saturating_sub(handler_pc),
                                })
                            })
                            .collect::<Result<_, Error>>()?;
                        b.code_add_try_block(
                            code_h,
                            start_pc,
                            end_pc.saturating_sub(start_pc),
                            &catches,
                        );
                    }
                    b.method_set_code(m_h, code_h);
                }

                // Debug info
                if let Some(ref dbg) = method.debug {
                    encode_debug_info(
                        &mut b,
                        &mut string_handles,
                        pool,
                        m_h,
                        dbg,
                        class_has_source_file,
                        &byte_offsets,
                        code_bytes.len() as u32,
                    )?;
                }

                if let Some(body) = &method.body
                    && !method_entity_ops.is_empty()
                {
                    code_references.push((m_h, method_entity_ops, body));
                }

                m_h
            };

            b.method_set_source_lang(method_h, method.source_lang);
            let raw_hi = ((method.access_flags.bits() >> 8) & 0xFF) as u8;
            let sendable = sys::FunctionKind_SENDABLE_FUNCTION;
            let raw_kind = if (raw_hi & !0x07) == sendable {
                let base = raw_hi & 0x07;
                if (method.function_kind == FunctionKind::SendableFunction
                    && base == sys::FunctionKind_FUNCTION)
                    || (base != 0
                        && base != sys::FunctionKind_CONCURRENT_FUNCTION
                        && (method.function_kind as u8) == base)
                {
                    raw_hi
                } else {
                    method.function_kind as u8
                }
            } else {
                method.function_kind as u8
            };
            b.method_set_function_kind_raw(method_h, raw_kind);

            entities.insert_method(method, method_h);
        }

        // --- Fields ---
        for field in &cls.fields {
            let field_name_cstr = rcstr(field.name)?;
            let ty = field.field_type;
            let field_h = if field.is_external {
                b.add_foreign_field_cstr(cls_h, &field_name_cstr, ty)
            } else if let Type::Reference(d) = ty {
                let ref_cls = resolve_class_id(&mut b, &mut class_handles, pool, d)?;
                b.class_add_field_ex_cstr(cls_h, &field_name_cstr, ty, ref_cls, field.access_flags)
            } else {
                b.class_add_field_cstr(cls_h, &field_name_cstr, ty, field.access_flags)
            };

            entities.insert_field(field, field_h);

            match &field.initial_value {
                Some(FieldValue::I32(v)) => b.field_set_value_i32(field_h, *v),
                Some(FieldValue::I64(v)) => b.field_set_value_i64(field_h, *v),
                Some(FieldValue::F32(v)) => b.field_set_value_f32(field_h, *v),
                Some(FieldValue::F64(v)) => b.field_set_value_f64(field_h, *v),
                Some(
                    FieldValue::String(sid) | FieldValue::JsonFileContent { content: sid, .. },
                ) => {
                    let sh = get_or_add_string_id(&mut b, &mut string_handles, pool, *sid)?;
                    b.field_set_value_string(field_h, sh)?;
                }
                Some(
                    fv @ (FieldValue::ModuleData(_)
                    | FieldValue::LiteralArrayRef { .. }
                    | FieldValue::ModuleRequestPhase(_)),
                ) => deferred_field_values.push((field_h, fv)),
                None => {}
            }
        }
    }

    // Pre-create model `literal_handles` BEFORE encoding annotations so model
    // literal arrays occupy `header.literalarray_idx[0..file.literal_arrays.len()]`
    // (`LiteralValue::LiteralBufferIndex` stability on `<= 12.0.6.0`), while
    // annotation-embedded literal arrays follow after them.
    let literal_handles: Vec<_> = (0..file.literal_arrays.len())
        .map(|index| b.add_literal_array(&index.to_string()))
        .collect();

    // --- Attach annotations now that all MethodHandles & FieldHandles exist ---
    let mut flat_method_idx = 0usize;
    let mut flat_field_idx = 0usize;
    for (&desc, cls) in &file.classes {
        let cls_h = class_handles[&desc];

        for method in &cls.methods {
            let method_h = entities.methods_by_idx[flat_method_idx];
            flat_method_idx += 1;

            // Method annotations
            {
                let synced_annotations;
                let annotations = match method.body.as_ref().and_then(|b| b.ic_size) {
                    Some(ic_size) => {
                        synced_annotations =
                            sync_slot_number_annotation(&method.annotations, pool, ic_size);
                        &synced_annotations
                    }
                    None => &method.annotations,
                };
                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    deferred_ann_las: &mut deferred_ann_las,
                    pool,
                };
                encode_annotations_on(
                    &mut b,
                    &mut ctx,
                    annotations,
                    AnnotationTarget::Method(method_h),
                )?;
            }

            // --- Parameter annotations ---
            let pa = &method.param_annotations;
            let has_compile = pa.compile_time.iter().any(|v| !v.is_empty());
            let has_runtime = pa.runtime.iter().any(|v| !v.is_empty());
            if !method.is_external && (has_compile || has_runtime) {
                let num_params = method
                    .arg_types
                    .len()
                    .max(pa.compile_time.len())
                    .max(pa.runtime.len());
                let mut param_handles = Vec::with_capacity(num_params);
                for i in 0..num_params {
                    let ty = method.arg_types.get(i).copied().unwrap_or(Type::Tagged);
                    let ref_cls = if let Type::Reference(d) = ty {
                        Some(resolve_class_id(&mut b, &mut class_handles, pool, d)?)
                    } else {
                        None
                    };
                    param_handles.push(b.method_add_param_ex(method_h, ty, ref_cls));
                }

                let mut ctx = AnnotationEncodeCtx {
                    string_handles: &mut string_handles,
                    class_handles: &mut class_handles,
                    entities: &entities,
                    ann_la_counter: &mut ann_la_counter,
                    deferred_ann_las: &mut deferred_ann_las,
                    pool,
                };
                if has_compile {
                    for (idx, param_h) in param_handles.iter().enumerate() {
                        for ann in pa.compile_time.get(idx).into_iter().flatten() {
                            let ann_h = encode_single_annotation(&mut b, &mut ctx, ann)?;
                            b.method_param_add_annotation(method_h, *param_h, ann_h);
                        }
                    }
                    b.method_seal_param_annotations(method_h, false)?;
                }
                if has_runtime {
                    for (idx, param_h) in param_handles.iter().enumerate() {
                        for ann in pa.runtime.get(idx).into_iter().flatten() {
                            let ann_h = encode_single_annotation(&mut b, &mut ctx, ann)?;
                            b.method_param_add_runtime_annotation(method_h, *param_h, ann_h);
                        }
                    }
                    b.method_seal_param_annotations(method_h, true)?;
                }
            }
        }

        for field in &cls.fields {
            let field_h = entities.fields_by_idx[flat_field_idx];
            flat_field_idx += 1;

            let mut ctx = AnnotationEncodeCtx {
                string_handles: &mut string_handles,
                class_handles: &mut class_handles,
                entities: &entities,
                ann_la_counter: &mut ann_la_counter,
                deferred_ann_las: &mut deferred_ann_las,
                pool,
            };
            encode_annotations_on(
                &mut b,
                &mut ctx,
                &field.annotations,
                AnnotationTarget::Field(field_h),
            )?;
        }

        // Class annotations
        {
            let mut ctx = AnnotationEncodeCtx {
                string_handles: &mut string_handles,
                class_handles: &mut class_handles,
                entities: &entities,
                ann_la_counter: &mut ann_la_counter,
                deferred_ann_las: &mut deferred_ann_las,
                pool,
            };
            encode_annotations_on(
                &mut b,
                &mut ctx,
                &cls.annotations,
                AnnotationTarget::Class(cls_h),
            )?;
        }
    }

    // --- Literal array contents ---
    {
        let mut lit_ctx = LiteralEncodeCtx {
            string_handles: &mut string_handles,
            pool,
            entities: &entities,
            literal_handles: &literal_handles,
        };
        for (la_h, values) in &deferred_ann_las {
            for val in values {
                encode_literal_value(&mut b, &mut lit_ctx, *la_h, val)?;
            }
        }
        for (i, (la, &la_h)) in file.literal_arrays.iter().zip(&literal_handles).enumerate() {
            debug_assert_eq!(
                la_h.as_raw(),
                i as u32,
                "model literal-array handles must occupy 0..file.literal_arrays.len()"
            );
            for val in &la.values {
                encode_literal_value(&mut b, &mut lit_ctx, la_h, val)?;
            }
        }
    }

    // --- Module-record blobs and scope-names field references ---
    let mut module_la_counter: u32 = 0;
    for (field_h, value) in deferred_field_values {
        match value {
            FieldValue::ModuleData(md) => {
                let la_h = b.add_literal_array(&format!("module_la_{module_la_counter}"));
                module_la_counter += 1;
                let requests: Vec<StringHandle> = md
                    .requests
                    .iter()
                    .map(|&sid| get_or_add_string_id(&mut b, &mut string_handles, pool, sid))
                    .collect::<Result<_, _>>()?;
                let records: Vec<ModuleRecordDef> = md
                    .records
                    .iter()
                    .map(|rec| module_record_def(rec, &mut b, &mut string_handles, pool))
                    .collect::<Result<_, _>>()?;
                b.literal_array_add_module_data(la_h, &requests, &records)?;
                b.field_set_value_literalarray(field_h, la_h)?;
            }
            FieldValue::ModuleRequestPhase(phase) => {
                let la_h = b.add_literal_array(&format!("phase_la_{module_la_counter}"));
                module_la_counter += 1;
                b.literal_array_add_module_request_phase(la_h, &phase.flags)?;
                b.field_set_value_literalarray(field_h, la_h)?;
            }
            FieldValue::LiteralArrayRef { index, .. } => {
                let la_h = *literal_handles.get(index.index()).ok_or_else(|| {
                    Error::ModuleData(format!(
                        "scope-names literal array index {} out of range",
                        index.0
                    ))
                })?;
                b.field_set_value_literalarray(field_h, la_h)?;
            }
            _ => unreachable!("only offset-reference field values are deferred"),
        }
    }

    // Relocate bytecode entity operands.
    for (owner, method_entity_ops, body) in code_references {
        for (byte_offset, ordinal, kind, raw_id) in method_entity_ops {
            use abcd_isa::EntityKind;
            let unresolved = || {
                Error::CodeRelocation(format!(
                    "{:?} index {raw_id} at byte {byte_offset:#x}",
                    kind
                ))
            };
            let entity_ref = *body.entities.get(&(kind, raw_id)).ok_or_else(unresolved)?;
            let target = match (kind, entity_ref) {
                (EntityKind::StringId, EntityRef::String { id: sid, .. }) => CodeEntity::String(
                    get_or_add_string_id(&mut b, &mut string_handles, pool, sid)?,
                ),
                (EntityKind::MethodId, EntityRef::Method(midx)) => CodeEntity::Method(
                    *entities
                        .methods_by_idx
                        .get(midx.index())
                        .ok_or_else(unresolved)?,
                ),
                (EntityKind::LiteralarrayId, EntityRef::LiteralArray(la_idx)) => {
                    CodeEntity::LiteralArray(
                        *literal_handles.get(la_idx.index()).ok_or_else(unresolved)?,
                    )
                }
                _ => return Err(unresolved()),
            };
            b.relocate_code_id(owner, byte_offset, ordinal, target)?;
        }
    }

    b.deduplicate();
    let output = b.finalize()?;
    if options.verify {
        crate::inspect_summary(&output, true)
            .map_err(|e| Error::FinalizeValidation(e.to_string()))?;
    }
    Ok(output)
}

/// Encode preflight over every annotation in the file (hard-errors rule):
/// reject out-of-bounds `LiteralValue::LiteralArray(idx)` inside an
/// annotation-embedded literal array (`CodeRelocation` with site/owner
/// context) BEFORE any bytes are emitted, using an explicit iterative
/// workstack.
fn validate_annotation_arrays(file: &File) -> Result<(), Error> {
    fn annotations(a: &Annotations) -> impl Iterator<Item = &Annotation> {
        a.compile_time
            .iter()
            .chain(a.runtime.iter())
            .chain(a.compile_time_type.iter())
            .chain(a.runtime_type.iter())
    }

    #[derive(Clone, Copy)]
    enum Owner {
        Class(StringId),
        Method(StringId, StringId),
        Field(StringId, StringId),
        MethodParam(StringId, StringId, usize),
    }

    #[derive(Clone, Copy)]
    struct Site {
        annotation: StringId,
        element: StringId,
    }

    fn resolve(pool: &StringPool, sid: StringId) -> &str {
        pool.resolve(sid).unwrap_or("<unknown>")
    }

    fn owner_string(pool: &StringPool, owner: Owner) -> String {
        match owner {
            Owner::Class(c) => format!("class {}", resolve(pool, c)),
            Owner::Method(c, m) => format!("method {}::{}", resolve(pool, c), resolve(pool, m)),
            Owner::Field(c, f) => format!("field {}::{}", resolve(pool, c), resolve(pool, f)),
            Owner::MethodParam(c, m, i) => format!(
                "parameter {i} of method {}::{}",
                resolve(pool, c),
                resolve(pool, m)
            ),
        }
    }

    fn validate_root<'a>(
        pool: &StringPool,
        literal_array_count: usize,
        owner: Owner,
        site: Site,
        root: &'a AnnotationValue,
        stack: &mut Vec<(Owner, Site, &'a AnnotationValue)>,
    ) -> Result<(), Error> {
        stack.clear();
        stack.push((owner, site, root));
        while let Some((cur_owner, cur_site, v)) = stack.pop() {
            match v {
                AnnotationValue::Array { values, .. } => {
                    for item in values.iter().rev() {
                        stack.push((cur_owner, cur_site, item));
                    }
                }
                AnnotationValue::Annotation(a) => {
                    for e in a.elements.iter().rev() {
                        stack.push((
                            cur_owner,
                            Site {
                                annotation: a.class_descriptor,
                                element: e.name,
                            },
                            &e.value,
                        ));
                    }
                }
                AnnotationValue::LiteralArray(values) => {
                    for (item_index, item) in values.iter().enumerate() {
                        if let Some(idx) = item.literal_array_idx()
                            && idx.index() >= literal_array_count
                        {
                            return Err(Error::CodeRelocation(format!(
                                "annotation {} element '{}' on {}: nested literal array index {} at item {} out of bounds (table len {})",
                                resolve(pool, cur_site.annotation),
                                resolve(pool, cur_site.element),
                                owner_string(pool, cur_owner),
                                idx.0,
                                item_index,
                                literal_array_count,
                            )));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    let pool = &file.strings;
    let literal_array_count = file.literal_arrays.len();
    let mut stack: Vec<(Owner, Site, &AnnotationValue)> = Vec::new();

    for class in file.classes.values() {
        for ann in annotations(&class.annotations) {
            for e in &ann.elements {
                validate_root(
                    pool,
                    literal_array_count,
                    Owner::Class(class.descriptor),
                    Site {
                        annotation: ann.class_descriptor,
                        element: e.name,
                    },
                    &e.value,
                    &mut stack,
                )?;
            }
        }
        for method in &class.methods {
            for ann in annotations(&method.annotations) {
                for e in &ann.elements {
                    validate_root(
                        pool,
                        literal_array_count,
                        Owner::Method(class.descriptor, method.name),
                        Site {
                            annotation: ann.class_descriptor,
                            element: e.name,
                        },
                        &e.value,
                        &mut stack,
                    )?;
                }
            }
            for bucket in [
                &method.param_annotations.compile_time,
                &method.param_annotations.runtime,
            ] {
                for (index, anns) in bucket.iter().enumerate() {
                    for ann in anns {
                        for e in &ann.elements {
                            validate_root(
                                pool,
                                literal_array_count,
                                Owner::MethodParam(class.descriptor, method.name, index),
                                Site {
                                    annotation: ann.class_descriptor,
                                    element: e.name,
                                },
                                &e.value,
                                &mut stack,
                            )?;
                        }
                    }
                }
            }
        }
        for field in &class.fields {
            for ann in annotations(&field.annotations) {
                for e in &ann.elements {
                    validate_root(
                        pool,
                        literal_array_count,
                        Owner::Field(class.descriptor, field.name),
                        Site {
                            annotation: ann.class_descriptor,
                            element: e.name,
                        },
                        &e.value,
                        &mut stack,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn validate_literal_array_graph(literal_arrays: &[LiteralArray]) -> Result<(), Error> {
    let len = literal_arrays.len();
    for la in literal_arrays {
        for item in &la.values {
            if let Some(idx) = item.literal_array_idx()
                && idx.index() >= len
            {
                return Err(Error::CodeRelocation(format!(
                    "nested literal array index {} out of bounds",
                    idx.0
                )));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

enum AnnotationTarget {
    Class(ClassHandle),
    Method(MethodHandle),
    Field(FieldHandle),
}

struct AnnotationEncodeCtx<'a> {
    string_handles: &'a mut [Option<StringHandle>],
    class_handles: &'a mut HashMap<StringId, ClassHandle>,
    entities: &'a EntityHandles,
    ann_la_counter: &'a mut u32,
    deferred_ann_las: &'a mut Vec<(LiteralArrayHandle, Vec<LiteralValue>)>,
    pool: &'a StringPool,
}

fn sync_slot_number_annotation(
    anns: &Annotations,
    pool: &crate::StringPool,
    ic_size: u32,
) -> Annotations {
    const ANNOTATION_CLASS: &str = "L_ESSlotNumberAnnotation;";
    const ELEMENT_NAME: &str = "SlotNumber";

    let mut synced = anns.clone();
    for bucket in [
        &mut synced.compile_time,
        &mut synced.runtime,
        &mut synced.compile_time_type,
        &mut synced.runtime_type,
    ] {
        for ann in bucket.iter_mut() {
            if pool.resolve(ann.class_descriptor) != Some(ANNOTATION_CLASS) {
                continue;
            }
            for elem in &mut ann.elements {
                if pool.resolve(elem.name) == Some(ELEMENT_NAME) {
                    elem.value = AnnotationValue::U32(ic_size);
                }
            }
        }
    }
    synced
}

type AttachAnnotationFn = fn(&mut Builder, &AnnotationTarget, AnnotationHandle);

fn encode_annotations_on(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    anns: &Annotations,
    target: AnnotationTarget,
) -> Result<(), Error> {
    let groups: [(&[Annotation], AttachAnnotationFn); 4] = [
        (&anns.compile_time, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_annotation(*h, a),
        }),
        (&anns.runtime, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_runtime_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_runtime_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_runtime_annotation(*h, a),
        }),
        (&anns.compile_time_type, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_type_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_type_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_type_annotation(*h, a),
        }),
        (&anns.runtime_type, |b, t, a| match t {
            AnnotationTarget::Class(h) => b.class_add_runtime_type_annotation(*h, a),
            AnnotationTarget::Method(h) => b.method_add_runtime_type_annotation(*h, a),
            AnnotationTarget::Field(h) => b.field_add_runtime_type_annotation(*h, a),
        }),
    ];

    for (ann_list, attach_fn) in &groups {
        for ann in *ann_list {
            let ann_h = encode_single_annotation(b, ctx, ann)?;
            attach_fn(b, &target, ann_h);
        }
    }
    Ok(())
}

enum PendingEncodeElem<'a> {
    Scalar {
        name: StringHandle,
    },
    Array {
        name: StringHandle,
        tag: u8,
        remaining: std::slice::Iter<'a, AnnotationValue>,
        handles: Vec<u64>,
    },
}

struct AnnEncodeFrame<'a> {
    ann_cls: ClassHandle,
    elems_iter: std::slice::Iter<'a, AnnotationElem>,
    encoded_elems: Vec<AnnotationElemDefEx>,
    pending: Option<PendingEncodeElem<'a>>,
}

fn encode_single_annotation(
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
    ann: &Annotation,
) -> Result<AnnotationHandle, Error> {
    use sys::AnnotationValueType as AVT;

    let root_cls = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, ann.class_descriptor)?;
    let mut stack = vec![AnnEncodeFrame {
        ann_cls: root_cls,
        elems_iter: ann.elements.iter(),
        encoded_elems: Vec::with_capacity(ann.elements.len()),
        pending: None,
    }];
    let mut completed: Option<AnnotationHandle> = None;

    while let Some(frame) = stack.last_mut() {
        let mut next_child: Option<AnnEncodeFrame<'_>> = None;
        if let Some(child_h) = completed.take() {
            match frame.pending.take() {
                Some(PendingEncodeElem::Scalar { name }) => {
                    frame.encoded_elems.push(AnnotationElemDefEx {
                        name,
                        tag: AVT::Annotation as u8,
                        value: AnnotationElemValue::EntityRef(child_h.0),
                    });
                }
                Some(PendingEncodeElem::Array {
                    name,
                    tag,
                    mut remaining,
                    mut handles,
                }) => {
                    handles.push(u64::from(child_h.0));
                    for item in &mut remaining {
                        if let AnnotationValue::Annotation(nested) = item {
                            let child_cls = resolve_class_for_ann(
                                b,
                                ctx.class_handles,
                                ctx.pool,
                                nested.class_descriptor,
                            )?;
                            frame.pending = Some(PendingEncodeElem::Array {
                                name,
                                tag,
                                remaining,
                                handles: std::mem::take(&mut handles),
                            });
                            next_child = Some(AnnEncodeFrame {
                                ann_cls: child_cls,
                                elems_iter: nested.elements.iter(),
                                encoded_elems: Vec::with_capacity(nested.elements.len()),
                                pending: None,
                            });
                            break;
                        }
                        handles.push(annotation_array_leaf_to_handle(item, b, ctx)?);
                    }
                    if next_child.is_none() {
                        let value = if is_entity_array_tag(tag) {
                            AnnotationElemValue::EntityArray(
                                handles.into_iter().map(|h| h as u32).collect(),
                            )
                        } else {
                            AnnotationElemValue::Array64(handles)
                        };
                        frame
                            .encoded_elems
                            .push(AnnotationElemDefEx { name, tag, value });
                    }
                }
                None => {}
            }
        }
        if let Some(child_frame) = next_child {
            stack.push(child_frame);
            continue;
        }

        for e in &mut frame.elems_iter {
            let name = get_or_add_string_id(b, ctx.string_handles, ctx.pool, e.name)?;
            match &e.value {
                AnnotationValue::Annotation(nested) => {
                    let child_cls = resolve_class_for_ann(
                        b,
                        ctx.class_handles,
                        ctx.pool,
                        nested.class_descriptor,
                    )?;
                    frame.pending = Some(PendingEncodeElem::Scalar { name });
                    next_child = Some(AnnEncodeFrame {
                        ann_cls: child_cls,
                        elems_iter: nested.elements.iter(),
                        encoded_elems: Vec::with_capacity(nested.elements.len()),
                        pending: None,
                    });
                    break;
                }
                AnnotationValue::Array { tag, values } => {
                    let mut remaining = values.iter();
                    let mut handles = Vec::with_capacity(values.len());
                    for item in &mut remaining {
                        if let AnnotationValue::Annotation(nested) = item {
                            let child_cls = resolve_class_for_ann(
                                b,
                                ctx.class_handles,
                                ctx.pool,
                                nested.class_descriptor,
                            )?;
                            frame.pending = Some(PendingEncodeElem::Array {
                                name,
                                tag: *tag,
                                remaining,
                                handles: std::mem::take(&mut handles),
                            });
                            next_child = Some(AnnEncodeFrame {
                                ann_cls: child_cls,
                                elems_iter: nested.elements.iter(),
                                encoded_elems: Vec::with_capacity(nested.elements.len()),
                                pending: None,
                            });
                            break;
                        }
                        handles.push(annotation_array_leaf_to_handle(item, b, ctx)?);
                    }
                    if next_child.is_some() {
                        break;
                    }
                    let value = if is_entity_array_tag(*tag) {
                        AnnotationElemValue::EntityArray(
                            handles.into_iter().map(|h| h as u32).collect(),
                        )
                    } else {
                        AnnotationElemValue::Array64(handles)
                    };
                    frame.encoded_elems.push(AnnotationElemDefEx {
                        name,
                        tag: *tag,
                        value,
                    });
                }
                other => {
                    let (tag, value) = annotation_scalar_value_to_raw(other, b, ctx)?;
                    frame
                        .encoded_elems
                        .push(AnnotationElemDefEx { name, tag, value });
                }
            }
        }

        if let Some(child_frame) = next_child {
            stack.push(child_frame);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        let ann_h = b.create_annotation_ex(finished.ann_cls, &finished.encoded_elems);
        if stack.is_empty() {
            return Ok(ann_h);
        }
        completed = Some(ann_h);
    }

    Err(Error::Finalize)
}

fn annotation_scalar_value_to_raw(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<(u8, AnnotationElemValue), Error> {
    use sys::AnnotationValueType as AVT;

    let unresolved = |kind: &str, name: StringId, offset: u32| {
        Error::CodeRelocation(format!(
            "annotation {kind} reference '{}' at offset {offset:#x} cannot be resolved",
            ctx.pool.resolve(name).unwrap_or("<unknown>")
        ))
    };

    let raw = match val {
        AnnotationValue::Bool(v) => (AVT::U1 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I8(v) => (AVT::I8 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U8(v) => (AVT::U8 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I16(v) => (AVT::I16 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U16(v) => (AVT::U16 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::I32(v) => (AVT::I32 as u8, AnnotationElemValue::Scalar(*v as u32)),
        AnnotationValue::U32(v) => (AVT::U32 as u8, AnnotationElemValue::Scalar(*v)),
        AnnotationValue::I64(v) => (AVT::I64 as u8, AnnotationElemValue::Scalar64(*v as u64)),
        AnnotationValue::U64(v) => (AVT::U64 as u8, AnnotationElemValue::Scalar64(*v)),
        AnnotationValue::F32(v) => (AVT::F32 as u8, AnnotationElemValue::Scalar(v.to_bits())),
        AnnotationValue::F64(v) => (AVT::F64 as u8, AnnotationElemValue::Scalar64(v.to_bits())),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            (AVT::String as u8, AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid)?;
            (AVT::Record as u8, AnnotationElemValue::EntityRef(h.0))
        }
        AnnotationValue::Method {
            name,
            method,
            offset,
        } => {
            let mh = ctx
                .entities
                .resolve_method(*name, *method, *offset)
                .ok_or_else(|| unresolved("method", *name, *offset))?;
            (AVT::Method as u8, AnnotationElemValue::EntityRef(mh.0))
        }
        AnnotationValue::Enum {
            name,
            field,
            offset,
        } => {
            let fh = ctx
                .entities
                .resolve_field(*name, *field, *offset)
                .ok_or_else(|| unresolved("enum", *name, *offset))?;
            (AVT::Enum as u8, AnnotationElemValue::EntityRef(fh.0))
        }
        AnnotationValue::MethodHandle(mh) => {
            let entity_handle = if mh.handle_type.is_field_op() {
                ctx.entities
                    .resolve_field(mh.entity, mh.target_field, mh.entity_offset)
                    .map(|h| h.0)
            } else {
                ctx.entities
                    .resolve_method(mh.entity, mh.target_method, mh.entity_offset)
                    .map(|h| h.0)
            }
            .ok_or_else(|| unresolved("method-handle", mh.entity, mh.entity_offset))?;
            let mh_item = b.create_method_handle(mh.handle_type as u8, entity_handle);
            (
                AVT::MethodHandle as u8,
                AnnotationElemValue::EntityRef(mh_item.0),
            )
        }
        AnnotationValue::LiteralArray(values) => {
            let id = format!("ann_la_{}", *ctx.ann_la_counter);
            *ctx.ann_la_counter += 1;
            let la_h = b.add_literal_array(&id);
            ctx.deferred_ann_las.push((la_h, values.clone()));
            (
                AVT::LiteralArray as u8,
                AnnotationElemValue::EntityRef(la_h.0),
            )
        }
        AnnotationValue::Void => (AVT::Void as u8, AnnotationElemValue::Scalar(0)),
        AnnotationValue::StringNullptr => {
            (AVT::StringNullptr as u8, AnnotationElemValue::Scalar(0))
        }
        AnnotationValue::Annotation(_) | AnnotationValue::Array { .. } => {
            unreachable!("compound annotation values are dispatched by encode_single_annotation")
        }
    };
    Ok(raw)
}

fn is_entity_array_tag(tag: u8) -> bool {
    use sys::AnnotationValueType as AVT;
    matches!(
        AVT::try_from(tag),
        Ok(AVT::ArrayString
            | AVT::ArrayRecord
            | AVT::ArrayMethod
            | AVT::ArrayEnum
            | AVT::ArrayAnnotation
            | AVT::ArrayMethodHandle
            | AVT::LiteralArray)
    )
}

fn annotation_array_leaf_to_handle(
    val: &AnnotationValue,
    b: &mut Builder,
    ctx: &mut AnnotationEncodeCtx<'_>,
) -> Result<u64, Error> {
    let raw = match val {
        AnnotationValue::Bool(v) => u64::from(*v),
        AnnotationValue::I8(v) => u64::from(*v as u32),
        AnnotationValue::U8(v) => u64::from(*v),
        AnnotationValue::I16(v) => u64::from(*v as u32),
        AnnotationValue::U16(v) => u64::from(*v),
        AnnotationValue::I32(v) => u64::from(*v as u32),
        AnnotationValue::U32(v) => u64::from(*v),
        AnnotationValue::I64(v) => *v as u64,
        AnnotationValue::U64(v) => *v,
        AnnotationValue::F32(v) => u64::from(v.to_bits()),
        AnnotationValue::F64(v) => v.to_bits(),
        AnnotationValue::String(sid) => {
            let h = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            u64::from(h.0)
        }
        AnnotationValue::Record(sid) => {
            let h = resolve_class_for_ann(b, ctx.class_handles, ctx.pool, *sid)?;
            u64::from(h.0)
        }
        AnnotationValue::Method {
            name,
            method,
            offset,
        } => u64::from(
            ctx.entities
                .resolve_method(*name, *method, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array method reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0,
        ),
        AnnotationValue::Enum {
            name,
            field,
            offset,
        } => u64::from(
            ctx.entities
                .resolve_field(*name, *field, *offset)
                .ok_or_else(|| {
                    Error::CodeRelocation(format!(
                        "annotation array enum reference '{}' at offset {offset:#x} cannot be resolved",
                        ctx.pool.resolve(*name).unwrap_or("<unknown>")
                    ))
                })?
                .0,
        ),
        AnnotationValue::MethodHandle(mh) => {
            let entity_handle = if mh.handle_type.is_field_op() {
                ctx.entities
                    .resolve_field(mh.entity, mh.target_field, mh.entity_offset)
                    .map(|h| h.0)
            } else {
                ctx.entities
                    .resolve_method(mh.entity, mh.target_method, mh.entity_offset)
                    .map(|h| h.0)
            }
            .ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "annotation array method-handle reference '{}' at offset {:#x} cannot be resolved",
                    ctx.pool.resolve(mh.entity).unwrap_or("<unknown>"),
                    mh.entity_offset
                ))
            })?;
            u64::from(b.create_method_handle(mh.handle_type as u8, entity_handle).0)
        }
        AnnotationValue::LiteralArray(_) => {
            match annotation_scalar_value_to_raw(val, b, ctx)? {
                (_, AnnotationElemValue::EntityRef(h)) => u64::from(h),
                _ => unreachable!("literal-array values encode as entity refs"),
            }
        }
        AnnotationValue::Annotation(_) => {
            unreachable!(
                "nested annotations are dispatched iteratively by encode_single_annotation"
            )
        }
        AnnotationValue::Void | AnnotationValue::StringNullptr => 0,
        AnnotationValue::Array { .. } => {
            return Err(Error::CodeRelocation(
                "nested annotation arrays are not supported by the builder ABI".into(),
            ));
        }
    };
    Ok(raw)
}

fn resolve_class_for_ann(
    b: &mut Builder,
    class_handles: &mut HashMap<StringId, ClassHandle>,
    pool: &StringPool,
    desc: StringId,
) -> Result<ClassHandle, Error> {
    if let Some(&h) = class_handles.get(&desc) {
        return Ok(h);
    }
    let bytes = pool.to_mutf8_bytes(desc).ok_or_else(|| Error::Malformed {
        field: "string_id",
        context: format!("dangling StringId {desc:?} for annotation class descriptor"),
    })?;
    let h = b.add_foreign_class_cstr(&Builder::mutf8_cstr(&bytes)?);
    class_handles.insert(desc, h);
    Ok(h)
}

#[derive(Clone, Copy)]
enum LnpEventKind {
    EndLocal {
        reg: i32,
    },
    Line {
        line: u32,
    },
    Column {
        column: u32,
    },
    StartLocal {
        reg: i32,
        name: StringHandle,
        type_name: StringHandle,
        type_sig: Option<StringHandle>,
    },
}

impl LnpEventKind {
    const fn priority(&self) -> u8 {
        match self {
            Self::EndLocal { .. } => 0,
            Self::Line { .. } => 1,
            Self::Column { .. } => 2,
            Self::StartLocal { .. } => 3,
        }
    }
}

struct LnpEvent {
    pc: u32,
    seq: usize,
    kind: LnpEventKind,
}

#[expect(
    clippy::too_many_arguments,
    reason = "debug encoder threads builder, string pool/handles, class source_file flag, and instruction PCs"
)]
fn encode_debug_info(
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
    pool: &StringPool,
    method_h: MethodHandle,
    dbg: &MethodDebugInfo,
    class_has_source_file: bool,
    byte_offsets: &[u32],
    code_len: u32,
) -> Result<(), Error> {
    let non_empty = |sid: StringId| !pool.resolve(sid).unwrap_or("").is_empty();
    let has_content = !dbg.line_table.is_empty()
        || !dbg.column_table.is_empty()
        || !dbg.local_vars.is_empty()
        || !dbg.params.is_empty()
        || dbg.source_file.is_some_and(non_empty)
        || dbg.source_code.is_some_and(non_empty);
    if !has_content {
        return Ok(());
    }

    let lnp = b.create_lnp();
    let first_line = dbg.line_table.first().map_or(0, |e| e.line);
    let debug_h = b.create_debug_info(lnp, first_line);

    let mut emitted_set_file = false;
    if let Some(sf) = dbg.source_file {
        let sf_str = pool.resolve(sf).unwrap_or("");
        if !sf_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sf)?;
            b.lnp_emit_set_file(lnp, debug_h, sh);
            emitted_set_file = true;
        }
    }
    if !emitted_set_file && !class_has_source_file {
        let empty_sh = b.add_string("");
        b.lnp_emit_set_file(lnp, debug_h, empty_sh);
    }
    if let Some(sc) = dbg.source_code {
        let sc_str = pool.resolve(sc).unwrap_or("");
        if !sc_str.is_empty() {
            let sh = get_or_add_string_id(b, string_handles, pool, sc)?;
            b.lnp_emit_set_source_code(lnp, debug_h, sh);
        }
    }

    for p in &dbg.params {
        let nh = get_or_add_string_id(b, string_handles, pool, p.name)?;
        b.debug_add_param(debug_h, nh);
    }

    // `ProcessBegin()` in `DebugInfoExtractor` unconditionally pushes
    // `{ offset: 0, line: first_line }` before executing the first opcode.
    // Skip `line_table[0]` when it already sits at PC 0 so it is not duplicated.
    let skip_initial_line = dbg
        .line_table
        .first()
        .is_some_and(|first| index_to_offset(byte_offsets, first.index, code_len) == 0);
    let line_slice = if skip_initial_line {
        &dbg.line_table[1..]
    } else {
        &dbg.line_table[..]
    };

    // Determine the final PC so local variables spanning to the end of the
    // method close via `ProcessVars()` at `END_SEQUENCE` instead of emitting a
    // trailing `END_LOCAL` that could overwrite a nested inner variable on the
    // same register (`DebugInfoExtractor::HandleEndLocal` scans `rbegin()`
    // without skipping already-closed entries).
    let mut final_unclosed_pc = code_len;
    for entry in line_slice {
        final_unclosed_pc =
            final_unclosed_pc.max(index_to_offset(byte_offsets, entry.index, code_len));
    }
    for entry in &dbg.column_table {
        final_unclosed_pc =
            final_unclosed_pc.max(index_to_offset(byte_offsets, entry.index, code_len));
    }
    for lv in &dbg.local_vars {
        let s = index_to_offset(byte_offsets, lv.start, code_len);
        let e = index_to_offset(byte_offsets, lv.end, code_len).max(s);
        final_unclosed_pc = final_unclosed_pc.max(e);
    }

    let mut events =
        Vec::with_capacity(line_slice.len() + dbg.column_table.len() + dbg.local_vars.len() * 2);
    let mut seq = 0usize;

    for entry in line_slice {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        events.push(LnpEvent {
            pc,
            seq,
            kind: LnpEventKind::Line { line: entry.line },
        });
        seq += 1;
    }

    for entry in &dbg.column_table {
        let pc = index_to_offset(byte_offsets, entry.index, code_len);
        events.push(LnpEvent {
            pc,
            seq,
            kind: LnpEventKind::Column {
                column: entry.column,
            },
        });
        seq += 1;
    }

    let mut has_implicit_end_local = false;
    for lv in &dbg.local_vars {
        let name_h = get_or_add_string_id(b, string_handles, pool, lv.name)?;
        let type_h = get_or_add_string_id(b, string_handles, pool, lv.type_name)?;
        let sig_h = if lv.type_signature == lv.type_name {
            None
        } else {
            Some(get_or_add_string_id(
                b,
                string_handles,
                pool,
                lv.type_signature,
            )?)
        };
        let start_pc = index_to_offset(byte_offsets, lv.start, code_len);
        let end_pc = index_to_offset(byte_offsets, lv.end, code_len).max(start_pc);

        if end_pc == start_pc {
            // Zero-length range: start then immediately end at `start_pc`
            // unless `end_pc == 0 == final_unclosed_pc` (empty program).
            events.push(LnpEvent {
                pc: start_pc,
                seq,
                kind: LnpEventKind::StartLocal {
                    reg: lv.reg_number,
                    name: name_h,
                    type_name: type_h,
                    type_sig: sig_h,
                },
            });
            seq += 1;
            if end_pc > 0 && end_pc < final_unclosed_pc {
                events.push(LnpEvent {
                    pc: end_pc,
                    seq,
                    kind: LnpEventKind::EndLocal { reg: lv.reg_number },
                });
                seq += 1;
            } else if end_pc > 0 {
                has_implicit_end_local = true;
            }
            continue;
        }

        events.push(LnpEvent {
            pc: start_pc,
            seq,
            kind: LnpEventKind::StartLocal {
                reg: lv.reg_number,
                name: name_h,
                type_name: type_h,
                type_sig: sig_h,
            },
        });
        seq += 1;

        if end_pc < final_unclosed_pc {
            events.push(LnpEvent {
                pc: end_pc,
                seq,
                kind: LnpEventKind::EndLocal { reg: lv.reg_number },
            });
            seq += 1;
        } else if end_pc > 0 {
            has_implicit_end_local = true;
        }
    }

    // Sort by `(pc, priority, seq)`: at any PC, `EndLocal` runs before
    // `StartLocal` (except zero-length `[pc, pc)` where `EndLocal` shares `pc`
    // — wait: for zero-length `[pc, pc)` with `pc > 0`, `StartLocal` must
    // precede its own `EndLocal`! Handle zero-length `EndLocal` via `seq` only
    // or emit after `StartLocal`).
    events.sort_by_key(|ev| (ev.pc, ev.kind.priority(), ev.seq));

    // Re-check zero-length `[pc, pc)` locals where `start_pc == end_pc < final_unclosed_pc`:
    // ensure no `EndLocal` precedes its matching `StartLocal` on an unstarted register.
    let mut active_regs: HashMap<i32, usize> = HashMap::new();
    let mut deferred_same_pc_ends: Vec<i32> = Vec::new();
    let mut cur_pc: u32 = 0;
    let mut prev_line: u32 = first_line;
    let mut idx = 0usize;

    while idx < events.len() {
        let group_pc = events[idx].pc;
        let group_end = events[idx..]
            .iter()
            .position(|e| e.pc != group_pc)
            .map_or(events.len(), |off| idx + off);

        deferred_same_pc_ends.clear();
        for ev in &events[idx..group_end] {
            match ev.kind {
                LnpEventKind::EndLocal { reg } => {
                    if let Some(cnt) = active_regs.get_mut(&reg).filter(|c| **c > 0) {
                        *cnt -= 1;
                        if group_pc > cur_pc {
                            b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                            cur_pc = group_pc;
                        }
                        b.lnp_emit_end_local(lnp, reg);
                    } else {
                        deferred_same_pc_ends.push(reg);
                    }
                }
                LnpEventKind::Line { line } => {
                    let pc_delta = group_pc - cur_pc;
                    let line_delta = (line as i32).wrapping_sub(prev_line as i32);
                    b.lnp_emit_special_opcode(lnp, debug_h, pc_delta, line_delta);
                    cur_pc = group_pc;
                    prev_line = line;
                }
                LnpEventKind::Column { column } => {
                    let pc_delta = group_pc - cur_pc;
                    b.lnp_emit_column(lnp, debug_h, pc_delta, column);
                    cur_pc = group_pc;
                }
                LnpEventKind::StartLocal {
                    reg,
                    name,
                    type_name,
                    type_sig,
                } => {
                    if group_pc > cur_pc {
                        b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                        cur_pc = group_pc;
                    }
                    if let Some(sig) = type_sig {
                        b.lnp_emit_start_local_extended(lnp, debug_h, reg, name, type_name, sig);
                    } else {
                        b.lnp_emit_start_local(lnp, debug_h, reg, name, type_name);
                    }
                    *active_regs.entry(reg).or_insert(0) += 1;
                }
            }
        }
        for &reg in &deferred_same_pc_ends {
            if let Some(cnt) = active_regs.get_mut(&reg).filter(|c| **c > 0) {
                *cnt -= 1;
                if group_pc > cur_pc {
                    b.lnp_emit_advance_pc(lnp, debug_h, group_pc - cur_pc);
                    cur_pc = group_pc;
                }
                b.lnp_emit_end_local(lnp, reg);
            }
        }

        idx = group_end;
    }

    if has_implicit_end_local && final_unclosed_pc > cur_pc {
        b.lnp_emit_advance_pc(lnp, debug_h, final_unclosed_pc - cur_pc);
    }

    b.lnp_emit_end(lnp);
    b.method_set_debug_info(method_h, debug_h);
    Ok(())
}

struct LiteralEncodeCtx<'a> {
    string_handles: &'a mut [Option<StringHandle>],
    pool: &'a StringPool,
    entities: &'a EntityHandles,
    literal_handles: &'a [LiteralArrayHandle],
}

fn encode_literal_value(
    b: &mut Builder,
    ctx: &mut LiteralEncodeCtx<'_>,
    la: LiteralArrayHandle,
    val: &LiteralValue,
) -> Result<(), Error> {
    let resolve_method = |idx: MethodIdx| -> Option<MethodHandle> {
        ctx.entities.methods_by_idx.get(idx.index()).copied()
    };
    let check_la_idx = |idx: LiteralArrayIdx| -> Result<(), Error> {
        if idx.index() >= ctx.literal_handles.len() {
            return Err(Error::CodeRelocation(format!(
                "nested literal array index {} out of bounds",
                idx.0
            )));
        }
        Ok(())
    };

    match val {
        LiteralValue::Bool(v) => {
            b.literal_array_add_u8(la, LiteralTag::Bool as u8);
            b.literal_array_add_u8(la, *v as u8);
        }
        LiteralValue::Integer8(v) => {
            b.literal_array_add_u8(la, LiteralTag::TagValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::Integer(v) => {
            b.literal_array_add_u8(la, LiteralTag::Integer as u8);
            b.literal_array_add_u32(la, *v);
        }
        LiteralValue::Float(v) => {
            b.literal_array_add_u8(la, LiteralTag::Float as u8);
            b.literal_array_add_u32(la, v.to_bits());
        }
        LiteralValue::Double(v) => {
            b.literal_array_add_u8(la, LiteralTag::Double as u8);
            b.literal_array_add_u64(la, v.to_bits());
        }
        LiteralValue::String(sid) => {
            b.literal_array_add_u8(la, LiteralTag::String as u8);
            let sh = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::Method(idx) => {
            let mh = resolve_method(*idx).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array method reference MethodIdx({}) cannot be resolved",
                    idx.0
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Method as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::GeneratorMethod(idx) => {
            let mh = resolve_method(*idx).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array generator-method reference MethodIdx({}) cannot be resolved",
                    idx.0
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::GeneratorMethod as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::AsyncGeneratorMethod(idx) => {
            let mh = resolve_method(*idx).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array async-generator-method reference MethodIdx({}) cannot be resolved",
                    idx.0
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::AsyncGeneratorMethod as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::Getter(idx) => {
            let mh = resolve_method(*idx).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array getter reference MethodIdx({}) cannot be resolved",
                    idx.0
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Getter as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::Setter(idx) => {
            let mh = resolve_method(*idx).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "literal array setter reference MethodIdx({}) cannot be resolved",
                    idx.0
                ))
            })?;
            b.literal_array_add_u8(la, LiteralTag::Setter as u8);
            b.literal_array_add_raw_method(la, mh);
        }
        LiteralValue::Accessor(v) => {
            b.literal_array_add_u8(la, LiteralTag::Accessor as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::MethodAffiliate(v) => {
            b.literal_array_add_u8(la, LiteralTag::MethodAffiliate as u8);
            b.literal_array_add_u16(la, *v);
        }
        LiteralValue::LiteralArray(idx) => {
            let target = ctx.literal_handles.get(idx.index()).ok_or_else(|| {
                Error::CodeRelocation(format!(
                    "nested literal array index {} out of bounds",
                    idx.0
                ))
            })?;
            b.literal_array_add_literalarray(la, *target);
        }
        LiteralValue::LiteralBufferIndex(idx) => {
            check_la_idx(*idx)?;
            b.literal_array_add_u8(la, LiteralTag::LiteralBufferIndex as u8);
            b.literal_array_add_u32(la, idx.0);
        }
        LiteralValue::BuiltinTypeIndex(v) => {
            b.literal_array_add_u8(la, LiteralTag::BuiltinTypeIndex as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::EtsImplements(sid) => {
            b.literal_array_add_u8(la, LiteralTag::EtsImplements as u8);
            let sh = get_or_add_string_id(b, ctx.string_handles, ctx.pool, *sid)?;
            b.literal_array_add_raw_string(la, sh);
        }
        LiteralValue::NullValue(v) => {
            b.literal_array_add_u8(la, LiteralTag::NullValue as u8);
            b.literal_array_add_u8(la, *v);
        }
        LiteralValue::ArrayU1(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayU1 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u8(la, u8::from(x));
            }
        }
        LiteralValue::ArrayU8(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayU8 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u8(la, x);
            }
        }
        LiteralValue::ArrayI8(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayI8 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u8(la, x as u8);
            }
        }
        LiteralValue::ArrayU16(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayU16 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u16(la, x);
            }
        }
        LiteralValue::ArrayI16(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayI16 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u16(la, x as u16);
            }
        }
        LiteralValue::ArrayU32(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayU32 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u32(la, x);
            }
        }
        LiteralValue::ArrayI32(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayI32 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u32(la, x as u32);
            }
        }
        LiteralValue::ArrayU64(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayU64 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u64(la, x);
            }
        }
        LiteralValue::ArrayI64(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayI64 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u64(la, x as u64);
            }
        }
        LiteralValue::ArrayF32(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayF32 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u32(la, x.to_bits());
            }
        }
        LiteralValue::ArrayF64(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayF64 as u8);
            b.literal_array_add_u32(la, n);
            for &x in elems {
                b.literal_array_add_u64(la, x.to_bits());
            }
        }
        LiteralValue::ArrayString(elems) => {
            let n = u32::try_from(elems.len()).map_err(|_| Error::Malformed {
                field: "literal_array",
                context: "typed literal array length overflows u32".into(),
            })?;
            b.literal_array_add_u8(la, LiteralTag::ArrayString as u8);
            b.literal_array_add_u32(la, n);
            for &sid in elems {
                let sh = get_or_add_string_id(b, ctx.string_handles, ctx.pool, sid)?;
                b.literal_array_add_raw_string(la, sh);
            }
        }
    }
    Ok(())
}

fn index_to_offset(byte_offsets: &[u32], index: u32, code_len: u32) -> u32 {
    byte_offsets
        .get(index as usize)
        .copied()
        .unwrap_or(code_len)
}

fn get_or_add_string_id(
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
    pool: &StringPool,
    sid: StringId,
) -> Result<StringHandle, Error> {
    let idx = sid.index();
    if let Some(&Some(h)) = string_handles.get(idx) {
        return Ok(h);
    }
    let h = if let Some(raw) = pool.raw_mutf8(sid) {
        b.add_string_mutf8(raw)?
    } else {
        let s = pool.as_str(sid).ok_or_else(|| Error::Malformed {
            field: "string_id",
            context: format!("dangling StringId {sid:?} in string table"),
        })?;
        b.add_string(s)
    };
    if let Some(slot) = string_handles.get_mut(idx) {
        *slot = Some(h);
    }
    Ok(h)
}

fn module_record_def(
    rec: &ModuleRecord,
    b: &mut Builder,
    string_handles: &mut [Option<StringHandle>],
    pool: &StringPool,
) -> Result<ModuleRecordDef, Error> {
    let mut gs =
        |b: &mut Builder, sid: StringId| get_or_add_string_id(b, string_handles, pool, sid);
    let idx = |v: u32| -> Result<u16, Error> {
        u16::try_from(v).map_err(|_| {
            Error::ModuleData(format!(
                "module request index {v} exceeds the vendored u16 slot"
            ))
        })
    };
    Ok(match rec {
        ModuleRecord::RegularImport {
            local_name,
            import_name,
            module_request_idx,
        } => ModuleRecordDef::RegularImport {
            local_name: gs(b, *local_name)?,
            import_name: gs(b, *import_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::NamespaceImport {
            local_name,
            module_request_idx,
        } => ModuleRecordDef::NamespaceImport {
            local_name: gs(b, *local_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::LocalExport {
            local_name,
            export_name,
        } => ModuleRecordDef::LocalExport {
            local_name: gs(b, *local_name)?,
            export_name: gs(b, *export_name)?,
        },
        ModuleRecord::IndirectExport {
            export_name,
            import_name,
            module_request_idx,
        } => ModuleRecordDef::IndirectExport {
            export_name: gs(b, *export_name)?,
            import_name: gs(b, *import_name)?,
            module_request_idx: idx(*module_request_idx)?,
        },
        ModuleRecord::StarExport { module_request_idx } => ModuleRecordDef::StarExport {
            module_request_idx: idx(*module_request_idx)?,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{AccessFlags, SourceLang};
    fn method(pool: &mut StringPool, name: &str, offset: u32) -> Method {
        Method {
            name: pool.get_or_intern(name),
            offset,
            access_flags: AccessFlags::empty(),
            function_kind: FunctionKind::None,
            source_lang: SourceLang::EcmaScript,
            is_external: false,
            return_type: None,
            arg_types: Vec::new(),
            body: None,
            annotations: Annotations::default(),
            param_annotations: ParamAnnotations::default(),
            debug: None,
        }
    }

    fn field(pool: &mut StringPool, name: &str, offset: u32) -> Field {
        Field {
            name: pool.get_or_intern(name),
            offset,
            field_type: Type::Tagged,
            access_flags: AccessFlags::empty(),
            is_external: false,
            initial_value: None,
            annotations: Annotations::default(),
        }
    }

    #[test]
    fn handles_resolve_by_idx_and_offset_when_names_collide() {
        let mut pool = StringPool::default();
        let name = pool.get_or_intern("foo");
        let mut entities = EntityHandles::default();

        entities.insert_method(&method(&mut pool, "foo", 100), MethodHandle(1));
        entities.insert_method(&method(&mut pool, "foo", 200), MethodHandle(2));
        entities.insert_field(&field(&mut pool, "foo", 300), FieldHandle(3));
        entities.insert_field(&field(&mut pool, "foo", 400), FieldHandle(4));

        assert_eq!(
            entities.resolve_method(name, Some(MethodIdx(0)), 0),
            Some(MethodHandle(1))
        );
        assert_eq!(
            entities.resolve_method(name, Some(MethodIdx(1)), 0),
            Some(MethodHandle(2))
        );
        assert_eq!(entities.resolve_method(name, Some(MethodIdx(99)), 0), None);
        assert_eq!(
            entities.resolve_field(name, Some(FieldIdx(0)), 0),
            Some(FieldHandle(3))
        );
        assert_eq!(
            entities.resolve_field(name, Some(FieldIdx(1)), 0),
            Some(FieldHandle(4))
        );
        assert_eq!(entities.resolve_field(name, Some(FieldIdx(99)), 0), None);

        assert_eq!(
            entities.resolve_method(name, None, 100),
            Some(MethodHandle(1))
        );
        assert_eq!(
            entities.resolve_method(name, None, 200),
            Some(MethodHandle(2))
        );
        assert_eq!(
            entities.resolve_field(name, None, 300),
            Some(FieldHandle(3))
        );
        assert_eq!(
            entities.resolve_field(name, None, 400),
            Some(FieldHandle(4))
        );
        assert_eq!(entities.resolve_method(name, None, 999), None);
        assert_eq!(entities.resolve_field(name, None, 999), None);
    }

    #[test]
    fn handles_fall_back_to_name_for_offsetless_models() {
        let mut pool = StringPool::default();
        let name = pool.get_or_intern("bar");
        let mut entities = EntityHandles::default();

        entities.insert_method(&method(&mut pool, "bar", 0), MethodHandle(10));
        entities.insert_field(&field(&mut pool, "bar", 0), FieldHandle(20));

        assert_eq!(
            entities.resolve_method(name, None, 0),
            Some(MethodHandle(10))
        );
        assert_eq!(entities.resolve_field(name, None, 0), Some(FieldHandle(20)));
        // Unknown non-zero offsets must never silently alias by name (#44 R1-H6 #7).
        assert_eq!(entities.resolve_method(name, None, 999), None);
        assert_eq!(entities.resolve_field(name, None, 999), None);
    }
}
