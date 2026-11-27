//! Whole-module lowering and pool-materializing file rewrite (#30, `#50`
//! `R3-D2`, `#57` `R3-H8`/`R3-H9`/`R3-M8`).
//!
//! Bridges the gap between pure IR transformations and encodable
//! [`abcd_file::File`] containers in two modes:
//!
//! 1. [`rewrite_file`]: lowers all functions of `module` onto a clone of an
//!    existing `base_file`, preserving untouched container metadata while
//!    materializing any newly introduced [`Sym`] strings, [`Const`] literal
//!    arrays, classes, helper functions, and reconstructed [`MethodDebugInfo`]
//!    records into the output [`File`].
//! 2. [`lower_module`] / [`lower_module_with_options`]: standalone lowering
//!    from `&abcd_ir::Module` + [`abcd_file::Version`] directly to a complete,
//!    encodable [`abcd_file::File`] with zero source `File` dependency and zero
//!    fabricated file offsets (`#50`).

use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Annotations, CatchBlock, Class,
    ColumnEntry, EntityRef, Field, FieldIdx, FieldValue, File, FileType,
    FunctionKind as FileFunctionKind, LineEntry, LiteralArray, LiteralArrayIdx, LiteralValue,
    Method, MethodBody, MethodDebugInfo, MethodIdx, ModuleData, ModuleRecord, ModuleRequestPhase,
    ParamAnnotations, ParamInfo, SourceLang as FileSourceLang, StringId, StringPool, TryBlock,
    Type, Version,
};
use abcd_ir::{
    AnnValue, ClassData, Const, ConstId, ExportDecl, FieldData, FuncId,
    FunctionKind as IrFunctionKind, ImportDecl, LitMethodKind, Modifiers, Module, ModuleRequest,
    SourceLang as IrSourceLang, StaticTy, Sym, Ty, TypedArrayTag,
};
use abcd_isa::EntityKind;
use rayon::prelude::*;

use crate::layout::{LayoutResult, LoweredTryBlock};
use crate::method_body::{EntityResolver, relocate_and_compact_entities};
use crate::{LowerError, LowerOptions, lower_function_with_options};

const SLOT_NUMBER_ANN_DESC: &str = "L_ESSlotNumberAnnotation;";
const SLOT_NUMBER_ELEM: &str = "SlotNumber";

/// Rewrite `base_file` with lowered bodies from `module`, materializing any
/// IR-synthesized strings, literal arrays, classes, helper functions, and
/// reconstructed [`MethodDebugInfo`] tables into the returned [`File`] (#30,
/// `#50`, `#57`).
///
/// Invalid/dangling entity IDs (`Sym` outside `module.sym`, `FuncId` outside
/// `module.functions`, `ConstId` outside `module.consts` or non-shape
/// constants in `LiteralarrayId` slots) fail loudly with
/// [`LowerError::UntraceableEntity`].
pub fn rewrite_file(
    module: &Module,
    base_file: &File,
    options: LowerOptions,
) -> Result<File, LowerError> {
    let layouts = lower_all_layouts(module, options)?;
    // Index `base_file`'s original strings and literal arrays BEFORE mutating
    // `out.classes` so `FuncId` indices in `base_file.literal_arrays` match
    // `base_file.all_methods()` verbatim.
    let base_resolver = EntityResolver::new(module, base_file);
    let mut out = base_file.clone();

    // Map existing methods and fields in `base_file.all_methods()` / `all_fields()` order.
    let base_method_locs: Vec<(StringId, usize)> = out
        .classes
        .iter()
        .flat_map(|(&desc_sid, cls)| (0..cls.methods.len()).map(move |mi| (desc_sid, mi)))
        .collect();
    let base_field_locs: Vec<(StringId, usize)> = out
        .classes
        .iter()
        .flat_map(|(&desc_sid, cls)| (0..cls.fields.len()).map(move |fi| (desc_sid, fi)))
        .collect();

    // Intern all `module.classes` descriptors first so synthesized `super_class`
    // and `interfaces` resolve regardless of `ClassId` order.
    let mut class_desc_sids: Vec<StringId> = Vec::with_capacity(module.classes.len());
    for cls_data in &module.classes {
        let desc_sid = intern_sym(&module.sym, &mut out.strings, cls_data.descriptor).ok_or(
            LowerError::UntraceableEntity {
                func: FuncId::new(0),
                kind: EntityKind::StringId,
                raw: cls_data.descriptor.0,
            },
        )?;
        class_desc_sids.push(desc_sid);
    }

    // Ensure every class in `module.classes` exists in `out.classes` and
    // materialize synthesized classes' fields, `scope_names`, and `es_module`.
    let mut is_synth_class: Vec<bool> = Vec::with_capacity(module.classes.len());
    let mut field_slots: Vec<Vec<(StringId, usize)>> = Vec::with_capacity(module.classes.len());
    let mut synth_field_flags: Vec<Vec<bool>> = Vec::with_capacity(module.classes.len());
    let mut synth_scope_name_slots: Vec<(StringId, usize, ConstId)> = Vec::new();

    for (ci, cls_data) in module.classes.iter().enumerate() {
        let desc_sid = class_desc_sids[ci];
        let is_new_cls = !out.classes.contains_key(&desc_sid);
        is_synth_class.push(is_new_cls);

        if is_new_cls {
            let name_sid =
                intern_sym(&module.sym, &mut out.strings, cls_data.name).unwrap_or(desc_sid);
            let is_external = is_external_class(cls_data, module);
            let flags = modifiers_to_access_flags(cls_data.modifiers);
            let super_class = cls_data
                .super_class
                .and_then(|sc| class_desc_sids.get(sc.index()).copied());
            let interfaces = cls_data
                .interfaces
                .iter()
                .filter_map(|ic| class_desc_sids.get(ic.index()).copied())
                .collect();
            let source_file = cls_data
                .source_file
                .and_then(|sf| intern_sym(&module.sym, &mut out.strings, sf));
            out.classes.insert(
                desc_sid,
                Class {
                    descriptor: desc_sid,
                    name: name_sid,
                    access_flags: flags,
                    source_lang: source_lang_to_file(cls_data.source_lang),
                    source_file,
                    is_external,
                    super_class,
                    interfaces,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    annotations: Annotations::default(),
                },
            );
        }

        let mut cls_field_slots = Vec::with_capacity(cls_data.fields.len());
        let mut cls_synth_flags = Vec::with_capacity(cls_data.fields.len());
        for fdata in &cls_data.fields {
            let f_sid = intern_sym(&module.sym, &mut out.strings, fdata.name).ok_or(
                LowerError::UntraceableEntity {
                    func: FuncId::new(0),
                    kind: EntityKind::StringId,
                    raw: fdata.name.0,
                },
            )?;
            let existing_pos = out
                .classes
                .get(&desc_sid)
                .and_then(|c| c.fields.iter().position(|ef| ef.name == f_sid));
            if let Some(pos) = existing_pos {
                cls_field_slots.push((desc_sid, pos));
                cls_synth_flags.push(false);
            } else {
                let shell =
                    build_field_shell(module, fdata, f_sid, &class_desc_sids, &mut out.strings);
                let cls = out.classes.get_mut(&desc_sid).expect("inserted above");
                let pos = cls.fields.len();
                cls.fields.push(shell);
                cls_field_slots.push((desc_sid, pos));
                cls_synth_flags.push(true);
            }
        }
        field_slots.push(cls_field_slots);
        synth_field_flags.push(cls_synth_flags);

        if is_new_cls {
            if let Some(sn_cid) = cls_data.scope_names {
                let sn_name = out.strings.get_or_intern(abcd_file::SCOPE_NAMES_FIELD);
                let cls = out.classes.get_mut(&desc_sid).expect("inserted above");
                let slot_idx = cls.fields.len();
                cls.fields.push(Field {
                    name: sn_name,
                    offset: 0,
                    field_type: Type::U32,
                    access_flags: AccessFlags::STATIC,
                    is_external: false,
                    initial_value: None,
                    annotations: Annotations::default(),
                });
                synth_scope_name_slots.push((desc_sid, slot_idx, sn_cid));
            }
            if let Some(es_mod) = &cls_data.es_module {
                let (md, phase_opt) = build_module_data(
                    &module.sym,
                    &mut out.strings,
                    &es_mod.imports,
                    &es_mod.exports,
                    &es_mod.module_requests,
                )?;
                let mr_name = out
                    .strings
                    .get_or_intern(abcd_file::MODULE_RECORD_IDX_FIELD);
                let pname_opt = phase_opt.as_ref().map(|_| {
                    out.strings
                        .get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD)
                });
                let cls = out.classes.get_mut(&desc_sid).expect("inserted above");
                cls.fields.push(Field {
                    name: mr_name,
                    offset: 0,
                    field_type: Type::U32,
                    access_flags: AccessFlags::STATIC,
                    is_external: false,
                    initial_value: Some(FieldValue::ModuleData(md)),
                    annotations: Annotations::default(),
                });
                if let (Some(ph), Some(pname)) = (phase_opt, pname_opt) {
                    cls.fields.push(Field {
                        name: pname,
                        offset: 0,
                        field_type: Type::U32,
                        access_flags: AccessFlags::STATIC,
                        is_external: false,
                        initial_value: Some(FieldValue::ModuleRequestPhase(ph)),
                        annotations: Annotations::default(),
                    });
                }
            }
        }
    }

    // Synthesize standalone `_ESModuleRecord` if `module` carries top-level ES
    // module declarations and `out` has no existing `FieldValue::ModuleData`.
    let has_existing_mod_record = out.classes.values().any(|c| {
        c.fields
            .iter()
            .any(|f| matches!(f.initial_value, Some(FieldValue::ModuleData(_))))
    });
    if !has_existing_mod_record
        && (!module.imports.is_empty()
            || !module.exports.is_empty()
            || !module.module_requests.is_empty())
    {
        let (md, phase_opt) = build_module_data(
            &module.sym,
            &mut out.strings,
            &module.imports,
            &module.exports,
            &module.module_requests,
        )?;
        let rec_desc = out
            .strings
            .get_or_intern(abcd_file::ES_MODULE_RECORD_DESCRIPTOR);
        let field_name = out.strings.get_or_intern("moduleRecordIdx");
        let mut fields = vec![Field {
            name: field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(md)),
            annotations: Annotations::default(),
        }];
        if let Some(ph) = phase_opt {
            let ph_name = out
                .strings
                .get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD);
            fields.push(Field {
                name: ph_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleRequestPhase(ph)),
                annotations: Annotations::default(),
            });
        }
        out.classes
            .entry(rec_desc)
            .and_modify(|cls| cls.fields.extend(fields.clone()))
            .or_insert_with(|| Class {
                descriptor: rec_desc,
                name: rec_desc,
                access_flags: AccessFlags::PUBLIC,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: Vec::new(),
                fields,
                annotations: Annotations::default(),
            });
    }

    // Place every `FuncId` into `out.classes`, recording `(class_desc_sid, mi)`.
    let mut func_slots: Vec<(StringId, usize)> = Vec::with_capacity(module.functions.len());
    for (fi, func_data) in module.functions.iter().enumerate() {
        if let Some(&(desc_sid, mi)) = base_method_locs.get(fi) {
            func_slots.push((desc_sid, mi));
        } else {
            let desc_sid = match class_desc_sids.get(func_data.class_id.index()).copied() {
                Some(sid) => sid,
                None => out
                    .classes
                    .keys()
                    .next()
                    .copied()
                    .unwrap_or_else(|| ensure_global_class(&mut out)),
            };
            let cls_sid = if out.classes.contains_key(&desc_sid) {
                desc_sid
            } else {
                ensure_global_class(&mut out)
            };
            let owner_lang = out
                .classes
                .get(&cls_sid)
                .map_or(FileSourceLang::EcmaScript, |c| c.source_lang);
            let synth_method = build_method_shell(
                module,
                func_data,
                layouts[fi].as_ref(),
                owner_lang,
                &class_desc_sids,
                &mut out.strings,
            )?;
            let cls =
                out.classes
                    .get_mut(&cls_sid)
                    .ok_or_else(|| LowerError::UntraceableEntity {
                        func: FuncId::new(fi as u32),
                        kind: EntityKind::StringId,
                        raw: cls_sid.index() as u32,
                    })?;
            let mi = cls.methods.len();
            cls.methods.push(synth_method);
            func_slots.push((cls_sid, mi));
        }
    }

    // Ensure `_ESSlotNumberAnnotation` class record BEFORE computing final
    // `func_to_method_idx` / `field_to_field_idx` so no later `out.classes`
    // insertion can shift `BTreeMap` indices!
    let need_slot_ann_record = layouts.iter().flatten().any(|lay| lay.ic_size > 0);
    let slot_ann_sids = if need_slot_ann_record {
        Some(ensure_slot_number_ann_record(&mut out))
    } else if let Some(desc_sid) = out.strings.get(SLOT_NUMBER_ANN_DESC) {
        let elem_sid = out.strings.get_or_intern(SLOT_NUMBER_ELEM);
        Some((desc_sid, elem_sid))
    } else {
        None
    };

    // Compute exact `FuncId -> MethodIdx` and `(ClassId, FieldId) -> FieldIdx`
    // over `out.classes` (`BTreeMap` order) and remap any pre-existing
    // `MethodIdx` / `FieldIdx` handles (including `param_annotations`) if
    // synthesized classes, fields, or methods shifted dense indices.
    let func_to_method_idx = compute_func_method_indices(&out.classes, &func_slots);
    let field_to_field_idx = compute_field_indices(&out.classes, &field_slots);
    remap_existing_method_indices(&mut out, base_method_locs.len(), &func_to_method_idx);
    remap_existing_field_indices(&mut out, &base_field_locs);

    let mut bodies: Vec<Option<MethodBody>> = Vec::with_capacity(layouts.len());
    let mut resolved_scope_names: Vec<(StringId, usize, LiteralArrayIdx)> =
        Vec::with_capacity(synth_scope_name_slots.len());
    {
        let mut materializer = Materializer::new(module, &mut out, &func_to_method_idx);
        for (fi, layout_opt) in layouts.iter().enumerate() {
            let func_id = FuncId::new(fi as u32);
            match layout_opt {
                Some(layout) => {
                    let body =
                        materializer.build_method_body(func_id, layout, Some(&base_resolver))?;
                    bodies.push(Some(body));
                }
                None => bodies.push(None),
            }
        }
        for &(desc_sid, f_idx, sn_cid) in &synth_scope_name_slots {
            let sn_idx =
                materializer
                    .literal_array_idx(sn_cid)
                    .ok_or(LowerError::UntraceableEntity {
                        func: FuncId::new(0),
                        kind: EntityKind::LiteralarrayId,
                        raw: sn_cid.0,
                    })?;
            resolved_scope_names.push((desc_sid, f_idx, sn_idx));
        }
    }

    for (desc_sid, f_idx, sn_idx) in resolved_scope_names {
        if let Some(cls) = out.classes.get_mut(&desc_sid)
            && let Some(field) = cls.fields.get_mut(f_idx)
        {
            field.initial_value = Some(FieldValue::literal_array_ref(sn_idx));
        }
    }

    // Populate annotations on synthesized classes and synthesized fields.
    for (ci, cls_data) in module.classes.iter().enumerate() {
        let desc_sid = class_desc_sids[ci];
        if is_synth_class[ci] && !cls_data.annotations.is_empty() {
            let cls_anns = build_annotations(
                module,
                &cls_data.annotations,
                &class_desc_sids,
                &func_to_method_idx,
                &field_to_field_idx,
                &mut out.strings,
            )?;
            if let Some(cls) = out.classes.get_mut(&desc_sid) {
                cls.annotations = cls_anns;
            }
        }
        for (fi, fdata) in cls_data.fields.iter().enumerate() {
            if synth_field_flags[ci][fi] && !fdata.annotations.is_empty() {
                let f_anns = build_annotations(
                    module,
                    &fdata.annotations,
                    &class_desc_sids,
                    &func_to_method_idx,
                    &field_to_field_idx,
                    &mut out.strings,
                )?;
                let (f_desc, f_pos) = field_slots[ci][fi];
                if let Some(cls) = out.classes.get_mut(&f_desc)
                    && let Some(field) = cls.fields.get_mut(f_pos)
                {
                    field.annotations = f_anns;
                }
            }
        }
    }

    for (fi, body_opt) in bodies.into_iter().enumerate() {
        let func_data = &module.functions[fi];
        let (desc_sid, mi) = func_slots[fi];
        let is_synth_fn = fi >= base_method_locs.len();
        let synth_m_anns = if is_synth_fn && !func_data.annotations.is_empty() {
            Some(build_annotations(
                module,
                &func_data.annotations,
                &class_desc_sids,
                &func_to_method_idx,
                &field_to_field_idx,
                &mut out.strings,
            )?)
        } else {
            None
        };
        let debug_rebuilt = if layouts[fi].is_some() || is_synth_fn {
            Some(rebuild_method_debug(
                module,
                func_data,
                layouts[fi].as_ref(),
                &mut out.strings,
            ))
        } else {
            None
        };
        if let Some(cls) = out.classes.get_mut(&desc_sid)
            && let Some(m) = cls.methods.get_mut(mi)
        {
            if let Some(m_anns) = synth_m_anns {
                m.annotations = m_anns;
            }
            if let Some(dbg) = debug_rebuilt {
                m.debug = dbg;
            }
            if let Some(body) = body_opt {
                if let Some(ic) = body.ic_size {
                    sync_method_slot_annotation(
                        &mut m.annotations,
                        &out.strings,
                        slot_ann_sids,
                        ic,
                    );
                }
                m.body = Some(body);
            }
        }
    }

    Ok(out)
}

/// Standalone whole-module lowering with default [`LowerOptions`] (#30):
/// lowers `module` directly into a complete, encodable [`File`] at `version`
/// without requiring an original source `File`.
pub fn lower_module(module: &Module, version: Version) -> Result<File, LowerError> {
    lower_module_with_options(module, version, LowerOptions::default())
}

/// Standalone whole-module lowering with explicit [`LowerOptions`] (#30, `#50`,
/// `#57`).
pub fn lower_module_with_options(
    module: &Module,
    version: Version,
    options: LowerOptions,
) -> Result<File, LowerError> {
    let layouts = lower_all_layouts(module, options)?;

    let mut file = File {
        version,
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings: StringPool::new(),
        classes: BTreeMap::new(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };

    // 1. Intern class descriptors.
    let mut class_desc_sids: Vec<StringId> = Vec::with_capacity(module.classes.len());
    for cls_data in &module.classes {
        let desc_sid = intern_sym(&module.sym, &mut file.strings, cls_data.descriptor).ok_or(
            LowerError::UntraceableEntity {
                func: FuncId::new(0),
                kind: EntityKind::StringId,
                raw: cls_data.descriptor.0,
            },
        )?;
        class_desc_sids.push(desc_sid);
    }
    if class_desc_sids.is_empty() && !module.functions.is_empty() {
        class_desc_sids.push(ensure_global_class(&mut file));
    }

    // 2. Build skeleton classes and fields (tracking `(desc_sid, field_idx_in_cls)`
    //    for every IR `(ClassId, FieldId)` and `scope_names` slot).
    let mut field_slots: Vec<Vec<(StringId, usize)>> = Vec::with_capacity(module.classes.len());
    let mut scope_name_slots: Vec<(StringId, usize, ConstId)> = Vec::new();

    for (ci, cls_data) in module.classes.iter().enumerate() {
        let desc_sid = class_desc_sids[ci];
        let name_sid =
            intern_sym(&module.sym, &mut file.strings, cls_data.name).unwrap_or(desc_sid);
        let is_external = is_external_class(cls_data, module);
        let mut flags = modifiers_to_access_flags(cls_data.modifiers);
        if file.strings.as_str(desc_sid) == Some("L_GLOBAL;")
            && (!module.imports.is_empty()
                || !module.exports.is_empty()
                || !module.module_requests.is_empty())
        {
            flags |= AccessFlags::PUBLIC;
        }
        let super_class = cls_data
            .super_class
            .and_then(|sc| class_desc_sids.get(sc.index()).copied());
        let interfaces = cls_data
            .interfaces
            .iter()
            .filter_map(|ic| class_desc_sids.get(ic.index()).copied())
            .collect();
        let source_file = cls_data
            .source_file
            .and_then(|sf| intern_sym(&module.sym, &mut file.strings, sf));

        let base_field_idx = file.classes.get(&desc_sid).map_or(0, |c| c.fields.len());
        let mut fields = Vec::with_capacity(cls_data.fields.len());
        let mut cls_field_slots = Vec::with_capacity(cls_data.fields.len());
        for (fi, fdata) in cls_data.fields.iter().enumerate() {
            let f_sid = intern_sym(&module.sym, &mut file.strings, fdata.name).ok_or(
                LowerError::UntraceableEntity {
                    func: FuncId::new(0),
                    kind: EntityKind::StringId,
                    raw: fdata.name.0,
                },
            )?;
            fields.push(build_field_shell(
                module,
                fdata,
                f_sid,
                &class_desc_sids,
                &mut file.strings,
            ));
            cls_field_slots.push((desc_sid, base_field_idx + fi));
        }
        field_slots.push(cls_field_slots);

        if let Some(sn_cid) = cls_data.scope_names {
            let sn_name = file.strings.get_or_intern(abcd_file::SCOPE_NAMES_FIELD);
            let slot_idx = base_field_idx + fields.len();
            fields.push(Field {
                name: sn_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: None,
                annotations: Annotations::default(),
            });
            scope_name_slots.push((desc_sid, slot_idx, sn_cid));
        }
        if let Some(es_mod) = &cls_data.es_module {
            let (md, phase_opt) = build_module_data(
                &module.sym,
                &mut file.strings,
                &es_mod.imports,
                &es_mod.exports,
                &es_mod.module_requests,
            )?;
            let mr_name = file
                .strings
                .get_or_intern(abcd_file::MODULE_RECORD_IDX_FIELD);
            fields.push(Field {
                name: mr_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleData(md)),
                annotations: Annotations::default(),
            });
            if let Some(ph) = phase_opt {
                let pname = file
                    .strings
                    .get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD);
                fields.push(Field {
                    name: pname,
                    offset: 0,
                    field_type: Type::U32,
                    access_flags: AccessFlags::STATIC,
                    is_external: false,
                    initial_value: Some(FieldValue::ModuleRequestPhase(ph)),
                    annotations: Annotations::default(),
                });
            }
        }

        if let Some(existing) = file.classes.get_mut(&desc_sid) {
            existing.fields.extend(fields);
        } else {
            file.classes.insert(
                desc_sid,
                Class {
                    descriptor: desc_sid,
                    name: name_sid,
                    access_flags: flags,
                    source_lang: source_lang_to_file(cls_data.source_lang),
                    source_file,
                    is_external,
                    super_class,
                    interfaces,
                    methods: Vec::new(),
                    fields,
                    annotations: Annotations::default(),
                },
            );
        }
    }

    // 3. Top-level standalone ES module record (`Module.imports` / `exports` / `module_requests`).
    if !module.imports.is_empty()
        || !module.exports.is_empty()
        || !module.module_requests.is_empty()
    {
        let (md, phase_opt) = build_module_data(
            &module.sym,
            &mut file.strings,
            &module.imports,
            &module.exports,
            &module.module_requests,
        )?;
        let rec_desc = file
            .strings
            .get_or_intern(abcd_file::ES_MODULE_RECORD_DESCRIPTOR);
        let field_name = file.strings.get_or_intern("moduleRecordIdx");
        let mut fields = vec![Field {
            name: field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(md)),
            annotations: Annotations::default(),
        }];
        if let Some(ph) = phase_opt {
            let ph_name = file
                .strings
                .get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD);
            fields.push(Field {
                name: ph_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleRequestPhase(ph)),
                annotations: Annotations::default(),
            });
        }
        file.classes
            .entry(rec_desc)
            .and_modify(|cls| cls.fields.extend(fields.clone()))
            .or_insert_with(|| Class {
                descriptor: rec_desc,
                name: rec_desc,
                access_flags: AccessFlags::PUBLIC,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: Vec::new(),
                fields,
                annotations: Annotations::default(),
            });
    }

    // 4. Place method shells into `file.classes` so `FuncId -> MethodIdx` and
    //    `(ClassId, FieldId) -> FieldIdx` match `file.all_methods()` /
    //    `file.all_fields()` (`BTreeMap` order) with 100% precision.
    let mut func_slots: Vec<(StringId, usize)> = Vec::with_capacity(module.functions.len());
    for (fi, func_data) in module.functions.iter().enumerate() {
        let desc_sid = class_desc_sids
            .get(func_data.class_id.index())
            .copied()
            .ok_or(LowerError::UntraceableEntity {
                func: FuncId::new(fi as u32),
                kind: EntityKind::MethodId,
                raw: func_data.class_id.0,
            })?;
        let owner_lang = module
            .class(func_data.class_id)
            .map_or(FileSourceLang::EcmaScript, |c| {
                source_lang_to_file(c.source_lang)
            });
        let method = build_method_shell(
            module,
            func_data,
            layouts[fi].as_ref(),
            owner_lang,
            &class_desc_sids,
            &mut file.strings,
        )?;
        let cls = file
            .classes
            .get_mut(&desc_sid)
            .ok_or(LowerError::UntraceableEntity {
                func: FuncId::new(fi as u32),
                kind: EntityKind::MethodId,
                raw: func_data.class_id.0,
            })?;
        let mi = cls.methods.len();
        cls.methods.push(method);
        func_slots.push((desc_sid, mi));
    }

    let func_to_method_idx = compute_func_method_indices(&file.classes, &func_slots);
    let field_to_field_idx = compute_field_indices(&file.classes, &field_slots);

    // 5. Materialize method bodies and literal arrays (`scope_names`, initializers, annotations).
    let mut lowered_bodies: Vec<Option<MethodBody>> = Vec::with_capacity(module.functions.len());
    let mut resolved_scope_names: Vec<(StringId, usize, LiteralArrayIdx)> =
        Vec::with_capacity(scope_name_slots.len());
    {
        let mut materializer = Materializer::new(module, &mut file, &func_to_method_idx);
        for (fi, layout_opt) in layouts.iter().enumerate() {
            let func_id = FuncId::new(fi as u32);
            match layout_opt {
                Some(layout) => {
                    let body = materializer.build_method_body(func_id, layout, None)?;
                    lowered_bodies.push(Some(body));
                }
                None => lowered_bodies.push(None),
            }
        }
        for &(desc_sid, f_idx, sn_cid) in &scope_name_slots {
            let sn_idx =
                materializer
                    .literal_array_idx(sn_cid)
                    .ok_or(LowerError::UntraceableEntity {
                        func: FuncId::new(0),
                        kind: EntityKind::LiteralarrayId,
                        raw: sn_cid.0,
                    })?;
            resolved_scope_names.push((desc_sid, f_idx, sn_idx));
        }
    }

    for (desc_sid, f_idx, sn_idx) in resolved_scope_names {
        if let Some(cls) = file.classes.get_mut(&desc_sid)
            && let Some(field) = cls.fields.get_mut(f_idx)
        {
            field.initial_value = Some(FieldValue::literal_array_ref(sn_idx));
        }
    }

    // 6. Populate class, field, and method annotations + attach bodies & `SlotNumber`.
    for (ci, cls_data) in module.classes.iter().enumerate() {
        let desc_sid = class_desc_sids[ci];
        let cls_anns = build_annotations(
            module,
            &cls_data.annotations,
            &class_desc_sids,
            &func_to_method_idx,
            &field_to_field_idx,
            &mut file.strings,
        )?;
        if let Some(cls) = file.classes.get_mut(&desc_sid) {
            cls.annotations = cls_anns;
        }
        for (fi, fdata) in cls_data.fields.iter().enumerate() {
            let f_anns = build_annotations(
                module,
                &fdata.annotations,
                &class_desc_sids,
                &func_to_method_idx,
                &field_to_field_idx,
                &mut file.strings,
            )?;
            let (f_desc, f_pos) = field_slots[ci][fi];
            if let Some(cls) = file.classes.get_mut(&f_desc)
                && let Some(field) = cls.fields.get_mut(f_pos)
            {
                field.annotations = f_anns;
            }
        }
    }

    let need_slot_ann = lowered_bodies
        .iter()
        .flatten()
        .any(|b| b.ic_size.unwrap_or(0) > 0);
    let slot_ann_sids = if need_slot_ann {
        Some(ensure_slot_number_ann_record(&mut file))
    } else if let Some(desc_sid) = file.strings.get(SLOT_NUMBER_ANN_DESC) {
        let elem_sid = file.strings.get_or_intern(SLOT_NUMBER_ELEM);
        Some((desc_sid, elem_sid))
    } else {
        None
    };

    for (fi, func_data) in module.functions.iter().enumerate() {
        let m_anns = build_annotations(
            module,
            &func_data.annotations,
            &class_desc_sids,
            &func_to_method_idx,
            &field_to_field_idx,
            &mut file.strings,
        )?;
        let (desc_sid, mi) = func_slots[fi];
        if let Some(cls) = file.classes.get_mut(&desc_sid)
            && let Some(method) = cls.methods.get_mut(mi)
        {
            method.annotations = m_anns;
            let body = lowered_bodies[fi].take();
            if let Some(b) = &body
                && let Some(ic) = b.ic_size
            {
                sync_method_slot_annotation(
                    &mut method.annotations,
                    &file.strings,
                    slot_ann_sids,
                    ic,
                );
            }
            method.body = body;
        }
    }

    Ok(file)
}

/// Reconstruct [`MethodDebugInfo`] for `func_data` from its IR [`abcd_ir::DebugData`]
/// and post-layout instruction PCs (`#57` `R3-H8`).
///
/// - Returns `None` when `func_data.debug` is `None`.
/// - Maps `DebugData::line_table` and `DebugData::column_table` `InstId`s
///   through `LayoutResult::inst_pcs` (falling back to `Inst.loc` when the
///   explicit table is empty), sorting by bytecode index and deduplicating
///   same-PC and consecutive-identical-line/column entries.
/// - Clears `local_vars` (`Vec::new()`) because register numbers and scope PCs
///   are invalidated by SSA + register allocation + block layout.
pub fn rebuild_method_debug(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    layout: Option<&LayoutResult>,
    strings: &mut StringPool,
) -> Option<MethodDebugInfo> {
    let dbg = func_data.debug.as_ref()?;

    let source_file = dbg
        .source_file
        .and_then(|sf| intern_sym(&module.sym, strings, sf));
    let source_code = dbg
        .source_code
        .as_deref()
        .filter(|s| !s.is_empty())
        .map(|s| strings.get_or_intern(s));

    let mut line_table: Vec<LineEntry> = Vec::new();
    let mut column_table: Vec<ColumnEntry> = Vec::new();

    if let Some(lay) = layout {
        if !dbg.line_table.is_empty() {
            for e in &dbg.line_table {
                if let Some(&pc) = lay.inst_pcs.get(&e.inst) {
                    line_table.push(LineEntry {
                        index: pc,
                        line: e.line,
                    });
                }
            }
        }
        if line_table.is_empty() {
            for &bb in &func_data.blocks {
                if let Some(blk) = module.block(bb) {
                    for &iid in &blk.insts {
                        if let (Some(loc), Some(&pc)) =
                            (module.inst(iid).and_then(|i| i.loc), lay.inst_pcs.get(&iid))
                        {
                            line_table.push(LineEntry {
                                index: pc,
                                line: loc.line,
                            });
                        }
                    }
                }
            }
        }
        line_table.sort_by_key(|e| (e.index, e.line));
        line_table.dedup_by_key(|e| e.index);
        line_table.dedup_by(|b, a| a.line == b.line);

        if !dbg.column_table.is_empty() {
            for e in &dbg.column_table {
                if let Some(&pc) = lay.inst_pcs.get(&e.inst) {
                    column_table.push(ColumnEntry {
                        index: pc,
                        column: e.column,
                    });
                }
            }
        } else {
            for &bb in &func_data.blocks {
                if let Some(blk) = module.block(bb) {
                    for &iid in &blk.insts {
                        if let (Some(col), Some(&pc)) = (
                            module.inst(iid).and_then(|i| i.loc).and_then(|l| l.column),
                            lay.inst_pcs.get(&iid),
                        ) {
                            column_table.push(ColumnEntry {
                                index: pc,
                                column: col,
                            });
                        }
                    }
                }
            }
        }
        column_table.sort_by_key(|e| (e.index, e.column));
        column_table.dedup_by_key(|e| e.index);
        column_table.dedup_by(|b, a| a.column == b.column);
    }

    let params = if dbg.param_names.is_empty() {
        Vec::new()
    } else {
        let empty_sig = strings.get_or_intern("");
        dbg.param_names
            .iter()
            .filter_map(|&p| {
                let name = intern_sym(&module.sym, strings, p)?;
                Some(ParamInfo {
                    name,
                    signature: empty_sig,
                })
            })
            .collect()
    };

    Some(MethodDebugInfo {
        source_file,
        source_code,
        line_table,
        column_table,
        local_vars: Vec::new(),
        params,
    })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn lower_all_layouts(
    module: &Module,
    options: LowerOptions,
) -> Result<Vec<Option<LayoutResult>>, LowerError> {
    let results: Vec<Result<Option<LayoutResult>, LowerError>> = (0..module.functions.len())
        .into_par_iter()
        .map(|i| {
            let func_id = FuncId::new(i as u32);
            let Some(func) = module.func(func_id) else {
                return Ok(None);
            };
            if func.blocks.is_empty() {
                return Ok(None);
            }
            lower_function_with_options(module, func_id, options).map(Some)
        })
        .collect();
    results.into_iter().collect()
}

fn compute_func_method_indices(
    classes: &BTreeMap<StringId, Class>,
    func_slots: &[(StringId, usize)],
) -> Vec<MethodIdx> {
    let mut class_base: HashMap<StringId, u32> = HashMap::with_capacity(classes.len());
    let mut running = 0u32;
    for (&sid, cls) in classes {
        class_base.insert(sid, running);
        running += cls.methods.len() as u32;
    }
    func_slots
        .iter()
        .map(|&(sid, mi)| MethodIdx(class_base[&sid] + mi as u32))
        .collect()
}

fn compute_field_indices(
    classes: &BTreeMap<StringId, Class>,
    field_slots: &[Vec<(StringId, usize)>],
) -> Vec<Vec<FieldIdx>> {
    let mut class_base: HashMap<StringId, u32> = HashMap::with_capacity(classes.len());
    let mut running = 0u32;
    for (&sid, cls) in classes {
        class_base.insert(sid, running);
        running += cls.fields.len() as u32;
    }
    field_slots
        .iter()
        .map(|slots| {
            slots
                .iter()
                .map(|&(sid, fi)| FieldIdx(class_base[&sid] + fi as u32))
                .collect()
        })
        .collect()
}

fn remap_existing_method_indices(
    file: &mut File,
    base_method_count: usize,
    func_to_method_idx: &[MethodIdx],
) {
    let any_shifted = (0..base_method_count)
        .any(|old| func_to_method_idx.get(old).copied() != Some(MethodIdx(old as u32)));
    if !any_shifted {
        return;
    }
    let remap = |midx: &mut MethodIdx| {
        if let Some(&new_midx) = func_to_method_idx.get(midx.index()) {
            *midx = new_midx;
        }
    };
    for la in &mut file.literal_arrays {
        for v in &mut la.values {
            if let Some(midx) = v.method_idx_mut() {
                remap(midx);
            }
        }
    }
    for cls in file.classes.values_mut() {
        remap_annotations_methods(&mut cls.annotations, &remap);
        for f in &mut cls.fields {
            remap_annotations_methods(&mut f.annotations, &remap);
        }
        for m in &mut cls.methods {
            remap_annotations_methods(&mut m.annotations, &remap);
            remap_param_annotations_methods(&mut m.param_annotations, &remap);
            if let Some(body) = &mut m.body {
                for entity in body.entities.values_mut() {
                    if let EntityRef::Method(midx) = entity {
                        remap(midx);
                    }
                }
            }
        }
    }
}

fn remap_existing_field_indices(file: &mut File, base_field_locs: &[(StringId, usize)]) {
    if base_field_locs.is_empty() {
        return;
    }
    let mut class_base: HashMap<StringId, u32> = HashMap::with_capacity(file.classes.len());
    let mut running = 0u32;
    for (&sid, cls) in &file.classes {
        class_base.insert(sid, running);
        running += cls.fields.len() as u32;
    }
    let new_indices: Vec<FieldIdx> = base_field_locs
        .iter()
        .map(|&(sid, fi)| FieldIdx(class_base[&sid] + fi as u32))
        .collect();
    let any_shifted = new_indices
        .iter()
        .enumerate()
        .any(|(old, &new_fidx)| new_fidx != FieldIdx(old as u32));
    if !any_shifted {
        return;
    }
    let remap_f = |fidx: &mut FieldIdx| {
        if let Some(&new_fidx) = new_indices.get(fidx.index()) {
            *fidx = new_fidx;
        }
    };
    for cls in file.classes.values_mut() {
        remap_annotations_fields(&mut cls.annotations, &remap_f);
        for f in &mut cls.fields {
            remap_annotations_fields(&mut f.annotations, &remap_f);
        }
        for m in &mut cls.methods {
            remap_annotations_fields(&mut m.annotations, &remap_f);
            for bucket in [
                &mut m.param_annotations.compile_time,
                &mut m.param_annotations.runtime,
            ] {
                for param_anns in bucket {
                    for ann in param_anns {
                        remap_ann_slice_fields(&mut ann.elements, &remap_f);
                    }
                }
            }
        }
    }
}

fn remap_param_annotations_methods(pa: &mut ParamAnnotations, remap: &impl Fn(&mut MethodIdx)) {
    for bucket in [&mut pa.compile_time, &mut pa.runtime] {
        for param_anns in bucket {
            for ann in param_anns {
                remap_ann_slice(&mut ann.elements, remap);
            }
        }
    }
}

fn remap_annotations_fields(anns: &mut Annotations, remap: &impl Fn(&mut FieldIdx)) {
    for bucket in [
        &mut anns.compile_time,
        &mut anns.runtime,
        &mut anns.compile_time_type,
        &mut anns.runtime_type,
    ] {
        for ann in bucket {
            remap_ann_slice_fields(&mut ann.elements, remap);
        }
    }
}

fn remap_ann_slice_fields(elems: &mut [AnnotationElem], remap: &impl Fn(&mut FieldIdx)) {
    let mut stack: Vec<&mut AnnotationValue> = elems.iter_mut().map(|e| &mut e.value).collect();
    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::Enum {
                field: Some(fidx), ..
            } => remap(fidx),
            AnnotationValue::MethodHandle(abcd_file::ResolvedMethodHandle {
                target_field: Some(fidx),
                ..
            }) => remap(fidx),
            AnnotationValue::Annotation(nested) => {
                stack.extend(nested.elements.iter_mut().map(|e| &mut e.value));
            }
            AnnotationValue::Array { values, .. } => {
                stack.extend(values.iter_mut());
            }
            _ => {}
        }
    }
}

fn remap_annotations_methods(anns: &mut Annotations, remap: &impl Fn(&mut MethodIdx)) {
    for bucket in [
        &mut anns.compile_time,
        &mut anns.runtime,
        &mut anns.compile_time_type,
        &mut anns.runtime_type,
    ] {
        for ann in bucket {
            remap_ann_slice(&mut ann.elements, remap);
        }
    }
}

fn remap_ann_slice(elems: &mut [AnnotationElem], remap: &impl Fn(&mut MethodIdx)) {
    let mut stack: Vec<&mut AnnotationValue> = elems.iter_mut().map(|e| &mut e.value).collect();
    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::Method {
                method: Some(midx), ..
            } => remap(midx),
            AnnotationValue::MethodHandle(abcd_file::ResolvedMethodHandle {
                target_method: Some(midx),
                ..
            }) => remap(midx),
            AnnotationValue::LiteralArray(vals) => {
                for v in vals {
                    if let Some(midx) = v.method_idx_mut() {
                        remap(midx);
                    }
                }
            }
            AnnotationValue::Annotation(nested) => {
                stack.extend(nested.elements.iter_mut().map(|e| &mut e.value));
            }
            AnnotationValue::Array { values, .. } => {
                stack.extend(values.iter_mut());
            }
            _ => {}
        }
    }
}

fn intern_sym(
    sym_table: &abcd_ir::SymbolTable,
    pool: &mut StringPool,
    sym: Sym,
) -> Option<StringId> {
    if let Some(raw) = sym_table.raw_mutf8(sym) {
        let lossy = sym_table.resolve(sym)?;
        return Some(pool.intern_lossy_raw(lossy, raw));
    }
    let s = sym_table.as_str(sym)?;
    Some(pool.get_or_intern(s))
}

fn ensure_global_class(file: &mut File) -> StringId {
    let desc = file.strings.get_or_intern("L_GLOBAL;");
    file.classes.entry(desc).or_insert_with(|| Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: Annotations::default(),
    });
    desc
}

fn ensure_slot_number_ann_record(file: &mut File) -> (StringId, StringId) {
    let desc = file.strings.get_or_intern(SLOT_NUMBER_ANN_DESC);
    let elem = file.strings.get_or_intern(SLOT_NUMBER_ELEM);
    file.classes.entry(desc).or_insert_with(|| Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC | AccessFlags::ANNOTATION,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: true,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations: Annotations::default(),
    });
    (desc, elem)
}

fn sync_method_slot_annotation(
    anns: &mut Annotations,
    strings: &StringPool,
    slot_ann_sids: Option<(StringId, StringId)>,
    ic_size: u32,
) {
    let mut found_any = false;
    for bucket in [
        &mut anns.compile_time,
        &mut anns.runtime,
        &mut anns.compile_time_type,
        &mut anns.runtime_type,
    ] {
        for ann in bucket {
            let is_slot_ann = slot_ann_sids.is_some_and(|(desc, _)| ann.class_descriptor == desc)
                || strings.as_str(ann.class_descriptor) == Some(SLOT_NUMBER_ANN_DESC);
            if !is_slot_ann {
                continue;
            }
            found_any = true;
            let mut updated_elem = false;
            for el in &mut ann.elements {
                let is_slot_elem = slot_ann_sids.is_some_and(|(_, ename)| el.name == ename)
                    || strings.as_str(el.name) == Some(SLOT_NUMBER_ELEM);
                if is_slot_elem {
                    el.value = AnnotationValue::U32(ic_size);
                    updated_elem = true;
                }
            }
            if !updated_elem && let Some((_, elem_name)) = slot_ann_sids {
                ann.elements.push(AnnotationElem {
                    name: elem_name,
                    value: AnnotationValue::U32(ic_size),
                });
            }
        }
    }
    if !found_any
        && ic_size > 0
        && let Some((ann_desc, elem_name)) = slot_ann_sids
    {
        anns.compile_time.push(Annotation {
            class_descriptor: ann_desc,
            elements: vec![AnnotationElem {
                name: elem_name,
                value: AnnotationValue::U32(ic_size),
            }],
        });
    }
}

#[derive(Clone, Copy)]
enum MatNestedWrap {
    Array,
    BufferRef { wrapper_cid: ConstId },
}

fn wrap_literal_array_value(wrap: MatNestedWrap, idx: LiteralArrayIdx) -> LiteralValue {
    match wrap {
        MatNestedWrap::Array => LiteralValue::LiteralArray(idx),
        MatNestedWrap::BufferRef { .. } => LiteralValue::LiteralBufferIndex(idx),
    }
}

struct Materializer<'m, 'f> {
    module: &'m Module,
    file: &'f mut File,
    func_to_method_idx: &'m [MethodIdx],
    synth_shapes: HashMap<ConstId, LiteralArrayIdx>,
}

impl<'m, 'f> Materializer<'m, 'f> {
    fn new(module: &'m Module, file: &'f mut File, func_to_method_idx: &'m [MethodIdx]) -> Self {
        Self {
            module,
            file,
            func_to_method_idx,
            synth_shapes: HashMap::new(),
        }
    }

    fn build_method_body(
        &mut self,
        func_id: FuncId,
        result: &LayoutResult,
        base_resolver: Option<&EntityResolver<'_>>,
    ) -> Result<MethodBody, LowerError> {
        let param_count = self
            .module
            .func(func_id)
            .map(|f| f.params.len())
            .unwrap_or_default();

        let (bytecodes, entities) =
            relocate_and_compact_entities(func_id, &result.bytecodes, |kind, raw| match kind {
                EntityKind::StringId => {
                    let sym = Sym::new(raw);
                    if let Some(r) = base_resolver
                        && let Some(eref) = r.string_ref(sym)
                    {
                        Ok(eref)
                    } else {
                        self.string_ref(sym).ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                    }
                }
                EntityKind::MethodId => {
                    self.method_ref(FuncId::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
                EntityKind::LiteralarrayId => {
                    let cid = ConstId::new(raw);
                    if let Some(r) = base_resolver
                        && let Some(eref) = r.literal_array_ref(cid)
                    {
                        Ok(eref)
                    } else {
                        self.literal_array_idx(cid)
                            .map(EntityRef::LiteralArray)
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind,
                                raw,
                            })
                    }
                }
            })?;

        let try_blocks = self.materialize_try_blocks(&result.try_blocks, func_id)?;

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            bytecodes,
            entities,
            try_blocks,
            ic_size: Some(result.ic_size),
        })
    }

    fn materialize_try_blocks(
        &mut self,
        lowered: &[LoweredTryBlock],
        func_id: FuncId,
    ) -> Result<Vec<TryBlock>, LowerError> {
        let mut out = Vec::with_capacity(lowered.len());
        for tb in lowered {
            let mut catches = Vec::with_capacity(tb.catches.len());
            for c in &tb.catches {
                let type_class = match c.type_class {
                    None => None,
                    Some(cid) => {
                        let cls = self
                            .module
                            .class(cid)
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind: EntityKind::StringId,
                                raw: cid.0,
                            })?;
                        let sid =
                            intern_sym(&self.module.sym, &mut self.file.strings, cls.descriptor)
                                .ok_or(LowerError::UntraceableEntity {
                                    func: func_id,
                                    kind: EntityKind::StringId,
                                    raw: cls.descriptor.0,
                                })?;
                        Some(sid)
                    }
                };
                catches.push(CatchBlock {
                    type_class,
                    handler: c.handler,
                    len: c.len,
                });
            }
            out.push(TryBlock {
                start: tb.start,
                len: tb.len,
                catches,
            });
        }
        Ok(out)
    }

    fn string_ref(&mut self, sym: Sym) -> Option<EntityRef> {
        let sid = intern_sym(&self.module.sym, &mut self.file.strings, sym)?;
        Some(EntityRef::string(sid))
    }

    fn method_idx(&self, func: FuncId) -> Option<MethodIdx> {
        self.func_to_method_idx.get(func.index()).copied()
    }

    fn method_ref(&self, func: FuncId) -> Option<EntityRef> {
        self.method_idx(func).map(EntityRef::Method)
    }

    fn literal_array_idx(&mut self, shape: ConstId) -> Option<LiteralArrayIdx> {
        if let Some(&idx) = self.synth_shapes.get(&shape) {
            return Some(idx);
        }
        self.materialize_shape_tree(shape)
    }

    fn materialize_shape_tree(&mut self, root_cid: ConstId) -> Option<LiteralArrayIdx> {
        let module = self.module;
        let mut active: HashSet<ConstId> = HashSet::new();
        let mut actual_root = root_cid;
        let root_const = loop {
            if !active.insert(actual_root) {
                return None;
            }
            match module.consts.get(actual_root)? {
                Const::LiteralBufferRef(inner) => actual_root = *inner,
                other => break other,
            }
        };
        if let Some(&existing) = self.synth_shapes.get(&actual_root) {
            self.synth_shapes.insert(root_cid, existing);
            return Some(existing);
        }
        if let Const::TypedArrayLiteral { tag, items } = root_const {
            let lit_val = self.materialize_typed_array(*tag, items)?;
            let idx = LiteralArrayIdx(self.file.literal_arrays.len() as u32);
            self.file
                .literal_arrays
                .push(LiteralArray::new(vec![lit_val]));
            self.synth_shapes.insert(actual_root, idx);
            self.synth_shapes.insert(root_cid, idx);
            return Some(idx);
        }
        let (root_cursor, root_cap) = ShapeCursor::from_const(root_const)?;
        let mut stack = vec![ShapeFrame {
            cid: actual_root,
            parent_wrap: None,
            cursor: root_cursor,
            values: Vec::with_capacity(root_cap),
        }];

        'outer: while let Some(mut frame) = stack.pop() {
            while let Some(child_cid) = frame.cursor.next_id() {
                let elem = module.consts.get(child_cid)?;
                if let Const::TypedArrayLiteral { tag, items } = elem {
                    frame
                        .values
                        .push(self.materialize_typed_array(*tag, items)?);
                    continue;
                }
                let nested = match elem {
                    Const::ArrayLiteral(_) | Const::ObjectLiteral { .. } => {
                        Some((child_cid, elem, MatNestedWrap::Array))
                    }
                    Const::LiteralBufferRef(inner_cid) => {
                        if active.contains(&child_cid) {
                            return None;
                        }
                        let inner_elem = module.consts.get(*inner_cid)?;
                        if let Const::TypedArrayLiteral { tag, items } = inner_elem {
                            let child_idx = if let Some(&cached) = self.synth_shapes.get(inner_cid)
                            {
                                cached
                            } else {
                                let lit_val = self.materialize_typed_array(*tag, items)?;
                                let idx = LiteralArrayIdx(self.file.literal_arrays.len() as u32);
                                self.file
                                    .literal_arrays
                                    .push(LiteralArray::new(vec![lit_val]));
                                self.synth_shapes.insert(*inner_cid, idx);
                                idx
                            };
                            frame
                                .values
                                .push(LiteralValue::LiteralBufferIndex(child_idx));
                            continue;
                        }
                        if !matches!(
                            inner_elem,
                            Const::ArrayLiteral(_) | Const::ObjectLiteral { .. }
                        ) {
                            return None;
                        }
                        Some((
                            *inner_cid,
                            inner_elem,
                            MatNestedWrap::BufferRef {
                                wrapper_cid: child_cid,
                            },
                        ))
                    }
                    _ => None,
                };

                if let Some((target_cid, target_elem, wrap)) = nested {
                    if active.contains(&target_cid) {
                        return None;
                    }
                    if let Some(&child_idx) = self.synth_shapes.get(&target_cid) {
                        frame.values.push(wrap_literal_array_value(wrap, child_idx));
                        continue;
                    }
                    let (child_cursor, child_cap) = ShapeCursor::from_const(target_elem)?;
                    if let MatNestedWrap::BufferRef { wrapper_cid } = wrap {
                        active.insert(wrapper_cid);
                    }
                    active.insert(target_cid);
                    stack.push(frame);
                    stack.push(ShapeFrame {
                        cid: target_cid,
                        parent_wrap: Some(wrap),
                        cursor: child_cursor,
                        values: Vec::with_capacity(child_cap),
                    });
                    continue 'outer;
                }
                frame.values.push(self.materialize_scalar_elem(elem)?);
            }

            active.remove(&frame.cid);
            if let Some(MatNestedWrap::BufferRef { wrapper_cid }) = frame.parent_wrap {
                active.remove(&wrapper_cid);
            }
            let idx = LiteralArrayIdx(self.file.literal_arrays.len() as u32);
            self.file
                .literal_arrays
                .push(LiteralArray::new(frame.values));
            self.synth_shapes.insert(frame.cid, idx);
            if let Some(parent) = stack.last_mut() {
                let wrap = frame.parent_wrap.unwrap_or(MatNestedWrap::Array);
                parent.values.push(wrap_literal_array_value(wrap, idx));
            } else {
                self.synth_shapes.insert(root_cid, idx);
                return Some(idx);
            }
        }
        None
    }

    fn materialize_scalar_elem(&mut self, c: &Const) -> Option<LiteralValue> {
        Some(match c {
            Const::Bool(b) => LiteralValue::Bool(*b),
            Const::Int8(n) => LiteralValue::Integer8(*n),
            Const::Int32(n) => LiteralValue::Integer(*n),
            Const::Float32(bits) => LiteralValue::Float(f32::from_bits(*bits)),
            Const::Number(bits) => LiteralValue::Double(f64::from_bits(*bits)),
            Const::Accessor(n) => LiteralValue::Accessor(*n),
            Const::MethodAffiliate(n) => LiteralValue::MethodAffiliate(*n),
            Const::BuiltinTypeIndex(n) => LiteralValue::BuiltinTypeIndex(*n),
            Const::LitNull(n) => LiteralValue::NullValue(*n),
            Const::Null | Const::Undefined | Const::Hole => LiteralValue::NullValue(0),
            Const::String(sym) | Const::BigInt(sym) => {
                let sid = intern_sym(&self.module.sym, &mut self.file.strings, *sym)?;
                LiteralValue::String(sid)
            }
            Const::EtsImplements(sym) => {
                let sid = intern_sym(&self.module.sym, &mut self.file.strings, *sym)?;
                LiteralValue::EtsImplements(sid)
            }
            Const::MethodRef { func, kind } => {
                let midx = self.method_idx(*func)?;
                match kind {
                    LitMethodKind::Method => LiteralValue::Method(midx),
                    LitMethodKind::GeneratorMethod => LiteralValue::GeneratorMethod(midx),
                    LitMethodKind::AsyncGeneratorMethod => LiteralValue::AsyncGeneratorMethod(midx),
                    LitMethodKind::Getter => LiteralValue::Getter(midx),
                    LitMethodKind::Setter => LiteralValue::Setter(midx),
                }
            }
            Const::Int64(_)
            | Const::UInt64(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_) => return None,
        })
    }

    fn materialize_typed_array(
        &mut self,
        tag: TypedArrayTag,
        items: &[ConstId],
    ) -> Option<LiteralValue> {
        let module = self.module;
        match tag {
            TypedArrayTag::U1 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let b = match module.consts.get(cid)? {
                        Const::Bool(b) => *b,
                        Const::Int8(n) if *n <= 1 => *n != 0,
                        Const::Int32(n) if *n <= 1 => *n != 0,
                        _ => return None,
                    };
                    out.push(b);
                }
                Some(LiteralValue::ArrayU1(out))
            }
            TypedArrayTag::U8 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => *n,
                        Const::Int32(n) => u8::try_from(*n).ok()?,
                        Const::UInt64(n) => u8::try_from(*n).ok()?,
                        Const::Int64(n) => u8::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU8(out))
            }
            TypedArrayTag::I8 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => *n as i8,
                        Const::Int32(n) => i8::try_from(*n as i32).ok()?,
                        Const::Int64(n) => i8::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI8(out))
            }
            TypedArrayTag::U16 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => u16::from(*n),
                        Const::Int32(n) => u16::try_from(*n).ok()?,
                        Const::UInt64(n) => u16::try_from(*n).ok()?,
                        Const::Int64(n) => u16::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU16(out))
            }
            TypedArrayTag::I16 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => i16::from(*n as i8),
                        Const::Int32(n) => i16::try_from(*n as i32).ok()?,
                        Const::Int64(n) => i16::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI16(out))
            }
            TypedArrayTag::U32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => u32::from(*n),
                        Const::Int32(n) => *n,
                        Const::UInt64(n) => u32::try_from(*n).ok()?,
                        Const::Int64(n) => u32::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU32(out))
            }
            TypedArrayTag::I32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => i32::from(*n as i8),
                        Const::Int32(n) => *n as i32,
                        Const::Int64(n) => i32::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI32(out))
            }
            TypedArrayTag::U64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::UInt64(n) => *n,
                        Const::Int64(n) => u64::try_from(*n).ok()?,
                        Const::Int32(n) => u64::from(*n),
                        Const::Int8(n) => u64::from(*n),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU64(out))
            }
            TypedArrayTag::I64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int64(n) => *n,
                        Const::UInt64(n) => i64::try_from(*n).ok()?,
                        Const::Int32(n) => i64::from(*n as i32),
                        Const::Int8(n) => i64::from(*n as i8),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI64(out))
            }
            TypedArrayTag::F32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Float32(b) => f32::from_bits(*b),
                        Const::Number(b) => f64::from_bits(*b) as f32,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayF32(out))
            }
            TypedArrayTag::F64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Number(b) => f64::from_bits(*b),
                        Const::Float32(b) => f64::from(f32::from_bits(*b)),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayF64(out))
            }
            TypedArrayTag::String => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let Const::String(sym) = module.consts.get(cid)? else {
                        return None;
                    };
                    let sid = intern_sym(&module.sym, &mut self.file.strings, *sym)?;
                    out.push(sid);
                }
                Some(LiteralValue::ArrayString(out))
            }
        }
    }
}

enum ShapeCursor<'t> {
    Array {
        items: &'t [ConstId],
        next: usize,
    },
    Object {
        keys: &'t [ConstId],
        values: &'t [ConstId],
        next: usize,
    },
}

impl<'t> ShapeCursor<'t> {
    fn from_const(tree: &'t Const) -> Option<(Self, usize)> {
        match tree {
            Const::ArrayLiteral(items) => Some((Self::Array { items, next: 0 }, items.len())),
            Const::ObjectLiteral { keys, values } => {
                if keys.len() != values.len() {
                    return None;
                }
                Some((
                    Self::Object {
                        keys,
                        values,
                        next: 0,
                    },
                    keys.len() * 2,
                ))
            }
            _ => None,
        }
    }

    fn next_id(&mut self) -> Option<ConstId> {
        match self {
            Self::Array { items, next } => {
                let id = *items.get(*next)?;
                *next += 1;
                Some(id)
            }
            Self::Object { keys, values, next } => {
                let pair_idx = *next / 2;
                let id = if *next % 2 == 0 {
                    *keys.get(pair_idx)?
                } else {
                    *values.get(pair_idx)?
                };
                *next += 1;
                Some(id)
            }
        }
    }
}

struct ShapeFrame<'t> {
    cid: ConstId,
    parent_wrap: Option<MatNestedWrap>,
    cursor: ShapeCursor<'t>,
    values: Vec<LiteralValue>,
}

fn modifiers_to_access_flags(m: Modifiers) -> AccessFlags {
    let mut out = AccessFlags::empty();
    if m.contains(Modifiers::PUBLIC) {
        out |= AccessFlags::PUBLIC;
    }
    if m.contains(Modifiers::PRIVATE) {
        out |= AccessFlags::PRIVATE;
    }
    if m.contains(Modifiers::PROTECTED) {
        out |= AccessFlags::PROTECTED;
    }
    if m.contains(Modifiers::STATIC) {
        out |= AccessFlags::STATIC;
    }
    if m.contains(Modifiers::FINAL) {
        out |= AccessFlags::FINAL;
    }
    if m.contains(Modifiers::ABSTRACT) {
        out |= AccessFlags::ABSTRACT;
    }
    if m.contains(Modifiers::INTERFACE) {
        out |= AccessFlags::INTERFACE;
    }
    if m.contains(Modifiers::ENUM) {
        out |= AccessFlags::ENUM;
    }
    if m.contains(Modifiers::ANNOTATION) {
        out |= AccessFlags::ANNOTATION;
    }
    out
}

fn source_lang_to_file(lang: IrSourceLang) -> FileSourceLang {
    match lang {
        IrSourceLang::EcmaScript => FileSourceLang::EcmaScript,
        IrSourceLang::TypeScript => FileSourceLang::TypeScript,
        IrSourceLang::ArkTS => FileSourceLang::ArkTs,
    }
}

fn function_kind_to_file(kind: IrFunctionKind) -> FileFunctionKind {
    match kind {
        IrFunctionKind::Function | IrFunctionKind::Constructor => FileFunctionKind::Function,
        IrFunctionKind::Getter | IrFunctionKind::Setter => FileFunctionKind::Function,
        IrFunctionKind::Generator => FileFunctionKind::GeneratorFunction,
        IrFunctionKind::Async => FileFunctionKind::AsyncFunction,
        IrFunctionKind::AsyncGenerator => FileFunctionKind::AsyncGeneratorFunction,
        IrFunctionKind::Arrow => FileFunctionKind::NcFunction,
        IrFunctionKind::AsyncArrow => FileFunctionKind::AsyncNcFunction,
    }
}

fn method_access_flags(func_data: &abcd_ir::FunctionData) -> AccessFlags {
    let mut flags = modifiers_to_access_flags(func_data.modifiers);
    if flags.is_empty() && !func_data.is_external {
        flags = if func_data.kind == IrFunctionKind::Constructor {
            AccessFlags::PUBLIC
        } else {
            AccessFlags::PUBLIC | AccessFlags::STATIC
        };
    }
    if func_data.kind == IrFunctionKind::Constructor {
        flags |= AccessFlags::CONSTRUCTOR;
    }
    flags
}

fn ty_to_file(ty: &Ty, class_desc_sids: &[StringId]) -> Type {
    match ty {
        Ty::Static(StaticTy::U1) => Type::Bool,
        Ty::Static(StaticTy::I8) => Type::I8,
        Ty::Static(StaticTy::U8) => Type::U8,
        Ty::Static(StaticTy::I16) => Type::I16,
        Ty::Static(StaticTy::U16) => Type::U16,
        Ty::Static(StaticTy::I32) => Type::I32,
        Ty::Static(StaticTy::U32) => Type::U32,
        Ty::Static(StaticTy::I64) => Type::I64,
        Ty::Static(StaticTy::U64) => Type::U64,
        Ty::Static(StaticTy::F32) => Type::F32,
        Ty::Static(StaticTy::F64) => Type::F64,
        Ty::Static(StaticTy::Void) => Type::Void,
        Ty::Static(StaticTy::Reference(cid)) => class_desc_sids
            .get(cid.index())
            .copied()
            .map(Type::Reference)
            .unwrap_or(Type::Tagged),
        _ => Type::Tagged,
    }
}

fn is_external_class(cls: &ClassData, module: &Module) -> bool {
    let desc = module.sym.as_str(cls.descriptor).unwrap_or("");
    if desc == "L_GLOBAL;"
        || !cls.fields.is_empty()
        || cls.es_module.is_some()
        || cls.scope_names.is_some()
    {
        return false;
    }
    if cls.methods.is_empty() {
        return cls.modifiers == Modifiers::NONE && cls.annotations.is_empty();
    }
    cls.methods
        .iter()
        .all(|&fid| module.func(fid).is_some_and(|f| f.is_external))
}

fn build_method_shell(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    layout: Option<&LayoutResult>,
    source_lang: FileSourceLang,
    class_desc_sids: &[StringId],
    strings: &mut StringPool,
) -> Result<Method, LowerError> {
    let name =
        intern_sym(&module.sym, strings, func_data.name).ok_or(LowerError::UntraceableEntity {
            func: FuncId::new(0),
            kind: EntityKind::StringId,
            raw: func_data.name.0,
        })?;
    let flags = method_access_flags(func_data);
    let (return_type, arg_types) = match &func_data.sig {
        Some(sig) => {
            let ret = sig
                .return_ty
                .as_ref()
                .map(|t| ty_to_file(t, class_desc_sids));
            let mut args: Vec<Type> = sig
                .param_tys
                .iter()
                .map(|t| ty_to_file(t, class_desc_sids))
                .collect();
            while args.len() < func_data.params.len() {
                args.push(Type::Tagged);
            }
            (ret, args)
        }
        None => (
            Some(Type::Tagged),
            vec![Type::Tagged; func_data.params.len()],
        ),
    };
    let debug = rebuild_method_debug(module, func_data, layout, strings);

    Ok(Method {
        name,
        offset: 0,
        access_flags: flags,
        function_kind: function_kind_to_file(func_data.kind),
        source_lang,
        is_external: func_data.is_external,
        return_type,
        arg_types,
        body: None,
        annotations: Annotations::default(),
        param_annotations: ParamAnnotations::default(),
        debug,
    })
}

fn build_field_shell(
    module: &Module,
    fdata: &FieldData,
    name: StringId,
    class_desc_sids: &[StringId],
    strings: &mut StringPool,
) -> Field {
    let field_type = ty_to_file(&fdata.ty, class_desc_sids);
    let initial_value = match fdata.initial_value.and_then(|cid| module.consts.get(cid)) {
        Some(Const::Bool(b)) => Some(FieldValue::I32(i32::from(*b))),
        Some(Const::Int8(n)) => Some(FieldValue::I32(i32::from(*n))),
        Some(Const::Int32(n)) => Some(FieldValue::I32(*n as i32)),
        Some(Const::Float32(bits)) => Some(FieldValue::F32(f32::from_bits(*bits))),
        Some(Const::Int64(n)) => Some(FieldValue::I64(*n)),
        Some(Const::UInt64(n)) => Some(FieldValue::I64(*n as i64)),
        Some(Const::Number(bits)) => {
            let v = f64::from_bits(*bits);
            match field_type {
                Type::F32 => Some(FieldValue::F32(v as f32)),
                Type::F64 => Some(FieldValue::F64(v)),
                Type::I64 | Type::U64 => Some(FieldValue::I64(v as i64)),
                _ => Some(FieldValue::I32(v as i32)),
            }
        }
        Some(Const::String(sym)) => intern_sym(&module.sym, strings, *sym).map(|sid| {
            if module.sym.as_str(fdata.name) == Some(abcd_file::JSON_FILE_CONTENT_FIELD) {
                FieldValue::JsonFileContent {
                    source_offset: 0,
                    content: sid,
                }
            } else {
                FieldValue::String(sid)
            }
        }),
        _ => None,
    };
    Field {
        name,
        offset: 0,
        field_type,
        access_flags: modifiers_to_access_flags(fdata.modifiers),
        is_external: false,
        initial_value,
        annotations: Annotations::default(),
    }
}

fn build_annotations(
    module: &Module,
    anns: &[abcd_ir::Annotation],
    class_desc_sids: &[StringId],
    func_to_method_idx: &[MethodIdx],
    field_to_field_idx: &[Vec<FieldIdx>],
    strings: &mut StringPool,
) -> Result<Annotations, LowerError> {
    let mut compile_time = Vec::with_capacity(anns.len());
    for ann in anns {
        let Some(&class_descriptor) = class_desc_sids.get(ann.class.index()) else {
            continue;
        };
        let mut elements = Vec::with_capacity(ann.elements.len());
        for (ename, eval) in &ann.elements {
            let Some(name) = intern_sym(&module.sym, strings, *ename) else {
                continue;
            };
            if let Some(value) = ann_value_to_file(
                module,
                eval,
                class_desc_sids,
                func_to_method_idx,
                field_to_field_idx,
                strings,
            ) {
                elements.push(AnnotationElem { name, value });
            }
        }
        compile_time.push(Annotation {
            class_descriptor,
            elements,
        });
    }
    Ok(Annotations {
        compile_time,
        runtime: Vec::new(),
        compile_time_type: Vec::new(),
        runtime_type: Vec::new(),
    })
}

fn ann_value_to_file(
    module: &Module,
    val: &AnnValue,
    class_desc_sids: &[StringId],
    func_to_method_idx: &[MethodIdx],
    field_to_field_idx: &[Vec<FieldIdx>],
    strings: &mut StringPool,
) -> Option<AnnotationValue> {
    match val {
        AnnValue::Const(cid) => {
            match module.consts.get(*cid)? {
                Const::Bool(b) => Some(AnnotationValue::Bool(*b)),
                Const::Int8(n) => Some(AnnotationValue::U8(*n)),
                Const::Int32(n) => Some(AnnotationValue::U32(*n)),
                Const::Float32(bits) => Some(AnnotationValue::F32(f32::from_bits(*bits))),
                Const::Int64(n) => Some(AnnotationValue::I64(*n)),
                Const::UInt64(n) => Some(AnnotationValue::U64(*n)),
                Const::Number(bits) => {
                    let v = f64::from_bits(*bits);
                    if *bits != (-0.0f64).to_bits()
                        && v.is_finite()
                        && v >= 0.0
                        && v <= f64::from(u32::MAX)
                        && (v as u32 as f64).to_bits() == *bits
                    {
                        Some(AnnotationValue::U32(v as u32))
                    } else {
                        Some(AnnotationValue::F64(v))
                    }
                }
                Const::String(sym) | Const::BigInt(sym) => Some(AnnotationValue::String(
                    intern_sym(&module.sym, strings, *sym)?,
                )),
                Const::MethodRef { func, .. } => {
                    let fdata = module.func(*func)?;
                    let name = intern_sym(&module.sym, strings, fdata.name)?;
                    let method = func_to_method_idx.get(func.index()).copied();
                    Some(AnnotationValue::Method {
                        name,
                        method,
                        offset: 0,
                    })
                }
                Const::Null => Some(AnnotationValue::StringNullptr),
                Const::Undefined => Some(AnnotationValue::Void),
                _ => None,
            }
        }
        AnnValue::Class(cid) => Some(AnnotationValue::Record(*class_desc_sids.get(cid.index())?)),
        AnnValue::Field(cid, fid) => {
            let fdata = module.classes.get(cid.index())?.fields.get(fid.index())?;
            let name = intern_sym(&module.sym, strings, fdata.name)?;
            let field = field_to_field_idx
                .get(cid.index())
                .and_then(|fs| fs.get(fid.index()))
                .copied();
            Some(AnnotationValue::Enum {
                name,
                field,
                offset: 0,
            })
        }
        AnnValue::Name(sym) => Some(AnnotationValue::String(intern_sym(
            &module.sym,
            strings,
            *sym,
        )?)),
    }
}

fn build_module_data(
    sym_table: &abcd_ir::SymbolTable,
    strings: &mut StringPool,
    imports: &[ImportDecl],
    exports: &[ExportDecl],
    module_requests: &[ModuleRequest],
) -> Result<(ModuleData, Option<ModuleRequestPhase>), LowerError> {
    let mut requests: Vec<StringId> = Vec::new();
    let mut req_idx_by_sym: HashMap<Sym, u32> = HashMap::new();
    let mut phase_flags: Vec<u8> = Vec::new();
    let mut any_lazy = false;

    for req in module_requests {
        let sid =
            intern_sym(sym_table, strings, req.specifier).ok_or(LowerError::UntraceableEntity {
                func: FuncId::new(0),
                kind: EntityKind::StringId,
                raw: req.specifier.0,
            })?;
        let idx = requests.len() as u32;
        req_idx_by_sym.entry(req.specifier).or_insert(idx);
        requests.push(sid);
        if req.lazy {
            any_lazy = true;
            phase_flags.push(1);
        } else {
            phase_flags.push(0);
        }
    }

    let mut ensure_req = |spec: Sym,
                          strings: &mut StringPool,
                          requests: &mut Vec<StringId>,
                          phase_flags: &mut Vec<u8>|
     -> Result<u32, LowerError> {
        if let Some(&idx) = req_idx_by_sym.get(&spec) {
            return Ok(idx);
        }
        let sid = intern_sym(sym_table, strings, spec).ok_or(LowerError::UntraceableEntity {
            func: FuncId::new(0),
            kind: EntityKind::StringId,
            raw: spec.0,
        })?;
        let idx = requests.len() as u32;
        req_idx_by_sym.insert(spec, idx);
        requests.push(sid);
        phase_flags.push(0);
        Ok(idx)
    };

    let sym_sid = |s: Sym, strings: &mut StringPool| -> Result<StringId, LowerError> {
        intern_sym(sym_table, strings, s).ok_or(LowerError::UntraceableEntity {
            func: FuncId::new(0),
            kind: EntityKind::StringId,
            raw: s.0,
        })
    };

    let mut records = Vec::with_capacity(imports.len() + exports.len());
    for imp in imports {
        match imp {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                let module_request_idx =
                    ensure_req(*module_request, strings, &mut requests, &mut phase_flags)?;
                records.push(ModuleRecord::RegularImport {
                    local_name: sym_sid(*local_name, strings)?,
                    import_name: sym_sid(*import_name, strings)?,
                    module_request_idx,
                });
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                let module_request_idx =
                    ensure_req(*module_request, strings, &mut requests, &mut phase_flags)?;
                records.push(ModuleRecord::NamespaceImport {
                    local_name: sym_sid(*local_name, strings)?,
                    module_request_idx,
                });
            }
        }
    }
    for exp in exports {
        match exp {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                records.push(ModuleRecord::LocalExport {
                    local_name: sym_sid(*local_name, strings)?,
                    export_name: sym_sid(*export_name, strings)?,
                });
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                let module_request_idx =
                    ensure_req(*module_request, strings, &mut requests, &mut phase_flags)?;
                records.push(ModuleRecord::IndirectExport {
                    export_name: sym_sid(*export_name, strings)?,
                    import_name: sym_sid(*import_name, strings)?,
                    module_request_idx,
                });
            }
            ExportDecl::Star { module_request } => {
                let module_request_idx =
                    ensure_req(*module_request, strings, &mut requests, &mut phase_flags)?;
                records.push(ModuleRecord::StarExport { module_request_idx });
            }
        }
    }

    let phase = any_lazy.then_some(ModuleRequestPhase {
        source_offset: 0,
        flags: phase_flags,
    });
    Ok((
        ModuleData {
            source_offset: 0,
            requests,
            records,
        },
        phase,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::{
        Block, ClassId, FunctionData, Inst, InstId, Op, Value, ValueDef, ValueId, verify_module,
    };

    /// Build a standalone IR module with NO source `File`: two functions
    /// (`func_main_0` defining closure `helper`), new string constants
    /// (including BMP PUA `U+E000` and a lone surrogate `U+D834`), an array
    /// literal, an object literal, and ES module import/export metadata.
    #[test]
    fn standalone_lower_module_encodes_and_roundtrips() {
        let mut m = Module::new();
        let global_desc = m.sym.intern("L_GLOBAL;");
        let mut cls = ClassData::new(global_desc, global_desc);
        cls.modifiers = Modifiers::PUBLIC;

        let main_name = m.sym.intern("func_main_0");
        let helper_name = m.sym.intern("helper");
        cls.methods = vec![FuncId::new(0), FuncId::new(1)];
        m.classes.push(cls);

        let mut f0 = FunctionData::new(ClassId::new(0), main_name, IrFunctionKind::Function);
        f0.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let b0 = abcd_ir::BlockId::new(0);
        m.blocks.push(Block::default());
        f0.blocks.push(b0);

        let mut f1 = FunctionData::new(ClassId::new(0), helper_name, IrFunctionKind::Function);
        f1.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let b1 = abcd_ir::BlockId::new(1);
        m.blocks.push(Block::default());
        f1.blocks.push(b1);

        let lone_sym = m.sym.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
        let lone_cid = m.consts.push(Const::String(lone_sym));
        let v_lone = ValueId::new(m.values.len() as u32);
        let i_lone = InstId::new(m.insts.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(i_lone),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op: Op::LoadConst(lone_cid),
            result: Some(v_lone),
            block: b1,
            loc: None,
        });
        let i_ret1 = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op: Op::Return {
                value: Some(v_lone),
            },
            result: None,
            block: b1,
            loc: None,
        });
        m.blocks[b1.index()].insts.extend([i_lone, i_ret1]);

        let pua_sym = m.sym.intern("\u{E000}icon");
        let c_one = m.consts.intern(Const::Int32(1));
        let c_pua = m.consts.intern(Const::String(pua_sym));
        let arr_shape = m.consts.push_array(vec![c_one, c_pua]);
        let v_arr = ValueId::new(m.values.len() as u32);
        let i_arr = InstId::new(m.insts.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(i_arr),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op: Op::AllocArray {
                shape: Some(arr_shape),
            },
            result: Some(v_arr),
            block: b0,
            loc: None,
        });

        let v_def = ValueId::new(m.values.len() as u32);
        let i_def = InstId::new(m.insts.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(i_def),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op: Op::DefineFunc {
                body: FuncId::new(1),
                captures: Vec::new(),
                length: 0,
            },
            result: Some(v_def),
            block: b0,
            loc: None,
        });
        let v_clos = ValueId::new(m.values.len() as u32);
        let i_clos = InstId::new(m.insts.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(i_clos),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op: Op::AllocClosure { func: v_def },
            result: Some(v_clos),
            block: b0,
            loc: None,
        });
        let prop_sym = m.sym.intern("fn");
        let i_store = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op: Op::StoreProp {
                object: v_arr,
                name: prop_sym,
                value: v_clos,
            },
            result: None,
            block: b0,
            loc: None,
        });
        let i_ret0 = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op: Op::Return { value: Some(v_arr) },
            result: None,
            block: b0,
            loc: None,
        });
        m.blocks[b0.index()]
            .insts
            .extend([i_arr, i_def, i_clos, i_store, i_ret0]);

        m.functions.push(f0);
        m.functions.push(f1);

        let dep_sym = m.sym.intern("./dep");
        let x_sym = m.sym.intern("x");
        m.module_requests.push(ModuleRequest {
            specifier: dep_sym,
            lazy: true,
        });
        m.imports.push(ImportDecl::Regular {
            local_name: x_sym,
            import_name: x_sym,
            module_request: dep_sym,
        });

        assert!(verify_module(&m).is_ok());

        let file = lower_module(&m, Version::new(12, 0, 6, 0)).expect("standalone lower_module");
        let bytes = abcd_file::encode(&file).expect("encode standalone File");
        let decoded = abcd_file::decode(&bytes).expect("decode standalone File");
        let relifted = abcd_lift::lift_file(&decoded).expect("re-lift standalone File");
        assert!(verify_module(&relifted).is_ok());

        assert_eq!(relifted.functions.len(), 2);
        assert_eq!(relifted.imports.len(), 1);
        assert_eq!(relifted.module_requests.len(), 1);
        assert!(relifted.module_requests[0].lazy);
        assert!(relifted.sym.get("\u{E000}icon").is_some());
        assert!(relifted.sym.get_raw_mutf8(&[0xED, 0xA0, 0xB4]).is_some());
    }

    /// `rewrite_file` materializes IR-synthesized strings, literal arrays, and
    /// newly appended helper functions onto an existing decoded `File`.
    #[test]
    fn rewrite_file_materializes_synthesized_entities() {
        let mut b = abcd_file::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, FileSourceLang::EcmaScript);
        let proto = b.create_proto(Type::Tagged, &[]);
        let (code, _) = abcd_isa::encode(&[abcd_isa::Bytecode::Returnundefined]).unwrap();
        let m_h = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 0, 0);
        b.method_set_source_lang(m_h, FileSourceLang::EcmaScript);
        let base_bytes = b.finalize().unwrap();
        let base_file = abcd_file::decode(&base_bytes).unwrap();

        let mut module = abcd_lift::lift_file(&base_file).unwrap();

        let synth_name = module.sym.intern("synth_helper");
        let synth_fid = FuncId::new(module.functions.len() as u32);
        let synth_bb = abcd_ir::BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());
        let mut synth_fn = FunctionData::new(ClassId::new(0), synth_name, IrFunctionKind::Function);
        synth_fn.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        synth_fn.blocks.push(synth_bb);
        module.classes[0].methods.push(synth_fid);

        let new_str = module.sym.intern("synthesized-string");
        let new_str_cid = module.consts.push(Const::String(new_str));
        let v_str = ValueId::new(module.values.len() as u32);
        let i_str = InstId::new(module.insts.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(i_str),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::LoadConst(new_str_cid),
            result: Some(v_str),
            block: synth_bb,
            loc: None,
        });
        let i_ret = InstId::new(module.insts.len() as u32);
        module.insts.push(Inst {
            op: Op::Return { value: Some(v_str) },
            result: None,
            block: synth_bb,
            loc: None,
        });
        module.blocks[synth_bb.index()].insts.extend([i_str, i_ret]);
        module.functions.push(synth_fn);

        let main_bb = module.functions[0].blocks[0];
        module.blocks[main_bb.index()].insts.clear();
        let c42 = module.consts.intern(Const::Int32(42));
        let arr_cid = module.consts.push_array(vec![c42]);
        let v_arr = ValueId::new(module.values.len() as u32);
        let i_arr = InstId::new(module.insts.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(i_arr),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::AllocArray {
                shape: Some(arr_cid),
            },
            result: Some(v_arr),
            block: main_bb,
            loc: None,
        });
        let v_def = ValueId::new(module.values.len() as u32);
        let i_def = InstId::new(module.insts.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(i_def),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::DefineFunc {
                body: synth_fid,
                captures: Vec::new(),
                length: 0,
            },
            result: Some(v_def),
            block: main_bb,
            loc: None,
        });
        let v_clos = ValueId::new(module.values.len() as u32);
        let i_clos = InstId::new(module.insts.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(i_clos),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::AllocClosure { func: v_def },
            result: Some(v_clos),
            block: main_bb,
            loc: None,
        });
        let i_ret0 = InstId::new(module.insts.len() as u32);
        module.insts.push(Inst {
            op: Op::Return {
                value: Some(v_clos),
            },
            result: None,
            block: main_bb,
            loc: None,
        });
        module.blocks[main_bb.index()]
            .insts
            .extend([i_arr, i_def, i_clos, i_ret0]);

        assert!(verify_module(&module).is_ok());

        let rewritten =
            rewrite_file(&module, &base_file, LowerOptions::default()).expect("rewrite_file");
        let encoded = abcd_file::encode(&rewritten).expect("encode rewritten file");
        let decoded = abcd_file::decode(&encoded).expect("decode rewritten file");
        assert!(decoded.strings.get("synthesized-string").is_some());
        assert_eq!(decoded.all_methods().count(), 2);
        assert_eq!(decoded.literal_arrays.len(), 1);
    }

    /// 64-bit static integer constants (`Const::Int64`, `Const::UInt64`, `R2-D5`)
    /// lower cleanly in field initializers and compile-time annotations, while
    /// failing cleanly with `UntraceableEntity` inside dynamic JS literal buffers.
    #[test]
    fn int64_and_uint64_field_and_annotation_consts_lower_cleanly() {
        let mut m = Module::new();
        let ann_desc = m.sym.intern("LMyAnn;");
        let ann_cls = ClassData::new(ann_desc, ann_desc);
        let ann_cid = ClassId::new(m.classes.len() as u32);
        m.classes.push(ann_cls);

        let cls_desc = m.sym.intern("LMyRecord;");
        let mut cls = ClassData::new(cls_desc, cls_desc);
        cls.modifiers = Modifiers::PUBLIC;

        let i64_val: i64 = (1_i64 << 55) + 7;
        let u64_val: u64 = (1_u64 << 63) + 99;
        let c_i64 = m.consts.intern(Const::Int64(i64_val));
        let c_u64 = m.consts.intern(Const::UInt64(u64_val));

        let f1_name = m.sym.intern("signed_f");
        let f2_name = m.sym.intern("unsigned_f");
        let e1_name = m.sym.intern("s");
        let e2_name = m.sym.intern("u");
        cls.fields.push(FieldData {
            name: f1_name,
            ty: Ty::Static(StaticTy::I64),
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(c_i64),
            annotations: vec![abcd_ir::Annotation {
                class: ann_cid,
                elements: vec![
                    (e1_name, AnnValue::Const(c_i64)),
                    (e2_name, AnnValue::Const(c_u64)),
                ],
            }],
        });
        cls.fields.push(FieldData {
            name: f2_name,
            ty: Ty::Static(StaticTy::U64),
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(c_u64),
            annotations: Vec::new(),
        });
        m.classes.push(cls);

        let file = lower_module(&m, Version::new(12, 0, 6, 0)).expect("lower 64-bit fields/anns");
        let rec_sid = file.strings.get("LMyRecord;").expect("record descriptor");
        let rec = &file.classes[&rec_sid];
        assert_eq!(rec.fields[0].initial_value, Some(FieldValue::I64(i64_val)));
        assert_eq!(
            rec.fields[1].initial_value,
            Some(FieldValue::I64(u64_val as i64))
        );
        let elems = &rec.fields[0].annotations.compile_time[0].elements;
        assert_eq!(elems[0].value, AnnotationValue::I64(i64_val));
        assert_eq!(elems[1].value, AnnotationValue::U64(u64_val));
    }

    /// All 12 `TypedArrayTag` variants (`U1..F64`, `String`) materialize
    /// losslessly into `LiteralValue::Array*(Vec<T>)` (both root and nested),
    /// encode/decode cleanly, and resolve via `EntityResolver`; non-JSON string
    /// fields emit `FieldValue::String(sid)`.
    #[test]
    fn typed_array_literals_and_string_field_initializers_lower_losslessly() {
        let mut m = Module::new();
        let global_desc = m.sym.intern("L_GLOBAL;");
        let mut cls = ClassData::new(global_desc, global_desc);
        cls.modifiers = Modifiers::PUBLIC;

        let str_field_name = m.sym.intern("GREETING");
        let json_field_name = m.sym.intern(abcd_file::JSON_FILE_CONTENT_FIELD);
        let hello_sym = m.sym.intern("hello-ark");
        let json_sym = m.sym.intern("{\"ok\":true}");
        let c_hello = m.consts.intern(Const::String(hello_sym));
        let c_json = m.consts.intern(Const::String(json_sym));

        cls.fields.push(FieldData {
            name: str_field_name,
            ty: Ty::Static(StaticTy::U32),
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(c_hello),
            annotations: Vec::new(),
        });
        cls.fields.push(FieldData {
            name: json_field_name,
            ty: Ty::Static(StaticTy::U32),
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(c_json),
            annotations: Vec::new(),
        });

        let fname = m.sym.intern("func_main_0");
        cls.methods = vec![FuncId::new(0)];
        m.classes.push(cls);

        let c_true = m.consts.intern(Const::Bool(true));
        let c_false = m.consts.intern(Const::Bool(false));
        let c_u8 = m.consts.intern(Const::Int8(200));
        let c_i8 = m.consts.intern(Const::Int32((-5_i32) as u32));
        let c_u16 = m.consts.intern(Const::Int32(50_000));
        let c_i16 = m.consts.intern(Const::Int32((-1234_i32) as u32));
        let c_u32 = m.consts.intern(Const::Int32(3_000_000_000));
        let c_i32 = m.consts.intern(Const::Int32((-99_999_i32) as u32));
        let c_u64 = m.consts.intern(Const::UInt64((1_u64 << 63) + 5));
        let c_i64 = m.consts.intern(Const::Int64(-777_777_777_777));
        let c_f32 = m.consts.intern(Const::float32(1.5));
        let c_f64 = m.consts.intern(Const::number(-2.25));

        let ta_u1 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U1,
            items: vec![c_true, c_false],
        });
        let ta_u8 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U8,
            items: vec![c_u8],
        });
        let ta_i8 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I8,
            items: vec![c_i8],
        });
        let ta_u16 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U16,
            items: vec![c_u16],
        });
        let ta_i16 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I16,
            items: vec![c_i16],
        });
        let ta_u32 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U32,
            items: vec![c_u32],
        });
        let ta_i32 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I32,
            items: vec![c_i32],
        });
        let ta_u64 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U64,
            items: vec![c_u64],
        });
        let ta_i64 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I64,
            items: vec![c_i64],
        });
        let ta_f32 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::F32,
            items: vec![c_f32],
        });
        let ta_f64 = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::F64,
            items: vec![c_f64],
        });
        let ta_str = m.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::String,
            items: vec![c_hello],
        });

        let root_shapes = [
            ta_u1, ta_u8, ta_i8, ta_u16, ta_i16, ta_u32, ta_i32, ta_u64, ta_i64, ta_f32, ta_f64,
            ta_str,
        ];
        // Also verify trailing inline `TypedArrayLiteral` inside `ArrayLiteral` (`round3_regressions` shape).
        let trailing_ta_shape = m.consts.push_array(vec![c_true, ta_u8]);

        let mut f0 = FunctionData::new(ClassId::new(0), fname, IrFunctionKind::Function);
        f0.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let bb = abcd_ir::BlockId::new(0);
        m.blocks.push(Block::default());
        f0.blocks.push(bb);

        let mut last_val = None;
        for &shape in root_shapes
            .iter()
            .chain(std::iter::once(&trailing_ta_shape))
        {
            let vid = ValueId::new(m.values.len() as u32);
            let iid = InstId::new(m.insts.len() as u32);
            m.values.push(Value {
                def: ValueDef::Inst(iid),
                ty: Ty::Any,
            });
            m.insts.push(Inst {
                op: Op::AllocArray { shape: Some(shape) },
                result: Some(vid),
                block: bb,
                loc: None,
            });
            m.blocks[0].insts.push(iid);
            last_val = Some(vid);
        }
        let i_ret = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op: Op::Return { value: last_val },
            result: None,
            block: bb,
            loc: None,
        });
        m.blocks[0].insts.push(i_ret);
        m.functions.push(f0);

        let file = lower_module(&m, Version::new(12, 0, 6, 0)).expect("lower typed arrays");
        let g_sid = file.strings.get("L_GLOBAL;").unwrap();
        let hello_sid = file.strings.get("hello-ark").unwrap();
        let json_sid = file.strings.get("{\"ok\":true}").unwrap();
        let g_cls = &file.classes[&g_sid];
        assert_eq!(
            g_cls.fields[0].initial_value,
            Some(FieldValue::String(hello_sid))
        );
        assert!(matches!(
            g_cls.fields[1].initial_value,
            Some(FieldValue::JsonFileContent { content, .. }) if content == json_sid
        ));

        let expected_roots = [
            LiteralValue::ArrayU1(vec![true, false]),
            LiteralValue::ArrayU8(vec![200]),
            LiteralValue::ArrayI8(vec![-5]),
            LiteralValue::ArrayU16(vec![50_000]),
            LiteralValue::ArrayI16(vec![-1234]),
            LiteralValue::ArrayU32(vec![3_000_000_000]),
            LiteralValue::ArrayI32(vec![-99_999]),
            LiteralValue::ArrayU64(vec![(1_u64 << 63) + 5]),
            LiteralValue::ArrayI64(vec![-777_777_777_777]),
            LiteralValue::ArrayF32(vec![1.5]),
            LiteralValue::ArrayF64(vec![-2.25]),
            LiteralValue::ArrayString(vec![hello_sid]),
        ];
        assert_eq!(file.literal_arrays.len(), 13);
        for (i, expected) in expected_roots.iter().enumerate() {
            assert_eq!(file.literal_arrays[i].values, vec![expected.clone()]);
        }
        assert_eq!(
            file.literal_arrays[12].values,
            vec![LiteralValue::Bool(true), LiteralValue::ArrayU8(vec![200])]
        );

        // Verify EntityResolver matches all 12 root TypedArrayLiterals + trailing shape!
        let resolver = EntityResolver::new(&m, &file);
        for (i, &shape) in root_shapes.iter().enumerate() {
            assert_eq!(
                resolver.literal_array_idx(shape),
                Some(LiteralArrayIdx(i as u32))
            );
        }
        assert_eq!(
            resolver.literal_array_idx(trailing_ta_shape),
            Some(LiteralArrayIdx(12))
        );

        // Encode & decode roundtrip across all 12 wire-legal standalone typed literal arrays!
        let mut wire_file = file.clone();
        wire_file.literal_arrays.truncate(12);
        for m_item in wire_file
            .classes
            .get_mut(&g_sid)
            .unwrap()
            .methods
            .iter_mut()
        {
            if let Some(body) = &mut m_item.body {
                for ent in body.entities.values_mut() {
                    if *ent == EntityRef::LiteralArray(LiteralArrayIdx(12)) {
                        *ent = EntityRef::LiteralArray(LiteralArrayIdx(1));
                    }
                }
            }
        }
        let bytes = abcd_file::encode(&wire_file).expect("encode typed array file");
        let decoded = abcd_file::decode(&bytes).expect("decode typed array file");
        assert_eq!(decoded.literal_arrays.len(), 12);
        for (i, expected) in expected_roots.iter().enumerate() {
            if let LiteralValue::ArrayString(_) = expected {
                let LiteralValue::ArrayString(sids) = &decoded.literal_arrays[i].values[0] else {
                    panic!("expected ArrayString at index {i}");
                };
                assert_eq!(sids.len(), 1);
                assert_eq!(decoded.strings.as_str(sids[0]), Some("hello-ark"));
            } else {
                assert_eq!(decoded.literal_arrays[i].values, vec![expected.clone()]);
            }
        }
    }

    /// `rewrite_file` updates pre-existing in-memory `_ESSlotNumberAnnotation`
    /// (`SlotNumber`) on `Method::annotations` before `encode`, remaps
    /// `MethodIdx` inside `param_annotations` when synthesized classes shift
    /// dense method indices, and preserves synthesized class fields.
    #[test]
    fn rewrite_file_syncs_in_memory_slot_number_and_remaps_param_annotations() {
        let mut strings = StringPool::new();
        // Intern `"L_AAA;"` FIRST so its `StringId(0)` sorts BEFORE `"L_GLOBAL;"`
        // in `File::classes: BTreeMap<StringId, Class>`, shifting `L_GLOBAL;`'s
        // existing `func_main_0` from `MethodIdx(0)` to `MethodIdx(1)` when
        // `L_AAA;` + `synth_fn` are synthesized!
        let synth_cls_sid = strings.get_or_intern("L_AAA;");
        let global_sid = strings.get_or_intern("L_GLOBAL;");
        let ann_desc_sid = strings.get_or_intern(SLOT_NUMBER_ANN_DESC);
        let slot_elem_sid = strings.get_or_intern(SLOT_NUMBER_ELEM);
        let param_ann_desc_sid = strings.get_or_intern("LParamHook;");
        let hook_elem_sid = strings.get_or_intern("target");
        let main_sid = strings.get_or_intern("func_main_0");

        let mut classes = BTreeMap::new();
        classes.insert(
            ann_desc_sid,
            Class {
                descriptor: ann_desc_sid,
                name: ann_desc_sid,
                access_flags: AccessFlags::PUBLIC | AccessFlags::ANNOTATION,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: true,
                super_class: None,
                interfaces: Vec::new(),
                methods: Vec::new(),
                fields: Vec::new(),
                annotations: Annotations::default(),
            },
        );
        classes.insert(
            global_sid,
            Class {
                descriptor: global_sid,
                name: global_sid,
                access_flags: AccessFlags::PUBLIC,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: vec![Method {
                    name: main_sid,
                    offset: 0,
                    access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                    function_kind: FileFunctionKind::Function,
                    source_lang: FileSourceLang::EcmaScript,
                    is_external: false,
                    return_type: Some(Type::Tagged),
                    arg_types: vec![Type::Tagged],
                    body: Some(MethodBody {
                        num_vregs: 0,
                        num_args: 1,
                        bytecodes: vec![abcd_isa::Bytecode::Returnundefined],
                        entities: HashMap::new(),
                        try_blocks: Vec::new(),
                        ic_size: Some(99),
                    }),
                    annotations: Annotations {
                        // Pre-existing stale `SlotNumber = 99` in memory!
                        compile_time: vec![Annotation {
                            class_descriptor: ann_desc_sid,
                            elements: vec![AnnotationElem {
                                name: slot_elem_sid,
                                value: AnnotationValue::U32(99),
                            }],
                        }],
                        runtime: Vec::new(),
                        compile_time_type: Vec::new(),
                        runtime_type: Vec::new(),
                    },
                    param_annotations: ParamAnnotations {
                        compile_time: vec![vec![Annotation {
                            class_descriptor: param_ann_desc_sid,
                            elements: vec![AnnotationElem {
                                name: hook_elem_sid,
                                value: AnnotationValue::Method {
                                    name: main_sid,
                                    method: Some(MethodIdx(0)),
                                    offset: 0,
                                },
                            }],
                        }]],
                        runtime: vec![vec![Annotation {
                            class_descriptor: param_ann_desc_sid,
                            elements: vec![AnnotationElem {
                                name: hook_elem_sid,
                                value: AnnotationValue::Method {
                                    name: main_sid,
                                    method: Some(MethodIdx(0)),
                                    offset: 0,
                                },
                            }],
                        }]],
                    },
                    debug: None,
                }],
                fields: Vec::new(),
                annotations: Annotations::default(),
            },
        );

        let base_file = File {
            version: Version::new(12, 0, 6, 0),
            checksum: 0,
            size: 0,
            file_type: FileType::Dynamic,
            strings,
            classes,
            literal_arrays: Vec::new(),
            literal_array_header_offsets: Vec::new(),
        };

        // Construct `Module` corresponding to `base_file` + synthesized `L_AAA;`
        // class (with a static string field) and synthesized method `synth_fn`
        // placed inside `L_AAA;`, while `func_main_0` emits 1 `Add2` (`ic_size = 1`).
        let mut m = Module::new();
        let g_sym = m.sym.intern("L_GLOBAL;");
        let a_sym = m.sym.intern("L_AAA;");
        let main_sym = m.sym.intern("func_main_0");
        let synth_fn_sym = m.sym.intern("synth_fn");
        let sf_name = m.sym.intern("TAG");
        let sf_val = m.sym.intern("v1");
        let sf_cid = m.consts.intern(Const::String(sf_val));

        let mut g_cls = ClassData::new(g_sym, g_sym);
        g_cls.modifiers = Modifiers::PUBLIC;
        g_cls.methods = vec![FuncId::new(0)];
        m.classes.push(g_cls);

        let mut a_cls = ClassData::new(a_sym, a_sym);
        a_cls.modifiers = Modifiers::PUBLIC;
        a_cls.methods = vec![FuncId::new(1)];
        a_cls.fields.push(FieldData {
            name: sf_name,
            ty: Ty::Static(StaticTy::U32),
            modifiers: Modifiers::PUBLIC.union(Modifiers::STATIC),
            initial_value: Some(sf_cid),
            annotations: Vec::new(),
        });
        m.classes.push(a_cls);

        // FuncId(0) = `func_main_0` on `L_GLOBAL;` (1 IC slot via `Add2`).
        let mut f0 = FunctionData::new(ClassId::new(0), main_sym, IrFunctionKind::Function);
        let b0 = abcd_ir::BlockId::new(0);
        m.blocks.push(Block::default());
        f0.blocks.push(b0);
        let p0 = ValueId::new(0);
        m.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        f0.params.push(p0);
        let sum = ValueId::new(1);
        m.values.push(Value {
            def: ValueDef::Inst(InstId::new(0)),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op: Op::BinaryOp {
                op: abcd_ir::BinOp::Add,
                left: p0,
                right: p0,
            },
            result: Some(sum),
            block: b0,
            loc: None,
        });
        m.insts.push(Inst {
            op: Op::Return { value: Some(sum) },
            result: None,
            block: b0,
            loc: None,
        });
        m.blocks[0].insts.extend([InstId::new(0), InstId::new(1)]);
        m.functions.push(f0);

        // FuncId(1) = `synth_fn` on `L_AAA;` (0 IC slots).
        let mut f1 = FunctionData::new(ClassId::new(1), synth_fn_sym, IrFunctionKind::Function);
        let b1 = abcd_ir::BlockId::new(1);
        m.blocks.push(Block::default());
        f1.blocks.push(b1);
        m.insts.push(Inst {
            op: Op::Return { value: None },
            result: None,
            block: b1,
            loc: None,
        });
        m.blocks[1].insts.push(InstId::new(2));
        m.functions.push(f1);

        let rewritten =
            rewrite_file(&m, &base_file, LowerOptions::default()).expect("rewrite_file");

        // 1. Synthesized class `L_AAA;` preserved its field `TAG = "v1"` (`FieldValue::String`)!
        let v1_sid = rewritten.strings.get("v1").unwrap();
        let a_out = &rewritten.classes[&synth_cls_sid];
        assert_eq!(a_out.fields.len(), 1);
        assert_eq!(
            a_out.fields[0].initial_value,
            Some(FieldValue::String(v1_sid))
        );

        // 2. `L_AAA;::synth_fn` sits at `MethodIdx(0)` and `L_GLOBAL;::func_main_0`
        //    shifted to `MethodIdx(1)` -> both `compile_time` and `runtime`
        //    `param_annotations` on `func_main_0` MUST be remapped to `MethodIdx(1)`!
        let main_out = &rewritten.classes[&global_sid].methods[0];
        assert_eq!(
            main_out.param_annotations.compile_time[0][0].elements[0].value,
            AnnotationValue::Method {
                name: main_sid,
                method: Some(MethodIdx(1)),
                offset: 0,
            }
        );
        assert_eq!(
            main_out.param_annotations.runtime[0][0].elements[0].value,
            AnnotationValue::Method {
                name: main_sid,
                method: Some(MethodIdx(1)),
                offset: 0,
            }
        );

        // 3. Pre-existing `SlotNumber = 99` on `func_main_0` was updated IN MEMORY
        //    to `U32(1)` (`ic_size = 1`) before `encode`!
        assert_eq!(main_out.body.as_ref().unwrap().ic_size, Some(1));
        assert_eq!(
            main_out.annotations.compile_time[0].elements[0].value,
            AnnotationValue::U32(1)
        );
    }
}
