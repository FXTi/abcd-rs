//! Whole-module lowering and pool-materializing file rewrite (#30, `#50`
//! `R3-D2`, `#57` `R3-H8`/`R3-H9`/`R3-M8`).
//!
//! Bridges the gap between pure IR transformations and encodable
//! [`abcd_file::File`] containers in two modes:
//!
//! 1. [`rewrite_file`] / [`rewrite_file_owned`]: lowers all functions of
//!    `module` onto an existing `base_file` (cloning or consuming by value),
//!    preserving untouched container metadata while materializing any newly
//!    introduced [`Sym`] strings, [`abcd_ir::Const`] literal arrays, classes,
//!    helper functions, and reconstructed [`MethodDebugInfo`] records into the
//!    output [`File`] in bounded parallel batches (`#84`).
//! 2. [`lower_module`] / [`lower_module_with_options`]: standalone lowering
//!    from `&abcd_ir::Module` + [`abcd_file::Version`] directly to a complete,
//!    encodable [`abcd_file::File`] with zero source `File` dependency and zero
//!    fabricated file offsets (`#50`, `#84`).

mod materialize;
mod metadata;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, HashMap};
use std::ops::Range;

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Annotations, Class, ColumnEntry,
    EntityRef, Field, FieldIdx, FieldValue, File, FileType, LineEntry, LiteralArrayIdx,
    MethodDebugInfo, MethodIdx, ParamAnnotations, ParamInfo, SourceLang as FileSourceLang,
    StringId, StringPool, Type, Version,
};
use abcd_ir::{ConstId, FuncId, Module, Sym};
use abcd_isa::EntityKind;
use rayon::prelude::*;

use self::materialize::Materializer;
use self::metadata::{
    build_annotations, build_field_shell, build_method_shell, build_module_data, is_external_class,
    modifiers_to_access_flags, source_lang_to_file,
};
use crate::layout::LayoutResult;
use crate::method_body::BaseEntityIndex;
use crate::{LowerError, LowerOptions, lower_function_with_options};

const SLOT_NUMBER_ANN_DESC: &str = "L_ESSlotNumberAnnotation;";
const SLOT_NUMBER_ELEM: &str = "SlotNumber";
const MAX_LOWER_BATCH_INSTS: usize = 65_536;
const MAX_LOWER_BATCH_FUNCS: usize = 512;

/// Rewrite a cloned `base_file` with lowered bodies from `module`,
/// materializing any IR-synthesized strings, literal arrays, classes, helper
/// functions, and reconstructed [`MethodDebugInfo`] tables into the returned
/// [`File`] (#30, `#50`, `#57`, `#84`).
///
/// Prefer [`rewrite_file_owned`] when the caller no longer needs `base_file`
/// after lowering, avoiding cloning pre-existing [`abcd_file::MethodBody`]
/// buffers.
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
    rewrite_file_owned(module, base_file.clone(), options)
}

/// Streaming, by-value counterpart of [`rewrite_file`] (`#84` Part 1b):
/// consumes `base_file`, drops replaced [`abcd_file::MethodBody`] buffers
/// before lowering, and lowers + relocates functions in bounded parallel
/// batches with zero duplicate bytecode vector clones.
pub fn rewrite_file_owned(
    module: &Module,
    base_file: File,
    options: LowerOptions,
) -> Result<File, LowerError> {
    let mut out = base_file;
    // Index `out`'s original strings (`HashTable<u32>`), `source_offset`
    // provenance, method count, and literal arrays BEFORE mutating `out` or
    // clearing replaced method bodies.
    let base_index = BaseEntityIndex::from_file(module, &out);

    // Map existing methods and fields in `all_methods()` / `all_fields()` order,
    // immediately freeing `m.body` on every method that `module` will replace
    // with a lowered body (`#84`).
    let mut base_method_locs: Vec<(StringId, usize)> = Vec::new();
    let mut base_field_locs: Vec<(StringId, usize)> = Vec::new();
    for (&desc_sid, cls) in &mut out.classes {
        for (mi, m) in cls.methods.iter_mut().enumerate() {
            let fi = base_method_locs.len();
            base_method_locs.push((desc_sid, mi));
            if module
                .functions
                .get(fi)
                .is_some_and(|f| !f.blocks.is_empty())
            {
                m.body = None;
            }
        }
        for fi in 0..cls.fields.len() {
            base_field_locs.push((desc_sid, fi));
        }
    }

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
    let mut class_field_indices: HashMap<StringId, HashMap<StringId, usize>> = HashMap::new();

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
        if !cls_data.fields.is_empty() {
            let existing_fields = out
                .classes
                .get(&desc_sid)
                .map_or(&[][..], |c| c.fields.as_slice());
            let field_map = class_field_indices.entry(desc_sid).or_insert_with(|| {
                let mut map = HashMap::with_capacity(existing_fields.len() + cls_data.fields.len());
                for (idx, ef) in existing_fields.iter().enumerate() {
                    map.entry(ef.name).or_insert(idx);
                }
                map
            });
            for fdata in &cls_data.fields {
                let f_sid = intern_sym(&module.sym, &mut out.strings, fdata.name).ok_or(
                    LowerError::UntraceableEntity {
                        func: FuncId::new(0),
                        kind: EntityKind::StringId,
                        raw: fdata.name.0,
                    },
                )?;
                if let Some(&pos) = field_map.get(&f_sid) {
                    cls_field_slots.push((desc_sid, pos));
                    cls_synth_flags.push(false);
                } else {
                    let shell =
                        build_field_shell(module, fdata, f_sid, &class_desc_sids, &mut out.strings);
                    let cls = out.classes.get_mut(&desc_sid).expect("inserted above");
                    let pos = cls.fields.len();
                    cls.fields.push(shell);
                    field_map.insert(f_sid, pos);
                    cls_field_slots.push((desc_sid, pos));
                    cls_synth_flags.push(true);
                }
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
                if let Some(field_map) = class_field_indices.get_mut(&desc_sid) {
                    field_map.entry(sn_name).or_insert(slot_idx);
                }
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
                let mr_idx = cls.fields.len();
                cls.fields.push(Field {
                    name: mr_name,
                    offset: 0,
                    field_type: Type::U32,
                    access_flags: AccessFlags::STATIC,
                    is_external: false,
                    initial_value: Some(FieldValue::ModuleData(md)),
                    annotations: Annotations::default(),
                });
                if let Some(field_map) = class_field_indices.get_mut(&desc_sid) {
                    field_map.entry(mr_name).or_insert(mr_idx);
                }
                if let (Some(ph), Some(pname)) = (phase_opt, pname_opt) {
                    let ph_idx = cls.fields.len();
                    cls.fields.push(Field {
                        name: pname,
                        offset: 0,
                        field_type: Type::U32,
                        access_flags: AccessFlags::STATIC,
                        is_external: false,
                        initial_value: Some(FieldValue::ModuleRequestPhase(ph)),
                        annotations: Annotations::default(),
                    });
                    if let Some(field_map) = class_field_indices.get_mut(&desc_sid) {
                        field_map.entry(pname).or_insert(ph_idx);
                    }
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
                None,
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
    // `func_to_method_idx` / `field_to_field_idx` and running `Materializer` so
    // `out.strings` `StringId` order and `out.classes` match verbatim!
    let need_slot_ann_record = crate::isel::module_emits_any_ic(module);
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

    // Phase A: Lower functions in bounded Rayon batches, relocating bytecodes
    // in-place and attaching `MethodBody`s directly onto `out.classes` while
    // retaining only compact `PreparedDebugTables` and `ic_size` for Phase B.
    let mut prepared_debug: Vec<Option<PreparedDebugTables>> = std::iter::repeat_with(|| None)
        .take(module.functions.len())
        .collect();
    let mut body_ic_sizes: Vec<Option<u32>> = vec![None; module.functions.len()];
    let mut resolved_scope_names: Vec<(StringId, usize, LiteralArrayIdx)> =
        Vec::with_capacity(synth_scope_name_slots.len());
    {
        let File {
            strings,
            classes,
            literal_arrays,
            ..
        } = &mut out;
        let mut materializer = Materializer::new(
            module,
            strings,
            literal_arrays,
            &func_to_method_idx,
            Some(&base_index),
        );
        for batch in build_lower_batches(module) {
            let lowered_batch = lower_batch_parallel(module, batch.clone(), options);
            for (offset, item_res) in lowered_batch.into_iter().enumerate() {
                let fi = batch.start + offset;
                if let Some((layout, dbg_tables)) = item_res? {
                    let func_id = FuncId::new(fi as u32);
                    let body = materializer.build_method_body_owned(func_id, layout)?;
                    body_ic_sizes[fi] = body.ic_size;
                    prepared_debug[fi] = dbg_tables;
                    let (desc_sid, mi) = func_slots[fi];
                    if let Some(cls) = classes.get_mut(&desc_sid)
                        && let Some(m) = cls.methods.get_mut(mi)
                    {
                        m.body = Some(body);
                    }
                }
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
    debug_assert_eq!(
        need_slot_ann_record,
        body_ic_sizes.iter().flatten().any(|&ic| ic > 0),
        "module_emits_any_ic disagreed with lowered LayoutResult::ic_size > 0"
    );

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

    // Phase B: Intern method annotations & debug strings in exact `0..N` order
    // and synchronize `_ESSlotNumberAnnotation`.
    for (fi, func_data) in module.functions.iter().enumerate() {
        let (desc_sid, mi) = func_slots[fi];
        let is_synth_fn = fi >= base_method_locs.len();
        let had_layout = body_ic_sizes[fi].is_some();
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
        let debug_rebuilt = if had_layout || is_synth_fn {
            Some(finalize_method_debug(
                module,
                func_data,
                prepared_debug[fi].take(),
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
            if let Some(ic) = body_ic_sizes[fi] {
                sync_method_slot_annotation(&mut m.annotations, &out.strings, slot_ann_sids, ic);
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
/// `#57`, `#84`).
pub fn lower_module_with_options(
    module: &Module,
    version: Version,
    options: LowerOptions,
) -> Result<File, LowerError> {
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
            None,
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

    // 5. Lower functions in bounded Rayon batches, relocating bytecodes in-place
    //    and attaching `MethodBody` + `PreparedDebugTables` directly onto
    //    `file.classes` without holding all `LayoutResult`s + `MethodBody`s at once.
    let mut body_ic_sizes: Vec<Option<u32>> = vec![None; module.functions.len()];
    let mut resolved_scope_names: Vec<(StringId, usize, LiteralArrayIdx)> =
        Vec::with_capacity(scope_name_slots.len());
    {
        let File {
            strings,
            classes,
            literal_arrays,
            ..
        } = &mut file;
        let mut materializer =
            Materializer::new(module, strings, literal_arrays, &func_to_method_idx, None);
        for batch in build_lower_batches(module) {
            let lowered_batch = lower_batch_parallel(module, batch.clone(), options);
            for (offset, item_res) in lowered_batch.into_iter().enumerate() {
                let fi = batch.start + offset;
                if let Some((layout, dbg_tables)) = item_res? {
                    let func_id = FuncId::new(fi as u32);
                    let body = materializer.build_method_body_owned(func_id, layout)?;
                    body_ic_sizes[fi] = body.ic_size;
                    let (desc_sid, mi) = func_slots[fi];
                    if let Some(cls) = classes.get_mut(&desc_sid)
                        && let Some(method) = cls.methods.get_mut(mi)
                    {
                        if let (Some(dbg), Some(tables)) = (&mut method.debug, dbg_tables) {
                            dbg.line_table = tables.line_table;
                            dbg.column_table = tables.column_table;
                        }
                        method.body = Some(body);
                    }
                }
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

    // 6. Populate class, field, and method annotations + sync `SlotNumber`.
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

    let need_slot_ann = body_ic_sizes.iter().flatten().any(|&ic| ic > 0);
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
            if let Some(ic) = body_ic_sizes[fi] {
                sync_method_slot_annotation(
                    &mut method.annotations,
                    &file.strings,
                    slot_ann_sids,
                    ic,
                );
            }
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
    let tables = prepare_debug_tables(module, func_data, layout);
    finalize_method_debug(module, func_data, tables, strings)
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

struct PreparedDebugTables {
    line_table: Vec<LineEntry>,
    column_table: Vec<ColumnEntry>,
}

fn prepare_debug_tables(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    layout: Option<&LayoutResult>,
) -> Option<PreparedDebugTables> {
    let dbg = func_data.debug.as_ref()?;
    let lay = layout?;

    let mut line_table: Vec<LineEntry> = Vec::new();
    let mut column_table: Vec<ColumnEntry> = Vec::new();

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

    Some(PreparedDebugTables {
        line_table,
        column_table,
    })
}

fn finalize_method_debug(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    tables: Option<PreparedDebugTables>,
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

    let (line_table, column_table) = match tables {
        Some(t) => (t.line_table, t.column_table),
        None => (Vec::new(), Vec::new()),
    };

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

/// Partition `0..module.functions.len()` into contiguous batches bounded by
/// `MAX_LOWER_BATCH_FUNCS` and `MAX_LOWER_BATCH_INSTS` (`#84`).
fn build_lower_batches(module: &Module) -> Vec<Range<usize>> {
    let total = module.functions.len();
    if total == 0 {
        return Vec::new();
    }
    let mut batches: Vec<Range<usize>> = Vec::new();
    let mut start = 0usize;
    let mut batch_insts = 0usize;

    for (fi, func) in module.functions.iter().enumerate() {
        let fn_insts: usize = func
            .blocks
            .iter()
            .filter_map(|&bb| module.block(bb))
            .map(|b| b.insts.len())
            .sum();
        if fi > start
            && (fi - start >= MAX_LOWER_BATCH_FUNCS
                || batch_insts.saturating_add(fn_insts) > MAX_LOWER_BATCH_INSTS)
        {
            batches.push(start..fi);
            start = fi;
            batch_insts = 0;
        }
        batch_insts = batch_insts.saturating_add(fn_insts);
    }
    batches.push(start..total);
    batches
}

type LoweredBatchItem = Result<Option<(LayoutResult, Option<PreparedDebugTables>)>, LowerError>;

fn lower_batch_parallel(
    module: &Module,
    batch: Range<usize>,
    options: LowerOptions,
) -> Vec<LoweredBatchItem> {
    batch
        .into_par_iter()
        .map(|fi| {
            let func_id = FuncId::new(fi as u32);
            let Some(func) = module.func(func_id) else {
                return Ok(None);
            };
            if func.blocks.is_empty() {
                return Ok(None);
            }
            let layout = lower_function_with_options(module, func_id, options)?;
            let dbg_tables = prepare_debug_tables(module, func, Some(&layout));
            Ok(Some((layout, dbg_tables)))
        })
        .collect()
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
