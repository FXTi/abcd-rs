//! Whole-module lowering and pool-materializing file rewrite (#30).
//!
//! Bridges the gap between pure IR transformations and encodable
//! [`abcd_file::File`] containers in two modes:
//!
//! 1. [`rewrite_file`]: lowers all functions of `module` onto a clone of an
//!    existing `base_file`, preserving untouched container metadata while
//!    materializing any newly introduced [`Sym`] strings, [`Const`] literal
//!    arrays, classes, or helper functions into the output [`File`].
//! 2. [`lower_module`] / [`lower_module_with_options`]: standalone lowering
//!    from `&abcd_ir::Module` + [`abcd_file::Version`] directly to a complete,
//!    encodable [`abcd_file::File`] with zero source `File` dependency.

use std::collections::{BTreeMap, HashMap};

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Annotations, Class, ColumnEntry,
    Field, FieldValue, File, FileType, FunctionKind as FileFunctionKind, LineEntry, LiteralArray,
    LiteralArrayIdx, LiteralValue, Method, MethodBody, MethodDebugInfo, ModuleData, ModuleRecord,
    ModuleRequestPhase, ParamAnnotations, ParamInfo, SourceLang as FileSourceLang, StringId,
    StringPool, Type, Version,
};
use abcd_ir::{
    AnnValue, ClassData, ClassId, Const, ConstId, ExportDecl, FieldData, FuncId,
    FunctionKind as IrFunctionKind, ImportDecl, InstId, Modifiers, Module, ModuleRequest,
    SourceLang as IrSourceLang, StaticTy, Sym, Ty,
};
use abcd_isa::EntityKind;
use rayon::prelude::*;

use crate::layout::LayoutResult;
use crate::method_body::EntityResolver;
use crate::{LowerError, LowerOptions, lower_function_with_options};

const SLOT_NUMBER_ANN_DESC: &str = "L_ESSlotNumberAnnotation;";
const SLOT_NUMBER_ELEM: &str = "SlotNumber";

/// Rewrite `base_file` with lowered bodies from `module`, materializing any
/// IR-synthesized strings, literal arrays, classes, and functions into the
/// returned [`File`] (#30).
///
/// Invalid/dangling entity IDs (`Sym` outside `module.sym`, `FuncId` outside
/// `module.functions`, `ConstId` outside `module.consts` or non-shape
/// constants in `LiteralarrayId` slots) still fail loudly with
/// [`LowerError::UntraceableEntity`].
pub fn rewrite_file(
    module: &Module,
    base_file: &File,
    options: LowerOptions,
) -> Result<File, LowerError> {
    let layouts = lower_all_layouts(module, options)?;
    let mut out = base_file.clone();
    let mut next_offset = initial_synth_offset(&out);

    // Map existing methods in `all_methods()` order (= lift reservation order).
    let base_method_locs: Vec<(StringId, usize, u32)> = out
        .classes
        .iter()
        .flat_map(|(&desc_sid, cls)| {
            cls.methods
                .iter()
                .enumerate()
                .map(move |(mi, m)| (desc_sid, mi, m.offset))
        })
        .collect();

    // Ensure every class in `module.classes` exists in `out.classes`.
    let mut class_desc_sids: Vec<StringId> = Vec::with_capacity(module.classes.len());
    for cls_data in &module.classes {
        let desc_sid = intern_sym(&module.sym, &mut out.strings, cls_data.descriptor).ok_or(
            LowerError::UntraceableEntity {
                func: FuncId::new(0),
                kind: EntityKind::StringId,
                raw: cls_data.descriptor.0,
            },
        )?;
        out.classes.entry(desc_sid).or_insert_with(|| {
            let name_sid =
                intern_sym(&module.sym, &mut out.strings, cls_data.name).unwrap_or(desc_sid);
            Class {
                descriptor: desc_sid,
                name: name_sid,
                access_flags: modifiers_to_access_flags(cls_data.modifiers),
                source_lang: source_lang_to_file(cls_data.source_lang),
                source_file: cls_data
                    .source_file
                    .and_then(|sf| intern_sym(&module.sym, &mut out.strings, sf)),
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: Vec::new(),
                fields: Vec::new(),
                annotations: Annotations::default(),
            }
        });
        class_desc_sids.push(desc_sid);
    }

    // Track `(class_desc_sid, method_idx_in_class)` and offset for every `FuncId`.
    let mut func_slots: Vec<(StringId, usize)> = Vec::with_capacity(module.functions.len());
    let mut method_offsets: Vec<u32> = Vec::with_capacity(module.functions.len());

    for (fi, func_data) in module.functions.iter().enumerate() {
        if let Some(&(desc_sid, mi, mut off)) = base_method_locs.get(fi) {
            if off == 0 {
                off = alloc_offset(&mut next_offset);
                if let Some(cls) = out.classes.get_mut(&desc_sid)
                    && let Some(m) = cls.methods.get_mut(mi)
                {
                    m.offset = off;
                }
            }
            func_slots.push((desc_sid, mi));
            method_offsets.push(off);
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
            let off = alloc_offset(&mut next_offset);
            let synth_method = build_synthesized_method(module, func_data, &mut out, off)?;
            out.entity_map.insert(off, synth_method.name);
            let cls = out.classes.get_mut(&desc_sid).expect("class exists");
            let mi = cls.methods.len();
            cls.methods.push(synth_method);
            func_slots.push((desc_sid, mi));
            method_offsets.push(off);
        }
    }

    let base_resolver = EntityResolver::new(module, &out);
    let mut materializer = Materializer::new(module, &mut out, &method_offsets, next_offset);

    let mut bodies: Vec<Option<MethodBody>> = Vec::with_capacity(layouts.len());
    for (fi, layout_opt) in layouts.into_iter().enumerate() {
        let func_id = FuncId::new(fi as u32);
        let Some(layout) = layout_opt else {
            bodies.push(None);
            continue;
        };
        let body = materializer.build_method_body(func_id, &layout, Some(&base_resolver))?;
        bodies.push(Some(body));
    }

    let need_slot_ann_record = bodies.iter().flatten().any(|b| b.ic_size.unwrap_or(0) > 0);
    let slot_ann_sids = if need_slot_ann_record {
        Some(ensure_slot_number_ann_record(&mut out))
    } else {
        None
    };

    for (fi, body_opt) in bodies.into_iter().enumerate() {
        let Some(body) = body_opt else {
            continue;
        };
        let (desc_sid, mi) = func_slots[fi];
        if let Some(cls) = out.classes.get_mut(&desc_sid)
            && let Some(m) = cls.methods.get_mut(mi)
        {
            if let (Some(ic), Some((ann_desc, elem_name))) = (body.ic_size, slot_ann_sids)
                && ic > 0
            {
                ensure_method_slot_annotation(&mut m.annotations, ann_desc, elem_name, ic);
            }
            m.body = Some(body);
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

/// Standalone whole-module lowering with explicit [`LowerOptions`] (#30).
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
        literal_array_offsets: HashMap::new(),
        literal_array_header_offsets: Vec::new(),
        entity_map: HashMap::new(),
    };
    let mut next_offset: u32 = 0x10_0000;

    // 1. Pre-allocate class descriptors and deterministic method/field offsets.
    let mut class_desc_sids: Vec<StringId> = Vec::with_capacity(module.classes.len());
    for (ci, cls_data) in module.classes.iter().enumerate() {
        let desc_sid = intern_sym(&module.sym, &mut file.strings, cls_data.descriptor).ok_or(
            LowerError::UntraceableEntity {
                func: FuncId::new(0),
                kind: EntityKind::StringId,
                raw: cls_data.descriptor.0,
            },
        )?;
        let cls_off = alloc_offset(&mut next_offset);
        file.entity_map.insert(cls_off, desc_sid);
        class_desc_sids.push(desc_sid);
        let _ = ci;
    }
    if class_desc_sids.is_empty() && !module.functions.is_empty() {
        class_desc_sids.push(ensure_global_class(&mut file));
    }

    let mut method_offsets: Vec<u32> = Vec::with_capacity(module.functions.len());
    for _ in 0..module.functions.len() {
        method_offsets.push(alloc_offset(&mut next_offset));
    }

    let mut field_offsets: Vec<Vec<u32>> = Vec::with_capacity(module.classes.len());
    for cls_data in &module.classes {
        let mut offs = Vec::with_capacity(cls_data.fields.len());
        for _ in 0..cls_data.fields.len() {
            offs.push(alloc_offset(&mut next_offset));
        }
        field_offsets.push(offs);
    }

    // 2. Build skeleton classes and fields.
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

        let mut fields = Vec::with_capacity(cls_data.fields.len());
        for (fi, fdata) in cls_data.fields.iter().enumerate() {
            let f_off = field_offsets[ci][fi];
            let f_sid = intern_sym(&module.sym, &mut file.strings, fdata.name).ok_or(
                LowerError::UntraceableEntity {
                    func: FuncId::new(0),
                    kind: EntityKind::StringId,
                    raw: fdata.name.0,
                },
            )?;
            file.entity_map.insert(f_off, f_sid);
            fields.push(build_field(
                module,
                fdata,
                f_sid,
                f_off,
                &class_desc_sids,
                &field_offsets,
                &mut file.strings,
            )?);
        }

        let cls_anns = build_annotations(
            module,
            &cls_data.annotations,
            &class_desc_sids,
            &field_offsets,
            &mut file.strings,
        )?;

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
                annotations: cls_anns,
            },
        );
    }

    // 3. Materialize lowered bodies and attach methods to their owning classes.
    // Note: in `File`, `classes` is a `BTreeMap<StringId, Class>`, so `all_methods()`
    // iterates classes in `StringId` order. To keep `FuncId` indices aligned with
    // `method_offsets[fi]`, each method stores its exact `method_offsets[fi]`, and
    // bytecode `MethodId` operands relocate through `method_offsets[target_fid]`.
    let mut lowered_bodies: Vec<Option<MethodBody>> = Vec::with_capacity(module.functions.len());
    {
        let mut materializer = Materializer::new(module, &mut file, &method_offsets, next_offset);
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
        // Materialize per-class `scope_names` and `es_module` fields if present.
        for (ci, cls_data) in module.classes.iter().enumerate() {
            let desc_sid = class_desc_sids[ci];
            if let Some(sn_cid) = cls_data.scope_names {
                let sn_off = materializer.literal_array_offset(sn_cid).ok_or(
                    LowerError::UntraceableEntity {
                        func: FuncId::new(0),
                        kind: EntityKind::LiteralarrayId,
                        raw: sn_cid.0,
                    },
                )?;
                let field_off = materializer.alloc_offset();
                let sn_name = materializer
                    .file
                    .strings
                    .get_or_intern(abcd_file::SCOPE_NAMES_FIELD);
                if let Some(cls) = materializer.file.classes.get_mut(&desc_sid) {
                    cls.fields.push(Field {
                        name: sn_name,
                        offset: field_off,
                        field_type: Type::U32,
                        access_flags: AccessFlags::STATIC,
                        is_external: false,
                        initial_value: Some(FieldValue::LiteralArrayRef(sn_off)),
                        annotations: Annotations::default(),
                    });
                }
            }
            if let Some(es_mod) = &cls_data.es_module {
                let (md, phase_opt) = build_module_data(
                    &module.sym,
                    &mut materializer.file.strings,
                    &es_mod.imports,
                    &es_mod.exports,
                    &es_mod.module_requests,
                )?;
                let mr_name = materializer
                    .file
                    .strings
                    .get_or_intern(abcd_file::MODULE_RECORD_IDX_FIELD);
                let mr_off = materializer.alloc_offset();
                let phase_entry = phase_opt.map(|ph| {
                    let pname = materializer
                        .file
                        .strings
                        .get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD);
                    let poff = materializer.alloc_offset();
                    (pname, poff, ph)
                });
                if let Some(cls) = materializer.file.classes.get_mut(&desc_sid) {
                    cls.fields.push(Field {
                        name: mr_name,
                        offset: mr_off,
                        field_type: Type::U32,
                        access_flags: AccessFlags::STATIC,
                        is_external: false,
                        initial_value: Some(FieldValue::ModuleData(md)),
                        annotations: Annotations::default(),
                    });
                    if let Some((pname, poff, ph)) = phase_entry {
                        cls.fields.push(Field {
                            name: pname,
                            offset: poff,
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
        next_offset = materializer.next_offset;
    }

    let need_slot_ann = lowered_bodies
        .iter()
        .flatten()
        .any(|b| b.ic_size.unwrap_or(0) > 0);
    let slot_ann_sids = if need_slot_ann {
        Some(ensure_slot_number_ann_record(&mut file))
    } else {
        None
    };

    for (fi, func_data) in module.functions.iter().enumerate() {
        let desc_sid = class_desc_sids
            .get(func_data.class_id.index())
            .copied()
            .ok_or(LowerError::UntraceableEntity {
                func: FuncId::new(fi as u32),
                kind: EntityKind::MethodId,
                raw: func_data.class_id.0,
            })?;
        let m_off = method_offsets[fi];
        let mut method = build_synthesized_method_full(
            module,
            func_data,
            layouts[fi].as_ref(),
            &class_desc_sids,
            &field_offsets,
            &mut file,
            m_off,
        )?;
        let body = lowered_bodies[fi].take();
        if let (Some(b), Some((ann_desc, elem_name))) = (&body, slot_ann_sids)
            && let Some(ic) = b.ic_size
            && ic > 0
        {
            ensure_method_slot_annotation(&mut method.annotations, ann_desc, elem_name, ic);
        }
        method.body = body;
        file.entity_map.insert(m_off, method.name);
        if let Some(cls) = file.classes.get_mut(&desc_sid) {
            cls.methods.push(method);
        }
    }

    // 4. Top-level standalone ES module record (`Module.imports` / `exports` / `module_requests`).
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
        let f_off = alloc_offset(&mut next_offset);
        let mut fields = vec![Field {
            name: field_name,
            offset: f_off,
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
            let ph_off = alloc_offset(&mut next_offset);
            fields.push(Field {
                name: ph_name,
                offset: ph_off,
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

    Ok(file)
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

fn initial_synth_offset(file: &File) -> u32 {
    let max_entity = file.entity_map.keys().copied().max().unwrap_or(0);
    let max_lit = file
        .literal_array_offsets
        .keys()
        .copied()
        .max()
        .unwrap_or(0);
    let max_method = file.all_methods().map(|(_, m)| m.offset).max().unwrap_or(0);
    let max_field = file
        .classes
        .values()
        .flat_map(|c| &c.fields)
        .map(|f| f.offset)
        .max()
        .unwrap_or(0);
    max_entity
        .max(max_lit)
        .max(max_method)
        .max(max_field)
        .max(0x10_0000)
        .saturating_add(0x1000)
}

#[inline]
fn alloc_offset(next: &mut u32) -> u32 {
    let off = *next;
    *next = next
        .checked_add(4)
        .expect("synthetic entity offset overflow");
    off
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

fn ensure_method_slot_annotation(
    anns: &mut Annotations,
    ann_desc: StringId,
    elem_name: StringId,
    ic_size: u32,
) {
    let has_existing = anns
        .compile_time
        .iter()
        .chain(&anns.runtime)
        .chain(&anns.compile_time_type)
        .chain(&anns.runtime_type)
        .any(|a| a.class_descriptor == ann_desc);
    if !has_existing {
        anns.compile_time.push(Annotation {
            class_descriptor: ann_desc,
            elements: vec![AnnotationElem {
                name: elem_name,
                value: AnnotationValue::U32(ic_size),
            }],
        });
    }
}

struct Materializer<'m, 'f> {
    module: &'m Module,
    file: &'f mut File,
    method_offsets: &'m [u32],
    next_offset: u32,
    string_offsets: HashMap<Box<[u8]>, u32>,
    synth_shape_offsets: HashMap<ConstId, u32>,
}

impl<'m, 'f> Materializer<'m, 'f> {
    fn new(
        module: &'m Module,
        file: &'f mut File,
        method_offsets: &'m [u32],
        next_offset: u32,
    ) -> Self {
        let mut string_offsets: HashMap<Box<[u8]>, u32> =
            HashMap::with_capacity(file.entity_map.len());
        let mut entries: Vec<(u32, StringId)> =
            file.entity_map.iter().map(|(&o, &s)| (o, s)).collect();
        entries.sort_unstable();
        for (off, sid) in entries {
            if let Some(bytes) = file.strings.to_mutf8_bytes(sid) {
                string_offsets
                    .entry(bytes.into_owned().into_boxed_slice())
                    .or_insert(off);
            }
        }
        Self {
            module,
            file,
            method_offsets,
            next_offset,
            string_offsets,
            synth_shape_offsets: HashMap::new(),
        }
    }

    fn alloc_offset(&mut self) -> u32 {
        alloc_offset(&mut self.next_offset)
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

        let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
        for bc in &result.bytecodes {
            for (kind, id) in bc.entity_operands() {
                let offset = match kind {
                    EntityKind::StringId => {
                        let sym = Sym::new(id.0);
                        if let Some(r) = base_resolver
                            && let Some(off) = r.string_offset(sym)
                        {
                            off
                        } else {
                            self.string_offset(sym)
                                .ok_or(LowerError::UntraceableEntity {
                                    func: func_id,
                                    kind,
                                    raw: id.0,
                                })?
                        }
                    }
                    EntityKind::MethodId => self.method_offset(FuncId::new(id.0)).ok_or(
                        LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        },
                    )?,
                    EntityKind::LiteralarrayId => {
                        let cid = ConstId::new(id.0);
                        if let Some(r) = base_resolver
                            && let Some(off) = r.literal_array_offset(cid)
                        {
                            off
                        } else {
                            self.literal_array_offset(cid)
                                .ok_or(LowerError::UntraceableEntity {
                                    func: func_id,
                                    kind,
                                    raw: id.0,
                                })?
                        }
                    }
                };
                entity_offsets.insert((kind, id.0), offset);
            }
        }

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            bytecodes: result.bytecodes.clone(),
            entity_offsets,
            try_blocks: result.try_blocks.clone(),
            ic_size: Some(result.ic_size),
        })
    }

    fn string_offset(&mut self, sym: Sym) -> Option<u32> {
        let bytes = self.module.sym.to_mutf8_bytes(sym)?.into_owned();
        if let Some(&off) = self.string_offsets.get(bytes.as_slice()) {
            return Some(off);
        }
        let sid = intern_sym(&self.module.sym, &mut self.file.strings, sym)?;
        let off = self.alloc_offset();
        self.file.entity_map.insert(off, sid);
        self.string_offsets.insert(bytes.into_boxed_slice(), off);
        Some(off)
    }

    fn method_offset(&self, func: FuncId) -> Option<u32> {
        self.method_offsets.get(func.index()).copied()
    }

    fn literal_array_offset(&mut self, shape: ConstId) -> Option<u32> {
        if let Some(&off) = self.synth_shape_offsets.get(&shape) {
            return Some(off);
        }
        let tree = self.module.consts.get(shape)?.clone();
        let (_idx, off) = self.materialize_shape_tree(&tree, 0)?;
        self.synth_shape_offsets.insert(shape, off);
        Some(off)
    }

    fn materialize_shape_tree(&mut self, tree: &Const, depth: u32) -> Option<(u32, u32)> {
        if depth > 64 {
            return None;
        }
        let values = match tree {
            Const::ArrayLiteral(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(self.materialize_literal_elem(item, depth)?);
                }
                out
            }
            Const::ObjectLiteral { keys, values } => {
                if keys.len() != values.len() {
                    return None;
                }
                let mut out = Vec::with_capacity(keys.len() * 2);
                for (k, v) in keys.iter().zip(values.iter()) {
                    out.push(self.materialize_literal_elem(k, depth)?);
                    out.push(self.materialize_literal_elem(v, depth)?);
                }
                out
            }
            _ => return None,
        };
        let idx = self.file.literal_arrays.len() as u32;
        let off = self.alloc_offset();
        self.file.literal_arrays.push(LiteralArray { values });
        self.file.literal_array_offsets.insert(off, idx);
        Some((idx, off))
    }

    fn materialize_literal_elem(&mut self, c: &Const, depth: u32) -> Option<LiteralValue> {
        Some(match c {
            Const::Bool(b) => LiteralValue::Bool(*b),
            Const::Null | Const::Undefined | Const::Hole => LiteralValue::NullValue(0),
            Const::Number(bits) => {
                let v = f64::from_bits(*bits);
                if *bits != (-0.0f64).to_bits()
                    && v.is_finite()
                    && (v as i32 as f64).to_bits() == *bits
                {
                    LiteralValue::Integer((v as i32) as u32)
                } else {
                    LiteralValue::Double(v)
                }
            }
            Const::String(sym) | Const::BigInt(sym) => {
                let sid = intern_sym(&self.module.sym, &mut self.file.strings, *sym)?;
                LiteralValue::String(sid)
            }
            Const::MethodRef(fid) => {
                let off = self.method_offset(*fid)?;
                let kind = self.module.func(*fid).map(|f| f.kind)?;
                match kind {
                    IrFunctionKind::Generator => LiteralValue::GeneratorMethod(off),
                    IrFunctionKind::AsyncGenerator => LiteralValue::AsyncGeneratorMethod(off),
                    IrFunctionKind::Getter => LiteralValue::Getter(off),
                    IrFunctionKind::Setter => LiteralValue::Setter(off),
                    _ => LiteralValue::Method(off),
                }
            }
            nested @ (Const::ArrayLiteral(_) | Const::ObjectLiteral { .. }) => {
                let (child_idx, _) = self.materialize_shape_tree(nested, depth + 1)?;
                LiteralValue::LiteralArray(LiteralArrayIdx(child_idx))
            }
        })
    }
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

fn source_lang_to_file(_lang: IrSourceLang) -> FileSourceLang {
    FileSourceLang::EcmaScript
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

fn build_synthesized_method(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    file: &mut File,
    offset: u32,
) -> Result<Method, LowerError> {
    let name = intern_sym(&module.sym, &mut file.strings, func_data.name).ok_or(
        LowerError::UntraceableEntity {
            func: FuncId::new(0),
            kind: EntityKind::StringId,
            raw: func_data.name.0,
        },
    )?;
    let mut flags = modifiers_to_access_flags(func_data.modifiers);
    if flags.is_empty() {
        flags = AccessFlags::PUBLIC | AccessFlags::STATIC;
    }
    let arg_types = vec![Type::Tagged; func_data.params.len()];
    Ok(Method {
        name,
        offset,
        access_flags: flags,
        function_kind: function_kind_to_file(func_data.kind),
        source_lang: FileSourceLang::EcmaScript,
        is_external: func_data.is_external,
        return_type: Some(Type::Tagged),
        arg_types,
        body: None,
        annotations: Annotations::default(),
        param_annotations: ParamAnnotations::default(),
        debug: None,
    })
}

fn build_synthesized_method_full(
    module: &Module,
    func_data: &abcd_ir::FunctionData,
    _layout: Option<&LayoutResult>,
    class_desc_sids: &[StringId],
    field_offsets: &[Vec<u32>],
    file: &mut File,
    offset: u32,
) -> Result<Method, LowerError> {
    let name = intern_sym(&module.sym, &mut file.strings, func_data.name).ok_or(
        LowerError::UntraceableEntity {
            func: FuncId::new(0),
            kind: EntityKind::StringId,
            raw: func_data.name.0,
        },
    )?;
    let mut flags = modifiers_to_access_flags(func_data.modifiers);
    if flags.is_empty() && !func_data.is_external {
        flags = AccessFlags::PUBLIC | AccessFlags::STATIC;
    }
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
    let annotations = build_annotations(
        module,
        &func_data.annotations,
        class_desc_sids,
        field_offsets,
        &mut file.strings,
    )?;
    let debug = func_data
        .debug
        .as_ref()
        .map(|dbg| build_debug_info(module, dbg, &mut file.strings));

    Ok(Method {
        name,
        offset,
        access_flags: flags,
        function_kind: function_kind_to_file(func_data.kind),
        source_lang: FileSourceLang::EcmaScript,
        is_external: func_data.is_external,
        return_type,
        arg_types,
        body: None,
        annotations,
        param_annotations: ParamAnnotations::default(),
        debug,
    })
}

fn build_debug_info(
    module: &Module,
    dbg: &abcd_ir::DebugData,
    strings: &mut StringPool,
) -> MethodDebugInfo {
    let source_file = dbg
        .source_file
        .and_then(|sf| intern_sym(&module.sym, strings, sf));
    let source_code = dbg
        .source_code
        .as_deref()
        .filter(|s| !s.is_empty())
        .map(|s| strings.get_or_intern(s));
    // Standalone lowering has no bytecode-index map per InstId; preserve line/column
    // metadata conservatively at instruction index 0 when non-empty, plus exact params.
    let _ = InstId::new(0);
    let line_table: Vec<LineEntry> = dbg
        .line_table
        .first()
        .map(|e| {
            vec![LineEntry {
                index: 0,
                line: e.line,
            }]
        })
        .unwrap_or_default();
    let column_table: Vec<ColumnEntry> = dbg
        .column_table
        .first()
        .map(|e| {
            vec![ColumnEntry {
                index: 0,
                column: e.column,
            }]
        })
        .unwrap_or_default();
    let empty_sig = strings.get_or_intern("");
    let params: Vec<ParamInfo> = dbg
        .param_names
        .iter()
        .filter_map(|&p| {
            let name = intern_sym(&module.sym, strings, p)?;
            Some(ParamInfo {
                name,
                signature: empty_sig,
            })
        })
        .collect();
    MethodDebugInfo {
        source_file,
        source_code,
        line_table,
        column_table,
        local_vars: Vec::new(),
        params,
    }
}

fn build_field(
    module: &Module,
    fdata: &FieldData,
    name: StringId,
    offset: u32,
    class_desc_sids: &[StringId],
    field_offsets: &[Vec<u32>],
    strings: &mut StringPool,
) -> Result<Field, LowerError> {
    let field_type = ty_to_file(&fdata.ty, class_desc_sids);
    let initial_value = match fdata.initial_value.and_then(|cid| module.consts.get(cid)) {
        Some(Const::Bool(b)) => Some(FieldValue::I32(i32::from(*b))),
        Some(Const::Number(bits)) => {
            let v = f64::from_bits(*bits);
            match field_type {
                Type::F32 => Some(FieldValue::F32(v as f32)),
                Type::F64 => Some(FieldValue::F64(v)),
                Type::I64 | Type::U64 => Some(FieldValue::I64(v as i64)),
                _ => Some(FieldValue::I32(v as i32)),
            }
        }
        Some(Const::String(sym))
            if module.sym.as_str(fdata.name) == Some(abcd_file::JSON_FILE_CONTENT_FIELD) =>
        {
            intern_sym(&module.sym, strings, *sym).map(|content| FieldValue::JsonFileContent {
                source_offset: 0,
                content,
            })
        }
        _ => None,
    };
    let annotations = build_annotations(
        module,
        &fdata.annotations,
        class_desc_sids,
        field_offsets,
        strings,
    )?;
    Ok(Field {
        name,
        offset,
        field_type,
        access_flags: modifiers_to_access_flags(fdata.modifiers),
        is_external: false,
        initial_value,
        annotations,
    })
}

fn build_annotations(
    module: &Module,
    anns: &[abcd_ir::Annotation],
    class_desc_sids: &[StringId],
    field_offsets: &[Vec<u32>],
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
            if let Some(value) =
                ann_value_to_file(module, eval, class_desc_sids, field_offsets, strings)
            {
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
    field_offsets: &[Vec<u32>],
    strings: &mut StringPool,
) -> Option<AnnotationValue> {
    match val {
        AnnValue::Const(cid) => {
            match module.consts.get(*cid)? {
                Const::Bool(b) => Some(AnnotationValue::Bool(*b)),
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
                Const::Null => Some(AnnotationValue::StringNullptr),
                _ => None,
            }
        }
        AnnValue::Class(cid) => Some(AnnotationValue::Record(*class_desc_sids.get(cid.index())?)),
        AnnValue::Field(cid, fid) => {
            let fdata = module.classes.get(cid.index())?.fields.get(fid.index())?;
            let name = intern_sym(&module.sym, strings, fdata.name)?;
            let offset = *field_offsets.get(cid.index())?.get(fid.index())?;
            Some(AnnotationValue::Enum { name, offset })
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

#[allow(dead_code)]
const _: fn(ClassId) = |_| {};

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::{Block, FunctionData, Inst, Op, Value, ValueDef, ValueId, verify_module};

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

        // Function 0: func_main_0
        let mut f0 = FunctionData::new(ClassId::new(0), main_name, IrFunctionKind::Function);
        f0.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let b0 = abcd_ir::BlockId::new(0);
        m.blocks.push(Block::default());
        f0.blocks.push(b0);

        // Function 1: helper
        let mut f1 = FunctionData::new(ClassId::new(0), helper_name, IrFunctionKind::Function);
        f1.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let b1 = abcd_ir::BlockId::new(1);
        m.blocks.push(Block::default());
        f1.blocks.push(b1);

        // helper returns a lone-surrogate string constant!
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

        // func_main_0 allocates an array `[1, "\u{E000}icon"]`, defines `helper`, and returns it.
        let pua_sym = m.sym.intern("\u{E000}icon");
        let arr_shape = m.consts.push(Const::ArrayLiteral(vec![
            Const::number(1.0),
            Const::String(pua_sym),
        ]));
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

        // Append a brand-new synthetic helper function + brand-new string + brand-new literal array!
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

        // Rewrite `func_main_0` to allocate a brand-new `[42]` literal array and reference `synth_helper`.
        let main_bb = module.functions[0].blocks[0];
        module.blocks[main_bb.index()].insts.clear();
        let arr_cid = module
            .consts
            .push(Const::ArrayLiteral(vec![Const::number(42.0)]));
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
}
