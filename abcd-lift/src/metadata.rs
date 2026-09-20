//! Metadata conversion: classes, fields, annotations, signatures,
//! types, debug info, and module records.
//!
//! Contracts implemented here (design/ir.md §6–§7):
//!
//! - **Annotations**: the four file buckets merge into ONE list per
//!   attach site, in the documented order `compile_time`, `runtime`,
//!   `compile_time_type`, `runtime_type` (the #9 fold; lowering folds
//!   back per FormatProfile — not IR content).
//! - **Types**: file `Type` → the dynamic-first `Ty` lattice;
//!   `Type::Reference` resolves through the module's own class table
//!   (N46 impossible by construction). `Tagged` → `Ty::Any`.
//! - **Debug**: LNP dual stream → [`DebugData`]; line/column keyed by
//!   the lifted [`InstId`]s; local names keep their #5 scope extents
//!   (mapped onto lifted instructions); `_ESScopeNamesRecord` fields
//!   attach to the functions whose `source_file` matches the field
//!   name (the record is keyed by source FILE, not by function —
//!   documented).
//! - **Modules**: `_ESModuleRecord` blobs →
//!   [`ImportDecl`]/[`ExportDecl`] with `module_request_idx` resolved
//!   to specifier syms; `moduleRequestPhaseIdx` blobs → per-request
//!   lazy flags on [`ModuleRequest`].

use abcd_file::{
    self, AccessFlags, AnnotationValue, Class, Field, Method, ModuleData, ModuleRecord, Type,
};
use abcd_ir2::{
    AnnValue, Annotation, ClassData, ClassId, Const, ExportDecl, FieldData, FieldId, FunctionKind,
    ImportDecl, LineEntry, LocalName, LocalScope, Modifiers, ModuleRequest, Signature, SourceLang,
    StaticTy, Sym, Ty, ValueId,
};

use crate::resolve;
use crate::translate::FnLift;
use crate::{LiftError, Lifter};

/// Map file access flags to the semantic modifier set (JVM-legacy bits
/// with no JS/TS meaning are dropped — documented).
pub fn modifiers(flags: AccessFlags) -> Modifiers {
    let mut m = Modifiers::NONE;
    if flags.contains(AccessFlags::PUBLIC) {
        m |= Modifiers::PUBLIC;
    }
    if flags.contains(AccessFlags::PRIVATE) {
        m |= Modifiers::PRIVATE;
    }
    if flags.contains(AccessFlags::PROTECTED) {
        m |= Modifiers::PROTECTED;
    }
    if flags.contains(AccessFlags::STATIC) {
        m |= Modifiers::STATIC;
    }
    if flags.contains(AccessFlags::FINAL) {
        m |= Modifiers::FINAL;
    }
    if flags.contains(AccessFlags::ABSTRACT) {
        m |= Modifiers::ABSTRACT;
    }
    if flags.contains(AccessFlags::INTERFACE) {
        m |= Modifiers::INTERFACE;
    }
    if flags.contains(AccessFlags::ENUM) {
        m |= Modifiers::ENUM;
    }
    if flags.contains(AccessFlags::ANNOTATION) {
        m |= Modifiers::ANNOTATION;
    }
    m
}

/// Map the file's source language (JavaScript folds into EcmaScript;
/// PandaAssembly has no semantic home and defaults to EcmaScript —
/// both documented).
pub fn source_lang(lang: abcd_file::SourceLang) -> SourceLang {
    match lang {
        abcd_file::SourceLang::EcmaScript
        | abcd_file::SourceLang::JavaScript
        | abcd_file::SourceLang::PandaAssembly => SourceLang::EcmaScript,
        abcd_file::SourceLang::TypeScript => SourceLang::TypeScript,
        abcd_file::SourceLang::ArkTs => SourceLang::ArkTS,
    }
}

/// Semantic function kind: the CONSTRUCTOR access flag selects
/// `Constructor`; the file's `FunctionKind` selects the generator/async
/// families. Getter/Setter have no signal in the file model and map to
/// `Function` (documented gap).
pub fn function_kind(method: &Method) -> FunctionKind {
    if method.access_flags.contains(AccessFlags::CONSTRUCTOR) {
        return FunctionKind::Constructor;
    }
    match method.function_kind {
        abcd_file::FunctionKind::GeneratorFunction => FunctionKind::Generator,
        abcd_file::FunctionKind::AsyncFunction | abcd_file::FunctionKind::AsyncNcFunction => {
            FunctionKind::Async
        }
        abcd_file::FunctionKind::AsyncGeneratorFunction => FunctionKind::AsyncGenerator,
        abcd_file::FunctionKind::None
        | abcd_file::FunctionKind::Function
        | abcd_file::FunctionKind::NcFunction
        | abcd_file::FunctionKind::ConcurrentFunction
        | abcd_file::FunctionKind::SendableFunction => FunctionKind::Function,
    }
}

/// File `Type` → v0.2 `Ty`. `Type::Reference` resolves through the
/// module's class table (stub-appending foreign descriptors — the same
/// policy as annotation classes); an unresolvable descriptor degrades
/// to `Ty::Any` (documented).
pub fn ty_of(lf: &mut Lifter, ty: &Type) -> Ty {
    match ty {
        Type::Void => Ty::Static(StaticTy::Void),
        Type::Bool => Ty::Static(StaticTy::U1),
        Type::I8 => Ty::Static(StaticTy::I8),
        Type::U8 => Ty::Static(StaticTy::U8),
        Type::I16 => Ty::Static(StaticTy::I16),
        Type::U16 => Ty::Static(StaticTy::U16),
        Type::I32 => Ty::Static(StaticTy::I32),
        Type::U32 => Ty::Static(StaticTy::U32),
        Type::I64 => Ty::Static(StaticTy::I64),
        Type::U64 => Ty::Static(StaticTy::U64),
        Type::F32 => Ty::Static(StaticTy::F32),
        Type::F64 => Ty::Static(StaticTy::F64),
        Type::Tagged => Ty::Any,
        Type::Reference(sid) => match lf.class_of_descriptor(*sid) {
            Some(cid) => Ty::Static(StaticTy::Reference(cid)),
            None => Ty::Any,
        },
    }
}

/// The declared signature, when the source carried one (format fact
/// #A7: absent on 12+/24 — the IR reflects reality).
pub fn signature(lf: &mut Lifter, method: &Method) -> Option<Signature> {
    if method.return_type.is_none() && method.arg_types.is_empty() {
        return None;
    }
    Some(Signature {
        return_ty: method.return_type.as_ref().map(|t| ty_of(lf, t)),
        param_tys: method.arg_types.iter().map(|t| ty_of(lf, t)).collect(),
    })
}

/// Parameters of a body-less external declaration: the proto's declared
/// argument types (on 12+ files there is no shorty — zero params;
/// documented).
pub fn external_params(lf: &mut Lifter, method: &Method) -> Vec<ValueId> {
    let mut params = Vec::with_capacity(method.arg_types.len());
    for (i, ty) in method.arg_types.iter().enumerate() {
        let ty = ty_of(lf, ty);
        let val = ValueId::new(lf.module.values.len() as u32);
        lf.module.values.push(abcd_ir2::Value {
            def: abcd_ir2::ValueDef::Param(i as u16),
            ty,
        });
        params.push(val);
    }
    params
}

/// Lift a class and its fields/methods into the module, returning its
/// (reserved) class-table index.
pub fn lift_class<'f>(lf: &mut Lifter<'f>, class: &'f Class) -> Result<ClassId, LiftError> {
    let Some(&class_id) = lf.class_to_id.get(&class.descriptor) else {
        return Err(LiftError::UnresolvedEntity(0));
    };
    let Some(&func_base) = lf.func_bases.get(&class.descriptor) else {
        return Err(LiftError::UnresolvedEntity(0));
    };
    let descriptor = lf
        .sym_of_file_sid(class.descriptor)
        .ok_or(LiftError::UnresolvedEntity(0))?;
    let name = lf.sym_of_file_sid(class.name).unwrap_or(descriptor);
    let source_file = class.source_file.and_then(|s| lf.sym_of_file_sid(s));
    let super_class = class.super_class.and_then(|s| lf.class_of_descriptor(s));
    let interfaces: Vec<ClassId> = class
        .interfaces
        .iter()
        .filter_map(|&s| lf.class_of_descriptor(s))
        .collect();

    let mut fields = Vec::with_capacity(class.fields.len());
    for f in &class.fields {
        fields.push(lift_field(lf, f)?);
    }
    let annotations = lift_annotations(lf, &class.annotations);

    let mut method_ids = Vec::with_capacity(class.methods.len());
    for (mi, method) in class.methods.iter().enumerate() {
        // FuncIds were reserved in pass 1 in this exact order (base +
        // declaration index — exact even for hand-built files with
        // duplicate method offsets).
        let func_id = abcd_ir2::FuncId::new(func_base + mi as u32);
        crate::lift_method(lf, class_id, method, func_id)?;
        method_ids.push(func_id);
    }

    // Assign into the reserved slot (pass 1 pre-filled a shell).
    lf.module.classes[class_id.index()] = ClassData {
        descriptor,
        name,
        modifiers: modifiers(class.access_flags),
        source_lang: source_lang(class.source_lang),
        super_class,
        interfaces,
        fields,
        methods: method_ids,
        annotations,
        source_file,
    };
    Ok(class_id)
}

/// Lift a class field; module-record/scope-names/lazy-flag blobs are
/// collected into the lifter's side channels (they become module-level
/// declarations in [`emit_module_records`]).
fn lift_field<'f>(lf: &mut Lifter<'f>, field: &'f Field) -> Result<FieldData, LiftError> {
    let name = lf
        .sym_of_file_sid(field.name)
        .ok_or(LiftError::UnresolvedEntity(0))?;
    let ty = ty_of(lf, &field.field_type);
    let initial_value = match &field.initial_value {
        Some(abcd_file::FieldValue::I32(v)) => Some(lf.const_scalar(Const::number(*v as f64))),
        Some(abcd_file::FieldValue::I64(v)) => Some(lf.const_scalar(Const::number(*v as f64))),
        Some(abcd_file::FieldValue::F32(v)) => Some(lf.const_scalar(Const::number(*v as f64))),
        Some(abcd_file::FieldValue::F64(v)) => Some(lf.const_scalar(Const::number(*v))),
        Some(abcd_file::FieldValue::ModuleData(md)) => {
            lf.module_datas.push(md);
            None
        }
        Some(abcd_file::FieldValue::ModuleRequestPhase(phase)) => {
            lf.module_phases.push(phase);
            None
        }
        Some(abcd_file::FieldValue::LiteralArrayRef(offset)) => {
            // `_ESScopeNamesRecord` field: the field NAME is the source
            // file, the blob a scope-names literal array (offset form —
            // resolve like the N52 typed-array payloads).
            let idx = lf
                .file
                .literal_array_offsets
                .get(offset)
                .copied()
                .ok_or(LiftError::UnresolvedEntity(*offset))?;
            let konst = resolve::const_for_literal_array(lf, idx)?;
            lf.scope_name_fields.push((name, konst));
            None
        }
        None => None,
    };
    Ok(FieldData {
        name,
        ty,
        modifiers: modifiers(field.access_flags),
        initial_value,
        annotations: lift_annotations(lf, &field.annotations),
    })
}

/// Lift one bucket list of file annotations.
fn lift_annotation_list(
    lf: &mut Lifter,
    list: &[abcd_file::Annotation],
    out: &mut Vec<Annotation>,
) {
    for a in list {
        let Some(class_id) = lf.class_of_descriptor(a.class_descriptor) else {
            continue; // dangling descriptor (hand-built) — documented skip
        };
        let mut elements = Vec::with_capacity(a.elements.len());
        for e in &a.elements {
            let Some(name) = lf.sym_of_file_sid(e.name) else {
                continue;
            };
            elements.push((name, annotation_value(lf, &e.value)));
        }
        out.push(Annotation {
            class: class_id,
            elements,
        });
    }
}

/// Merge the four file buckets into ONE annotation list, in the
/// documented order: `compile_time`, `runtime`, `compile_time_type`,
/// `runtime_type`.
pub fn lift_annotations(lf: &mut Lifter, anns: &abcd_file::Annotations) -> Vec<Annotation> {
    let mut out = Vec::new();
    lift_annotation_list(lf, &anns.compile_time, &mut out);
    lift_annotation_list(lf, &anns.runtime, &mut out);
    lift_annotation_list(lf, &anns.compile_time_type, &mut out);
    lift_annotation_list(lf, &anns.runtime_type, &mut out);
    out
}

/// Convert an annotation element value to an [`AnnValue`] (elements
/// reference only IR-owned identities: Const / ClassId / FieldId /
/// Sym).
fn annotation_value(lf: &mut Lifter, v: &AnnotationValue) -> AnnValue {
    let number = |lf: &mut Lifter, x: f64| AnnValue::Const(lf.const_scalar(Const::number(x)));
    match v {
        AnnotationValue::Bool(b) => AnnValue::Const(lf.const_scalar(Const::Bool(*b))),
        AnnotationValue::I8(x) => number(lf, *x as f64),
        AnnotationValue::U8(x) => number(lf, *x as f64),
        AnnotationValue::I16(x) => number(lf, *x as f64),
        AnnotationValue::U16(x) => number(lf, *x as f64),
        AnnotationValue::I32(x) => number(lf, *x as f64),
        AnnotationValue::U32(x) => number(lf, *x as f64),
        AnnotationValue::I64(x) => number(lf, *x as f64),
        AnnotationValue::U64(x) => number(lf, *x as f64),
        AnnotationValue::F32(x) => number(lf, *x as f64),
        AnnotationValue::F64(x) => number(lf, *x),
        AnnotationValue::String(sid) => {
            let sym = lf.sym_of_file_sid(*sid);
            match sym {
                Some(s) => AnnValue::Const(lf.const_scalar(Const::String(s))),
                None => AnnValue::Const(lf.const_scalar(Const::Null)),
            }
        }
        AnnotationValue::Record(sid) => match lf.class_of_descriptor(*sid) {
            Some(cid) => AnnValue::Class(cid),
            None => AnnValue::Const(lf.const_scalar(Const::Null)),
        },
        // Method references are constants in the module pool
        // (Const::MethodRef — the same identity path as bytecode method
        // references; unresolvable offsets degrade to the display name,
        // documented for hand-built models).
        AnnotationValue::Method { name, offset } => match resolve::func_of_offset(lf, *offset) {
            Ok(fid) => AnnValue::Const(lf.const_shape(Const::MethodRef(fid))),
            Err(_) => {
                let sym = lf
                    .sym_of_file_sid(*name)
                    .unwrap_or_else(|| lf.sym("<unresolved>"));
                AnnValue::Name(sym)
            }
        },
        AnnotationValue::Enum { name, offset } => match lf.field_to_id.get(offset).copied() {
            Some((cid, fi)) => AnnValue::Field(cid, FieldId::new(fi)),
            None => {
                let sym = lf
                    .sym_of_file_sid(*name)
                    .unwrap_or_else(|| lf.sym("<unresolved>"));
                AnnValue::Name(sym)
            }
        },
        // Nested annotations have no AnnValue home in v0.2: represent
        // by the nested annotation's CLASS (its element list is
        // unrepresentable — registered taxonomy gap).
        AnnotationValue::Annotation(nested) => {
            match lf.class_of_descriptor(nested.class_descriptor) {
                Some(cid) => AnnValue::Class(cid),
                None => AnnValue::Const(lf.const_scalar(Const::Null)),
            }
        }
        // Method handles have no AnnValue home (registered gap): keep
        // the entity name.
        AnnotationValue::MethodHandle(rmh) => {
            let sym = lf
                .sym_of_file_sid(rmh.entity)
                .unwrap_or_else(|| lf.sym("<unresolved>"));
            AnnValue::Name(sym)
        }
        AnnotationValue::LiteralArray(values) => {
            let mut consts = Vec::with_capacity(values.len());
            for v in values {
                match resolve::const_for_literal_value(lf, v) {
                    Ok(c) => consts.push(c),
                    Err(_) => consts.push(Const::Null),
                }
            }
            AnnValue::Const(lf.const_shape(Const::ArrayLiteral(consts)))
        }
        AnnotationValue::Void => AnnValue::Const(lf.const_scalar(Const::Undefined)),
        AnnotationValue::StringNullptr => AnnValue::Const(lf.const_scalar(Const::Null)),
        AnnotationValue::Array { values, .. } => {
            // Typed element tag is not part of v0.2's Const
            // (documented); elements convert to constants, with
            // name-carrying payloads preserved as string constants
            // (documented policy).
            let consts = values
                .iter()
                .map(|v| annotation_value_as_const(lf, v))
                .collect();
            AnnValue::Const(lf.const_shape(Const::ArrayLiteral(consts)))
        }
    }
}

/// Convert an annotation value inside an annotation ARRAY to a
/// [`Const`] (scalars/strings/methods exact; name-carrying payloads as
/// string constants — documented).
fn annotation_value_as_const(lf: &mut Lifter, v: &AnnotationValue) -> Const {
    match v {
        AnnotationValue::Bool(b) => Const::Bool(*b),
        AnnotationValue::I8(x) => Const::number(*x as f64),
        AnnotationValue::U8(x) => Const::number(*x as f64),
        AnnotationValue::I16(x) => Const::number(*x as f64),
        AnnotationValue::U16(x) => Const::number(*x as f64),
        AnnotationValue::I32(x) => Const::number(*x as f64),
        AnnotationValue::U32(x) => Const::number(*x as f64),
        AnnotationValue::I64(x) => Const::number(*x as f64),
        AnnotationValue::U64(x) => Const::number(*x as f64),
        AnnotationValue::F32(x) => Const::number(*x as f64),
        AnnotationValue::F64(x) => Const::number(*x),
        AnnotationValue::String(sid)
        | AnnotationValue::Record(sid)
        | AnnotationValue::Enum { name: sid, .. } => match lf.sym_of_file_sid(*sid) {
            Some(s) => Const::String(s),
            None => Const::Null,
        },
        AnnotationValue::Method { name, offset } => match resolve::func_of_offset(lf, *offset) {
            Ok(fid) => Const::MethodRef(fid),
            Err(_) => match lf.sym_of_file_sid(*name) {
                Some(s) => Const::String(s),
                None => Const::Null,
            },
        },
        AnnotationValue::MethodHandle(rmh) => match lf.sym_of_file_sid(rmh.entity) {
            Some(s) => Const::String(s),
            None => Const::Null,
        },
        AnnotationValue::Annotation(nested) => match lf.sym_of_file_sid(nested.class_descriptor) {
            Some(s) => Const::String(s),
            None => Const::Null,
        },
        AnnotationValue::LiteralArray(values) => {
            let mut consts = Vec::with_capacity(values.len());
            for v in values {
                match resolve::const_for_literal_value(lf, v) {
                    Ok(c) => consts.push(c),
                    Err(_) => consts.push(Const::Null),
                }
            }
            Const::ArrayLiteral(consts)
        }
        AnnotationValue::Void => Const::Undefined,
        AnnotationValue::StringNullptr => Const::Null,
        AnnotationValue::Array { values, .. } => Const::ArrayLiteral(
            values
                .iter()
                .map(|v| annotation_value_as_const(lf, v))
                .collect(),
        ),
    }
}

/// Whether a decoded debug record is the N55 empty invention (decode
/// wraps a contentless `source_file: Some("")` for debug-less
/// methods). v0.2's lift treats the invention as "no debug info" (the
/// N55 decode wart is fixed at this boundary — documented).
fn debug_is_empty_invention(lf: &Lifter, debug: &abcd_file::MethodDebugInfo) -> bool {
    let empty_source = match debug.source_file {
        None => true,
        Some(sid) => lf.file.strings.resolve(sid).is_some_and(|s| s.is_empty()),
    };
    empty_source
        && debug.source_code.is_none()
        && debug.line_table.is_empty()
        && debug.column_table.is_empty()
        && debug.local_vars.is_empty()
        && debug.params.is_empty()
}

/// Assemble the function's [`abcd_ir2::DebugData`] after translation:
/// line/column tables keyed by the lifted InstIds, local names with
/// scope extents, param names, source file/code, and the home-record
/// scope names.
pub fn finish_debug(fx: &mut FnLift) {
    let Some(debug) = fx.method.debug.as_ref() else {
        return;
    };
    if debug_is_empty_invention(fx.lf, debug) {
        return;
    }

    let func_id = fx.func_id;
    let source_file = debug.source_file.and_then(|s| fx.lf.sym_of_file_sid(s));
    let source_code = debug
        .source_code
        .and_then(|s| fx.lf.file.strings.resolve(s).map(str::to_owned));

    // Line/column tables, keyed by the LIFTED InstIds (block order).
    let mut line_table = Vec::new();
    let mut column_table = Vec::new();
    // Ordered (inst, pc) list for the scope-extent mapping (phis carry
    // no source position and are skipped).
    let mut inst_pcs: Vec<(abcd_ir2::InstId, u32)> = Vec::new();
    let blocks = fx.lf.module.functions[func_id.index()].blocks.clone();
    for bb in &blocks {
        let insts = fx.lf.module.blocks[bb.index()].insts.clone();
        for iid in insts {
            let Some(&pc) = fx.inst_pc.get(&iid) else {
                continue;
            };
            inst_pcs.push((iid, pc));
            if let Some(line) = fx.line_of(pc) {
                line_table.push(LineEntry { inst: iid, line });
            }
            if let Some(column) = fx.column_of(pc) {
                column_table.push(abcd_ir2::ColumnEntry { inst: iid, column });
            }
        }
    }

    // Local names with their #5 scope extents mapped onto lifted
    // instructions (start = first lifted inst at-or-after the scope
    // start pc; end = last lifted inst at-or-before the scope end pc).
    let mut local_names: Vec<LocalName> = Vec::new();
    for lv in &debug.local_vars {
        let Some(name) = fx.lf.sym_of_file_sid(lv.name) else {
            continue;
        };
        let ty = local_var_ty(fx.lf, lv.type_signature);
        let start = inst_pcs
            .iter()
            .find(|(_, pc)| *pc >= lv.start)
            .map(|(iid, _)| *iid);
        let end = inst_pcs
            .iter()
            .rev()
            .find(|(_, pc)| *pc <= lv.end)
            .map(|(iid, _)| *iid);
        let scope = match (start, end) {
            (Some(start), Some(end)) if start.index() <= end.index() => {
                Some(LocalScope { start, end })
            }
            _ => None,
        };
        let entry = LocalName { name, ty, scope };
        if !local_names.contains(&entry) {
            local_names.push(entry);
        }
    }

    // Parameter names, in parameter order.
    let param_names: Vec<Sym> = debug
        .params
        .iter()
        .filter_map(|p| fx.lf.sym_of_file_sid(p.name))
        .collect();

    // The home record's scope names attach by source-FILE name (the
    // _ESScopeNamesRecord field name is the source file).
    let scope_names = source_file.and_then(|sf| {
        fx.lf
            .scope_name_fields
            .iter()
            .find(|(name, _)| *name == sf)
            .map(|(_, c)| *c)
    });

    fx.lf.module.functions[func_id.index()].debug = Some(abcd_ir2::DebugData {
        source_file,
        source_code,
        line_table,
        column_table,
        local_names,
        param_names,
        scope_names,
    });
}

/// Parse a local variable's type signature: primitive descriptors map
/// to static types; anything else is a class-table reference (or `None`
/// when the signature is empty/unresolvable — documented).
fn local_var_ty(lf: &mut Lifter, sig: abcd_file::StringId) -> Option<Ty> {
    let descriptor = lf.file.strings.resolve(sig)?;
    if descriptor.is_empty() {
        return None;
    }
    let ty = Type::from_descriptor(descriptor, sig);
    Some(ty_of(lf, &ty))
}

/// Convert the collected module-record blobs into the module's
/// imports/exports and per-request lazy flags.
pub fn emit_module_records(lf: &mut Lifter) -> Result<(), LiftError> {
    let module_datas: Vec<&ModuleData> = lf.module_datas.clone();
    for (ri, md) in module_datas.iter().enumerate() {
        // Per-request lazy flags: the phase blob paired with this
        // record (positional pairing; missing blob or short flag list →
        // eager, documented).
        let phase = lf.module_phases.get(ri).copied();
        for (qi, &req_sid) in md.requests.iter().enumerate() {
            let Some(specifier) = lf.sym_of_file_sid(req_sid) else {
                continue;
            };
            let lazy = phase.and_then(|p| p.flags.get(qi)).is_some_and(|&f| f > 0);
            lf.module
                .module_requests
                .push(ModuleRequest { specifier, lazy });
        }
        for record in &md.records {
            emit_module_record(lf, md, record)?;
        }
    }
    Ok(())
}

/// Convert one module record into an import/export declaration.
fn emit_module_record(
    lf: &mut Lifter,
    md: &ModuleData,
    record: &ModuleRecord,
) -> Result<(), LiftError> {
    let request_sym = |lf: &mut Lifter, idx: u32| -> Result<Sym, LiftError> {
        let Some(&sid) = md.requests.get(idx as usize) else {
            return Err(LiftError::MalformedModuleData {
                idx,
                count: md.requests.len(),
            });
        };
        lf.sym_of_file_sid(sid)
            .ok_or(LiftError::UnresolvedEntity(idx))
    };
    match record {
        ModuleRecord::RegularImport {
            local_name,
            import_name,
            module_request_idx,
        } => {
            let module_request = request_sym(lf, *module_request_idx)?;
            let local_name = lf
                .sym_of_file_sid(*local_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            let import_name = lf
                .sym_of_file_sid(*import_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            lf.module.imports.push(ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            });
        }
        ModuleRecord::NamespaceImport {
            local_name,
            module_request_idx,
        } => {
            let module_request = request_sym(lf, *module_request_idx)?;
            let local_name = lf
                .sym_of_file_sid(*local_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            lf.module.imports.push(ImportDecl::Namespace {
                local_name,
                module_request,
            });
        }
        ModuleRecord::LocalExport {
            local_name,
            export_name,
        } => {
            let local_name = lf
                .sym_of_file_sid(*local_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            let export_name = lf
                .sym_of_file_sid(*export_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            lf.module.exports.push(ExportDecl::Local {
                local_name,
                export_name,
            });
        }
        ModuleRecord::IndirectExport {
            export_name,
            import_name,
            module_request_idx,
        } => {
            let module_request = request_sym(lf, *module_request_idx)?;
            let export_name = lf
                .sym_of_file_sid(*export_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            let import_name = lf
                .sym_of_file_sid(*import_name)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            lf.module.exports.push(ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            });
        }
        ModuleRecord::StarExport { module_request_idx } => {
            let module_request = request_sym(lf, *module_request_idx)?;
            lf.module.exports.push(ExportDecl::Star { module_request });
        }
    }
    Ok(())
}
