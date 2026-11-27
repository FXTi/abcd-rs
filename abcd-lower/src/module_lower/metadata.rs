//! IR metadata to [`abcd_file`] container record builders: class/method/field
//! shells, access flags, static signatures, compile-time annotations, and
//! ECMAScript module records (`ModuleData` / `ModuleRequestPhase`).

use std::collections::HashMap;

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Annotations, Field, FieldIdx,
    FieldValue, FunctionKind as FileFunctionKind, Method, MethodIdx, ModuleData, ModuleRecord,
    ModuleRequestPhase, ParamAnnotations, SourceLang as FileSourceLang, StringId, StringPool, Type,
};
use abcd_ir::{
    AnnValue, ClassData, Const, ExportDecl, FieldData, FuncId, FunctionKind as IrFunctionKind,
    ImportDecl, Modifiers, Module, ModuleRequest, SourceLang as IrSourceLang, StaticTy, Sym, Ty,
};
use abcd_isa::EntityKind;

use super::{intern_sym, rebuild_method_debug};
use crate::LowerError;
use crate::layout::LayoutResult;

pub(super) fn modifiers_to_access_flags(m: Modifiers) -> AccessFlags {
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

pub(super) fn source_lang_to_file(lang: IrSourceLang) -> FileSourceLang {
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

pub(super) fn is_external_class(cls: &ClassData, module: &Module) -> bool {
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

pub(super) fn build_method_shell(
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

pub(super) fn build_field_shell(
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

pub(super) fn build_annotations(
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

pub(super) fn build_module_data(
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
