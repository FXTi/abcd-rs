//! Focused unit tests for the v0.2 lift (synthetic Builder-made files,
//! plus one struct-literal model test). Every test also runs the v0.2
//! verifier on the lifted module — zero errors required.

use abcd_file::{
    AccessFlags, Builder, CatchBlockDef, FieldValue, ModuleRecordDef, SourceLang, Type, decode,
};
use abcd_ir2::{
    self, AnnValue, Const, EdgeKind, ExportDecl, FunctionKind as IrFunctionKind, ImportDecl, Op,
    ValueDef,
};
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::{LiftError, SuperKeyForm, lift_file, super_key};

/// Builder helper: run `setup`, finalize, decode.
fn build(setup: impl FnOnce(&mut Builder)) -> abcd_file::File {
    let mut b = Builder::new();
    setup(&mut b);
    decode(&b.finalize().expect("finalize")).expect("decode")
}

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// The lifted module must verify with ZERO errors.
fn verify_clean(m: &abcd_ir2::Module) {
    let report = abcd_ir2::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

fn resolve<'m>(m: &'m abcd_ir2::Module, s: abcd_ir2::Sym) -> &'m str {
    m.sym.resolve(s).expect("dangling sym")
}

// ─── 1. Parameter seeding from the code-header num_args (B5) ────────

#[test]
fn params_seeded_from_code_header_num_args() {
    // 12.x identity: proto carries no shorty (#A7), but the code header
    // declares num_args = 1. Body: lda v1 (arg0); return.
    let file = build(|b| {
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[Bytecode::Lda(Reg(1)), Bytecode::Return]).unwrap();
        b.class_add_method(cls, "identity", proto, AccessFlags::STATIC, &code, 1, 1);
    });

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let f = &m.functions[0];
    assert_eq!(f.params.len(), 1, "param from the code header, not proto");
    assert_eq!(m.values[f.params[0].index()].def, ValueDef::Param(0));
    // #A7: no shorty on 12.x → no signature.
    assert!(f.sig.is_none());
    // The entry block ends in Return{value: params[0]}.
    let entry = f.blocks[0];
    let insts = &m.blocks[entry.index()].insts;
    let ret = m.insts[insts.last().unwrap().index()].clone();
    match ret.op {
        Op::Return { value: Some(v) } => assert_eq!(v, f.params[0]),
        other => panic!("expected Return of the param, got {other:?}"),
    }
}

// ─── 2. Handler seeding (N13) + exceptional edges ───────────────────

#[test]
fn handler_gets_exception_param_and_exceptional_edges() {
    // [0] ldundefined   ┐ try
    // [1] return        ┘
    // [2] sta v0        ┐ handler: acc (the exception) → v0
    // [3] lda v0        │
    // [4] return        ┘
    let file = build(|b| {
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (insns, _) = encode_bytecodes(&[
            Bytecode::Ldundefined,
            Bytecode::Return,
            Bytecode::Sta(Reg(0)),
            Bytecode::Lda(Reg(0)),
            Bytecode::Return,
        ])
        .unwrap();
        let code = b.create_code(&insns, 1, 0);
        b.code_add_try_block(
            code,
            0,
            2,
            &[CatchBlockDef {
                type_class: None,
                handler_pc: 2,
                code_size: 3,
            }],
        );
        let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &[], 0, 0);
        b.method_set_code(m, code);
    });

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let f = &m.functions[0];
    assert_eq!(f.try_regions.len(), 1);
    let region = &f.try_regions[0];
    assert_eq!(region.catches.len(), 1);
    let catch = &region.catches[0];
    // The exception value is defined by the dispatch at the handler.
    assert_eq!(
        m.values[catch.exception.index()].def,
        ValueDef::ExceptionParam(catch.handler)
    );
    // Every protected block is an Exceptional predecessor of the
    // handler (MissingExceptionalPred rule).
    let handler = &m.blocks[catch.handler.index()];
    for &p in &region.protected {
        assert!(
            handler.preds.contains(&abcd_ir2::Edge {
                from: p,
                kind: EdgeKind::Exceptional,
            }),
            "missing exceptional pred {p:?}"
        );
    }
    // The handler's sta/lda/return chain carries the exception value:
    // the handler's Return uses it (through the v0 alias).
    let handler_insts = &m.blocks[catch.handler.index()].insts;
    let ret = m.insts[handler_insts.last().unwrap().index()].clone();
    match ret.op {
        Op::Return { value: Some(v) } => assert_eq!(v, catch.exception),
        other => panic!("expected Return of the exception, got {other:?}"),
    }
}

// ─── 3. Literal arrays → ConstPool (nested + method ref) ────────────

#[test]
fn literal_array_nested_and_method_ref() {
    let file = build(|b| {
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (ret, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
        let target = b.class_add_method(cls, "target", proto, AccessFlags::STATIC, &ret, 0, 0);

        let inner = b.add_literal_array("inner");
        let x = b.add_string("x");
        b.literal_array_add_string(inner, x);
        let outer = b.add_literal_array("outer");
        b.literal_array_add_integer(outer, 7);
        b.literal_array_add_literalarray(outer, inner);
        b.literal_array_add_method(outer, target);

        let (code, offsets) = encode_bytecodes(&[
            Bytecode::Createarraywithbuffer(Imm(1), PLACEHOLDER),
            Bytecode::Returnundefined,
        ])
        .unwrap();
        let owner = b.class_add_method(cls, "main", proto, AccessFlags::STATIC, &code, 0, 0);
        b.relocate_code_id(
            owner,
            offsets[0],
            0,
            abcd_file::CodeEntity::LiteralArray(outer),
        )
        .unwrap();
        b.deduplicate();
    });

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    // Find the AllocObject and inspect its shape constant.
    let alloc = m
        .insts
        .iter()
        .find(|i| matches!(i.op, Op::AllocObject { .. }))
        .expect("AllocObject emitted");
    let Op::AllocObject { shape } = alloc.op else {
        unreachable!()
    };
    // Method order in the decoded class is the Builder's layout order,
    // not necessarily creation order — resolve by name.
    let target_fid = abcd_ir2::FuncId::new(
        m.functions
            .iter()
            .position(|f| resolve(&m, f.name) == "target")
            .expect("target function") as u32,
    );
    let x_sym = m.sym.intern("x");
    let expected = Const::ArrayLiteral(vec![
        Const::number(7.0),
        Const::ArrayLiteral(vec![Const::String(x_sym)]),
        Const::MethodRef(target_fid),
    ]);
    assert_eq!(m.consts.get(shape), Some(&expected));
    // The MethodRef points at the function named "target".
    let target_name = resolve(&m, m.functions[target_fid.index()].name);
    assert_eq!(target_name, "target");
}

// ─── 4. Module records → imports/exports/module_requests ────────────

#[test]
fn module_record_becomes_declarations() {
    let file = build(|b| {
        b.set_api(12, "beta1");
        // _ESModuleRecord with one request + two records.
        let rec_cls = b.add_class("L_ESModuleRecord;");
        let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
        let dep = b.add_string("dep1");
        let module_la = b.add_literal_array("module");
        let records = vec![
            ModuleRecordDef::RegularImport {
                local_name: b.add_string("local1"),
                import_name: b.add_string("imp1"),
                module_request_idx: 0,
            },
            ModuleRecordDef::StarExport {
                module_request_idx: 0,
            },
        ];
        b.literal_array_add_module_data(module_la, &[dep], &records)
            .expect("stage module data");
        b.field_set_value_literalarray(field, module_la)
            .expect("wire module field");

        // NOTE: no phase blob here — the Builder path for
        // `literal_array_add_module_request_phase` has no working
        // precedent and corrupts the module blob's string offsets when
        // combined (suspected bridge staging-order issue, reported —
        // abcd-file is read-only for this worker). The lazy-flag
        // conversion is covered by a struct-literal model test below.

        // Minimal global class so the file is well-formed.
        let global = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
        b.class_add_method(global, "main", proto, AccessFlags::STATIC, &code, 0, 0);
    });

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);

    // Imports.
    assert_eq!(m.imports.len(), 1);
    let ImportDecl::Regular {
        local_name,
        import_name,
        module_request,
    } = &m.imports[0]
    else {
        panic!("expected regular import: {:?}", m.imports);
    };
    assert_eq!(resolve(&m, *local_name), "local1");
    assert_eq!(resolve(&m, *import_name), "imp1");
    assert_eq!(resolve(&m, *module_request), "dep1");

    // Exports.
    assert_eq!(m.exports.len(), 1);
    let ExportDecl::Star { module_request } = &m.exports[0] else {
        panic!("expected star export: {:?}", m.exports);
    };
    assert_eq!(resolve(&m, *module_request), "dep1");

    // Module requests (no phase blob → eager, documented pairing).
    assert_eq!(m.module_requests.len(), 1);
    assert_eq!(resolve(&m, m.module_requests[0].specifier), "dep1");
    assert!(!m.module_requests[0].lazy);
}

/// N7 lazy flags: a `moduleRequestPhaseIdx` blob pairs with the module
/// record's request list positionally (struct-literal model — the
/// Builder's phase-blob path is under suspicion, see above).
#[test]
fn module_request_phase_flags_become_lazy_requests() {
    use abcd_file::{FileType, ModuleData, ModuleRecord, ModuleRequestPhase, Version};

    let mut strings = abcd_file::StringPool::default();
    let rec_desc = strings.get_or_intern("L_ESModuleRecord;");
    let field_name = strings.get_or_intern("test.js");
    let phase_name = strings.get_or_intern("moduleRequestPhaseIdx");
    let dep = strings.get_or_intern("dep1");
    let lazy_dep = strings.get_or_intern("lazy2");
    let local = strings.get_or_intern("local1");
    let imp = strings.get_or_intern("imp1");
    let class = abcd_file::Class {
        descriptor: rec_desc,
        name: rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: SourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![
            abcd_file::Field {
                name: field_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::PUBLIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleData(ModuleData {
                    source_offset: 0,
                    requests: vec![dep, lazy_dep],
                    records: vec![ModuleRecord::RegularImport {
                        local_name: local,
                        import_name: imp,
                        module_request_idx: 1,
                    }],
                })),
                annotations: Default::default(),
            },
            abcd_file::Field {
                name: phase_name,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::PUBLIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleRequestPhase(ModuleRequestPhase {
                    source_offset: 0,
                    flags: vec![0, 7],
                })),
                annotations: Default::default(),
            },
        ],
        annotations: Default::default(),
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(rec_desc, class)].into_iter().collect(),
        literal_arrays: vec![],
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
    };

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let laziness: Vec<(&str, bool)> = m
        .module_requests
        .iter()
        .map(|r| (resolve(&m, r.specifier), r.lazy))
        .collect();
    assert_eq!(laziness, [("dep1", false), ("lazy2", true)]);
    // The record's module_request_idx resolves to the second request.
    let ImportDecl::Regular { module_request, .. } = &m.imports[0] else {
        panic!("expected regular import");
    };
    assert_eq!(resolve(&m, *module_request), "lazy2");
}

/// `_ESScopeNamesRecord` fields attach to DebugData.scope_names of the
/// function whose debug source file matches the field name.
#[test]
fn scope_names_record_attaches_by_source_file() {
    let file = build(|b| {
        b.set_api(12, "beta1");
        let scope_cls = b.add_class("L_ESScopeNamesRecord;");
        let scope_field = b.class_add_field(scope_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
        let scope_la = b.add_literal_array("scope");
        let box_name = b.add_string("Box");
        b.literal_array_add_string(scope_la, box_name);
        b.field_set_value_literalarray(scope_field, scope_la)
            .expect("wire scope field");

        let global = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
        let m = b.class_add_method(global, "main", proto, AccessFlags::STATIC, &code, 0, 0);
        let lnp = b.create_lnp();
        let debug = b.create_debug_info(lnp, 1);
        let src = b.add_string("test.js");
        b.lnp_emit_set_file(lnp, debug, src);
        b.lnp_emit_end(lnp);
        b.method_set_debug_info(m, debug);
    });

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let main_fn = m
        .functions
        .iter()
        .find(|f| resolve(&m, f.name) == "main")
        .expect("main function");
    let debug = main_fn.debug.as_ref().expect("debug data");
    let scope_const = debug.scope_names.expect("scope names attached");
    let box_sym = m.sym.intern("Box");
    assert_eq!(
        m.consts.get(scope_const),
        Some(&Const::ArrayLiteral(vec![Const::String(box_sym)]))
    );
}

// ─── 5. Annotation merge order (struct-literal model) ───────────────

#[test]
fn annotation_buckets_merge_in_documented_order() {
    use abcd_file::{AnnotationValue, FileType, Version};

    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("Lglobal;");
    let ann_desc =
        |strings: &mut abcd_file::StringPool, i: u32| strings.get_or_intern(&format!("LAnn{i};"));
    let level = |strings: &mut abcd_file::StringPool| strings.get_or_intern("level");
    let mk_ann = |strings: &mut abcd_file::StringPool, i: u32| abcd_file::Annotation {
        class_descriptor: ann_desc(strings, i),
        elements: vec![abcd_file::AnnotationElem {
            name: level(strings),
            value: AnnotationValue::U32(i),
        }],
    };
    let annotations = abcd_file::Annotations {
        compile_time: vec![mk_ann(&mut strings, 1)],
        runtime: vec![mk_ann(&mut strings, 2)],
        compile_time_type: vec![mk_ann(&mut strings, 3)],
        runtime_type: vec![mk_ann(&mut strings, 4)],
    };
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: SourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: Vec::new(),
        annotations,
    };
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: vec![],
        entity_map: Default::default(),
        literal_array_offsets: Default::default(),
    };

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let anns = &m.classes[0].annotations;
    assert_eq!(anns.len(), 4, "four buckets fold into one list");
    // Merge order: compile_time, runtime, compile_time_type,
    // runtime_type (values 1, 2, 3, 4).
    for (i, ann) in anns.iter().enumerate() {
        let desc = resolve(&m, m.classes[ann.class.index()].descriptor);
        assert_eq!(desc, format!("LAnn{};", i + 1));
        let AnnValue::Const(c) = ann.elements[0].1 else {
            panic!("expected const element: {:?}", ann.elements[0]);
        };
        assert_eq!(
            m.consts.get(c),
            Some(&Const::number((i + 1) as f64)),
            "merge order position {i}"
        );
    }
}

// ─── 6. Debug: LNP → DebugData ──────────────────────────────────────

#[test]
fn debug_locals_lines_and_params() {
    let file = build(|b| {
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let proto = b.create_proto(Type::Tagged, &[]);
        let (code, _) = encode_bytecodes(&[
            Bytecode::Ldtrue,  // 0
            Bytecode::Ldfalse, // 1
            Bytecode::Return,  // 2
        ])
        .unwrap();
        let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &code, 2, 0);

        let lnp = b.create_lnp();
        let debug = b.create_debug_info(lnp, 10);
        let src = b.add_string("main.js");
        b.lnp_emit_set_file(lnp, debug, src);
        let src_code = b.add_string("function f() {}");
        b.lnp_emit_set_source_code(lnp, debug, src_code);
        let p1 = b.add_string("param1");
        b.debug_add_param(debug, p1);
        let p2 = b.add_string("param2");
        b.debug_add_param(debug, p2);
        b.lnp_emit_advance_pc(lnp, debug, 1);
        b.lnp_emit_advance_line(lnp, debug, 2);
        b.lnp_emit_column(lnp, debug, 0, 3);
        let vname = b.add_string("local_var");
        let vtype = b.add_string("i32");
        b.lnp_emit_start_local(lnp, debug, 1, vname, vtype);
        b.lnp_emit_advance_pc(lnp, debug, 1);
        b.lnp_emit_end_local(lnp, 1);
        b.lnp_emit_end(lnp);
        b.method_set_debug_info(m, debug);
    });

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let f = &m.functions[0];
    let debug = f.debug.as_ref().expect("debug data");
    assert_eq!(resolve(&m, debug.source_file.unwrap()), "main.js");
    assert_eq!(debug.source_code.as_deref(), Some("function f() {}"));
    let names: Vec<&str> = debug.param_names.iter().map(|&s| resolve(&m, s)).collect();
    assert_eq!(names, ["param1", "param2"]);

    // Line table keyed by the LIFTED InstIds; the running-line
    // semantics cover pcs between change entries.
    assert!(!debug.line_table.is_empty());
    let entry = f.blocks[0];
    let block_insts = &m.blocks[entry.index()].insts;
    for e in &debug.line_table {
        assert!(
            block_insts.contains(&e.inst),
            "line entry keys on a lifted inst"
        );
    }
    // The vendored extractor emits the initial row (pc 0 → line 10);
    // the lift's running-line semantics then cover EVERY pc — all
    // emitted insts carry a location (T8), none fabricated.
    let first = m.insts[block_insts[0].index()].clone();
    assert_eq!(first.loc.map(|l| l.line), Some(10));
    for &iid in block_insts {
        assert!(
            m.insts[iid.index()].loc.is_some(),
            "running line must cover {iid}"
        );
    }

    // The local has a name, a parsed type, and a scope over lifted
    // instructions (#5 extents: pc 1..2 → the covering insts).
    assert_eq!(debug.local_names.len(), 1);
    let lv = &debug.local_names[0];
    assert_eq!(resolve(&m, lv.name), "local_var");
    assert_eq!(lv.ty, Some(abcd_ir2::Ty::Static(abcd_ir2::StaticTy::I32)));
    let scope = lv.scope.expect("scope extents mapped");
    assert!(block_insts.contains(&scope.start));
    assert!(block_insts.contains(&scope.end));
}

// ─── 7. Deprecated opcodes fold to modern ops ───────────────────────

#[test]
fn deprecated_opcodes_fold_to_modern() {
    // [0] deprecated.tonumber v0   (v0 never written → frame-initial)
    // [1] sta v1
    // [2] deprecated.delobjprop v1 v0
    // [3] return
    let file = build(|b| {
        b.set_api(9, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Tagged, &[]);
        let (code, _) = encode_bytecodes(&[
            Bytecode::DeprecatedTonumber(Reg(0)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedDelobjprop(Reg(1), Reg(0)),
            Bytecode::Return,
        ])
        .unwrap();
        b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 2, 0);
    });

    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let entry = m.functions[0].blocks[0];
    let ops: Vec<&Op> = m.blocks[entry.index()]
        .insts
        .iter()
        .map(|&iid| &m.insts[iid.index()].op)
        .collect();
    // deprecated.tonumber → UnaryOp{ToNumber} over the frame-initial
    // UNDEFINED constant (v0 was never written — P3-T7).
    let Some(Op::UnaryOp {
        op: abcd_ir2::UnOp::ToNumber,
        operand,
    }) = ops.first()
    else {
        panic!("expected UnaryOp::ToNumber first, got {ops:?}");
    };
    let ValueDef::Const(c) = m.values[operand.index()].def else {
        panic!(
            "frame-initial value must be a Const: {:?}",
            m.values[operand.index()]
        );
    };
    assert_eq!(m.consts.get(c), Some(&Const::Undefined));
    // deprecated.delobjprop → DeleteProp.
    assert!(
        ops.iter().any(|op| matches!(op, Op::DeleteProp { .. })),
        "DeleteProp expected: {ops:?}"
    );
}

// ─── 8. Super-by-index is a hard error ──────────────────────────────

#[test]
fn super_by_index_is_a_hard_error() {
    // The ISA has name/dynamic super forms only; a constant-index super
    // key can never come from real bytecode, and no semantics may be
    // invented for it.
    assert!(matches!(
        super_key(SuperKeyForm::Index(3)),
        Err(LiftError::UnsupportedSuperByIndex)
    ));
    let m = abcd_ir2::Module::new();
    let _ = m;
    let name = abcd_ir2::Sym::new(0);
    assert!(super_key(SuperKeyForm::Name(name)).is_ok());
    assert!(super_key(SuperKeyForm::Dynamic(abcd_ir2::ValueId::new(0))).is_ok());
}

// ─── Function kind mapping smoke ────────────────────────────────────

#[test]
fn function_kind_maps_generator_and_async() {
    let file = build(|b| {
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
        let g = b.class_add_method(cls, "gen", proto, AccessFlags::STATIC, &code, 0, 0);
        b.method_set_function_kind(g, abcd_file::FunctionKind::GeneratorFunction);
        let a = b.class_add_method(cls, "fut", proto, AccessFlags::STATIC, &code, 0, 0);
        b.method_set_function_kind(a, abcd_file::FunctionKind::AsyncFunction);
        // The CONSTRUCTOR access flag selects FunctionKind::Constructor
        // when present; the Builder path does not round-trip that flag
        // (probe-verified), so it is not exercised here.
    });
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let kind_of = |name: &str| {
        m.functions
            .iter()
            .find(|f| resolve(&m, f.name) == name)
            .map(|f| f.kind)
            .expect("function")
    };
    assert_eq!(kind_of("gen"), IrFunctionKind::Generator);
    assert_eq!(kind_of("fut"), IrFunctionKind::Async);
}

/// The `_ESModuleRecord` field surfaces as FieldValue::ModuleData on
/// the file model (sanity that the test wiring works as intended).
#[test]
fn module_field_wiring_is_as_expected() {
    let file = build(|b| {
        b.set_api(12, "beta1");
        let rec_cls = b.add_class("L_ESModuleRecord;");
        let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
        let dep = b.add_string("dep1");
        let module_la = b.add_literal_array("module");
        b.literal_array_add_module_data(module_la, &[dep], &[])
            .expect("stage module data");
        b.field_set_value_literalarray(field, module_la)
            .expect("wire module field");
        let global = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
        b.class_add_method(global, "main", proto, AccessFlags::STATIC, &code, 0, 0);
    });
    let rec = file
        .class_by_str("L_ESModuleRecord;")
        .expect("record class");
    assert!(matches!(
        rec.fields[0].initial_value,
        Some(FieldValue::ModuleData(_))
    ));
}
