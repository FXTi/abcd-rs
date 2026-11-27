//! Unit tests for standalone whole-module lowering (`lower_module`),
//! container-preserving binary rewrite (`rewrite_file` / `rewrite_file_owned`),
//! 64-bit static field/annotation constants, all 12 `TypedArrayTag` literal
//! shapes, `_ESSlotNumberAnnotation` synchronization, `param_annotations`
//! `MethodIdx` remapping, and multi-batch `decode_lazy` determinism.

use abcd_file::{FunctionKind as FileFunctionKind, LiteralValue, Method, MethodBody, MethodCode};
use abcd_ir::{
    AnnValue, Block, ClassData, ClassId, Const, FieldData, FunctionData,
    FunctionKind as IrFunctionKind, ImportDecl, Inst, InstId, Modifiers, ModuleRequest, Op,
    StaticTy, Ty, TypedArrayTag, Value, ValueDef, ValueId, verify_module,
};

use super::*;

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
        ta_u1, ta_u8, ta_i8, ta_u16, ta_i16, ta_u32, ta_i32, ta_u64, ta_i64, ta_f32, ta_f64, ta_str,
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
    let resolver = crate::method_body::EntityResolver::new(&m, &file);
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
                    code: MethodCode::Decoded(vec![abcd_isa::Bytecode::Returnundefined]),
                    entities: abcd_file::MethodEntities::new(),
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

    let rewritten = rewrite_file(&m, &base_file, LowerOptions::default()).expect("rewrite_file");

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

/// `rewrite_file_owned` produces 100% byte-identical `.abc` output (and
/// identical `StringId` order, classes, literal arrays, `_ESSlotNumberAnnotation`,
/// and `MethodDebugInfo`) to `rewrite_file` across multi-batch modules
/// (`> MAX_LOWER_BATCH_FUNCS`), and lowering onto a `decode_lazy`
/// (`MethodCode::Span`) `base_file` produces byte-identical output to
/// lowering onto an eager `decode` `base_file` (`#49`, `#84`).
#[test]
fn rewrite_file_owned_and_lazy_span_base_file_are_byte_identical_across_batches() {
    use abcd_ir::{ColumnEntry as IrColumnEntry, DebugData, LineEntry as IrLineEntry, Loc};
    use std::sync::Arc;

    let mut b = abcd_file::Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, FileSourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged]);
    let (code, _) = abcd_isa::encode(&[
        abcd_isa::Bytecode::Lda(abcd_isa::Reg(0)),
        abcd_isa::Bytecode::Return,
    ])
    .unwrap();
    let m_h = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 0, 1);
    b.method_set_source_lang(m_h, FileSourceLang::EcmaScript);
    let base_bytes = b.finalize().unwrap();

    let eager_base = abcd_file::decode(&base_bytes).unwrap();
    let lazy_base = abcd_file::decode_lazy(Arc::from(base_bytes.as_slice())).unwrap();
    assert!(matches!(
        eager_base
            .all_methods()
            .next()
            .unwrap()
            .1
            .body
            .as_ref()
            .unwrap()
            .code,
        MethodCode::Decoded(_)
    ));
    assert!(matches!(
        lazy_base
            .all_methods()
            .next()
            .unwrap()
            .1
            .body
            .as_ref()
            .unwrap()
            .code,
        MethodCode::Span(_)
    ));

    let mut module = abcd_lift::lift_file(&lazy_base).unwrap();

    // Enrich `func_main_0` with IC op (`Add`), synthesized literal array,
    // and `DebugData` (source_file, source_code, line_table, column_table, param_names).
    let f0_bb = module.functions[0].blocks[0];
    module.blocks[f0_bb.index()].insts.clear();
    let p0 = module.functions[0].params[0];
    let lit_str = module.sym.intern("batch_lit_payload\0nul_🚀");
    let lit_cid = module.consts.push(Const::String(lit_str));
    let arr_shape = module.consts.push_array(vec![lit_cid]);
    let v_arr = ValueId::new(module.values.len() as u32);
    let i_arr = InstId::new(module.insts.len() as u32);
    module.values.push(Value {
        def: ValueDef::Inst(i_arr),
        ty: Ty::Any,
    });
    module.insts.push(Inst {
        op: Op::AllocArray {
            shape: Some(arr_shape),
        },
        result: Some(v_arr),
        block: f0_bb,
        loc: Some(Loc {
            line: 10,
            column: Some(4),
        }),
    });
    let v_sum = ValueId::new(module.values.len() as u32);
    let i_sum = InstId::new(module.insts.len() as u32);
    module.values.push(Value {
        def: ValueDef::Inst(i_sum),
        ty: Ty::Any,
    });
    module.insts.push(Inst {
        op: Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: p0,
            right: v_arr,
        },
        result: Some(v_sum),
        block: f0_bb,
        loc: Some(Loc {
            line: 11,
            column: Some(8),
        }),
    });
    let i_ret = InstId::new(module.insts.len() as u32);
    module.insts.push(Inst {
        op: Op::Return { value: Some(v_sum) },
        result: None,
        block: f0_bb,
        loc: Some(Loc {
            line: 12,
            column: Some(2),
        }),
    });
    module.blocks[f0_bb.index()]
        .insts
        .extend([i_arr, i_sum, i_ret]);

    let sf_sym = module.sym.intern("entry.ts");
    let param_sym = module.sym.intern("inputArg");
    module.functions[0].debug = Some(DebugData {
        source_file: Some(sf_sym),
        source_code: Some(Arc::from("export function main(inputArg) {}")),
        line_table: vec![
            IrLineEntry {
                inst: i_arr,
                line: 10,
            },
            IrLineEntry {
                inst: i_sum,
                line: 11,
            },
            IrLineEntry {
                inst: i_ret,
                line: 12,
            },
        ],
        column_table: vec![
            IrColumnEntry {
                inst: i_arr,
                column: 4,
            },
            IrColumnEntry {
                inst: i_sum,
                column: 8,
            },
            IrColumnEntry {
                inst: i_ret,
                column: 2,
            },
        ],
        local_names: Vec::new(),
        param_names: vec![param_sym],
        scope_names: None,
    });

    // Synthesize a new class + > 520 helper functions so `build_lower_batches`
    // spans multiple `MAX_LOWER_BATCH_FUNCS = 512` batches!
    let synth_cls_sym = module.sym.intern("LSynthBatch;");
    let mut synth_cls = ClassData::new(synth_cls_sym, synth_cls_sym);
    synth_cls.modifiers = Modifiers::PUBLIC;
    let synth_cls_id = ClassId::new(module.classes.len() as u32);
    module.classes.push(synth_cls);

    for idx in 0..530usize {
        let h_sym = module.sym.intern(&format!("batch_helper_{idx}"));
        let h_fid = FuncId::new(module.functions.len() as u32);
        let h_bb = abcd_ir::BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());

        let s_sym = module.sym.intern(&format!("batch_str_{idx}"));
        let s_cid = module.consts.push(Const::String(s_sym));
        let v_s = ValueId::new(module.values.len() as u32);
        let i_s = InstId::new(module.insts.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(i_s),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::LoadConst(s_cid),
            result: Some(v_s),
            block: h_bb,
            loc: None,
        });
        let i_hr = InstId::new(module.insts.len() as u32);
        module.insts.push(Inst {
            op: Op::Return { value: Some(v_s) },
            result: None,
            block: h_bb,
            loc: None,
        });
        module.blocks[h_bb.index()].insts.extend([i_s, i_hr]);

        let mut hf = FunctionData::new(synth_cls_id, h_sym, IrFunctionKind::Function);
        hf.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        hf.blocks.push(h_bb);
        module.functions.push(hf);
        module.classes[synth_cls_id.index()].methods.push(h_fid);
    }
    assert!(build_lower_batches(&module).len() >= 2);
    assert!(verify_module(&module).is_ok());

    let opts = LowerOptions::default();
    let rw_ref = rewrite_file(&module, &eager_base, opts).expect("rewrite_file eager");
    let rw_owned =
        rewrite_file_owned(&module, eager_base.clone(), opts).expect("rewrite_file_owned eager");
    let rw_lazy = rewrite_file_owned(&module, lazy_base, opts).expect("rewrite_file_owned lazy");

    let enc_ref = abcd_file::encode(&rw_ref).expect("encode rw_ref");
    let enc_owned = abcd_file::encode(&rw_owned).expect("encode rw_owned");
    let enc_lazy = abcd_file::encode(&rw_lazy).expect("encode rw_lazy");

    assert_eq!(
        enc_ref, enc_owned,
        "rewrite_file and rewrite_file_owned must emit 100% identical .abc bytes"
    );
    assert_eq!(
        enc_ref, enc_lazy,
        "lowering onto decode_lazy (MethodCode::Span) must emit 100% identical .abc bytes to eager decode"
    );

    let rw_strings: Vec<(StringId, &str)> = rw_ref.strings.iter().collect();
    let owned_strings: Vec<(StringId, &str)> = rw_owned.strings.iter().collect();
    let lazy_strings: Vec<(StringId, &str)> = rw_lazy.strings.iter().collect();
    assert_eq!(rw_strings, owned_strings);
    assert_eq!(rw_strings, lazy_strings);
}
