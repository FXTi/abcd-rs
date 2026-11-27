//! Round 3 Stage 2 regression tests (`#50`, `#55`, `#57`, `#58`, `#61`):
//! - `R3-C1..C7`: `NewSpread`, async-generator & generator-state ops,
//!   `LexEnvKind::{Plain, Sendable, Patch}`, `NotifyConcurrentResult` &
//!   `ToPropertyKey`, `Supercallthisrange` / `Supercallforwardallargs`
//!   no-`read_acc` & `SuperArrow`, `Createobjectwithexcludedkeys` `imm + 1`
//!   keys, and `ClassInit`.
//! - `R3-H1..H4`, `R3-M4`: `Ldsuperbyname` `acc` receiver,
//!   `Definegettersetterbyvalue` `acc` `set_name`, all 4 `OwnStoreKind`s,
//!   `LoadSymbol`, and legacy `0.0.0.2` `DeprecatedTonumeric`.
//! - `R3-H9`, `#50`, `#58`: `Catch::type_class` synthesizing external
//!   exception `ClassData`, `Arc::ptr_eq` deduplication on
//!   `DebugData::source_code`, lossless `LiteralValue` tags & non-colliding
//!   wrapper caches, and `256 KiB`-stack `5,000`-deep nested literal buffers.
//! - `R3-X1` (`#61`): `JumpEqz` / `JumpNez` vs direct `CondBranch` on proven
//!   booleans (`ldnull; jeqz`, `ldnan; jnez`, `cmp; jnez`, `cmp; jeqz`).
//! - `R3-M3`: malformed register, range, jump, fall-through, and try/catch
//!   bounds returning typed `LiftError`s without panics.

use std::collections::HashMap;
use std::sync::Arc;

use abcd_file::{
    AccessFlags, Builder, CatchBlock, CodeEntity, EntityRef, File, FileType,
    FunctionKind as FileFunctionKind, LiteralArray, LiteralArrayIdx, LiteralValue, Method,
    MethodBody, MethodDebugInfo, MethodIdx, SourceLang as FileSourceLang, StringPool, TryBlock,
    Type, Version, decode,
};
use abcd_ir::{
    CallKind, CmpOp, Const, DynPrim, LexEnvKind, LitMethodKind, Module, Op, OwnStoreKind, SuperKey,
    Ty, TypedArrayTag, UnOp, ValueDef, ValueId,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::{LiftError, lift_file};

const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

fn verify_clean(m: &Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

fn build_single(bytecodes: &[Bytecode], num_vregs: u32, num_args: u32) -> File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(
        cls,
        "f",
        proto,
        AccessFlags::STATIC,
        &code,
        num_vregs,
        num_args,
    );
    decode(&b.finalize().unwrap()).unwrap()
}

fn single_body_model(
    num_vregs: u32,
    num_args: u32,
    bytecodes: Vec<Bytecode>,
    entities: HashMap<(EntityKind, u32), EntityRef>,
    try_blocks: Vec<TryBlock>,
) -> File {
    let mut strings = StringPool::default();
    let desc = strings.get_or_intern("LR3;");
    let fname = strings.get_or_intern("f");
    let method = Method {
        name: fname,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            entities,
            try_blocks,
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![method],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    }
}

fn const_of(m: &Module, v: ValueId) -> Const {
    match &m.values[v.index()].def {
        ValueDef::Const(c) => m.consts.get(*c).unwrap().clone(),
        ValueDef::Inst(iid) => match &m.insts[iid.index()].op {
            Op::LoadConst(c) => m.consts.get(*c).unwrap().clone(),
            other => panic!("expected LoadConst behind {v:?}, got {other:?}"),
        },
        other => panic!("expected const-defined value for {v:?}, got {other:?}"),
    }
}

// ─── R3-C1, R3-C2, R3-C4: AsyncGenerator, GeneratorState, Concurrent & ToPropertyKey ───

#[test]
fn r3_c2_c4_async_generator_state_concurrent_and_to_property_key() {
    let file = build_single(
        &[
            Bytecode::Ldai(Imm(10)), // closure in v0
            Bytecode::Sta(Reg(0)),
            Bytecode::Createasyncgeneratorobj(Reg(0)), // acc = genobj
            Bytecode::Sta(Reg(1)),                     // v1 = genobj
            Bytecode::Setgeneratorstate(Imm(3)),       // acc in = genobj (acc stays genobj)
            Bytecode::CallruntimeNotifyconcurrentresult, // acc in = genobj (acc stays genobj)
            Bytecode::Ldai(Imm(20)),
            Bytecode::Sta(Reg(2)), // v2 = yielded value
            Bytecode::Ldtrue,
            Bytecode::Sta(Reg(3)), // v3 = done/canSuspend
            Bytecode::Asyncgeneratorresolve(Reg(1), Reg(2), Reg(3)), // acc = resolved
            Bytecode::CallruntimeTopropertykey, // acc = ToPropertyKey(acc)
            Bytecode::Asyncgeneratorreject(Reg(1)), // v1 = genobj, acc = reason
            Bytecode::Return,
        ],
        4,
        0,
    );
    let m = lift_file(&file).expect("lift async generator & runtime ops");
    verify_clean(&m);

    let ops: Vec<&Op> = m.insts.iter().map(|i| &i.op).collect();
    let gen_val = m
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::CreateAsyncGenerator { func } => {
                assert_eq!(const_of(&m, func), Const::number(10.0));
                i.result
            }
            _ => None,
        })
        .expect("CreateAsyncGenerator emitted");

    assert!(
        ops.iter().any(
            |op| matches!(op, Op::SetGeneratorState { genobj, state: 3 } if *genobj == gen_val)
        )
    );
    assert!(
        ops.iter()
            .any(|op| matches!(op, Op::NotifyConcurrentResult { value } if *value == gen_val)),
        "SetGeneratorState & NotifyConcurrentResult both read acc without clobbering it"
    );

    let resolve_res = m
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::AsyncGeneratorResolve {
                genobj,
                value,
                done,
            } => {
                assert_eq!(genobj, gen_val);
                assert_eq!(const_of(&m, value), Const::number(20.0));
                assert_eq!(const_of(&m, done), Const::Bool(true));
                i.result
            }
            _ => None,
        })
        .expect("AsyncGeneratorResolve emitted");

    let key_res = m
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::UnaryOp {
                op: UnOp::ToPropertyKey,
                operand,
            } => {
                assert_eq!(operand, resolve_res);
                i.result
            }
            _ => None,
        })
        .expect("ToPropertyKey emitted");

    assert!(ops.iter().any(|op| matches!(
        op,
        Op::AsyncGeneratorReject { genobj, value } if *genobj == gen_val && *value == key_res
    )));
}

// ─── R3-C3: LexEnvKind::{Plain, Sendable, Patch} ───────────────────────────

#[test]
fn r3_c3_lex_env_kinds_preserve_plain_sendable_and_patch() {
    let file = build_single(
        &[
            Bytecode::Newlexenv(Imm(2)),
            Bytecode::Stlexvar(Imm(0), Imm(1)),
            Bytecode::Ldlexvar(Imm(0), Imm(1)),
            Bytecode::CallruntimeNewsendableenv(Imm(4)),
            Bytecode::CallruntimeStsendablevar(Imm(1), Imm(2)),
            Bytecode::CallruntimeLdsendablevar(Imm(1), Imm(2)),
            Bytecode::WideStpatchvar(Imm(7)),
            Bytecode::WideLdpatchvar(Imm(7)),
            Bytecode::Return,
        ],
        0,
        0,
    );
    let m = lift_file(&file).expect("lift lexenv kinds");
    verify_clean(&m);

    let ops: Vec<&Op> = m.insts.iter().map(|i| &i.op).collect();
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::NewLexEnv {
            num_vars: 2,
            kind: LexEnvKind::Plain
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::NewLexEnv {
            num_vars: 4,
            kind: LexEnvKind::Sendable
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::GetLexVar {
            level: 0,
            slot: 1,
            kind: LexEnvKind::Plain
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::GetLexVar {
            level: 1,
            slot: 2,
            kind: LexEnvKind::Sendable
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::GetLexVar {
            level: 0,
            slot: 7,
            kind: LexEnvKind::Patch
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::PutLexVar {
            level: 0,
            slot: 1,
            kind: LexEnvKind::Plain,
            ..
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::PutLexVar {
            level: 1,
            slot: 2,
            kind: LexEnvKind::Sendable,
            ..
        }
    )));
    assert!(ops.iter().any(|op| matches!(
        op,
        Op::PutLexVar {
            level: 0,
            slot: 7,
            kind: LexEnvKind::Patch,
            ..
        }
    )));
}

// ─── R3-C5, R3-C6, R3-C7: Super calls (zero bogus acc reads), ExcludedKeys, ClassInit ───

#[test]
fn r3_c5_supercallthisrange_and_forwardallargs_never_read_acc() {
    // Frame leaves `acc` completely untouched before `Supercallthisrange` and
    // `CallruntimeSupercallforwardallargs` — so `frame_init_consts` MUST NOT
    // materialize `Const::Hole`!
    let f_super = build_single(
        &[
            Bytecode::Supercallthisrange(Imm(0), Imm(2), Reg(0)),
            Bytecode::Return,
        ],
        0,
        2,
    );
    let m_super = lift_file(&f_super).expect("lift supercallthisrange");
    verify_clean(&m_super);
    assert!(
        !m_super.functions[0]
            .frame_init_consts
            .iter()
            .any(|&v| const_of(&m_super, v) == Const::Hole),
        "supercallthisrange must not read uninitialized acc (`Const::Hole`)"
    );
    let call_super = m_super
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::Call {
                callee,
                this,
                args,
                kind,
            } => Some((*callee, *this, args.clone(), *kind)),
            _ => None,
        })
        .expect("Call::Super emitted");
    assert_eq!(call_super.3, CallKind::Super);
    assert_eq!(call_super.1, None);
    assert_eq!(call_super.2.len(), 2);
    let ValueDef::Inst(callee_iid) = m_super.values[call_super.0.index()].def else {
        panic!("Supercallthisrange callee must come from LoadFunction");
    };
    assert!(matches!(
        m_super.insts[callee_iid.index()].op,
        Op::LoadFunction
    ));

    let f_fwd = build_single(
        &[
            Bytecode::CallruntimeSupercallforwardallargs(Reg(0)),
            Bytecode::Return,
        ],
        0,
        1,
    );
    let m_fwd = lift_file(&f_fwd).expect("lift supercallforwardallargs");
    verify_clean(&m_fwd);
    assert!(
        !m_fwd.functions[0]
            .frame_init_consts
            .iter()
            .any(|&v| const_of(&m_fwd, v) == Const::Hole),
        "supercallforwardallargs must not read uninitialized acc (`Const::Hole`)"
    );
    let call_fwd = m_fwd
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::Call {
                callee,
                this,
                args,
                kind,
            } => Some((*callee, *this, args.clone(), *kind)),
            _ => None,
        })
        .expect("Call::SuperForwardAllArgs emitted");
    assert_eq!(call_fwd.3, CallKind::SuperForwardAllArgs);
    assert_eq!(call_fwd.1, None);
    assert_eq!(call_fwd.0, m_fwd.functions[0].params[0]);
    assert_eq!(call_fwd.2, vec![m_fwd.functions[0].params[0]]);
}

#[test]
fn r3_c6_c7_excluded_keys_reads_imm_plus_one_and_callinit_lifts_class_init() {
    // `Createobjectwithexcludedkeys(Imm(2), Reg(0), Reg(1))` reads `2 + 1 = 3`
    // excluded key registers `Reg(1)..=Reg(3)`, then `CallruntimeCallinit`
    // emits `CallKind::ClassInit`.
    let file = build_single(
        &[
            Bytecode::Createobjectwithexcludedkeys(Imm(2), Reg(0), Reg(1)),
            Bytecode::CallruntimeCallinit(Imm(0), Reg(0)),
            Bytecode::Return,
        ],
        0,
        4,
    );
    let m = lift_file(&file).expect("lift excluded keys + callinit");
    verify_clean(&m);
    let params = &m.functions[0].params;

    let excluded = m
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::CreateObjectWithExcludedKeys { obj, keys } => Some((*obj, keys.clone())),
            _ => None,
        })
        .expect("CreateObjectWithExcludedKeys emitted");
    assert_eq!(excluded.0, params[0]);
    assert_eq!(
        excluded.1,
        vec![params[1], params[2], params[3]],
        "range_1 immediate 2 must read 2 + 1 = 3 key registers"
    );

    let init_call = m
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::Call {
                this, args, kind, ..
            } => Some((*this, args.clone(), *kind)),
            _ => None,
        })
        .expect("ClassInit emitted");
    assert_eq!(init_call.2, CallKind::ClassInit);
    assert_eq!(init_call.0, Some(params[0]));
    assert!(init_call.1.is_empty());
}

// ─── R3-H1, R3-H2, R3-H3, R3-M4: Ldsuperbyname acc, DefineGetterSetterByValue, OwnStoreKind ───

#[test]
fn r3_h1_h2_m4_superbyname_acc_gettersetter_set_name_and_deprecated_tonumeric() {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Ldai(Imm(88)), // receiver in acc
        Bytecode::Ldsuperbyname(Imm(0), PLACEHOLDER),
        Bytecode::Sta(Reg(0)), // obj
        Bytecode::Ldai(Imm(1)),
        Bytecode::Sta(Reg(1)), // key
        Bytecode::Ldai(Imm(2)),
        Bytecode::Sta(Reg(2)), // getter
        Bytecode::Ldai(Imm(3)),
        Bytecode::Sta(Reg(3)), // setter
        Bytecode::Ldtrue,      // set_name in acc!
        Bytecode::Definegettersetterbyvalue(Reg(0), Reg(1), Reg(2), Reg(3)),
        Bytecode::DeprecatedTonumeric(Reg(1)),
        Bytecode::Return,
    ])
    .unwrap();
    let m_h = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 4, 0);
    let prop_s = b.add_string("sup");
    b.relocate_code_id(m_h, offsets[1], 0, CodeEntity::String(prop_s))
        .unwrap();
    let file = decode(&b.finalize().unwrap()).unwrap();

    let mut m = lift_file(&file).expect("lift H1/H2/M4");
    verify_clean(&m);
    let sup_sym = m.sym.intern("sup");

    let (sup_res, sup_this) = m
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::LoadSuper {
                key: SuperKey::Name(n),
                this_value,
            } if n == sup_sym => Some((i.result.unwrap(), this_value)),
            _ => None,
        })
        .expect("LoadSuper emitted");
    assert_eq!(
        const_of(&m, sup_this),
        Const::number(88.0),
        "Ldsuperbyname must read receiver from acc"
    );

    let gs_set_name = m
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::DefineGetterSetterByValue { obj, set_name, .. } if obj == sup_res => Some(set_name),
            _ => None,
        })
        .expect("DefineGetterSetterByValue emitted");
    assert_eq!(
        const_of(&m, gs_set_name),
        Const::Bool(true),
        "DefineGetterSetterByValue must read set_name from acc"
    );

    assert!(m.insts.iter().any(|i| matches!(
        i.op,
        Op::UnaryOp {
            op: UnOp::ToNumeric,
            ..
        }
    )));
}

#[test]
fn r3_h3_own_store_kinds_distinguish_all_four_flavors() {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Lda(Reg(0)),
        Bytecode::Stownbyname(Imm(0), PLACEHOLDER, Reg(1)),
        Bytecode::Stownbynamewithnameset(Imm(0), PLACEHOLDER, Reg(1)),
        Bytecode::Definefieldbyname(Imm(0), PLACEHOLDER, Reg(1)),
        Bytecode::Definepropertybyname(Imm(0), PLACEHOLDER, Reg(1)),
        Bytecode::Stownbyvalue(Imm(0), Reg(1), Reg(2)),
        Bytecode::Stownbyvaluewithnameset(Imm(0), Reg(1), Reg(2)),
        Bytecode::CallruntimeDefinefieldbyvalue(Imm(0), Reg(2), Reg(1)),
        Bytecode::Stownbyindex(Imm(0), Reg(1), Imm(0)),
        Bytecode::CallruntimeDefinefieldbyindex(Imm(0), Imm(1), Reg(1)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let m_h = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 3);
    let k = b.add_string("k");
    for &idx in &[1usize, 2, 3, 4] {
        b.relocate_code_id(m_h, offsets[idx], 0, CodeEntity::String(k))
            .unwrap();
    }
    let file = decode(&b.finalize().unwrap()).unwrap();
    let m = lift_file(&file).expect("lift own-store kinds");
    verify_clean(&m);

    let name_kinds: Vec<OwnStoreKind> = m
        .insts
        .iter()
        .filter_map(|i| match i.op {
            Op::StoreOwnPropName { kind, .. } => Some(kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        name_kinds,
        vec![
            OwnStoreKind::OwnProp,
            OwnStoreKind::OwnPropWithNameSet,
            OwnStoreKind::ClassField,
            OwnStoreKind::DefineProperty,
        ]
    );

    let dyn_kinds: Vec<OwnStoreKind> = m
        .insts
        .iter()
        .filter_map(|i| match i.op {
            Op::StoreOwnPropDyn { kind, .. } => Some(kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        dyn_kinds,
        vec![
            OwnStoreKind::OwnProp,
            OwnStoreKind::OwnPropWithNameSet,
            OwnStoreKind::ClassField,
        ]
    );

    let idx_kinds: Vec<OwnStoreKind> = m
        .insts
        .iter()
        .filter_map(|i| match i.op {
            Op::StoreOwnPropIdx { kind, .. } => Some(kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        idx_kinds,
        vec![OwnStoreKind::OwnProp, OwnStoreKind::ClassField]
    );
}

// ─── R3-H9, #50, #58: Typed Catch::type_class, Arc<str> dedup & Lossless Literals ───

#[test]
fn r3_d2_a6_h9_typed_catch_synthesizes_external_class_and_deduplicates_source_code() {
    let mut strings = StringPool::default();
    let desc = strings.get_or_intern("LApp;");
    let foreign_exc = strings.get_or_intern("Lstd/core/TypeError;");
    let src_file = strings.get_or_intern("app.ets");
    let shared_src = strings.get_or_intern("function f1() {}\nfunction f2() {}\n");
    let f1_name = strings.get_or_intern("f1");
    let f2_name = strings.get_or_intern("f2");
    let impl_iface = strings.get_or_intern("LMyIface;");

    let mk_debug = || {
        Some(MethodDebugInfo {
            source_file: Some(src_file),
            source_code: Some(shared_src),
            line_table: Vec::new(),
            column_table: Vec::new(),
            local_vars: Vec::new(),
            params: Vec::new(),
        })
    };

    let m1 = Method {
        name: f1_name,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::ArkTs,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Createarraywithbuffer(Imm(0), EntityId(0)), // 0 (try)
                Bytecode::Return,                                     // 1
                Bytecode::Return,                                     // 2 (typed catch)
                Bytecode::Returnundefined,                            // 3 (catch-all)
            ],
            entities: HashMap::from([(
                (EntityKind::LiteralarrayId, 0),
                EntityRef::LiteralArray(LiteralArrayIdx(0)),
            )]),
            try_blocks: vec![TryBlock {
                start: 0,
                len: 2,
                catches: vec![
                    CatchBlock {
                        type_class: Some(foreign_exc),
                        handler: 2,
                        len: 1,
                    },
                    CatchBlock {
                        type_class: Some(desc),
                        handler: 3,
                        len: 1,
                    },
                ],
            }],
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: mk_debug(),
    };

    let m2 = Method {
        name: f2_name,
        offset: 0x200,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::ArkTs,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![Bytecode::Returnundefined],
            entities: HashMap::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: mk_debug(),
    };

    // Literal array 1 is referenced THREE different ways from literal array 0
    // (`LiteralArray`, `LiteralBufferIndex`, and `ArrayU8`) to prove wrapper
    // caches never collide (`R3-H9`)!
    let shared_inner = LiteralArray::new(vec![LiteralValue::Integer8(42)]);
    let root_lit = LiteralArray::new(vec![
        LiteralValue::Accessor(1),
        LiteralValue::MethodAffiliate(2),
        LiteralValue::BuiltinTypeIndex(3),
        LiteralValue::EtsImplements(impl_iface),
        LiteralValue::NullValue(0),
        LiteralValue::GeneratorMethod(MethodIdx(0)),
        LiteralValue::Setter(MethodIdx(1)),
        LiteralValue::LiteralArray(LiteralArrayIdx(1)),
        LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1)),
        LiteralValue::ArrayU8(vec![42]),
    ]);

    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::ArkTs,
        source_file: Some(src_file),
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![m1, m2],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let file = File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Static,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: vec![root_lit, shared_inner],
        literal_array_header_offsets: Vec::new(),
    };

    let mut ir = lift_file(&file).expect("lift typed catch + shared source_code + literals");
    verify_clean(&ir);

    // 1. Typed `Catch::type_class` synthesized `Lstd/core/TypeError;` cleanly.
    let catches = &ir.functions[0].try_regions[0].catches;
    assert_eq!(catches.len(), 2);
    let foreign_cid = catches[0].type_class.expect("foreign type_class");
    let local_cid = catches[1].type_class.expect("local type_class");
    assert_eq!(
        ir.sym.resolve(ir.classes[foreign_cid.index()].descriptor),
        Some("Lstd/core/TypeError;")
    );
    assert_eq!(
        ir.sym.resolve(ir.classes[local_cid.index()].descriptor),
        Some("LApp;")
    );

    // 2. `DebugData::source_code` shares one `Arc<str>` allocation across functions (`R3-A6`).
    let sc1 = ir.functions[0]
        .debug
        .as_ref()
        .and_then(|d| d.source_code.as_ref())
        .expect("f1 source_code");
    let sc2 = ir.functions[1]
        .debug
        .as_ref()
        .and_then(|d| d.source_code.as_ref())
        .expect("f2 source_code");
    assert!(
        Arc::ptr_eq(sc1, sc2),
        "functions in the same file must share one Arc<str> source_code allocation"
    );

    // 3. Lossless literal tags & non-colliding wrapper caches (`R3-H9`).
    let shape = ir
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::AllocArray { shape: Some(s) } => Some(s),
            _ => None,
        })
        .expect("AllocArray emitted");
    let c42 = ir.consts.intern(Const::Int8(42));
    let plain_inner = ir.consts.intern(Const::ArrayLiteral(vec![c42]));
    let buf_inner = ir.consts.intern(Const::LiteralBufferRef(plain_inner));
    let u8_inner = ir.consts.intern(Const::TypedArrayLiteral {
        tag: TypedArrayTag::U8,
        items: vec![c42],
    });
    let iface_sym = ir.sym.intern("LMyIface;");
    let expected = vec![
        ir.consts.intern(Const::Accessor(1)),
        ir.consts.intern(Const::MethodAffiliate(2)),
        ir.consts.intern(Const::BuiltinTypeIndex(3)),
        ir.consts.intern(Const::EtsImplements(iface_sym)),
        ir.consts.intern(Const::LitNull(0)),
        ir.consts.intern(Const::method_ref_with_kind(
            abcd_ir::FuncId::new(0),
            LitMethodKind::GeneratorMethod,
        )),
        ir.consts.intern(Const::method_ref_with_kind(
            abcd_ir::FuncId::new(1),
            LitMethodKind::Setter,
        )),
        plain_inner,
        buf_inner,
        u8_inner,
    ];
    assert_eq!(ir.consts.get(shape), Some(&Const::ArrayLiteral(expected)));
}

// ─── R3-X1 (#61): JumpEqz / JumpNez vs Proven-Boolean CondBranch ───────────

#[test]
fn r3_x1_raw_jeqz_jnez_vs_proven_boolean_cond_branch() {
    // 1. `ldnull; jeqz L`: NOT proven boolean -> emits `UnOp::JumpEqz`.
    let f_null_jeqz = build_single(
        &[
            Bytecode::Ldnull,
            Bytecode::Jeqz(Label(4)),
            Bytecode::Ldai(Imm(1)),
            Bytecode::Return,
            Bytecode::Ldai(Imm(2)),
            Bytecode::Return,
        ],
        0,
        0,
    );
    let m_null = lift_file(&f_null_jeqz).expect("lift ldnull; jeqz");
    verify_clean(&m_null);
    let entry_null = m_null.functions[0].blocks[0];
    let ops_null: Vec<&Op> = m_null.blocks[entry_null.index()]
        .insts
        .iter()
        .map(|&iid| &m_null.insts[iid.index()].op)
        .collect();
    assert!(
        ops_null.iter().any(|op| matches!(
            op,
            Op::UnaryOp {
                op: UnOp::JumpEqz,
                ..
            }
        )),
        "ldnull; jeqz must emit UnOp::JumpEqz, never IsFalse: {ops_null:?}"
    );

    // 2. `ldnan; jnez L`: NOT proven boolean -> emits `UnOp::JumpNez` with `DynPrim::Bool`.
    let f_nan_jnez = build_single(
        &[
            Bytecode::Ldnan,
            Bytecode::Jnez(Label(4)),
            Bytecode::Ldai(Imm(1)),
            Bytecode::Return,
            Bytecode::Ldai(Imm(2)),
            Bytecode::Return,
        ],
        0,
        0,
    );
    let m_nan = lift_file(&f_nan_jnez).expect("lift ldnan; jnez");
    verify_clean(&m_nan);
    let pred_val = m_nan
        .insts
        .iter()
        .find_map(|i| match i.op {
            Op::UnaryOp {
                op: UnOp::JumpNez, ..
            } => i.result,
            _ => None,
        })
        .expect("ldnan; jnez must emit UnOp::JumpNez");
    assert_eq!(
        m_nan.values[pred_val.index()].ty,
        Ty::DynPrim(DynPrim::Bool)
    );

    // 3. `eq; jnez L` and `eq; jeqz L`: proven boolean -> ZERO `UnaryOp` emitted!
    for (branch_bc, swapped) in [
        (Bytecode::Jnez(Label(5)), false),
        (Bytecode::Jeqz(Label(5)), true),
    ] {
        let f_cmp = build_single(
            &[
                Bytecode::Lda(Reg(0)),
                Bytecode::Eq(Imm(0), Reg(1)),
                branch_bc,
                Bytecode::Ldai(Imm(10)), // fallthrough block (blocks[1])
                Bytecode::Return,
                Bytecode::Ldai(Imm(20)), // target block L (blocks[2])
                Bytecode::Return,
            ],
            0,
            2,
        );
        let m_cmp = lift_file(&f_cmp).expect("lift cmp + branch");
        verify_clean(&m_cmp);
        assert!(
            !m_cmp
                .insts
                .iter()
                .any(|i| matches!(i.op, Op::UnaryOp { .. })),
            "proven-boolean Compare must branch directly without UnaryOp"
        );
        let cmp_res = m_cmp
            .insts
            .iter()
            .find_map(|i| matches!(i.op, Op::Compare { op: CmpOp::Eq, .. }).then_some(i.result?))
            .expect("Compare::Eq emitted");
        let fall_bb = m_cmp.functions[0].blocks[1];
        let target_bb = m_cmp.functions[0].blocks[2];
        let last_iid = *m_cmp.blocks[m_cmp.functions[0].blocks[0].index()]
            .insts
            .last()
            .unwrap();
        let Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } = m_cmp.insts[last_iid.index()].op
        else {
            panic!("expected CondBranch");
        };
        assert_eq!(cond, cmp_res);
        if swapped {
            assert_eq!((true_dest, false_dest), (fall_bb, target_bb));
        } else {
            assert_eq!((true_dest, false_dest), (target_bb, fall_bb));
        }
    }
}

// ─── R3-M3: Malformed Register / Range / Jump / Fallthrough / Try-Catch Guards ───

#[test]
fn r3_m3_malformed_bounds_return_typed_errors_without_panics() {
    // 1. Out-of-frame single register read & write.
    let bad_lda = single_body_model(
        2,
        1, // frame_limit = 3 (v0..=v2)
        vec![Bytecode::Lda(Reg(3)), Bytecode::Return],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_lda),
        Err(LiftError::InvalidRegister {
            reg: 3,
            frame_limit: 3
        })
    ));

    let bad_sta = single_body_model(
        1,
        0, // frame_limit = 1 (v0 only)
        vec![
            Bytecode::Ldundefined,
            Bytecode::Sta(Reg(1)),
            Bytecode::Return,
        ],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_sta),
        Err(LiftError::InvalidRegister {
            reg: 1,
            frame_limit: 1
        })
    ));

    // 2. Register range `u16` addition overflow (`start = 65530, count = 10`).
    let bad_range_overflow = single_body_model(
        10,
        0,
        vec![
            Bytecode::Ldundefined,
            Bytecode::WideCallrange(Imm(10), Reg(65530)),
            Bytecode::Return,
        ],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_range_overflow),
        Err(LiftError::RegisterRangeOverflow {
            start: 65530,
            count: 10
        })
    ));

    // 3. Register range exceeding `frame_limit` (`start = 1, count = 3` on `frame_limit = 3`).
    let bad_range_frame = single_body_model(
        2,
        1,
        vec![
            Bytecode::Ldundefined,
            Bytecode::Callrange(Imm(0), Imm(3), Reg(1)),
            Bytecode::Return,
        ],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_range_frame),
        Err(LiftError::InvalidRegister {
            reg: 3,
            frame_limit: 3
        })
    ));

    // 4. Out-of-bounds jump target.
    let bad_jmp = single_body_model(
        0,
        0,
        vec![Bytecode::Jmp(Label(5)), Bytecode::Returnundefined],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_jmp),
        Err(LiftError::JumpTargetOutOfBounds {
            pc: 0,
            target: 5,
            len: 2
        })
    ));

    // 5. Fallthrough past end of bytecode stream (non-terminator final instruction).
    let bad_fall = single_body_model(
        0,
        0,
        vec![Bytecode::Ldai(Imm(1))],
        HashMap::new(),
        Vec::new(),
    );
    assert!(matches!(
        lift_file(&bad_fall),
        Err(LiftError::FallthroughOutOfBounds { pc: 0, len: 1 })
    ));

    // 6. Out-of-bounds TryBlock and CatchBlock ranges.
    let bad_try = single_body_model(
        0,
        0,
        vec![Bytecode::Returnundefined],
        HashMap::new(),
        vec![TryBlock {
            start: 0,
            len: 2,
            catches: Vec::new(),
        }],
    );
    assert!(matches!(
        lift_file(&bad_try),
        Err(LiftError::TryRangeOutOfBounds {
            start: 0,
            len: 2,
            bytecode_len: 1
        })
    ));

    let bad_catch = single_body_model(
        0,
        0,
        vec![Bytecode::Ldundefined, Bytecode::Return],
        HashMap::new(),
        vec![TryBlock {
            start: 0,
            len: 1,
            catches: vec![CatchBlock {
                type_class: None,
                handler: 1,
                len: 5,
            }],
        }],
    );
    assert!(matches!(
        lift_file(&bad_catch),
        Err(LiftError::CatchRangeOutOfBounds {
            handler: 1,
            len: 5,
            bytecode_len: 2
        })
    ));
}

// ─── 256 KiB-Stack Deep Nested LiteralArray / TypedArrayLiteral Guard ──────

#[test]
fn deep_5000_nested_literal_and_typed_arrays_lift_on_256kib_stack() {
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 5_000usize;
            let mut literal_arrays = Vec::with_capacity(depth);
            for i in 0..depth {
                let val = if i + 1 == depth {
                    LiteralValue::ArrayI32(vec![-777, 777])
                } else if i % 2 == 0 {
                    LiteralValue::LiteralArray(LiteralArrayIdx((i + 1) as u32))
                } else {
                    LiteralValue::LiteralBufferIndex(LiteralArrayIdx((i + 1) as u32))
                };
                literal_arrays.push(LiteralArray::new(vec![val]));
            }

            let mut strings = StringPool::default();
            let desc = strings.get_or_intern("LDeepLit;");
            let fname = strings.get_or_intern("f");
            let method = Method {
                name: fname,
                offset: 0x100,
                access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                function_kind: FileFunctionKind::None,
                source_lang: FileSourceLang::EcmaScript,
                is_external: false,
                return_type: None,
                arg_types: Vec::new(),
                body: Some(MethodBody {
                    num_vregs: 0,
                    num_args: 0,
                    bytecodes: vec![
                        Bytecode::Createarraywithbuffer(Imm(0), EntityId(0)),
                        Bytecode::Return,
                    ],
                    entities: HashMap::from([(
                        (EntityKind::LiteralarrayId, 0),
                        EntityRef::LiteralArray(LiteralArrayIdx(0)),
                    )]),
                    try_blocks: Vec::new(),
                    ic_size: None,
                }),
                annotations: Default::default(),
                param_annotations: Default::default(),
                debug: None,
            };
            let class = abcd_file::Class {
                descriptor: desc,
                name: desc,
                access_flags: AccessFlags::PUBLIC,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: vec![method],
                fields: Vec::new(),
                annotations: Default::default(),
            };
            let file = File {
                version: Version::new(12, 0, 6, 0),
                checksum: 0,
                size: 0,
                file_type: FileType::Dynamic,
                strings,
                classes: [(desc, class)].into_iter().collect(),
                literal_arrays,
                literal_array_header_offsets: Vec::new(),
            };

            let ir = lift_file(&file).expect("lift 5000-deep nested literal arrays");
            verify_clean(&ir);
        })
        .unwrap();
    handle.join().unwrap();
}

// ─── #93 D3: Module::dialect & Pre-Method ClassData / Standalone Module ────

#[test]
fn module_dialect_and_pre_method_es_module_visibility() {
    // 1. DynamicModern (`12.0.6.0`), DynamicLegacy (`0.0.0.2`), and Static (`0.1.0.7`)
    //    map to `Dialect::DynamicEcma` vs `Dialect::StaticArkTS`.
    let make_dialect_file = |version: Version, file_type: FileType| -> File {
        let mut strings = StringPool::default();
        let desc = strings.get_or_intern("LDialect;");
        let cls = abcd_file::Class {
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
            annotations: Default::default(),
        };
        File {
            version,
            checksum: 0,
            size: 0,
            file_type,
            strings,
            classes: [(desc, cls)].into_iter().collect(),
            literal_arrays: Vec::new(),
            literal_array_header_offsets: Vec::new(),
        }
    };

    let m_mod = lift_file(&make_dialect_file(
        Version::new(12, 0, 6, 0),
        FileType::Dynamic,
    ))
    .unwrap();
    assert_eq!(m_mod.dialect, abcd_ir::Dialect::DynamicEcma);

    let m_leg = lift_file(&make_dialect_file(
        Version::new(0, 0, 0, 2),
        FileType::Dynamic,
    ))
    .unwrap();
    assert_eq!(m_leg.dialect, abcd_ir::Dialect::DynamicEcma);

    let m_stat = lift_file(&make_dialect_file(
        Version::new(0, 1, 0, 7),
        FileType::Static,
    ))
    .unwrap();
    assert_eq!(m_stat.dialect, abcd_ir::Dialect::StaticArkTS);

    // 2. Standalone `_ESModuleRecord` interned AFTER `L_GLOBAL;` (so `L_GLOBAL;`
    //    sorts earlier in `file.classes` `BTreeMap`) is STILL already lifted into
    //    `Module::{imports, exports, module_requests}` before `L_GLOBAL;::main`
    //    is translated (`D3`).
    let mut strings = StringPool::default();
    let global_desc = strings.get_or_intern("L_GLOBAL;"); // StringId(0) — sorts FIRST!
    let esm_desc = strings.get_or_intern(abcd_file::ES_MODULE_RECORD_DESCRIPTOR); // StringId(1) — sorts SECOND!
    let mod_field_name = strings.get_or_intern("moduleRecordIdx");
    let main_name = strings.get_or_intern("func_main_0");
    let req_dep = strings.get_or_intern("./dep");
    let imp_a = strings.get_or_intern("impA");
    let imp_b = strings.get_or_intern("impB");
    let exp_x = strings.get_or_intern("expX");
    let exp_y = strings.get_or_intern("expY");

    let main_method = Method {
        name: main_name,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)), // External `impB` -> slot 1
                Bytecode::DeprecatedStmodulevar(EntityId(1)),         // Local `expY` -> slot 1
                Bytecode::Returnundefined,
            ],
            entities: HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(imp_b)),
                ((EntityKind::StringId, 1), EntityRef::string(exp_y)),
            ]),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };
    let global_cls = abcd_file::Class {
        descriptor: global_desc,
        name: global_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![main_method],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let esm_cls = abcd_file::Class {
        descriptor: esm_desc,
        name: esm_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![abcd_file::Field {
            name: mod_field_name,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(abcd_file::FieldValue::ModuleData(abcd_file::ModuleData {
                source_offset: 0,
                requests: vec![req_dep],
                records: vec![
                    abcd_file::ModuleRecord::RegularImport {
                        local_name: imp_a,
                        import_name: imp_a,
                        module_request_idx: 0,
                    },
                    abcd_file::ModuleRecord::RegularImport {
                        local_name: imp_b,
                        import_name: imp_b,
                        module_request_idx: 0,
                    },
                    abcd_file::ModuleRecord::LocalExport {
                        local_name: exp_x,
                        export_name: exp_x,
                    },
                    abcd_file::ModuleRecord::LocalExport {
                        local_name: exp_y,
                        export_name: exp_y,
                    },
                ],
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    let standalone_esm_file = File {
        version: Version::new(0, 0, 0, 2),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(global_desc, global_cls), (esm_desc, esm_cls)]
            .into_iter()
            .collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };

    let ir = lift_file(&standalone_esm_file).expect("lift standalone legacy ESM");
    verify_clean(&ir);
    let ld = ir
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::LoadModuleVar { index, kind } => Some((*index, *kind)),
            _ => None,
        })
        .expect("LoadModuleVar");
    let st = ir
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::StoreModuleVar { index, .. } => Some(*index),
            _ => None,
        })
        .expect("StoreModuleVar");
    assert_eq!(ld, (1, abcd_ir::ModuleVarKind::External));
    assert_eq!(st, 1);
}

#[test]
fn dead_predecessor_sweep_cascades_newly_trivial_phi_to_zero_phis() {
    // Bytecode layout:
    //   0..3: `ldai 5; sta v0; jmp 6` (live entry jumps directly to join at 6)
    //   3..6: `ldai 99; sta v0; jmp 6` (dead unreachable island feeding join at 6!)
    //   6..8: `lda v0; return` (join has 2 predecessors during Braun SSA: live [0..3)
    //         with `v0 = 5` and dead [3..6) with `v0 = 99` -> non-trivial 2-entry Phi
    //         before `sweep_dead_blocks`; once `sweep_dead_blocks` prunes [3..6),
    //         `finalize_function` collapses the 1-entry Phi to `5` and removes it!)
    let f = build_single(
        &[
            Bytecode::Ldai(Imm(5)),  // 0
            Bytecode::Sta(Reg(0)),   // 1
            Bytecode::Jmp(Label(6)), // 2 -> join
            Bytecode::Ldai(Imm(99)), // 3 (unreachable island)
            Bytecode::Sta(Reg(0)),   // 4
            Bytecode::Jmp(Label(6)), // 5 -> join
            Bytecode::Lda(Reg(0)),   // 6 (join)
            Bytecode::Return,        // 7
        ],
        1,
        0,
    );
    let ir = lift_file(&f).expect("lift dead-island join");
    verify_clean(&ir);
    let func = &ir.functions[0];
    let phi_count: usize = func
        .blocks
        .iter()
        .flat_map(|&bb| &ir.blocks[bb.index()].insts)
        .filter(|&&iid| ir.insts[iid.index()].op.is_phi())
        .count();
    assert_eq!(
        phi_count, 0,
        "post-sweep 1-predecessor trivial phi must be collapsed and removed"
    );
}
