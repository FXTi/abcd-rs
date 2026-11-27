//! Coverage for abcd-lift/src/resolve.rs — entity resolution and
//! literal-array → Const conversion — through hand-built file models
//! (the lift_unit.rs struct-literal precedent):
//!
//! - `class_member_attrs` kinds (Getter/Setter/GeneratorMethod/
//!   AsyncGeneratorMethod — corpus member buffers carry plain methods
//!   only) and its conservative fallbacks (ungrounded buffer shapes
//!   yield an EMPTY attribute vector, never a guess);
//! - `const_for_literal_value`'s rare kinds (Integer8/Float/
//!   BuiltinTypeIndex/LiteralBufferIndex/the typed ARRAY_* family —
//!   N52: no corpus trigger) plus the literal-tree cache hit;
//! - `typed_array_table_index` (offset-map hit, direct-index fallback,
//!   miss);
//! - the ERROR paths: unregistered EntityIds (resolve_sym /
//!   resolve_method / literal_table_index), LiteralArrayOutOfRange,
//!   LiteralArrayCycle.
//!
//! The consumer bytecodes are `deprecated.createarraywithbuffer`
//! (raw table index — no entity relocation needed) and
//! `defineclasswithbuffer` (entity-offset indirection, wired through
//! `MethodBody::entity_offsets`).

use std::collections::HashMap;

use abcd_file::{
    AccessFlags, EntityRef, FileType, FunctionKind as FileFunctionKind, LiteralArrayIdx,
    LiteralValue, MethodIdx, SourceLang as FileSourceLang, Version,
};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Const, LitMethodKind, Op, TypedArrayTag};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg};
use abcd_lift::{LiftError, lift_file};

/// Build the class shell around the given methods.
fn model(
    strings: abcd_file::StringPool,
    desc: abcd_file::StringId,
    methods: Vec<abcd_file::Method>,
    literal_arrays: Vec<Vec<LiteralValue>>,
) -> abcd_file::File {
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods,
        fields: Vec::new(),
        annotations: Default::default(),
    };
    abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: literal_arrays
            .into_iter()
            .map(abcd_file::LiteralArray::new)
            .collect(),
        literal_array_header_offsets: Vec::new(),
    }
}

/// A method record with the given name/offset/bytecodes/entity map.
fn method(
    strings: &mut abcd_file::StringPool,
    name: &str,
    offset: u32,
    bytecodes: Vec<Bytecode>,
    entities: HashMap<(EntityKind, u32), EntityRef>,
) -> abcd_file::Method {
    abcd_file::Method {
        name: strings.get_or_intern(name),
        offset,
        access_flags: AccessFlags::PUBLIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(abcd_file::MethodBody {
            num_vregs: 1,
            num_args: 0,
            code: abcd_file::MethodCode::Decoded(bytecodes),
            entities: entities.into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    }
}

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

// ── class_member_attrs ───────────────────────────────────────────────

/// The literal-array entity id / offset wiring shared by the
/// defineclasswithbuffer tests: the buffer is literal_arrays[0], the
/// ctor is the method at offset 100.
const METHOD_EID: u32 = 5;
const LIT_EID: u32 = 6;
const CTOR_OFFSET: u32 = 100;

fn defineclass_file(
    buffer: impl FnOnce(abcd_file::StringId) -> Vec<LiteralValue>,
) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let x = strings.get_or_intern("x");
    let ctor = method(
        &mut strings,
        "A",
        CTOR_OFFSET,
        vec![Bytecode::Returnundefined],
        HashMap::new(),
    );
    let mem = method(
        &mut strings,
        "mem",
        0,
        vec![Bytecode::Returnundefined],
        HashMap::new(),
    );
    let main = method(
        &mut strings,
        "main",
        0,
        vec![
            Bytecode::Defineclasswithbuffer(
                Imm(0),
                EntityId(METHOD_EID),
                EntityId(LIT_EID),
                Imm(2),
                Reg(0),
            ),
            Bytecode::Returnundefined,
        ],
        HashMap::from([
            (
                (EntityKind::MethodId, METHOD_EID),
                EntityRef::Method(MethodIdx(0)),
            ),
            (
                (EntityKind::LiteralarrayId, LIT_EID),
                EntityRef::LiteralArray(LiteralArrayIdx(0)),
            ),
        ]),
    );
    model(strings, desc, vec![ctor, mem, main], vec![buffer(x)])
}

/// Lift and extract the DefineClass op's member_attrs.
fn lifted_attrs(file: &abcd_file::File) -> (Vec<MemberAttrs>, abcd_ir::Module) {
    let m = lift_file(file).expect("lift");
    verify_clean(&m);
    for inst in &m.insts {
        if let Op::DefineClass(data) = &inst.op {
            return (data.member_attrs.clone(), m);
        }
    }
    panic!("DefineClass emitted")
}

#[test]
fn member_attrs_carry_the_callable_kinds() {
    type KindCase = (fn(MethodIdx) -> LiteralValue, FunctionKind);
    let cases: [KindCase; 4] = [
        (LiteralValue::Getter, FunctionKind::Getter),
        (LiteralValue::Setter, FunctionKind::Setter),
        (LiteralValue::GeneratorMethod, FunctionKind::Generator),
        (
            LiteralValue::AsyncGeneratorMethod,
            FunctionKind::AsyncGenerator,
        ),
    ];
    for (mk, want_kind) in cases {
        let file = defineclass_file(|x| {
            vec![
                LiteralValue::String(x),
                mk(MethodIdx(1)),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::Integer(1), // one non-static member
            ]
        });
        let (attrs, _m) = lifted_attrs(&file);
        assert_eq!(
            attrs,
            vec![MemberAttrs {
                is_static: false,
                kind: want_kind,
            }],
            "kind tag → {want_kind:?}"
        );
    }
}

#[test]
fn member_attrs_conservative_fallbacks() {
    type BufferCase = (&'static str, fn(abcd_file::StringId) -> Vec<LiteralValue>);
    let cases: Vec<BufferCase> = vec![
        ("name collision (string after string)", |x| {
            vec![
                LiteralValue::String(x),
                LiteralValue::String(x),
                LiteralValue::Integer(0),
            ]
        }),
        ("method before any name", |_| {
            vec![LiteralValue::Method(MethodIdx(1)), LiteralValue::Integer(0)]
        }),
        ("affiliate without a pending kind", |x| {
            vec![
                LiteralValue::String(x),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::Integer(0),
            ]
        }),
        ("trailing name after a complete triple", |x| {
            vec![
                LiteralValue::String(x),
                LiteralValue::Method(MethodIdx(1)),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::String(x),
            ]
        }),
        ("trailing kind after a complete triple", |x| {
            vec![
                LiteralValue::String(x),
                LiteralValue::Method(MethodIdx(1)),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::Method(MethodIdx(1)),
            ]
        }),
    ];
    for (what, mk) in cases {
        let file = defineclass_file(mk);
        let (attrs, _m) = lifted_attrs(&file);
        assert!(attrs.is_empty(), "{what}: conservative empty fallback");
    }
}

// ── const_for_literal_value kinds + the literal-tree cache ───────────

fn literal_consumer_file(
    bytecodes: Vec<Bytecode>,
    arrays: Vec<Vec<LiteralValue>>,
) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(&mut strings, "f", 0, bytecodes, HashMap::new());
    model(strings, desc, vec![f], arrays)
}

/// The lifted module and pooled shape `ConstId` of the single AllocArray in `f`.
fn lifted_array_shape(file: &abcd_file::File) -> (abcd_ir::Module, abcd_ir::ConstId) {
    let m = lift_file(file).expect("lift");
    verify_clean(&m);
    let alloc = m
        .insts
        .iter()
        .find(|i| matches!(i.op, Op::AllocArray { shape: Some(_) }))
        .expect("AllocArray emitted");
    let Op::AllocArray { shape: Some(shape) } = alloc.op else {
        unreachable!()
    };
    (m, shape)
}

#[test]
fn literal_value_rare_kinds() {
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![vec![
            LiteralValue::Integer8(7),
            LiteralValue::Float(2.5),
            LiteralValue::BuiltinTypeIndex(4),
            LiteralValue::AsyncGeneratorMethod(MethodIdx(0)),
            LiteralValue::Getter(MethodIdx(0)),
        ]],
    );
    let (mut m, shape) = lifted_array_shape(&file);
    let c7 = m.consts.intern(Const::Int8(7));
    let c25 = m.consts.intern(Const::float32(2.5));
    let c4 = m.consts.intern(Const::BuiltinTypeIndex(4));
    let cag = m.consts.intern(Const::method_ref_with_kind(
        abcd_ir::FuncId::new(0),
        LitMethodKind::AsyncGeneratorMethod,
    ));
    let cget = m.consts.intern(Const::method_ref_with_kind(
        abcd_ir::FuncId::new(0),
        LitMethodKind::Getter,
    ));
    assert_eq!(
        m.consts.get(shape),
        Some(&Const::ArrayLiteral(vec![c7, c25, c4, cag, cget])),
        "every literal value kind becomes a lossless typed Const (`R3-H9`)"
    );
}

#[test]
fn literal_tree_cache_hit_on_second_reference() {
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![vec![LiteralValue::Integer(1)]],
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let shapes: Vec<abcd_ir::ConstId> = m
        .insts
        .iter()
        .filter_map(|i| match i.op {
            Op::AllocArray { shape: Some(s) } => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(shapes.len(), 2, "two buffer consumers");
    assert_eq!(
        shapes[0], shapes[1],
        "the second reference reuses the cached tree (and the shape dedup)"
    );
}

#[test]
fn typed_array_payloads_preserve_exact_typed_array_tags() {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let s1 = strings.get_or_intern("alpha");
    let s2 = strings.get_or_intern("beta");
    let nan32 = f32::from_bits(0x7fc0_1234);
    let nan64 = f64::from_bits(0x7ff8_0000_1234_5678);

    let outer = vec![
        LiteralValue::ArrayU1(vec![true, false]),
        LiteralValue::ArrayU8(vec![0, 255]),
        LiteralValue::ArrayI8(vec![i8::MIN, -1, i8::MAX]),
        LiteralValue::ArrayU16(vec![0, 258, u16::MAX]),
        LiteralValue::ArrayI16(vec![i16::MIN, -258, i16::MAX]),
        LiteralValue::ArrayU32(vec![0, 0x89AB_CDEF, u32::MAX]),
        LiteralValue::ArrayI32(vec![i32::MIN, -123_456, i32::MAX]),
        LiteralValue::ArrayU64(vec![0, 0x0123_4567_89AB_CDEF, u64::MAX]),
        LiteralValue::ArrayI64(vec![i64::MIN, -9_876_543_210, i64::MAX]),
        LiteralValue::ArrayF32(vec![-0.0, nan32]),
        LiteralValue::ArrayF64(vec![-0.0, nan64]),
        LiteralValue::ArrayString(vec![s1, s2]),
    ];
    let f = method(
        &mut strings,
        "f",
        0,
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        HashMap::new(),
    );
    let file = model(strings, desc, vec![f], vec![outer]);
    let (mut m, shape) = lifted_array_shape(&file);
    let sym_alpha = m.sym.intern("alpha");
    let sym_beta = m.sym.intern("beta");
    fn intern_ta(
        m: &mut abcd_ir::Module,
        tag: TypedArrayTag,
        vals: Vec<Const>,
    ) -> abcd_ir::ConstId {
        let items = vals.into_iter().map(|c| m.consts.intern(c)).collect();
        m.consts.intern(Const::TypedArrayLiteral { tag, items })
    }
    let expected_ids = vec![
        intern_ta(
            &mut m,
            TypedArrayTag::U1,
            vec![Const::Bool(true), Const::Bool(false)],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::U8,
            vec![Const::Int8(0), Const::Int8(255)],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::I8,
            vec![
                Const::Int8(i8::MIN as u8),
                Const::Int8(-1i8 as u8),
                Const::Int8(i8::MAX as u8),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::U16,
            vec![
                Const::Int32(0),
                Const::Int32(258),
                Const::Int32(u32::from(u16::MAX)),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::I16,
            vec![
                Const::Int32(i32::from(i16::MIN) as u32),
                Const::Int32(-258i32 as u32),
                Const::Int32(i32::from(i16::MAX) as u32),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::U32,
            vec![
                Const::Int32(0),
                Const::Int32(0x89AB_CDEF),
                Const::Int32(u32::MAX),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::I32,
            vec![
                Const::Int32(i32::MIN as u32),
                Const::Int32(-123_456i32 as u32),
                Const::Int32(i32::MAX as u32),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::U64,
            vec![
                Const::UInt64(0),
                Const::UInt64(0x0123_4567_89AB_CDEF),
                Const::UInt64(u64::MAX),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::I64,
            vec![
                Const::Int64(i64::MIN),
                Const::Int64(-9_876_543_210),
                Const::Int64(i64::MAX),
            ],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::F32,
            vec![Const::float32(-0.0), Const::float32(nan32)],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::F64,
            vec![Const::number(-0.0), Const::number(nan64)],
        ),
        intern_ta(
            &mut m,
            TypedArrayTag::String,
            vec![Const::String(sym_alpha), Const::String(sym_beta)],
        ),
    ];
    assert_eq!(
        m.consts.get(shape),
        Some(&Const::ArrayLiteral(expected_ids)),
        "every inline typed-array payload preserves its TypedArrayTag and exact bits (`R1-5`)"
    );
}

#[test]
fn literal_buffer_index_wraps_in_literal_buffer_ref() {
    let inner = vec![LiteralValue::Integer(9)];
    let outer = vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer, inner],
    );
    let (mut m, shape) = lifted_array_shape(&file);
    let c9 = m.consts.intern(Const::Int32(9));
    let inner_cid = m.consts.intern(Const::ArrayLiteral(vec![c9]));
    let buf_ref_cid = m.consts.intern(Const::LiteralBufferRef(inner_cid));
    assert_eq!(
        m.consts.get(shape),
        Some(&Const::ArrayLiteral(vec![buf_ref_cid]))
    );
}

#[test]
fn dangling_typed_array_string_element_is_an_error() {
    let mut other = abcd_file::StringPool::default();
    for i in 0..8 {
        other.get_or_intern(format!("pad{i}"));
    }
    let ghost = other.get_or_intern("ghost");
    let outer = vec![LiteralValue::ArrayString(vec![ghost])];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer],
    );
    let err = lift_file(&file).expect_err("dangling StringId in ArrayString must fail");
    assert!(
        matches!(err, LiftError::UnresolvedEntity(id) if id == ghost.index() as u32),
        "got {err:?}"
    );
}

#[test]
fn field_value_string_lifts_to_string_constant() {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LStrField;");
    let str_cls = strings.get_or_intern("Lstd/core/String;");
    let fname = strings.get_or_intern("GREETING");
    let fval = strings.get_or_intern("hello arkts");
    let cls = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::ArkTs,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![abcd_file::Field {
            name: fname,
            offset: 0,
            field_type: abcd_file::Type::Reference(str_cls),
            access_flags: abcd_file::AccessFlags::PUBLIC | abcd_file::AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(abcd_file::FieldValue::String(fval)),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    let file = abcd_file::File {
        version: Version::new(0, 1, 0, 7),
        checksum: 0,
        size: 0,
        file_type: FileType::Static,
        strings,
        classes: [(desc, cls)].into_iter().collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };
    let mut m = lift_file(&file).expect("FieldValue::String lifts cleanly");
    verify_clean(&m);
    assert_eq!(m.dialect, abcd_ir::Dialect::StaticArkTS);
    let want_sym = m.sym.intern("hello arkts");
    let init_cid = m.classes[0].fields[0]
        .initial_value
        .expect("initial_value populated");
    assert_eq!(m.consts.get(init_cid), Some(&Const::String(want_sym)));
}

// ── Error paths ──────────────────────────────────────────────────────

#[test]
fn literal_array_table_index_out_of_range() {
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(9)),
            Bytecode::Returnundefined,
        ],
        vec![vec![LiteralValue::Integer(1)]],
    );
    let err = lift_file(&file).expect_err("table index 9 out of range");
    assert!(
        matches!(err, LiftError::LiteralArrayOutOfRange(9)),
        "got {err:?}"
    );
}

#[test]
fn literal_array_cycle_is_an_error() {
    let cyclic = vec![LiteralValue::LiteralArray(LiteralArrayIdx(0))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![cyclic],
    );
    let err = lift_file(&file).expect_err("self-referential literal array");
    assert!(
        matches!(err, LiftError::LiteralArrayCycle(0)),
        "got {err:?}"
    );
}

#[test]
fn resolve_sym_unregistered_entity_id() {
    let file = literal_consumer_file(
        vec![Bytecode::LdaStr(EntityId(5)), Bytecode::Returnundefined],
        Vec::new(),
    );
    let err = lift_file(&file).expect_err("unregistered string id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

#[test]
fn resolve_sym_dangling_file_string() {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let mut other = abcd_file::StringPool::default();
    for i in 0..8 {
        other.get_or_intern(format!("pad{i}"));
    }
    let ghost = other.get_or_intern("ghost");
    let f = method(
        &mut strings,
        "f",
        0,
        vec![Bytecode::LdaStr(EntityId(5)), Bytecode::Returnundefined],
        HashMap::from([((EntityKind::StringId, 5), EntityRef::string(ghost))]),
    );
    let file = model(strings, desc, vec![f], Vec::new());
    let err = lift_file(&file).expect_err("dangling string id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

#[test]
fn resolve_method_error_chain() {
    let definefunc = || {
        vec![
            Bytecode::Definefunc(Imm(0), EntityId(5), Imm(0)),
            Bytecode::Returnundefined,
        ]
    };

    // 1. No (MethodId, 5) entry at all.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(&mut strings, "f", 0, definefunc(), HashMap::new());
    let file = model(strings, desc, vec![f], Vec::new());
    let err = lift_file(&file).expect_err("unregistered method id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");

    // 2. Out-of-bounds MethodIdx(999).
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(
        &mut strings,
        "f",
        0,
        definefunc(),
        HashMap::from([((EntityKind::MethodId, 5), EntityRef::Method(MethodIdx(999)))]),
    );
    let file = model(strings, desc, vec![f], Vec::new());
    let err = lift_file(&file).expect_err("MethodIdx(999) out of bounds");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");

    // 3. ExternalMethod in Definefunc is rejected as UnresolvedEntity(5).
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let ext_name = strings.get_or_intern("ext");
    let f = method(
        &mut strings,
        "f",
        0,
        definefunc(),
        HashMap::from([(
            (EntityKind::MethodId, 5),
            EntityRef::ExternalMethod {
                name: ext_name,
                source_offset: 0x300,
            },
        )]),
    );
    let file = model(strings, desc, vec![f], Vec::new());
    let err = lift_file(&file).expect_err("external method in definefunc");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

#[test]
fn literal_table_index_unregistered_entity_id() {
    let file = literal_consumer_file(
        vec![
            Bytecode::Createarraywithbuffer(Imm(0), EntityId(5)),
            Bytecode::Returnundefined,
        ],
        Vec::new(),
    );
    let err = lift_file(&file).expect_err("unregistered literal-array id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

// ── Deep-nesting iterative stack guards (#37-B) ──────────────────────

#[test]
fn deep_literal_array_chain_lifts_without_recursion_overflow() {
    // 512-deep nested LiteralArray chain (0 → 1 → … → 511 → [42]),
    // plus a 4,000-deep chain ending in a cycle to verify iterative
    // traversal and active-set cleanup on error.
    let depth = 512usize;
    let mut arrays = Vec::with_capacity(depth);
    for i in 0..depth {
        if i + 1 < depth {
            arrays.push(vec![LiteralValue::LiteralArray(LiteralArrayIdx(
                (i + 1) as u32,
            ))]);
        } else {
            arrays.push(vec![LiteralValue::Integer(42)]);
        }
    }
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        arrays,
    );
    let (mut m, mut cur_cid) = lifted_array_shape(&file);
    for _ in 0..depth - 1 {
        let Some(Const::ArrayLiteral(elems)) = m.consts.get(cur_cid) else {
            panic!("expected nested ArrayLiteral");
        };
        assert_eq!(elems.len(), 1);
        cur_cid = elems[0];
    }
    let c42 = m.consts.intern(Const::Int32(42));
    assert_eq!(m.consts.get(cur_cid), Some(&Const::ArrayLiteral(vec![c42])));

    let cyc_depth = 4_000usize;
    let mut cyc_arrays = Vec::with_capacity(cyc_depth);
    for i in 0..cyc_depth {
        let next = if i + 1 < cyc_depth { i + 1 } else { 0 };
        cyc_arrays.push(vec![LiteralValue::LiteralArray(LiteralArrayIdx(
            next as u32,
        ))]);
    }
    let cyc_file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        cyc_arrays,
    );
    let err = lift_file(&cyc_file).expect_err("4000-deep literal cycle");
    assert!(
        matches!(err, LiftError::LiteralArrayCycle(0)),
        "got {err:?}"
    );
}

#[test]
fn unreachable_sealed_single_pred_cycle_lifts_and_verifies() {
    use abcd_isa::Label;
    let file = literal_consumer_file(
        vec![
            Bytecode::Returnundefined, // 0 (B0)
            Bytecode::Jmp(Label(2)),   // 1 (B1 → B2)
            Bytecode::Ldtrue,          // 2 (B2)
            Bytecode::Jeqz(Label(1)),  // 3 (B2 → B1 or fallthrough B3)
            Bytecode::Lda(Reg(0)),     // 4 (B3 reads v0 across B1 <-> B2)
            Bytecode::Return,          // 5
        ],
        Vec::new(),
    );
    let m = lift_file(&file).expect("lift dead cycle without hanging");
    verify_clean(&m);
}
