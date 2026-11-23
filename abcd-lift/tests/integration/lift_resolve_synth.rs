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
    AccessFlags, FileType, FunctionKind as FileFunctionKind, LiteralArrayIdx, LiteralValue,
    SourceLang as FileSourceLang, Version,
};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Const, Op};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg};
use abcd_lift::{LiftError, lift_file};

/// Build the class shell around the given methods.
fn model(
    strings: abcd_file::StringPool,
    desc: abcd_file::StringId,
    methods: Vec<abcd_file::Method>,
    literal_arrays: Vec<Vec<LiteralValue>>,
    entity_map: HashMap<u32, abcd_file::StringId>,
    literal_array_offsets: HashMap<u32, u32>,
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
            .map(|values| abcd_file::LiteralArray { values })
            .collect(),
        entity_map,
        literal_array_offsets,
        literal_array_header_offsets: Vec::new(),
        string_raw_bytes: Default::default(),
    }
}

/// A method record with the given name/offset/bytecodes/entity map.
fn method(
    strings: &mut abcd_file::StringPool,
    name: &str,
    offset: u32,
    bytecodes: Vec<Bytecode>,
    entity_offsets: HashMap<(EntityKind, u32), u32>,
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
            bytecodes,
            entity_offsets,
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
const LIT_OFFSET: u32 = 200;

/// Build a file whose `main` runs `defineclasswithbuffer` over the
/// given member buffer; the ctor `A` (offset 100) and the member
/// `mem` (offset 0 — the hand-built identity) are the buffer targets.
/// `buffer` receives the file pool's "x" sid for member-name entries.
fn defineclass_file(
    buffer: impl FnOnce(abcd_file::StringId) -> Vec<LiteralValue>,
) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let ctor_name = strings.get_or_intern("A");
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
            ((EntityKind::MethodId, METHOD_EID), CTOR_OFFSET),
            ((EntityKind::LiteralarrayId, LIT_EID), LIT_OFFSET),
        ]),
    );
    model(
        strings,
        desc,
        vec![ctor, mem, main],
        vec![buffer(x)],
        HashMap::from([(CTOR_OFFSET, ctor_name)]),
        HashMap::from([(LIT_OFFSET, 0)]),
    )
}

/// Lift and extract the DefineClass op's member_attrs.
fn lifted_attrs(file: &abcd_file::File) -> (Vec<MemberAttrs>, abcd_ir::Module) {
    let m = lift_file(file).expect("lift");
    verify_clean(&m);
    for inst in &m.insts {
        if let Op::DefineClass { member_attrs, .. } = &inst.op {
            return (member_attrs.clone(), m);
        }
    }
    panic!("DefineClass emitted")
}

#[test]
fn member_attrs_carry_the_callable_kinds() {
    // resolve.rs:148-152 — the method-kind tag of each entry selects
    // the MemberAttrs kind; the trailing i32 is the non-static count.
    type KindCase = (fn(u32) -> LiteralValue, FunctionKind);
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
                mk(0), // → the offset-0 member method
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
    // resolve.rs:134 (name collision), :144 (method before name), :157
    // (affiliate without a pending kind), :174 (trailing name/kind) —
    // every ungrounded shape yields an EMPTY vector, never a guess.
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
            vec![LiteralValue::Method(0), LiteralValue::Integer(0)]
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
                LiteralValue::Method(0),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::String(x),
            ]
        }),
        ("trailing kind after a complete triple", |x| {
            vec![
                LiteralValue::String(x),
                LiteralValue::Method(0),
                LiteralValue::MethodAffiliate(1),
                LiteralValue::Method(0),
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

/// A file whose single method `f` runs the given consumer bytecodes
/// over literal_arrays[0].
fn literal_consumer_file(
    bytecodes: Vec<Bytecode>,
    arrays: Vec<Vec<LiteralValue>>,
    literal_array_offsets: HashMap<u32, u32>,
) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(&mut strings, "f", 0, bytecodes, HashMap::new());
    model(
        strings,
        desc,
        vec![f],
        arrays,
        HashMap::new(),
        literal_array_offsets,
    )
}

/// The pooled shape constant of the single AllocArray in `f`.
fn lifted_array_shape(file: &abcd_file::File) -> Const {
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
    m.consts.get(shape).expect("const").clone()
}

#[test]
fn literal_value_rare_kinds() {
    // resolve.rs:235 (Integer8), :237 (Float), :249-250
    // (AsyncGeneratorMethod/Getter arm lines), :257 (BuiltinTypeIndex).
    // Method references resolve through the pass-1 table: offset 0 is
    // the file's own single method `f` (FuncId 0).
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![vec![
            LiteralValue::Integer8(7),
            LiteralValue::Float(2.5),
            LiteralValue::BuiltinTypeIndex(4),
            LiteralValue::AsyncGeneratorMethod(0),
            LiteralValue::Getter(0),
        ]],
        HashMap::new(),
    );
    let shape = lifted_array_shape(&file);
    assert_eq!(
        shape,
        Const::ArrayLiteral(vec![
            Const::number(7.0),
            Const::number(2.5),
            Const::number(4.0),
            Const::MethodRef(abcd_ir::FuncId::new(0)),
            Const::MethodRef(abcd_ir::FuncId::new(0)),
        ]),
        "every literal value kind becomes a typed Const"
    );
}

#[test]
fn literal_tree_cache_hit_on_second_reference() {
    // resolve.rs:205 — the same table index consumed twice hits the
    // memoized tree.
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![vec![LiteralValue::Integer(1)]],
        HashMap::new(),
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
fn typed_array_payloads_resolve_through_the_direct_index_fallback() {
    // resolve.rs:275-292 (all twelve ARRAY_* tags) + :303-305
    // (typed_array_table_index's direct-index fallback for hand-built
    // models). Each payload is the table index 1 — the inner array.
    let inner = vec![LiteralValue::Integer(9)];
    let outer = vec![
        LiteralValue::ArrayU1(LiteralArrayIdx(1)),
        LiteralValue::ArrayU8(LiteralArrayIdx(1)),
        LiteralValue::ArrayI8(LiteralArrayIdx(1)),
        LiteralValue::ArrayU16(LiteralArrayIdx(1)),
        LiteralValue::ArrayI16(LiteralArrayIdx(1)),
        LiteralValue::ArrayU32(LiteralArrayIdx(1)),
        LiteralValue::ArrayI32(LiteralArrayIdx(1)),
        LiteralValue::ArrayU64(LiteralArrayIdx(1)),
        LiteralValue::ArrayI64(LiteralArrayIdx(1)),
        LiteralValue::ArrayF32(LiteralArrayIdx(1)),
        LiteralValue::ArrayF64(LiteralArrayIdx(1)),
        LiteralValue::ArrayString(LiteralArrayIdx(1)),
    ];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer, inner],
        HashMap::new(),
    );
    let shape = lifted_array_shape(&file);
    let inner_tree = Const::ArrayLiteral(vec![Const::number(9.0)]);
    assert_eq!(
        shape,
        Const::ArrayLiteral(vec![inner_tree; 12]),
        "every typed-array payload resolves to the target array's tree \
         (the element-type tag is a lowering concern — documented)"
    );
}

#[test]
fn typed_array_payloads_prefer_the_offset_map() {
    // resolve.rs:300-301 — the raw payload is a FILE OFFSET on the
    // wire; the offset → index map wins when it has an entry.
    let inner = vec![LiteralValue::Integer(9)];
    let outer = vec![LiteralValue::ArrayF64(LiteralArrayIdx(55))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer, inner],
        HashMap::from([(55, 1)]),
    );
    let shape = lifted_array_shape(&file);
    assert_eq!(
        shape,
        Const::ArrayLiteral(vec![Const::ArrayLiteral(vec![Const::number(9.0)])]),
        "offset 55 maps to table index 1"
    );
}

#[test]
fn literal_buffer_index_resolves_like_a_typed_array() {
    // resolve.rs:266-269 — LiteralBufferIndex payloads are raw offsets
    // (N52), resolved through the same helper.
    let inner = vec![LiteralValue::Integer(9)];
    let outer = vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer, inner],
        HashMap::new(),
    );
    let shape = lifted_array_shape(&file);
    assert_eq!(
        shape,
        Const::ArrayLiteral(vec![Const::ArrayLiteral(vec![Const::number(9.0)])])
    );
}

#[test]
fn unresolvable_typed_array_payload_is_an_error() {
    // resolve.rs:287-288,306 — neither the offset map nor the
    // direct-index fallback covers the payload.
    let inner = vec![LiteralValue::Integer(9)];
    let outer = vec![LiteralValue::ArrayU1(LiteralArrayIdx(99))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![outer, inner],
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("payload 99 resolves nowhere");
    assert!(
        matches!(err, LiftError::UnresolvedEntity(99)),
        "got {err:?}"
    );
}

// ── Error paths ──────────────────────────────────────────────────────

#[test]
fn literal_array_table_index_out_of_range() {
    // resolve.rs:208 — the raw table index names no literal array.
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(9)),
            Bytecode::Returnundefined,
        ],
        vec![vec![LiteralValue::Integer(1)]],
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("table index 9 out of range");
    assert!(
        matches!(err, LiftError::LiteralArrayOutOfRange(9)),
        "got {err:?}"
    );
}

#[test]
fn literal_array_cycle_is_an_error() {
    // resolve.rs:211 — array 0 contains itself (decode is cycle-safe
    // since v2-P1a, so only a hand-built model reaches the lift).
    let cyclic = vec![LiteralValue::LiteralArray(LiteralArrayIdx(0))];
    let file = literal_consumer_file(
        vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(0)),
            Bytecode::Returnundefined,
        ],
        vec![cyclic],
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("self-referential literal array");
    assert!(
        matches!(err, LiftError::LiteralArrayCycle(0)),
        "got {err:?}"
    );
}

#[test]
fn resolve_sym_unregistered_entity_id() {
    // resolve.rs:30 — the (kind, id) pair is absent from the method's
    // index mapping.
    let file = literal_consumer_file(
        vec![Bytecode::LdaStr(EntityId(5)), Bytecode::Returnundefined],
        Vec::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("unregistered string id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

#[test]
fn resolve_sym_offset_without_file_string() {
    // resolve.rs:33 — the index mapping resolves to a file offset that
    // the entity map does not name.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(
        &mut strings,
        "f",
        0,
        vec![Bytecode::LdaStr(EntityId(5)), Bytecode::Returnundefined],
        HashMap::from([((EntityKind::StringId, 5), 777)]),
    );
    let file = model(
        strings,
        desc,
        vec![f],
        Vec::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("offset 777 names no string");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}

#[test]
fn resolve_method_error_chain() {
    // resolve.rs:52 (no index-mapping entry), :55 (offset is not a
    // lifted method), :58 (no file string for the method offset).
    let definefunc = || {
        vec![
            Bytecode::Definefunc(Imm(0), EntityId(5), Imm(0)),
            Bytecode::Returnundefined,
        ]
    };

    // :52 — no (MethodId, 5) entry at all.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(&mut strings, "f", 0, definefunc(), HashMap::new());
    let file = model(
        strings,
        desc,
        vec![f],
        Vec::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("unregistered method id");
    assert!(
        matches!(err, LiftError::UnresolvedEntity(5)),
        ":52 — got {err:?}"
    );

    // :55 — the offset resolves to no method (999 is nobody's offset).
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(
        &mut strings,
        "f",
        0,
        definefunc(),
        HashMap::from([((EntityKind::MethodId, 5), 999)]),
    );
    let file = model(
        strings,
        desc,
        vec![f],
        Vec::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("offset 999 is not a method");
    assert!(
        matches!(err, LiftError::UnresolvedEntity(5)),
        ":55 — got {err:?}"
    );

    // :58 — the offset IS a method (0 — this method's own hand-built
    // offset) but the entity map has no name for it.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LK;");
    let f = method(
        &mut strings,
        "f",
        0,
        definefunc(),
        HashMap::from([((EntityKind::MethodId, 5), 0)]),
    );
    let file = model(
        strings,
        desc,
        vec![f],
        Vec::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("no file string for offset 0");
    assert!(
        matches!(err, LiftError::UnresolvedEntity(5)),
        ":58 — got {err:?}"
    );
}

#[test]
fn literal_table_index_unregistered_entity_id() {
    // resolve.rs:77 — the modern (entity-offset) literal-array
    // reference has no index-mapping entry.
    let file = literal_consumer_file(
        vec![
            Bytecode::Createarraywithbuffer(Imm(0), EntityId(5)),
            Bytecode::Returnundefined,
        ],
        Vec::new(),
        HashMap::new(),
    );
    let err = lift_file(&file).expect_err("unregistered literal-array id");
    assert!(matches!(err, LiftError::UnresolvedEntity(5)), "got {err:?}");
}
