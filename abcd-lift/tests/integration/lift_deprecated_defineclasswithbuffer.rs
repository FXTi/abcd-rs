//! `ADR-08` / `#38` (overturning `N54`): `deprecated.defineclasswithbuffer
//! method_id, imm1:u16, imm2:u16, v1:in:top, v2:in:top`
//! (`vendor/arkcompiler_runtime_core/isa/isa.yaml`, runtime ground truth in
//! `arkcompiler_ets_runtime/ecmascript/interpreter/interpreter_assembly.cpp:4624-4648`,
//! `HandleDeprecatedDefineclasswithbufferPrefId16Imm16Imm16V8V8`) reads `v1`
//! as `lexenv` and `v2` as `proto` (`heritage`), lifting cleanly into
//! [`Op::DefineClass`] across both:
//! 1. `MethodBody::entity_offsets`-mapped literal-array references (decoded
//!    legacy `0.0.0.2` files), and
//! 2. direct `File::literal_arrays` table indices (synthetic modern `9.0.0.0+`
//!    bodies).

use std::collections::HashMap;

use abcd_file::{
    AccessFlags, Builder, CodeEntity, File, FileType, FunctionKind as FileFunctionKind,
    LiteralValue, SourceLang as FileSourceLang, Type, Version, decode,
};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Const, Op, ValueDef, ValueId};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

fn const_of(m: &abcd_ir::Module, v: ValueId) -> Const {
    match &m.values[v.index()].def {
        ValueDef::Const(c) => m.consts.get(*c).expect("const").clone(),
        ValueDef::Inst(iid) => match &m.insts[iid.index()].op {
            Op::LoadConst(c) => m.consts.get(*c).expect("const").clone(),
            other => panic!("expected LoadConst behind {v:?}, got {other:?}"),
        },
        other => panic!("expected const-defined value for {v:?}, got {other:?}"),
    }
}

/// Build a 12.x file whose method `f` executes `deprecated.defineclasswithbuffer`
/// using a direct `literal_arrays` table index (`Imm(0)` — no `(LiteralarrayId, 0)`
/// entry in `entity_offsets`), distinct `v0 = lexenv (11)` and `v1 = proto (22)`
/// registers, `count = 3`, and a vendor-shaped class member buffer.
fn build_direct_index_file() -> File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (ret, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let ctor = b.class_add_method(cls, "MyCtor", proto, AccessFlags::STATIC, &ret, 0, 3);
    let member = b.class_add_method(cls, "greet", proto, AccessFlags::STATIC, &ret, 0, 3);

    let la = b.add_literal_array("members");
    let greet_s = b.add_string("greet");
    b.literal_array_add_string(la, greet_s);
    b.literal_array_add_method(la, member);
    b.literal_array_add_method_affiliate(la, 1);
    b.literal_array_add_integer(la, 1); // 1 non-static (instance) method

    let bytecodes = [
        Bytecode::Ldai(Imm(11)), // decoy lexenv -> v0
        Bytecode::Sta(Reg(0)),
        Bytecode::Ldai(Imm(22)), // proto / heritage -> v1
        Bytecode::Sta(Reg(1)),
        Bytecode::DeprecatedDefineclasswithbuffer(PLACEHOLDER, Imm(0), Imm(3), Reg(0), Reg(1)),
        Bytecode::Return,
    ];
    let (code, offsets) = encode_bytecodes(&bytecodes).unwrap();
    let f = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 2, 0);
    b.relocate_code_id(f, offsets[4], 0, CodeEntity::Method(ctor))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

#[test]
fn deprecated_defineclasswithbuffer_direct_table_index_lifts_define_class() {
    let file = build_direct_index_file();
    let mut m = lift_file(&file).expect("deprecated.defineclasswithbuffer lifts cleanly");
    verify_clean(&m);

    let ctor_fid = abcd_ir::FuncId::new(
        m.functions
            .iter()
            .position(|fn_data| m.sym.resolve(fn_data.name) == Some("MyCtor"))
            .expect("MyCtor lifted") as u32,
    );
    let member_fid = abcd_ir::FuncId::new(
        m.functions
            .iter()
            .position(|fn_data| m.sym.resolve(fn_data.name) == Some("greet"))
            .expect("greet lifted") as u32,
    );
    let greet_sym = m.sym.intern("greet");

    let (def_iid, def_res) = m
        .insts
        .iter()
        .enumerate()
        .find_map(|(idx, inst)| {
            matches!(inst.op, Op::DefineClass(_))
                .then_some((abcd_ir::InstId::new(idx as u32), inst.result.unwrap()))
        })
        .expect("DefineClass emitted");

    let Op::DefineClass(data) = &m.insts[def_iid.index()].op else {
        unreachable!()
    };
    let (ctor, heritage, members, member_attrs, count) = (
        data.ctor,
        data.heritage,
        data.members,
        &data.member_attrs,
        data.count,
    );

    assert_eq!(ctor, ctor_fid, "method_id resolves to constructor FuncId");
    assert_eq!(count, 3, "count_imm preserved as class .length");
    let base = heritage.expect("v2 proto register populates heritage");
    assert_eq!(
        const_of(&m, base),
        Const::number(22.0),
        "v2 (Reg(1)=22) is proto/heritage, never v1 (Reg(0)=11 lexenv)"
    );
    assert_eq!(
        member_attrs,
        &vec![MemberAttrs {
            is_static: false,
            kind: FunctionKind::Function,
        }],
        "direct table-index fallback extracts class_member_attrs"
    );
    let c_greet = m.consts.intern(Const::String(greet_sym));
    let c_member = m.consts.intern(Const::MethodRef(member_fid));
    let c_one = m.consts.intern(Const::number(1.0));
    assert_eq!(
        m.consts.get(members),
        Some(&Const::ArrayLiteral(vec![c_greet, c_member, c_one, c_one])),
        "members pool constant matches literal array"
    );

    // Return consumes acc written by DefineClass.
    let f = m
        .functions
        .iter()
        .find(|fn_data| m.sym.resolve(fn_data.name) == Some("f"))
        .expect("f lifted");
    let ret_val = f
        .blocks
        .iter()
        .flat_map(|bb| &m.blocks[bb.index()].insts)
        .find_map(|iid| match m.insts[iid.index()].op {
            Op::Return { value } => value,
            _ => None,
        })
        .expect("Return carries DefineClass acc result");
    assert_eq!(ret_val, def_res, "DefineClass writes result into acc");
}

#[test]
fn deprecated_defineclasswithbuffer_entity_offsets_and_lexenv_read() {
    // Legacy 0.0.0.2 decode shape: `body.entity_offsets` maps
    // `(LiteralarrayId, lit_imm)` to the literal array's file offset (`0x200` ->
    // table index 1, while table index 0 is a decoy array so falling back to
    // raw index 0 would pick the wrong buffer). Also branches before the
    // instruction with distinct `v0` (`lexenv`) definitions on each arm to
    // verify `fx.read_reg(*lexenv_reg, block)` materializes the Braun SSA Phi.
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LLegacy;");
    let ctor_name = strings.get_or_intern("LegacyCtor");
    let mem_name = strings.get_or_intern("staticFn");
    let main_name = strings.get_or_intern("main");

    let mk_empty = |name, offset| abcd_file::Method {
        name,
        offset,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(abcd_file::MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![Bytecode::Returnundefined],
            entity_offsets: HashMap::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let ctor_method = mk_empty(ctor_name, 0x100);
    let mem_method = mk_empty(mem_name, 0x140);

    // Branch diamond defining v0 (lexenv) differently on both arms (1 vs 2)
    // while v1 (proto) holds 77, then `DeprecatedDefineclasswithbuffer` at join.
    let main_method = abcd_file::Method {
        name: main_name,
        offset: 0x180,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(abcd_file::MethodBody {
            num_vregs: 2,
            num_args: 1,
            bytecodes: vec![
                Bytecode::Ldai(Imm(77)),  // 0: proto = 77 -> v1
                Bytecode::Sta(Reg(1)),    // 1
                Bytecode::Lda(Reg(2)),    // 2: cond from arg0
                Bytecode::Jeqz(Label(7)), // 3 -> else at 7
                Bytecode::Ldai(Imm(1)),   // 4: then: lexenv v0 = 1
                Bytecode::Sta(Reg(0)),    // 5
                Bytecode::Jmp(Label(9)),  // 6 -> join at 9
                Bytecode::Ldai(Imm(2)),   // 7: else: lexenv v0 = 2
                Bytecode::Sta(Reg(0)),    // 8
                Bytecode::DeprecatedDefineclasswithbuffer(
                    EntityId(9),
                    Imm(0), // raw imm 0 mapped via entity_offsets -> 0x200 -> table index 1!
                    Imm(2),
                    Reg(0),
                    Reg(1),
                ), // 9
                Bytecode::Return,         // 10
            ],
            entity_offsets: HashMap::from([
                ((EntityKind::MethodId, 9), 0x100),
                ((EntityKind::LiteralarrayId, 0), 0x200),
            ]),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let decoy_array = abcd_file::LiteralArray {
        values: vec![LiteralValue::Integer(999)],
    };
    let target_array = abcd_file::LiteralArray {
        values: vec![
            LiteralValue::String(mem_name),
            LiteralValue::Method(0x140),
            LiteralValue::MethodAffiliate(0),
            LiteralValue::Integer(0), // 0 non-static -> static method!
        ],
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
        methods: vec![ctor_method, mem_method, main_method],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let file = File {
        version: Version::new(0, 0, 0, 2),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: vec![decoy_array, target_array],
        entity_map: HashMap::from([(0x100, ctor_name), (0x140, mem_name)]),
        literal_array_offsets: HashMap::from([(0x190, 0), (0x200, 1)]),
        literal_array_header_offsets: Vec::new(),
    };

    let mut m = lift_file(&file).expect("legacy entity_offsets shape lifts cleanly");
    verify_clean(&m);

    let mem_sym = m.sym.intern("staticFn");
    let c_mem = m.consts.intern(Const::String(mem_sym));
    let c_fn = m.consts.intern(Const::MethodRef(abcd_ir::FuncId::new(1)));
    let c_zero = m.consts.intern(Const::number(0.0));
    let def_inst = m
        .insts
        .iter()
        .find(|inst| matches!(inst.op, Op::DefineClass(_)))
        .expect("DefineClass emitted");
    let Op::DefineClass(data) = &def_inst.op else {
        unreachable!()
    };
    let (ctor, heritage, members, member_attrs, count) = (
        data.ctor,
        data.heritage,
        data.members,
        &data.member_attrs,
        data.count,
    );

    assert_eq!(ctor, abcd_ir::FuncId::new(0));
    assert_eq!(count, 2);
    assert_eq!(
        const_of(&m, heritage.expect("heritage present")),
        Const::number(77.0),
        "v2 (Reg(1)=77) is bound as heritage"
    );
    assert_eq!(
        member_attrs,
        &vec![MemberAttrs {
            is_static: true,
            kind: FunctionKind::Function,
        }],
        "entity_offsets resolved literal array index 1 (static method), not decoy index 0"
    );
    assert_eq!(
        m.consts.get(members),
        Some(&Const::ArrayLiteral(vec![c_mem, c_fn, c_zero, c_zero]))
    );

    // Join block must carry the non-trivial Phi joining `[1.0, 2.0]` materialized
    // exclusively by `fx.read_reg(*lexenv_reg, block)` (`v0`).
    let has_lexenv_phi = m.blocks[def_inst.block.index()].insts.iter().any(|&iid| {
        let Op::Phi { entries } = &m.insts[iid.index()].op else {
            return false;
        };
        let vals: Vec<Const> = entries.iter().map(|(_, v)| const_of(&m, *v)).collect();
        vals.contains(&Const::number(1.0)) && vals.contains(&Const::number(2.0))
    });
    assert!(
        has_lexenv_phi,
        "reading v1 (lexenv_reg) at the join block materializes its Braun SSA Phi over [1.0, 2.0]"
    );
}
