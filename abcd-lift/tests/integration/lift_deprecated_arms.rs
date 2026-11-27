//! Coverage for the `deprecated.*` opcode arms of the v0.2 lift
//! (abcd-lift/src/translate.rs:1924-2364). es2abc never emits these
//! opcodes (zero `deprecated.*` occurrences across all 5517 corpus
//! reference.pa files, every API version/profile; isa.yaml:293 keeps
//! the group "for compatibility"), but the maintainer ruling
//! (2026-10-03) covers every arm with a synthetic L1 test that pins
//! the exact IR shape the arm produces — the operand roles are
//! vendor-derived (interpreter-inl.cpp citations per arm in
//! translate.rs), so a role mix-up breaks the pinned assertion, not
//! just coverage.
//!
//! Already covered elsewhere (not repeated here): deprecated.callspread
//! (lift_apply.rs), deprecated.asyncfunctionawaituncaught/resolve/reject
//! (lift_async_acc_value.rs), deprecated.delobjprop + tonumber
//! (lift_unit.rs), deprecated.create{array,object}withbuffer
//! (lift_alloc_array_buffer.rs), and
//! deprecated.defineclasswithbuffer (lift_deprecated_defineclasswithbuffer.rs).

use abcd_file::{AccessFlags, Builder, CodeEntity, Type, decode};
use abcd_ir::{CallKind, Const, Op, SuperKey, UnOp, ValueDef, ValueId};
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a 9.x file whose global class carries one static method `f`
/// with the given bytecodes (deprecated opcodes are an old-file decode
/// feature; the existing deprecated-arm tests all use api 9).
fn build(bytecodes: &[Bytecode], num_vregs: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    decode(&b.finalize().unwrap()).unwrap()
}

/// Build a 9.x file where instruction `insn`'s entity operand `operand`
/// is relocated to the string `s`.
fn build_with_string(
    bytecodes: &[Bytecode],
    num_vregs: u32,
    insn: usize,
    s: &str,
) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    let sh = b.add_string(s);
    b.relocate_code_id(m, offsets[insn], 0, CodeEntity::String(sh))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

/// The single function's ops, in block order.
fn ops(m: &abcd_ir::Module) -> Vec<&Op> {
    assert_eq!(m.functions.len(), 1, "one function in the built file");
    let f = &m.functions[0];
    let mut out = Vec::new();
    for &b in &f.blocks {
        for &iid in &m.blocks[b.index()].insts {
            out.push(&m.insts[iid.index()].op);
        }
    }
    out
}

/// The single op matching `pred`.
fn find_op(m: &abcd_ir::Module, pred: impl Fn(&Op) -> bool) -> &Op {
    let found: Vec<&Op> = ops(m).into_iter().filter(|op| pred(op)).collect();
    assert_eq!(found.len(), 1, "exactly one match expected: {found:?}");
    found[0]
}

/// Trace a value to its constant: either a frame-initial
/// `ValueDef::Const` or an instruction-defined `LoadConst`.
fn const_of(m: &abcd_ir::Module, v: ValueId) -> Const {
    match &m.values[v.index()].def {
        ValueDef::Const(c) => m.consts.get(*c).expect("const").clone(),
        ValueDef::Inst(iid) => match &m.insts[iid.index()].op {
            Op::LoadConst(c) => m.consts.get(*c).expect("const").clone(),
            other => panic!("expected LoadConst behind {v:?}, got {other:?}"),
        },
        other => panic!("expected a const-defined value for {v:?}, got {other:?}"),
    }
}

/// The Return's value (the final acc).
fn returned_value(m: &abcd_ir::Module) -> Option<ValueId> {
    match find_op(m, |op| matches!(op, Op::Return { .. })) {
        Op::Return { value } => *value,
        _ => unreachable!(),
    }
}

// ── deprecated.ldlexenv / deprecated.ldhomeobject (`D8`) ────────────

#[test]
fn deprecated_ldlexenv_and_ldhomeobject_do_not_miscompile_to_load_function() {
    // 1. `deprecated.ldlexenv` emits pure `LoadConst(Undefined)` rather than
    //    miscompiling the lexical environment as the executing closure (`LoadFunction`).
    let lex_file = build(&[Bytecode::DeprecatedLdlexenv, Bytecode::Return], 0);
    let lex_m = lift_file(&lex_file).expect("lift deprecated.ldlexenv");
    verify_clean(&lex_m);
    assert!(
        !ops(&lex_m).iter().any(|op| matches!(op, Op::LoadFunction)),
        "deprecated.ldlexenv must not emit LoadFunction"
    );
    let rv_lex = returned_value(&lex_m).expect("return carries acc");
    assert_eq!(const_of(&lex_m, rv_lex), Const::Undefined);

    // 2. `deprecated.ldhomeobject` loads `func["[[HomeObject]]"]` (`LoadFunction`
    //    + `LoadProp`), never returning `LoadFunction` directly as `acc`.
    let home_file = build(&[Bytecode::DeprecatedLdhomeobject, Bytecode::Return], 0);
    let mut home_m = lift_file(&home_file).expect("lift deprecated.ldhomeobject");
    verify_clean(&home_m);
    let home_sym = home_m.sym.intern("[[HomeObject]]");
    let Op::LoadProp { object, name } = find_op(&home_m, |op| matches!(op, Op::LoadProp { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*name, home_sym);
    let ValueDef::Inst(obj_iid) = home_m.values[object.index()].def else {
        panic!("LoadProp receiver must come from LoadFunction")
    };
    assert!(matches!(home_m.insts[obj_iid.index()].op, Op::LoadFunction));

    let rv_home = returned_value(&home_m).expect("return carries LoadProp result");
    let ValueDef::Inst(rv_iid) = home_m.values[rv_home.index()].def else {
        panic!("returned value must be an instruction result")
    };
    assert!(
        matches!(home_m.insts[rv_iid.index()].op, Op::LoadProp { .. }),
        "acc holds `[[HomeObject]]` LoadProp, never LoadFunction"
    );
}

// ── deprecated.poplexenv → PopLexEnv ─────────────────────────────────

#[test]
fn deprecated_poplexenv_emits_pop_lex_env() {
    let file = build(
        &[Bytecode::DeprecatedPoplexenv, Bytecode::Returnundefined],
        0,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        ops(&m).iter().any(|op| matches!(op, Op::PopLexEnv)),
        "deprecated.poplexenv → PopLexEnv: {:?}",
        ops(&m)
    );
}

// ── deprecated.getiteratornext → IteratorNext over the REGISTER ──────

#[test]
fn deprecated_getiteratornext_reads_the_register_operand() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(9)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedGetiteratornext(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::IteratorNext { iterator } = find_op(&m, |op| matches!(op, Op::IteratorNext { .. }))
    else {
        unreachable!()
    };
    assert_eq!(
        const_of(&m, *iterator),
        Const::number(7.0),
        "the iterator is the FIRST register (v0), not the step register"
    );
}

// ── deprecated.neg/not/inc/dec → UnaryOp over the REGISTER ───────────

#[test]
fn deprecated_unary_ops_read_the_register_operand() {
    // translate.rs:1965-2014: the deprecated unary family reads the
    // REGISTER (the modern forms read the acc). acc holds a different
    // constant (99) to pin the role.
    type UnaryCase = (fn(Reg) -> Bytecode, UnOp);
    let cases: [UnaryCase; 4] = [
        (Bytecode::DeprecatedNeg, UnOp::Minus),
        (Bytecode::DeprecatedNot, UnOp::BitNot),
        (Bytecode::DeprecatedInc, UnOp::Inc),
        (Bytecode::DeprecatedDec, UnOp::Dec),
    ];
    for (mk, want) in cases {
        let file = build(
            &[
                Bytecode::Ldai(Imm(5)),
                Bytecode::Sta(Reg(0)),
                Bytecode::Ldai(Imm(99)), // acc decoy — must NOT be the operand
                mk(Reg(0)),
                Bytecode::Return,
            ],
            1,
        );
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let Op::UnaryOp { op, operand } = find_op(&m, |o| matches!(o, Op::UnaryOp { .. })) else {
            unreachable!()
        };
        assert_eq!(*op, want, "deprecated unary folds to {want:?}");
        assert_eq!(
            const_of(&m, *operand),
            Const::number(5.0),
            "the operand is the register (v0=5), never the acc (99)"
        );
    }
}

// ── deprecated.callarg{0,1,s2,s3} → Call{Dynamic} with reg callee ────

#[test]
fn deprecated_callarg0_reg_callee_no_args() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(11)),
            Bytecode::Sta(Reg(2)),
            Bytecode::DeprecatedCallarg0(Reg(2)),
            Bytecode::Return,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(this, &None);
    assert!(args.is_empty());
    assert_eq!(const_of(&m, *callee), Const::number(11.0), "callee = v2");
}

#[test]
fn deprecated_callarg1_reg_callee_one_arg() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(11)),
            Bytecode::Sta(Reg(2)),
            Bytecode::Ldai(Imm(21)),
            Bytecode::Sta(Reg(3)),
            Bytecode::DeprecatedCallarg1(Reg(2), Reg(3)),
            Bytecode::Return,
        ],
        4,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(this, &None);
    assert_eq!(args.len(), 1);
    assert_eq!(const_of(&m, *callee), Const::number(11.0));
    assert_eq!(const_of(&m, args[0]), Const::number(21.0));
}

#[test]
fn deprecated_callargs2_reg_callee_two_args() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(11)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(21)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(22)),
            Bytecode::Sta(Reg(2)),
            Bytecode::DeprecatedCallargs2(Reg(0), Reg(1), Reg(2)),
            Bytecode::Return,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(this, &None);
    assert_eq!(args.len(), 2);
    assert_eq!(const_of(&m, *callee), Const::number(11.0));
    assert_eq!(const_of(&m, args[0]), Const::number(21.0));
    assert_eq!(const_of(&m, args[1]), Const::number(22.0));
}

#[test]
fn deprecated_callargs3_reg_callee_three_args() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(11)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(21)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(22)),
            Bytecode::Sta(Reg(2)),
            Bytecode::Ldai(Imm(23)),
            Bytecode::Sta(Reg(3)),
            Bytecode::DeprecatedCallargs3(Reg(0), Reg(1), Reg(2), Reg(3)),
            Bytecode::Return,
        ],
        4,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(this, &None);
    assert_eq!(args.len(), 3);
    assert_eq!(const_of(&m, *callee), Const::number(11.0));
    for (i, want) in [21.0, 22.0, 23.0].into_iter().enumerate() {
        assert_eq!(const_of(&m, args[i]), Const::number(want));
    }
}

// ── deprecated.callrange → Call{Dynamic}, window [callee, args...] (`D8`) ─

#[test]
fn deprecated_callrange_reads_callee_and_args_from_register_window() {
    // Legacy `0.0.0.2` `ecma.callirangedyn imm16, v8` (`isa.yaml` `acc: out:top`):
    // `start` (`v0`) holds `callee` and `start+1..=start+argc` (`v1, v2`) hold
    // the `argc` positional arguments (`argc + 1` total registers read).
    let file = build(
        &[
            Bytecode::Ldai(Imm(11)),
            Bytecode::Sta(Reg(0)), // callee = v0
            Bytecode::Ldai(Imm(31)),
            Bytecode::Sta(Reg(1)), // arg0 = v1
            Bytecode::Ldai(Imm(32)),
            Bytecode::Sta(Reg(2)),   // arg1 = v2
            Bytecode::Ldai(Imm(99)), // acc decoy — must NOT be read!
            Bytecode::DeprecatedCallrange(Imm(2), Reg(0)),
            Bytecode::Return,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(this, &None);
    assert_eq!(
        const_of(&m, *callee),
        Const::number(11.0),
        "deprecated.callrange's callee is start (`v0`), never acc"
    );
    assert_eq!(args.len(), 2);
    assert_eq!(const_of(&m, args[0]), Const::number(31.0));
    assert_eq!(const_of(&m, args[1]), Const::number(32.0));

    // Frame bounds check covers all `argc + 1` registers (`v2` out-of-range when `num_vregs = 2`).
    let oob_file = build(
        &[
            Bytecode::DeprecatedCallrange(Imm(2), Reg(0)),
            Bytecode::Return,
        ],
        2,
    );
    assert!(matches!(
        lift_file(&oob_file),
        Err(abcd_lift::LiftError::InvalidRegister {
            reg: 2,
            frame_limit: 2
        })
    ));
}

// ── deprecated.callthisrange → window [func, this, args...] ──────────

#[test]
fn deprecated_callthisrange_window_layout() {
    // translate.rs:2113-2141 (vendor DEPRECATED_CALLTHISRANGE): the
    // window's FIRST slot is the func, the second is `this`, and the
    // encoded imm is actualNumArgs + 1 — args come from
    // sp[start+2 .. start+imm]. Window v0=[func=10], v1=[this=20],
    // v2=30, v3=40 with imm=3 → args [30, 40].
    let file = build(
        &[
            Bytecode::Ldai(Imm(10)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(20)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(30)),
            Bytecode::Sta(Reg(2)),
            Bytecode::Ldai(Imm(40)),
            Bytecode::Sta(Reg(3)),
            Bytecode::DeprecatedCallthisrange(Imm(3), Reg(0)),
            Bytecode::Return,
        ],
        4,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Call {
        callee,
        this,
        args,
        kind,
    } = find_op(&m, |o| matches!(o, Op::Call { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*kind, CallKind::Dynamic);
    assert_eq!(
        const_of(&m, *callee),
        Const::number(10.0),
        "the func is the window's FIRST slot (interpreter-inl.cpp:1365-1371)"
    );
    let Some(this) = this else {
        panic!("callthisrange carries a receiver")
    };
    assert_eq!(
        const_of(&m, *this),
        Const::number(20.0),
        "this is the SECOND window slot"
    );
    assert_eq!(args.len(), 2, "imm = actualNumArgs + 1");
    assert_eq!(const_of(&m, args[0]), Const::number(30.0));
    assert_eq!(const_of(&m, args[1]), Const::number(40.0));
}

// ── deprecated.resumegenerator / getresumemode / gettemplateobject ───

#[test]
fn deprecated_resumegenerator_reads_the_register() {
    // translate.rs:2153-2159: the genobj is the register operand here
    // (the modern `resumegenerator` reads the acc instead).
    let file = build(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedResumegenerator(Reg(0)),
            Bytecode::Return,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::ResumeGenerator { genobj } = find_op(&m, |o| matches!(o, Op::ResumeGenerator { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *genobj), Const::number(7.0));
}

#[test]
fn deprecated_getresumemode_reads_the_register() {
    // translate.rs:2160-2166.
    let file = build(
        &[
            Bytecode::Ldai(Imm(8)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedGetresumemode(Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::GetResumeMode { genobj } = find_op(&m, |o| matches!(o, Op::GetResumeMode { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *genobj), Const::number(8.0));
}

#[test]
fn deprecated_gettemplateobject_reads_the_register() {
    // translate.rs:2167-2173: the template literal comes from the
    // register operand (the modern form reads the acc).
    let file = build(
        &[
            Bytecode::Ldai(Imm(3)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedGettemplateobject(Reg(0)),
            Bytecode::Return,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::GetTemplateObject { literal } =
        find_op(&m, |o| matches!(o, Op::GetTemplateObject { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *literal), Const::number(3.0));
}

// ── deprecated.suspendgenerator → SuspendGenerator over two regs ─────

#[test]
fn deprecated_suspendgenerator_two_register_operands() {
    // translate.rs:2180-2187: v1 = generator object, v2 = yield value.
    let file = build(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(9)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedSuspendgenerator(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::SuspendGenerator { genobj, value } =
        find_op(&m, |o| matches!(o, Op::SuspendGenerator { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *genobj), Const::number(7.0), "genobj = v1");
    assert_eq!(const_of(&m, *value), Const::number(9.0), "value = v2");
}

// ── deprecated.copydataproperties → CopyDataProps + acc := dst ───────

#[test]
fn deprecated_copydataproperties_writes_dst_back_to_acc() {
    // translate.rs:2197-2204: v1 = target, v2 = source; the target is
    // written back to acc (v0.1 parity).
    let file = build(
        &[
            Bytecode::Ldai(Imm(10)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(20)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedCopydataproperties(Reg(0), Reg(1)),
            Bytecode::Return, // returns acc — must be the TARGET (v0)
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::CopyDataProps { dst, src } = find_op(&m, |o| matches!(o, Op::CopyDataProps { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *dst), Const::number(10.0), "dst = v1");
    assert_eq!(const_of(&m, *src), Const::number(20.0), "src = v2");
    let Some(rv) = returned_value(&m) else {
        panic!("return carries a value")
    };
    assert_eq!(
        const_of(&m, rv),
        Const::number(10.0),
        "acc after deprecated.copydataproperties is the TARGET"
    );
}

// ── deprecated.setobjectwithproto → SetObjectWithProto (reg, reg) ────

#[test]
fn deprecated_setobjectwithproto_register_roles() {
    // translate.rs:2205-2211: v1 = proto, v2 = obj (isa.yaml:1338-1342).
    let file = build(
        &[
            Bytecode::Ldai(Imm(1)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(2)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedSetobjectwithproto(Reg(0), Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::SetObjectWithProto { proto, obj } =
        find_op(&m, |o| matches!(o, Op::SetObjectWithProto { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *proto), Const::number(1.0), "proto = v1");
    assert_eq!(const_of(&m, *obj), Const::number(2.0), "obj = v2");
}

// ── deprecated.ldobjbyvalue → LoadPropDyn (reg, reg) ─────────────────

#[test]
fn deprecated_ldobjbyvalue_register_roles() {
    // translate.rs:2212-2217: both operands are registers (the modern
    // form takes the key from the acc).
    let file = build(
        &[
            Bytecode::Ldai(Imm(10)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(20)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedLdobjbyvalue(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::LoadPropDyn { object, key } = find_op(&m, |o| matches!(o, Op::LoadPropDyn { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *object), Const::number(10.0), "object = v1");
    assert_eq!(const_of(&m, *key), Const::number(20.0), "key = v2");
}

// ── deprecated.ldsuperbyvalue → LoadSuper (Dynamic key, reg this) ────

#[test]
fn deprecated_ldsuperbyvalue_register_roles() {
    // translate.rs:2218-2227: v0 = thisValue, v1 = the key (N74-W4).
    let file = build(
        &[
            Bytecode::Ldai(Imm(10)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(20)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedLdsuperbyvalue(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::LoadSuper { key, this_value } = find_op(&m, |o| matches!(o, Op::LoadSuper { .. }))
    else {
        unreachable!()
    };
    let SuperKey::Dynamic(k) = key else {
        panic!("the key is dynamic (v2), got {key:?}")
    };
    assert_eq!(const_of(&m, *k), Const::number(20.0), "key = v2");
    assert_eq!(
        const_of(&m, *this_value),
        Const::number(10.0),
        "thisValue = v1"
    );
}

// ── deprecated.ldobjbyindex → LoadPropIdx (materialized index) ───────

#[test]
fn deprecated_ldobjbyindex_materializes_the_index() {
    // translate.rs:2228-2240: object = v0, index imm materialized as a
    // LoadConst.
    let file = build(
        &[
            Bytecode::Ldai(Imm(42)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedLdobjbyindex(Reg(0), Imm(7)),
            Bytecode::Return,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::LoadPropIdx { object, index } = find_op(&m, |o| matches!(o, Op::LoadPropIdx { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *object), Const::number(42.0));
    assert_eq!(
        const_of(&m, *index),
        Const::number(7.0),
        "the immediate index is a materialized constant"
    );
}

// ── deprecated.stlexvar → PutLexVar, value from the REGISTER ─────────

#[test]
fn deprecated_stlexvar_value_is_the_register() {
    // translate.rs:2261-2272: level/slot imms + the VALUE in v3 (the
    // modern form reads the acc). acc holds a decoy (99).
    let file = build(
        &[
            Bytecode::Ldai(Imm(5)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(99)),
            Bytecode::DeprecatedStlexvar(Imm(1), Imm(2), Reg(0)),
            Bytecode::Returnundefined,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::PutLexVar {
        level,
        slot,
        value,
        kind,
    } = find_op(&m, |o| matches!(o, Op::PutLexVar { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*level, 1);
    assert_eq!(*slot, 2);
    assert_eq!(*kind, abcd_ir::LexEnvKind::Plain);
    assert_eq!(
        const_of(&m, *value),
        Const::number(5.0),
        "the value is the register (v0=5), never the acc (99)"
    );
}

// ── deprecated.{getmodulenamespace,stmodulevar,ldmodulevar} ──────────
// v0.1's raw-symbol-index payload hack (translate.rs:2273-2312): the
// string entity's SYMBOL INDEX is reused as the module-slot index.

#[test]
fn deprecated_getmodulenamespace_carries_the_symbol_index() {
    let file = build_with_string(
        &[
            Bytecode::DeprecatedGetmodulenamespace(PLACEHOLDER),
            Bytecode::Return,
        ],
        0,
        0,
        "mod-ns",
    );
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let sym_idx = m.sym.intern("mod-ns").0;
    let Op::GetModuleNamespace { index } =
        find_op(&m, |o| matches!(o, Op::GetModuleNamespace { .. }))
    else {
        unreachable!()
    };
    assert_eq!(
        *index, sym_idx,
        "v0.1 parity: the raw symbol index is the payload"
    );
}

#[test]
fn deprecated_stmodulevar_carries_the_symbol_index() {
    let file = build_with_string(
        &[
            Bytecode::Ldai(Imm(44)),
            Bytecode::DeprecatedStmodulevar(PLACEHOLDER),
            Bytecode::Returnundefined,
        ],
        0,
        1,
        "mod-var",
    );
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let sym_idx = m.sym.intern("mod-var").0;
    let Op::StoreModuleVar { index, value } =
        find_op(&m, |o| matches!(o, Op::StoreModuleVar { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*index, sym_idx);
    assert_eq!(const_of(&m, *value), Const::number(44.0), "value = acc");
}

#[test]
fn deprecated_ldmodulevar_polarity_and_es_module_slot_resolution() {
    // 1. Without an `EsModule`, `flag == 0` -> `External` and `flag != 0` ->
    //    `Local` (`D8`, matching `0.0.0.2` `panda_file_translator.cpp`), falling
    //    back to the interned symbol index.
    let ext_file = build_with_string(
        &[
            Bytecode::DeprecatedLdmodulevar(PLACEHOLDER, Imm(0)),
            Bytecode::Return,
        ],
        0,
        0,
        "mod-ext",
    );
    let mut ext_m = lift_file(&ext_file).expect("lift external deprecated.ldmodulevar");
    verify_clean(&ext_m);
    let sym_idx = ext_m.sym.intern("mod-ext").0;
    let Op::LoadModuleVar { index, kind } =
        find_op(&ext_m, |o| matches!(o, Op::LoadModuleVar { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*index, sym_idx);
    assert_eq!(*kind, abcd_ir::ModuleVarKind::External);

    let loc_file = build_with_string(
        &[
            Bytecode::DeprecatedLdmodulevar(PLACEHOLDER, Imm(1)),
            Bytecode::Return,
        ],
        0,
        0,
        "mod-loc",
    );
    let loc_m = lift_file(&loc_file).expect("lift local deprecated.ldmodulevar");
    verify_clean(&loc_m);
    let Op::LoadModuleVar { kind: loc_kind, .. } =
        find_op(&loc_m, |o| matches!(o, Op::LoadModuleVar { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*loc_kind, abcd_ir::ModuleVarKind::Local);

    // 2. With an enclosing `ClassData::es_module`, string operands on
    //    `DeprecatedLdmodulevar`, `DeprecatedStmodulevar`, and
    //    `DeprecatedGetmodulenamespace` resolve to dense 0-based `u32` slots!
    let mut strings = abcd_file::StringPool::default();
    let rec_desc = strings.get_or_intern("Lentry/index;");
    let mod_field = strings.get_or_intern("moduleRecordIdx");
    let fn_name = strings.get_or_intern("func_main_0");
    let req0 = strings.get_or_intern("./a");
    let req1 = strings.get_or_intern("./b");
    let ns_local = strings.get_or_intern("nsB");
    let imp0 = strings.get_or_intern("firstImp");
    let imp1 = strings.get_or_intern("secondImp");
    let exp0 = strings.get_or_intern("firstExp");
    let exp1_local = strings.get_or_intern("secondLocal");
    let exp1_pub = strings.get_or_intern("secondPub");

    let method = abcd_file::Method {
        name: fn_name,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: abcd_file::FunctionKind::Function,
        source_lang: abcd_file::SourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(abcd_file::MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)), // External `secondImp` -> slot 1
                Bytecode::DeprecatedStmodulevar(EntityId(1)),         // Local `secondPub` -> slot 1
                Bytecode::DeprecatedLdmodulevar(EntityId(2), Imm(1)), // Local `secondLocal` -> slot 1
                Bytecode::DeprecatedGetmodulenamespace(EntityId(3)), // Namespace `nsB` -> request 1
                Bytecode::Return,
            ],
            entities: std::collections::HashMap::from([
                (
                    (abcd_isa::EntityKind::StringId, 0),
                    abcd_file::EntityRef::string(imp1),
                ),
                (
                    (abcd_isa::EntityKind::StringId, 1),
                    abcd_file::EntityRef::string(exp1_pub),
                ),
                (
                    (abcd_isa::EntityKind::StringId, 2),
                    abcd_file::EntityRef::string(exp1_local),
                ),
                (
                    (abcd_isa::EntityKind::StringId, 3),
                    abcd_file::EntityRef::string(ns_local),
                ),
            ]),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };
    let cls = abcd_file::Class {
        descriptor: rec_desc,
        name: rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: abcd_file::SourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![method],
        fields: vec![abcd_file::Field {
            name: mod_field,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(abcd_file::FieldValue::ModuleData(abcd_file::ModuleData {
                source_offset: 0,
                requests: vec![req0, req1],
                records: vec![
                    abcd_file::ModuleRecord::NamespaceImport {
                        local_name: ns_local,
                        module_request_idx: 1,
                    },
                    abcd_file::ModuleRecord::RegularImport {
                        local_name: imp0,
                        import_name: imp0,
                        module_request_idx: 0,
                    },
                    abcd_file::ModuleRecord::RegularImport {
                        local_name: imp1,
                        import_name: imp1,
                        module_request_idx: 1,
                    },
                    abcd_file::ModuleRecord::LocalExport {
                        local_name: exp0,
                        export_name: exp0,
                    },
                    abcd_file::ModuleRecord::LocalExport {
                        local_name: exp1_local,
                        export_name: exp1_pub,
                    },
                ],
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };
    let esm_file = abcd_file::File {
        version: abcd_isa::Version::new(0, 0, 0, 2),
        checksum: 0,
        size: 0,
        file_type: abcd_file::FileType::Dynamic,
        strings,
        classes: [(rec_desc, cls)].into_iter().collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };

    let esm_ir = lift_file(&esm_file).expect("lift --merge-abc legacy ESM");
    verify_clean(&esm_ir);
    let lifted = ops(&esm_ir);
    assert!(matches!(
        lifted[0],
        Op::LoadModuleVar {
            index: 1,
            kind: abcd_ir::ModuleVarKind::External
        }
    ));
    assert!(matches!(lifted[1], Op::StoreModuleVar { index: 1, .. }));
    assert!(matches!(
        lifted[2],
        Op::LoadModuleVar {
            index: 1,
            kind: abcd_ir::ModuleVarKind::Local
        }
    ));
    assert!(matches!(lifted[3], Op::GetModuleNamespace { index: 1 }));
}

// ── deprecated.ldobjbyname → LoadProp (reg object) ───────────────────

#[test]
fn deprecated_ldobjbyname_reads_the_register_object() {
    // translate.rs:2293-2297: the OBJECT is the register operand (the
    // modern ldobjbyname takes it from the acc).
    let file = build_with_string(
        &[
            Bytecode::Ldai(Imm(42)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedLdobjbyname(PLACEHOLDER, Reg(0)),
            Bytecode::Return,
        ],
        1,
        2,
        "prop",
    );
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let name = m.sym.intern("prop");
    let Op::LoadProp { object, name: n } = find_op(&m, |o| matches!(o, Op::LoadProp { .. })) else {
        unreachable!()
    };
    assert_eq!(*n, name);
    assert_eq!(const_of(&m, *object), Const::number(42.0), "object = v1");
}

// ── deprecated.ldsuperbyname → LoadSuper (Name key, reg receiver) ────

#[test]
fn deprecated_ldsuperbyname_reads_the_receiver_register() {
    // R3-M4: legacy `deprecated.ldsuperbyname string_id, v` passes the
    // super receiver in `obj_reg` (`Reg(0)`).
    let file = build_with_string(
        &[
            Bytecode::Ldai(Imm(55)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedLdsuperbyname(PLACEHOLDER, Reg(0)),
            Bytecode::Return,
        ],
        1,
        2,
        "superProp",
    );
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let name = m.sym.intern("superProp");
    let Op::LoadSuper { key, this_value } = find_op(&m, |o| matches!(o, Op::LoadSuper { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*key, SuperKey::Name(name));
    assert_eq!(const_of(&m, *this_value), Const::number(55.0));
}

// ── deprecated.stconstto/stletto/stclasstoglobalrecord ───────────────

#[test]
fn deprecated_stconsttoglobalrecord_is_const() {
    // translate.rs:2314-2328: SlowRuntimeStub::StGlobalRecord(isConst =
    // true).
    let file = build_with_string(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::DeprecatedStconsttoglobalrecord(PLACEHOLDER),
            Bytecode::Returnundefined,
        ],
        0,
        1,
        "c",
    );
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let name = m.sym.intern("c");
    let Op::StoreGlobalRecord {
        name: n,
        value,
        is_const,
    } = find_op(&m, |o| matches!(o, Op::StoreGlobalRecord { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*n, name);
    assert!(*is_const, "stconst → is_const = true");
    assert_eq!(const_of(&m, *value), Const::number(7.0), "value = acc");
}

#[test]
fn deprecated_stlet_stclass_toglobalrecord_are_mutable() {
    // translate.rs:2330-2344: isConst = false for both.
    for (mk, tag) in [
        (
            Bytecode::DeprecatedStlettoglobalrecord as fn(EntityId) -> Bytecode,
            "let",
        ),
        (
            Bytecode::DeprecatedStclasstoglobalrecord as fn(EntityId) -> Bytecode,
            "class",
        ),
    ] {
        let file = build_with_string(
            &[
                Bytecode::Ldai(Imm(8)),
                mk(PLACEHOLDER),
                Bytecode::Returnundefined,
            ],
            0,
            1,
            tag,
        );
        let mut m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let want = m.sym.intern(tag);
        let Op::StoreGlobalRecord {
            name: n,
            value,
            is_const,
        } = find_op(&m, |o| matches!(o, Op::StoreGlobalRecord { .. }))
        else {
            unreachable!()
        };
        assert_eq!(*n, want);
        assert!(!is_const, "stlet/stclass → is_const = false");
        assert_eq!(const_of(&m, *value), Const::number(8.0));
    }
}

// ── deprecated.createobjecthavingmethod → AllocObject (raw index) ────

#[test]
fn deprecated_createobjecthavingmethod_lifts_to_alloc_object() {
    // translate.rs:2346-2350: the operand is the RAW literal-table index
    // (v0.1 parity — same resolution path as the deprecated buffer
    // forms).
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[
        Bytecode::DeprecatedCreateobjecthavingmethod(Imm(0)),
        Bytecode::Return,
    ])
    .unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let la = b.add_literal_array("lit");
    let s = b.add_string("m");
    b.literal_array_add_string(la, s);
    let file = decode(&b.finalize().unwrap()).unwrap();

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let s_sym = m.sym.intern("m");
    let s_cid = m.consts.intern(Const::String(s_sym));
    let Op::AllocObject { shape } = find_op(&m, |o| matches!(o, Op::AllocObject { .. })) else {
        unreachable!()
    };
    assert_eq!(
        m.consts.get(*shape),
        Some(&Const::ArrayLiteral(vec![s_cid])),
        "the raw-index literal array is the object shape"
    );
}

// ── deprecated.dynamicimport → DynamicImport over the REGISTER ───────

#[test]
fn deprecated_dynamicimport_reads_the_register() {
    // translate.rs:2351-2355: the specifier is the register operand
    // (the modern form reads the acc).
    let file = build(
        &[
            Bytecode::Ldai(Imm(6)),
            Bytecode::Sta(Reg(0)),
            Bytecode::DeprecatedDynamicimport(Reg(0)),
            Bytecode::Return,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::DynamicImport { specifier } = find_op(&m, |o| matches!(o, Op::DynamicImport { .. }))
    else {
        unreachable!()
    };
    assert_eq!(
        const_of(&m, *specifier),
        Const::number(6.0),
        "specifier = v0"
    );
}

// ── deprecated.asyncgeneratorreject → AsyncGeneratorReject (reg, reg) ─

#[test]
fn deprecated_asyncgeneratorreject_register_roles() {
    // R3-M4: v1 = async generator object, v2 = rejection reason.
    let file = build(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(9)),
            Bytecode::Sta(Reg(1)),
            Bytecode::DeprecatedAsyncgeneratorreject(Reg(0), Reg(1)),
            Bytecode::Return,
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::AsyncGeneratorReject { genobj, value } =
        find_op(&m, |o| matches!(o, Op::AsyncGeneratorReject { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *genobj), Const::number(7.0), "genobj = v1");
    assert_eq!(const_of(&m, *value), Const::number(9.0), "reason = v2");
}
