//! Coverage for the MODERN-but-zero-corpus opcode arms of the v0.2 lift
//! (abcd-lift/src/translate.rs): all are current-table instructions
//! (isa.yaml:335,525,1378,1393,1162,530,363,388,421,1333,1727,1737,982,
//! 998,1647,1652) that es2abc simply never selects for the corpus
//! shapes (0/5517 reference.pa occurrences — see
//! /tmp/cov-diag/lift-lower.md finding 3). Maintainer ruling 2026-10-03:
//! every arm gets a synthetic L1 test pinning the exact IR shape.
//!
//! Also covers the two defensive/error arms of translate.rs:
//! `ThrowIfsupernotcorrectcall` with an out-of-{0,1} kind immediate
//! (LiftError::InvalidSuperCheckKind), `newobjrange` with argc = 0
//! (the acc fallback), and the `fallthrough_block` last-block fallback
//! (a conditional branch as the method's final instruction).

use abcd_file::{AccessFlags, Builder, CodeEntity, Type, decode};
use abcd_ir::{CallKind, CmpOp, Const, Op, UnOp, ValueDef, ValueId};
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::{LiftError, lift_file};

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a 12.x file whose global class carries one static method `f`
/// with the given bytecodes.
fn build(bytecodes: &[Bytecode], num_vregs: u32) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
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

/// The defining op of an instruction-defined value.
fn defining_op(m: &abcd_ir::Module, v: ValueId) -> &Op {
    match &m.values[v.index()].def {
        ValueDef::Inst(iid) => &m.insts[iid.index()].op,
        other => panic!("expected an instruction-defined value, got {other:?}"),
    }
}

// ── ldsymbol → TryGetGlobal{Symbol, default: undefined} ──────────────

#[test]
fn ldsymbol_loads_the_symbol_global_with_undefined_default() {
    // translate.rs:478-490 (isa.yaml:335): ldsymbol lifts to a tolerant
    // global load of the name "Symbol".
    let file = build(&[Bytecode::Ldsymbol, Bytecode::Return], 0);
    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let sym = m.sym.intern("Symbol");
    let Op::TryGetGlobal { name, default } = find_op(&m, |o| matches!(o, Op::TryGetGlobal { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*name, sym);
    let Some(d) = default else {
        panic!("ldsymbol carries an explicit undefined default")
    };
    assert_eq!(const_of(&m, *d), Const::Undefined);
}

// ── createregexpwithliteral → AllocRegExp ────────────────────────────

#[test]
fn createregexpwithliteral_lifts_to_alloc_regexp() {
    // translate.rs:552-562 (isa.yaml:525): pattern from the string
    // entity, flags from the immediate.
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Createregexpwithliteral(Imm(0), PLACEHOLDER, Imm(5)),
        Bytecode::Return,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 0, 0);
    let pat = b.add_string("a+b");
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(pat))
        .unwrap();
    let file = decode(&b.finalize().unwrap()).unwrap();

    let mut m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let pat_sym = m.sym.intern("a+b");
    let Op::AllocRegExp { pattern, flags } = find_op(&m, |o| matches!(o, Op::AllocRegExp { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*pattern, pat_sym);
    assert_eq!(*flags, 5);
}

// ── ld/stobjbyindex (+wide) → LoadPropIdx/StorePropIdx ───────────────

#[test]
fn ldobjbyindex_materializes_the_immediate_index() {
    // translate.rs:616-628: object = acc, index = the imm as a const.
    for (bc, want) in [
        (Bytecode::Ldobjbyindex(Imm(0), Imm(7)), 7.0),
        (Bytecode::WideLdobjbyindex(Imm(5000)), 5000.0),
    ] {
        let file = build(&[Bytecode::Ldai(Imm(42)), bc, Bytecode::Return], 0);
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let Op::LoadPropIdx { object, index } =
            find_op(&m, |o| matches!(o, Op::LoadPropIdx { .. }))
        else {
            unreachable!()
        };
        assert_eq!(const_of(&m, *object), Const::number(42.0), "object = acc");
        assert_eq!(const_of(&m, *index), Const::number(want));
    }
}

#[test]
fn stobjbyindex_materializes_the_immediate_index() {
    // translate.rs:629-642: value = acc, object = the register, index =
    // the imm as a const.
    let cases: [Bytecode; 2] = [
        Bytecode::Stobjbyindex(Imm(0), Reg(0), Imm(9)),
        Bytecode::WideStobjbyindex(Reg(0), Imm(6000)),
    ];
    let wants = [9.0, 6000.0];
    for (bc, want) in cases.into_iter().zip(wants) {
        let file = build(
            &[
                Bytecode::Ldai(Imm(42)), // object
                Bytecode::Sta(Reg(0)),
                Bytecode::Ldai(Imm(77)), // value (acc)
                bc,
                Bytecode::Returnundefined,
            ],
            1,
        );
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let Op::StorePropIdx {
            object,
            index,
            value,
        } = find_op(&m, |o| matches!(o, Op::StorePropIdx { .. }))
        else {
            unreachable!()
        };
        assert_eq!(const_of(&m, *object), Const::number(42.0), "object = v0");
        assert_eq!(const_of(&m, *index), Const::number(want));
        assert_eq!(const_of(&m, *value), Const::number(77.0), "value = acc");
    }
}

// ── supercallarrowrange (+wide) → Call{Super} ────────────────────────

#[test]
fn supercallarrowrange_lifts_to_super_call() {
    // translate.rs:1301-1317: callee = acc, this = None (inherited),
    // args = the register window; the arrow distinction folds into
    // CallKind::Super.
    let cases: [Bytecode; 2] = [
        Bytecode::Supercallarrowrange(Imm(0), Imm(2), Reg(1)),
        Bytecode::WideSupercallarrowrange(Imm(2), Reg(1)),
    ];
    for bc in cases {
        let file = build(
            &[
                Bytecode::Ldai(Imm(11)),
                Bytecode::Sta(Reg(1)),
                Bytecode::Ldai(Imm(22)),
                Bytecode::Sta(Reg(2)),
                Bytecode::Ldai(Imm(99)), // acc = the super constructor
                bc,
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
        assert_eq!(*kind, CallKind::Super, "arrowrange folds into Super");
        assert_eq!(this, &None, "super this is inherited");
        assert_eq!(const_of(&m, *callee), Const::number(99.0), "callee = acc");
        assert_eq!(args.len(), 2);
        assert_eq!(const_of(&m, args[0]), Const::number(11.0));
        assert_eq!(const_of(&m, args[1]), Const::number(22.0));
    }
}

// ── newobjapply → Call{New}, callee = register, args = [acc] ─────────

#[test]
fn newobjapply_normalizes_the_swapped_roles() {
    // translate.rs:1379-1397: the REGISTER is the constructor, the ACC
    // is the spread array (v0.1's swapped NewObjApply roles normalized).
    let file = build(
        &[
            Bytecode::Ldai(Imm(44)), // ctor
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(33)), // args array (acc)
            Bytecode::Newobjapply(Imm(0), Reg(0)),
            Bytecode::Return,
        ],
        1,
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
    assert_eq!(*kind, CallKind::New);
    assert_eq!(this, &None);
    assert_eq!(
        const_of(&m, *callee),
        Const::number(44.0),
        "the register operand is the constructor"
    );
    assert_eq!(args.len(), 1);
    assert_eq!(
        const_of(&m, args[0]),
        Const::number(33.0),
        "the acc is the spread array"
    );
}

// ── newobjrange argc = 0 → acc fallback ──────────────────────────────

#[test]
fn newobjrange_argc_zero_falls_back_to_acc() {
    // translate.rs:1365: vendor argc always counts the constructor
    // (>= 1); the degenerate argc = 0 keeps v0.1's acc fallback — no
    // operand invented or dropped.
    let file = build(
        &[
            Bytecode::Ldai(Imm(42)), // acc = the fallback ctor
            Bytecode::Newobjrange(Imm(0), Imm(0), Reg(0)),
            Bytecode::Return,
        ],
        1,
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
    assert_eq!(*kind, CallKind::New);
    assert_eq!(this, &None);
    assert!(args.is_empty(), "argc = 0 → no arguments");
    assert_eq!(
        const_of(&m, *callee),
        Const::number(42.0),
        "argc = 0 reads the acc as the constructor"
    );
}

// ── ldnewtarget / ldfunction ─────────────────────────────────────────

#[test]
fn ldnewtarget_lifts_to_load_new_target() {
    // translate.rs:1404-1407.
    let file = build(&[Bytecode::Ldnewtarget, Bytecode::Return], 0);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Return { value: Some(v) } = find_op(&m, |o| matches!(o, Op::Return { .. })) else {
        unreachable!()
    };
    assert!(
        matches!(defining_op(&m, *v), Op::LoadNewTarget),
        "ldnewtarget → LoadNewTarget"
    );
}

#[test]
fn ldfunction_lifts_to_load_function() {
    // translate.rs:1412-1415.
    let file = build(&[Bytecode::Ldfunction, Bytecode::Return], 0);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::Return { value: Some(v) } = find_op(&m, |o| matches!(o, Op::Return { .. })) else {
        unreachable!()
    };
    assert!(
        matches!(defining_op(&m, *v), Op::LoadFunction),
        "ldfunction → LoadFunction"
    );
}

// ── closeiterator → IteratorReturn ───────────────────────────────────

#[test]
fn closeiterator_lifts_to_iterator_return() {
    // translate.rs:1447-1453 (isa.yaml:421): `closeiterator` calls the
    // iterator's `return()`.
    let file = build(
        &[
            Bytecode::Ldai(Imm(5)),
            Bytecode::Sta(Reg(2)),
            Bytecode::Closeiterator(Imm(0), Reg(2)),
            Bytecode::Return,
        ],
        3,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::IteratorReturn { iterator } = find_op(&m, |o| matches!(o, Op::IteratorReturn { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *iterator), Const::number(5.0), "iterator = v2");
}

// ── setobjectwithproto → SetObjectWithProto (proto reg, obj acc) ─────

#[test]
fn setobjectwithproto_proto_in_register_obj_in_acc() {
    // translate.rs:1574-1581 (isa.yaml:1333-1337).
    let file = build(
        &[
            Bytecode::Ldai(Imm(2)), // proto
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(1)), // obj (acc)
            Bytecode::Setobjectwithproto(Imm(0), Reg(0)),
            Bytecode::Returnundefined,
        ],
        1,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::SetObjectWithProto { proto, obj } =
        find_op(&m, |o| matches!(o, Op::SetObjectWithProto { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *proto), Const::number(2.0), "proto = v0");
    assert_eq!(const_of(&m, *obj), Const::number(1.0), "obj = acc");
}

// ── Fused acc-branch family (jstricteqz / jeqnull / ...) ─────────────
// translate.rs:1609-1625: every fused null/undefined/strict-zero form
// folds to the SAME shape as jeqz/jnez — a UnaryOp IsFalse/IsTrue over
// the acc feeding a CondBranch (the strict/null/undefined payload is
// NOT preserved — pinned as-is; see the wave report).

/// Layout: `ldtrue; <branch> →L; ldnull; return; L: ldfalse; return`.
fn fused_acc_branch(bc: Bytecode) -> abcd_ir::Module {
    let file = build(
        &[
            Bytecode::Ldtrue,
            bc,                // idx 1, target Label(4)
            Bytecode::Ldnull,  // idx 2 (fall-through block)
            Bytecode::Return,  // idx 3
            Bytecode::Ldfalse, // idx 4 (target block)
            Bytecode::Return,  // idx 5
        ],
        0,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    m
}

#[test]
fn fused_acc_branches_fold_to_istrue_isfalse() {
    let falsy: [fn(Label) -> Bytecode; 5] = [
        |l| Bytecode::Jstricteqz(l),
        |l| Bytecode::Jeqnull(l),
        |l| Bytecode::Jstricteqnull(l),
        |l| Bytecode::Jequndefined(l),
        |l| Bytecode::Jstrictequndefined(l),
    ];
    let truthy: [fn(Label) -> Bytecode; 5] = [
        |l| Bytecode::Jnstricteqz(l),
        |l| Bytecode::Jnenull(l),
        |l| Bytecode::Jnstricteqnull(l),
        |l| Bytecode::Jneundefined(l),
        |l| Bytecode::Jnstrictequndefined(l),
    ];
    for (family, want_op) in [(falsy, UnOp::IsFalse), (truthy, UnOp::IsTrue)] {
        for mk in family {
            let bc = mk(Label(4));
            let m = fused_acc_branch(bc);
            let Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            } = find_op(&m, |o| matches!(o, Op::CondBranch { .. }))
            else {
                unreachable!()
            };
            let Op::UnaryOp { op, operand } = defining_op(&m, *cond) else {
                panic!("the branch condition is a unary truth test")
            };
            assert_eq!(*op, want_op, "{bc:?} folds to {want_op:?}");
            assert_eq!(
                const_of(&m, *operand),
                Const::Bool(true),
                "the tested value is the acc"
            );
            assert_ne!(
                true_dest, false_dest,
                "taken and fall-through targets differ"
            );
        }
    }
}

// ── Fused compare-branch family (jne / jstricteq / jnstricteq) ───────
// translate.rs:1629-1637: acc CMP reg → CondBranch.

#[test]
fn fused_compare_branches_carry_the_cmp_op() {
    type CompareBranchCase = (fn(Reg, Label) -> Bytecode, CmpOp);
    let cases: [CompareBranchCase; 3] = [
        (Bytecode::Jne, CmpOp::NotEq),
        (Bytecode::Jstricteq, CmpOp::StrictEq),
        (Bytecode::Jnstricteq, CmpOp::StrictNotEq),
    ];
    for (mk, want) in cases {
        let bc = mk(Reg(3), Label(6));
        let file = build(
            &[
                Bytecode::Ldai(Imm(2)),
                Bytecode::Sta(Reg(3)),
                Bytecode::Ldai(Imm(1)), // acc
                bc,                     // idx 3, target Label(6)
                Bytecode::Ldnull,       // idx 4 (fall-through)
                Bytecode::Return,       // idx 5
                Bytecode::Ldnull,       // idx 6 (target)
                Bytecode::Return,       // idx 7
            ],
            4,
        );
        let m = lift_file(&file).expect("lift");
        verify_clean(&m);
        let Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } = find_op(&m, |o| matches!(o, Op::CondBranch { .. }))
        else {
            unreachable!()
        };
        let Op::Compare { op, left, right } = defining_op(&m, *cond) else {
            panic!("the branch condition is a Compare")
        };
        assert_eq!(*op, want, "{bc:?} carries {want:?}");
        assert_eq!(const_of(&m, *left), Const::number(1.0), "left = acc");
        assert_eq!(const_of(&m, *right), Const::number(2.0), "right = v3");
        assert_ne!(true_dest, false_dest);
    }
}

// ── throw.deletesuperproperty → ThrowDeleteSuperProperty ─────────────

#[test]
fn throw_deletesuperproperty_lifts_to_the_dedicated_op() {
    // translate.rs:1659-1661 (isa.yaml:982).
    let file = build(&[Bytecode::ThrowDeletesuperproperty], 0);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    assert!(
        ops(&m)
            .iter()
            .any(|op| matches!(op, Op::ThrowDeleteSuperProperty)),
        "throw.deletesuperproperty → ThrowDeleteSuperProperty: {:?}",
        ops(&m)
    );
}

// ── throw.undefinedifhole (two-register) → ThrowUndefinedIfHole ──────

#[test]
fn throw_undefinedifhole_two_register_roles() {
    // translate.rs:1672-1679 (isa.yaml:998-1002): v1 carries the
    // variable name AS A RUNTIME STRING VALUE, v2 the checked value;
    // acc untouched.
    let file = build(
        &[
            Bytecode::Ldai(Imm(10)), // name value
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(20)), // checked value
            Bytecode::Sta(Reg(1)),
            Bytecode::ThrowUndefinedifhole(Reg(0), Reg(1)),
        ],
        2,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::ThrowUndefinedIfHole { name, value } =
        find_op(&m, |o| matches!(o, Op::ThrowUndefinedIfHole { .. }))
    else {
        unreachable!()
    };
    assert_eq!(const_of(&m, *name), Const::number(10.0), "name = v1");
    assert_eq!(const_of(&m, *value), Const::number(20.0), "value = v2");
}

// ── throw.ifsupernotcorrectcall with imm ∉ {0,1} → hard error ────────

#[test]
fn throw_ifsupernotcorrectcall_rejects_unknown_check_kind() {
    // translate.rs:1702: only 0 (NotCalled) and 1 (Rebind) are
    // vendor-defined check kinds.
    let file = build(&[Bytecode::ThrowIfsupernotcorrectcall(Imm(2))], 0);
    let err = lift_file(&file).expect_err("imm = 2 is not a vendor check kind");
    assert!(
        matches!(err, LiftError::InvalidSuperCheckKind(2)),
        "got {err:?}"
    );
}

// ── wide.ldpatchvar / wide.stpatchvar → GetLexVar/PutLexVar ──────────
// translate.rs:1900-1922 (isa.yaml:1647/1652): the patch opcodes are
// wide-only (hot-reload feature); they fold to the level-0 lexical
// variable forms.

#[test]
fn wide_ldpatchvar_lifts_to_get_lex_var() {
    let file = build(&[Bytecode::WideLdpatchvar(Imm(300)), Bytecode::Return], 0);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::GetLexVar { level, slot } = find_op(&m, |o| matches!(o, Op::GetLexVar { .. })) else {
        unreachable!()
    };
    assert_eq!(*level, 0, "patch vars live at level 0");
    assert_eq!(*slot, 300);
}

#[test]
fn wide_stpatchvar_lifts_to_put_lex_var() {
    let file = build(
        &[
            Bytecode::Ldai(Imm(17)),
            Bytecode::WideStpatchvar(Imm(301)),
            Bytecode::Returnundefined,
        ],
        0,
    );
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::PutLexVar { level, slot, value } = find_op(&m, |o| matches!(o, Op::PutLexVar { .. }))
    else {
        unreachable!()
    };
    assert_eq!(*level, 0);
    assert_eq!(*slot, 301);
    assert_eq!(const_of(&m, *value), Const::number(17.0), "value = acc");
}

// ── fallthrough_block last-block fallback ────────────────────────────

#[test]
fn conditional_branch_as_final_instruction_falls_back_to_last_block() {
    // translate.rs:396-400: es2abc always terminates methods with
    // return/throw, so the fall-through of a conditional branch always
    // has a block — except in hand-built bytecode where the branch is
    // the final instruction. Here the jeqz targets ITSELF (Label(1)),
    // so the taken and fall-through destinations both land on the
    // branch's own block.
    let file = build(&[Bytecode::Lda(Reg(0)), Bytecode::Jeqz(Label(1))], 1);
    let m = lift_file(&file).expect("lift");
    verify_clean(&m);
    let Op::CondBranch {
        true_dest,
        false_dest,
        ..
    } = find_op(&m, |o| matches!(o, Op::CondBranch { .. }))
    else {
        unreachable!()
    };
    let f = &m.functions[0];
    assert_eq!(f.blocks.len(), 2, "entry block + the self-loop block");
    let loop_block = f.blocks[1];
    assert_eq!(*true_dest, loop_block);
    assert_eq!(
        *false_dest, loop_block,
        "the fall-through past the final instruction maps to the last block"
    );
}
