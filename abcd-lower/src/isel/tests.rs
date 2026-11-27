//! Unit tests for instruction selection (`isel`): accumulator-as-cache
//! hit/miss tracking, dead-result suppression, operand materialization order,
//! `acc` invalidation across multi-bytecode expansions, `ThrowUndefinedIfHole`
//! operand order, and narrow `u8` immediate overflow / invalid `SuperSpread`
//! error diagnostics.

use std::collections::{HashMap, HashSet};

use abcd_ir::{FuncId, ValueId};
use abcd_isa::{Bytecode, Reg};

use super::{
    AccContent, LowerError, RegAlloc, RegSlot, ensure_acc, home_result, materialize_operands,
    val_reg,
};

const F: FuncId = FuncId(0);

fn alloc_with(slots: &[(ValueId, u16)]) -> RegAlloc {
    RegAlloc {
        allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 8,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    }
}

fn used_set(values: &[ValueId]) -> HashSet<ValueId> {
    values.iter().copied().collect()
}

#[test]
fn reg_colored_operand_passes_through_without_emission() {
    let v = ValueId::new(1);
    let alloc = alloc_with(&[(v, 2)]);
    let mut codes = Vec::new();
    let r = val_reg(F, v, &alloc, &mut codes, 0).expect("reg operand must resolve");
    assert_eq!(r, Reg(2));
    assert!(codes.is_empty(), "no lda/sta expected, got {codes:?}");
}

#[test]
fn unallocated_operand_is_a_hard_error_not_silent_acc() {
    let alloc = alloc_with(&[]);
    let mut codes = Vec::new();
    let mut tracker = AccContent::Hole;
    let dangling = ValueId::new(42);
    assert!(matches!(
        val_reg(F, dangling, &alloc, &mut codes, 0),
        Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
    ));
    assert!(matches!(
        ensure_acc(&mut tracker, F, dangling, &alloc, &mut codes),
        Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
    ));
}

#[test]
fn ensure_acc_loads_the_home_on_a_miss_and_records_the_content() {
    let v = ValueId::new(1);
    let alloc = alloc_with(&[(v, 3)]);
    let mut codes = Vec::new();
    let mut tracker = AccContent::Hole;
    ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("load must succeed");
    assert!(
        matches!(codes.as_slice(), [Bytecode::Lda(Reg(3))]),
        "a tracker miss must emit Lda(home), got {codes:?}"
    );
    assert_eq!(tracker, AccContent::Holds(v));
}

#[test]
fn ensure_acc_hit_emits_no_load() {
    let v = ValueId::new(1);
    let alloc = alloc_with(&[(v, 3)]);
    let mut codes = Vec::new();
    let mut tracker = AccContent::Holds(v);
    ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("hit must succeed");
    assert!(codes.is_empty(), "a cache hit must not emit, got {codes:?}");
    // A DIFFERENT value is a miss even when the tracker holds something.
    let w = ValueId::new(2);
    let alloc = alloc_with(&[(v, 3), (w, 4)]);
    ensure_acc(&mut tracker, F, w, &alloc, &mut codes).expect("miss must succeed");
    assert!(
        matches!(codes.as_slice(), [Bytecode::Lda(Reg(4))]),
        "a different value must reload from its own home, got {codes:?}"
    );
    assert_eq!(tracker, AccContent::Holds(w));
}

#[test]
fn used_results_are_homed_and_tracked_dead_results_are_not() {
    let live = ValueId::new(1);
    let dead = ValueId::new(2);
    let alloc = alloc_with(&[(live, 5), (dead, 6)]);
    let used = used_set(&[live]);
    let mut codes = Vec::new();
    let mut tracker = AccContent::Hole;

    home_result(&mut tracker, Some(live), &used, F, &alloc, &mut codes)
        .expect("homing must succeed");
    assert!(
        matches!(codes.as_slice(), [Bytecode::Sta(Reg(5))]),
        "a used result must be homed with Sta, got {codes:?}"
    );
    assert_eq!(tracker, AccContent::Holds(live));

    codes.clear();
    home_result(&mut tracker, Some(dead), &used, F, &alloc, &mut codes)
        .expect("dead result must not error");
    assert!(codes.is_empty(), "a dead result gets no Sta, got {codes:?}");
    assert_eq!(
        tracker,
        AccContent::Unknown,
        "a dead result's acc content is untracked"
    );
}

#[test]
fn register_operands_read_homes_and_the_acc_operand_loads_last() {
    // obj in R7, key in R0: val_reg emits nothing (low homes), then
    // ensure_acc(key) emits the Lda. No spill slot, no Sta — the old
    // B3 spill-before-load dance is gone by construction.
    let obj = ValueId::new(1);
    let key = ValueId::new(2);
    let alloc = alloc_with(&[(obj, 7), (key, 0)]);
    let mut codes = Vec::new();
    let mut tracker = AccContent::Hole;
    let regs = materialize_operands(&mut tracker, F, &[obj], Some(key), &alloc, &mut codes)
        .expect("materialization must succeed");
    assert_eq!(regs, vec![Reg(7)]);
    assert!(
        matches!(codes.as_slice(), [Bytecode::Lda(Reg(0))]),
        "expected exactly the key's Lda(home), got {codes:?}"
    );
    assert_eq!(tracker, AccContent::Holds(key));
}

fn mk_fn_module() -> (abcd_ir::Module, FuncId, abcd_ir::BlockId) {
    let mut m = abcd_ir::Module::new();
    let desc = m.sym.intern("Ltest;");
    m.classes.push(abcd_ir::ClassData::new(desc, desc));
    let fname = m.sym.intern("f");
    let fid = FuncId::new(0);
    let bb = abcd_ir::BlockId::new(0);
    m.blocks.push(abcd_ir::Block::default());
    let mut f = abcd_ir::FunctionData::new(
        abcd_ir::ClassId::new(0),
        fname,
        abcd_ir::FunctionKind::Function,
    );
    f.blocks.push(bb);
    m.functions.push(f);
    (m, fid, bb)
}

fn push_inst(
    m: &mut abcd_ir::Module,
    bb: abcd_ir::BlockId,
    op: abcd_ir::Op,
    has_res: bool,
) -> Option<ValueId> {
    let iid = abcd_ir::InstId::new(m.insts.len() as u32);
    let res = has_res.then(|| {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(abcd_ir::Value {
            def: abcd_ir::ValueDef::Inst(iid),
            ty: abcd_ir::Ty::Any,
        });
        vid
    });
    m.insts.push(abcd_ir::Inst {
        op,
        result: res,
        block: bb,
        loc: None,
    });
    m.blocks[bb.index()].insts.push(iid);
    res
}

#[test]
fn empty_excluded_keys_and_unused_sendable_env_invalidate_acc_tracker() {
    let (mut m, fid, bb) = mk_fn_module();
    let c42 = m.consts.intern(abcd_ir::Const::number(42.0));
    // `obj` is in `acc` right before `CreateObjectWithExcludedKeys { obj, keys: [] }`:
    // `Createemptyobject` clobbers `acc`, so `ensure_acc(obj)` MUST emit `Lda`!
    let obj = push_inst(&mut m, bb, abcd_ir::Op::LoadConst(c42), true).unwrap();
    let copy = push_inst(
        &mut m,
        bb,
        abcd_ir::Op::CreateObjectWithExcludedKeys {
            obj,
            keys: Vec::new(),
        },
        true,
    )
    .unwrap();
    // Unused `NewLexEnv(Sendable)` must invalidate `tracker` (`Holds(copy)` -> `Unknown`)
    // so `Return { value: Some(copy) }` reloads `copy` via `Lda`!
    let _unused_env = push_inst(
        &mut m,
        bb,
        abcd_ir::Op::NewLexEnv {
            num_vars: 2,
            kind: abcd_ir::LexEnvKind::Sendable,
        },
        true,
    );
    let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: Some(copy) }, false);

    let lowered = crate::lower_function(&m, fid).expect("must lower");
    let bcs = &lowered.bytecodes;
    let create_pos = bcs
        .iter()
        .position(|bc| matches!(bc, Bytecode::Createemptyobject))
        .expect("createemptyobject");
    let copydp_pos = bcs
        .iter()
        .position(|bc| matches!(bc, Bytecode::Copydataproperties(_)))
        .expect("copydataproperties");
    assert!(
        bcs[create_pos..copydp_pos]
            .iter()
            .any(|bc| matches!(bc, Bytecode::Lda(_))),
        "Lda(obj) must be emitted between Createemptyobject and Copydataproperties: {bcs:?}"
    );
    let sendable_pos = bcs
        .iter()
        .position(|bc| matches!(bc, Bytecode::CallruntimeNewsendableenv(_)))
        .expect("newsendableenv");
    assert!(
        bcs[sendable_pos + 1..]
            .iter()
            .any(|bc| matches!(bc, Bytecode::Lda(_))),
        "unused NewLexEnv(Sendable) must invalidate acc so Return reloads copy: {bcs:?}"
    );
}

#[test]
fn throw_undefined_if_hole_orders_value_first_then_name() {
    let (mut m, fid, bb) = mk_fn_module();
    let name = ValueId::new(0);
    let value = ValueId::new(1);
    m.values.push(abcd_ir::Value {
        def: abcd_ir::ValueDef::Param(0),
        ty: abcd_ir::Ty::Any,
    });
    m.values.push(abcd_ir::Value {
        def: abcd_ir::ValueDef::Param(1),
        ty: abcd_ir::Ty::Any,
    });
    m.functions[0].params.extend([name, value]);
    let _ = push_inst(
        &mut m,
        bb,
        abcd_ir::Op::ThrowUndefinedIfHole { name, value },
        false,
    );
    let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: None }, false);

    let sup = crate::fusion::analyze(&m, &m.functions[0].blocks);
    let alloc = crate::regalloc::allocate(&m, fid, &sup).unwrap();
    let RegSlot::Reg(name_r) = alloc.allocation[&name];
    let RegSlot::Reg(val_r) = alloc.allocation[&value];
    assert_ne!(name_r, val_r);

    let lowered = crate::lower_function(&m, fid).unwrap();
    assert!(
        lowered
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::ThrowUndefinedifhole(v1, v2) if v1.0 == val_r && v2.0 == name_r)),
        "isa.yaml requires throw.undefinedifhole v1(value), v2(name): {:?}",
        lowered.bytecodes
    );
}

#[test]
fn narrow_u8_immediate_overflows_and_invalid_superspread_return_errors() {
    // 1. AllocRegExp flags > 255
    {
        let (mut m, fid, bb) = mk_fn_module();
        let pat = m.sym.intern("a");
        let _ = push_inst(
            &mut m,
            bb,
            abcd_ir::Op::AllocRegExp {
                pattern: pat,
                flags: 256,
            },
            true,
        );
        let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: None }, false);
        assert!(matches!(
            crate::lower_function(&m, fid),
            Err(LowerError::ImmediateOutOfRange {
                op: "AllocRegExp",
                field: "flags",
                value: 256,
                ..
            })
        ));
    }
    // 2. Fused DefineFunc + AllocClosure length > 255
    {
        let (mut m, fid, bb) = mk_fn_module();
        let df = push_inst(
            &mut m,
            bb,
            abcd_ir::Op::DefineFunc {
                body: fid,
                captures: Vec::new(),
                length: 300,
            },
            true,
        )
        .unwrap();
        let _ = push_inst(&mut m, bb, abcd_ir::Op::AllocClosure { func: df }, true);
        let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: None }, false);
        assert!(matches!(
            crate::lower_function(&m, fid),
            Err(LowerError::ImmediateOutOfRange {
                op: "DefineFunc",
                field: "length",
                value: 300,
                ..
            })
        ));
    }
    // 3. DefineMethod length > 255
    {
        let (mut m, fid, bb) = mk_fn_module();
        let c0 = m.consts.intern(abcd_ir::Const::Null);
        let obj = push_inst(&mut m, bb, abcd_ir::Op::LoadConst(c0), true).unwrap();
        let df = push_inst(
            &mut m,
            bb,
            abcd_ir::Op::DefineFunc {
                body: fid,
                captures: Vec::new(),
                length: 1,
            },
            true,
        )
        .unwrap();
        let clos = push_inst(&mut m, bb, abcd_ir::Op::AllocClosure { func: df }, true).unwrap();
        let mname = m.sym.intern("m");
        let _ = push_inst(
            &mut m,
            bb,
            abcd_ir::Op::DefineMethod {
                object: obj,
                name: mname,
                func: clos,
                length: 256,
            },
            false,
        );
        let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: None }, false);
        assert!(matches!(
            crate::lower_function(&m, fid),
            Err(LowerError::ImmediateOutOfRange {
                op: "DefineMethod",
                field: "length",
                value: 256,
                ..
            })
        ));
    }
    // 4. SuperSpread with invalid shape (empty args)
    {
        let (mut m, fid, bb) = mk_fn_module();
        let c0 = m.consts.intern(abcd_ir::Const::Null);
        let callee = push_inst(&mut m, bb, abcd_ir::Op::LoadConst(c0), true).unwrap();
        let _ = push_inst(
            &mut m,
            bb,
            abcd_ir::Op::Call {
                callee,
                this: None,
                args: Vec::new(),
                kind: abcd_ir::CallKind::SuperSpread,
            },
            true,
        );
        let _ = push_inst(&mut m, bb, abcd_ir::Op::Return { value: None }, false);
        assert!(matches!(
            crate::lower_function(&m, fid),
            Err(LowerError::UnsupportedInstruction { .. })
        ));
    }
}
