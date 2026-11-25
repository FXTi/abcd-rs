//! Register, IC-slot, and range-window overflow error tests for `regalloc`
//! and `isel` — nothing is silently truncated.
//!
//! Two drivers:
//!
//! - `regalloc::allocate` directly (the reservation and coloring checks),
//!   asserting the exact [`RegAllocError`] variant;
//! - `isel::select` directly with a hand-pinned [`RegAlloc`] (the isel-side
//!   re-checks that regalloc's own guards make pipeline-infeasible — the
//!   hand-crafted allocation bypasses them).
//!
//! The giant-arg-count shapes carry DANGLING argument value ids: the
//! overflow checks fire before any operand is resolved, so the ids are
//! never dereferenced, and coloring never sees them.

use crate::common;
use std::collections::HashMap;

use abcd_ir::{CallKind, FuncId, FunctionKind, Module, Op, ValueId};
use abcd_lower::LowerError;
use abcd_lower::fusion::Suppression;
use abcd_lower::isel;
use abcd_lower::regalloc::{self, RegAlloc, RegAllocError, RegSlot};

use common::V2Builder;

/// `ValueId`s that exist in no arena — operands the overflow checks reject
/// before resolution.
fn dangling_args(base: u32, count: usize) -> Vec<ValueId> {
    (0..count as u32).map(|i| ValueId::new(base + i)).collect()
}

/// A hand-pinned allocation with an optional call-window base.
fn pinned_alloc(
    slots: &[(ValueId, u16)],
    num_regs: u16,
    call_window_base: Option<u16>,
) -> RegAlloc {
    RegAlloc {
        allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs,
        copy_temp: None,
        call_window_base,
        low_scratch_base: None,
    }
}

// ── isel: IC slot degradation past u16 (`SetIcSlot` + `ReArrangeIc`) ────

/// Upstream `es2panda` (`templates/isa.h.erb` `SetIcSlot` + `PandaGen::ReArrangeIc`)
/// degrades 16-bit IC instructions once `counter > 0xFFFF` to `0xFF`
/// (`IC_SLOT_INVALID`) without advancing `counter`:
/// - Pass A: 257 one-slot `add2`s assign `0..=0xFE` to the first 255, degrade the
///   256th (`counter: 0xFF -> 0x100`) and 257th to `0xFF`, leaving `counter = 0x100`.
/// - Pass B: 32,639 two-slot `ldobjbyname`s fill `0x100..=0xFFFC` (`counter -> 0xFFFE`),
///   one 1-slot `ldglobalvar` takes `0xFFFE` (`counter -> 0xFFFF`), the next two-slot
///   `ldobjbyname` takes `0xFFFF` (`counter -> 0x10001`), and the final `ldobjbyname`
///   (`counter > 0xFFFF`) degrades to `0xFF` while keeping `ic_size == 0x1_0001`.
#[test]
fn ic_slot_consumption_beyond_u16_degrades_to_0xff_after_rearrangement() {
    const ONE_SLOT_IC: usize = 257; // eight_bit_ic overflow trigger
    const TWO_SLOT_PREFIX: usize = 32_639; // 0x100..=0xFFFC -> counter = 0xFFFE

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        for _ in 0..ONE_SLOT_IC {
            b.emit_val(Op::BinaryOp {
                op: abcd_ir::BinOp::Add,
                left: p,
                right: p,
            });
        }
        let name = b.sym("x");
        for _ in 0..TWO_SLOT_PREFIX {
            b.emit_val(Op::LoadProp { object: p, name });
        }
        b.emit_val(Op::TryGetGlobal {
            name,
            default: None,
        });
        b.emit_val(Op::LoadProp { object: p, name }); // slot 0xFFFF -> counter 0x10001
        b.emit_val(Op::LoadProp { object: p, name }); // degraded to 0xFF, counter stays 0x10001
        b.emit_void(Op::Return { value: None });
    }

    let param = module.functions[func.index()].params[0];
    let alloc = pinned_alloc(&[(param, 0)], 1, None);
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let res = isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect("16-bit IC consumption past 0xFFFF must degrade to 0xFF, not error");
    assert_eq!(res.ic_size, 0x1_0001);

    let prop_slots: Vec<i64> = res.block_codes[0]
        .1
        .iter()
        .filter_map(|bc| match *bc {
            abcd_isa::Bytecode::Ldobjbyname(abcd_isa::Imm(s), _) => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(prop_slots.len(), TWO_SLOT_PREFIX + 2);
    assert_eq!(prop_slots[0], 0x100);
    assert_eq!(prop_slots[TWO_SLOT_PREFIX - 1], 0xFFFC);
    assert_eq!(prop_slots[TWO_SLOT_PREFIX], 0xFFFF);
    assert_eq!(prop_slots[TWO_SLOT_PREFIX + 1], 0xFF);
}

// ── isel: register overflow in the copy-in prologue (isel.rs:715) ───────

/// With a frame of `num_regs = u16::MAX`, the second parameter's ABI top
/// slot lies outside the register space: the copy-in `mov` cannot encode
/// its source.
#[test]
fn arg_slot_beyond_u16_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        b.create_param();
        b.create_param();
        b.emit_void(Op::Return { value: None });
    }
    let params = &module.functions[func.index()].params;
    let alloc = pinned_alloc(&[(params[0], 0), (params[1], 1)], u16::MAX, None);
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let err = isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect_err("an arg slot past u16::MAX must be a hard error");
    assert!(
        matches!(err, LowerError::RegisterOverflow(f) if f == func),
        "expected RegisterOverflow, got {err:?}"
    );
}

// ── isel: range-call window checks (isel.rs:2364-2367, 2377, 2380) ──────

/// A range-form call with more than u16::MAX arguments: no vendored form
/// encodes the argc.
#[test]
fn call_argc_beyond_u16_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        b.emit_val(Op::Call {
            callee,
            this: None,
            args: dangling_args(1_000_000, u16::MAX as usize + 1),
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let param = module.functions[func.index()].params[0];
    let alloc = pinned_alloc(&[(param, 0)], 1, Some(0));
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let err = isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect_err("argc > u16::MAX must be a hard error");
    assert!(
        matches!(err, LowerError::CallArgcOverflow { func: f, argc } if f == func && argc == u16::MAX as usize + 1),
        "expected CallArgcOverflow, got {err:?}"
    );
}

/// A hand-crafted allocation whose reserved window starts above 255: every
/// vendored range form carries a u8 start register (narrow AND wide), so
/// this is a hard error rather than a truncated operand. (Regalloc's own
/// `WindowBaseOverflow` guard makes this pipeline-infeasible; the isel
/// re-check covers direct callers.)
#[test]
fn isel_window_base_beyond_u8_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        b.emit_val(Op::Call {
            callee,
            this: None,
            args: vec![callee; 4],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let param = module.functions[func.index()].params[0];
    let alloc = pinned_alloc(&[(param, 0)], 1, Some(256));
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let err = isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect_err("a window base > 255 must be a hard error");
    assert!(
        matches!(err, LowerError::CallWindowOverflow(f) if f == func),
        "expected CallWindowOverflow, got {err:?}"
    );
}

/// A window whose END runs past the register space: base 255 with 65282
/// arguments ends at 65536 > u16::MAX.
#[test]
fn window_end_beyond_u16_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        b.emit_val(Op::Call {
            callee,
            this: None,
            args: dangling_args(1_000_000, 65_282),
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let param = module.functions[func.index()].params[0];
    let alloc = pinned_alloc(&[(param, 0)], 1, Some(255));
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let err = isel::select(&module, func, &alloc, &rpo, &Suppression::default())
        .expect_err("a window end past u16::MAX must be a hard error");
    assert!(
        matches!(err, LowerError::RegisterOverflow(f) if f == func),
        "expected RegisterOverflow, got {err:?}"
    );
}

// ── regalloc: entry guards (regalloc.rs:362-370, 515, 520) ──────────────

/// Allocating a function the module does not contain yields the empty
/// allocation (a degenerate-but-harmless caller mistake).
#[test]
fn allocate_of_a_missing_function_is_an_empty_allocation() {
    let module = Module::new();
    let alloc = regalloc::allocate(&module, FuncId::new(99), &Suppression::default())
        .expect("a missing function allocates empty");
    assert!(alloc.allocation.is_empty());
    assert_eq!(alloc.num_regs, 0);
    assert!(alloc.call_window_base.is_none());
}

/// A range call whose window cannot fit the frame (window base + argc past
/// u16::MAX) fails at reservation, before any coloring work.
#[test]
fn call_window_exceeding_the_frame_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let callee = b.create_param();
        b.emit_val(Op::Call {
            callee,
            this: None,
            args: dangling_args(1_000_000, 65_534),
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let err = regalloc::allocate(&module, func, &Suppression::default())
        .expect_err("a window that cannot fit must be a hard error");
    assert!(
        matches!(err, RegAllocError::RegisterOverflow),
        "expected RegisterOverflow, got {err:?}"
    );
}

/// `R3-M7`: 252+ parameters place `low_scratch` (`0..5`) at the bottom of the
/// frame and parameter homes above them (`5..257`), succeeding cleanly; only
/// when `LOW_SCRATCH_COUNT + param_count > TEMP_REG_BASE` (`65_516` params)
/// does reservation reject with `RegAllocError::RegisterOverflow`.
#[test]
fn low_scratches_plus_params_placement_and_frame_ceiling() {
    let mut ok_module = Module::new();
    let ok_func = V2Builder::create_function(&mut ok_module, "f252", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut ok_module, ok_func);
        for _ in 0..252 {
            b.create_param();
        }
        b.emit_void(Op::Return { value: None });
    }
    let alloc = regalloc::allocate(&ok_module, ok_func, &Suppression::default())
        .expect("252 params must succeed with low_scratches placed at 0..5 (R3-M7)");
    assert_eq!(alloc.low_scratch_base, Some(0));

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        for _ in 0..65_516 {
            b.create_param();
        }
        b.emit_void(Op::Return { value: None });
    }
    let err = regalloc::allocate(&module, func, &Suppression::default())
        .expect_err("low_scratches + params past TEMP_REG_BASE must be a hard error");
    assert!(
        matches!(err, RegAllocError::RegisterOverflow),
        "expected RegisterOverflow, got {err:?}"
    );
}

// ── regalloc: coloring ceiling (regalloc.rs:1047, 620) ──────────────────

/// With the reserved window/scratch range covering 0..65520, the first
/// colorable value lands at 65520 = TEMP_REG_BASE — outside the declared
/// frame. (The window reservation itself fits: 5 + 65515 = 65520 ≤
/// u16::MAX, so this is the coloring check, not the reservation check.)
#[test]
fn coloring_past_temp_reg_base_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        b.emit_val(Op::Call {
            callee: ValueId::new(2_000_000),
            this: None,
            args: dangling_args(1_000_000, 65_515),
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let err = regalloc::allocate(&module, func, &Suppression::default())
        .expect_err("a color at TEMP_REG_BASE must be a hard error");
    assert!(
        matches!(err, RegAllocError::RegisterOverflow),
        "expected RegisterOverflow, got {err:?}"
    );
}

/// A phi copy exists (the incoming value is deliberately uncolored, so its
/// slot differs from the result's) and the frame's reserved end lands
/// exactly at TEMP_REG_BASE: the copy-temp reservation itself overflows.
///
/// The phi RESULT is hand-rewritten to parameter p0 (inconsistent input —
/// regalloc does not validate it), so no value needs coloring above the
/// parameter homes and the overflow lands on the copy-temp check, not on
/// the coloring ceiling.
#[test]
fn copy_temp_past_temp_reg_base_is_a_hard_error() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (big_call, phi);
    {
        let mut b = V2Builder::new(&mut module, func);
        let mut params = Vec::new();
        for _ in 0..5 {
            params.push(b.create_param());
        }
        // The window reservation: 65510 range args (dangling values —
        // rejected consumers never resolve them), so the reserved block is
        // 5 (params) + 5 (low scratches) + 65510 (window) = 65520 slots.
        let entry = b.entry();
        let (call_iid, _) = b.emit(Op::Call {
            callee: ValueId::new(2_000_000),
            this: None,
            args: dangling_args(1_000_000, 65_510),
            kind: CallKind::Dynamic,
        });
        big_call = call_iid;
        let join = b.create_block();
        b.add_predecessor(join, entry);
        b.emit_void(Op::Branch { dest: join });
        b.set_insert_block(join);
        // A phi whose result IS parameter p0 (hand-rewritten below): the
        // incoming value is uncolored, so a copy is recorded on the edge.
        let (phi_iid, _) = b.emit(Op::Phi {
            entries: vec![(
                abcd_ir::Edge {
                    from: entry,
                    kind: abcd_ir::EdgeKind::Normal,
                },
                ValueId::new(2_000_001),
            )],
        });
        phi = phi_iid;
        b.emit_void(Op::Return {
            value: Some(params[0]),
        });
        // Hand-rewire the phi result onto the parameter (inconsistent
        // input — the whole point is reaching the copy-temp ceiling).
        module.insts[phi.index()].result = Some(params[0]);
    }

    // The big call's result must stay out of the coloring (it would hit
    // the coloring ceiling first); suppress it like fusion would.
    let mut suppression = Suppression::default();
    suppression.insts.insert(big_call);

    let err = regalloc::allocate(&module, func, &suppression)
        .expect_err("a copy temp at TEMP_REG_BASE must be a hard error");
    assert!(
        matches!(err, RegAllocError::RegisterOverflow),
        "expected RegisterOverflow, got {err:?}"
    );
}
