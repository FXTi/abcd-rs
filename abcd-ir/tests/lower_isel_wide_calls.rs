//! P3 regression (S2 + N4): wide range-call selection, consecutive argument
//! windows, and high-register acc routing.
//!
//! Vendor facts (abcd-isa-sys/vendor/isa/isa.yaml):
//! - `callrange imm1:u8, imm2:u8, v:in:top` (~:1082): u8 argc, u8 window
//!   start. `wide.callrange imm:u16, v:in:top` (~:1087): u16 argc, but the
//!   start register is STILL u8, and the wide form has NO IC slot operand.
//!   Same shape for callthisrange/supercallthisrange/supercallarrowrange.
//! - `sta v` / `lda v` are `op_v_8` ONLY (~:1827-1849): a value colored to a
//!   register ≥ 256 cannot be stored/loaded through the accumulator without
//!   routing through a low scratch register via `mov` (the only mnemonic
//!   with a v1_16_v2_16 format, ~:1810).
//! - N4: a range call's arguments must occupy CONSECUTIVE registers starting
//!   at the encoded start register; regalloc never guaranteed that.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::StringId;
use abcd_ir::inst::{BinOp, CallKind, InstData};
use abcd_ir::lower::isel;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::lower::{LowerError, lower_function};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, EntityId, Reg};

use common::{Halt, Machine};

/// Build `f(callee) { return callee(0, 1, ..., argc-1) }` with one literal
/// per argument.
fn build_const_arg_call(argc: usize) -> (Module, abcd_ir::entity::FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "wide", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let callee = builder.create_func_param(0, IrType::default());
    let args: Vec<_> = (0..argc)
        .map(|i| builder.emit_val(InstData::LiteralNumber(i as f64), IrType::default()))
        .collect();
    let call = builder.emit_val(
        InstData::Call {
            kind: CallKind::Call,
            callee,
            args,
        },
        IrType::default(),
    );
    builder.emit_void(InstData::Return { value: Some(call) });
    (module, func)
}

/// (a) A 300-arg call cannot encode argc in the narrow `callrange` u8 field,
/// and its argument values are colored to registers ≥ 256 that `sta`/`lda`
/// cannot encode. Today this fails at encode with OperandOutOfRange. After
/// the fix: `wide.callrange 300, v<base>` with base ≤ 255, and a per-call
/// consecutive window filled by (auto-widening) `mov` copies in call order.
#[test]
fn three_hundred_arg_call_selects_wide_callrange_with_window() {
    const ARGC: usize = 300;
    const CALLEE: i64 = 777;

    let (module, func) = build_const_arg_call(ARGC);
    let result = lower_function(&module, func).expect("300-arg call must lower");

    // The whole lowered body must be encodable (pre-fix: OperandOutOfRange
    // on the u8-only sta/lda/callrange operands).
    abcd_isa::encode(&result.bytecodes).expect("300-arg call must encode");

    // Wide form selected, with a u8-encodable window start.
    let (argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::WideCallrange(imm, Reg(start)) => Some((imm.0, *start)),
            _ => None,
        })
        .expect("wide.callrange must be emitted for argc > 255");
    assert_eq!(argc, ARGC as i64);
    assert!(
        base <= 255,
        "range-call window start must fit the u8 start operand, got {base}"
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Callrange(..))),
        "the narrow callrange cannot encode argc = {ARGC}"
    );

    // Simulate: the window Mov copies must place argument j at window
    // register base + j, in call order (N4). The single parameter (the
    // callee) arrives in the ABI top slot Reg(num_regs).
    let mut machine = Machine::new().with_reg(result.num_regs, CALLEE);
    let halt = machine.run(&result.bytecodes);
    let Halt::WideCallRange { argc, start } = halt else {
        panic!(
            "expected execution to stop at wide.callrange, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(argc, ARGC as i64);
    assert_eq!(start, base);
    for j in 0..ARGC {
        assert_eq!(
            machine.reg(start + j as u16),
            j as i64,
            "window slot v{} must hold argument {j} (bytecodes: {:?})",
            start + j as u16,
            result.bytecodes
        );
    }
}

/// (b) A value colored to Reg(300): `sta`/`lda` are op_v_8-only, so the
/// store and the reload must route through a reserved LOW scratch register
/// (`sta scratch; mov high, scratch` / `mov scratch, high; lda scratch`).
/// Today isel emits `Sta(Reg(300))` which cannot encode.
#[test]
fn high_register_store_and_reload_routes_through_low_scratch() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "hi", FunctionKind::Function, 1);

    let (s, t, r);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let _p = builder.create_func_param(0, IrType::default());
        s = builder.emit_val(InstData::LiteralNumber(40.0), IrType::default());
        t = builder.emit_val(InstData::LiteralNumber(2.0), IrType::default());
        r = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: s,
                right: t,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(r) });
    }

    // Hand-pinned allocation: s and r live in HIGH registers (≥ 256), t in a
    // low register. Low scratch block at 250..=254 (operand scratches
    // 250..=253, acc-routing scratch 254).
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (module.func(func).param_values[0], RegSlot::Reg(0)),
            (s, RegSlot::Reg(300)),
            (t, RegSlot::Reg(1)),
            (r, RegSlot::Reg(301)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 302,
        copy_temp: None,
        spill_slot: None,
        // High-register mode: the reserved low scratch block at 250..=254
        // (operand scratches 250..=253, acc-routing scratch 254), as
        // regalloc would reserve it right after the parameter homes.
        call_window_base: None,
        low_scratch_base: Some(250),
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let selected = isel::select(&module, func, &alloc, &rpo, &string_map)
        .expect("selection must succeed with a reserved low scratch");
    let codes = &selected.block_codes[0].1;

    // Pre-fix red: Sta(Reg(300)) does not encode (op_v_8 only).
    abcd_isa::encode(codes).expect("high-register sta/lda must route through a low scratch");

    // Simulator: value integrity through the scratch routing — s = 40 lands
    // in v300, is reloaded for the add, and r = 42 lands in v301.
    let mut machine = Machine::new().with_reg(302, 0); // ABI top slot for the param
    let halt = machine.run(codes);
    assert_eq!(
        halt,
        Halt::Return(42),
        "r = s + t must survive the high-register round trip (bytecodes: {codes:?})"
    );
    assert_eq!(machine.reg(300), 40, "s must be stored to its colored slot");
    assert_eq!(machine.reg(301), 42, "r must be stored to its colored slot");
}

/// (c1) Fixed-arity preservation: a 3-arg call keeps `callargs3` (no range
/// form, no window copies).
#[test]
fn three_arg_call_keeps_fixed_arity_form() {
    let (module, func) = build_const_arg_call(3);
    let result = lower_function(&module, func).expect("3-arg call must lower");
    abcd_isa::encode(&result.bytecodes).expect("3-arg call must encode");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Callargs3(..))),
        "expected callargs3, got {:?}",
        result.bytecodes
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Callrange(..) | Bytecode::WideCallrange(..))),
        "a 3-arg call must not use a range form"
    );
}

/// (c2) A 5-arg call keeps the NARROW `callrange` (argc ≤ 255), but the
/// arguments are copied into the reserved consecutive window in call order
/// — regalloc never guaranteed consecutiveness (N4). The literal for call
/// argument 0 is created LAST, so pre-fix the colored slots are not in call
/// order and the simulated window contents are wrong.
#[test]
fn five_arg_call_keeps_narrow_callrange_with_window_copies() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "narrow", FunctionKind::Function, 1);

    {
        let mut builder = IRBuilder::new(&mut module, func);
        let callee = builder.create_func_param(0, IrType::default());
        // Creation order is the REVERSE of the call order.
        let lits: Vec<_> = (0..5)
            .map(|i| builder.emit_val(InstData::LiteralNumber(100.0 + i as f64), IrType::default()))
            .collect();
        let args: Vec<_> = lits.iter().rev().copied().collect();
        let call = builder.emit_val(
            InstData::Call {
                kind: CallKind::Call,
                callee,
                args,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(call) });
    }

    let result = lower_function(&module, func).expect("5-arg call must lower");
    abcd_isa::encode(&result.bytecodes).expect("5-arg call must encode");

    let (ic, argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Callrange(ic, imm, Reg(start)) => Some((ic.0, imm.0, *start)),
            _ => None,
        })
        .expect("a 5-arg call must keep the narrow callrange");
    let _ = ic;
    assert_eq!(argc, 5);
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::WideCallrange(..))),
        "argc = 5 fits the narrow form"
    );

    let mut machine = Machine::new().with_reg(result.num_regs, 555);
    let halt = machine.run(&result.bytecodes);
    let Halt::CallRange { argc, start } = halt else {
        panic!(
            "expected execution to stop at callrange, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(argc, 5);
    assert_eq!(start, base);
    // Call order is the reverse of creation order: 104, 103, 102, 101, 100.
    for j in 0..5u16 {
        assert_eq!(
            machine.reg(start + j),
            104 - j as i64,
            "window slot v{} must hold call argument {j} in call order (bytecodes: {:?})",
            start + j,
            result.bytecodes
        );
    }
}

/// (d) The range-call window start must be ≤ 255 in EVERY vendored form
/// (narrow AND wide). A function whose parameter area alone reaches past
/// 255 cannot host the window: that is a hard error, never a silently
/// misencoded start register.
#[test]
fn window_base_beyond_u8_is_a_hard_error() {
    const PARAMS: u16 = 253;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "toomany", FunctionKind::Function, PARAMS);

    {
        let mut builder = IRBuilder::new(&mut module, func);
        let params: Vec<_> = (0..PARAMS)
            .map(|i| builder.create_func_param(i, IrType::default()))
            .collect();
        let call = builder.emit_val(
            InstData::Call {
                kind: CallKind::Call,
                callee: params[0],
                args: params[1..6].to_vec(),
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(call) });
    }

    let result = lower_function(&module, func);
    assert!(
        matches!(&result, Err(LowerError::CallWindowOverflow(f)) if *f == func),
        "a window base > 255 must be a hard CallWindowOverflow error, not a \
         truncated start register; got {result:?}"
    );
}
