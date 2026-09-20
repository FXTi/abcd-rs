//! N9 regression (v0.2 port of
//! `abcd-ir/tests/lower_excluded_keys_window.rs`):
//! `createobjectwithexcludedkeys` must NOT assume the key registers are
//! consecutive from the first key's home (the N4 landmine class), and
//! must select the wide form when the key count exceeds the u8 imm of
//! the narrow encoding.
//!
//! Vendor facts:
//! - `createobjectwithexcludedkeys imm:u8, v1:in:top, v2:in:top`,
//!   `acc: out:top`, `properties: [range_1]` (isa.yaml:494-498): imm =
//!   key count, v1 = source object, v2 = START of a CONSECUTIVE register
//!   range holding the imm keys.
//! - `wide.createobjectwithexcludedkeys imm:u16, v1:in:top, v2:in:top`
//!   (isa.yaml:499-504): same shape with a u16 key count; the v2 start
//!   register is still u8.
//!
//! Corpus coverage: only `local/object-spread` uses the opcode, always
//! with imm = 0 (zero keys) — the consecutive/wide paths have NO corpus
//! coverage, so these regressions are synthetic.

mod common;

use std::collections::HashMap;

use abcd_ir2::{CallKind, FunctionKind, Module, Op, verify_module};
use abcd_isa::Bytecode;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{fusion, isel, lower_function};

use common::{Halt, Machine, V2Builder};

/// `f() { createobjectwithexcludedkeys obj, [keys...]; return }` with
/// literal-number keys carrying the sentinels `key_base + i`.
fn build_excluded_keys(n_keys: usize, key_base: i64) -> (Module, abcd_ir2::FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let cobj = builder.konst(abcd_ir2::Const::number(0x0b1 as f64));
        let obj = builder.emit_val(Op::LoadConst(cobj));
        let keys: Vec<_> = (0..n_keys)
            .map(|i| {
                let cid = builder.konst(abcd_ir2::Const::number((key_base + i as i64) as f64));
                builder.emit_val(Op::LoadConst(cid))
            })
            .collect();
        let result = builder.emit_val(Op::CreateObjectWithExcludedKeys { obj, keys });
        builder.emit_void(Op::Return {
            value: Some(result),
        });
    }
    (module, func)
}

/// (a) Window fill: with a hand-crafted allocation that homes the keys
/// NON-consecutively, isel must mov-fill the reserved consecutive
/// window and encode the window base as the range start — never the
/// first key's (non-consecutive) home.
#[test]
fn keys_are_mov_filled_into_the_consecutive_window() {
    let (module, func) = build_excluded_keys(3, 0xce1);
    assert!(verify_module(&module).is_ok());

    // Collect the values in emission order: obj, k1, k2, k3, result.
    let block = module.functions[func.index()].blocks[0];
    let vals: Vec<_> = module.blocks[block.index()]
        .insts
        .iter()
        .filter_map(|&id| module.insts[id.index()].result)
        .collect();
    let (obj, keys) = (vals[0], &vals[1..4]);

    // Deliberately non-consecutive key homes; the reserved window lives
    // at 20..23 and collides with nothing (coloring normally skips it —
    // this hand allocation encodes the same reservation).
    let allocation = HashMap::from([
        (obj, RegSlot::Reg(3)),
        (keys[0], RegSlot::Reg(5)),
        (keys[1], RegSlot::Reg(9)),
        (keys[2], RegSlot::Reg(13)),
        (vals[4], RegSlot::Reg(17)),
    ]);
    let alloc = RegAlloc {
        allocation,
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 23,
        copy_temp: None,
        call_window_base: Some(20),
        low_scratch_base: None,
    };
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let rpo = regalloc::compute_rpo(&module, func);
    let result = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("selection must succeed for a consistent allocation");
    let (_, codes) = &result.block_codes[0];

    let mut machine = Machine::new();
    let halt = machine.run(codes);
    let Halt::CreateObjectWithExcludedKeys { argc, obj, start } = halt else {
        panic!(
            "expected execution to stop at createobjectwithexcludedkeys, got {halt:?} (codes: {codes:?})"
        );
    };
    assert_eq!(argc, 3);
    assert_eq!(obj, 0x0b1, "v1 must hold the source object");
    assert_eq!(
        start, 20,
        "the encoded start register must be the reserved consecutive \
         window base, not the first key's non-consecutive home (codes: \
         {codes:?})"
    );
    let window: Vec<i64> = (0..3).map(|i| machine.reg(start + i)).collect();
    assert_eq!(
        window,
        vec![0xce1, 0xce2, 0xce3],
        "the window must hold ALL keys in order (codes: {codes:?})"
    );
}

/// (b) Coexistence: a function containing BOTH a range call and a
/// createobjectwithexcludedkeys must size ONE shared window to the max
/// of the two — and both sites must encode the window base.
#[test]
fn window_is_shared_with_range_calls() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let cc = builder.konst(abcd_ir2::Const::number(0xca11 as f64));
        let callee = builder.emit_val(Op::LoadConst(cc));
        let args: Vec<_> = (0..5)
            .map(|i| {
                let cid = builder.konst(abcd_ir2::Const::number((0xa00 + i) as f64));
                builder.emit_val(Op::LoadConst(cid))
            })
            .collect();
        let _call = builder.emit_val(Op::Call {
            callee,
            this: None,
            args,
            kind: CallKind::Dynamic,
        });
        let cobj = builder.konst(abcd_ir2::Const::number(0x0b1 as f64));
        let obj = builder.emit_val(Op::LoadConst(cobj));
        let keys: Vec<_> = (0..3)
            .map(|i| {
                let cid = builder.konst(abcd_ir2::Const::number((0xce1 + i) as f64));
                builder.emit_val(Op::LoadConst(cid))
            })
            .collect();
        let result = builder.emit_val(Op::CreateObjectWithExcludedKeys { obj, keys });
        builder.emit_void(Op::Return {
            value: Some(result),
        });
    }
    assert!(verify_module(&module).is_ok());

    // Auto regalloc: the shared window must be sized max(5 call args,
    // 3 keys) = 5; lowering must succeed and both sites must work.
    let lowered = lower_function(&module, func).expect("must lower with a shared window");
    abcd_isa::encode(&lowered.bytecodes).expect("must encode");

    let mut machine = Machine::new();
    let halt = machine.run_at(&lowered.bytecodes, 0);
    // The first record-and-stop is the range call; re-enter after it to
    // reach the createobjectwithexcludedkeys.
    let Halt::CallRange { argc, start } = halt else {
        panic!(
            "expected the range call first, got {halt:?} ({:?})",
            lowered.bytecodes
        );
    };
    assert_eq!(argc, 5);
    let call_args: Vec<i64> = (0..5).map(|i| machine.reg(start + i)).collect();
    assert_eq!(call_args, vec![0xa00, 0xa01, 0xa02, 0xa03, 0xa04]);

    // Find the createobjectwithexcludedkeys pc and re-run the window
    // fill just before it: run to the call, then continue after it.
    let site = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Createobjectwithexcludedkeys(..)))
        .expect("lowered stream must contain createobjectwithexcludedkeys");
    let mut machine2 = Machine::new();
    let call_pc = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Callrange(..)))
        .expect("range call present");
    let _ = machine2.run_until(&lowered.bytecodes, 0, call_pc);
    let halt2 = machine2.run_at(&lowered.bytecodes, call_pc + 1);
    let Halt::CreateObjectWithExcludedKeys { argc, start, .. } = halt2 else {
        panic!(
            "expected createobjectwithexcludedkeys at pc {site}, got \
             {halt2:?} ({:?})",
            lowered.bytecodes
        );
    };
    assert_eq!(argc, 3);
    let window: Vec<i64> = (0..3).map(|i| machine2.reg(start + i)).collect();
    assert_eq!(window, vec![0xce1, 0xce2, 0xce3]);
}

/// (c) Width selection: 255 keys keep the narrow form; 256 keys select
/// `wide.createobjectwithexcludedkeys` (u16 imm) and must still encode.
#[test]
fn wide_form_selected_above_u8_key_count() {
    for (n, expect_wide) in [(255usize, false), (256, true)] {
        let (module, func) = build_excluded_keys(n, 0x1000);
        assert!(verify_module(&module).is_ok());
        let lowered =
            lower_function(&module, func).unwrap_or_else(|e| panic!("{n} keys must lower: {e:?}"));
        abcd_isa::encode(&lowered.bytecodes)
            .unwrap_or_else(|e| panic!("{n} keys must encode: {e:?}"));

        let narrow = lowered
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Createobjectwithexcludedkeys(..)));
        let wide = lowered
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::WideCreateobjectwithexcludedkeys(..)));
        assert_eq!(
            wide, expect_wide,
            "{n} keys: wide form expected={expect_wide} ({:?})",
            lowered.bytecodes
        );
        assert_eq!(
            narrow, !expect_wide,
            "{n} keys: narrow form expected={} ({:?})",
            !expect_wide,
            lowered.bytecodes
        );

        let mut machine = Machine::new();
        let halt = machine.run(&lowered.bytecodes);
        let (argc, start) = match halt {
            Halt::CreateObjectWithExcludedKeys { argc, start, .. } => (argc, start),
            Halt::WideCreateObjectWithExcludedKeys { argc, start, .. } => (argc, start),
            other => panic!("{n} keys: expected the createobject halt, got {other:?}"),
        };
        assert_eq!(argc, n as i64);
        let last = machine.reg(start + n as u16 - 1);
        assert_eq!(
            last,
            0x1000 + n as i64 - 1,
            "{n} keys: the LAST window slot must hold the last key"
        );
    }
}
