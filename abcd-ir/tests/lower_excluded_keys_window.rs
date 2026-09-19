//! N9 regression (P4-T1): `createobjectwithexcludedkeys` must NOT assume
//! the key registers are consecutive from the first key's home (the N4
//! landmine class), and must select the wide form when the key count
//! exceeds the u8 imm of the narrow encoding.
//!
//! Vendor facts:
//! - `createobjectwithexcludedkeys imm:u8, v1:in:top, v2:in:top`,
//!   `acc: out:top`, `properties: [range_1]`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:494-498, opcode_idx 0xb3, format
//!   `op_imm_8_v1_8_v2_8`): imm = key count, v1 = source object, v2 =
//!   START of a CONSECUTIVE register range holding the imm keys.
//! - `wide.createobjectwithexcludedkeys imm:u16, v1:in:top, v2:in:top`
//!   (isa.yaml:499-504, opcode_idx 0x00 + wide prefix, format
//!   `pref_op_imm_16_v1_8_v2_8`, `properties: [range_1]`): same shape
//!   with a u16 key count; the v2 start register is still u8.
//!
//! Pre-N9 isel encoded `start = home(keys[0])` and assumed regalloc had
//! colored the keys consecutively (it never guarantees that), and never
//! selected the wide form — 256+ keys failed encode with
//! OperandOutOfRange on the u8 imm.
//!
//! Corpus coverage: only `local/object-spread` uses the opcode, always
//! with imm = 0 (zero keys) — the consecutive/wide paths have NO corpus
//! coverage, so these regressions are synthetic.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lower::isel;
use abcd_ir::lower::lower_function;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::Bytecode;
use std::collections::HashMap;

use common::{Halt, Machine};

/// `f() { createobjectwithexcludedkeys obj, [keys...]; return }` with
/// literal-number keys carrying the sentinels `key_base + i`.
fn build_excluded_keys(n_keys: usize, key_base: i64) -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let mut builder = IRBuilder::new(&mut module, func);
    let obj = builder.emit_val(InstData::LiteralNumber(0x0b1 as f64), IrType::default());
    let keys: Vec<_> = (0..n_keys)
        .map(|i| {
            builder.emit_val(
                InstData::LiteralNumber((key_base + i as i64) as f64),
                IrType::default(),
            )
        })
        .collect();
    let result = builder.emit_val(
        InstData::CreateObjectWithExcludedKeys { obj, keys },
        IrType::default(),
    );
    builder.emit_void(InstData::Return {
        value: Some(result),
    });
    (module, func)
}

/// (a) Window fill: with a hand-crafted allocation that homes the keys
/// NON-consecutively, isel must mov-fill the reserved consecutive
/// window and encode the window base as the range start — never the
/// first key's (non-consecutive) home.
#[test]
fn keys_are_mov_filled_into_the_consecutive_window() {
    let (module, func) = build_excluded_keys(3, 0xce1);
    assert!(verify_module(&module).is_empty());

    // Collect the values in emission order: obj, k1, k2, k3, result.
    let block = module.func(func).blocks[0];
    let vals: Vec<_> = module
        .block(block)
        .insts
        .iter()
        .filter_map(|&id| module.inst(id).result)
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
    let rpo = regalloc::compute_rpo(&module, func);
    let result = isel::select(&module, func, &alloc, &rpo, &HashMap::new())
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
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let mut builder = IRBuilder::new(&mut module, func);
    let callee = builder.emit_val(InstData::LiteralNumber(0xca11 as f64), IrType::default());
    let args: Vec<_> = (0..5)
        .map(|i| {
            builder.emit_val(
                InstData::LiteralNumber((0xa00 + i) as f64),
                IrType::default(),
            )
        })
        .collect();
    let _call = builder.emit_val(
        InstData::Call {
            kind: abcd_ir::inst::CallKind::Call,
            callee,
            args,
        },
        IrType::default(),
    );
    let obj = builder.emit_val(InstData::LiteralNumber(0x0b1 as f64), IrType::default());
    let keys: Vec<_> = (0..3)
        .map(|i| {
            builder.emit_val(
                InstData::LiteralNumber((0xce1 + i) as f64),
                IrType::default(),
            )
        })
        .collect();
    let result = builder.emit_val(
        InstData::CreateObjectWithExcludedKeys { obj, keys },
        IrType::default(),
    );
    builder.emit_void(InstData::Return {
        value: Some(result),
    });
    drop(builder);
    assert!(verify_module(&module).is_empty());

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
    // fill just before it: the simplest faithful replay is to re-run
    // from the top and stop at the second site — the machine has no
    // call, so step manually: re-run up to just past the call.
    let site = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Createobjectwithexcludedkeys(..)))
        .expect("lowered stream must contain createobjectwithexcludedkeys");
    let mut machine2 = Machine::new();
    // Execute everything except the call instruction itself (the
    // machine stops there): run to the call, then continue after it.
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
        assert!(verify_module(&module).is_empty());
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
            !expect_wide, lowered.bytecodes
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
