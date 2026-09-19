//! vreg-hole regressions (Phase 3, P3-T7; P2-T2 deferral).
//!
//! Bytecode reads of never-written vreg slots (`Reg(r)`, r < num_vregs,
//! no reaching definition) previously bottomed out in the Braun SSA
//! recursion as EMPTY PHIS (zero entries) in a sealed predecessor-less
//! block. That models nothing: the Ark frame has a defined initial state
//! for every slot. Vendor (arkcompiler_ets_runtime-master/ecmascript/
//! interpreter/interpreter-inl.cpp):
//!
//! - vregs start as `undefined`: `CALL_PUSH_UNDEFINED(numVregs)` pushes
//!   `JSTaggedValue::VALUE_UNDEFINED` per vreg at frame creation
//!   (:285-291 macro, :731-732 and :1471-1472 call sites; identical fill
//!   in the fast-new-frame path, interpreter_assembly.cpp:3653-3657).
//! - the accumulator starts as the hole: `state->acc =
//!   JSTaggedValue::Hole()` (:739 and :1482; fast path
//!   interpreter_assembly.cpp:3695).
//!
//! Lift must therefore resolve a no-reaching-definition read to a shared
//! frame-initial literal (undefined for vregs, hole for the accumulator)
//! instead of a zero-entry phi.

mod common;

use abcd_file::{AccessFlags, Builder, File, Type};
use abcd_ir::entity::{FuncId, Value};
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::{lower_function, to_method_body};
use abcd_ir::module::{Module, ValueDef};
use abcd_isa::{Bytecode, Reg, encode as encode_bytecodes};

use common::{HOLE, Halt, Machine, UNDEFINED};

/// Build a 12.x file whose global class carries one static method `f`
/// with the given code-header frame and raw bytecodes.
fn build_file(bytecodes: &[Bytecode], num_vregs: u32, num_args: u32) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    builder.class_add_method(
        class,
        "f",
        proto,
        AccessFlags::STATIC,
        &code,
        num_vregs,
        num_args,
    );
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// Count zero-entry phi instructions in `func` (the invalid-SSA artifact
/// of the Braun base case firing on a sealed predecessor-less block).
fn zero_entry_phis(module: &Module, func: FuncId) -> usize {
    module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).phis.iter())
        .filter(
            |&&id| matches!(&module.inst(id).data, InstData::Phi { entries } if entries.is_empty()),
        )
        .count()
}

/// Collect the values produced by instructions of the given literal kind.
fn literal_values(module: &Module, func: FuncId, pred: fn(&InstData) -> bool) -> Vec<Value> {
    let mut out = Vec::new();
    for &bb in &module.func(func).blocks {
        for &id in &module.block(bb).insts {
            let node = module.inst(id);
            if pred(&node.data) {
                out.push(node.result.expect("literal has a result"));
            }
        }
    }
    out
}

/// The value returned by the (single) `Return { value }` instruction.
fn return_operand(module: &Module, func: FuncId) -> Value {
    for &bb in &module.func(func).blocks {
        for &id in &module.block(bb).insts {
            if let InstData::Return { value: Some(v) } = &module.inst(id).data {
                return *v;
            }
        }
    }
    panic!("no Return with a value")
}

/// `lda v0 (never written); return` — the read must resolve to the shared
/// frame-initial `undefined` constant, not a zero-entry phi.
#[test]
fn never_written_vreg_read_resolves_to_frame_initial_undefined() {
    let file = build_file(&[Bytecode::Lda(Reg(0)), Bytecode::Return], 1, 0);
    let module = lift_file(&file).unwrap();
    let func = func_by_name(&module, "f");

    assert_eq!(
        zero_entry_phis(&module, func),
        0,
        "a never-written vreg read must not produce a zero-entry phi"
    );
    let undefined = literal_values(&module, func, |d| matches!(d, InstData::LiteralUndefined));
    assert_eq!(
        undefined.len(),
        1,
        "expected one shared frame-initial undefined literal"
    );
    assert_eq!(
        return_operand(&module, func),
        undefined[0],
        "the returned value must be the frame-initial undefined constant"
    );
}

/// Reads of TWO different never-written vregs share ONE undefined
/// constant (frame initialization is a single state, minimal liveness
/// perturbation).
#[test]
fn never_written_vregs_share_one_undefined_constant() {
    // lda v0; sta v1; lda v2; sta v3; lda v1; return  (v0/v2 never written)
    let file = build_file(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Lda(Reg(2)),
            Bytecode::Sta(Reg(3)),
            Bytecode::Lda(Reg(1)),
            Bytecode::Return,
        ],
        4,
        0,
    );
    let module = lift_file(&file).unwrap();
    let func = func_by_name(&module, "f");

    assert_eq!(zero_entry_phis(&module, func), 0);
    let undefined = literal_values(&module, func, |d| matches!(d, InstData::LiteralUndefined));
    assert_eq!(
        undefined.len(),
        1,
        "never-written vregs must share one frame-initial undefined constant"
    );
    // Both written slots carry the shared constant.
    let ret = return_operand(&module, func);
    assert_eq!(ret, undefined[0]);
}

/// Semantic end-to-end: `lda v0 (never written); sta v1; lda v1; return`.
/// On the VM, v0 is `undefined` at frame creation, so the function
/// returns `undefined`. Before the fix the read was a zero-entry phi
/// whose slot was never written; the simulator (missing regs read as 0)
/// returned 0 instead of the undefined sentinel.
///
/// The shape deliberately keeps the seeded constant the only acc
/// candidate and free of intervening acc loads, so the registered B4
/// acc-clobber modeling gap (an Acc-colored value must not be live
/// across another acc load) cannot mask the value flow either way the
/// allocator colors it.
#[test]
fn never_written_vreg_value_flows_to_return() {
    let file = build_file(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Lda(Reg(1)),
            Bytecode::Return,
        ],
        2,
        0,
    );
    let module = lift_file(&file).unwrap();
    let func = func_by_name(&module, "f");

    let lowered = lower_function(&module, func).unwrap();
    let body = to_method_body(&module, func, &lowered, &file).unwrap();
    let halt = Machine::new().run(&body.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(UNDEFINED),
        "never-written v0 is frame-initial undefined"
    );
}

/// A read of the never-written accumulator at entry resolves to the
/// frame-initial HOLE (vendor `state->acc = JSTaggedValue::Hole()` at
/// frame creation), not a zero-entry phi.
#[test]
fn never_written_acc_read_resolves_to_frame_initial_hole() {
    // sta v0 (reads acc before any acc def); lda v0; return
    let file = build_file(
        &[
            Bytecode::Sta(Reg(0)),
            Bytecode::Lda(Reg(0)),
            Bytecode::Return,
        ],
        1,
        0,
    );
    let module = lift_file(&file).unwrap();
    let func = func_by_name(&module, "f");

    assert_eq!(
        zero_entry_phis(&module, func),
        0,
        "a never-written acc read must not produce a zero-entry phi"
    );
    let holes = literal_values(&module, func, |d| matches!(d, InstData::LiteralHole));
    assert_eq!(
        holes.len(),
        1,
        "expected one shared frame-initial hole literal for the accumulator"
    );
    // The stored-then-returned value is the hole.
    let ret = return_operand(&module, func);
    let ValueDef::Inst(ret_inst) = module.value(ret).def else {
        panic!("return operand must be instruction-defined")
    };
    let _ = ret_inst;

    let lowered = lower_function(&module, func).unwrap();
    let body = to_method_body(&module, func, &lowered, &file).unwrap();
    let halt = Machine::new().run(&body.bytecodes);
    assert_eq!(halt, Halt::Return(HOLE), "frame-initial acc is hole");
}
