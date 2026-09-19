//! N12 regression (P3-T16): `throw.ifsupernotcorrectcall` must carry its
//! check-kind imm AND the acc operand (the `this` value being checked).
//!
//! Vendor facts:
//! - `throw.ifsupernotcorrectcall imm:u16`, `acc: in:top`,
//!   `properties: [conditional_throw]`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1003-1008); formats
//!   `pref_op_imm_8` / `pref_op_imm_16` (opcode_idx 0x07 / 0x08).
//! - The imm selects the CHECK KIND and the acc carries `this` —
//!   `RuntimeStubs::RuntimeThrowIfSuperNotCorrectCall(thread, index,
//!   thisValue)` (arkcompiler_ets_runtime
//!   ecmascript/stubs/runtime_stubs-inl.h:2520-2532):
//!     * kind 0: throw ReferenceError "sub-class must call super before
//!       use 'this'" when thisValue IsUndefined || IsHole (TDZ guard
//!       before using/returning `this` in a derived constructor);
//!     * kind 1: throw ReferenceError "super() forbidden re-bind 'this'"
//!       when thisValue is neither undefined nor hole (guard against
//!       calling super() twice).
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/super-properties/
//!   baseline/reference.pa:46-57), derived constructor B:
//!
//! ```text
//! supercallspread 0x0, v5
//! sta v5
//! lda v2                          # acc = this (still hole)
//! throw.ifsupernotcorrectcall 0x1 # kind 1: re-bind guard
//! lda v5
//! sta v2                          # this = super result
//! lda v2                          # acc = this (now bound)
//! try_begin:
//! throw.ifsupernotcorrectcall 0x0 # kind 0: TDZ guard before return
//! ```
//!
//! Pre-N12 the lift fabricated `LiteralNumber(imm)` as the operand value
//! and dropped the acc input (`this` was never checked), and isel
//! hardcoded `Imm(0)` — a kind-1 re-bind guard came back as a kind-0
//! TDZ guard.

mod common;

use abcd_file::{AccessFlags, Builder, File, FileType, FunctionKind, Type, Version};
use abcd_ir::analysis::inst_operands;
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};

use common::{Halt, Machine};

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

/// The single `ThrowIfSuperNotCorrectCall` instruction's operands.
fn super_check_operands(module: &Module, func: FuncId) -> Vec<abcd_ir::entity::Value> {
    let mut out = Vec::new();
    for &bb in &module.func(func).blocks {
        for &id in &module.block(bb).insts {
            let node = module.inst(id);
            if matches!(node.data, InstData::ThrowIfSuperNotCorrectCall { .. }) {
                out.extend(inst_operands(&node.data));
            }
        }
    }
    out
}

/// (a) Synthetic lift: `lda v0; throw.ifsupernotcorrectcall 0x1;
/// return.undefined` (v0 never written → frame-initial undefined).
///
/// - The operand value must be the acc input (the value `lda v0` put in
///   acc — the frame-initial undefined literal), NOT a fabricated
///   `LiteralNumber(imm)`.
/// - The lowered instruction must carry the REAL kind (`imm = 1`), not
///   the pre-N12 hardcoded `Imm(0)`.
#[test]
fn lift_preserves_check_kind_and_acc_operand() {
    let file = build_file(
        &[
            Bytecode::Lda(Reg(0)),
            Bytecode::ThrowIfsupernotcorrectcall(Imm(1)),
            Bytecode::Returnundefined,
        ],
        1,
        0,
    );
    let module = lift_file(&file).expect("lift synthetic throw.ifsupernotcorrectcall");
    assert!(verify_module(&module).is_empty());
    let func = func_by_name(&module, "f");

    let operands = super_check_operands(&module, func);
    assert_eq!(
        operands.len(),
        1,
        "vendor `throw.ifsupernotcorrectcall imm:u16, acc: in:top` has \
         exactly one SSA input: the acc value being checked"
    );
    let value = operands[0];
    let abcd_ir::module::ValueDef::Inst(def_inst) = module.value(value).def else {
        panic!("the acc operand must be defined by an instruction")
    };
    let def = &module.inst(def_inst).data;
    assert!(
        !matches!(def, InstData::LiteralNumber(_)),
        "the operand value must be the acc input, not a fabricated \
         LiteralNumber(imm) — got {def:?}"
    );
    assert!(
        matches!(def, InstData::LiteralUndefined),
        "the checked value is what `lda v0` put in acc: the \
         frame-initial undefined literal — got {def:?}"
    );

    let result = lower_function(&module, func).expect("super check must lower");
    abcd_isa::encode(&result.bytecodes).expect("super check must encode");
    let kinds: Vec<i64> = result
        .bytecodes
        .iter()
        .filter_map(|bc| match bc {
            Bytecode::ThrowIfsupernotcorrectcall(imm) => Some(imm.0),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![1],
        "the lowered instruction must carry the source kind imm = 1 \
         (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── Synthetic simulator tests (no corpus required) ────────────────────

const THIS: i64 = 0x7b15;

/// `f(this) { throw.ifsupernotcorrectcall(kind) with acc = this; return }`
/// — the single parameter arrives in the ABI top slot Reg(num_regs).
fn build_super_check(kind: u16) -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let this = builder.create_func_param(0, IrType::default());
    builder.emit_void(InstData::ThrowIfSuperNotCorrectCall { value: this, kind });
    builder.emit_void(InstData::Return { value: None });
    (module, func)
}

/// (b) Vendor `throw.ifsupernotcorrectcall imm:u16, acc: in:top`: the
/// lowered instruction carries the REAL kind imm and the checked `this`
/// value is loaded into the acc. The simulator records both at the
/// opcode. Both corpus kinds (0 and 1) are exercised.
#[test]
fn lowered_super_check_carries_kind_and_acc_value() {
    for kind in [0u16, 1] {
        let (module, func) = build_super_check(kind);
        let result = lower_function(&module, func).expect("super check must lower");
        abcd_isa::encode(&result.bytecodes).expect("super check must encode");

        let mut machine = Machine::new().with_reg(result.num_regs, THIS);
        let halt = machine.run(&result.bytecodes);
        let Halt::ThrowIfSuperNotCorrectCall {
            kind: seen_kind,
            value,
        } = halt
        else {
            panic!(
                "expected execution to stop at throw.ifsupernotcorrectcall, \
                 got {halt:?} (bytecodes: {:?})",
                result.bytecodes
            );
        };
        assert_eq!(
            seen_kind,
            i64::from(kind),
            "the lowered imm must be the check kind {kind}, not the \
             pre-N12 hardcoded 0 (bytecodes: {:?})",
            result.bytecodes
        );
        assert_eq!(
            value, THIS,
            "the acc must hold the checked `this` value (bytecodes: {:?})",
            result.bytecodes
        );
    }
}

/// (b') Encoding boundary: the sig is `imm:u16` with BOTH pref_op_imm_8
/// and pref_op_imm_16 formats (isa.yaml:1003-1008), so a kind > 0xff
/// must still round-trip through the u16 field (the emitter's Imm range
/// check — EncodeError::OperandOutOfRange — is the hard error path for
/// anything beyond u16, which the IR's `kind: u16` makes unreachable).
#[test]
fn super_check_kind_above_u8_encodes_via_imm16_form() {
    let (module, func) = build_super_check(0x123);
    let result = lower_function(&module, func).expect("super check must lower");
    abcd_isa::encode(&result.bytecodes).expect("kind 0x123 must encode (imm16 form)");

    let mut machine = Machine::new().with_reg(result.num_regs, THIS);
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowIfSuperNotCorrectCall { kind, value } = halt else {
        panic!(
            "expected execution to stop at throw.ifsupernotcorrectcall, \
             got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(kind, 0x123, "the u16 kind must survive lowering");
    assert_eq!(value, THIS);
}

/// (c) Opt smoke: a throwing instruction is essential (DCE keeps it),
/// its acc operand is a real use (the `this` producer cannot be
/// deleted), and the kind survives optimize → verify → lower.
#[test]
fn super_check_survives_optimize_and_verify() {
    let (mut module, func) = build_super_check(1);
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let checks: Vec<u16> = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter())
        .filter_map(|&id| match &module.inst(id).data {
            InstData::ThrowIfSuperNotCorrectCall { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        checks,
        vec![1],
        "DCE must keep the throwing check with its kind intact"
    );

    let result = lower_function(&module, func).expect("optimized super check must lower");
    let mut machine = Machine::new().with_reg(result.num_regs, THIS);
    let halt = machine.run(&result.bytecodes);
    let Halt::ThrowIfSuperNotCorrectCall { kind, value } = halt else {
        panic!(
            "expected execution to stop at throw.ifsupernotcorrectcall, \
             got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(kind, 1);
    assert_eq!(value, THIS);
}
