//! N39+N40 regression (P3-T22): lift's `not` label and peephole's
//! StrictEq bit-comparison.
//!
//! N39 — the vendored `not` opcode (`not imm:u8`, isa.yaml:731-734;
//! handler interpreter_assembly.cpp:767-790) is BITWISE `~acc`
//! (`SET_ACC(JSTaggedValue(~number))` on both the int and double fast
//! paths), NOT logical negation — and `deprecated.not`
//! (interpreter_assembly.cpp:4761-4786) is the same bitwise `~` on the
//! register operand. There is no separate logical-not opcode in this
//! ISA (JS `!x` compiles to isfalse-family bytecodes). Lift mapped
//! `Bytecode::Not` to `UnOp::LogicalNot`, so peephole folded
//! `not(ldai 5)` to `false` where the VM computes `-6`.
//!
//! N40 — peephole folded StrictEq/StrictNotEq on numbers by comparing
//! `to_bits()`: `0.0 === -0.0` folded to FALSE (JS: true — same-value
//! equality treats them equal) and identical-bits NaN folded to TRUE
//! (JS: NaN !== NaN). Fixed to plain `a == b` / `a != b`, which matches
//! JS strict equality on the number domain exactly.

use abcd_file::{AccessFlags, Builder, FileType, FunctionKind, Type, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::{BinOp, InstData, UnOp};
use abcd_ir::lift::lift_file;
use abcd_ir::module::Module;
use abcd_ir::opt::FuncPass;
use abcd_ir::opt::peephole::Peephole;
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, Imm, encode as encode_bytecodes};

/// Build a 12.x file whose static method `f` runs `ldai 5; not; return`.
fn build_not_file() -> abcd_file::File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let code_seq = [
        Bytecode::Ldai(Imm(5)),
        Bytecode::Not(Imm(0)), // imm is the IC slot
        Bytecode::Return,
    ];
    let (bytes, _offsets) = encode_bytecodes(&code_seq).unwrap();
    let method = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &[], 0, 0);
    let code = builder.create_code(&bytes, 0, 0);
    builder.method_set_code(method, code);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// N39 red pin: `not` must lift to UnOp::BitNot, and peephole must
/// then fold `not(ldai 5)` to LiteralNumber(-6.0) — never to
/// LiteralBool(false).
#[test]
fn lift_not_is_bitwise_not_logical() {
    let file = build_not_file();
    let mut module = lift_file(&file).expect("lift not file");
    let func = func_by_name(&module, "f");

    let mut saw_unop = false;
    for &bb in &module.func(func).blocks.clone() {
        for &inst_id in &module.block(bb).insts {
            if let InstData::UnaryOp { op, .. } = &module.inst(inst_id).data {
                saw_unop = true;
                assert_eq!(
                    *op,
                    UnOp::BitNot,
                    "vendored `not` is bitwise ~acc (interpreter_assembly.cpp:767-790), \
                     lift must not label it LogicalNot (N39)"
                );
            }
        }
    }
    assert!(saw_unop, "fixture must contain the lifted `not` unary op");

    Peephole.run(&mut module, func);
    let mut folded = None;
    for &bb in &module.func(func).blocks.clone() {
        for &inst_id in &module.block(bb).insts {
            match &module.inst(inst_id).data {
                InstData::LiteralNumber(n) => folded = Some(*n),
                InstData::LiteralBool(b) => {
                    panic!("not(ldai 5) folded to LiteralBool({b}) — LogicalNot misfire (N39)")
                }
                _ => {}
            }
        }
    }
    assert_eq!(
        folded,
        Some(-6.0),
        "not(ldai 5) must fold to ~5 = -6, got {folded:?}"
    );
}

/// Peephole helper: fold `lhs OP rhs` and return the binop's data.
fn peephole_fold(op: BinOp, lhs: f64, rhs: f64) -> InstData {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let binop_inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let left = builder.emit_val(InstData::LiteralNumber(lhs), IrType::default());
        let right = builder.emit_val(InstData::LiteralNumber(rhs), IrType::default());
        let (inst, result) =
            builder.emit(InstData::BinaryOp { op, left, right }, IrType::default());
        binop_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    Peephole.run(&mut module, func);
    module.inst(binop_inst).data.clone()
}

/// N40 red pins: JS strict equality on numbers — `0 === -0` is true,
/// `NaN === NaN` is false. The to_bits comparison inverted both.
#[test]
fn strict_eq_uses_js_number_equality_not_bits() {
    let data = peephole_fold(BinOp::StrictEq, 0.0, -0.0);
    assert!(
        matches!(&data, InstData::LiteralBool(true)),
        "0 === -0 must fold to true (N40), got {data:?}"
    );
    let data = peephole_fold(BinOp::StrictNotEq, 0.0, -0.0);
    assert!(
        matches!(&data, InstData::LiteralBool(false)),
        "0 !== -0 must fold to false (N40), got {data:?}"
    );
    let data = peephole_fold(BinOp::StrictEq, f64::NAN, f64::NAN);
    assert!(
        matches!(&data, InstData::LiteralBool(false)),
        "NaN === NaN must fold to false (N40), got {data:?}"
    );
    let data = peephole_fold(BinOp::StrictNotEq, f64::NAN, f64::NAN);
    assert!(
        matches!(&data, InstData::LiteralBool(true)),
        "NaN !== NaN must fold to true (N40), got {data:?}"
    );
    // Sanity: ordinary strict equality still folds.
    let data = peephole_fold(BinOp::StrictEq, 3.0, 3.0);
    assert!(
        matches!(&data, InstData::LiteralBool(true)),
        "3 === 3 must still fold to true, got {data:?}"
    );
    let data = peephole_fold(BinOp::StrictEq, 3.0, 4.0);
    assert!(
        matches!(&data, InstData::LiteralBool(false)),
        "3 === 4 must still fold to false, got {data:?}"
    );
}

/// N39 unit sanity (dispatch pin): BitNot(Lit 5) folds to -6, not
/// false — the peephole BitNot arm itself was already correct; this
/// pins the fold the corrected lift label now reaches.
#[test]
fn bitnot_literal_folds_to_bitwise_result() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let unop_inst;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let operand = builder.emit_val(InstData::LiteralNumber(5.0), IrType::default());
        let (inst, result) = builder.emit(
            InstData::UnaryOp {
                op: UnOp::BitNot,
                operand,
            },
            IrType::default(),
        );
        unop_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    Peephole.run(&mut module, func);
    assert!(
        matches!(&module.inst(unop_inst).data, InstData::LiteralNumber(n) if *n == -6.0),
        "BitNot(Lit 5) must fold to -6, got {:?}",
        module.inst(unop_inst).data
    );
}
