//! N16 regression (P5-T2): the `CallKind::Apply` arity overload collapsed
//! three different vendor opcodes into one kind selected by args.len():
//!
//! - `apply imm:u8, v1:in:top, v2:in:top` (isa.yaml:1104): func = acc,
//!   this = v1, args array = v2 (interpreter_assembly.cpp:6973-6991).
//! - `newobjapply imm:u16, v:in:top` (isa.yaml:530): ctor = v, spread array
//!   = acc (interpreter_assembly.cpp:1912-1926) — a CONSTRUCT with swapped
//!   operand roles, not a 1-arg apply.
//! - `deprecated.callspread v1, v2, v3` (isa.yaml:1109): func = v1,
//!   this = v2, array = v3 (interpreter_assembly.cpp:4651-4670) — a call.
//!
//! Pre-N16: newobjapply lifted as Apply{1 arg}; deprecated.callspread
//! DROPPED v3 (the argument array) and surfaced as Apply{1 arg} too, so
//! isel lowered it to newobjapply — a call became a construct with the
//! `this` value as ctor and no arguments; and a 0-arg Apply silently
//! emitted callarg0. Now: distinct CallKind::NewObjApply,
//! deprecated.callspread keeps all three operands (lowered as the modern
//! `apply`, N3 deprecated→modern precedent), and a wrong-arity Apply /
//! NewObjApply is a hard LowerError.

mod common;

use abcd_file::{AccessFlags, Builder, File, Type, decode};
use abcd_ir::entity::FuncId;
use abcd_ir::inst::{CallKind, InstData};
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};

/// Sentinel values for operand-role tracking.
const FUNC: i64 = 0xF0;
const THIS: i64 = 0x71;
const ARRAY: i64 = 0xA4;
const CTOR: i64 = 0xC0;

fn build_file(bytecodes: &[Bytecode], num_vregs: u32) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(bytecodes).unwrap();
    builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    builder.deduplicate();
    decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

fn lift_and_lower(bytecodes: &[Bytecode], num_vregs: u32) -> (Module, Vec<Bytecode>) {
    let file = build_file(bytecodes, num_vregs);
    let module = lift_file(&file).expect("lift");
    let func = func_by_name(&module, "f");
    let result = lower_function(&module, func).expect("lower");
    abcd_isa::encode(&result.bytecodes).expect("encode");
    (module, result.bytecodes)
}

/// Which register holds the value loaded by `Ldai(sentinel)`: track the
/// first `Ldai(sentinel); ...; Sta(Reg(r))` flow (other traffic in between
/// is fine — we follow the register that received the sentinel).
fn reg_holding(codes: &[Bytecode], sentinel: i64) -> Option<u16> {
    let mut current: Option<i64> = None;
    for bc in codes {
        match bc {
            Bytecode::Ldai(Imm(v)) => current = Some(*v),
            Bytecode::Sta(Reg(r)) => {
                if current == Some(sentinel) {
                    return Some(*r);
                }
                current = None;
            }
            _ => {}
        }
    }
    None
}

/// newobjapply must keep its identity and operand roles: the register
/// operand holds the CTOR value; the acc holds the array.
#[test]
fn newobjapply_round_trips_as_construct() {
    let (module, codes) = lift_and_lower(
        &[
            Bytecode::Ldai(Imm(CTOR)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(ARRAY)),
            Bytecode::Newobjapply(Imm(0), Reg(0)),
            Bytecode::Returnundefined,
        ],
        1,
    );

    let func = func_by_name(&module, "f");
    let kinds: Vec<(CallKind, usize)> = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter().copied())
        .filter_map(|id| match &module.inst(id).data {
            InstData::Call { kind, args, .. } => Some((*kind, args.len())),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![(CallKind::NewObjApply, 1)],
        "newobjapply must lift to CallKind::NewObjApply with the ctor as the single argument"
    );

    let ctor_reg = reg_holding(&codes, CTOR).expect("ctor stored to a register");
    let newobj: Vec<&Bytecode> = codes
        .iter()
        .filter(|bc| matches!(bc, Bytecode::Newobjapply(..)))
        .collect();
    assert_eq!(
        newobj.len(),
        1,
        "exactly one newobjapply must be emitted (bytecodes: {codes:?})"
    );
    let Bytecode::Newobjapply(_, Reg(r)) = newobj[0] else {
        unreachable!()
    };
    assert_eq!(
        *r, ctor_reg,
        "the newobjapply register operand must hold the ctor (bytecodes: {codes:?})"
    );
    assert!(
        !codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Apply(..) | Bytecode::Callarg0(..))),
        "newobjapply must not degenerate to apply/callarg0 (bytecodes: {codes:?})"
    );
}

/// deprecated.callspread must keep all three operands and lower to the
/// modern `apply` (func in acc, this and array in the registers) — never
/// to a 1-arg construct.
#[test]
fn deprecated_callspread_keeps_all_three_operands() {
    let (module, codes) = lift_and_lower(
        &[
            Bytecode::Ldai(Imm(FUNC)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(THIS)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(ARRAY)),
            Bytecode::Sta(Reg(2)),
            Bytecode::DeprecatedCallspread(Reg(0), Reg(1), Reg(2)),
            Bytecode::Returnundefined,
        ],
        3,
    );

    let func = func_by_name(&module, "f");
    let kinds: Vec<(CallKind, usize)> = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter().copied())
        .filter_map(|id| match &module.inst(id).data {
            InstData::Call { kind, args, .. } => Some((*kind, args.len())),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![(CallKind::Apply, 2)],
        "deprecated.callspread is a 2-operand apply (this, array) — the array must not be dropped"
    );

    let this_reg = reg_holding(&codes, THIS).expect("this stored");
    let array_reg = reg_holding(&codes, ARRAY).expect("array stored");
    let applies: Vec<&Bytecode> = codes
        .iter()
        .filter(|bc| matches!(bc, Bytecode::Apply(..)))
        .collect();
    assert_eq!(
        applies.len(),
        1,
        "deprecated.callspread lowers to exactly one modern apply (bytecodes: {codes:?})"
    );
    let Bytecode::Apply(_, Reg(t), Reg(a)) = applies[0] else {
        unreachable!()
    };
    assert_eq!(
        (*t, *a),
        (this_reg, array_reg),
        "apply operands are (this, array)"
    );
    assert!(
        !codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Newobjapply(..) | Bytecode::Callarg0(..))),
        "a call must never come back as a construct/callarg0 (bytecodes: {codes:?})"
    );
}

/// The arity overload is gone: a hand-built Apply without exactly two
/// arguments is a hard error, not a silent callarg0/newobjapply.
#[test]
fn wrong_arity_apply_is_a_hard_error() {
    use abcd_file::{FileType, FunctionKind, Version};
    use abcd_ir::builder::IRBuilder;
    use abcd_ir::types::IrType;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let callee = builder.emit_val(InstData::LiteralUndefined, IrType::default());
        let result = builder.emit_val(
            InstData::Call {
                kind: CallKind::Apply,
                callee,
                args: vec![], // no (this, array) pair
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(result),
        });
    }

    let err = lower_function(&module, func).expect_err("0-arg apply must not lower");
    assert!(
        err.to_string().contains("exactly 2 arguments"),
        "unexpected error: {err}"
    );
}
