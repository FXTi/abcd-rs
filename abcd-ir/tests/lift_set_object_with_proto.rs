//! N3 regression (P4-T1): `setobjectwithproto` /
//! `deprecated.setobjectwithproto` must be modeled as a dedicated
//! proto-setting instruction — NOT as a `StoreProperty` with a synthetic
//! "__proto__" name (an untraceable S3-class synthetic string, and a
//! different runtime operation: stobjbyname "__proto__" runs the
//! prototype setter machinery and needs the name in the string pool).
//!
//! Vendor facts:
//! - `setobjectwithproto imm:u16, v:in:top, acc: in:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1333-1337, opcode_idx 0x77/0xc7,
//!   formats `op_imm_8_v_8` / `op_imm_16_v_8`, properties `[ic_slot,
//!   two_slot, eight_sixteen_bit_ic]`): v is the proto, the OBJECT rides
//!   the accumulator.
//! - `deprecated.setobjectwithproto v1:in:top, v2:in:top, acc: none`
//!   (isa.yaml:1338-1342, opcode_idx 0x1a, format `pref_op_v1_8_v2_8`):
//!   v1 = proto, v2 = obj; no accumulator traffic.
//!
//! Neither form appears anywhere in the exported corpus (grep over
//! reference.pa: zero hits), so these regressions are synthetic
//! round-trips.

mod common;

use abcd_file::{AccessFlags, Builder, File, Type};
use abcd_ir::entity::FuncId;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};

use common::{Halt, Machine};

/// Sentinels for the proto and object values.
const PROTO: i64 = 0x9070;
const OBJ: i64 = 0x0b1;

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

/// Lower a synthetic one-method file and return the bytecodes.
fn lift_and_lower(bytecodes: &[Bytecode], num_vregs: u32) -> Vec<Bytecode> {
    let file = build_file(bytecodes, num_vregs, 0);
    let module = lift_file(&file).expect("lift synthetic setobjectwithproto");
    let func = func_by_name(&module, "f");
    let result = lower_function(&module, func).expect("setobjectwithproto must lower");
    abcd_isa::encode(&result.bytecodes).expect("setobjectwithproto must encode");
    result.bytecodes
}

/// (a) Deprecated form: `deprecated.setobjectwithproto v1, v2` (v1 =
/// proto, v2 = obj) must lower to the modern `setobjectwithproto`
/// (proto in the register operand, obj in the acc) — never to a
/// `stobjbyname "__proto__"` with a fabricated name.
#[test]
fn deprecated_form_lowers_to_modern_opcode() {
    let codes = lift_and_lower(
        &[
            Bytecode::Ldai(Imm(PROTO)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(OBJ)),
            Bytecode::Sta(Reg(2)),
            Bytecode::DeprecatedSetobjectwithproto(Reg(1), Reg(2)),
            Bytecode::Returnundefined,
        ],
        3,
    );

    assert!(
        !codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..))),
        "setobjectwithproto is NOT a named-property store — no \
         stobjbyname may appear (bytecodes: {codes:?})"
    );

    let mut machine = Machine::new();
    let halt = machine.run(&codes);
    let Halt::SetObjectWithProto { proto, obj } = halt else {
        panic!(
            "expected execution to stop at setobjectwithproto, got \
             {halt:?} (bytecodes: {codes:?})"
        );
    };
    assert_eq!(proto, PROTO, "the register operand must hold the proto");
    assert_eq!(obj, OBJ, "the acc must hold the object");
}

/// (b) Modern form: `setobjectwithproto imm, v` (v = proto, obj in acc)
/// must round-trip as the same opcode with the same operand roles.
#[test]
fn modern_form_round_trips_opcode_and_roles() {
    let codes = lift_and_lower(
        &[
            Bytecode::Ldai(Imm(PROTO)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldai(Imm(OBJ)),
            Bytecode::Setobjectwithproto(Imm(0), Reg(1)),
            Bytecode::Returnundefined,
        ],
        2,
    );

    assert!(
        !codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..))),
        "setobjectwithproto must not become a named-property store \
         (bytecodes: {codes:?})"
    );

    let mut machine = Machine::new();
    let halt = machine.run(&codes);
    let Halt::SetObjectWithProto { proto, obj } = halt else {
        panic!(
            "expected execution to stop at setobjectwithproto, got \
             {halt:?} (bytecodes: {codes:?})"
        );
    };
    assert_eq!(proto, PROTO);
    assert_eq!(obj, OBJ);
}
