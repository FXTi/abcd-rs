//! N51 regression: the `this-by-*` family — `ldthisbyname` /
//! `stthisbyname` / `ldthisbyvalue` / `stthisbyvalue`
//! (abcd-isa-sys/vendor/isa/isa.yaml:1627-1642) — is IC-fused `this`
//! property access that es2panda NEVER emits (upstream source grep:
//! zero hits; the 36-compile matrix shows `this[k] = v` always
//! compiles to `ldthis` + `stobjbyvalue`). Corpus coverage is zero, so
//! there is no VM evidence for the lift — the v0.1 lifter must refuse
//! loudly (maintainer ruling 2026-09-20, N51: hard error, never a
//! warning, never silent pass-through).

use abcd_file::{AccessFlags, Builder, CodeEntity, File, Type, decode};
use abcd_ir::lift::lift_file;
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a 12.x file whose global class carries one static method `f`
/// with the given bytecodes; `wire` relocates entity operands.
fn build_file(
    bytecodes: &[Bytecode],
    num_vregs: u32,
    wire: impl FnOnce(&mut Builder, abcd_file::MethodHandle, &[u32]),
) -> File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, num_vregs, 0);
    wire(&mut b, m, &offsets);
    decode(&b.finalize().unwrap()).unwrap()
}

/// A `*byname` body: the string operand is wired to a real string.
fn build_byname(make: impl FnOnce(EntityId) -> Bytecode) -> File {
    build_file(
        &[make(PLACEHOLDER), Bytecode::Returnundefined],
        1,
        |b, m, offsets| {
            let name = b.add_string("key");
            b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(name))
                .unwrap();
        },
    )
}

/// A `*byvalue` body: key in v0, value through the accumulator.
fn build_byvalue(make: impl FnOnce() -> Bytecode) -> File {
    build_file(&[make(), Bytecode::Returnundefined], 1, |_, _, _| {})
}

#[test]
fn ldthisbyname_is_hard_error() {
    let file = build_byname(|id| Bytecode::Ldthisbyname(Imm(0), id));
    let err = lift_file(&file).expect_err("ldthisbyname must fail lift (N51)");
    assert!(
        matches!(
            err,
            abcd_ir::lift::LiftError::UnsupportedThisByAccess("ldthisbyname")
        ),
        "dedicated N51 variant naming the opcode, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("ldthisbyname"),
        "error names the opcode: {msg}"
    );
    assert!(msg.contains("N51"), "error cites the ruling: {msg}");
}

#[test]
fn stthisbyname_is_hard_error() {
    let file = build_byname(|id| Bytecode::Stthisbyname(Imm(0), id));
    let err = lift_file(&file).expect_err("stthisbyname must fail lift (N51)");
    assert!(
        matches!(
            err,
            abcd_ir::lift::LiftError::UnsupportedThisByAccess("stthisbyname")
        ),
        "dedicated N51 variant naming the opcode, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("stthisbyname"),
        "error names the opcode: {msg}"
    );
}

#[test]
fn ldthisbyvalue_is_hard_error() {
    let file = build_byvalue(|| Bytecode::Ldthisbyvalue(Imm(0)));
    let err = lift_file(&file).expect_err("ldthisbyvalue must fail lift (N51)");
    assert!(
        matches!(
            err,
            abcd_ir::lift::LiftError::UnsupportedThisByAccess("ldthisbyvalue")
        ),
        "dedicated N51 variant naming the opcode, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("ldthisbyvalue"),
        "error names the opcode: {msg}"
    );
}

#[test]
fn stthisbyvalue_is_hard_error() {
    let file = build_byvalue(|| Bytecode::Stthisbyvalue(Imm(0), Reg(0)));
    let err = lift_file(&file).expect_err("stthisbyvalue must fail lift (N51)");
    assert!(
        matches!(
            err,
            abcd_ir::lift::LiftError::UnsupportedThisByAccess("stthisbyvalue")
        ),
        "dedicated N51 variant naming the opcode, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("stthisbyvalue"),
        "error names the opcode: {msg}"
    );
}
