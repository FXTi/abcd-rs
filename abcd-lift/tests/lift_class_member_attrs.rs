//! B2 golden (v0.2 lifter): the `defineclasswithbuffer` member buffer's
//! attribute payloads lift into [`abcd_ir::op::MemberAttrs`] —
//! placement (static vs instance) from the trailing `i32 nonStaticNum`
//! and the callable kind from the entry's method-kind tag, with the
//! conservative EMPTY fallback for shapes outside the vendor-grounded
//! member form.
//!
//! Vendor grounding (arkcompiler_ets_runtime-master): the buffer's
//! collapsed runtime array keeps (name, value) pairs and hides the
//! non-static count in the last slot
//! (`ecmascript/jspandafile/class_info_extractor.cpp:36-42`); pairs
//! at-or-past that count are STATIC (`class_info_extractor.cpp:78`).

use abcd_file::{AccessFlags, Builder, CodeEntity, File, LiteralArrayHandle, Type, decode};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{MemberAttrs, Op};
use abcd_isa::{Bytecode, EntityId, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity ids wired later via `relocate_code_id`.
const M_PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);
const L_PLACEHOLDER: EntityId = EntityId((u16::MAX - 1) as u32);

/// Build a 12.x file: global class with ctor `A`, member method `has`,
/// and `f` running `defineclasswithbuffer` over the given buffer.
fn build_class_file(
    fill: impl FnOnce(&mut Builder, LiteralArrayHandle, abcd_file::MethodHandle),
) -> File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (ret, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let ctor = b.class_add_method(cls, "A", proto, AccessFlags::STATIC, &ret, 0, 3);
    let member = b.class_add_method(cls, "has", proto, AccessFlags::STATIC, &ret, 0, 4);
    let la = b.add_literal_array("members");
    fill(&mut b, la, member);
    let bytecodes = [
        Bytecode::Defineclasswithbuffer(Imm(0), M_PLACEHOLDER, L_PLACEHOLDER, Imm(0), Reg(0)),
        Bytecode::Returnundefined,
    ];
    let (code, offsets) = encode_bytecodes(&bytecodes).unwrap();
    let f = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 1, 3);
    b.relocate_code_id(f, offsets[0], 0, CodeEntity::Method(ctor))
        .unwrap();
    b.relocate_code_id(f, offsets[0], 1, CodeEntity::LiteralArray(la))
        .unwrap();
    decode(&b.finalize().unwrap()).unwrap()
}

/// The `DefineClass` op's member_attrs of the built file.
fn lifted_attrs(file: &File) -> Vec<MemberAttrs> {
    let module = lift_file(file).expect("lift");
    for inst in &module.insts {
        if let Op::DefineClass { member_attrs, .. } = &inst.op {
            return member_attrs.clone();
        }
    }
    panic!("DefineClass emitted")
}

#[test]
fn static_method_placement_from_trailing_zero_nonstatic() {
    // { string:"has", method:has, method_affiliate:1, i32:0 } — zero
    // non-static members → the single member is STATIC (the
    // private-property-in corpus shape).
    let file = build_class_file(|b, la, member| {
        let name = b.add_string("has");
        b.literal_array_add_string(la, name);
        b.literal_array_add_method(la, member);
        b.literal_array_add_method_affiliate(la, 1);
        b.literal_array_add_integer(la, 0);
    });
    assert_eq!(
        lifted_attrs(&file),
        vec![MemberAttrs {
            is_static: true,
            kind: FunctionKind::Function,
        }]
    );
}

#[test]
fn instance_method_placement_from_nonstatic_count() {
    // { string:"has", method:has, method_affiliate:1, i32:1 } — one
    // non-static member → INSTANCE placement (the private-field corpus
    // shape).
    let file = build_class_file(|b, la, member| {
        let name = b.add_string("has");
        b.literal_array_add_string(la, name);
        b.literal_array_add_method(la, member);
        b.literal_array_add_method_affiliate(la, 1);
        b.literal_array_add_integer(la, 1);
    });
    assert_eq!(
        lifted_attrs(&file),
        vec![MemberAttrs {
            is_static: false,
            kind: FunctionKind::Function,
        }]
    );
}

#[test]
fn missing_trailing_count_is_conservative_empty() {
    // No trailing i32 — outside the grounded member form: attributes
    // UNKNOWN (empty), never guessed.
    let file = build_class_file(|b, la, member| {
        let name = b.add_string("has");
        b.literal_array_add_string(la, name);
        b.literal_array_add_method(la, member);
        b.literal_array_add_method_affiliate(la, 1);
    });
    assert!(lifted_attrs(&file).is_empty());
}

#[test]
fn nonstatic_count_exceeding_members_is_conservative_empty() {
    // i32:5 with a single member — malformed: attributes UNKNOWN.
    let file = build_class_file(|b, la, member| {
        let name = b.add_string("has");
        b.literal_array_add_string(la, name);
        b.literal_array_add_method(la, member);
        b.literal_array_add_method_affiliate(la, 1);
        b.literal_array_add_integer(la, 5);
    });
    assert!(lifted_attrs(&file).is_empty());
}
