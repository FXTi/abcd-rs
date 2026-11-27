//! `D8` (repealing historical `N51`): IC-fused `this` property accesses —
//! `ldthisbyname`, `stthisbyname`, `ldthisbyvalue`, and `stthisbyvalue`
//! (`isa.yaml:1627-1646`) — lift cleanly by binding `this` via
//! `abcd_ir::frame::this_param_index` (`FnLift::this_value`, matching `ldthis`)
//! and emitting [`Op::LoadProp`], [`Op::StoreProp`], [`Op::LoadPropDyn`], and
//! [`Op::StorePropDyn`].

use std::collections::HashMap;

use abcd_file::{
    AccessFlags, Builder, CodeEntity, File, FileType, FunctionKind as FileFunctionKind, Method,
    MethodBody, SourceLang as FileSourceLang, StringPool, Type, Version, decode,
};
use abcd_ir::{Const, Dialect, Op, ValueDef, ValueId};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

/// Placeholder entity id wired later via `relocate_code_id`.
const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a 12.x dynamic file whose global class carries one method `f`
/// (`num_args` parameters; `num_args = 3` gives `[func, new.target, this]`
/// under `0xF` default).
fn build_file(
    bytecodes: &[Bytecode],
    num_vregs: u32,
    num_args: u32,
    wire: impl FnOnce(&mut Builder, abcd_file::MethodHandle, &[u32]),
) -> abcd_file::File {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(bytecodes).unwrap();
    let m = b.class_add_method(
        cls,
        "f",
        proto,
        AccessFlags::STATIC,
        &code,
        num_vregs,
        num_args,
    );
    wire(&mut b, m, &offsets);
    decode(&b.finalize().unwrap()).unwrap()
}

fn verify_clean(m: &abcd_ir::Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors: {:?}",
        report.errors
    );
}

fn const_of(m: &abcd_ir::Module, v: ValueId) -> Const {
    match &m.values[v.index()].def {
        ValueDef::Const(c) => m.consts.get(*c).expect("const").clone(),
        ValueDef::Inst(iid) => match &m.insts[iid.index()].op {
            Op::LoadConst(c) => m.consts.get(*c).expect("const").clone(),
            other => panic!("expected LoadConst behind {v:?}, got {other:?}"),
        },
        other => panic!("expected const-defined value for {v:?}, got {other:?}"),
    }
}

#[test]
fn ldthisbyname_lifts_load_prop_on_this_param() {
    let file = build_file(
        &[
            Bytecode::Ldthisbyname(Imm(0), PLACEHOLDER),
            Bytecode::Return,
        ],
        0,
        3,
        |b, m, offsets| {
            let name = b.add_string("key");
            b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(name))
                .unwrap();
        },
    );
    let mut m = lift_file(&file).expect("ldthisbyname lifts cleanly");
    verify_clean(&m);
    let f = &m.functions[0];
    let this_param = f.params[2];
    let key_sym = m.sym.intern("key");

    let (load_val, ret_val) = (
        m.insts
            .iter()
            .find_map(|i| match &i.op {
                Op::LoadProp { object, name } => {
                    assert_eq!(*object, this_param, "object is params[2] (`this`)");
                    assert_eq!(*name, key_sym);
                    i.result
                }
                _ => None,
            })
            .expect("LoadProp emitted"),
        m.insts
            .iter()
            .find_map(|i| match &i.op {
                Op::Return { value } => *value,
                _ => None,
            })
            .expect("Return carries acc"),
    );
    assert_eq!(load_val, ret_val, "ldthisbyname writes result into acc");
}

#[test]
fn stthisbyname_lifts_store_prop_on_this_param() {
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(42)),
            Bytecode::Stthisbyname(Imm(0), PLACEHOLDER),
            Bytecode::Returnundefined,
        ],
        0,
        3,
        |b, m, offsets| {
            let name = b.add_string("prop");
            b.relocate_code_id(m, offsets[1], 0, CodeEntity::String(name))
                .unwrap();
        },
    );
    let mut m = lift_file(&file).expect("stthisbyname lifts cleanly");
    verify_clean(&m);
    let this_param = m.functions[0].params[2];
    let prop_sym = m.sym.intern("prop");

    let found = m.insts.iter().find_map(|i| match &i.op {
        Op::StoreProp {
            object,
            name,
            value,
        } => Some((*object, *name, *value)),
        _ => None,
    });
    let (object, name, value) = found.expect("StoreProp emitted");
    assert_eq!(object, this_param, "object is params[2] (`this`)");
    assert_eq!(name, prop_sym);
    assert_eq!(const_of(&m, value), Const::number(42.0), "value = acc");
}

#[test]
fn ldthisbyvalue_lifts_load_prop_dyn_with_acc_key() {
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(7)),
            Bytecode::Ldthisbyvalue(Imm(0)),
            Bytecode::Return,
        ],
        0,
        3,
        |_, _, _| {},
    );
    let m = lift_file(&file).expect("ldthisbyvalue lifts cleanly");
    verify_clean(&m);
    let this_param = m.functions[0].params[2];

    let (load_res, object, key) = m
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::LoadPropDyn { object, key } => Some((i.result.unwrap(), *object, *key)),
            _ => None,
        })
        .expect("LoadPropDyn emitted");
    assert_eq!(object, this_param, "object is params[2] (`this`)");
    assert_eq!(const_of(&m, key), Const::number(7.0), "key = acc input");

    let ret_val = m
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::Return { value } => *value,
            _ => None,
        })
        .expect("Return value");
    assert_eq!(ret_val, load_res, "ldthisbyvalue writes result into acc");
}

#[test]
fn stthisbyvalue_lifts_store_prop_dyn_with_reg_key_and_acc_value() {
    let file = build_file(
        &[
            Bytecode::Ldai(Imm(9)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldai(Imm(99)),
            Bytecode::Stthisbyvalue(Imm(0), Reg(0)),
            Bytecode::Returnundefined,
        ],
        1,
        3,
        |_, _, _| {},
    );
    let m = lift_file(&file).expect("stthisbyvalue lifts cleanly");
    verify_clean(&m);
    let this_param = m.functions[0].params[2];

    let (object, key, value) = m
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::StorePropDyn { object, key, value } => Some((*object, *key, *value)),
            _ => None,
        })
        .expect("StorePropDyn emitted");
    assert_eq!(object, this_param, "object is params[2] (`this`)");
    assert_eq!(const_of(&m, key), Const::number(9.0), "key = Reg(0)");
    assert_eq!(const_of(&m, value), Const::number(99.0), "value = acc");
}

#[test]
fn this_by_access_respects_static_arkts_instance_and_no_this_fallback() {
    // 1. StaticArkTS (`0.1.0.7`) non-static instance method binds `this` at `params[0]`.
    let mut strings = StringPool::default();
    let desc = strings.get_or_intern("LWidget;");
    let m_name = strings.get_or_intern("getVal");
    let field_str = strings.get_or_intern("count");
    let inst_method = Method {
        name: m_name,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC, // instance method (no STATIC)
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::ArkTs,
        is_external: false,
        return_type: None,
        arg_types: vec![Type::Reference(desc)],
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 1,
            bytecodes: vec![
                Bytecode::Ldthisbyname(Imm(0), EntityId(0)),
                Bytecode::Return,
            ],
            entities: HashMap::from([(
                (EntityKind::StringId, 0),
                abcd_file::EntityRef::string(field_str),
            )]),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };
    let cls = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::ArkTs,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![inst_method],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let static_file = File {
        version: Version::new(0, 1, 0, 7),
        checksum: 0,
        size: 0,
        file_type: FileType::Static,
        strings,
        classes: [(desc, cls)].into_iter().collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };
    let m_static = lift_file(&static_file).expect("lift StaticArkTS instance ldthisbyname");
    verify_clean(&m_static);
    assert_eq!(m_static.dialect, Dialect::StaticArkTS);
    let obj_static = m_static
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::LoadProp { object, .. } => Some(*object),
            _ => None,
        })
        .expect("LoadProp");
    assert_eq!(
        obj_static, m_static.functions[0].params[0],
        "StaticArkTS instance method binds `this` to params[0]"
    );

    // 2. Dynamic method with `num_args = 0` (shorter than implicit prefix) falls back to Undefined.
    let no_this_file = build_file(
        &[
            Bytecode::Ldthisbyname(Imm(0), PLACEHOLDER),
            Bytecode::Returnundefined,
        ],
        0,
        0,
        |b, m, offsets| {
            let name = b.add_string("x");
            b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(name))
                .unwrap();
        },
    );
    let m_fallback = lift_file(&no_this_file).expect("no-this fallback lifts cleanly");
    verify_clean(&m_fallback);
    let obj_fallback = m_fallback
        .insts
        .iter()
        .find_map(|i| match &i.op {
            Op::LoadProp { object, .. } => Some(*object),
            _ => None,
        })
        .expect("LoadProp");
    assert_eq!(const_of(&m_fallback, obj_fallback), Const::Undefined);
}
