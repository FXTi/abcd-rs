//! Roundtrip test for the v0.2 lower-to-encode entity relocation channel
//! (port of `abcd-ir/tests/lower_method_body.rs`): decode → v0.2 lift →
//! lower → `to_method_body` → `abcd_file::encode` → decode, asserting
//! entity operands resolve to the same targets after the real relocation
//! path (`MethodBody.entity_offsets` + `Builder::relocate_code_id`)
//! rewrote the raw indices. Also covers the channel's hard errors for
//! untraceable entity operands.
//!
//! v0.2 differences: emitted raw operands are IR identities (Sym /
//! function-table index / ConstId), and the reverse resolution (content /
//! function-table position / literal-shape content → source offset) lives
//! in `to_method_body`. The S1/N2 name-collision regressions are
//! non-issues BY CONSTRUCTION in v0.2 (method identity is the
//! function-table index, never a name); the tests below pin the
//! equivalent end-to-end behavior.

mod common;

use abcd_file::{AccessFlags, Builder, CodeEntity, File, LiteralValue, Type};
use abcd_ir::{Const, FuncId, FunctionKind, Module, Op, verify_module};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::{LowerError, lower_function, to_method_body};

use common::V2Builder;

/// Offsets of the entities the caller body references, as assigned by the
/// builder-produced input file.
struct SourceEntities {
    caller_offset: u32,
    target_offset: u32,
    string_offset: u32,
    array_offset: u32,
}

/// Build the input file: a global-class `caller` method whose body carries a
/// method reference (definefunc), a string reference (lda.str), and a
/// literal-array reference (createarraywithbuffer), plus the referenced
/// target method in another class.
fn build_input_file() -> (File, SourceEntities) {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let class = builder.add_global_class();
    let other_class = builder.add_class("LOther;");
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(2)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Createarraywithbuffer(Imm(1), placeholder),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let caller = builder.class_add_method(class, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    let (ret, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let target = builder.class_add_method(
        other_class,
        "target",
        proto,
        AccessFlags::STATIC,
        &ret,
        0,
        0,
    );
    let name = builder.add_string("payload");
    let array = builder.add_literal_array("payload-array");
    builder.literal_array_add_integer(array, 42);
    builder
        .relocate_code_id(caller, offsets[0], 0, CodeEntity::Method(target))
        .unwrap();
    builder
        .relocate_code_id(caller, offsets[1], 0, CodeEntity::String(name))
        .unwrap();
    builder
        .relocate_code_id(caller, offsets[2], 0, CodeEntity::LiteralArray(array))
        .unwrap();
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();

    let caller_offset = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .unwrap()
        .1
        .offset;
    let target_offset = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("target"))
        .unwrap()
        .1
        .offset;
    let body = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
        .unwrap()
        .1
        .body
        .as_ref()
        .unwrap();
    let mut string_offset = None;
    let mut array_offset = None;
    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset = body.entity_offsets[&(kind, id.0)];
            match kind {
                EntityKind::StringId => string_offset = Some(offset),
                EntityKind::LiteralarrayId => array_offset = Some(offset),
                EntityKind::MethodId => {}
            }
        }
    }
    (
        file,
        SourceEntities {
            caller_offset,
            target_offset,
            string_offset: string_offset.unwrap(),
            array_offset: array_offset.unwrap(),
        },
    )
}

fn method_by_name<'a>(file: &'a File, name: &str) -> &'a abcd_file::Method {
    file.all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some(name))
        .unwrap_or_else(|| panic!("method {name}"))
        .1
}

fn method_in_class<'a>(file: &'a File, descriptor: &str, name: &str) -> &'a abcd_file::Method {
    file.all_methods()
        .find(|(desc, m)| {
            file.strings.resolve(*desc) == Some(descriptor)
                && file.strings.resolve(m.name) == Some(name)
        })
        .unwrap_or_else(|| panic!("method {name} in {descriptor}"))
        .1
}

fn func_id_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.functions[f.index()].name) == Some(name))
        .unwrap_or_else(|| panic!("function {name}"))
}

/// Replace `target_offset`'s body in a clone of `file` with `body`.
fn splice_body(file: &File, target_offset: u32, body: &abcd_file::MethodBody) -> File {
    let mut rebuilt = file.clone();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            if method.offset == target_offset {
                method.body = Some(body.clone());
            }
        }
    }
    rebuilt
}

/// The relocation entries of the lowered caller body, keyed by entity
/// kind: every entity operand's (kind, raw) → source offset.
fn relocation_targets(
    body: &abcd_file::MethodBody,
) -> std::collections::HashMap<EntityKind, Vec<u32>> {
    let mut out: std::collections::HashMap<EntityKind, Vec<u32>> = Default::default();
    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            out.entry(kind)
                .or_default()
                .push(body.entity_offsets[&(kind, id.0)]);
        }
    }
    out
}

#[test]
fn lowered_method_body_roundtrips_through_encode_relocation() {
    let (file, entities) = build_input_file();
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());

    let caller_id = func_id_by_name(&module, "caller");

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    // The v0.2 relocation channel contract: raw operands are IR
    // identities (Sym / FuncId / ConstId); the entries resolve them to
    // the source offsets — the method by function-table position, the
    // string by content, the literal shape by content.
    let targets = relocation_targets(&body);
    assert_eq!(targets[&EntityKind::MethodId], vec![entities.target_offset]);
    assert_eq!(targets[&EntityKind::StringId], vec![entities.string_offset]);
    assert_eq!(
        targets[&EntityKind::LiteralarrayId],
        vec![entities.array_offset]
    );
    // Frame convention: vregs from the lowering frame, args from the IR
    // function signature.
    assert_eq!(body.num_vregs, u32::from(result.num_regs));
    assert_eq!(body.num_args, 0);

    // Splice the lowered body into a copy of the source file and run the
    // real encode + relocation path.
    let rebuilt = splice_body(&file, entities.caller_offset, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let out_caller = method_by_name(&output, "caller");
    let out_body = out_caller.body.as_ref().unwrap();
    assert_eq!(out_body.num_vregs, u32::from(result.num_regs));
    assert_eq!(out_body.num_args, 0);

    // Resolve every entity operand of the re-encoded body through the output
    // file and compare targets (resolved names/contents, not raw indices).
    let out_target_offset = method_by_name(&output, "target").offset;
    let mut saw_method = false;
    let mut saw_string = false;
    let mut saw_array = false;
    for bc in &out_body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset = out_body.entity_offsets[&(kind, id.0)];
            match kind {
                EntityKind::MethodId => {
                    assert_eq!(offset, out_target_offset);
                    assert_eq!(output.resolve_entity_str(offset), Some("target"));
                    saw_method = true;
                }
                EntityKind::StringId => {
                    assert_eq!(output.resolve_entity_str(offset), Some("payload"));
                    saw_string = true;
                }
                EntityKind::LiteralarrayId => {
                    let index = output.literal_array_offsets[&offset] as usize;
                    assert!(
                        matches!(
                            output.literal_arrays[index].values.as_slice(),
                            [LiteralValue::Integer(42)]
                        ),
                        "literal array contents must survive relocation"
                    );
                    saw_array = true;
                }
            }
        }
    }
    assert!(saw_method && saw_string && saw_array);
}

/// S1/N2 in v0.2: a string/method name collision ("A" the string vs "A"
/// the method) is a non-issue by construction — the DefineFunc's identity
/// is the function-table index, never the name. Pin the end-to-end
/// behavior: both operands relocate to their own entities.
#[test]
fn string_first_name_collision_relocates_method_operand_to_the_method() {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let global = builder.add_global_class();
    let class_a = builder.add_class("LA;");
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::LdaStr(placeholder),
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let caller =
        builder.class_add_method(global, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    let (ret, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let ctor = builder.class_add_method(class_a, "A", proto, AccessFlags::STATIC, &ret, 0, 0);
    let name = builder.add_string("A");
    builder
        .relocate_code_id(caller, offsets[0], 0, CodeEntity::String(name))
        .unwrap();
    builder
        .relocate_code_id(caller, offsets[1], 0, CodeEntity::Method(ctor))
        .unwrap();
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();
    let caller_offset = method_by_name(&file, "caller").offset;

    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    let caller_id = func_id_by_name(&module, "caller");

    // IR identity: the DefineFunc body's function-table index names the
    // "A" METHOD, independent of the string "A".
    let ctor_index = file
        .all_methods()
        .position(|(_, m)| file.strings.resolve(m.name) == Some("A"))
        .unwrap();
    let define_bodies: Vec<usize> = module.functions[caller_id.index()]
        .blocks
        .iter()
        .flat_map(|&bb| module.blocks[bb.index()].insts.iter())
        .filter_map(|&inst| match &module.insts[inst.index()].op {
            Op::DefineFunc { body, .. } => Some(body.index()),
            _ => None,
        })
        .collect();
    assert_eq!(define_bodies, vec![ctor_index]);

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    let rebuilt = splice_body(&file, caller_offset, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let out_ctor = method_in_class(&output, "LA;", "A");
    let out_body = method_by_name(&output, "caller").body.clone().unwrap();
    let mut saw_method = false;
    let mut saw_string = false;
    for bc in &out_body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset = out_body.entity_offsets[&(kind, id.0)];
            match kind {
                EntityKind::MethodId => {
                    assert_eq!(
                        offset, out_ctor.offset,
                        "definefunc must relocate to the method \"A\", not the string \"A\""
                    );
                    saw_method = true;
                }
                EntityKind::StringId => {
                    assert_eq!(output.resolve_entity_str(offset), Some("A"));
                    saw_string = true;
                }
                EntityKind::LiteralarrayId => {}
            }
        }
    }
    assert!(saw_method && saw_string);
}

/// N2 in v0.2: two same-named methods referenced from one body keep their
/// own function-table indices and relocate to their own offsets.
#[test]
fn same_named_method_references_keep_their_own_offsets() {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let global = builder.add_global_class();
    let class_a = builder.add_class("LA;");
    let class_b = builder.add_class("LB;");
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Definefunc(Imm(1), placeholder, Imm(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let caller =
        builder.class_add_method(global, "caller", proto, AccessFlags::STATIC, &code, 1, 0);
    let (ret1, _) = encode_bytecodes(&[Bytecode::Returnundefined]).unwrap();
    let m1 = builder.class_add_method(class_a, "f", proto, AccessFlags::STATIC, &ret1, 0, 0);
    let (ret2, _) = encode_bytecodes(&[Bytecode::Ldai(Imm(7)), Bytecode::Returnundefined]).unwrap();
    let m2 = builder.class_add_method(class_b, "f", proto, AccessFlags::STATIC, &ret2, 0, 0);
    let name = builder.add_string("f");
    builder
        .relocate_code_id(caller, offsets[0], 0, CodeEntity::Method(m1))
        .unwrap();
    builder
        .relocate_code_id(caller, offsets[1], 0, CodeEntity::String(name))
        .unwrap();
    builder
        .relocate_code_id(caller, offsets[2], 0, CodeEntity::Method(m2))
        .unwrap();
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();
    let caller_offset = method_by_name(&file, "caller").offset;

    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    let caller_id = func_id_by_name(&module, "caller");

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    let rebuilt = splice_body(&file, caller_offset, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let m1_out = method_in_class(&output, "LA;", "f").offset;
    let m2_out = method_in_class(&output, "LB;", "f").offset;
    assert_ne!(m1_out, m2_out, "the two methods are distinct entities");

    let out_body = method_by_name(&output, "caller").body.clone().unwrap();
    let method_offsets: Vec<u32> = out_body
        .bytecodes
        .iter()
        .flat_map(|bc| bc.entity_operands())
        .filter(|(kind, _)| *kind == EntityKind::MethodId)
        .map(|(kind, id)| out_body.entity_offsets[&(kind, id.0)])
        .collect();
    assert_eq!(
        method_offsets,
        vec![m1_out, m2_out],
        "each definefunc must relocate to its own method"
    );
    // The string operand still resolves to the string "f".
    let saw_string = out_body.bytecodes.iter().any(|bc| {
        bc.entity_operands().iter().any(|(kind, id)| {
            *kind == EntityKind::StringId
                && output.resolve_entity_str(out_body.entity_offsets[&(*kind, id.0)]) == Some("f")
        })
    });
    assert!(saw_string, "lda.str operand must survive relocation");
}

/// A hand-built module has no source file: lowering stays lenient (the
/// Sym emits fine), but the relocation channel must hard-error instead of
/// passing an unresolvable operand through.
#[test]
fn untraced_string_operand_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let sym = builder.sym("no-such-source-string");
        let cid = builder.konst(Const::String(sym));
        builder.emit_val(Op::LoadConst(cid));
        builder.emit_void(Op::Return { value: None });
    }

    let result = lower_function(&module, func).expect("lower_function stays lenient");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::StringId,
                ..
            }
        ),
        "expected UntraceableEntity for an unmapped string, got {err:?}"
    );
}

/// A method reference whose function-table index has no method in the
/// file must hard-error.
#[test]
fn out_of_range_method_reference_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        builder.emit_val(Op::DefineFunc {
            body: FuncId::new(99),
            captures: Vec::new(),
            length: 0,
        });
        builder.emit_void(Op::Return { value: None });
    }

    let result = lower_function(&module, func).expect("lower");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::MethodId,
                raw: 99,
                ..
            }
        ),
        "expected UntraceableEntity for an out-of-range method reference, got {err:?}"
    );
}

/// A literal shape no literal array of the file matches must hard-error.
#[test]
fn unknown_literal_shape_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let shape = builder.konst(Const::ArrayLiteral(vec![
            Const::number(1.0),
            Const::number(2.0),
            Const::number(3.0),
        ]));
        builder.emit_val(Op::AllocArray { shape: Some(shape) });
        builder.emit_void(Op::Return { value: None });
    }

    let result = lower_function(&module, func).expect("lower");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                ..
            }
        ),
        "expected UntraceableEntity for an unknown literal shape, got {err:?}"
    );
}

/// S3 regression: `copydataproperties` must round-trip as the real opcode.
#[test]
fn copydataproperties_survives_lift_lower_encode_as_the_real_opcode() {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = encode_bytecodes(&[
        Bytecode::Createemptyobject,
        Bytecode::Sta(Reg(0)),
        Bytecode::LdaStr(placeholder),
        Bytecode::Copydataproperties(Reg(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let spread = builder.class_add_method(class, "spread", proto, AccessFlags::STATIC, &code, 1, 0);
    let name = builder.add_string("payload");
    builder
        .relocate_code_id(spread, offsets[2], 0, CodeEntity::String(name))
        .unwrap();
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();

    let module = lift_file(&file).expect("lift");
    let spread_id = func_id_by_name(&module, "spread");

    let result = lower_function(&module, spread_id).expect("lower spread");
    let body = to_method_body(&module, spread_id, &result, &file)
        .expect("copydataproperties has no entity operands and must relocate cleanly");

    // The lowered body must contain the real opcode and no stobjbyname
    // impersonating it.
    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "lowered body must contain Copydataproperties, got {:?}",
        body.bytecodes
    );
    assert!(
        !body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..))),
        "lowered body must not contain Stobjbyname, got {:?}",
        body.bytecodes
    );

    // Full encode → decode roundtrip: the opcode must survive relocation.
    let spread_offset = method_by_name(&file, "spread").offset;
    let rebuilt = splice_body(&file, spread_offset, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");
    let out_body = method_by_name(&output, "spread")
        .body
        .as_ref()
        .unwrap()
        .clone();
    assert!(
        out_body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "re-encoded body must still contain Copydataproperties, got {:?}",
        out_body.bytecodes
    );
    // The string operand of lda.str must still resolve to "payload".
    let saw_payload = out_body.bytecodes.iter().any(|bc| {
        bc.entity_operands().iter().any(|(kind, id)| {
            *kind == EntityKind::StringId
                && output.resolve_entity_str(out_body.entity_offsets[&(*kind, id.0)])
                    == Some("payload")
        })
    });
    assert!(saw_payload, "lda.str operand must survive relocation");
}

/// S3, deprecated form: `deprecated.copydataproperties v1, v2` lifts to
/// the same op and lowers to the modern opcode.
#[test]
fn deprecated_copydataproperties_lifts_and_lowers_to_the_modern_opcode() {
    let mut builder = Builder::new();
    builder.set_api(24, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[
        Bytecode::Createemptyobject,
        Bytecode::Sta(Reg(0)),
        Bytecode::Createemptyobject,
        Bytecode::Sta(Reg(1)),
        Bytecode::DeprecatedCopydataproperties(Reg(0), Reg(1)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    builder.class_add_method(class, "spread", proto, AccessFlags::STATIC, &code, 2, 0);
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();

    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    let spread_id = func_id_by_name(&module, "spread");

    // Exactly one CopyDataProps.
    let mut saw_copy = false;
    for &bb in &module.functions[spread_id.index()].blocks {
        for &inst_id in &module.blocks[bb.index()].insts {
            if matches!(&module.insts[inst_id.index()].op, Op::CopyDataProps { .. }) {
                saw_copy = true;
            }
        }
    }
    assert!(saw_copy, "deprecated form must lift to CopyDataProps");

    let result = lower_function(&module, spread_id).expect("lower");
    let body = to_method_body(&module, spread_id, &result, &file).expect("method body");
    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "deprecated form must lower to the modern Copydataproperties, got {:?}",
        body.bytecodes
    );
    assert!(
        !body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..))),
        "no Stobjbyname impersonation, got {:?}",
        body.bytecodes
    );

    let spread_offset = method_by_name(&file, "spread").offset;
    let rebuilt = splice_body(&file, spread_offset, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");
    let out_body = method_by_name(&output, "spread").body.clone().unwrap();
    assert!(
        out_body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_))),
        "re-encoded body must still contain Copydataproperties, got {:?}",
        out_body.bytecodes
    );
}
