//! Roundtrip test for the lower-to-encode entity relocation channel:
//! decode → lift → lower → `to_method_body` → `abcd_file::encode` → decode,
//! asserting entity operands resolve to the same targets after the real
//! relocation path (`MethodBody.entity_offsets` + `Builder::relocate_code_id`)
//! rewrote the raw indices. Also covers the channel's hard errors for
//! untraceable entity operands.

use abcd_file::{AccessFlags, Builder, CodeEntity, File, LiteralValue, Type};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::{EntityTrace, LowerError, lower_function, to_method_body};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg, encode as encode_bytecodes};

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
/// target method in another class. Builder + decode yields a real File with
/// genuine index regions and entity_offsets — the same shape decode produces
/// for corpus files.
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

#[test]
fn lowered_method_body_roundtrips_through_encode_relocation() {
    let (file, entities) = build_input_file();
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_empty());

    let caller_id = (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == "caller")
        .expect("caller function");

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    // The relocation channel contract: string/method operands carry their
    // source offsets in the bytecode, so the entries are identities; the
    // literal-array operand carries the decoded table index mapped back to
    // its source offset.
    assert_eq!(
        body.entity_offsets[&(EntityKind::StringId, entities.string_offset)],
        entities.string_offset
    );
    assert_eq!(
        body.entity_offsets[&(EntityKind::MethodId, entities.target_offset)],
        entities.target_offset
    );
    let array_index = file.literal_array_offsets[&entities.array_offset];
    assert_eq!(
        body.entity_offsets[&(EntityKind::LiteralarrayId, array_index)],
        entities.array_offset
    );
    // Every string/method operand must be selection-time traced.
    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            if kind != EntityKind::LiteralarrayId {
                assert_eq!(result.entity_traces.get(&id.0), Some(&EntityTrace::Traced));
            }
        }
    }
    // Frame convention: vregs from the lowering frame, args from the IR
    // function signature.
    assert_eq!(body.num_vregs, u32::from(result.num_regs));
    assert_eq!(body.num_args, 0);

    // Splice the lowered body into a copy of the source file and run the
    // real encode + relocation path.
    let mut rebuilt = file.clone();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            if method.offset == entities.caller_offset {
                method.body = Some(body.clone());
            }
        }
    }
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

/// A hand-built module has no source file: lowering stays lenient (identity
/// EntityId fallback), but the relocation channel must hard-error instead of
/// passing an unresolvable operand through.
#[test]
fn untraced_string_operand_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new(file.version, file.file_type);
    let func = IRBuilder::create_function(&mut module, "f", abcd_file::FunctionKind::Function, 0);
    let mut builder = IRBuilder::new(&mut module, func);
    let name = builder.intern("no-such-source-string");
    builder.emit_val(InstData::LiteralString(name), IrType::default());
    builder.emit_void(InstData::Return { value: None });

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

/// A string operand whose recorded source offset does not resolve in the
/// given file (module/file mismatch) must hard-error, not relocate to a
/// dangling offset.
#[test]
fn stale_source_offset_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new(file.version, file.file_type);
    let func = IRBuilder::create_function(&mut module, "f", abcd_file::FunctionKind::Function, 0);
    let mut builder = IRBuilder::new(&mut module, func);
    let name = builder.intern("payload");
    builder.emit_val(InstData::LiteralString(name), IrType::default());
    builder.emit_void(InstData::Return { value: None });
    // Forge a source mapping to an offset the file does not contain.
    module.string_entities.insert(name, EntityId(0xdead));

    let result = lower_function(&module, func).expect("lower");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::StringId,
                raw: 0xdead,
                ..
            }
        ),
        "expected UntraceableEntity for a stale offset, got {err:?}"
    );
}

/// A literal-array operand whose table index has no source offset in the
/// file must hard-error.
#[test]
fn unknown_literal_array_index_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new(file.version, file.file_type);
    let func = IRBuilder::create_function(&mut module, "f", abcd_file::FunctionKind::Function, 0);
    let mut builder = IRBuilder::new(&mut module, func);
    builder.emit_val(
        InstData::CreateArrayWithBuffer { literal_array: 99 },
        IrType::default(),
    );
    builder.emit_void(InstData::Return { value: None });

    let result = lower_function(&module, func).expect("lower");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                raw: 99,
                ..
            }
        ),
        "expected UntraceableEntity for an unknown literal-array index, got {err:?}"
    );
}

/// Build the S3 input file: a global-class `spread` method whose body
/// creates an empty object into v0, loads a string into the accumulator,
/// and runs the real `copydataproperties v0` (vendor
/// `copydataproperties v:in:top, acc: inout:top`: the register operand is
/// the target object, the accumulator carries the source and receives the
/// result).
fn build_spread_input_file() -> File {
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
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// S3 regression: `copydataproperties` must round-trip as the real opcode.
///
/// Red state: lift models the instruction as
/// `StoreProperty { key: ByName("[[CopyDataProperties]]") }` with a
/// synthetic interned name that exists in no source file; isel lowers that
/// to `stobjbyname` with an identity-fallback StringId operand, and
/// `to_method_body` hard-errors with `UntraceableEntity` (the 18
/// object-spread corpus skips).
#[test]
fn copydataproperties_survives_lift_lower_encode_as_the_real_opcode() {
    let file = build_spread_input_file();
    let module = lift_file(&file).expect("lift");

    let spread_id = (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == "spread")
        .expect("spread function");

    // Lift must not synthesize the fake "[[CopyDataProperties]]" property
    // name: no StoreProperty keyed by it may exist anywhere in the module.
    for &bb in &module.func(spread_id).blocks {
        for &inst_id in &module.block(bb).insts {
            if let InstData::StoreProperty {
                key: abcd_ir::inst::PropKind::ByName(name),
                ..
            } = &module.inst(inst_id).data
            {
                assert_ne!(
                    module.strings.get(*name),
                    "[[CopyDataProperties]]",
                    "lift must not model copydataproperties as a synthetic-name store"
                );
            }
        }
    }

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
    let mut rebuilt = file.clone();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            if method.offset == spread_offset {
                method.body = Some(body.clone());
            }
        }
    }
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

/// S3, deprecated form: `deprecated.copydataproperties v1, v2` (v1 = target,
/// v2 = source, `acc: out:top`) lifts to the same IR variant and lowers to
/// the modern opcode — the codebase's deprecated-opcode convention (cf.
/// `DeprecatedDelobjprop` → `DeleteProperty` → `Delobjprop`). No corpus
/// fixture uses this form, so this builder-driven body is its only
/// end-to-end coverage.
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
    assert!(verify_module(&module).is_empty());
    let spread_id = (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == "spread")
        .expect("spread function");

    // Exactly one CopyDataProperties, no synthetic-name StoreProperty.
    let mut saw_copy = false;
    for &bb in &module.func(spread_id).blocks {
        for &inst_id in &module.block(bb).insts {
            match &module.inst(inst_id).data {
                InstData::CopyDataProperties { .. } => saw_copy = true,
                InstData::StoreProperty {
                    key: abcd_ir::inst::PropKind::ByName(name),
                    ..
                } => assert_ne!(module.strings.get(*name), "[[CopyDataProperties]]"),
                _ => {}
            }
        }
    }
    assert!(saw_copy, "deprecated form must lift to CopyDataProperties");

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
    let mut rebuilt = file.clone();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            if method.offset == spread_offset {
                method.body = Some(body.clone());
            }
        }
    }
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
