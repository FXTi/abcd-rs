//! Roundtrip tests for the lower-to-encode entity relocation and per-method
//! `u16` compaction channel (`design/ir.md` §5, `design/decisions.md` `ADR-10`):
//! decode → lift → lower → `to_method_body` → `abcd_file::encode` → decode,
//! asserting entity operands resolve to the same targets after relocation
//! (`MethodBody.entity_offsets` + `Builder::relocate_code_id`), plus hard
//! errors for untraceable entity operands.
//!
//! Emitted raw operands in `LayoutResult` are IR identities (`Sym` /
//! function-table `FuncId` / `ConstId`), which `to_method_body` resolves to
//! source-file offsets and compacts into per-method `u16` placeholder indices.
//! Name collisions between methods and strings (`S1`/`N2`) are impossible by
//! construction because method identity is always the function-table index.

use crate::common;
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

    // Relocation channel contract: IR entity identities resolve to source
    // offsets — the method by function-table position, the string by content,
    // and the literal shape by content.
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

/// `S1`/`N2`: a string/method name collision ("A" the string vs "A" the
/// method) cannot alias because `DefineFunc` carries the function-table index,
/// never the name.
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

/// `N2`: two same-named methods referenced from one body keep their own
/// function-table indices and relocate to their own offsets.
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
        let c1 = builder.konst(Const::number(1.0));
        let c2 = builder.konst(Const::number(2.0));
        let c3 = builder.konst(Const::number(3.0));
        let shape = builder.konst(Const::ArrayLiteral(vec![c1, c2, c3]));
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

// ─── N62 literal-dedup matcher matrix ────────────────────────────────────────
//
// `to_method_body`'s reverse literal-shape resolution
// (`const_matches_literal_array`/`const_matches_literal_value`/
// `typed_array_table_index`) mirrors the lift's forward resolution for
// every `LiteralValue` kind. The corpus literal tables carry only a subset
// (Integer/Double/String/Method/...), so the rare kinds — Integer8, Float,
// BuiltinTypeIndex, EtsImplements, the method-kind tags, the typed-array
// raw-offset payloads — plus the guard arms (non-array tree, depth>64,
// out-of-range table index) are pinned here with hand-built const trees
// matched against hand-extended decoded files.

use abcd_file::{LiteralArray, LiteralArrayIdx};
use abcd_ir::ConstId;
use abcd_lower::LayoutResult;

/// A lowered-result stand-in carrying one `createarraywithbuffer` per given
/// shape const (entity operand raw value = the ConstId), so
/// `to_method_body`'s reverse resolution runs on it.
fn layout_result_with_shapes(shapes: &[ConstId]) -> LayoutResult {
    let mut bytecodes: Vec<Bytecode> = shapes
        .iter()
        .map(|&cid| Bytecode::Createarraywithbuffer(Imm(0), EntityId(cid.0)))
        .collect();
    bytecodes.push(Bytecode::Returnundefined);
    LayoutResult {
        bytecodes,
        try_blocks: Vec::new(),
        num_regs: 0,
        entity_traces: Default::default(),
        ic_size: 0,
    }
}

/// Resolve `shape` (a const of `module`) against `file`'s literal-array
/// table through the real `to_method_body` channel.
fn resolve_shape(
    file: &File,
    module: &Module,
    shape: ConstId,
) -> Result<abcd_file::MethodBody, LowerError> {
    let result = layout_result_with_shapes(&[shape]);
    to_method_body(module, FuncId::new(0), &result, file)
}

/// Push a literal array onto the file's table, registered at `offset`.
fn push_array(file: &mut File, offset: u32, values: Vec<LiteralValue>) -> u32 {
    let idx = file.literal_arrays.len() as u32;
    file.literal_arrays.push(LiteralArray { values });
    file.literal_array_offsets.insert(offset, idx);
    idx
}

/// The resolved source offset of the first shape operand in the produced body
/// (looking up its compacted method-local `u16` key in `entity_offsets`).
fn resolved_offset(body: &abcd_file::MethodBody, _shape: ConstId) -> u32 {
    let (kind, local_id) = body
        .bytecodes
        .iter()
        .flat_map(|bc| bc.entity_operands())
        .find(|(k, _)| *k == EntityKind::LiteralarrayId)
        .expect("body must carry a LiteralarrayId operand");
    body.entity_offsets[&(kind, local_id.0)]
}

/// Rare scalar tags: an 8-bit integer, a 32-bit float, and a builtin-type
/// index all match a `Const::Number` by payload value.
#[test]
fn literal_dedup_matches_rare_scalar_kinds() {
    let (mut file, _) = build_input_file();
    push_array(
        &mut file,
        0x9500,
        vec![
            LiteralValue::Integer8(42),
            LiteralValue::Float(2.5),
            LiteralValue::BuiltinTypeIndex(7),
        ],
    );
    let mut module = Module::new();
    let c42 = module.consts.push(Const::number(42.0));
    let c25 = module.consts.push(Const::number(2.5));
    let c7 = module.consts.push(Const::number(7.0));
    let shape = module.consts.push_array(vec![c42, c25, c7]);
    let body = resolve_shape(&file, &module, shape)
        .expect("Integer8/Float/BuiltinTypeIndex payloads match by value");
    assert_eq!(resolved_offset(&body, shape), 0x9500);

    // A payload mismatch (43 != 42) does NOT match — nothing resolves.
    let mut module = Module::new();
    let c43 = module.consts.push(Const::number(43.0));
    let c25 = module.consts.push(Const::number(2.5));
    let c7 = module.consts.push(Const::number(7.0));
    let wrong = module.consts.push_array(vec![c43, c25, c7]);
    let err = resolve_shape(&file, &module, wrong)
        .expect_err("a mismatched Integer8 payload must not resolve");
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                raw,
                ..
            } if raw == wrong.0
        ),
        "expected UntraceableEntity, got {err:?}"
    );
}

/// An `EtsImplements` string entry matches a `Const::String` by content
/// (same arm as the plain `String` tag).
#[test]
fn literal_dedup_matches_ets_implements_by_content() {
    let (mut file, _) = build_input_file();
    let sid = file
        .strings
        .get("payload")
        .expect("the input file carries the string \"payload\"");
    push_array(&mut file, 0x9510, vec![LiteralValue::EtsImplements(sid)]);

    let mut module = Module::new();
    let sym = module.sym.intern("payload");
    let c_sym = module.consts.push(Const::String(sym));
    let shape = module.consts.push_array(vec![c_sym]);
    let body = resolve_shape(&file, &module, shape)
        .expect("EtsImplements matches a string const by content");
    assert_eq!(resolved_offset(&body, shape), 0x9510);

    // Different content must not match.
    let mut module = Module::new();
    let other = module.sym.intern("not-payload");
    let c_other = module.consts.push(Const::String(other));
    let wrong = module.consts.push_array(vec![c_other]);
    let err = resolve_shape(&file, &module, wrong).expect_err("different content must not resolve");
    assert!(
        matches!(err, LowerError::UntraceableEntity { .. }),
        "expected UntraceableEntity, got {err:?}"
    );
}

/// The rare method-kind tags (async-generator / getter / setter) match a
/// `Const::MethodRef` by function-table position, like the plain `Method`
/// and `GeneratorMethod` tags do. Each kind gets its own file: the matcher
/// takes the SMALLEST matching table index, and the tags are
/// indistinguishable from each other by content.
#[test]
fn literal_dedup_matches_rare_method_kinds() {
    for (i, make) in [
        LiteralValue::AsyncGeneratorMethod as fn(u32) -> LiteralValue,
        LiteralValue::Getter,
        LiteralValue::Setter,
    ]
    .into_iter()
    .enumerate()
    {
        let (mut file, entities) = build_input_file();
        let target_index = file
            .all_methods()
            .position(|(_, m)| m.offset == entities.target_offset)
            .expect("target is in the function table") as u32;
        let offset = 0x9520 + 0x10 * i as u32;
        push_array(&mut file, offset, vec![make(entities.target_offset)]);

        let mut module = Module::new();
        let c_mref = module
            .consts
            .push(Const::MethodRef(FuncId::new(target_index)));
        let shape = module.consts.push_array(vec![c_mref]);
        let body = resolve_shape(&file, &module, shape)
            .expect("async-generator/getter/setter tags resolve by table position");
        assert_eq!(resolved_offset(&body, shape), offset);
    }
}

/// The typed-array/raw-buffer payload family (`LiteralBufferIndex` and
/// `ArrayU1`..`ArrayString`, N52): each payload is a raw file offset that
/// resolves to a table index through the offset map (with a direct-index
/// fallback for hand-built models), and the nested array then matches by
/// content.
#[test]
fn literal_dedup_matches_the_typed_array_family() {
    let (mut file, _) = build_input_file();
    // The shared nested match target: [7].
    let inner = push_array(&mut file, 0x9600, vec![LiteralValue::Integer(7)]);
    // Thirteen raw payloads: twelve resolve through the offset map, the
    // thirteenth (ArrayString) uses the direct-index fallback — its raw
    // value IS the target's table index and is absent from the map.
    let mut raws = Vec::new();
    for i in 0..12u32 {
        raws.push(0x9700 + i * 0x10);
    }
    let outer_values = vec![
        LiteralValue::LiteralBufferIndex(LiteralArrayIdx(raws[0])),
        LiteralValue::ArrayU1(LiteralArrayIdx(raws[1])),
        LiteralValue::ArrayU8(LiteralArrayIdx(raws[2])),
        LiteralValue::ArrayI8(LiteralArrayIdx(raws[3])),
        LiteralValue::ArrayU16(LiteralArrayIdx(raws[4])),
        LiteralValue::ArrayI16(LiteralArrayIdx(raws[5])),
        LiteralValue::ArrayU32(LiteralArrayIdx(raws[6])),
        LiteralValue::ArrayI32(LiteralArrayIdx(raws[7])),
        LiteralValue::ArrayU64(LiteralArrayIdx(raws[8])),
        LiteralValue::ArrayI64(LiteralArrayIdx(raws[9])),
        LiteralValue::ArrayF32(LiteralArrayIdx(raws[10])),
        LiteralValue::ArrayF64(LiteralArrayIdx(raws[11])),
        LiteralValue::ArrayString(LiteralArrayIdx(inner)),
    ];
    for &raw in &raws {
        file.literal_array_offsets.insert(raw, inner);
    }
    let outer = push_array(&mut file, 0x9800, outer_values);
    assert_eq!(outer, 2, "the input file starts with one literal array");

    let mut module = Module::new();
    let c7 = module.consts.push(Const::number(7.0));
    let inner_cid = module.consts.push_array(vec![c7]);
    let shape = module
        .consts
        .push_array((0..13).map(|_| inner_cid).collect());
    let body = resolve_shape(&file, &module, shape)
        .expect("every typed-array payload kind resolves to the nested target");
    assert_eq!(resolved_offset(&body, shape), 0x9800);
}

/// A typed-array payload whose raw offset is neither in the offset map nor
/// a valid direct index resolves to NOTHING — the shape is untraceable.
#[test]
fn literal_dedup_typed_array_unknown_offset_is_untraceable() {
    let (mut file, _) = build_input_file();
    push_array(
        &mut file,
        0x9810,
        vec![LiteralValue::ArrayU8(LiteralArrayIdx(0xDEAD))],
    );
    let mut module = Module::new();
    let empty_arr = module.consts.push_array(vec![]);
    let shape = module.consts.push_array(vec![empty_arr]);
    let err = resolve_shape(&file, &module, shape)
        .expect_err("an unmappable typed-array payload must not resolve");
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                ..
            }
        ),
        "expected UntraceableEntity, got {err:?}"
    );
}

/// The depth guard: literal trees nested deeper than 64 levels never match
/// (the forward lift resolution has the same guard) — the shape is
/// untraceable even though every intermediate level pairs up.
#[test]
fn literal_dedup_depth_guard_beyond_64_levels() {
    let (mut file, _) = build_input_file();
    // Chain: table[1] = [LiteralArray(2)], table[2] = [LiteralArray(3)], …
    // — 65 links deep; index 66 never exists (the guard fires first).
    for i in 1..=65u32 {
        let idx = file.literal_arrays.len() as u32;
        assert_eq!(idx, i);
        file.literal_arrays.push(LiteralArray {
            values: vec![LiteralValue::LiteralArray(LiteralArrayIdx(i + 1))],
        });
    }
    // The matching const pool chain, 65 levels of nesting.
    let mut module = Module::new();
    let mut cur = module.consts.push_array(vec![]);
    for _ in 0..65 {
        cur = module.consts.push_array(vec![cur]);
    }
    let shape = cur;
    let err =
        resolve_shape(&file, &module, shape).expect_err("a 65-deep nesting hits the depth guard");
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                ..
            }
        ),
        "expected UntraceableEntity, got {err:?}"
    );
}

/// A NON-array const tree matched against the literal table fails
/// immediately (the guard before the element walk), and a nested
/// `LiteralArray` payload past the end of the table fails the lookup.
#[test]
fn literal_dedup_rejects_non_array_trees_and_oob_nested_indices() {
    let (mut file, _) = build_input_file();
    // (a) the shape const is not an ArrayLiteral at all.
    let mut module = Module::new();
    let null_shape = module.consts.push(Const::Null);
    let err = resolve_shape(&file, &module, null_shape)
        .expect_err("a non-array tree never matches a literal array");
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                ..
            }
        ),
        "(a) expected UntraceableEntity, got {err:?}"
    );

    // (b) the nested payload index is out of the table's range.
    push_array(
        &mut file,
        0x9820,
        vec![LiteralValue::LiteralArray(LiteralArrayIdx(999))],
    );
    let mut module = Module::new();
    let empty_arr = module.consts.push_array(vec![]);
    let shape = module.consts.push_array(vec![empty_arr]);
    let err = resolve_shape(&file, &module, shape)
        .expect_err("an out-of-range nested index must not resolve");
    assert!(
        matches!(
            err,
            LowerError::UntraceableEntity {
                kind: EntityKind::LiteralarrayId,
                ..
            }
        ),
        "(b) expected UntraceableEntity, got {err:?}"
    );
}

/// #32 commercial `--merge-abc` regression (`94,065` `Sym`s in `modules.abc`):
/// when `module.sym` holds `> 65,536` symbols, `isel` emits `Sym.0 >= 65,536`
/// in `LayoutResult.bytecodes`, which exceeds the 16-bit `id:u16` encoding
/// limit if left uncompacted. Verify that `to_method_body`, `rewrite_file`,
/// and `lower_module` all compact per-method `EntityId`s into `u16` indices,
/// pass `abcd_isa::encode` and `abcd_file::encode -> decode`, and preserve the
/// target strings (`Sym >= 65,590`) without loss.
#[test]
fn symbols_above_65536_compact_and_roundtrip_across_all_body_builders() {
    use abcd_file::{SourceLang, Version};
    use abcd_ir::Modifiers;
    use abcd_lower::{LowerOptions, lower_module, rewrite_file};

    const TARGET_STR: &str = "high_sym_str_65590";
    const TARGET_PROP: &str = "high_sym_prop_65591";

    // Build a base `.abc` file that already contains TARGET_STR and TARGET_PROP
    // so `to_method_body` (which resolves against an existing source `File`) as
    // well as `rewrite_file` and `lower_module` can all be exercised.
    let mut fb = Builder::new();
    fb.set_api(12, "beta1");
    let cls = fb.add_global_class();
    fb.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = fb.create_proto(Type::Tagged, &[Type::Tagged]);
    let placeholder = EntityId(0);
    let (stub_code, stub_offs) = encode_bytecodes(&[
        Bytecode::LdaStr(placeholder),
        Bytecode::Ldobjbyname(Imm(0), placeholder),
        Bytecode::Return,
    ])
    .expect("encode stub");
    let m_h = fb.class_add_method(
        cls,
        "high_sym_fn",
        proto,
        AccessFlags::STATIC,
        &stub_code,
        0,
        1,
    );
    fb.method_set_source_lang(m_h, SourceLang::EcmaScript);
    let s_str = fb.add_string(TARGET_STR);
    let s_prop = fb.add_string(TARGET_PROP);
    fb.relocate_code_id(m_h, stub_offs[0], 0, CodeEntity::String(s_str))
        .unwrap();
    fb.relocate_code_id(m_h, stub_offs[1], 0, CodeEntity::String(s_prop))
        .unwrap();
    let base_bytes = fb.finalize().expect("finalize base file");
    let base_file = abcd_file::decode(&base_bytes).expect("decode base file");
    let fn_offset = method_by_name(&base_file, "high_sym_fn").offset;

    // Construct an IR module with > 65,536 symbols BEFORE interning TARGET_STR
    // and TARGET_PROP so their `Sym.0` indices sit well above `u16::MAX`.
    let mut module = Module::new();
    let global_desc = module.sym.intern("L_GLOBAL;");
    let mut cls_data = abcd_ir::ClassData::new(global_desc, global_desc);
    cls_data.modifiers = Modifiers::PUBLIC;
    module.classes.push(cls_data);

    let func = V2Builder::create_function(&mut module, "high_sym_fn", FunctionKind::Function);
    module.functions[func.index()].modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    module.classes[0].methods.push(func);

    while module.sym.len() < 65_590 {
        let idx = module.sym.len();
        module.sym.intern(&format!("pad_sym_{idx}"));
    }
    let sym_str = module.sym.intern(TARGET_STR);
    let sym_prop = module.sym.intern(TARGET_PROP);
    let sym_synth = module.sym.intern("high_sym_synth_65592");
    while module.sym.len() < 65_600 {
        let idx = module.sym.len();
        module.sym.intern(&format!("pad_tail_{idx}"));
    }
    assert!(sym_str.0 >= 65_590 && sym_prop.0 > u32::from(u16::MAX));
    assert!(sym_synth.0 > u32::from(u16::MAX));

    {
        let mut b = V2Builder::new(&mut module, func);
        let recv = b.create_param();
        let cid = b.konst(Const::String(sym_str));
        // Reference `sym_str` twice and `sym_prop` once to pin deduplication too.
        let s1 = b.emit_val(Op::LoadConst(cid));
        let _ = b.emit_val(Op::LoadProp {
            object: recv,
            name: sym_prop,
        });
        let s2 = b.emit_val(Op::LoadConst(cid));
        let prop_val = b.emit_val(Op::LoadProp {
            object: s1,
            name: sym_prop,
        });
        let _ = s2;
        b.emit_void(Op::Return {
            value: Some(prop_val),
        });
    }
    assert!(verify_module(&module).is_ok());

    let lowered = lower_function(&module, func).expect("lower_function must succeed");
    // Raw `LayoutResult` carries uncompacted `Sym.0 > 65,535` (confirming that
    // direct `encode_bytecodes(&lowered.bytecodes)` would fail without compaction).
    assert!(
        lowered
            .bytecodes
            .iter()
            .flat_map(|bc| bc.entity_operands())
            .any(|(_, id)| id.0 > u32::from(u16::MAX)),
        "pre-compaction LayoutResult must carry raw Sym >= 65536"
    );

    let assert_decoded_strings = |decoded: &File, expected: &[&str]| {
        let m = method_by_name(decoded, "high_sym_fn");
        let body = m.body.as_ref().expect("method body");
        encode_bytecodes(&body.bytecodes).expect("decoded body bytecodes fit u16");
        let resolved: Vec<&str> = body
            .bytecodes
            .iter()
            .flat_map(|bc| bc.entity_operands())
            .filter(|(k, _)| *k == EntityKind::StringId)
            .map(|(k, id)| {
                let off = body.entity_offsets[&(k, id.0)];
                decoded.resolve_entity_str(off).expect("resolved string")
            })
            .collect();
        for &target in expected {
            assert!(
                resolved.contains(&target),
                "expected string {target:?} in resolved entity operands, got {resolved:?}"
            );
        }
    };

    // 1. `to_method_body` path:
    let body = to_method_body(&module, func, &lowered, &base_file)
        .expect("to_method_body must compact Sym >= 65536");
    encode_bytecodes(&body.bytecodes)
        .expect("to_method_body compacted bytecodes must pass abcd_isa::encode");
    assert_eq!(
        body.entity_offsets.len(),
        2,
        "duplicate uses of sym_str and sym_prop must deduplicate to 2 local StringId slots"
    );
    let spliced = splice_body(&base_file, fn_offset, &body);
    let enc1 = abcd_file::encode(&spliced).expect("abcd_file::encode after to_method_body");
    let dec1 = abcd_file::decode(&enc1).expect("decode after to_method_body");
    assert_decoded_strings(&dec1, &[TARGET_STR, TARGET_PROP]);

    // Also append a synthesized string (`sym_synth`, absent from `base_file`)
    // to exercise `rewrite_file` and `lower_module` materialization at Sym > 65535.
    {
        let entry = module.functions[func.index()].blocks[0];
        let ret_inst = module.blocks[entry.index()].insts.pop().unwrap();
        let mut b = V2Builder::new(&mut module, func);
        let synth_cid = b.konst(Const::String(sym_synth));
        let v_synth = b.emit_val(Op::LoadConst(synth_cid));
        let _ = ret_inst;
        b.emit_void(Op::Return {
            value: Some(v_synth),
        });
    }
    assert!(verify_module(&module).is_ok());

    // 2. `rewrite_file` path:
    let rewritten = rewrite_file(&module, &base_file, LowerOptions::default())
        .expect("rewrite_file must compact Sym >= 65536");
    let rw_body = method_by_name(&rewritten, "high_sym_fn")
        .body
        .as_ref()
        .expect("rewritten body");
    encode_bytecodes(&rw_body.bytecodes)
        .expect("rewrite_file compacted bytecodes must pass abcd_isa::encode");
    let enc2 = abcd_file::encode(&rewritten).expect("abcd_file::encode after rewrite_file");
    let dec2 = abcd_file::decode(&enc2).expect("decode after rewrite_file");
    assert_decoded_strings(&dec2, &[TARGET_STR, TARGET_PROP, "high_sym_synth_65592"]);

    // 3. `lower_module` standalone path:
    let standalone = lower_module(&module, Version::new(12, 0, 6, 0))
        .expect("lower_module must compact Sym >= 65536");
    let st_body = method_by_name(&standalone, "high_sym_fn")
        .body
        .as_ref()
        .expect("standalone body");
    encode_bytecodes(&st_body.bytecodes)
        .expect("lower_module compacted bytecodes must pass abcd_isa::encode");
    let enc3 = abcd_file::encode(&standalone).expect("abcd_file::encode after lower_module");
    let dec3 = abcd_file::decode(&enc3).expect("decode after lower_module");
    assert_decoded_strings(&dec3, &[TARGET_STR, TARGET_PROP, "high_sym_synth_65592"]);
}
