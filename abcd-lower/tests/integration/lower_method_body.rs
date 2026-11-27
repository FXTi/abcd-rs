//! Roundtrip tests for the lower-to-encode entity relocation and per-method
//! `u16` compaction channel (`design/ir.md` §5, `design/decisions.md` `ADR-10`,
//! `#50` `R3-D2`, `#57` `R3-H9`):
//! decode → lift → lower → `to_method_body` → `abcd_file::encode` → decode,
//! asserting entity operands resolve to the same typed [`EntityRef`] targets
//! after relocation (`MethodBody.entities`), plus hard errors for untraceable
//! entity operands and tag-exact literal-array matching.

use crate::common;
use abcd_file::{
    AccessFlags, Builder, CodeEntity, EntityRef, File, LiteralArray, LiteralArrayIdx, LiteralValue,
    MethodIdx, StringId, Type,
};
use abcd_ir::{
    Const, ConstId, FuncId, FunctionKind, LitMethodKind, Module, Op, TypedArrayTag, verify_module,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::{LayoutResult, LowerError, lower_function, to_method_body};

use common::V2Builder;

/// Expected semantic targets of the entities the caller body references.
struct SourceEntities {
    caller_idx: MethodIdx,
    target_idx: MethodIdx,
    string_id: StringId,
    array_idx: LiteralArrayIdx,
}

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

    let caller_idx = MethodIdx(
        file.all_methods()
            .position(|(_, m)| file.strings.resolve(m.name) == Some("caller"))
            .unwrap() as u32,
    );
    let target_idx = MethodIdx(
        file.all_methods()
            .position(|(_, m)| file.strings.resolve(m.name) == Some("target"))
            .unwrap() as u32,
    );
    let body = file
        .method_by_idx(caller_idx)
        .unwrap()
        .2
        .body
        .as_ref()
        .unwrap();
    let mut string_id = None;
    let mut array_idx = None;
    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            match body.entities[&(kind, id.0)] {
                EntityRef::String { id: sid, .. } => string_id = Some(sid),
                EntityRef::LiteralArray(lidx) => array_idx = Some(lidx),
                EntityRef::Method(_) | EntityRef::ExternalMethod { .. } => {}
            }
        }
    }
    (
        file,
        SourceEntities {
            caller_idx,
            target_idx,
            string_id: string_id.unwrap(),
            array_idx: array_idx.unwrap(),
        },
    )
}

fn method_by_name<'a>(file: &'a File, name: &str) -> &'a abcd_file::Method {
    file.all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some(name))
        .unwrap_or_else(|| panic!("method {name}"))
        .1
}

fn method_idx_by_name(file: &File, name: &str) -> MethodIdx {
    MethodIdx(
        file.all_methods()
            .position(|(_, m)| file.strings.resolve(m.name) == Some(name))
            .unwrap_or_else(|| panic!("method {name}")) as u32,
    )
}

fn method_idx_in_class(file: &File, descriptor: &str, name: &str) -> MethodIdx {
    MethodIdx(
        file.all_methods()
            .position(|(desc, m)| {
                file.strings.resolve(desc) == Some(descriptor)
                    && file.strings.resolve(m.name) == Some(name)
            })
            .unwrap_or_else(|| panic!("method {name} in {descriptor}")) as u32,
    )
}

fn func_id_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.functions[f.index()].name) == Some(name))
        .unwrap_or_else(|| panic!("function {name}"))
}

/// Replace `target_idx`'s body in a clone of `file` with `body`.
fn splice_body(file: &File, target_idx: MethodIdx, body: &abcd_file::MethodBody) -> File {
    let mut rebuilt = file.clone();
    let mut rem = target_idx.index();
    for class in rebuilt.classes.values_mut() {
        if rem < class.methods.len() {
            class.methods[rem].body = Some(body.clone());
            return rebuilt;
        }
        rem -= class.methods.len();
    }
    panic!("method_idx {target_idx:?} out of range");
}

#[test]
fn lowered_method_body_roundtrips_through_encode_relocation() {
    let (file, entities) = build_input_file();
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());

    let caller_id = func_id_by_name(&module, "caller");

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    assert_eq!(body.num_vregs, u32::from(result.num_regs));
    assert_eq!(body.num_args, 0);

    for bc in &body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            match (kind, body.entities[&(kind, id.0)]) {
                (EntityKind::MethodId, EntityRef::Method(midx)) => {
                    assert_eq!(midx, entities.target_idx);
                }
                (EntityKind::StringId, EntityRef::String { id: sid, .. }) => {
                    assert_eq!(sid, entities.string_id);
                }
                (EntityKind::LiteralarrayId, EntityRef::LiteralArray(lidx)) => {
                    assert_eq!(lidx, entities.array_idx);
                }
                other => panic!("unexpected entity binding: {other:?}"),
            }
        }
    }

    let rebuilt = splice_body(&file, entities.caller_idx, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let out_caller = method_by_name(&output, "caller");
    let out_body = out_caller.body.as_ref().unwrap();
    assert_eq!(out_body.num_vregs, u32::from(result.num_regs));
    assert_eq!(out_body.num_args, 0);

    let out_target_idx = method_idx_by_name(&output, "target");
    let mut saw_method = false;
    let mut saw_string = false;
    let mut saw_array = false;
    for bc in &out_body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            match (kind, out_body.entities[&(kind, id.0)]) {
                (EntityKind::MethodId, EntityRef::Method(midx)) => {
                    assert_eq!(midx, out_target_idx);
                    saw_method = true;
                }
                (EntityKind::StringId, EntityRef::String { id: sid, .. }) => {
                    assert_eq!(output.strings.resolve(sid), Some("payload"));
                    saw_string = true;
                }
                (EntityKind::LiteralarrayId, EntityRef::LiteralArray(lidx)) => {
                    assert!(
                        matches!(
                            output.literal_arrays[lidx.index()].values.as_slice(),
                            [LiteralValue::Integer(42)]
                        ),
                        "literal array contents must survive relocation"
                    );
                    saw_array = true;
                }
                other => panic!("unexpected entity in decoded output: {other:?}"),
            }
        }
    }
    assert!(saw_method && saw_string && saw_array);
}

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
    let caller_idx = method_idx_by_name(&file, "caller");

    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    let caller_id = func_id_by_name(&module, "caller");

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

    let rebuilt = splice_body(&file, caller_idx, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let out_ctor_idx = method_idx_in_class(&output, "LA;", "A");
    let out_body = method_by_name(&output, "caller").body.clone().unwrap();
    let mut saw_method = false;
    let mut saw_string = false;
    for bc in &out_body.bytecodes {
        for (kind, id) in bc.entity_operands() {
            match (kind, out_body.entities[&(kind, id.0)]) {
                (EntityKind::MethodId, EntityRef::Method(midx)) => {
                    assert_eq!(midx, out_ctor_idx);
                    saw_method = true;
                }
                (EntityKind::StringId, EntityRef::String { id: sid, .. }) => {
                    assert_eq!(output.strings.resolve(sid), Some("A"));
                    saw_string = true;
                }
                _ => {}
            }
        }
    }
    assert!(saw_method && saw_string);
}

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
    let caller_idx = method_idx_by_name(&file, "caller");

    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_ok());
    let caller_id = func_id_by_name(&module, "caller");

    let result = lower_function(&module, caller_id).expect("lower caller");
    let body = to_method_body(&module, caller_id, &result, &file).expect("method body");

    let rebuilt = splice_body(&file, caller_idx, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");

    let m1_out = method_idx_in_class(&output, "LA;", "f");
    let m2_out = method_idx_in_class(&output, "LB;", "f");
    assert_ne!(m1_out, m2_out);

    let out_body = method_by_name(&output, "caller").body.clone().unwrap();
    let method_refs: Vec<MethodIdx> = out_body
        .bytecodes
        .iter()
        .flat_map(|bc| bc.entity_operands())
        .filter(|(kind, _)| *kind == EntityKind::MethodId)
        .map(|(kind, id)| match out_body.entities[&(kind, id.0)] {
            EntityRef::Method(midx) => midx,
            other => panic!("expected MethodIdx, got {other:?}"),
        })
        .collect();
    assert_eq!(method_refs, vec![m1_out, m2_out]);

    let saw_string = out_body.bytecodes.iter().any(|bc| {
        bc.entity_operands().iter().any(|(kind, id)| {
            *kind == EntityKind::StringId
                && matches!(
                    out_body.entities[&(*kind, id.0)],
                    EntityRef::String { id: sid, .. } if output.strings.resolve(sid) == Some("f")
                )
        })
    });
    assert!(saw_string);
}

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
    assert!(matches!(
        err,
        LowerError::UntraceableEntity {
            kind: EntityKind::StringId,
            ..
        }
    ));
}

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
    assert!(matches!(
        err,
        LowerError::UntraceableEntity {
            kind: EntityKind::MethodId,
            raw: 99,
            ..
        }
    ));
}

#[test]
fn unknown_literal_shape_is_a_hard_error() {
    let (file, _) = build_input_file();
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let c1 = builder.konst(Const::Int32(1));
        let c2 = builder.konst(Const::Int32(2));
        let c3 = builder.konst(Const::Int32(3));
        let shape = builder.konst(Const::ArrayLiteral(vec![c1, c2, c3]));
        builder.emit_val(Op::AllocArray { shape: Some(shape) });
        builder.emit_void(Op::Return { value: None });
    }

    let result = lower_function(&module, func).expect("lower");
    let err = to_method_body(&module, func, &result, &file).unwrap_err();
    assert!(matches!(
        err,
        LowerError::UntraceableEntity {
            kind: EntityKind::LiteralarrayId,
            ..
        }
    ));
}

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

    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_)))
    );
    assert!(
        !body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stobjbyname(..)))
    );

    let spread_idx = method_idx_by_name(&file, "spread");
    let rebuilt = splice_body(&file, spread_idx, &body);
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
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_)))
    );
    let saw_payload = out_body.bytecodes.iter().any(|bc| {
        bc.entity_operands().iter().any(|(kind, id)| {
            *kind == EntityKind::StringId
                && matches!(
                    out_body.entities[&(*kind, id.0)],
                    EntityRef::String { id: sid, .. } if output.strings.resolve(sid) == Some("payload")
                )
        })
    });
    assert!(saw_payload);
}

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

    let result = lower_function(&module, spread_id).expect("lower");
    let body = to_method_body(&module, spread_id, &result, &file).expect("method body");
    assert!(
        body.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_)))
    );

    let spread_idx = method_idx_by_name(&file, "spread");
    let rebuilt = splice_body(&file, spread_idx, &body);
    let encoded = abcd_file::encode(&rebuilt).expect("encode rebuilt file");
    let output = abcd_file::decode(&encoded).expect("decode rebuilt file");
    let out_body = method_by_name(&output, "spread").body.clone().unwrap();
    assert!(
        out_body
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Copydataproperties(_)))
    );
}

// ─── Tag-exact literal-dedup matcher matrix (`#50` `R3-D2`, `#57` `R3-H9`) ──

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
        inst_pcs: Default::default(),
    }
}

fn resolve_shape(
    file: &File,
    module: &Module,
    shape: ConstId,
) -> Result<abcd_file::MethodBody, LowerError> {
    let result = layout_result_with_shapes(&[shape]);
    to_method_body(module, FuncId::new(0), &result, file)
}

fn push_array(file: &mut File, values: Vec<LiteralValue>) -> LiteralArrayIdx {
    let idx = LiteralArrayIdx(file.literal_arrays.len() as u32);
    file.literal_arrays.push(LiteralArray::new(values));
    idx
}

fn resolved_lit_idx(body: &abcd_file::MethodBody) -> LiteralArrayIdx {
    let (kind, local_id) = body
        .bytecodes
        .iter()
        .flat_map(|bc| bc.entity_operands())
        .find(|(k, _)| *k == EntityKind::LiteralarrayId)
        .expect("body must carry a LiteralarrayId operand");
    match body.entities[&(kind, local_id.0)] {
        EntityRef::LiteralArray(idx) => idx,
        other => panic!("expected LiteralArrayIdx, got {other:?}"),
    }
}

/// Tag-exact scalar matching (`R3-H9`): `Integer8`, `Float`, and
/// `BuiltinTypeIndex` match their exact `Const` counterparts and NEVER collide
/// with `Const::Number` / `Const::Int32` of equal numeric value.
#[test]
fn literal_dedup_matches_rare_scalar_kinds_with_tag_exactness() {
    let (mut file, _) = build_input_file();
    let expected_idx = push_array(
        &mut file,
        vec![
            LiteralValue::Integer8(42),
            LiteralValue::Float(2.5),
            LiteralValue::BuiltinTypeIndex(7),
        ],
    );

    let mut module = Module::new();
    let c42 = module.consts.push(Const::Int8(42));
    let c25 = module.consts.push(Const::float32(2.5));
    let c7 = module.consts.push(Const::BuiltinTypeIndex(7));
    let shape = module.consts.push_array(vec![c42, c25, c7]);
    let body = resolve_shape(&file, &module, shape).expect("tag-exact rare scalars must match");
    assert_eq!(resolved_lit_idx(&body), expected_idx);

    // Same numeric values with `Const::Number` (`Double` tag) must NOT collide!
    let mut wrong_tag_mod = Module::new();
    let d42 = wrong_tag_mod.consts.push(Const::number(42.0));
    let d25 = wrong_tag_mod.consts.push(Const::number(2.5));
    let d7 = wrong_tag_mod.consts.push(Const::number(7.0));
    let wrong_tag = wrong_tag_mod.consts.push_array(vec![d42, d25, d7]);
    assert!(matches!(
        resolve_shape(&file, &wrong_tag_mod, wrong_tag),
        Err(LowerError::UntraceableEntity {
            kind: EntityKind::LiteralarrayId,
            ..
        })
    ));
}

#[test]
fn literal_dedup_matches_ets_implements_without_colliding_with_plain_string() {
    let (mut file, _) = build_input_file();
    let sid = file.strings.get("payload").unwrap();
    let ets_idx = push_array(&mut file, vec![LiteralValue::EtsImplements(sid)]);

    let mut module = Module::new();
    let sym = module.sym.intern("payload");
    let c_ets = module.consts.push(Const::EtsImplements(sym));
    let shape = module.consts.push_array(vec![c_ets]);
    let body = resolve_shape(&file, &module, shape).expect("EtsImplements matches tag-exactly");
    assert_eq!(resolved_lit_idx(&body), ets_idx);

    // Plain `Const::String` with identical text must NOT match `EtsImplements`.
    let mut plain_str_mod = Module::new();
    let psym = plain_str_mod.sym.intern("payload");
    let c_str = plain_str_mod.consts.push(Const::String(psym));
    let wrong = plain_str_mod.consts.push_array(vec![c_str]);
    assert!(matches!(
        resolve_shape(&file, &plain_str_mod, wrong),
        Err(LowerError::UntraceableEntity { .. })
    ));
}

#[test]
fn literal_dedup_matches_rare_method_kinds_tag_exactly() {
    for (make_lit, ir_kind) in [
        (
            LiteralValue::AsyncGeneratorMethod as fn(MethodIdx) -> LiteralValue,
            LitMethodKind::AsyncGeneratorMethod,
        ),
        (LiteralValue::Getter, LitMethodKind::Getter),
        (LiteralValue::Setter, LitMethodKind::Setter),
    ] {
        let (mut file, entities) = build_input_file();
        let expected_idx = push_array(&mut file, vec![make_lit(entities.target_idx)]);

        let mut module = Module::new();
        let c_mref = module.consts.push(Const::method_ref_with_kind(
            FuncId::new(entities.target_idx.0),
            ir_kind,
        ));
        let shape = module.consts.push_array(vec![c_mref]);
        let body = resolve_shape(&file, &module, shape).expect("method kind resolves tag-exactly");
        assert_eq!(resolved_lit_idx(&body), expected_idx);

        // Mismatched method kind (`LitMethodKind::Method`) must NOT collide.
        let mut wrong_mod = Module::new();
        let c_wrong = wrong_mod
            .consts
            .push(Const::method_ref(FuncId::new(entities.target_idx.0)));
        let wrong_shape = wrong_mod.consts.push_array(vec![c_wrong]);
        assert!(resolve_shape(&file, &wrong_mod, wrong_shape).is_err());
    }
}

#[test]
fn literal_dedup_matches_the_typed_array_and_buffer_ref_family() {
    let (mut file, _) = build_input_file();
    let str_sid = file.strings.get_or_intern("ta-elem");
    let inner = push_array(&mut file, vec![LiteralValue::Integer(7)]);
    let outer_values = vec![
        LiteralValue::LiteralBufferIndex(inner),
        LiteralValue::ArrayU1(vec![true]),
        LiteralValue::ArrayU8(vec![7]),
        LiteralValue::ArrayI8(vec![-7]),
        LiteralValue::ArrayU16(vec![7]),
        LiteralValue::ArrayI16(vec![-7]),
        LiteralValue::ArrayU32(vec![7]),
        LiteralValue::ArrayI32(vec![-7]),
        LiteralValue::ArrayU64(vec![7]),
        LiteralValue::ArrayI64(vec![-7]),
        LiteralValue::ArrayF32(vec![1.5]),
        LiteralValue::ArrayF64(vec![2.5]),
        LiteralValue::ArrayString(vec![str_sid]),
    ];
    let outer = push_array(&mut file, outer_values);

    let mut module = Module::new();
    let sym = module.sym.intern("ta-elem");
    let c_true = module.consts.push(Const::Bool(true));
    let c7 = module.consts.push(Const::Int32(7));
    let c_neg7 = module.consts.push(Const::Int32((-7_i32) as u32));
    let c_u64 = module.consts.push(Const::UInt64(7));
    let c_i64 = module.consts.push(Const::Int64(-7));
    let c_f32 = module.consts.push(Const::float32(1.5));
    let c_f64 = module.consts.push(Const::number(2.5));
    let c_str = module.consts.push(Const::String(sym));
    let plain_inner = module.consts.push_array(vec![c7]);
    let buf_ref = module.consts.push(Const::LiteralBufferRef(plain_inner));
    let children = vec![
        buf_ref,
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U1,
            items: vec![c_true],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U8,
            items: vec![c7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I8,
            items: vec![c_neg7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U16,
            items: vec![c7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I16,
            items: vec![c_neg7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U32,
            items: vec![c7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I32,
            items: vec![c_neg7],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::U64,
            items: vec![c_u64],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::I64,
            items: vec![c_i64],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::F32,
            items: vec![c_f32],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::F64,
            items: vec![c_f64],
        }),
        module.consts.push(Const::TypedArrayLiteral {
            tag: TypedArrayTag::String,
            items: vec![c_str],
        }),
    ];
    let shape = module.consts.push_array(children);
    let body = resolve_shape(&file, &module, shape)
        .expect("every typed-array and buffer-ref payload resolves tag-exactly");
    assert_eq!(resolved_lit_idx(&body), outer);
}

#[test]
fn literal_dedup_rejects_non_array_trees_and_oob_nested_indices() {
    let (mut file, _) = build_input_file();
    let mut module = Module::new();
    let null_shape = module.consts.push(Const::Null);
    assert!(matches!(
        resolve_shape(&file, &module, null_shape),
        Err(LowerError::UntraceableEntity {
            kind: EntityKind::LiteralarrayId,
            ..
        })
    ));

    push_array(
        &mut file,
        vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(999))],
    );
    let mut module = Module::new();
    let c0 = module.consts.push(Const::Int32(0));
    let inner = module.consts.push_array(vec![c0]);
    let buf_ref = module.consts.push(Const::LiteralBufferRef(inner));
    let shape = module.consts.push_array(vec![buf_ref]);
    assert!(matches!(
        resolve_shape(&file, &module, shape),
        Err(LowerError::UntraceableEntity {
            kind: EntityKind::LiteralarrayId,
            ..
        })
    ));
}

#[test]
fn symbols_above_65536_compact_and_roundtrip_across_all_body_builders() {
    use abcd_file::{SourceLang, Version};
    use abcd_ir::Modifiers;
    use abcd_lower::{LowerOptions, lower_module, rewrite_file};

    const TARGET_STR: &str = "high_sym_str_65590";
    const TARGET_PROP: &str = "high_sym_prop_65591";

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
    let fn_idx = method_idx_by_name(&base_file, "high_sym_fn");

    let mut module = Module::new();
    let global_desc = module.sym.intern("L_GLOBAL;");
    let mut cls_data = abcd_ir::ClassData::new(global_desc, global_desc);
    cls_data.modifiers = Modifiers::PUBLIC;
    module.classes.push(cls_data);

    let func = V2Builder::create_function(&mut module, "high_sym_fn", FunctionKind::Function);
    module.functions[func.index()].modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);

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
    assert!(
        lowered
            .bytecodes
            .iter()
            .flat_map(|bc| bc.entity_operands())
            .any(|(_, id)| id.0 > u32::from(u16::MAX))
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
            .map(|(k, id)| match body.entities[&(k, id.0)] {
                EntityRef::String { id: sid, .. } => {
                    decoded.strings.resolve(sid).expect("resolved string")
                }
                other => panic!("expected EntityRef::String, got {other:?}"),
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
    assert_eq!(body.entities.len(), 2);
    let spliced = splice_body(&base_file, fn_idx, &body);
    let enc1 = abcd_file::encode(&spliced).expect("abcd_file::encode after to_method_body");
    let dec1 = abcd_file::decode(&enc1).expect("decode after to_method_body");
    assert_decoded_strings(&dec1, &[TARGET_STR, TARGET_PROP]);

    // Append synthesized string (`sym_synth`, absent from `base_file`).
    {
        let entry = module.functions[func.index()].blocks[0];
        let _ = module.blocks[entry.index()].insts.pop().unwrap();
        let mut b = V2Builder::new(&mut module, func);
        let synth_cid = b.konst(Const::String(sym_synth));
        let v_synth = b.emit_val(Op::LoadConst(synth_cid));
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
