//! Module-level reference integrity, class-method bijection, field/annotation/debug
//! table bounds, constant-pool shapes, diagnostic formatting, and Quick Start
//! verification tests.

use super::*;

#[test]
fn verify_module_covers_all_funcs() {
    let mut m = mk_module();
    let f1 = add_func(&mut m);
    let e1 = entry_of(&m, f1);
    emit_void(&mut m, e1, Op::Return { value: None });
    let f2 = add_func(&mut m);
    let e2 = entry_of(&m, f2);
    emit_void(&mut m, e2, Op::Return { value: None });

    let r = verify_module(&m);
    assert!(r.is_ok(), "got: {:?}", r.errors);
}

// ── Module-level reference integrity & class-method bijection ────────────

#[test]
fn class_super_and_interface_out_of_range_are_errors() {
    let (mut m, _f) = minimal_func_module();
    let bogus_super = ClassId::new(99);
    let bogus_iface = ClassId::new(98);
    m.classes[0].super_class = Some(bogus_super);
    m.classes[0].interfaces.push(bogus_iface);
    let r = verify_module(&m);
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_super),
        "ClassOutOfRange(super)",
    );
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_iface),
        "ClassOutOfRange(interface)",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error: class {bogus_iface} is outside the class table")
    );
}

#[test]
fn class_method_out_of_range_is_error() {
    let (mut m, _f) = minimal_func_module();
    let bogus = FuncId::new(99);
    m.classes[0].methods.push(bogus);
    let r = verify_module(&m);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus),
        "FuncOutOfRange(class method)",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error: function {bogus} is outside the function table")
    );
}

#[test]
fn func_class_out_of_range_is_error() {
    let (mut m, _f) = minimal_func_module();
    let name = m.sym.intern("orphan");
    let bogus_class = ClassId::new(99);
    m.functions.push(FunctionData {
        class_id: bogus_class,
        is_external: true, // isolate from MissingBody
        ..FunctionData::new(ClassId::new(0), name, FunctionKind::Function)
    });
    let r = verify_module(&m);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_class),
        "ClassOutOfRange(func.class_id)",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error: class {bogus_class} is outside the class table")
    );
}

/// Const-pool `MethodRef` payloads are checked, including nested inside
/// `ObjectLiteral` and `ArrayLiteral` trees.
#[test]
fn const_method_ref_out_of_range_is_error() {
    let (mut m, _f) = minimal_func_module();
    let bogus_direct = FuncId::new(77);
    let bogus_nested = FuncId::new(78);
    let bogus_in_array = FuncId::new(79);
    m.consts.push(Const::method_ref(bogus_direct));
    let key = m.sym.intern("k");
    let k_cid = m.consts.push(Const::String(key));
    let nested_cid = m.consts.push(Const::method_ref(bogus_nested));
    m.consts.push(Const::ObjectLiteral {
        keys: vec![k_cid],
        values: vec![nested_cid],
    });
    let null_cid = m.consts.push(Const::Null);
    let arr_m_cid = m.consts.push(Const::method_ref(bogus_in_array));
    m.consts
        .push(Const::ArrayLiteral(vec![null_cid, arr_m_cid]));
    let r = verify_module(&m);
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_direct),
        "FuncOutOfRange(direct const)",
    );
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_nested),
        "FuncOutOfRange(nested const)",
    );
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_in_array),
        "FuncOutOfRange(array const)",
    );
}

/// Valid shapes: a class with a super class and interfaces verifies clean.
#[test]
fn valid_super_class_and_interfaces_pass() {
    let (mut m, _f) = minimal_func_module();
    m.classes[0].super_class = Some(ClassId::new(0)); // self
    m.classes[0].interfaces.push(ClassId::new(0));
    let r = verify_module(&m);
    assert!(
        r.is_ok(),
        "valid super/interfaces must pass: {:?}",
        r.errors
    );
}

#[test]
fn detached_inst_value_class_methods_bijection_debug_and_const_shapes_are_checked() {
    use crate::function::{ColumnEntry, DebugData, LineEntry, LocalName, LocalScope};
    use crate::module::Annotation;

    // 1. Detached `ValueDef::Inst` (instruction in arena with `block = entry`,
    //    but unlinked from `entry.insts`) MUST be rejected!
    let (mut m1, f1) = minimal_func_module();
    let e1 = entry_of(&m1, f1);
    let c1 = m1.consts.push(Const::number(42.0));
    let detached_iid = InstId::new(m1.insts.len() as u32);
    let detached_val = ValueId::new(m1.values.len() as u32);
    m1.values.push(Value {
        def: ValueDef::Inst(detached_iid),
        ty: Ty::Any,
    });
    m1.insts.push(Inst {
        op: Op::LoadConst(c1),
        result: Some(detached_val),
        block: e1,
        loc: None,
    });
    m1.block_mut(e1).unwrap().insts.clear();
    emit_void(
        &mut m1,
        e1,
        Op::Return {
            value: Some(detached_val),
        },
    );
    let r1 = verify_func(&m1, f1);
    expect_error(
        &r1,
        |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == detached_val),
        "ForeignValue(detached inst)",
    );

    // 2. ClassData::methods <-> FunctionData::class_id bijection, AnnValue::Field,
    //    ExternalFunctionHasBody, DebugData InstIds, and Const payload shapes.
    let (mut m2, f2) = minimal_func_module();
    let e2 = entry_of(&m2, f2);
    let sym = m2.sym.intern("x");
    m2.classes.push(ClassData::new(sym, sym)); // ClassId(1)

    // Duplicate method + owner mismatch (`f2` has `class_id == ClassId(0)`, also listed in `ClassId(1)`).
    m2.classes[1].methods.push(f2);

    // Unlisted method (`f_unlisted` has `class_id == ClassId(1)`, not in `classes[1].methods`)
    // AND is external with non-empty blocks (`ExternalFunctionHasBody`).
    let f_unlisted = FuncId::new(m2.functions.len() as u32);
    let b_ext = BlockId::new(m2.blocks.len() as u32);
    m2.blocks.push(Block::default());
    emit_void(&mut m2, b_ext, Op::Return { value: None });
    let mut ext_fd = FunctionData::new(ClassId::new(1), sym, FunctionKind::Function);
    ext_fd.is_external = true;
    ext_fd.blocks.push(b_ext);
    m2.functions.push(ext_fd);

    // AnnValue::Field out of range on `ClassId(0)` (`0` fields).
    m2.classes[0].annotations.push(Annotation {
        class: ClassId::new(0),
        elements: vec![(sym, AnnValue::Field(ClassId::new(0), FieldId::new(3)))],
    });

    // DebugData referencing an instruction of `f_unlisted` (foreign to `f2`) + out-of-arena InstId.
    let foreign_iid = m2.block(b_ext).unwrap().insts[0];
    m2.func_mut(f2).unwrap().debug = Some(DebugData {
        line_table: vec![LineEntry {
            inst: foreign_iid,
            line: 1,
        }],
        column_table: vec![ColumnEntry {
            inst: InstId::new(9999),
            column: 1,
        }],
        local_names: vec![LocalName {
            name: sym,
            ty: None,
            scope: Some(LocalScope {
                start: foreign_iid,
                end: foreign_iid,
            }),
        }],
        ..DebugData::default()
    });

    // InvalidConstShape: LiteralBufferRef pointing to scalar + AllocObject pointing to scalar + LoadConst of ArrayLiteral.
    let c_scalar = m2.consts.push(Const::Null);
    let c_bad_bref = m2.consts.push(Const::LiteralBufferRef(c_scalar));
    let c_arr = m2.consts.push_array(vec![c_scalar]);
    m2.block_mut(e2).unwrap().insts.clear();
    let _ = emit(&mut m2, e2, Op::AllocObject { shape: c_scalar });
    let _ = emit(&mut m2, e2, Op::LoadConst(c_arr));
    emit_void(&mut m2, e2, Op::Return { value: None });

    let r2 = verify_module(&m2);
    expect_error(
        &r2,
        |k| matches!(k, VerifyErrorKind::DuplicateClassMethod(id) if *id == f2),
        "DuplicateClassMethod",
    );
    expect_error(
        &r2,
        |k| {
            matches!(
                k,
                VerifyErrorKind::ClassMethodOwnerMismatch {
                    class,
                    func,
                    actual_class,
                } if *class == ClassId::new(1) && *func == f2 && *actual_class == ClassId::new(0)
            )
        },
        "ClassMethodOwnerMismatch",
    );
    expect_error(
        &r2,
        |k| {
            matches!(
                k,
                VerifyErrorKind::UnlistedClassMethod { class, func }
                    if *class == ClassId::new(1) && *func == f_unlisted
            )
        },
        "UnlistedClassMethod",
    );
    expect_error(
        &r2,
        |k| matches!(k, VerifyErrorKind::ExternalFunctionHasBody),
        "ExternalFunctionHasBody",
    );
    expect_error(
        &r2,
        |k| {
            matches!(
                k,
                VerifyErrorKind::FieldOutOfRange { class, field }
                    if *class == ClassId::new(0) && *field == FieldId::new(3)
            )
        },
        "FieldOutOfRange",
    );
    assert!(has_error(&r2, |k| {
        matches!(k, VerifyErrorKind::DebugInstNotInFunc(id) if *id == foreign_iid)
    }));
    assert!(has_error(&r2, |k| {
        matches!(k, VerifyErrorKind::InstOutOfArena(id) if *id == InstId::new(9999))
    }));
    expect_error(
        &r2,
        |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_bad_bref),
        "InvalidConstShape(LiteralBufferRef)",
    );
    expect_error(
        &r2,
        |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_scalar),
        "InvalidConstShape(AllocObject)",
    );
    expect_error(
        &r2,
        |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_arr),
        "InvalidConstShape(LoadConst)",
    );
}

// ── Diagnostic Display + Error::source() & Quick Start smoke ─────────────

#[test]
fn error_and_warning_display_cover_all_location_combos() {
    let kind = || VerifyErrorKind::MissingTerminator;
    let combos = [
        (
            None,
            None,
            None,
            "verify error: block does not end with a terminator",
        ),
        (
            Some(FuncId::new(1)),
            None,
            None,
            "verify error in FuncId(1): block does not end with a terminator",
        ),
        (
            Some(FuncId::new(1)),
            Some(BlockId::new(2)),
            None,
            "verify error in FuncId(1) BlockId(2): block does not end with a terminator",
        ),
        (
            Some(FuncId::new(1)),
            Some(BlockId::new(2)),
            Some(InstId::new(3)),
            "verify error in FuncId(1) BlockId(2) InstId(3): block does not end with a terminator",
        ),
    ];
    for (func, block, inst, want) in combos {
        let e = VerifyError {
            func,
            block,
            inst,
            kind: kind(),
        };
        assert_eq!(format!("{e}"), want);
        assert_eq!(
            format!("{}", std::error::Error::source(&e).unwrap()),
            "block does not end with a terminator"
        );
    }

    let w_combos = [
        (
            None,
            None,
            None,
            "verify warning: handler phi joins 2 distinct values across exceptional edges — imprecise join; passes must NOT constant-fold it (N38)",
        ),
        (
            Some(FuncId::new(1)),
            Some(BlockId::new(4)),
            Some(InstId::new(5)),
            "verify warning in FuncId(1) BlockId(4) InstId(5): handler phi joins 2 distinct values across exceptional edges — imprecise join; passes must NOT constant-fold it (N38)",
        ),
    ];
    for (func, block, inst, want) in w_combos {
        let w = VerifyWarning {
            func,
            block,
            inst,
            kind: VerifyWarningKind::HandlerPhiImpreciseJoin {
                handler: BlockId::new(4),
                count: 2,
            },
        };
        assert_eq!(format!("{w}"), want);
        assert!(std::error::Error::source(&w).is_some());
    }
}

#[test]
fn readme_quick_start_module_verifies_clean() {
    let mut module = Module::new();
    let desc = module.sym.intern("L_GLOBAL;");
    module.classes.push(ClassData::new(desc, desc));

    let fname = module.sym.intern("add");
    let entry = BlockId::new(0);
    module.blocks.push(Block::default());

    let mut func = FunctionData::new(ClassId::new(0), fname, FunctionKind::Function);
    func.blocks.push(entry);
    for idx in 0..5u16 {
        let vid = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        func.params.push(vid);
    }
    let (a, b) = (func.params[3], func.params[4]);
    module.functions.push(func);
    module.classes[0].methods.push(FuncId::new(0));

    let sum_inst = InstId::new(0);
    let sum_val = ValueId::new(module.values.len() as u32);
    module.values.push(Value {
        def: ValueDef::Inst(sum_inst),
        ty: Ty::Any,
    });
    module.insts.push(Inst {
        op: Op::BinaryOp {
            op: BinOp::Add,
            left: a,
            right: b,
        },
        result: Some(sum_val),
        block: entry,
        loc: None,
    });
    let ret_inst = InstId::new(1);
    module.insts.push(Inst {
        op: Op::Return {
            value: Some(sum_val),
        },
        result: None,
        block: entry,
        loc: None,
    });
    module.blocks[entry.index()]
        .insts
        .extend([sum_inst, ret_inst]);

    assert!(verify_module(&module).is_ok());
}
