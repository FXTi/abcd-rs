//! Unit tests for [`crate::remap`]: iterative `Const`/`Ty`/`Signature`/`Op`
//! ID visitors, [`FragmentRemapper`] arena shifting, and structural module
//! equivalence ([`modules_structurally_eq`]).

use std::sync::Arc;

use super::*;
use crate::consts::{LitMethodKind, TypedArrayTag};
use crate::function::{EdgeKind, Loc};
use crate::module::{Dialect, FunctionKind, Modifiers, SourceLang};
use crate::op::{BinOp, DefineClassData};
use crate::ty::DynPrim;
use crate::verify::verify_module;

// ── Iterative ID visitors ────────────────────────────────────────────────

#[test]
fn const_ty_signature_and_op_visitors_visit_and_mutate_in_order() {
    // 1. Const visitors (`Sym`, `ConstId`, `FuncId`).
    let mut c_str = Const::String(Sym::new(2));
    c_str.for_each_sym_mut(|s| *s = Sym::new(s.raw() + 10));
    assert_eq!(c_str, Const::String(Sym::new(12)));

    let mut c_obj = Const::ObjectLiteral {
        keys: vec![ConstId::new(1), ConstId::new(2)],
        values: vec![ConstId::new(3), ConstId::new(4)],
    };
    let mut seen_cids = Vec::new();
    c_obj.for_each_const_id(|c| seen_cids.push(c));
    assert_eq!(
        seen_cids,
        vec![
            ConstId::new(1),
            ConstId::new(2),
            ConstId::new(3),
            ConstId::new(4)
        ]
    );
    c_obj.for_each_const_id_mut(|c| *c = ConstId::new(c.raw() + 100));
    assert_eq!(
        c_obj,
        Const::ObjectLiteral {
            keys: vec![ConstId::new(101), ConstId::new(102)],
            values: vec![ConstId::new(103), ConstId::new(104)],
        }
    );

    let mut c_mref = Const::method_ref_with_kind(FuncId::new(5), LitMethodKind::Getter);
    c_mref.for_each_func_id_mut(|f| *f = FuncId::new(f.raw() + 20));
    assert_eq!(
        c_mref,
        Const::method_ref_with_kind(FuncId::new(25), LitMethodKind::Getter)
    );

    let mut c_ta = Const::TypedArrayLiteral {
        tag: TypedArrayTag::U32,
        items: vec![ConstId::new(7)],
    };
    c_ta.for_each_const_id_mut(|c| *c = ConstId::new(c.raw() + 1));
    assert_eq!(
        c_ta,
        Const::TypedArrayLiteral {
            tag: TypedArrayTag::U32,
            items: vec![ConstId::new(8)],
        }
    );

    // 2. Deep nested `Ty::Union` & `Signature` iterative `ClassId` remapping (zero recursion).
    let mut deep_ty = Ty::Static(StaticTy::Reference(ClassId::new(0)));
    for step in 1..=256u32 {
        deep_ty = Ty::Union(Box::new([
            deep_ty,
            Ty::Static(StaticTy::Reference(ClassId::new(step))),
        ]));
    }
    let mut before_classes = Vec::new();
    deep_ty.for_each_class_id(|c| before_classes.push(c.raw()));
    assert_eq!(before_classes.len(), 257);
    assert_eq!(before_classes[0], 0);
    assert_eq!(before_classes[256], 256);

    let mut sig = Signature {
        return_ty: Some(deep_ty),
        param_tys: vec![
            Ty::DynPrim(DynPrim::Number),
            Ty::Static(StaticTy::Reference(ClassId::new(900))),
        ],
    };
    sig.for_each_class_id_mut(|c| *c = ClassId::new(c.raw() + 1000));
    let mut after_classes = Vec::new();
    sig.for_each_class_id(|c| after_classes.push(c.raw()));
    assert_eq!(after_classes.len(), 258);
    assert_eq!(after_classes[0], 1000);
    assert_eq!(after_classes[256], 1256);
    assert_eq!(after_classes[257], 1900);
}

// ── FragmentRemapper & arena shifting ────────────────────────────────────

fn build_rich_module() -> Module {
    let mut m = Module::new();
    let g_desc = m.sym.intern("L_GLOBAL;");
    let g_name = m.sym.intern("_GLOBAL");
    let lone_sym = m.sym.intern_raw_mutf8(&[0xED, 0xA0, 0xB4]);
    let fn_name = m.sym.intern("entry");
    let sf_sym = m.sym.intern("entry.ts");
    let spec_sym = m.sym.intern("./dep");
    let loc_sym = m.sym.intern("x");
    let prop_sym = m.sym.intern("prop");

    let c_num = m.consts.intern(Const::number(-0.0));
    let c_str = m.consts.intern(Const::String(lone_sym));
    let c_arr = m.consts.push_array(vec![c_num, c_str]);

    let mut cls = ClassData::new(g_desc, g_name);
    cls.modifiers = Modifiers::PUBLIC;
    cls.source_lang = SourceLang::TypeScript;
    cls.source_file = Some(sf_sym);
    cls.scope_names = Some(c_arr);
    cls.fields.push(FieldData {
        name: prop_sym,
        ty: Ty::Static(StaticTy::Reference(ClassId::new(0))),
        modifiers: Modifiers::PUBLIC,
        initial_value: Some(c_num),
        annotations: vec![Annotation {
            class: ClassId::new(0),
            elements: vec![
                (prop_sym, AnnValue::Const(c_str)),
                (loc_sym, AnnValue::Field(ClassId::new(0), FieldId::new(0))),
            ],
        }],
    });
    cls.es_module = Some(EsModule {
        imports: vec![ImportDecl::Regular {
            local_name: loc_sym,
            import_name: prop_sym,
            module_request: spec_sym,
        }],
        exports: vec![ExportDecl::Local {
            local_name: loc_sym,
            export_name: prop_sym,
        }],
        module_requests: vec![ModuleRequest {
            specifier: spec_sym,
            lazy: true,
        }],
    });
    m.classes.push(cls);

    m.imports.push(ImportDecl::Namespace {
        local_name: loc_sym,
        module_request: spec_sym,
    });
    m.exports.push(ExportDecl::Star {
        module_request: spec_sym,
    });
    m.module_requests.push(ModuleRequest {
        specifier: spec_sym,
        lazy: false,
    });

    let b0 = BlockId::new(0);
    let b1 = BlockId::new(1);
    m.blocks.push(Block::default());
    m.blocks.push(Block {
        insts: Vec::new(),
        preds: vec![Edge {
            from: b0,
            kind: EdgeKind::Exceptional,
        }],
    });

    let mut fd = FunctionData::new(ClassId::new(0), fn_name, FunctionKind::Function);
    fd.sig = Some(Signature {
        return_ty: Some(Ty::Static(StaticTy::Reference(ClassId::new(0)))),
        param_tys: vec![Ty::Any],
    });
    for idx in 0..3u16 {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        fd.params.push(vid);
    }
    let fic_vid = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(c_num),
        ty: Ty::DynPrim(DynPrim::Number),
    });
    fd.frame_init_consts.push(fic_vid);

    let exc_vid = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(b1),
        ty: Ty::Any,
    });
    fd.blocks.extend([b0, b1]);
    fd.try_regions.push(TryRegion {
        protected: vec![b0],
        catches: vec![Catch {
            handler: b1,
            exception: exc_vid,
            type_class: Some(ClassId::new(0)),
        }],
    });

    let add_iid = InstId::new(0);
    let add_vid = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(add_iid),
        ty: Ty::Any,
    });
    m.insts.push(Inst {
        op: Op::BinaryOp {
            op: BinOp::Add,
            left: fd.params[0],
            right: fic_vid,
        },
        result: Some(add_vid),
        block: b0,
        loc: Some(Loc {
            line: 10,
            column: Some(4),
        }),
    });
    let ret0_iid = InstId::new(1);
    m.insts.push(Inst {
        op: Op::Return {
            value: Some(add_vid),
        },
        result: None,
        block: b0,
        loc: None,
    });
    let ret1_iid = InstId::new(2);
    m.insts.push(Inst {
        op: Op::Return {
            value: Some(exc_vid),
        },
        result: None,
        block: b1,
        loc: None,
    });
    m.blocks[0].insts.extend([add_iid, ret0_iid]);
    m.blocks[1].insts.push(ret1_iid);

    fd.debug = Some(DebugData {
        source_file: Some(sf_sym),
        source_code: Some(Arc::from("export let x = 1;")),
        line_table: vec![LineEntry {
            inst: add_iid,
            line: 10,
        }],
        column_table: vec![ColumnEntry {
            inst: add_iid,
            column: 4,
        }],
        local_names: vec![LocalName {
            name: loc_sym,
            ty: Some(Ty::Static(StaticTy::Reference(ClassId::new(0)))),
            scope: Some(LocalScope {
                start: add_iid,
                end: ret0_iid,
            }),
        }],
        param_names: vec![loc_sym],
        scope_names: Some(c_arr),
    });
    fd.annotations.push(Annotation {
        class: ClassId::new(0),
        elements: vec![(prop_sym, AnnValue::Name(fn_name))],
    });

    let fid = FuncId::new(0);
    m.functions.push(fd);
    m.classes[0].methods.push(fid);
    assert!(verify_module(&m).is_ok());
    m
}

#[test]
fn fragment_remapper_shifts_function_arenas_and_verifies() {
    let base = build_rich_module();

    // Build a destination module pre-populated with dummy prefix entries in every
    // arena so every ID space (`Sym`, `ConstId`, `BlockId`, `InstId`, `ValueId`) shifts!
    let mut dst = Module::new();
    let _pad_sym0 = dst.sym.intern("__pad_sym_0");
    let _pad_sym1 = dst.sym.intern("__pad_sym_1");
    let mut sym_map = Vec::with_capacity(base.sym.len());
    for i in 0..base.sym.len() {
        let sid = Sym::new(i as u32);
        let mapped = if let Some(raw) = base.sym.raw_mutf8(sid) {
            dst.sym.intern_raw_mutf8(raw)
        } else {
            dst.sym.intern(base.sym.resolve(sid).unwrap())
        };
        sym_map.push(mapped);
    }

    let _pad_const = dst.consts.push(Const::Undefined);
    let const_off = dst.consts.len() as u32;
    let mut const_map: Vec<ConstId> = (0..base.consts.len())
        .map(|i| ConstId::new(i as u32 + const_off))
        .collect();
    for i in 0..base.consts.len() {
        let mut c = base.consts.get(ConstId::new(i as u32)).unwrap().clone();
        let mut cr = FragmentRemapper {
            sym_map: Some(&sym_map),
            const_map: Some(&const_map),
            ..FragmentRemapper::default()
        };
        c.remap_ids(&mut cr);
        let actual = dst.consts.push(c);
        const_map[i] = actual;
    }

    // `verify_module` allows unreferenced arena entries, so shifting offsets
    // tests that every `FunctionData`, `Block`, `Inst`, `Value`, `DebugData`, and
    // `TryRegion` reference moves in lockstep!
    dst.blocks.push(Block::default());
    dst.insts.push(Inst {
        op: Op::Unreachable,
        result: None,
        block: BlockId::new(0),
        loc: None,
    });
    dst.values.push(Value {
        def: ValueDef::Param(0),
        ty: Ty::Any,
    });
    dst.values.push(Value {
        def: ValueDef::Param(1),
        ty: Ty::Any,
    });

    let mut remapper = FragmentRemapper {
        sym_map: Some(&sym_map),
        const_map: Some(&const_map),
        class_map: None,
        func_map: None,
        block_offset: dst.blocks.len() as u32,
        inst_offset: dst.insts.len() as u32,
        value_offset: dst.values.len() as u32,
    };

    let mut cloned_cls = base.classes[0].clone();
    cloned_cls.remap_ids(&mut remapper);
    dst.classes.push(cloned_cls);

    let mut cloned_fn = base.functions[0].clone();
    cloned_fn.remap_ids(&mut remapper);
    dst.functions.push(cloned_fn);

    for b in &base.blocks {
        let mut nb = b.clone();
        nb.remap_ids(&mut remapper);
        dst.blocks.push(nb);
    }
    for inst in &base.insts {
        let mut ni = inst.clone();
        ni.remap_ids(&mut remapper);
        dst.insts.push(ni);
    }
    for val in &base.values {
        let mut nv = val.clone();
        nv.remap_ids(&mut remapper);
        dst.values.push(nv);
    }

    // Also test `DefineClass` op remapping (`FuncId`, `ConstId`, `ValueId`).
    let mut dc_op = Op::DefineClass(Box::new(DefineClassData {
        ctor: FuncId::new(0),
        heritage: Some(ValueId::new(0)),
        members: ConstId::new(2),
        member_attrs: Vec::new(),
        count: 1,
    }));
    dc_op.remap_ids(&mut remapper);
    assert_eq!(
        dc_op,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: FuncId::new(0),
            heritage: Some(ValueId::new(2)),
            members: const_map[2],
            member_attrs: Vec::new(),
            count: 1,
        }))
    );

    let report = verify_module(&dst);
    assert!(
        report.is_ok(),
        "remapped module must verify: {:?}",
        report.errors
    );
}

// ── Structural module equivalence ────────────────────────────────────────

#[test]
fn modules_structurally_eq_accepts_identical_and_pinpoints_mismatches() {
    let a = build_rich_module();
    let mut b = a.clone();
    // Dropping hash indices must NOT affect structural equivalence!
    b.sym.drop_index();
    b.consts.drop_index();
    assert_eq!(modules_structurally_eq(&a, &b), Ok(()));

    // 1. Dialect mismatch.
    let mut m_dialect = a.clone();
    m_dialect.dialect = Dialect::StaticArkTS;
    assert!(
        modules_structurally_eq(&a, &m_dialect)
            .unwrap_err()
            .contains("dialect mismatch")
    );

    // 2. Lone-surrogate raw MUTF-8 mismatch sharing identical U+FFFD display text!
    let mut m_sym_a = Module::new();
    let _ = m_sym_a.sym.intern_raw_mutf8(&[0xED, 0xA0, 0x81]);
    let mut m_sym_b = Module::new();
    let _ = m_sym_b.sym.intern_raw_mutf8(&[0xED, 0xA0, 0x82]);
    assert!(
        modules_structurally_eq(&m_sym_a, &m_sym_b)
            .unwrap_err()
            .contains("sym[0].raw_mutf8 mismatch")
    );

    // 3. `-0.0` vs `+0.0` IEEE-754 bit mismatch in ConstPool.
    let mut m_const = a.clone();
    m_const.consts = crate::consts::ConstPool::new();
    let _ = m_const.consts.push(Const::number(0.0));
    let _ = m_const
        .consts
        .push(a.consts.get(ConstId::new(1)).unwrap().clone());
    let _ = m_const
        .consts
        .push(a.consts.get(ConstId::new(2)).unwrap().clone());
    assert!(
        modules_structurally_eq(&a, &m_const)
            .unwrap_err()
            .contains("consts[0] mismatch")
    );

    // 4. Bundled `es_module` mismatch.
    let mut m_esm = a.clone();
    m_esm.classes[0].es_module.as_mut().unwrap().module_requests[0].lazy = false;
    assert!(
        modules_structurally_eq(&a, &m_esm)
            .unwrap_err()
            .contains("classes[0].es_module.module_requests[0] mismatch")
    );

    // 5. Function `try_regions` mismatch.
    let mut m_try = a.clone();
    m_try.functions[0].try_regions[0].catches[0].type_class = None;
    assert!(
        modules_structurally_eq(&a, &m_try)
            .unwrap_err()
            .contains("functions[0].try_regions[0].catches[0].type_class mismatch")
    );

    // 6. Instruction op mismatch.
    let mut m_inst = a.clone();
    m_inst.insts[0].op = Op::BinaryOp {
        op: BinOp::Sub,
        left: m_inst.functions[0].params[0],
        right: m_inst.functions[0].frame_init_consts[0],
    };
    assert!(
        modules_structurally_eq(&a, &m_inst)
            .unwrap_err()
            .contains("insts[0].op mismatch")
    );
}
