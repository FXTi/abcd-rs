//! Round 2 regression, soundness, and 256 KiB-stack scale suite (#51, #52, #53, #54).

use std::borrow::Cow;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use abcd_ir::{
    BinOp, Block, BlockId, CallKind, Catch, ClassData, ClassId, CmpOp, Const, ConstId,
    DefineClassData, DomTree, DynPrim, Edge, EdgeKind, ExceptionHandlerMap, FuncId, FunctionData,
    FunctionKind, Inst, InstId, LexEnvKind, LitMethodKind, Module, Op, OwnStoreKind, StaticTy, Sym,
    SymbolTable, TryRegion, Ty, TypedArrayTag, UnOp, Value, ValueDef, ValueId, VerifyErrorKind,
    verify_func, verify_module,
};

fn mk_module() -> Module {
    let mut m = Module::new();
    let desc = m.sym.intern("Ltest;");
    m.classes.push(ClassData::new(desc, desc));
    m
}

fn add_func(m: &mut Module) -> FuncId {
    let name = m.sym.intern("f");
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    m.classes[0].methods.push(id);
    add_block(m, id);
    id
}

fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

fn emit(m: &mut Module, b: BlockId, op: Op, ty: Ty) -> ValueId {
    assert!(op.has_result());
    let inst = InstId::new(m.insts.len() as u32);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty,
    });
    m.insts.push(Inst {
        op,
        result: Some(val),
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(inst);
    val
}

fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    assert!(!op.has_result());
    let inst = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(inst);
    inst
}

fn add_param(m: &mut Module, f: FuncId, idx: u16, ty: Ty) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty,
    });
    m.func_mut(f).unwrap().params.push(val);
    val
}

fn add_exc_param(m: &mut Module, h: BlockId) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(h),
        ty: Ty::Any,
    });
    val
}

fn link(m: &mut Module, from: BlockId, to: BlockId, kind: EdgeKind) {
    m.block_mut(to).unwrap().preds.push(Edge { from, kind });
}

fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId, exc: ValueId) {
    for &p in &protected {
        link(m, p, handler, EdgeKind::Exceptional);
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_class: None,
        }],
    });
}

#[test]
fn op_and_ty_memory_layouts_are_compact() {
    assert!(
        std::mem::size_of::<Op>() <= 40,
        "Op size {} exceeded 40B",
        std::mem::size_of::<Op>()
    );
    // Boxing `DefineClassData` shrinks `Op` from 48B -> 40B and `Inst` from
    // 72B -> 64B (`40B Op + 8B Option<ValueId> + 4B BlockId + 12B Option<Loc>`).
    assert!(
        std::mem::size_of::<Inst>() <= 64,
        "Inst size {} exceeded 64B",
        std::mem::size_of::<Inst>()
    );
    assert_eq!(
        std::mem::size_of::<Box<[Ty]>>(),
        2 * std::mem::size_of::<usize>()
    );
    assert!(std::mem::size_of::<Box<[Ty]>>() < std::mem::size_of::<Vec<Ty>>());
}

#[test]
fn r2_c1_h2_post_throw_def_and_handler_join_soundness() {
    // 1. Post-throw def in protected block T cannot be used in single-pred H or join J.
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = m.func(f).unwrap().blocks[0];
    let callee = add_param(&mut m, f, 0, Ty::Any);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: t });
    link(&mut m, entry, t, EdgeKind::Normal);
    let exc = add_exc_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);

    let c1 = m.consts.push(Const::number(1.0));
    let pre_throw = emit(&mut m, t, Op::LoadConst(c1), Ty::DynPrim(DynPrim::Number));
    let post_throw = emit(
        &mut m,
        t,
        Op::Call {
            callee,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
        Ty::Any,
    );
    emit_void(&mut m, t, Op::Branch { dest: j });
    link(&mut m, t, j, EdgeKind::Normal);

    // `pre_throw` dominates both H and J; `post_throw` dominates NEITHER H nor J!
    let _ok_use = emit(&mut m, h, Op::Mov { src: pre_throw }, Ty::Any);
    let _bad_h = emit(&mut m, h, Op::Mov { src: post_throw }, Ty::Any);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, h, j, EdgeKind::Normal);
    emit_void(
        &mut m,
        j,
        Op::Return {
            value: Some(post_throw),
        },
    );

    let r = verify_func(&m, f);
    let non_dom: Vec<_> = r
        .errors
        .iter()
        .filter(|e| matches!(e.kind, VerifyErrorKind::UseNotDominated { value, .. } if value == post_throw))
        .collect();
    assert_eq!(
        non_dom.len(),
        2,
        "both H and J must reject post_throw: {:?}",
        r.errors
    );
    assert!(
        !r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::UseNotDominated { value, .. } if value == pre_throw)),
        "pre_throw must remain valid in H: {:?}",
        r.errors
    );

    // 2. Handler subgraph diamond: def in H1 used in H_join is rejected.
    let mut m2 = mk_module();
    let f2 = add_func(&mut m2);
    let e2 = m2.func(f2).unwrap().blocks[0];
    let cond = add_param(&mut m2, f2, 0, Ty::Any);
    let h0 = add_block(&mut m2, f2);
    let h1 = add_block(&mut m2, f2);
    let h2 = add_block(&mut m2, f2);
    let hj = add_block(&mut m2, f2);
    let exc2 = add_exc_param(&mut m2, h0);
    add_try(&mut m2, f2, vec![e2], h0, exc2);
    emit_void(&mut m2, e2, Op::Return { value: None });
    emit_void(
        &mut m2,
        h0,
        Op::CondBranch {
            cond,
            true_dest: h1,
            false_dest: h2,
        },
    );
    link(&mut m2, h0, h1, EdgeKind::Normal);
    link(&mut m2, h0, h2, EdgeKind::Normal);
    let c2 = m2.consts.push(Const::number(9.0));
    let h1_val = emit(&mut m2, h1, Op::LoadConst(c2), Ty::Any);
    emit_void(&mut m2, h1, Op::Branch { dest: hj });
    emit_void(&mut m2, h2, Op::Branch { dest: hj });
    link(&mut m2, h1, hj, EdgeKind::Normal);
    link(&mut m2, h2, hj, EdgeKind::Normal);
    emit_void(
        &mut m2,
        hj,
        Op::Return {
            value: Some(h1_val),
        },
    );
    let r2 = verify_func(&m2, f2);
    assert!(
        r2.errors.iter().any(
            |e| matches!(e.kind, VerifyErrorKind::UseNotDominated { value, .. } if value == h1_val)
        ),
        "handler diamond non-dominated use must error: {:?}",
        r2.errors
    );

    // 3. ExceptionParam(h) used in post-try join J (`entry -> J` & `entry ~exc~> h -> J`) is rejected,
    // AND protected `entry` throwing def used in `h` is rejected!
    let mut m3 = mk_module();
    let f3 = add_func(&mut m3);
    let e3 = m3.func(f3).unwrap().blocks[0];
    let p3 = add_param(&mut m3, f3, 0, Ty::Any);
    let h3 = add_block(&mut m3, f3);
    let j3 = add_block(&mut m3, f3);
    let exc3 = add_exc_param(&mut m3, h3);
    add_try(&mut m3, f3, vec![e3], h3, exc3);
    let entry_throw_val = emit(
        &mut m3,
        e3,
        Op::Call {
            callee: p3,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
        Ty::Any,
    );
    emit_void(&mut m3, e3, Op::Branch { dest: j3 });
    link(&mut m3, e3, j3, EdgeKind::Normal);
    let _bad_entry_use = emit(
        &mut m3,
        h3,
        Op::Mov {
            src: entry_throw_val,
        },
        Ty::Any,
    );
    emit_void(&mut m3, h3, Op::Branch { dest: j3 });
    link(&mut m3, h3, j3, EdgeKind::Normal);
    emit_void(&mut m3, j3, Op::Return { value: Some(exc3) });
    let r3 = verify_func(&m3, f3);
    assert!(
        r3.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::UseNotDominated { value, .. } if value == entry_throw_val)),
        "protected entry throwing def must not dominate handler: {:?}",
        r3.errors
    );
    assert!(
        r3.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ExceptionParamOutOfScope { value, .. } if value == exc3)),
        "ExceptionParam must not escape into post-try join: {:?}",
        r3.errors
    );
}

#[test]
fn r2_d2_effects_in_refinement_and_symbol_m9() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let b = m.func(f).unwrap().blocks[0];
    let v_any = add_param(&mut m, f, 0, Ty::Any);
    let v_num = add_param(&mut m, f, 1, Ty::DynPrim(DynPrim::Number));
    let v_str = add_param(&mut m, f, 2, Ty::DynPrim(DynPrim::String));
    let v_big = add_param(&mut m, f, 3, Ty::DynPrim(DynPrim::BigInt));
    let v_i32 = add_param(&mut m, f, 4, Ty::Static(StaticTy::I32));
    let c_nz = m.consts.intern(Const::Int64(5));
    let v_nz = emit(&mut m, b, Op::LoadConst(c_nz), Ty::Static(StaticTy::I32));

    // Untyped Add is effectful; Number+String Add is PURE; Number+BigInt Add stays may_throw.
    assert!(
        Op::BinaryOp {
            op: BinOp::Add,
            left: v_any,
            right: v_num
        }
        .effects_in(&m)
        .may_throw
    );
    assert!(
        Op::BinaryOp {
            op: BinOp::Add,
            left: v_num,
            right: v_str
        }
        .effects_in(&m)
        .is_pure()
    );
    assert!(
        Op::BinaryOp {
            op: BinOp::Add,
            left: v_num,
            right: v_big
        }
        .effects_in(&m)
        .may_throw
    );
    // Relational Compare on BigInt vs Number is PURE in ECMA-262!
    assert!(
        Op::Compare {
            op: CmpOp::Less,
            left: v_big,
            right: v_num
        }
        .effects_in(&m)
        .is_pure()
    );
    // Static integer Div (`N36`: `left` = divisor, `right` = dividend):
    // unknown divisor `may_throw`, proven non-zero non-(-1) const divisor is PURE.
    assert!(
        Op::BinaryOp {
            op: BinOp::Div,
            left: v_i32,
            right: v_nz
        }
        .effects_in(&m)
        .may_throw
    );
    assert!(
        Op::BinaryOp {
            op: BinOp::Div,
            left: v_nz,
            right: v_i32
        }
        .effects_in(&m)
        .is_pure()
    );
    // Unary ToNumber on String is PURE.
    assert!(
        Op::UnaryOp {
            op: UnOp::ToNumber,
            operand: v_str
        }
        .effects_in(&m)
        .is_pure()
    );

    // R2-M9: intern_lossy_raw routes valid MUTF-8/UTF-8 to lossless bucket;
    // to_mutf8_bytes borrows ASCII/BMP slices without allocating.
    let mut sym = SymbolTable::new();
    let s1 = sym.intern("hello");
    let s2 = sym.intern_lossy_raw("hello", b"hello");
    assert_eq!(s1, s2);
    assert_eq!(sym.lossy_count(), 0);
    assert!(matches!(
        sym.to_mutf8_bytes(s1),
        Some(Cow::Borrowed(b"hello"))
    ));
    let nul = sym.intern("a\0b");
    assert!(matches!(sym.to_mutf8_bytes(nul), Some(Cow::Owned(_))));

    // R3-D1: UnOp::ToPropertyKey refines to PURE on String/Symbol/Number/Bool, stays effectful on Any.
    let v_sym = add_param(&mut m, f, 5, Ty::DynPrim(DynPrim::Symbol));
    assert!(
        Op::UnaryOp {
            op: UnOp::ToPropertyKey,
            operand: v_sym,
        }
        .effects_in(&m)
        .is_pure()
    );
    assert!(
        Op::UnaryOp {
            op: UnOp::ToPropertyKey,
            operand: v_any,
        }
        .effects_in(&m)
        .may_throw
    );

    // #61 R3-X1: raw jeqz/jnez unary predicates are boolean-valued and unconditionally PURE.
    for op in [UnOp::JumpEqz, UnOp::JumpNez] {
        assert!(op.is_boolean_result());
        let u = Op::UnaryOp { op, operand: v_any };
        assert_eq!(u.effects(), abcd_ir::Effects::PURE);
        assert_eq!(u.effects_in(&m), abcd_ir::Effects::PURE);
    }
    assert!(UnOp::LogicalNot.is_boolean_result());
    assert!(UnOp::IsTrue.is_boolean_result());
    assert!(UnOp::IsFalse.is_boolean_result());
    assert!(!UnOp::Minus.is_boolean_result());
    assert!(!UnOp::ToPropertyKey.is_boolean_result());
}

#[test]
fn r3_stage1_call_lex_ownstore_and_const_verifier_checks() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let b = m.func(f).unwrap().blocks[0];
    let p0 = add_param(&mut m, f, 0, Ty::Any);
    let h = add_block(&mut m, f);
    let exc = add_exc_param(&mut m, h);
    link(&mut m, b, h, EdgeKind::Exceptional);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b],
        catches: vec![Catch {
            handler: h,
            exception: exc,
            type_class: Some(ClassId::new(404)),
        }],
    });
    emit_void(&mut m, h, Op::Return { value: None });

    // InvalidCallShape for NewSpread (with `this`), SuperArrow (with `this`), ClassInit (with arg).
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: Some(p0),
            args: vec![p0],
            kind: CallKind::NewSpread,
        },
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: Some(p0),
            args: vec![],
            kind: CallKind::SuperArrow,
        },
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: Some(p0),
            args: vec![p0],
            kind: CallKind::ClassInit,
        },
        Ty::Any,
    );

    // InvalidOpModifier for NewLexEnv(Patch), GetLexVar(Patch, level=1), StoreOwnPropDyn(DefineProperty), StoreOwnPropIdx(OwnPropWithNameSet).
    let _ = emit(
        &mut m,
        b,
        Op::NewLexEnv {
            num_vars: 1,
            kind: LexEnvKind::Patch,
        },
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 1,
            slot: 0,
            kind: LexEnvKind::Patch,
        },
        Ty::Any,
    );
    emit_void(
        &mut m,
        b,
        Op::StoreOwnPropDyn {
            object: p0,
            key: p0,
            value: p0,
            kind: OwnStoreKind::DefineProperty,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StoreOwnPropIdx {
            object: p0,
            index: p0,
            value: p0,
            kind: OwnStoreKind::OwnPropWithNameSet,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    // Const checks: EtsImplements(SymOutOfRange), MethodRef { func, kind } (FuncOutOfRange),
    // TypedArrayLiteral -> LiteralBufferRef cycle (`ConstCycle`).
    m.consts.push(Const::EtsImplements(Sym::new(555)));
    m.consts.push(Const::method_ref_with_kind(
        FuncId::new(666),
        LitMethodKind::Setter,
    ));
    let cyc_a = ConstId::new(m.consts.len() as u32);
    let cyc_b = ConstId::new(m.consts.len() as u32 + 1);
    m.consts.push(Const::TypedArrayLiteral {
        tag: TypedArrayTag::I32,
        items: vec![cyc_b],
    });
    m.consts.push(Const::LiteralBufferRef(cyc_a));

    let r = verify_module(&m);
    assert!(
        r.errors.iter().any(
            |e| matches!(e.kind, VerifyErrorKind::ClassOutOfRange(c) if c == ClassId::new(404))
        )
    );
    for want in [
        CallKind::NewSpread,
        CallKind::SuperArrow,
        CallKind::ClassInit,
    ] {
        assert!(
            r.errors.iter().any(
                |e| matches!(e.kind, VerifyErrorKind::InvalidCallShape { kind } if kind == want)
            ),
            "missing InvalidCallShape for {want:?}: {:?}",
            r.errors
        );
    }
    let mod_errs = r
        .errors
        .iter()
        .filter(|e| matches!(e.kind, VerifyErrorKind::InvalidOpModifier { .. }))
        .count();
    assert_eq!(
        mod_errs, 4,
        "expected 4 InvalidOpModifier errors, got: {:?}",
        r.errors
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::SymOutOfRange(s) if s == Sym::new(555)))
    );
    assert!(
        r.errors.iter().any(
            |e| matches!(e.kind, VerifyErrorKind::FuncOutOfRange(id) if id == FuncId::new(666))
        )
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ConstCycle(c) if c == cyc_a))
    );
}

#[test]
fn r2_h5_structural_negative_checks() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let b = m.func(f).unwrap().blocks[0];
    let p0 = add_param(&mut m, f, 0, Ty::Any);

    // Dynamic call with explicit receiver (`callthis*`) is valid; Apply with `this: None`
    // and SuperSpread with `this: Some` trigger InvalidCallShape.
    let ok_dyn_this = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: Some(p0),
            args: vec![],
            kind: CallKind::Dynamic,
        },
        Ty::Any,
    );
    let bad_call = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: None,
            args: vec![ok_dyn_this],
            kind: CallKind::Apply,
        },
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::Call {
            callee: p0,
            this: Some(p0),
            args: vec![ok_dyn_this],
            kind: CallKind::SuperSpread,
        },
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::DefineClass(Box::new(DefineClassData {
            ctor: FuncId::new(777),
            heritage: Some(bad_call),
            members: ConstId::new(888),
            member_attrs: vec![],
            count: 0,
        })),
        Ty::Any,
    );
    let _ = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: p0,
            name: Sym::new(999),
        },
        Ty::Any,
    );

    // ResultPresenceMismatch + DuplicateInst: void Return given `result: Some`, listed twice.
    let ret = emit_void(&mut m, b, Op::Return { value: None });
    let extra_val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(ret),
        ty: Ty::Any,
    });
    m.inst_mut(ret).unwrap().result = Some(extra_val);
    m.block_mut(b).unwrap().insts.push(ret);

    // ObjectLiteralArityMismatch + ConstCycle (`c_cyc0 -> c_cyc1 -> c_cyc0`).
    let c_k = m.consts.push(Const::Null);
    m.consts.push_object(vec![c_k], vec![]);
    let next_cid = ConstId::new(m.consts.len() as u32);
    let next_cid_2 = ConstId::new(m.consts.len() as u32 + 1);
    m.consts.push_array(vec![next_cid_2]);
    m.consts.push_array(vec![next_cid]);

    let r = verify_module(&m);
    assert!(!r.errors.iter().any(|e| matches!(
        e.kind,
        VerifyErrorKind::InvalidCallShape {
            kind: CallKind::Dynamic
        }
    )));
    assert!(r.errors.iter().any(|e| matches!(
        e.kind,
        VerifyErrorKind::InvalidCallShape {
            kind: CallKind::Apply
        }
    )));
    assert!(r.errors.iter().any(|e| matches!(
        e.kind,
        VerifyErrorKind::InvalidCallShape {
            kind: CallKind::SuperSpread
        }
    )));
    assert!(
        r.errors.iter().any(
            |e| matches!(e.kind, VerifyErrorKind::FuncOutOfRange(id) if id == FuncId::new(777))
        )
    );
    assert!(r.errors.iter().any(
        |e| matches!(e.kind, VerifyErrorKind::ConstOutOfRange(id) if id == ConstId::new(888))
    ));
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::SymOutOfRange(id) if id == Sym::new(999)))
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ResultPresenceMismatch { .. }))
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::DuplicateInst(id) if id == ret))
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ObjectLiteralArityMismatch { .. }))
    );
    assert!(
        r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ConstCycle(_)))
    );
}

#[test]
fn scale_256kib_stack_cfg_const_and_ty_chains() {
    let handle = std::thread::Builder::new()
        .name("round2-256k".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            // 1. 10,000-block linear & reverse-numbered chain through DomTree + verify_func.
            let mut m = mk_module();
            let f = add_func(&mut m);
            let entry = m.func(f).unwrap().blocks[0];
            let n = 10_000usize;
            let mut blocks = Vec::with_capacity(n);
            blocks.push(entry);
            for _ in 1..n {
                blocks.push(add_block(&mut m, f));
            }
            // Reverse arena listing order for blocks[1..] to stress RPO + CHK intersect!
            m.func_mut(f).unwrap().blocks[1..].reverse();
            let ordered: Vec<BlockId> = blocks;
            let c0 = m.consts.intern(Const::number(1.0));
            let v0 = emit(
                &mut m,
                ordered[0],
                Op::LoadConst(c0),
                Ty::DynPrim(DynPrim::Number),
            );
            for i in 0..(n - 1) {
                emit_void(
                    &mut m,
                    ordered[i],
                    Op::Branch {
                        dest: ordered[i + 1],
                    },
                );
                link(&mut m, ordered[i], ordered[i + 1], EdgeKind::Normal);
            }
            emit_void(&mut m, ordered[n - 1], Op::Return { value: Some(v0) });

            let dt = DomTree::compute_normal(&m, f).unwrap();
            assert_eq!(dt.rpo().len(), n);
            assert!(dt.dominates(ordered[0], ordered[n - 1]));
            assert_eq!(dt.idom(ordered[n - 1]), Some(ordered[n - 2]));
            let r = verify_func(&m, f);
            assert!(r.is_ok(), "10k chain verify errors: {:?}", r.errors);

            // 2. Catch handler with 2,000 protected predecessors and 16 phis.
            let mut mh = mk_module();
            let fh = add_func(&mut mh);
            let eh = mh.func(fh).unwrap().blocks[0];
            let p_count = 2_000usize;
            let mut p_blocks = Vec::with_capacity(p_count);
            p_blocks.push(eh);
            for _ in 1..p_count {
                p_blocks.push(add_block(&mut mh, fh));
            }
            let handler = add_block(&mut mh, fh);
            let c_init = mh.consts.intern(Const::number(0.0));
            let v_init = emit(
                &mut mh,
                eh,
                Op::LoadConst(c_init),
                Ty::DynPrim(DynPrim::Number),
            );
            for i in 0..(p_count - 1) {
                emit_void(
                    &mut mh,
                    p_blocks[i],
                    Op::Branch {
                        dest: p_blocks[i + 1],
                    },
                );
                link(&mut mh, p_blocks[i], p_blocks[i + 1], EdgeKind::Normal);
            }
            emit_void(
                &mut mh,
                p_blocks[p_count - 1],
                Op::Return {
                    value: Some(v_init),
                },
            );
            let exc = add_exc_param(&mut mh, handler);
            add_try(&mut mh, fh, p_blocks.clone(), handler, exc);
            let phi_entries: Vec<(Edge, ValueId)> = p_blocks
                .iter()
                .map(|&pb| {
                    (
                        Edge {
                            from: pb,
                            kind: EdgeKind::Exceptional,
                        },
                        v_init,
                    )
                })
                .collect();
            let mut last_phi = v_init;
            for _ in 0..16 {
                last_phi = emit(
                    &mut mh,
                    handler,
                    Op::Phi {
                        entries: phi_entries.clone(),
                    },
                    Ty::Any,
                );
            }
            emit_void(
                &mut mh,
                handler,
                Op::Return {
                    value: Some(last_phi),
                },
            );
            let emap = ExceptionHandlerMap::build(&mh, fh).unwrap();
            assert_eq!(emap.handlers_of(eh), &[handler]);
            assert!(verify_func(&mh, fh).is_ok());

            // 3. 10,000-deep Const::ArrayLiteral chain through verify_module.
            let mut mc = mk_module();
            let fc = add_func(&mut mc);
            let ec = mc.func(fc).unwrap().blocks[0];
            emit_void(&mut mc, ec, Op::Return { value: None });
            let mut prev_cid = mc.consts.push(Const::Null);
            for _ in 0..10_000 {
                prev_cid = mc.consts.push_array(vec![prev_cid]);
            }
            assert!(verify_module(&mc).is_ok());

            // 4. 10,000-deep nested raw `Ty::Union` + canonical `Ty::union`:
            //    clone, ==, Hash, Debug, canonicalize, and Drop on 256 KiB stack.
            let mut deep_ty = Ty::DynPrim(DynPrim::Number);
            for _ in 0..10_000 {
                deep_ty = Ty::Union(Box::new([deep_ty]));
            }
            let cloned_ty = deep_ty.clone();
            assert_eq!(deep_ty, cloned_ty);
            let mut hasher1 = DefaultHasher::new();
            let mut hasher2 = DefaultHasher::new();
            deep_ty.hash(&mut hasher1);
            cloned_ty.hash(&mut hasher2);
            assert_eq!(hasher1.finish(), hasher2.finish());
            let dbg = format!("{deep_ty:?}");
            assert!(dbg.starts_with("Union([Union(["));
            assert_eq!(Ty::union([cloned_ty]), Ty::DynPrim(DynPrim::Number));
            drop(deep_ty);
        })
        .unwrap();
    handle.join().unwrap();
}
