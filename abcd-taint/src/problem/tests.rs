use abcd_analysis::dataflow::heap::{AllocSiteSet, FieldChain, FieldKey, Rung0AliasOracle};
use abcd_analysis::dataflow::ifds::IfdsProblem;
use abcd_ir::{CallKind, Const, Edge, EdgeKind, ValueDef};

use super::*;
use crate::fact::{TaintBase, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers};
use abcd_ir::ty::Ty;

#[test]
fn func_bitset_and_lazy_liveness_and_global_reader_index_work_across_boundaries() {
    let mut bs = FuncBitSet::new(131);
    for &idx in &[0usize, 1, 63, 64, 65, 127, 128, 130] {
        assert!(!bs.get(idx));
        assert!(bs.set(idx));
        assert!(!bs.set(idx));
        assert!(bs.get(idx));
    }
    assert!(!bs.get(62));
    assert!(!bs.get(500));

    let all = FuncBitSet::new_all_set(66);
    assert!(all.get(0) && all.get(63) && all.get(65));
    assert!(!all.get(66) && !all.get(127) && !all.get(200));

    // Build >65 functions so `GlobalReaderIndex` and `LocalLiveness` exercise
    // multi-word `FuncBitSet` cones and both `Dense` and `Sparse` `InstLocMap`s.
    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d_glob, n_glob));

    let mut fids = Vec::new();
    for i in 0..70 {
        let name = format!("f_{i}");
        let sym = m.sym.intern(&name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, FunctionKind::Function);
        fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let bid = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        fd.blocks.push(bid);
        m.functions.push(fd);
        m.classes[0].methods.push(fid);
        fids.push((fid, bid));
    }

    // `f_0`: first instruction at InstId(0); we will append another instruction to `f_0`
    // after populating `f_1..f_69` so `f_0` exercises `InstLocMap::Sparse`!
    let g_sym = m.sym.intern("SHARED_G");
    let v0 = ValueId::new(m.values.len() as u32);
    let i0 = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::TryGetGlobal {
            name: g_sym,
            default: None,
        },
        result: Some(v0),
        block: fids[0].1,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(i0),
        ty: Ty::Any,
    });
    m.blocks[fids[0].1.index()].insts.push(i0);

    for &(_, bid) in &fids[1..68] {
        let ri = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op: Op::Return { value: None },
            result: None,
            block: bid,
            loc: None,
        });
        m.blocks[bid.index()].insts.push(ri);
    }

    // `f_68`: reads `globalThis.SHARED_G`.
    let go_v = ValueId::new(m.values.len() as u32);
    let go_i = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::LoadGlobalObject,
        result: Some(go_v),
        block: fids[68].1,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(go_i),
        ty: Ty::Any,
    });
    m.blocks[fids[68].1.index()].insts.push(go_i);
    let gp_v = ValueId::new(m.values.len() as u32);
    let gp_i = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::LoadProp {
            object: go_v,
            name: g_sym,
        },
        result: Some(gp_v),
        block: fids[68].1,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(gp_i),
        ty: Ty::Any,
    });
    m.blocks[fids[68].1.index()].insts.push(gp_i);
    let r68 = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: Some(gp_v) },
        result: None,
        block: fids[68].1,
        loc: None,
    });
    m.blocks[fids[68].1.index()].insts.push(r68);

    // `f_69`: dynamic global reader (`globalThis[idx]`).
    let go2_v = ValueId::new(m.values.len() as u32);
    let go2_i = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::LoadGlobalObject,
        result: Some(go2_v),
        block: fids[69].1,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(go2_i),
        ty: Ty::Any,
    });
    m.blocks[fids[69].1.index()].insts.push(go2_i);
    let idx_cid = m.consts.push(Const::Int32(0));
    let idx_v = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(idx_cid),
        ty: Ty::Any,
    });
    let dyn_v = ValueId::new(m.values.len() as u32);
    let dyn_i = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::LoadPropIdx {
            object: go2_v,
            index: idx_v,
        },
        result: Some(dyn_v),
        block: fids[69].1,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(dyn_i),
        ty: Ty::Any,
    });
    m.blocks[fids[69].1.index()].insts.push(dyn_i);
    let r69 = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: Some(dyn_v) },
        result: None,
        block: fids[69].1,
        loc: None,
    });
    m.blocks[fids[69].1.index()].insts.push(r69);

    // Append trailing `Return(v0)` to `f_0` so `f_0`'s instructions span `0..>70` (`Sparse`).
    let r0 = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: Some(v0) },
        result: None,
        block: fids[0].1,
        loc: None,
    });
    m.blocks[fids[0].1.index()].insts.push(r0);

    let other_sym = m.sym.intern("OTHER_G");
    let links = ModuleLinkTable::build(&m);
    let cg = CallGraph::build_with_links(&m, &links);
    let reg = SummaryRegistry::new();
    let cfg = TaintConfig::default();
    let prob = TaintProblem::new_with_links(
        &m,
        links.clone(),
        &cg,
        Oracle::Rung0(Rung0AliasOracle::new(&m)),
        &reg,
        &cfg,
    );

    assert!(prob.can_callee_read_global(g_sym, fids[0].0));
    assert!(prob.can_callee_read_global(g_sym, fids[68].0));
    assert!(prob.can_callee_read_global(g_sym, fids[69].0));
    assert!(!prob.can_callee_read_global(g_sym, fids[10].0));
    // Dynamic global reader (`f_69`) can read `other_sym`, while `f_0` and `f_68` cannot.
    assert!(prob.can_callee_read_global(other_sym, fids[69].0));
    assert!(!prob.can_callee_read_global(other_sym, fids[0].0));
    assert!(!prob.can_callee_read_global(other_sym, fids[68].0));

    // Lazy `LocalLiveness`: zero functions built prior to first query!
    assert!(prob.liveness.funcs.borrow().iter().all(Option::is_none));
    assert!(
        prob.liveness
            .is_live_at(&m, links.block_func_slice(), &prob.await_resume, r0, v0,)
    );
    assert!(prob.liveness.funcs.borrow()[0].is_some());
    assert!(
        prob.liveness.funcs.borrow()[1..]
            .iter()
            .all(Option::is_none)
    );
}

#[test]
fn normal_vs_exceptional_exit_and_harness_heap_isolation_regressions() {
    use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze_with_links_and_roots};
    use abcd_ir::function::{Catch, Edge, EdgeKind, TryRegion};
    use abcd_ir::module::{EsModule, ExportDecl};

    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid_host = ClassId::new(0);
    m.classes.push(ClassData::new(d_glob, n_glob));

    let d_a = m.sym.intern("La;");
    let n_a = m.sym.intern("a");
    let cid_a = ClassId::new(1);
    let mut cls_a = ClassData::new(d_a, n_a);
    let exp_sym = m.sym.intern("sharedBox");
    cls_a.es_module = Some(EsModule {
        imports: Vec::new(),
        exports: vec![ExportDecl::Local {
            local_name: exp_sym,
            export_name: exp_sym,
        }],
        module_requests: Vec::new(),
    });
    m.classes.push(cls_a);

    let d_b = m.sym.intern("Lb;");
    let n_b = m.sym.intern("b");
    let cid_b = ClassId::new(2);
    let mut cls_b = ClassData::new(d_b, n_b);
    cls_b.es_module = Some(EsModule::default());
    m.classes.push(cls_b);

    // `callee_a` in `cid_a`: allocates a purely local object `loc_obj`, has both
    // a normal `Op::Return` exit and an `Op::Throw` exit.
    let fn_a_sym = m.sym.intern("calleeA");
    let fid_a = FuncId::new(m.functions.len() as u32);
    let mut fd_a = FunctionData::new(cid_a, fn_a_sym, FunctionKind::Function);
    fd_a.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let ba_ret = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let ba_thr = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd_a.blocks.extend([ba_ret, ba_thr]);
    m.functions.push(fd_a);
    m.classes[cid_a.index()].methods.push(fid_a);

    let empty_shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    let v_loc_obj = ValueId::new(m.values.len() as u32);
    let iid_loc_alloc = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::AllocObject { shape: empty_shape },
        result: Some(v_loc_obj),
        block: ba_ret,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid_loc_alloc),
        ty: Ty::Any,
    });
    let v_pure_loc = ValueId::new(m.values.len() as u32);
    let iid_pure_loc = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::AllocObject { shape: empty_shape },
        result: Some(v_pure_loc),
        block: ba_ret,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid_pure_loc),
        ty: Ty::Any,
    });
    let iid_store_mod_a = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::StoreModuleVar {
            index: 0,
            value: v_loc_obj,
        },
        result: None,
        block: ba_ret,
        loc: None,
    });
    let v_load_mod_a = ValueId::new(m.values.len() as u32);
    let iid_load_mod_a = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::LoadModuleVar {
            index: 0,
            kind: abcd_ir::ModuleVarKind::Local,
        },
        result: Some(v_load_mod_a),
        block: ba_ret,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid_load_mod_a),
        ty: Ty::Any,
    });
    let iid_ret_a = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: None },
        result: None,
        block: ba_ret,
        loc: None,
    });
    m.blocks[ba_ret.index()].insts.extend([
        iid_loc_alloc,
        iid_pure_loc,
        iid_store_mod_a,
        iid_load_mod_a,
        iid_ret_a,
    ]);

    let iid_thr_a = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Throw { value: v_loc_obj },
        result: None,
        block: ba_thr,
        loc: None,
    });
    m.blocks[ba_thr.index()].insts.push(iid_thr_a);

    // `callee_b` in `cid_b`: unrelated component method that does NOT import `cid_a`.
    let fn_b_sym = m.sym.intern("calleeB");
    let fid_b = FuncId::new(m.functions.len() as u32);
    let mut fd_b = FunctionData::new(cid_b, fn_b_sym, FunctionKind::Function);
    fd_b.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bb_entry = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd_b.blocks.push(bb_entry);
    m.functions.push(fd_b);
    m.classes[cid_b.index()].methods.push(fid_b);
    let iid_ret_b = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: None },
        result: None,
        block: bb_entry,
        loc: None,
    });
    m.blocks[bb_entry.index()].insts.push(iid_ret_b);

    // `caller_try` in `cid_a`: calls `callee_a` inside `try { ... } catch (e) { ... }`.
    let fn_caller_sym = m.sym.intern("callerTry");
    let fid_caller = FuncId::new(m.functions.len() as u32);
    let mut fd_caller = FunctionData::new(cid_a, fn_caller_sym, FunctionKind::Function);
    fd_caller.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bc_try = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let bc_norm = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let bc_catch = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let v_exc = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(bc_catch),
        ty: Ty::Any,
    });
    fd_caller.try_regions.push(TryRegion {
        protected: vec![bc_try],
        catches: vec![Catch {
            type_class: None,
            handler: bc_catch,
            exception: v_exc,
        }],
    });
    fd_caller.blocks.extend([bc_try, bc_norm, bc_catch]);
    m.functions.push(fd_caller);
    m.classes[cid_a.index()].methods.push(fid_caller);

    let c_ref_a = m.consts.push(Const::MethodRef {
        func: fid_a,
        kind: abcd_ir::LitMethodKind::Method,
    });
    let v_ref_a = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(c_ref_a),
        ty: Ty::Any,
    });
    let iid_call_try = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Call {
            callee: v_ref_a,
            this: None,
            args: Vec::new(),
            kind: CallKind::Direct,
        },
        result: None,
        block: bc_try,
        loc: None,
    });
    let iid_br_norm = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Branch { dest: bc_norm },
        result: None,
        block: bc_try,
        loc: None,
    });
    m.blocks[bc_try.index()]
        .insts
        .extend([iid_call_try, iid_br_norm]);
    m.blocks[bc_norm.index()].preds.push(Edge {
        from: bc_try,
        kind: EdgeKind::Normal,
    });
    m.blocks[bc_catch.index()].preds.push(Edge {
        from: bc_try,
        kind: EdgeKind::Exceptional,
    });

    let v_read_g = ValueId::new(m.values.len() as u32);
    let iid_rs_norm = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::TryGetGlobal {
            name: exp_sym,
            default: None,
        },
        result: Some(v_read_g),
        block: bc_norm,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid_rs_norm),
        ty: Ty::Any,
    });
    let iid_ret_norm = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return {
            value: Some(v_read_g),
        },
        result: None,
        block: bc_norm,
        loc: None,
    });
    m.blocks[bc_norm.index()]
        .insts
        .extend([iid_rs_norm, iid_ret_norm]);

    let iid_rs_catch = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: Some(v_exc) },
        result: None,
        block: bc_catch,
        loc: None,
    });
    m.blocks[bc_catch.index()].insts.push(iid_rs_catch);

    // Synthetic `__abcd_ohos_harness__` calling `fid_a` and `fid_b`.
    let h_sym = m.sym.intern("__abcd_ohos_harness__");
    let h_fid = FuncId::new(m.functions.len() as u32);
    let mut fd_h = FunctionData::new(cid_host, h_sym, FunctionKind::Function);
    fd_h.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bh = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd_h.blocks.push(bh);
    m.functions.push(fd_h);
    m.classes[cid_host.index()].methods.push(h_fid);

    let c_ref_b = m.consts.push(Const::MethodRef {
        func: fid_b,
        kind: abcd_ir::LitMethodKind::Method,
    });
    let v_ref_b = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(c_ref_b),
        ty: Ty::Any,
    });
    let iid_h_call_a = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Call {
            callee: v_ref_a,
            this: None,
            args: Vec::new(),
            kind: CallKind::Direct,
        },
        result: None,
        block: bh,
        loc: None,
    });
    let iid_h_call_b = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Call {
            callee: v_ref_b,
            this: None,
            args: Vec::new(),
            kind: CallKind::Direct,
        },
        result: None,
        block: bh,
        loc: None,
    });
    let iid_h_ret = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op: Op::Return { value: None },
        result: None,
        block: bh,
        loc: None,
    });
    m.blocks[bh.index()]
        .insts
        .extend([iid_h_call_a, iid_h_call_b, iid_h_ret]);

    let dead_sym = m.sym.intern("unreadGlobalSym");
    let links = ModuleLinkTable::build_with_harness(&m, Some(h_fid));
    let base_cg = CallGraph::build_with_links(&m, &links);
    let pta_cfg = PtaConfig {
        harness_func: Some(h_fid),
        ..PtaConfig::default()
    };
    let (cg, tables, stats) =
        analyze_with_links_and_roots(&m, &links, &base_cg, &pta_cfg, None).into_parts();
    let reg = SummaryRegistry::new();
    let cfg = TaintConfig::default();
    let prob = TaintProblem::new_with_harness(
        &m,
        links,
        &cg,
        Oracle::rung2(Rung2AliasOracle::new(&m, tables, stats)),
        &reg,
        &cfg,
        Some(h_fid),
    );

    let dead_fact = Fact::of(TaintFact {
        base: TaintBase::Global(dead_sym),
        fields: FieldChain::new(),
    });
    let g_fact = Fact::of(TaintFact {
        base: TaintBase::Global(exp_sym),
        fields: FieldChain::new(),
    });
    let heap_fact = Fact::of(TaintFact {
        base: TaintBase::Heap(AllocSiteSet::one(iid_loc_alloc)),
        fields: FieldChain::new(),
    });

    // 1. `call_uncaught_exit_flow`: normal `Op::Return` MUST NOT emit fake uncaught exits,
    //    whereas `Op::Throw` propagates state + `UNCAUGHT_EXCEPTION_VALUE`.
    let mut out = Vec::new();
    prob.call_uncaught_exit_flow(&m, iid_call_try, fid_a, iid_ret_a, &g_fact, &mut out);
    assert!(
        out.is_empty(),
        "normal Op::Return must never trigger call_uncaught_exit_flow: {out:?}"
    );
    prob.call_uncaught_exit_flow(&m, iid_call_try, fid_a, iid_thr_a, &heap_fact, &mut out);
    assert!(out.contains(&heap_fact));
    assert!(out.contains(&Fact::of(TaintFact::local(UNCAUGHT_EXCEPTION_VALUE))));

    // 2. `return_flow`: normal `Op::Return` state facts route only to `iid_rs_norm`,
    //    and `Op::Throw` state facts route only to `iid_rs_catch`.
    out.clear();
    prob.return_flow(
        &m,
        Some(iid_call_try),
        fid_a,
        iid_ret_a,
        Some(iid_rs_catch),
        &g_fact,
        &mut out,
    );
    assert!(
        out.is_empty(),
        "Op::Return state must not route to catch handler: {out:?}"
    );
    prob.return_flow(
        &m,
        Some(iid_call_try),
        fid_a,
        iid_ret_a,
        Some(iid_rs_norm),
        &g_fact,
        &mut out,
    );
    assert_eq!(out, vec![g_fact.clone()]);

    out.clear();
    prob.return_flow(
        &m,
        Some(iid_call_try),
        fid_a,
        iid_ret_a,
        Some(iid_rs_norm),
        &dead_fact,
        &mut out,
    );
    assert!(
        out.is_empty(),
        "unread state fact must be pruned across return_flow: {out:?}"
    );

    out.clear();
    prob.return_flow(
        &m,
        Some(iid_call_try),
        fid_a,
        iid_thr_a,
        Some(iid_rs_norm),
        &g_fact,
        &mut out,
    );
    assert!(
        out.is_empty(),
        "Op::Throw state must not route to normal continuation: {out:?}"
    );
    prob.return_flow(
        &m,
        Some(iid_call_try),
        fid_a,
        iid_thr_a,
        Some(iid_rs_catch),
        &g_fact,
        &mut out,
    );
    assert_eq!(out, vec![g_fact]);

    // 3. Cross-harness heap isolation: exported `iid_loc_alloc` in `cid_a` can exit and
    //    re-enter `fid_a` across harness, MUST NOT enter unrelated `fid_b` (`cid_b`), and
    //    unexported local `iid_pure_loc` MUST NOT even exit into harness.
    let Fact::Taint(ref tf_heap) = heap_fact else {
        panic!("expected taint fact");
    };
    let tf_pure = TaintFact {
        base: TaintBase::Heap(AllocSiteSet::one(iid_pure_loc)),
        fields: FieldChain::new(),
    };
    assert!(prob.allow_state_across_harness(iid_h_call_a, fid_a, tf_heap, false));
    assert!(prob.allow_state_across_harness(iid_h_call_a, fid_a, tf_heap, true));
    assert!(!prob.allow_state_across_harness(iid_h_call_b, fid_b, tf_heap, true));
    assert!(!prob.allow_state_across_harness(iid_h_call_a, fid_a, &tf_pure, false));
    assert!(!prob.allow_state_across_harness(iid_h_call_a, fid_a, &tf_pure, true));
}

#[test]
fn classify_dyn_prop_key_rejects_string_concat_and_non_numeric_phi_seeds() {
    let mut m = Module::new();
    let d_glob = m.sym.intern("L_GLOBAL;");
    let n_glob = m.sym.intern("_GLOBAL");
    let cid = ClassId::new(0);
    m.classes.push(ClassData::new(d_glob, n_glob));
    let fname = m.sym.intern("func_main_0");
    let mut fd = FunctionData::new(cid, fname, FunctionKind::Function);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);

    let b_entry = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let b_loop_str = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    let b_loop_num = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd.blocks = vec![b_entry, b_loop_str, b_loop_num];
    m.functions.push(fd);

    let push_val_inst = |m: &mut Module, b: BlockId, op: Op| -> ValueId {
        let iid = InstId::new(m.insts.len() as u32);
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        m.insts.push(Inst {
            op,
            result: Some(vid),
            block: b,
            loc: None,
        });
        m.blocks[b.index()].insts.push(iid);
        vid
    };

    let s_pref = m.sym.intern("prefix");
    let c_pref = m.consts.intern(Const::String(s_pref));
    let c_zero = m.consts.intern(Const::Int32(0));
    let c_one = m.consts.intern(Const::Int32(1));

    let v_pref = push_val_inst(&mut m, b_entry, Op::LoadConst(c_pref));
    let v_zero = push_val_inst(&mut m, b_entry, Op::LoadConst(c_zero));
    let v_one = push_val_inst(&mut m, b_entry, Op::LoadConst(c_one));

    // 1. `"prefix" + 1` evaluates to `"prefix1"` (string concatenation), NOT a numeric index.
    let v_str_concat = push_val_inst(
        &mut m,
        b_entry,
        Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: v_pref,
            right: v_one,
        },
    );
    assert_eq!(
        classify_dyn_prop_key(&m, v_str_concat),
        FieldKey::AnyDynamic
    );

    // 2. `k = phi("prefix", k + 1)` has a string initial seed -> `FieldKey::AnyDynamic`.
    let phi_str_iid = InstId::new(m.insts.len() as u32);
    let v_phi_str = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(phi_str_iid),
        ty: Ty::Any,
    });
    m.insts.push(Inst {
        op: Op::Phi {
            entries: Vec::new(),
        },
        result: Some(v_phi_str),
        block: b_loop_str,
        loc: None,
    });
    m.blocks[b_loop_str.index()].insts.push(phi_str_iid);
    let v_str_step = push_val_inst(
        &mut m,
        b_loop_str,
        Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: v_phi_str,
            right: v_one,
        },
    );
    m.insts[phi_str_iid.index()].op = Op::Phi {
        entries: vec![
            (
                Edge {
                    from: b_entry,
                    kind: EdgeKind::Normal,
                },
                v_pref,
            ),
            (
                Edge {
                    from: b_loop_str,
                    kind: EdgeKind::Normal,
                },
                v_str_step,
            ),
        ],
    };
    assert_eq!(classify_dyn_prop_key(&m, v_phi_str), FieldKey::AnyDynamic);

    // 3. `i = phi(0, i + 1)` has numeric seed and numeric step -> `FieldKey::AnyIndex`.
    let phi_num_iid = InstId::new(m.insts.len() as u32);
    let v_phi_num = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(phi_num_iid),
        ty: Ty::Any,
    });
    m.insts.push(Inst {
        op: Op::Phi {
            entries: Vec::new(),
        },
        result: Some(v_phi_num),
        block: b_loop_num,
        loc: None,
    });
    m.blocks[b_loop_num.index()].insts.push(phi_num_iid);
    let v_num_step = push_val_inst(
        &mut m,
        b_loop_num,
        Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: v_phi_num,
            right: v_one,
        },
    );
    m.insts[phi_num_iid.index()].op = Op::Phi {
        entries: vec![
            (
                Edge {
                    from: b_entry,
                    kind: EdgeKind::Normal,
                },
                v_zero,
            ),
            (
                Edge {
                    from: b_loop_num,
                    kind: EdgeKind::Normal,
                },
                v_num_step,
            ),
        ],
    };
    assert_eq!(classify_dyn_prop_key(&m, v_phi_num), FieldKey::AnyIndex);
}
