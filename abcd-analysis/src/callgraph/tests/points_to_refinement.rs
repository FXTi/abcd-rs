//! Rung-1 `refine_with_points_to` callback bridging and Rung-2 PTA `super` call
//! co-evolution tests.

use super::*;

/// Higher-order callback dispatch (`design/analysis.md`):
/// `register(cb) { cb(); }` — the inner call's param callee is
/// unknown to the base trace; the `points_to` refinement bridges it to
/// the caller's closure body, and the refined graph's caller index
/// records the new edge.
#[test]
fn refine_bridges_param_callee() {
    let mut m = mk_module();
    let cb = add_func_named(&mut m, "cb");
    {
        let b = entry_of(&m, cb);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let register = add_func_named(&mut m, "register");
    let inner_call;
    {
        let b = entry_of(&m, register);
        m.func_mut(register).unwrap().modifiers = Modifiers::STATIC;
        add_param(&mut m, register, 0);
        add_param(&mut m, register, 1);
        add_param(&mut m, register, 2);
        let cb_param = add_param(&mut m, register, 3);
        inner_call = push_inst(
            &mut m,
            b,
            Op::Call {
                callee: cb_param,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let caller = add_func_named(&mut m, "caller");
    {
        let b = entry_of(&m, caller);
        let def_reg = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: register,
                captures: vec![],
                length: 1,
            },
        );
        let clo_reg = emit(&mut m, b, Op::AllocClosure { func: def_reg });
        let def_cb = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: cb,
                captures: vec![],
                length: 0,
            },
        );
        let clo_cb = emit(&mut m, b, Op::AllocClosure { func: def_cb });
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: clo_reg,
                this: None,
                args: vec![clo_cb],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let base = CallGraph::build(&m);
    assert_eq!(
        base.edge_at(inner_call).unwrap().targets,
        CallTargets::UnknownCallees
    );
    assert!(base.callers_of(cb).is_empty());

    let oracle = Rung1AliasOracle::new(&m, &base);
    let refined = CallGraph::refine_with_points_to(&m, &base, &oracle);
    let edge = refined.edge_at(inner_call).expect("edge");
    assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
    assert_eq!(edge.targets, CallTargets::Resolved(vec![cb]));
    assert!(edge.resolution_complete);
    assert_eq!(refined.callers_of(cb), &[inner_call]);
    // The base graph is untouched (immutable snapshot).
    assert_eq!(
        base.edge_at(inner_call).unwrap().targets,
        CallTargets::UnknownCallees
    );
    // Refinement is deterministic.
    let oracle2 = Rung1AliasOracle::new(&m, &base);
    assert_eq!(
        refined,
        CallGraph::refine_with_points_to(&m, &base, &oracle2)
    );

    // Sites that stay unknown: a callee that is a plain global load
    // (the engine's answer is opaque, no sites).
    let mut m2 = mk_module();
    let f = add_func_named(&mut m2, "f");
    let b = entry_of(&m2, f);
    let g = {
        let sym = m2.sym.intern("print");
        emit(
            &mut m2,
            b,
            Op::TryGetGlobal {
                name: sym,
                default: None,
            },
        )
    };
    let call = push_inst(
        &mut m2,
        b,
        Op::Call {
            callee: g,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m2, b, Op::Return { value: None });
    let base2 = CallGraph::build(&m2);
    let oracle3 = Rung1AliasOracle::new(&m2, &base2);
    let refined2 = CallGraph::refine_with_points_to(&m2, &base2, &oracle3);
    assert_eq!(
        refined2.edge_at(call).unwrap().targets,
        CallTargets::UnknownCallees,
        "opaque callees stay explicitly unknown"
    );
}

#[test]
fn super_call_with_load_function_resolves_base_ctor_and_never_self_recurses() {
    use crate::dataflow::pta::{
        PtaConfig, Rung2AliasOracle, analyze, analyze_with_links_and_roots,
    };
    use crate::module_link::ModuleLinkTable;

    let mut m = mk_module();
    let cid = ClassId::new(0);
    let s_tag = intern(&mut m, "tag");
    let s_base_owned = intern(&mut m, "baseOwned");

    // `Base` constructor writes `this.baseOwned = base_alloc` and `this.tag = arg0`.
    let (base_ctor, b_bc, p_bc) = add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 1);
    let base_alloc = alloc_object(&mut m, b_bc);
    emit_void(
        &mut m,
        b_bc,
        Op::StoreProp {
            object: p_bc[2],
            name: s_base_owned,
            value: base_alloc,
        },
    );
    emit_void(
        &mut m,
        b_bc,
        Op::StoreProp {
            object: p_bc[2],
            name: s_tag,
            value: p_bc[3],
        },
    );
    emit_void(&mut m, b_bc, Op::Return { value: None });

    // `Sub` constructor lifts `supercallthisrange` (`R3-C5`):
    // `callee = LoadFunction`, `this = None`, `kind = CallKind::Super`.
    let (sub_ctor, b_sc, p_sc) = add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 1);
    let lf_sub = emit(&mut m, b_sc, Op::LoadFunction);
    let super_res = emit(
        &mut m,
        b_sc,
        Op::Call {
            callee: lf_sub,
            this: None,
            args: vec![p_sc[3]],
            kind: CallKind::Super,
        },
    );
    let sub_super_call = match m.value(super_res).unwrap().def {
        ValueDef::Inst(i) => i,
        _ => unreachable!(),
    };
    emit_void(
        &mut m,
        b_sc,
        Op::Return {
            value: Some(super_res),
        },
    );

    // Standalone function with no `DefineClass` superclass: all `Super*`
    // calls on `LoadFunction` must stay `UnknownCallees` (never self-edges).
    let (standalone, b_st, _) = add_method_fn(&mut m, cid, "standalone", FunctionKind::Function, 0);
    let lf_st = emit(&mut m, b_st, Op::LoadFunction);
    let arr_st = alloc_array(&mut m, b_st);
    let mut standalone_super_calls = Vec::new();
    for kind in [
        CallKind::Super,
        CallKind::SuperArrow,
        CallKind::SuperSpread,
        CallKind::SuperForwardAllArgs,
    ] {
        let args = match kind {
            CallKind::SuperSpread | CallKind::SuperForwardAllArgs => vec![arr_st],
            _ => vec![],
        };
        standalone_super_calls.push(push_inst(
            &mut m,
            b_st,
            Op::Call {
                callee: lf_st,
                this: None,
                args,
                kind,
            },
        ));
    }
    emit_void(&mut m, b_st, Op::Return { value: None });

    // `func_main_0`: defines `Base` and `Sub extends Base`, constructs `new Sub(payload)`.
    let (main_fn, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
    let empty_mem = m.consts.push_array(vec![]);
    let base_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: base_ctor,
            heritage: None,
            members: empty_mem,
            member_attrs: vec![],
            count: 1,
        })),
    );
    let sub_cls = emit(
        &mut m,
        b_main,
        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
            ctor: sub_ctor,
            heritage: Some(base_cls),
            members: empty_mem,
            member_attrs: vec![],
            count: 1,
        })),
    );
    let payload = alloc_object(&mut m, b_main);
    let sub_inst = emit(
        &mut m,
        b_main,
        Op::Call {
            callee: sub_cls,
            this: None,
            args: vec![payload],
            kind: CallKind::New,
        },
    );
    let read_owned = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: sub_inst,
            name: s_base_owned,
        },
    );
    let read_tag = emit(
        &mut m,
        b_main,
        Op::LoadProp {
            object: sub_inst,
            name: s_tag,
        },
    );
    emit_void(&mut m, b_main, Op::Return { value: None });

    // 1. Base CallGraph + Rung-1 points-to refinement
    let links = ModuleLinkTable::build(&m);
    let base_cg = CallGraph::build_with_links(&m, &links);
    let r1 = Rung1AliasOracle::new(&m, &base_cg);
    let r1_cg = CallGraph::refine_with_points_to(&m, &base_cg, &r1);
    for cg in [&base_cg, &r1_cg] {
        let sub_edge = cg.edge_at(sub_super_call).expect("Sub super() edge");
        assert_eq!(sub_edge.targets, CallTargets::Resolved(vec![base_ctor]));
        assert!(!cg.callers_of(sub_ctor).contains(&sub_super_call));
        for &st_call in &standalone_super_calls {
            let st_edge = cg.edge_at(st_call).expect("standalone super edge");
            assert_eq!(st_edge.targets, CallTargets::UnknownCallees);
            assert_eq!(st_edge.edge_kind, CallEdgeKind::UnknownCallees);
        }
        assert!(cg.callers_of(standalone).is_empty());
    }

    // 2. Rung-2 whole-module PTA co-evolution
    let pta_out = analyze(&m, &base_cg, &PtaConfig::default());
    let pta_cg = pta_out.graph();
    assert_eq!(
        pta_cg.edge_at(sub_super_call).unwrap().targets,
        CallTargets::Resolved(vec![base_ctor])
    );
    assert!(!pta_cg.callers_of(sub_ctor).contains(&sub_super_call));
    for &st_call in &standalone_super_calls {
        let st_edge = pta_cg.edge_at(st_call).expect("pta standalone super edge");
        assert_eq!(st_edge.targets, CallTargets::UnknownCallees);
        assert_eq!(st_edge.edge_kind, CallEdgeKind::UnknownCallees);
    }
    assert!(pta_cg.callers_of(standalone).is_empty());

    let (_, tables, stats) = pta_out.into_parts();
    let r2 = Rung2AliasOracle::new(&m, tables, stats);
    let owned_ans = r2.query(read_owned, sub_super_call);
    assert!(!owned_ans.has_unknown, "{owned_ans:?}");
    assert_eq!(owned_ans.sites, r2.query(base_alloc, sub_super_call).sites);

    // Root-sliced PTA from `func_main_0` resolves `this.tag = arg0` precisely through `super(arg0)`.
    let sliced_out = analyze_with_links_and_roots(
        &m,
        &links,
        &base_cg,
        &PtaConfig::default(),
        Some(&[main_fn]),
    );
    let (_, s_tables, s_stats) = sliced_out.into_parts();
    let s_r2 = Rung2AliasOracle::new(&m, s_tables, s_stats);
    let tag_ans = s_r2.query(read_tag, sub_super_call);
    assert!(!tag_ans.has_unknown, "{tag_ans:?}");
    assert_eq!(tag_ans.sites, s_r2.query(payload, sub_super_call).sites);
}
