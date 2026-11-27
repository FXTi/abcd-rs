//! IFDS micro-analyses: a tiny taint problem proving the wiring — normal
//! flow, call → callee → return (incl. summary replay across two call
//! sites), call-to-return bypass, and exceptional paths (intra- AND
//! inter-procedural, including an exception-ONLY path to a sink).

use super::*;
use crate::testutil::*;
use abcd_ir::{BlockId, ClassId, Const, EdgeKind, FunctionKind, Op, ValueId};

/// The fact: zero or a tainted SSA value (the interned-id discipline:
/// facts are newtypes over `ValueId`, so hashing is an integer compare).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Fact {
    Zero,
    V(ValueId),
    UncaughtThrow,
}

/// Test-local intraprocedural empty call-graph oracle (`#83`).
struct NoCalls;

impl CallGraphOracle for NoCalls {
    fn callees_of_call_at(&self, _call: InstId) -> &[FuncId] {
        &[]
    }

    fn callers_of(&self, _func: FuncId) -> &[InstId] {
        &[]
    }
}

/// A map-backed call-graph oracle for tests.
#[derive(Default)]
struct MapCallGraph {
    callees: HashMap<InstId, Vec<FuncId>>,
    callers: HashMap<FuncId, Vec<InstId>>,
}

impl MapCallGraph {
    fn add(&mut self, call: InstId, callee: FuncId) {
        self.callees.entry(call).or_default().push(callee);
        self.callers.entry(callee).or_default().push(call);
    }
}

impl CallGraphOracle for MapCallGraph {
    fn callees_of_call_at(&self, call: InstId) -> &[FuncId] {
        self.callees.get(&call).map(Vec::as_slice).unwrap_or(&[])
    }

    fn callers_of(&self, func: FuncId) -> &[InstId] {
        self.callers.get(&func).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// Mini taint: sources are `LoadConst` of the string "secret"; taint
/// flows through Mov / compute ops / phis / loads; call args map to
/// callee params (params[1..], params[0] is `this` — T10); returns map to
/// the call result; `Throw` maps to the handler's `ExceptionParam` on
/// exceptional edges, intra- and inter-procedurally.
struct MicroTaint;

impl MicroTaint {
    /// Is `inst`'s op a `LoadConst` of the "secret" string?
    fn is_source(&self, module: &Module, inst: InstId) -> bool {
        matches!(
            module.inst(inst).map(|i| &i.op),
            Some(Op::LoadConst(c)) if matches!(module.consts.get(*c), Some(Const::String(s)) if module.sym.resolve(*s) == Some("secret"))
        )
    }

    /// The `ExceptionParam` value delivered at the head of the block that
    /// contains `first_inst` (when that block is a catch handler).
    fn handler_param(module: &Module, first_inst: InstId) -> Option<ValueId> {
        let block = module.inst(first_inst)?.block;
        let func = module.funcs_of_block(block)?;
        for region in &func.try_regions {
            for catch in &region.catches {
                if catch.handler == block {
                    return Some(catch.exception);
                }
            }
        }
        None
    }

    /// Propagate value taint across one instruction's semantics.
    fn propagate_inst(module: &Module, inst: InstId, v: ValueId, out: &mut Vec<Fact>) {
        let Some(inst) = module.inst(inst) else {
            return;
        };
        let result = || inst.result.map(Fact::V);
        match &inst.op {
            Op::Mov { src } if *src == v => out.extend(result()),
            Op::BinaryOp { left, right, .. } if *left == v || *right == v => out.extend(result()),
            Op::UnaryOp { operand, .. } if *operand == v => out.extend(result()),
            Op::Compare { left, right, .. } if *left == v || *right == v => out.extend(result()),
            Op::Phi { entries } if entries.iter().any(|(_, e)| *e == v) => out.extend(result()),
            Op::LoadProp { object, .. } if *object == v => out.extend(result()),
            _ => {}
        }
    }
}

impl IfdsProblem for MicroTaint {
    type Fact = Fact;

    fn zero(&self) -> Fact {
        Fact::Zero
    }

    fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
        Vec::new() // tests pass seeds via `solve_seeded`
    }

    fn normal_flow(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        match *source {
            Fact::Zero => {
                // Source generation: the seed is the zero fact flowing
                // over the source instruction.
                if self.is_source(module, curr)
                    && let Some(v) = module.inst(curr).and_then(|i| i.result)
                {
                    out.push(Fact::V(v));
                }
            }
            Fact::V(v) => {
                // Value facts persist (SSA values are never overwritten).
                out.push(Fact::V(v));
                Self::propagate_inst(module, curr, v, out);
                // Exception dispatch: `throw v` taints the handler's
                // exception parameter along the exceptional edge.
                if matches!(module.inst(curr).map(|i| &i.op), Some(Op::Throw { value }) if *value == v)
                    && let Some(exc) = Self::handler_param(module, succ)
                {
                    out.push(Fact::V(exc));
                }
            }
            Fact::UncaughtThrow => {}
        }
    }

    fn call_flow(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Fact::V(v) = *source else { return };
        let Some(inst) = module.inst(call) else {
            return;
        };
        let Op::Call { this, args, .. } = &inst.op else {
            return;
        };
        let Some(cf) = module.func(callee) else {
            return;
        };
        // T10 binding table: params[0] is `this`, formals follow.
        if *this == Some(v)
            && let Some(&p) = cf.params.first()
        {
            out.push(Fact::V(p));
        }
        for (i, &a) in args.iter().enumerate() {
            if a == v
                && let Some(&p) = cf.params.get(i + 1)
            {
                out.push(Fact::V(p));
            }
        }
    }

    fn return_flow(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        _callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        if *source == Fact::UncaughtThrow {
            if let Some(exc) = return_site.and_then(|r| Self::handler_param(module, r)) {
                out.push(Fact::V(exc));
            }
            return;
        }
        let Fact::V(v) = *source else { return };
        let Some(exit_inst) = module.inst(exit) else {
            return;
        };
        match &exit_inst.op {
            // Returned value taints the call's result.
            Op::Return { value: Some(rv) } if *rv == v => {
                if let Some(result) = call_site
                    .and_then(|c| module.inst(c))
                    .and_then(|i| i.result)
                {
                    out.push(Fact::V(result));
                }
            }
            // Thrown value taints the handler's exception parameter on
            // exceptional return sites only.
            Op::Throw { value } if *value == v => {
                if let Some(exc) = return_site.and_then(|r| Self::handler_param(module, r)) {
                    out.push(Fact::V(exc));
                }
            }
            _ => {}
        }
    }

    fn call_uncaught_exit_flow(
        &self,
        module: &Module,
        _call_site: InstId,
        _callee: FuncId,
        callee_exit: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        match *source {
            Fact::UncaughtThrow => out.push(Fact::UncaughtThrow),
            Fact::V(v) => {
                if matches!(
                    module.inst(callee_exit).map(|i| &i.op),
                    Some(Op::Throw { value }) if *value == v
                ) {
                    out.push(Fact::UncaughtThrow);
                }
            }
            Fact::Zero => {}
        }
    }

    fn call_to_return_flow(
        &self,
        _module: &Module,
        _call: InstId,
        _return_site: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        // The bypass is the identity: caller-local facts survive the call.
        out.push(*source);
    }
}

/// Solve the micro problem over `module` with `seeds` and `cg`.
fn solve_micro(module: &Module, cg: &MapCallGraph, seeds: Vec<(FuncId, Fact)>) -> IfdsResult<Fact> {
    struct Seeded<'a> {
        inner: &'a MicroTaint,
        seeds: Vec<(FuncId, Fact)>,
    }
    impl IfdsProblem for Seeded<'_> {
        type Fact = Fact;
        fn zero(&self) -> Fact {
            self.inner.zero()
        }
        fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
            self.seeds.clone()
        }
        fn normal_flow(&self, m: &Module, c: InstId, s: InstId, src: &Fact, out: &mut Vec<Fact>) {
            self.inner.normal_flow(m, c, s, src, out);
        }
        fn call_flow(&self, m: &Module, c: InstId, f: FuncId, src: &Fact, out: &mut Vec<Fact>) {
            self.inner.call_flow(m, c, f, src, out);
        }
        fn return_flow(
            &self,
            m: &Module,
            c: Option<InstId>,
            f: FuncId,
            e: InstId,
            r: Option<InstId>,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            self.inner.return_flow(m, c, f, e, r, src, out);
        }
        fn call_to_return_flow(
            &self,
            m: &Module,
            c: InstId,
            r: InstId,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            self.inner.call_to_return_flow(m, c, r, src, out);
        }
        fn call_uncaught_exit_flow(
            &self,
            m: &Module,
            cs: InstId,
            f: FuncId,
            ce: InstId,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            self.inner.call_uncaught_exit_flow(m, cs, f, ce, src, out);
        }
    }
    let problem = Seeded {
        inner: &MicroTaint,
        seeds,
    };
    IfdsSolver::new(module, &problem, cg, IfdsConfig::default()).solve()
}

// `Module` has no block→function lookup; the micro problem needs it for
// handler discovery. These helpers keep the test code honest.
trait ModuleExt {
    fn funcs_of_block(&self, block: BlockId) -> Option<&abcd_ir::FunctionData>;
}

impl ModuleExt for Module {
    fn funcs_of_block(&self, block: BlockId) -> Option<&abcd_ir::FunctionData> {
        self.functions.iter().find(|f| f.blocks.contains(&block))
    }
}

/// An external sink function (no body — T6 attachment point).
fn add_external_sink(m: &mut Module, name: &str) -> FuncId {
    let sym = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    let mut fd = abcd_ir::FunctionData::new(ClassId::new(0), sym, FunctionKind::Function);
    fd.is_external = true;
    m.functions.push(fd);
    m.classes[0].methods.push(id);
    id
}

/// Straight-line: `x = secret; y = x + 1; sink(y)` — normal flow only.
#[test]
fn straight_line_source_to_sink() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let sink = add_external_sink(&mut m, "sink");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0); // this

    let x = load_string(&mut m, entry, "secret");
    let one = load_number(&mut m, entry, 1.0);
    let y = add(&mut m, entry, x, one);
    let callee = load_method_ref(&mut m, entry, sink);
    let call = emit_void_call(&mut m, entry, callee, vec![y]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut cg = MapCallGraph::default();
    cg.add(call, sink);
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    // The tainted argument's fact reaches the sink call node.
    assert!(
        result.is_reached(call, &Fact::V(y)),
        "tainted arg must reach the sink call: {:?}",
        result.path_edges()
    );
    // The untainted operand never becomes a fact.
    assert!(!result.is_reached(call, &Fact::V(one)));
    // The sink has no body: nothing propagates into it, and the caller's
    // facts flow around the call (call-to-return bypass).
    let ret = m.block(entry).unwrap().insts.last().copied().unwrap();
    assert!(result.is_reached(ret, &Fact::V(y)));
}

/// Interprocedural: two callers of `id(p) = p`, each sinking the result.
/// Exercises call flow (arg→param), exit summaries (return value→call
/// result), and second-arriver replay: both call sites must receive the
/// summary regardless of arrival order.
#[test]
fn call_return_summary_both_call_sites() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // identity(p): return p
    let id = add_func_named(&mut m, "id");
    let id_entry = entry_of(&m, id);
    add_param(&mut m, id, 0); // this
    let p = add_param(&mut m, id, 1);
    emit_void(&mut m, id_entry, Op::Return { value: Some(p) });

    let mut calls = Vec::new();
    let mut results = Vec::new();
    let mut callers = Vec::new();
    for _ in 0..2 {
        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let x = load_string(&mut m, entry, "secret");
        let idref = load_method_ref(&mut m, entry, id);
        let r = emit(
            &mut m,
            entry,
            Op::Call {
                callee: idref,
                this: None,
                args: vec![x],
                kind: abcd_ir::CallKind::Direct,
            },
        );
        let sinkref = load_method_ref(&mut m, entry, sink);
        let sink_call = emit_void_call(&mut m, entry, sinkref, vec![r]);
        emit_void(&mut m, entry, Op::Return { value: None });
        callers.push(f);
        calls.push(sink_call);
        results.push(r);
    }

    let mut cg = MapCallGraph::default();
    for &f in &callers {
        // The id(...) call inst is the one with a result; find both calls.
        let entry = entry_of(&m, f);
        for &iid in &m.block(entry).unwrap().insts {
            if let Some(inst) = m.inst(iid)
                && matches!(inst.op, Op::Call { .. })
            {
                if inst.result.is_some() {
                    cg.add(iid, id);
                } else {
                    cg.add(iid, sink);
                }
            }
        }
    }

    let result = solve_micro(&m, &cg, callers.iter().map(|&f| (f, Fact::Zero)).collect());
    for (i, &sink_call) in calls.iter().enumerate() {
        assert!(
            result.is_reached(sink_call, &Fact::V(results[i])),
            "caller {i}: tainted call result must reach the sink call"
        );
    }
}

/// Intraprocedural exception path: `try { throw secret } catch (e) {
/// sink(e) }` — the ONLY path to the sink is the exceptional edge.
#[test]
fn exception_only_path_to_sink_intraprocedural() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let handler = add_block(&mut m, f);
    add_param(&mut m, f, 0);

    let x = load_string(&mut m, entry, "secret");
    emit_void(&mut m, entry, Op::Throw { value: x });
    emit_void(&mut m, entry, Op::Unreachable);

    let e = add_exception_param(&mut m, handler);
    let sinkref = load_method_ref(&mut m, handler, sink);
    let sink_call = emit_void_call(&mut m, handler, sinkref, vec![e]);
    emit_void(&mut m, handler, Op::Return { value: None });
    add_try(&mut m, f, vec![entry], handler, e);

    let mut cg = MapCallGraph::default();
    cg.add(sink_call, sink);
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    assert!(
        result.is_reached(sink_call, &Fact::V(e)),
        "the exception parameter must be tainted at the sink: {:?}",
        result.path_edges()
    );
}

/// Interprocedural exception path: the callee throws the tainted value
/// (unprotected → function exit); the caller's call site is protected, so
/// return flow along the EXCEPTIONAL return site taints the handler's
/// exception parameter. The call's normal continuation is dead
/// (`Unreachable`) — the sink is reachable only through the exception.
#[test]
fn exception_only_path_to_sink_interprocedural() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // bomb(p): throw p
    let bomb = add_func_named(&mut m, "bomb");
    let bomb_entry = entry_of(&m, bomb);
    add_param(&mut m, bomb, 0);
    let p = add_param(&mut m, bomb, 1);
    emit_void(&mut m, bomb_entry, Op::Throw { value: p });
    emit_void(&mut m, bomb_entry, Op::Unreachable);

    // caller: try { bomb(secret) } catch (e) { sink(e) }
    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    let handler = add_block(&mut m, f);
    add_param(&mut m, f, 0);
    let x = load_string(&mut m, entry, "secret");
    let bombref = load_method_ref(&mut m, entry, bomb);
    let call = emit_void_call(&mut m, entry, bombref, vec![x]);
    emit_void(&mut m, entry, Op::Unreachable);
    let e = add_exception_param(&mut m, handler);
    let sinkref = load_method_ref(&mut m, handler, sink);
    let sink_call = emit_void_call(&mut m, handler, sinkref, vec![e]);
    emit_void(&mut m, handler, Op::Return { value: None });
    add_try(&mut m, f, vec![entry], handler, e);

    let mut cg = MapCallGraph::default();
    cg.add(call, bomb);
    cg.add(sink_call, sink);
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    assert!(
        result.is_reached(sink_call, &Fact::V(e)),
        "the tainted thrown value must reach the caller's handler: {:?}",
        result.path_edges()
    );
}

/// The call-to-return bypass: a caller-local fact not passed to the
/// callee survives the call site unchanged.
#[test]
fn call_to_return_bypass_keeps_local_facts() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // noop(): return undefined
    let noop = add_func_named(&mut m, "noop");
    {
        let b = entry_of(&m, noop);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let x = load_string(&mut m, entry, "secret"); // tainted, never passed on
    let noopref = load_method_ref(&mut m, entry, noop);
    let call = emit_void_call(&mut m, entry, noopref, vec![]);
    let sinkref = load_method_ref(&mut m, entry, sink);
    let sink_call = emit_void_call(&mut m, entry, sinkref, vec![x]);
    emit_void(&mut m, entry, Op::Return { value: None });

    let mut cg = MapCallGraph::default();
    cg.add(call, noop);
    cg.add(sink_call, sink);
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    assert!(
        result.is_reached(sink_call, &Fact::V(x)),
        "caller-local taint must survive the call via the bypass edge"
    );
}

/// Phi merging: taint through one arm of a diamond taints the phi result.
#[test]
fn phi_merge_propagates_taint() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    add_param(&mut m, f, 0);

    let cond = load_number(&mut m, entry, 1.0);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: e,
        },
    );
    let x = load_string(&mut m, t, "secret");
    emit_void(&mut m, t, Op::Branch { dest: join });
    let y = load_number(&mut m, e, 2.0);
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);

    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    x,
                ),
                (
                    abcd_ir::Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    y,
                ),
            ],
        },
    );
    let sinkref = load_method_ref(&mut m, join, sink);
    let sink_call = emit_void_call(&mut m, join, sinkref, vec![phi]);
    emit_void(&mut m, join, Op::Return { value: None });

    let mut cg = MapCallGraph::default();
    cg.add(sink_call, sink);
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    assert!(result.is_reached(sink_call, &Fact::V(phi)));
}

/// Two identical solver runs produce identical path-edge sequences
/// (`design/decisions.md` N20 determinism).
#[test]
fn solver_is_deterministic() {
    let build = || {
        let mut m = mk_module();
        let sink = add_external_sink(&mut m, "sink");
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let handler = add_block(&mut m, f);
        add_param(&mut m, f, 0);
        let x = load_string(&mut m, entry, "secret");
        emit_void(&mut m, entry, Op::Throw { value: x });
        emit_void(&mut m, entry, Op::Unreachable);
        let e = add_exception_param(&mut m, handler);
        let sinkref = load_method_ref(&mut m, handler, sink);
        let sink_call = emit_void_call(&mut m, handler, sinkref, vec![e]);
        emit_void(&mut m, handler, Op::Return { value: None });
        add_try(&mut m, f, vec![entry], handler, e);
        (m, f, sink, sink_call)
    };
    let (m1, f1, sink1, call1) = build();
    let (m2, f2, sink2, call2) = build();
    let mut cg1 = MapCallGraph::default();
    cg1.add(call1, sink1);
    let mut cg2 = MapCallGraph::default();
    cg2.add(call2, sink2);
    let r1 = solve_micro(&m1, &cg1, vec![(f1, Fact::Zero)]);
    let r2 = solve_micro(&m2, &cg2, vec![(f2, Fact::Zero)]);
    assert_eq!(r1.path_edge_count(), r2.path_edge_count());
    assert_eq!(r1.raw_path_edges(), r2.raw_path_edges());
    assert_eq!(r1.path_edges(), r2.path_edges());
}

/// Lazy `path_edges` remains unmaterialized until requested, agrees with
/// `raw_path_edges` / `fact_by_id` / `id_of_fact`, and preserves `Clone`
/// across both uninitialized and initialized states.
#[test]
fn lazy_path_edges_and_raw_accessors_agree() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let s = load_string(&mut m, entry, "secret");
    let copy = emit(&mut m, entry, Op::Mov { src: s });
    emit_void(&mut m, entry, Op::Return { value: Some(copy) });

    let cg = MapCallGraph::default();
    let result = solve_micro(&m, &cg, vec![(f, Fact::Zero)]);

    assert!(result.path_edges.get().is_none());
    let uninit_clone = result.clone();
    assert!(uninit_clone.path_edges.get().is_none());

    let raw = result.raw_path_edges();
    assert_eq!(result.path_edge_count(), raw.len());
    assert_eq!(result.id_of_fact(&Fact::Zero), Some(0));
    assert_eq!(result.fact_by_id(0), Some(&Fact::Zero));
    let copy_id = result.id_of_fact(&Fact::V(copy)).unwrap();
    assert_eq!(result.fact_by_id(copy_id), Some(&Fact::V(copy)));
    assert_eq!(result.fact_by_id(u32::MAX), None);

    let materialized = result.path_edges();
    assert!(result.path_edges.get().is_some());
    assert_eq!(materialized.len(), raw.len());
    for (&(src, target_node, dst), edge) in raw.iter().zip(materialized.iter()) {
        assert_eq!(result.fact_by_id(src), Some(&edge.source_fact));
        assert_eq!(target_node, edge.target_node);
        assert_eq!(result.fact_by_id(dst), Some(&edge.target_fact));
    }

    let init_clone = result.clone();
    assert!(init_clone.path_edges.get().is_some());
    assert_eq!(init_clone.path_edges(), materialized);
    assert_eq!(uninit_clone.path_edges(), materialized);
}

/// Compact-set promotion (>8 facts and >8 incoming call sites) preserves
/// exact insertion order in `facts_at` and `is_reached`.
#[test]
fn compact_sets_promote_past_eight_preserving_order() {
    let mut m = mk_module();
    let id = add_func_named(&mut m, "id");
    let id_entry = entry_of(&m, id);
    add_param(&mut m, id, 0);
    let p = add_param(&mut m, id, 1);
    emit_void(&mut m, id_entry, Op::Return { value: Some(p) });

    let f = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let mut seeded_params = Vec::new();
    for idx in 1..=12 {
        seeded_params.push(Fact::V(add_param(&mut m, f, idx)));
    }

    let mut cg = MapCallGraph::default();
    let mut call_facts = Vec::new();
    for _ in 0..12 {
        let s = load_string(&mut m, entry, "secret");
        call_facts.push(Fact::V(s));
        let idref = load_method_ref(&mut m, entry, id);
        let r = emit(
            &mut m,
            entry,
            Op::Call {
                callee: idref,
                this: None,
                args: vec![s],
                kind: abcd_ir::CallKind::Direct,
            },
        );
        let call_iid = match m.value(r).unwrap().def {
            abcd_ir::ValueDef::Inst(i) => i,
            _ => panic!(),
        };
        cg.add(call_iid, id);
        call_facts.push(Fact::V(r));
    }
    emit_void(&mut m, entry, Op::Return { value: None });
    let sp_iid = m.block(entry).unwrap().insts[0];
    let ret_iid = *m.block(entry).unwrap().insts.last().unwrap();

    let mut seeds = vec![(f, Fact::Zero)];
    for &pf in &seeded_params {
        seeds.push((f, pf));
    }
    let result = solve_micro(&m, &cg, seeds);
    assert_eq!(result.facts_at(sp_iid, &Fact::Zero), seeded_params);
    assert!(result.is_reached(ret_iid, &Fact::Zero));
    for fact in seeded_params.iter().chain(call_facts.iter()) {
        assert!(result.is_reached(ret_iid, fact), "missing {fact:?}");
    }
}

/// Emit a `Call` with no result (void sink call); returns the InstId.
fn emit_void_call(m: &mut Module, b: BlockId, callee: ValueId, args: Vec<ValueId>) -> InstId {
    push_inst(
        m,
        b,
        Op::Call {
            callee,
            this: None,
            args,
            kind: abcd_ir::CallKind::Direct,
        },
    )
}

/// Selective `Λ -> Λ` call-edge gating (`propagate_zero_to_callee == false`)
/// skips `(Λ, inst, Λ)` tabulation inside source-free callees while preserving
/// both non-zero argument summaries `(d, sp, d)` and direct `Λ -> d` seed edges
/// produced by `call_flow(call, callee, &Λ)`.
#[test]
fn propagate_zero_to_callee_false_skips_zero_preserving_arg_and_seed_edges() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // Source-free identity helper: `id(p) { copy = Mov(p); return copy; }`.
    let id = add_func_named(&mut m, "id");
    let id_entry = entry_of(&m, id);
    add_param(&mut m, id, 0);
    let id_p = add_param(&mut m, id, 1);
    let id_copy = emit(&mut m, id_entry, Op::Mov { src: id_p });
    let id_ret_inst = emit_void(
        &mut m,
        id_entry,
        Op::Return {
            value: Some(id_copy),
        },
    );
    let id_sp = m.block(id_entry).unwrap().insts[0];

    // Source-free callback helper seeded directly on call entry (`Λ -> V(cb_p)`):
    // `cb(cb_p) { return cb_p; }`.
    let cb = add_func_named(&mut m, "cb");
    let cb_entry = entry_of(&m, cb);
    add_param(&mut m, cb, 0);
    let cb_p = add_param(&mut m, cb, 1);
    let cb_ret_inst = emit_void(&mut m, cb_entry, Op::Return { value: Some(cb_p) });

    // Caller: `x = "secret"; r1 = id(x); r2 = cb(dummy); sink(r1); sink(r2);`
    let caller = add_func_named(&mut m, "caller");
    let entry = entry_of(&m, caller);
    add_param(&mut m, caller, 0);
    let x = load_string(&mut m, entry, "secret");
    let dummy = load_number(&mut m, entry, 0.0);
    let id_ref = load_method_ref(&mut m, entry, id);
    let r1 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: id_ref,
            this: None,
            args: vec![x],
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let call_id = match m.value(r1).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        _ => panic!(),
    };
    let cb_ref = load_method_ref(&mut m, entry, cb);
    let r2 = emit(
        &mut m,
        entry,
        Op::Call {
            callee: cb_ref,
            this: None,
            args: vec![dummy],
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let call_cb = match m.value(r2).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        _ => panic!(),
    };
    let sink_ref1 = load_method_ref(&mut m, entry, sink);
    let sink_call1 = emit_void_call(&mut m, entry, sink_ref1, vec![r1]);
    let sink_ref2 = load_method_ref(&mut m, entry, sink);
    let sink_call2 = emit_void_call(&mut m, entry, sink_ref2, vec![r2]);
    let caller_ret = emit_void(&mut m, entry, Op::Return { value: None });

    let mut cg = MapCallGraph::default();
    cg.add(call_id, id);
    cg.add(call_cb, cb);
    cg.add(sink_call1, sink);
    cg.add(sink_call2, sink);

    struct GatedProblem {
        caller: FuncId,
        cb: FuncId,
        cb_param: ValueId,
    }

    impl IfdsProblem for GatedProblem {
        type Fact = Fact;

        fn zero(&self) -> Fact {
            Fact::Zero
        }

        fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
            vec![(self.caller, Fact::Zero)]
        }

        fn propagate_zero_to_callee(&self, _call: InstId, _callee: FuncId) -> bool {
            false
        }

        fn normal_flow(&self, m: &Module, c: InstId, s: InstId, src: &Fact, out: &mut Vec<Fact>) {
            MicroTaint.normal_flow(m, c, s, src, out);
        }

        fn call_flow(
            &self,
            m: &Module,
            call: InstId,
            callee: FuncId,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            if *src == Fact::Zero && callee == self.cb {
                out.push(Fact::V(self.cb_param));
                return;
            }
            MicroTaint.call_flow(m, call, callee, src, out);
        }

        fn return_flow(
            &self,
            m: &Module,
            c: Option<InstId>,
            f: FuncId,
            e: InstId,
            r: Option<InstId>,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            MicroTaint.return_flow(m, c, f, e, r, src, out);
        }

        fn call_to_return_flow(
            &self,
            m: &Module,
            c: InstId,
            r: InstId,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            MicroTaint.call_to_return_flow(m, c, r, src, out);
        }
    }

    let problem = GatedProblem {
        caller,
        cb,
        cb_param: cb_p,
    };
    let result = IfdsSolver::new(&m, &problem, &cg, IfdsConfig::default()).solve();

    // Neither source-free callee receives `(Λ, inst, Λ)` path edges.
    assert!(!result.is_reached(id_sp, &Fact::Zero));
    assert!(!result.is_reached(id_ret_inst, &Fact::Zero));
    assert!(!result.is_reached(cb_ret_inst, &Fact::Zero));

    // Non-zero argument flow `(V(id_p), id_sp, V(id_p))` still tabulates `id`
    // and returns taint to `r1`.
    assert!(result.is_reached(id_sp, &Fact::V(id_p)));
    assert!(result.is_reached(id_ret_inst, &Fact::V(id_copy)));
    assert!(result.is_reached(sink_call1, &Fact::V(r1)));

    // Direct `Λ -> V(cb_p)` seed edges from `call_flow` still fire and return to `r2`.
    assert!(result.is_reached(cb_ret_inst, &Fact::V(cb_p)));
    assert!(result.is_reached(sink_call2, &Fact::V(r2)));

    // Caller `Λ` still bypasses calls via `call_to_return_flow`.
    assert!(result.is_reached(caller_ret, &Fact::Zero));
}

/// 3-frame uncaught `Throw` (`f0 -> f1 -> f2` where `f2` throws `secret`, `f1`
/// does not catch, and `f0` catches `e` and passes `e` to `sink`) propagates
/// through `f1`'s call site into `f0`'s catch handler, while a locally
/// catch-all-caught `Throw` in `swallow` stays isolated inside `swallow` (`#79`).
#[test]
fn three_frame_uncaught_throw_propagates_and_local_catch_all_isolates() {
    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // `f2(p2) { throw p2; }`
    let f2 = add_func_named(&mut m, "f2");
    let f2_entry = entry_of(&m, f2);
    add_param(&mut m, f2, 0);
    let p2 = add_param(&mut m, f2, 1);
    emit_void(&mut m, f2_entry, Op::Throw { value: p2 });
    emit_void(&mut m, f2_entry, Op::Unreachable);

    // `f1(p1) { f2(p1); return; }` (no try/catch around `f2(p1)`)
    let f1 = add_func_named(&mut m, "f1");
    let f1_entry = entry_of(&m, f1);
    add_param(&mut m, f1, 0);
    let p1 = add_param(&mut m, f1, 1);
    let f2_ref = load_method_ref(&mut m, f1_entry, f2);
    let call_f2 = emit_void_call(&mut m, f1_entry, f2_ref, vec![p1]);
    let f1_ret = emit_void(&mut m, f1_entry, Op::Return { value: None });

    // `swallow(ps) { try { throw ps; } catch (es) { return; } }` (catch-all caught locally!)
    let swallow = add_func_named(&mut m, "swallow");
    let sw_entry = entry_of(&m, swallow);
    let sw_handler = add_block(&mut m, swallow);
    add_param(&mut m, swallow, 0);
    let ps = add_param(&mut m, swallow, 1);
    emit_void(&mut m, sw_entry, Op::Throw { value: ps });
    emit_void(&mut m, sw_entry, Op::Unreachable);
    let es = add_exception_param(&mut m, sw_handler);
    emit_void(&mut m, sw_handler, Op::Return { value: None });
    add_try(&mut m, swallow, vec![sw_entry], sw_handler, es);

    // Intraprocedural sanity check using `NoCalls`.
    let intra = IfdsSolver::new(
        &m,
        &MicroTaint,
        &NoCalls,
        IfdsConfig {
            follow_returns_past_seeds: false,
        },
    )
    .solve();
    assert_eq!(intra.path_edge_count(), 0);

    // `f0`:
    //   1) `try { swallow(secret) } catch (e_swallow) { sink(e_swallow) }` -> MUST NOT taint `e_swallow`!
    //   2) `try { f1(secret) } catch (e_uncaught) { sink(e_uncaught) }` -> MUST taint `e_uncaught`!
    let f0 = add_func_named(&mut m, "f0");
    let b_sw = entry_of(&m, f0);
    let h_sw = add_block(&mut m, f0);
    let b_f1 = add_block(&mut m, f0);
    let h_f1 = add_block(&mut m, f0);
    let b_done = add_block(&mut m, f0);
    add_param(&mut m, f0, 0);

    let sec1 = load_string(&mut m, b_sw, "secret");
    let sw_ref = load_method_ref(&mut m, b_sw, swallow);
    let call_sw = emit_void_call(&mut m, b_sw, sw_ref, vec![sec1]);
    emit_void(&mut m, b_sw, Op::Branch { dest: b_f1 });

    let e_sw = add_exception_param(&mut m, h_sw);
    let sink_ref1 = load_method_ref(&mut m, h_sw, sink);
    let sink_sw = emit_void_call(&mut m, h_sw, sink_ref1, vec![e_sw]);
    emit_void(&mut m, h_sw, Op::Branch { dest: b_f1 });

    let sec2 = load_string(&mut m, b_f1, "secret");
    let f1_ref = load_method_ref(&mut m, b_f1, f1);
    let call_f1 = emit_void_call(&mut m, b_f1, f1_ref, vec![sec2]);
    emit_void(&mut m, b_f1, Op::Branch { dest: b_done });

    let e_f1 = add_exception_param(&mut m, h_f1);
    let sink_ref2 = load_method_ref(&mut m, h_f1, sink);
    let sink_f1 = emit_void_call(&mut m, h_f1, sink_ref2, vec![e_f1]);
    emit_void(&mut m, h_f1, Op::Branch { dest: b_done });

    emit_void(&mut m, b_done, Op::Return { value: None });

    link(&mut m, b_sw, b_f1);
    link(&mut m, h_sw, b_f1);
    link(&mut m, b_f1, b_done);
    link(&mut m, h_f1, b_done);
    add_try(&mut m, f0, vec![b_sw], h_sw, e_sw);
    add_try(&mut m, f0, vec![b_f1], h_f1, e_f1);

    let mut cg = MapCallGraph::default();
    cg.add(call_sw, swallow);
    cg.add(call_f1, f1);
    cg.add(call_f2, f2);
    cg.add(sink_sw, sink);
    cg.add(sink_f1, sink);

    let result = solve_micro(&m, &cg, vec![(f0, Fact::Zero)]);

    // 3-frame uncaught throw reaches `call_f2` as `UncaughtThrow`, does NOT leak
    // onto `f1`'s normal return, and taints `e_f1` at `sink_f1` in `f0`.
    assert!(result.is_reached(call_f2, &Fact::UncaughtThrow));
    assert!(!result.is_reached(f1_ret, &Fact::UncaughtThrow));
    assert!(result.is_reached(sink_f1, &Fact::V(e_f1)));

    // Locally catch-all-caught throw in `swallow` reaches `sw_handler`, NEVER
    // escapes `swallow` to `e_sw` in `f0`.
    let sw_first = m.block(sw_handler).unwrap().insts[0];
    assert!(result.is_reached(sw_first, &Fact::V(es)));
    assert!(!result.is_reached(sink_sw, &Fact::V(e_sw)));
}

/// Regression test for `D6` (`#94`): when a callee BOTH throws uncaught on one
/// branch AND returns normally on another branch, and an identical global/heap
/// fact (`SharedFact::Token`) is used for both uncaught-exit propagation and
/// normal arrival at a call site in a middle frame `mid`:
/// - `propagate_uncaught_exit(d1, call_site, Token)` MUST NOT mask normal
///   arrival `(d1, call_site, Token)` (which feeds `by_target` + `process_call`
///   call-to-return + second-call normal return!), AND
/// - normal arrival `(d1, call_site, Token)` MUST NOT mask `propagate_uncaught_exit`
///   from forwarding the uncaught throw up to `outer`'s catch handler!
#[test]
fn uncaught_edge_set_separation_preserves_both_normal_return_and_uncaught_throw() {
    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum SharedFact {
        Zero,
        Token,
        Val(ValueId),
    }

    let mut m = mk_module();
    let sink = add_external_sink(&mut m, "sink");

    // `may_fail(cond)`: on `true` branch generates `Token` and throws; on
    // `false` branch returns `"secret"` normally.
    fn emit_call(
        m: &mut Module,
        b: BlockId,
        callee: ValueId,
        args: Vec<ValueId>,
    ) -> (InstId, ValueId) {
        let iid = InstId::new(m.insts.len() as u32);
        let v = emit(
            m,
            b,
            Op::Call {
                callee,
                this: None,
                args,
                kind: abcd_ir::CallKind::Direct,
            },
        );
        (iid, v)
    }
    let may_fail = add_func_named(&mut m, "may_fail");
    let mf_entry = entry_of(&m, may_fail);
    let mf_throw = add_block(&mut m, may_fail);
    let mf_ret = add_block(&mut m, may_fail);
    add_param(&mut m, may_fail, 0);
    let mf_cond = load_number(&mut m, mf_entry, 1.0);
    emit_void(
        &mut m,
        mf_entry,
        Op::CondBranch {
            cond: mf_cond,
            true_dest: mf_throw,
            false_dest: mf_ret,
        },
    );
    link(&mut m, mf_entry, mf_throw);
    link(&mut m, mf_entry, mf_ret);

    let thrown_src_iid = InstId::new(m.insts.len() as u32);
    let thrown_sec = load_string(&mut m, mf_throw, "secret");
    let mf_throw_iid = emit_void(&mut m, mf_throw, Op::Throw { value: thrown_sec });
    emit_void(&mut m, mf_throw, Op::Unreachable);

    let ret_src_iid = InstId::new(m.insts.len() as u32);
    let ret_sec = load_string(&mut m, mf_ret, "secret");
    let mf_ret_iid = emit_void(
        &mut m,
        mf_ret,
        Op::Return {
            value: Some(ret_sec),
        },
    );

    // `echo_if_token()`: when entered with `SharedFact::Token`, returns `"ok"` tainted!
    let echo = add_func_named(&mut m, "echo");
    let echo_entry = entry_of(&m, echo);
    add_param(&mut m, echo, 0);
    let echo_val = load_number(&mut m, echo_entry, 42.0);
    let echo_ret_iid = emit_void(
        &mut m,
        echo_entry,
        Op::Return {
            value: Some(echo_val),
        },
    );

    // `mid()`:
    //   1. Calls `may_fail()` FIRST (no catch-all): `may_fail`'s throw branch
    //      records `(Zero, call1, Token)` in `uncaught_edge_set` BEFORE normal
    //      return from `may_fail` generates `Token` after `call1`!
    //   2. Also loops back so `Token` arrives NORMALLY at `call1` `(Zero, call1, Token)`!
    //      With a single `edge_set`, `(Zero, call1, Token)` was already in `edge_set`
    //      from `propagate_uncaught_exit`, suppressing `by_target` + `call_to_return_flow`
    //      for `Token` across `call1` AND suppressing `echo()` at `call2`!
    let mid = add_func_named(&mut m, "mid");
    let mid_entry = entry_of(&m, mid);
    let mid_loop = add_block(&mut m, mid);
    let mid_after = add_block(&mut m, mid);
    add_param(&mut m, mid, 0);
    emit_void(&mut m, mid_entry, Op::Branch { dest: mid_loop });
    link(&mut m, mid_entry, mid_loop);

    let mf_ref = load_method_ref(&mut m, mid_loop, may_fail);
    let (call1, call1_res) = emit_call(&mut m, mid_loop, mf_ref, Vec::new());
    let loop_cond = load_number(&mut m, mid_loop, 0.0);
    emit_void(
        &mut m,
        mid_loop,
        Op::CondBranch {
            cond: loop_cond,
            true_dest: mid_loop,
            false_dest: mid_after,
        },
    );
    link(&mut m, mid_loop, mid_loop);
    link(&mut m, mid_loop, mid_after);

    let echo_ref = load_method_ref(&mut m, mid_after, echo);
    let (call2, call2_res) = emit_call(&mut m, mid_after, echo_ref, Vec::new());
    let mid_ret_iid = emit_void(
        &mut m,
        mid_after,
        Op::Return {
            value: Some(call2_res),
        },
    );

    // `outer()`: `try { let r = mid(); sink(r); } catch (e) { sink(e); }`
    let outer = add_func_named(&mut m, "outer");
    let out_try = entry_of(&m, outer);
    let out_catch = add_block(&mut m, outer);
    let out_done = add_block(&mut m, outer);
    add_param(&mut m, outer, 0);

    let mid_ref = load_method_ref(&mut m, out_try, mid);
    let (call_mid, mid_res) = emit_call(&mut m, out_try, mid_ref, Vec::new());
    let sink_ref1 = load_method_ref(&mut m, out_try, sink);
    let sink_norm = emit_void_call(&mut m, out_try, sink_ref1, vec![mid_res]);
    emit_void(&mut m, out_try, Op::Branch { dest: out_done });

    let exc_outer = add_exception_param(&mut m, out_catch);
    let sink_ref2 = load_method_ref(&mut m, out_catch, sink);
    let sink_exc = emit_void_call(&mut m, out_catch, sink_ref2, vec![exc_outer]);
    emit_void(&mut m, out_catch, Op::Branch { dest: out_done });

    emit_void(&mut m, out_done, Op::Return { value: None });
    link(&mut m, out_try, out_done);
    link(&mut m, out_catch, out_done);
    add_try(&mut m, outer, vec![out_try], out_catch, exc_outer);

    let mut cg = MapCallGraph::default();
    cg.add(call_mid, mid);
    cg.add(call1, may_fail);
    cg.add(call2, echo);
    cg.add(sink_norm, sink);
    cg.add(sink_exc, sink);

    struct DualExitProblem {
        outer: FuncId,
        thrown_src_iid: InstId,
        ret_src_iid: InstId,
        mf_throw_iid: InstId,
        mf_ret_iid: InstId,
        echo_ret_iid: InstId,
        mid_ret_iid: InstId,
        call1: InstId,
        call1_res: ValueId,
        call2: InstId,
        call2_res: ValueId,
        call_mid: InstId,
        mid_res: ValueId,
        exc_outer: ValueId,
        out_catch_first: InstId,
    }

    impl IfdsProblem for DualExitProblem {
        type Fact = SharedFact;

        fn zero(&self) -> SharedFact {
            SharedFact::Zero
        }

        fn initial_seeds(&self) -> Vec<(FuncId, SharedFact)> {
            vec![(self.outer, SharedFact::Zero)]
        }

        fn normal_flow_out(
            &self,
            _module: &Module,
            curr: InstId,
            _succ: InstId,
            _source_id: FactId,
            source: &SharedFact,
            out: &mut FlowSink<SharedFact>,
        ) {
            match *source {
                SharedFact::Zero => {
                    if curr == self.thrown_src_iid || curr == self.ret_src_iid {
                        out.emit(SharedFact::Token);
                    }
                }
                SharedFact::Token | SharedFact::Val(_) => out.pass_through(),
            }
        }

        fn call_flow_out(
            &self,
            _module: &Module,
            _call: InstId,
            _callee: FuncId,
            _source_id: FactId,
            source: &SharedFact,
            out: &mut FlowSink<SharedFact>,
        ) {
            if *source == SharedFact::Token {
                out.pass_through();
            }
        }

        fn return_flow_out(
            &self,
            _module: &Module,
            call_site: Option<InstId>,
            _callee: FuncId,
            exit: InstId,
            return_site: Option<InstId>,
            _source_id: FactId,
            source: &SharedFact,
            out: &mut FlowSink<SharedFact>,
        ) {
            match *source {
                SharedFact::Token => {
                    if exit == self.mf_ret_iid && call_site == Some(self.call1) {
                        out.pass_through();
                        out.emit(SharedFact::Val(self.call1_res));
                    } else if exit == self.echo_ret_iid && call_site == Some(self.call2) {
                        out.pass_through();
                        out.emit(SharedFact::Val(self.call2_res));
                    } else if call_site == Some(self.call_mid)
                        && return_site == Some(self.out_catch_first)
                    {
                        out.emit(SharedFact::Val(self.exc_outer));
                    }
                }
                SharedFact::Val(v) => {
                    if exit == self.mid_ret_iid
                        && v == self.call2_res
                        && call_site == Some(self.call_mid)
                        && return_site != Some(self.out_catch_first)
                    {
                        out.emit(SharedFact::Val(self.mid_res));
                    }
                }
                SharedFact::Zero => {}
            }
        }

        fn call_to_return_flow_out(
            &self,
            _module: &Module,
            _call: InstId,
            _return_site: InstId,
            _source_id: FactId,
            source: &SharedFact,
            out: &mut FlowSink<SharedFact>,
        ) {
            if *source != SharedFact::Zero {
                out.pass_through();
            }
        }

        fn call_uncaught_exit_flow_out(
            &self,
            _module: &Module,
            _call_site: InstId,
            _callee: FuncId,
            callee_exit: InstId,
            _source_id: FactId,
            source: &SharedFact,
            out: &mut FlowSink<SharedFact>,
        ) {
            if (*source == SharedFact::Zero && callee_exit == self.mf_throw_iid)
                || *source == SharedFact::Token
            {
                out.emit(SharedFact::Token);
            }
        }
    }

    let out_catch_first = m.block(out_catch).unwrap().insts[0];
    let prob = DualExitProblem {
        outer,
        thrown_src_iid,
        ret_src_iid,
        mf_throw_iid,
        mf_ret_iid,
        echo_ret_iid,
        mid_ret_iid,
        call1,
        call1_res,
        call2,
        call2_res,
        call_mid,
        mid_res,
        exc_outer,
        out_catch_first,
    };

    let res = IfdsSolver::new(&m, &prob, &cg, IfdsConfig::default()).solve();
    assert!(
        res.is_reached(call2, &SharedFact::Token),
        "Token must still traverse call1 via normal arrival + call_to_return_flow even after uncaught exit recorded (Zero, call1, Token)"
    );
    assert!(
        res.is_reached(sink_norm, &SharedFact::Val(mid_res)),
        "normal return path from mid() must reach sink_norm"
    );
    assert!(
        res.is_reached(sink_exc, &SharedFact::Val(exc_outer)),
        "uncaught throw path through mid() must ALSO reach outer's catch handler sink_exc"
    );
}

/// Verify that `FlowSink::pass_through()` performs ZERO `Fact::clone()` calls
/// across arbitrarily long intraprocedural and call-to-return bypass chains (`D6`).
#[test]
fn flow_sink_pass_through_is_zero_clone() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static CLONE_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug)]
    struct CountedFact {
        tag: u32,
    }

    impl Clone for CountedFact {
        fn clone(&self) -> Self {
            CLONE_COUNT.fetch_add(1, Ordering::Relaxed);
            Self { tag: self.tag }
        }
    }

    impl PartialEq for CountedFact {
        fn eq(&self, other: &Self) -> bool {
            self.tag == other.tag
        }
    }

    impl Eq for CountedFact {}

    impl std::hash::Hash for CountedFact {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.tag.hash(state);
        }
    }

    CLONE_COUNT.store(0, Ordering::Relaxed);

    let mut m = mk_module();
    let ext = add_external_sink(&mut m, "noop");
    let f = add_func_named(&mut m, "chain");
    let b = entry_of(&m, f);
    let mut v = load_number(&mut m, b, 1.0);
    let src_iid = m.blocks[b.index()].insts[0];
    for _ in 0..25 {
        v = emit(&mut m, b, Op::Mov { src: v });
    }
    let ext_ref = load_method_ref(&mut m, b, ext);
    let call_iid = emit_void_call(&mut m, b, ext_ref, vec![v]);
    for _ in 0..25 {
        v = emit(&mut m, b, Op::Mov { src: v });
    }
    let ret_iid = emit_void(&mut m, b, Op::Return { value: Some(v) });

    let mut cg = MapCallGraph::default();
    cg.add(call_iid, ext);

    struct ZeroCloneProblem {
        func: FuncId,
        src_iid: InstId,
    }

    impl IfdsProblem for ZeroCloneProblem {
        type Fact = CountedFact;

        fn zero(&self) -> CountedFact {
            CountedFact { tag: 0 }
        }

        fn initial_seeds(&self) -> Vec<(FuncId, CountedFact)> {
            vec![(self.func, self.zero())]
        }

        fn normal_flow_out(
            &self,
            _module: &Module,
            curr: InstId,
            _succ: InstId,
            _source_id: FactId,
            source: &CountedFact,
            out: &mut FlowSink<CountedFact>,
        ) {
            if source.tag == 0 {
                if curr == self.src_iid {
                    out.emit(CountedFact { tag: 1 });
                }
            } else {
                out.pass_through();
            }
        }

        fn call_to_return_flow_out(
            &self,
            _module: &Module,
            _call: InstId,
            _return_site: InstId,
            _source_id: FactId,
            source: &CountedFact,
            out: &mut FlowSink<CountedFact>,
        ) {
            if source.tag != 0 {
                out.pass_through();
            }
        }
    }

    let prob = ZeroCloneProblem { func: f, src_iid };
    let solver = IfdsSolver::new(&m, &prob, &cg, IfdsConfig::default());
    // Reset after solver construction (`zero` interning clones once) and plant
    // only propagation-loop clones: interning `tag: 1` clones once on first
    // insertion into `fact_ids`, and all ~52 subsequent `pass_through()` hops
    // perform ZERO clones!
    CLONE_COUNT.store(0, Ordering::Relaxed);
    let res = solver.solve();
    let clones_during_solve = CLONE_COUNT.load(Ordering::Relaxed);
    assert!(
        clones_during_solve <= 1,
        "expected <= 1 clone (initial interning of tag=1) across 52 pass-through steps, got {clones_during_solve}"
    );
    assert_eq!(
        res.raw_path_edges()
            .iter()
            .filter(|&&(_, n, _)| n == ret_iid)
            .count(),
        2
    );
}

#[test]
fn lazy_supergraph_shared_block_func_and_compact_csr_queries() {
    use crate::module_link::ModuleLinkTable;

    let mut m = mk_module();
    let seeded_fn = add_func_named(&mut m, "entry_fn");
    let b_entry = entry_of(&m, seeded_fn);
    let b_tail = add_block(&mut m, seeded_fn);
    let secret = load_string(&mut m, b_entry, "secret");
    emit_void(&mut m, b_entry, Op::Branch { dest: b_tail });
    link(&mut m, b_entry, b_tail);

    // Insert 200 unvisited functions between `b_entry` and `b_tail`'s instructions
    // so `seeded_fn`'s instructions span a wide ID gap (exercising `FuncSupergraph`'s
    // sparse sorted-ID path AND proving `EdgeCsr::offsets` sizes to `max_target_idx + 2`
    // rather than `module.insts.len() + 1` when trailing functions are unreached!).
    for idx in 0..200 {
        let uf = add_func_named(&mut m, &format!("unvisited_{idx}"));
        let ub = entry_of(&m, uf);
        let _ = load_number(&mut m, ub, idx as f64);
        emit_void(&mut m, ub, Op::Return { value: None });
    }

    let copied = emit(&mut m, b_tail, Op::Mov { src: secret });
    let ret_iid = emit_void(
        &mut m,
        b_tail,
        Op::Return {
            value: Some(copied),
        },
    );

    // Append another 200 unvisited functions AFTER `ret_iid`.
    for idx in 200..400 {
        let uf = add_func_named(&mut m, &format!("unvisited_{idx}"));
        let ub = entry_of(&m, uf);
        let _ = load_number(&mut m, ub, idx as f64);
        emit_void(&mut m, ub, Op::Return { value: None });
    }
    let last_unvisited_iid = InstId::new((m.insts.len() - 1) as u32);

    let links = ModuleLinkTable::build(&m);
    let cg = MapCallGraph::default();
    let seeds = vec![(seeded_fn, Fact::Zero)];

    struct Seeded<'a> {
        inner: &'a MicroTaint,
        seeds: Vec<(FuncId, Fact)>,
    }
    impl IfdsProblem for Seeded<'_> {
        type Fact = Fact;
        fn zero(&self) -> Fact {
            self.inner.zero()
        }
        fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
            self.seeds.clone()
        }
        fn normal_flow(&self, m: &Module, c: InstId, s: InstId, src: &Fact, out: &mut Vec<Fact>) {
            self.inner.normal_flow(m, c, s, src, out);
        }
    }

    let prob = Seeded {
        inner: &MicroTaint,
        seeds,
    };
    let res_owned_bf = IfdsSolver::new(&m, &prob, &cg, IfdsConfig::default()).solve();
    let res_shared_bf = IfdsSolver::new(&m, &prob, &cg, IfdsConfig::default())
        .solve_with_block_func(Some(links.block_func_slice()));

    assert_eq!(
        res_owned_bf.raw_path_edges(),
        res_shared_bf.raw_path_edges()
    );
    assert_eq!(
        res_shared_bf.facts_at(ret_iid, &Fact::Zero),
        vec![Fact::V(secret), Fact::V(copied)]
    );
    assert!(res_shared_bf.has_any_fact_at(ret_iid));
    assert!(res_shared_bf.has_non_zero_fact_at(ret_iid, &Fact::Zero));
    assert!(!res_shared_bf.has_any_fact_at(last_unvisited_iid));
    assert!(!res_shared_bf.has_non_zero_fact_at(last_unvisited_iid, &Fact::Zero));
    assert!(res_shared_bf.edge_indices_at(last_unvisited_iid).is_empty());

    let eidxs = res_shared_bf.edge_indices_at(ret_iid);
    assert_eq!(eidxs.len(), 3); // Zero, V(secret), V(copied)
    for &ei in eidxs {
        let (src_f, tgt_node, dst_f) = res_shared_bf.edge_at(ei).expect("valid edge_idx");
        assert_eq!(tgt_node, ret_iid);
        assert_eq!(*src_f, Fact::Zero);
        assert!(matches!(dst_f, Fact::Zero | Fact::V(_)));
    }
    assert!(res_shared_bf.edge_at(u32::MAX).is_none());

    // CSR `offsets` length must be `ret_iid.index() + 2`, NOT `m.insts.len() + 1`!
    let csr = res_shared_bf.csr.get().expect("CSR initialized");
    assert_eq!(csr.offsets.len(), ret_iid.index() + 2);
    assert!(csr.offsets.len() < m.insts.len());

    let cloned = res_shared_bf.clone();
    assert_eq!(
        cloned.facts_at(ret_iid, &Fact::Zero),
        vec![Fact::V(secret), Fact::V(copied)]
    );
}

#[test]
fn follow_returns_past_seeds_does_not_auto_cascade_zero_to_unseeded_callers() {
    let mut m = mk_module();

    // 1. Taint-free seeded leaf: `unseeded_outer -> unseeded_mid -> seeded_leaf`.
    let seeded_leaf = add_func_named(&mut m, "seeded_leaf");
    let b_leaf = entry_of(&m, seeded_leaf);
    let benign = load_number(&mut m, b_leaf, 1.0);
    emit_void(
        &mut m,
        b_leaf,
        Op::Return {
            value: Some(benign),
        },
    );

    let unseeded_mid = add_func_named(&mut m, "unseeded_mid");
    let b_mid = entry_of(&m, unseeded_mid);
    let leaf_ref = load_method_ref(&mut m, b_mid, seeded_leaf);
    let mid_call_val = emit(
        &mut m,
        b_mid,
        Op::Call {
            callee: leaf_ref,
            this: None,
            args: Vec::new(),
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let mid_call_iid = match m.value(mid_call_val).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        other => panic!("expected inst def: {other:?}"),
    };
    let mid_ret_iid = emit_void(
        &mut m,
        b_mid,
        Op::Return {
            value: Some(mid_call_val),
        },
    );

    let unseeded_outer = add_func_named(&mut m, "unseeded_outer");
    let b_outer = entry_of(&m, unseeded_outer);
    let mid_ref = load_method_ref(&mut m, b_outer, unseeded_mid);
    let outer_call_val = emit(
        &mut m,
        b_outer,
        Op::Call {
            callee: mid_ref,
            this: None,
            args: Vec::new(),
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let outer_call_iid = match m.value(outer_call_val).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        other => panic!("expected inst def: {other:?}"),
    };
    let outer_ret_iid = emit_void(
        &mut m,
        b_outer,
        Op::Return {
            value: Some(outer_call_val),
        },
    );

    // 2. Source-bearing seeded leaf: `unseeded_caller2 -> seeded_source_leaf`.
    let seeded_source_leaf = add_func_named(&mut m, "seeded_source_leaf");
    let b_src_leaf = entry_of(&m, seeded_source_leaf);
    let secret = load_string(&mut m, b_src_leaf, "secret");
    emit_void(
        &mut m,
        b_src_leaf,
        Op::Return {
            value: Some(secret),
        },
    );

    let unseeded_caller2 = add_func_named(&mut m, "unseeded_caller2");
    let b_caller2 = entry_of(&m, unseeded_caller2);
    let src_leaf_ref = load_method_ref(&mut m, b_caller2, seeded_source_leaf);
    let call_result = emit(
        &mut m,
        b_caller2,
        Op::Call {
            callee: src_leaf_ref,
            this: None,
            args: Vec::new(),
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let caller2_call_iid = match m.value(call_result).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        other => panic!("expected inst def: {other:?}"),
    };
    let copied = emit(&mut m, b_caller2, Op::Mov { src: call_result });
    let caller2_mov_iid = match m.value(copied).unwrap().def {
        abcd_ir::ValueDef::Inst(i) => i,
        other => panic!("expected inst def: {other:?}"),
    };
    let caller2_ret_iid = emit_void(
        &mut m,
        b_caller2,
        Op::Return {
            value: Some(copied),
        },
    );

    let mut cg = MapCallGraph::default();
    cg.add(mid_call_iid, seeded_leaf);
    cg.add(outer_call_iid, unseeded_mid);
    cg.add(caller2_call_iid, seeded_source_leaf);

    struct PartialSeededProblem<'a> {
        inner: &'a MicroTaint,
        seeds: Vec<(FuncId, Fact)>,
    }
    impl IfdsProblem for PartialSeededProblem<'_> {
        type Fact = Fact;
        fn zero(&self) -> Fact {
            self.inner.zero()
        }
        fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
            self.seeds.clone()
        }
        fn normal_flow(&self, m: &Module, c: InstId, s: InstId, src: &Fact, out: &mut Vec<Fact>) {
            self.inner.normal_flow(m, c, s, src, out);
        }
        fn call_flow(&self, m: &Module, c: InstId, f: FuncId, src: &Fact, out: &mut Vec<Fact>) {
            self.inner.call_flow(m, c, f, src, out);
        }
        fn return_flow(
            &self,
            m: &Module,
            c: Option<InstId>,
            f: FuncId,
            e: InstId,
            r: Option<InstId>,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            self.inner.return_flow(m, c, f, e, r, src, out);
        }
        fn call_to_return_flow(
            &self,
            m: &Module,
            c: InstId,
            r: InstId,
            src: &Fact,
            out: &mut Vec<Fact>,
        ) {
            self.inner.call_to_return_flow(m, c, r, src, out);
        }
    }

    let prob = PartialSeededProblem {
        inner: &MicroTaint,
        seeds: vec![(seeded_leaf, Fact::Zero), (seeded_source_leaf, Fact::Zero)],
    };
    let res = IfdsSolver::new(
        &m,
        &prob,
        &cg,
        IfdsConfig {
            follow_returns_past_seeds: true,
        },
    )
    .solve();

    // `seeded_leaf` emits nothing from `return_flow_out` on `Fact::Zero`, so
    // neither `unseeded_mid` nor `unseeded_outer` may be woken up with `Λ`!
    for &iid in m
        .block(b_mid)
        .unwrap()
        .insts
        .iter()
        .chain(m.block(b_outer).unwrap().insts.iter())
    {
        assert!(
            !res.has_any_fact_at(iid),
            "unseeded caller instruction {iid:?} must not receive Λ or any fact"
        );
        assert!(res.facts_at(iid, &Fact::Zero).is_empty());
    }
    let _ = (mid_ret_iid, outer_ret_iid);

    // `seeded_source_leaf` DOES generate `Fact::V(secret)` and return it, so
    // `Fact::V(call_result)` propagates into `unseeded_caller2` via unbalanced
    // return flow without injecting `Fact::Zero`.
    assert!(!res.is_reached(caller2_mov_iid, &Fact::Zero));
    assert_eq!(
        res.facts_at(caller2_mov_iid, &Fact::Zero),
        vec![Fact::V(call_result)]
    );
    assert_eq!(
        res.facts_at(caller2_ret_iid, &Fact::Zero),
        vec![Fact::V(call_result), Fact::V(copied)]
    );
}
