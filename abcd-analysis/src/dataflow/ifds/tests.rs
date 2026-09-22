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
                if self.is_source(module, curr) {
                    if let Some(v) = module.inst(curr).and_then(|i| i.result) {
                        out.push(Fact::V(v));
                    }
                }
            }
            Fact::V(v) => {
                // Value facts persist (SSA values are never overwritten).
                out.push(Fact::V(v));
                Self::propagate_inst(module, curr, v, out);
                // Exception dispatch: `throw v` taints the handler's
                // exception parameter along the exceptional edge.
                if matches!(module.inst(curr).map(|i| &i.op), Some(Op::Throw { value }) if *value == v)
                {
                    if let Some(exc) = Self::handler_param(module, succ) {
                        out.push(Fact::V(exc));
                    }
                }
            }
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
        if *this == Some(v) {
            if let Some(&p) = cf.params.first() {
                out.push(Fact::V(p));
            }
        }
        for (i, &a) in args.iter().enumerate() {
            if a == v {
                if let Some(&p) = cf.params.get(i + 1) {
                    out.push(Fact::V(p));
                }
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

    fn call_to_return_flow(
        &self,
        _module: &Module,
        _call: InstId,
        _return_site: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        // The bypass is the identity: caller-local facts survive the call.
        out.push(source.clone());
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
            if let Some(inst) = m.inst(iid) {
                if matches!(inst.op, Op::Call { .. }) {
                    if inst.result.is_some() {
                        cg.add(iid, id);
                    } else {
                        cg.add(iid, sink);
                    }
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
/// (determinism, heros.md §5 item 4).
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
    assert_eq!(r1.path_edges(), r2.path_edges());
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
