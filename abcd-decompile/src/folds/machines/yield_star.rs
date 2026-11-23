//! `yield*` iterator delegation driver fold (sync and async).

use crate::folds::*;

// ── YieldStar delegation fold (d-P15, R4) ──────────────────────────
//
// VENDOR LOWERING MODEL (es2panda
// `compiler/function/functionBuilder.cpp` `FunctionBuilder::YieldStar`
// :177-342 + the `Iterator` helper (`GetMethod`/`Close`/
// `CallMethodWithValue`/`Complete`/`Value`); `enum class ResumeMode {
// RETURN=0, THROW=1, NEXT=2 }` in `functionBuilder.h`; probe-verified
// on the d-P15 fixtures (now corpus-exported:
// `24.0.0.0/local/yield-star/*/baseline/reference.pa`):
//
//   iter = GetIterator(expr)        // async kind: GetAsyncIterator
//   next = iter.next
//   received = undefined; mode = NEXT(2)
//   loop:
//     exitReturn = false
//     if mode === NEXT(2):  method = next; goto call
//     if mode === THROW(1): method = iter.throw
//                           if method === undefined:
//                             IteratorClose()  // try iter.return() + rethrow
//                             throw.notexists  // TypeError
//     /* RETURN(0) */       exitReturn = true
//                           method = iter.return
//                           if method === undefined: return received
//                           // (async: Await(received) first)
//     call: inner = method.call(iter, received)   // async: Await(inner)
//           ThrowIfNotObject(inner)
//           if inner.done: goto complete
//           sync:  GeneratorYield(inner) — the delegate's result object
//                  passes through AS-IS (no CreateIterResultObj wrap);
//                  received/mode = ResumeGenerator/GetResumeMode(gen)
//           async: value = Await(inner.value); AsyncGeneratorYield(value)
//                  → received/mode; a RETURN resumption awaits the resume
//                  value and re-enters the loop with mode RETURN
//           goto loop
//     complete:
//       if !exitReturn: <yield* value> = inner.value
//       else:           return inner.value   // .return() propagation
//
// The fold eliminates the WHOLE driver loop back to `yield* <expr>`
// (or `const ret = yield* <expr>` when the completion value is used):
// the delegated yields pass through natively, the delegate's
// completion value is the expression's value, and the .return() /
// .throw() protocol plumbing (incl. IteratorClose + the not-exists
// TypeError) is exactly what the source-level operator specifies —
// every piece dissolves.
//
// SOUNDNESS / HONESTY (design §8 R4 budget, mirroring d-P11/13/14):
// per-site all-or-nothing. The site matches ONLY the vendor shape,
// anchored on: the GetIterator/GetAsyncIterator setup, the phi-init
// (mode=NEXT, received=undefined, flag=false), the loop-header mode
// dispatch (NEXT/THROW stricteq tests), the method call
// (`method.call(iter, received)`), the ThrowIfNotObject elision, the
// done test, the pass-through suspend + resumption pair, the
// loop-back mode/value assigns, and the completion dispatch
// (exitReturn test with the `inner.value` normal arm and the
// `return inner.value` propagation arm). Any deviation leaves the
// whole site LOUD (today's fallbacks, counted).

/// What the driver-loop match extracted.
pub(in crate::folds) struct YsLoop {
    /// Loop phi: the resumption mode (`receivedType`).
    pub(in crate::folds) rt: (ValueId, String),
    /// Loop phi: the resumption value (`received`).
    pub(in crate::folds) rv: (ValueId, String),
    /// Loop phi: the delegate iterator.
    pub(in crate::folds) it: (ValueId, String),
    /// Loop phi: the generator object.
    pub(in crate::folds) g: (ValueId, String),
    /// Loop phi: the close-attempt flag.
    pub(in crate::folds) flag: (ValueId, String),
    /// The `exitReturn` phi tested by the completion dispatch.
    pub(in crate::folds) exit_phi: (ValueId, String),
    /// The completion-value binding + continuation (async: extracted
    /// from the done arm inside the loop; sync: from the sibling
    /// completion dispatch — filled by [`ys_match_exit`]).
    pub(in crate::folds) bind: Option<(String, ValueId)>,
    /// The post-delegation continuation (async: done-arm content).
    pub(in crate::folds) continuation: Vec<SNode>,
}

/// Fold the es2panda YieldStar driver loop back to `yield* <expr>`.
/// Runs after the generator/async-generator machine folds (their
/// entry gates already vetted the function's genobj plumbing; the
/// YieldStar suspend sites are not theirs and stay for this fold).
pub fn yield_star_fold(nodes: &mut Vec<SNode>, kind: FunctionKind, stats: &mut FoldStats) {
    let async_ = match kind {
        FunctionKind::Generator => false,
        FunctionKind::AsyncGenerator => true,
        _ => return,
    };
    let mut uses = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    ys_fold_seq(nodes, async_, &uses, stats);
}

/// The recursive driver: children first, then the sequence scan.
pub(in crate::folds) fn ys_fold_seq(
    nodes: &mut Vec<SNode>,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                ys_fold_seq(then, async_, uses, stats);
                ys_fold_seq(otherwise, async_, uses, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after yield_star_fold
            // (emit.rs:530 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => ys_fold_seq(body, async_, uses, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                ys_fold_seq(body, async_, uses, stats);
                for c in catches {
                    ys_fold_seq(&mut c.body, async_, uses, stats);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // yield_star_fold — c-COV diagnosis
                if let Some(f) = finally {
                    ys_fold_seq(f, async_, uses, stats);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // yield_star_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    ys_fold_seq(&mut c.body, async_, uses, stats);
                }
            }
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    let mut i = 0;
    while i < nodes.len() {
        // Arrangement A (bare siblings): [.., setup-run, phi-init-run,
        // While, exit-If (sync)]. Arrangement B (try fragments, the
        // structurer's "protected statements are not contiguous"
        // split): [Try(setup+init), Try(While), Try(exit-If)].
        if matches!(&nodes[i], SNode::While { cond: None, .. })
            && ys_apply_bare(nodes, i, async_, uses, stats)
        {
            continue;
        }
        if matches!(&nodes[i], SNode::Try { .. })
            && ys_apply_fragments(nodes, i, async_, uses, stats)
        {
            continue;
        }
        i += 1;
    }
}

// ── small matchers ─────────────────────────────────────────────────

/// A `Stmts` run consisting solely of exceptional phi assigns (the
/// catch-region context plumbing es2abc sprinkles everywhere in an
/// async generator / around a source try).
pub(in crate::folds) fn ys_is_exc_run(n: &SNode) -> bool {
    let SNode::Stmts(run) = n else {
        return false;
    };
    !run.is_empty()
        && run.iter().all(|l| {
            matches!(
                l,
                Leaf::Raw(Stmt::PhiAssign {
                    exceptional: true,
                    ..
                })
            )
        })
}

/// The sequence's significant nodes (exceptional-assign runs dropped).
pub(in crate::folds) fn ys_sig(nodes: &[SNode]) -> Vec<&SNode> {
    nodes.iter().filter(|n| !ys_is_exc_run(n)).collect()
}

/// A run of phi assigns whose NON-exceptional members all target one
/// block (exceptional catch-context assigns may be interspersed —
/// they are machinery plumbing); returns that block.
pub(in crate::folds) fn ys_assign_run(n: &SNode) -> Option<abcd_ir::BlockId> {
    let SNode::Stmts(run) = n else {
        return None;
    };
    if run.is_empty() {
        return None;
    }
    let mut to = None;
    for l in run {
        let Leaf::Raw(Stmt::PhiAssign {
            to: t, exceptional, ..
        }) = l
        else {
            return None;
        };
        if *exceptional {
            continue;
        }
        if let Some(prev) = to {
            if prev != *t {
                return None;
            }
        } else {
            to = Some(*t);
        }
    }
    to
}

/// A `Stmts` run's LEADING phi decls as name → id (stops at the first
/// non-phi leaf).
pub(in crate::folds) fn ys_phi_decls(n: &SNode) -> Option<BTreeMap<String, ValueId>> {
    let SNode::Stmts(run) = n else {
        return None;
    };
    let mut out = BTreeMap::new();
    for l in run {
        match l {
            Leaf::Raw(Stmt::PhiDecl { name, value_id }) => {
                out.insert(name.clone(), *value_id);
            }
            _ => break,
        }
    }
    Some(out)
}

/// A mode test: `IsFalse(StrictEq(Temp(phi), <num>))` in either
/// operand order; returns the phi and the immediate.
pub(in crate::folds) fn ys_mode_test(cond: &Expr, want: f64) -> Option<ValueId> {
    let Expr::Unary {
        op: UnOp::IsFalse,
        operand,
    } = cond
    else {
        return None;
    };
    let Expr::Compare {
        op: CmpOp::StrictEq,
        left,
        right,
    } = operand.as_ref()
    else {
        return None;
    };
    let (t, n) = if let Expr::Lit(Lit::Number(bits)) = right.as_ref() {
        (temp_value(left)?, f64::from_bits(*bits))
    } else if let Expr::Lit(Lit::Number(bits)) = left.as_ref() {
        (temp_value(right)?, f64::from_bits(*bits))
    } else {
        return None;
    };
    (n == want).then_some(t)
}

/// An `istrue`/`isfalse`-wrapped temp test: strips the wrappers and
/// returns (temp, positive).
pub(in crate::folds) fn ys_flag_test(cond: &Expr) -> Option<(ValueId, bool)> {
    let mut e = cond;
    let mut positive = true;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsFalse,
                operand,
            } => {
                positive = !positive;
                e = operand;
            }
            Expr::Unary {
                op: UnOp::IsTrue,
                operand,
            } => e = operand,
            _ => break,
        }
    }
    Some((temp_value(e)?, positive))
}

/// `<temp> == undefined` (either order, `Eq`).
pub(in crate::folds) fn ys_undefined_test(cond: &Expr) -> Option<(ValueId, bool)> {
    let Expr::Unary {
        op: UnOp::IsFalse,
        operand,
    } = cond
    else {
        return None;
    };
    let Expr::Compare {
        op: CmpOp::Eq,
        left,
        right,
    } = operand.as_ref()
    else {
        return None;
    };
    if matches!(right.as_ref(), Expr::Lit(Lit::Undefined)) {
        // IsFalse(temp == undefined) → "temp is defined".
        temp_value(left).map(|t| (t, true))
    } else if matches!(left.as_ref(), Expr::Lit(Lit::Undefined)) {
        temp_value(right).map(|t| (t, true))
    } else {
        None
    }
}

/// Debug tracing (YS_DEBUG=1).
pub(in crate::folds) fn ys_trace(stage: &str) {
    if std::env::var_os("YS_DEBUG").is_some() {
        eprintln!("yield-star: bail at {stage}");
    }
}

/// A `GeneratorDriver` expr with the given resume flag and genobj temp.
pub(in crate::folds) fn ys_driver(e: &Expr, resume: bool, g: ValueId) -> bool {
    matches!(
        e,
        Expr::GeneratorDriver { resume: r, genobj }
            if *r == resume && temp_value(genobj) == Some(g)
    )
}

/// A `PropName` load `<base>.<name>`; returns the base temp.
pub(in crate::folds) fn ys_prop(e: &Expr, name: &str) -> Option<ValueId> {
    let Expr::PropName {
        object, name: n, ..
    } = e
    else {
        return None;
    };
    (n == name).then(|| temp_value(object))?
}

/// A Declare leaf with the given value shape; returns (name, id).
pub(in crate::folds) fn ys_declare_of(l: &Leaf) -> Option<(&str, ValueId, &Expr)> {
    let Leaf::Raw(Stmt::Declare {
        name,
        value,
        value_id,
        ..
    }) = l
    else {
        return None;
    };
    Some((name, *value_id, value))
}

/// Does the subtree contain an `Elided` with this op name?
pub(in crate::folds) fn ys_contains_elided(nodes: &[SNode], op: &str) -> bool {
    let mut found = false;
    walk_leaves(nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::Elided { op: o, .. }) if *o == op) {
            found = true;
        }
    });
    found
}

// ── the driver-loop match ──────────────────────────────────────────

/// Match the YieldStar driver loop. `async_` selects the async
/// (AsyncGenerator) tail shape.
pub(in crate::folds) fn ys_match_loop(w: &SNode, async_: bool) -> Option<YsLoop> {
    let SNode::While {
        cond: None, body, ..
    } = w
    else {
        return None;
    };
    let sig = ys_sig(body);
    // [header, dispatch, pre-call, done-test | async-call-await, …]
    if sig.len() < 4 {
        return None;
    }
    // ── header run: phi decls + `exitReturn = false` ──
    let SNode::Stmts(header) = sig[0] else {
        return None;
    };
    if header.is_empty() {
        return None;
    }
    let (phis, exit_decl) = {
        let mut phis = BTreeMap::new();
        for l in &header[..header.len() - 1] {
            let Leaf::Raw(Stmt::PhiDecl { name, value_id }) = l else {
                return None;
            };
            phis.insert(name.clone(), *value_id);
        }
        let (_, id, value) = ys_declare_of(&header[header.len() - 1])?;
        if !matches!(value, Expr::Lit(Lit::Bool(false))) {
            return None;
        }
        (phis, id)
    };
    let in_phis = |id: &ValueId| phis.values().any(|v| v == id);

    // ── the mode dispatch ──
    let SNode::If {
        cond,
        then,
        otherwise,
    } = sig[1]
    else {
        ys_trace("loop:sig1-not-if");
        return None;
    };
    let Some(rt_id) = ys_mode_test(cond, 2.0).filter(in_phis) else {
        ys_trace("loop:mode-test");
        return None;
    };
    let rt_name = phis
        .iter()
        .find(|(_, v)| **v == rt_id)
        .map(|(n, _)| n.clone())?;
    let Some(first) = ys_sig(otherwise).into_iter().next().cloned() else {
        ys_trace("loop:next-arm");
        return None;
    };
    let Some(call_block) = ys_assign_run(&first) else {
        ys_trace("loop:next-arm-assigns");
        return None;
    };
    let dsig = ys_sig(then);
    let [
        SNode::If {
            cond: cond2,
            then: ret_arm,
            otherwise: throw_arm,
        },
    ] = dsig.as_slice()
    else {
        return None;
    };
    if ys_mode_test(cond2, 1.0) != Some(rt_id) {
        return None;
    }

    // ── RETURN arm: extract the iterator phi, the exitReturn phi,
    // and the received-value phi (the DirectReturn temp) ──
    let rasig = ys_sig(ret_arm);
    let Some((it_id, exit_phi, rv_id)) = ys_match_return_arm(&rasig, &phis, call_block, async_)
    else {
        ys_trace("loop:return-arm");
        return None;
    };
    let it_name = phis
        .iter()
        .find(|(_, v)| **v == it_id)
        .map(|(n, _)| n.clone())?;
    // Async: the received-value phi comes from the call's argument in
    // the tail (the RETURN arm's DirectReturn is the awaited
    // completion machinery, not a plain `return received`).
    let rv_name = if async_ {
        String::new()
    } else {
        phis.iter()
            .find(|(_, v)| **v == rv_id)
            .map(|(n, _)| n.clone())?
    };
    let exit_name = exit_phi.1.clone();

    // ── THROW arm: `throw` method lookup + the close machinery ──
    let Some(flag_id) = ys_match_throw_arm(
        &ys_sig(throw_arm),
        it_id,
        &exit_name,
        exit_decl,
        call_block,
        &phis,
    ) else {
        ys_trace("loop:throw-arm");
        return None;
    };
    let flag_name = phis
        .iter()
        .find(|(_, v)| **v == flag_id)
        .map(|(n, _)| n.clone())?;

    let out = if async_ {
        ys_match_loop_tail_async(
            &sig, &phis, rt_id, it_id, exit_phi, rt_name, rv_name, it_name, flag_name,
        )
    } else {
        ys_match_loop_tail_sync(
            &sig, &phis, rt_id, it_id, rv_id, exit_decl, exit_phi, rt_name, rv_name, it_name,
            flag_name,
        )
    };
    if out.is_none() {
        ys_trace("loop:tail");
    }
    out
}

/// The RETURN completion arm (sync shape; async shares the head):
///
/// `[assigns → B_ret, [phis…, T = true, retM = it.return],
///   if (retM !== undefined) { assigns → B_call incl. exitPhi ← T }
///   else { break }, return received]`
///
/// Returns (it, exitPhi, received).
pub(in crate::folds) fn ys_match_return_arm(
    arm: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    call_block: abcd_ir::BlockId,
    async_: bool,
) -> Option<(ValueId, (ValueId, String), ValueId)> {
    let in_phis = |id: &ValueId| phis.values().any(|v| v == id);
    let mut it_id = None;
    let mut true_decl = None;
    let mut exit_phi = None;
    let mut rv_id = None;
    let mut saw_break_if = false;
    for (idx, n) in arm.iter().enumerate() {
        match n {
            SNode::Stmts(run) => {
                // The decl run: [phis…, T = true, retM = it.return].
                for l in run {
                    if let Some((_, id, value)) = ys_declare_of(l) {
                        if matches!(value, Expr::Lit(Lit::Bool(true))) {
                            true_decl = Some(id);
                        }
                        if let Some(base) = ys_prop(value, "return")
                            && in_phis(&base)
                        {
                            it_id = Some((base, id));
                        }
                    }
                }
                // The propagation return: `return received`.
                if !async_
                    && let [Leaf::Raw(Stmt::Return(Some(e)))] = run.as_slice()
                    && let Some(t) = temp_value(e).filter(in_phis)
                {
                    rv_id = Some(t);
                }
                let _ = idx;
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                // `if (retM !== undefined) { assigns → B_call } else { break }`.
                let Some((t, _)) = ys_undefined_test(cond) else {
                    ys_trace("ret-arm:undefined-test");
                    return None;
                };
                if Some(t) != it_id.map(|(_, m)| m) {
                    ys_trace("ret-arm:method-id");
                    return None;
                }
                let tsig = ys_sig(then);
                let [assigns] = tsig.as_slice() else {
                    ys_trace("ret-arm:then-shape");
                    return None;
                };
                if ys_assign_run(assigns) != Some(call_block) {
                    ys_trace("ret-arm:call-block");
                    return None;
                }
                // The exitReturn phi gets the `true` decl here.
                let SNode::Stmts(arun) = assigns else {
                    return None;
                };
                for l in arun {
                    if let Leaf::Raw(Stmt::PhiAssign { target, value, .. }) = l
                        && temp_value(value) == true_decl
                    {
                        // The exitReturn phi is declared in the
                        // pre-call run, not the header — carry the
                        // name; the tail resolves the id.
                        exit_phi = Some((ValueId::new(u32::MAX), target.clone()));
                    }
                }
                if exit_phi.is_none() {
                    ys_trace("ret-arm:exit-phi");
                    return None;
                }
                let [SNode::Break { .. }] = ys_sig(otherwise).as_slice() else {
                    ys_trace("ret-arm:break");
                    return None;
                };
                saw_break_if = true;
                if async_ {
                    // The async RETURN arm continues with the awaited
                    // DirectReturn machinery (d-P14 shapes) — the head
                    // anchors above pin the vendor shape; the rest is
                    // consumed with the loop either way.
                    break;
                }
            }
            _ => return None,
        }
    }
    if !saw_break_if {
        ys_trace("ret-arm:no-if");
        return None;
    }
    if std::env::var_os("YS_DEBUG").is_some() {
        eprintln!(
            "yield-star: ret-arm it={it_id:?} exit={exit_phi:?} rv={rv_id:?} true={true_decl:?}"
        );
    }
    if async_ {
        // The async RETURN arm awaits the resume value and completes
        // via the AsyncGeneratorResolve machinery (d-P14 shapes,
        // partially folded) — the head anchors above (true decl,
        // it.return lookup, the undefined test with the B_call
        // assigns incl. the exitReturn link, the break) pin it; the
        // received phi comes from the tail match instead.
        let _ = rv_id;
        Some((it_id?.0, exit_phi?, ValueId::new(u32::MAX)))
    } else {
        Some((it_id?.0, exit_phi?, rv_id?))
    }
}

/// The THROW completion arm:
///
/// `[throwM = it.throw; eqM = throwM == undefined],
///  if (!eqM) { assigns → B_call incl. exitPhi ← exitDecl } ,
///  if (flag) { close-already machinery } else { close-try machinery }`
///
/// Returns the flag phi. The close machinery itself is opaque (fixed
/// vendor IteratorClose + ThrowNotExists shape) but must contain the
/// elided ThrowNotExists guard.
pub(in crate::folds) fn ys_match_throw_arm(
    arm: &[&SNode],
    it: ValueId,
    exit_name: &str,
    exit_decl: ValueId,
    call_block: abcd_ir::BlockId,
    phis: &BTreeMap<String, ValueId>,
) -> Option<ValueId> {
    let mut throw_m = None;
    let mut eq_m = None;
    let mut flag = None;
    let mut saw_close_if = false;
    for n in arm {
        match n {
            SNode::Stmts(run) => {
                for l in run {
                    if let Some((_, id, value)) = ys_declare_of(l) {
                        if ys_prop(value, "throw") == Some(it) {
                            throw_m = Some(id);
                        }
                        if let Expr::Compare {
                            op: CmpOp::Eq,
                            left,
                            right,
                        } = value
                        {
                            let is_undef_pair = |a: &Expr, b: &Expr| {
                                temp_value(a) == throw_m && matches!(b, Expr::Lit(Lit::Undefined))
                            };
                            if is_undef_pair(left, right) || is_undef_pair(right, left) {
                                eq_m = Some(id);
                            }
                        }
                    }
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                if let Some((t, positive)) = ys_flag_test(cond) {
                    if Some(t) == eq_m && !positive {
                        // `if (!eqM) { assigns → B_call incl.
                        // exitPhi ← exitDecl }` — method exists → call.
                        let tsig = ys_sig(then);
                        let [assigns] = tsig.as_slice() else {
                            return None;
                        };
                        if ys_assign_run(assigns) != Some(call_block) {
                            return None;
                        }
                        let SNode::Stmts(arun) = assigns else {
                            return None;
                        };
                        if !arun.iter().any(|l| {
                            matches!(
                                l,
                                Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                                    if target == exit_name && temp_value(value) == Some(exit_decl)
                            )
                        }) {
                            return None;
                        }
                        if !ys_sig(otherwise).is_empty() {
                            return None;
                        }
                        continue;
                    }
                    if phis.values().any(|v| *v == t) && positive {
                        // `if (flag) { … } else { … }` — the close
                        // machinery; ThrowNotExists must be in there.
                        flag = Some(t);
                        saw_close_if = true;
                        if !ys_contains_elided(then, "ThrowNotExists")
                            && !ys_contains_elided(otherwise, "ThrowNotExists")
                        {
                            return None;
                        }
                        continue;
                    }
                }
                return None;
            }
            _ => return None,
        }
    }
    throw_m?;
    eq_m?;
    if !saw_close_if {
        return None;
    }
    flag
}

/// The sync driver tail: pre-call run, done test, pass-through
/// suspend, loop-back assigns, continue.
#[allow(clippy::too_many_arguments)]
pub(in crate::folds) fn ys_match_loop_tail_sync(
    sig: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    rt: ValueId,
    it: ValueId,
    rv: ValueId,
    exit_decl: ValueId,
    exit_phi: (ValueId, String),
    rt_name: String,
    rv_name: String,
    it_name: String,
    flag_name: String,
) -> Option<YsLoop> {
    // [header, dispatch, precall, done-if, suspend, loopback, continue]
    let [
        _,
        _,
        precall,
        done_if,
        suspend,
        loopback,
        SNode::Continue { .. },
    ] = sig
    else {
        ys_trace("sync-tail:skeleton");
        return None;
    };
    let pre_phis = ys_phi_decls(precall)?;
    let exit_id = pre_phis.get(&exit_phi.1).copied()?;
    let exit_phi = (exit_id, exit_phi.1);
    let SNode::Stmts(prun) = precall else {
        return None;
    };
    let mut res = None;
    let mut done = None;
    for l in &prun[pre_phis.len()..] {
        match l {
            Leaf::Raw(Stmt::Declare {
                value: Expr::Call {
                    callee, this, args, ..
                },
                value_id,
                ..
            }) => {
                // `res = methodPhi.call(iter, received)`.
                if !pre_phis.values().any(|v| temp_value(callee) == Some(*v)) {
                    return None;
                }
                let Expr::Temp { value: this_t, .. } = this.as_deref()? else {
                    return None;
                };
                if *this_t != it {
                    return None;
                }
                let [Expr::Temp { value: arg, .. }] = args.as_slice() else {
                    return None;
                };
                if *arg != rv {
                    return None;
                }
                res = Some(*value_id);
            }
            Leaf::Raw(Stmt::Declare {
                value, value_id, ..
            }) => {
                if ys_prop(value, "done") == res {
                    done = Some(*value_id);
                }
            }
            Leaf::Raw(Stmt::Elided { op, .. }) if *op == "ThrowIfNotObject" => {}
            _ => return None,
        }
    }
    let Some(res) = res else {
        ys_trace("sync-tail:call");
        return None;
    };
    let Some(done) = done else {
        ys_trace("sync-tail:done-decl");
        return None;
    };
    // `if (done) break;`
    let SNode::If {
        cond,
        then,
        otherwise,
    } = done_if
    else {
        return None;
    };
    if ys_flag_test(cond) != Some((done, true)) {
        return None;
    }
    let [SNode::Break { .. }] = ys_sig(then).as_slice() else {
        return None;
    };
    if !ys_sig(otherwise).is_empty() {
        return None;
    }
    // The pass-through suspend: `yield res; resume = ResumeGenerator(g)`.
    let SNode::Stmts(srun) = suspend else {
        ys_trace("sync-tail:suspend-run");
        return None;
    };
    let [
        Leaf::Raw(Stmt::Expr(Expr::Yield { value })),
        Leaf::Raw(Stmt::Declare {
            value: drv,
            value_id: resume,
            ..
        }),
    ] = srun.as_slice()
    else {
        ys_trace("sync-tail:suspend-shape");
        return None;
    };
    if temp_value(value) != Some(res) {
        return None;
    }
    let Expr::GeneratorDriver {
        resume: true,
        genobj,
    } = drv
    else {
        return None;
    };
    let g_id = temp_value(genobj).filter(|g| phis.values().any(|v| v == g))?;
    // Loop-back: `rt ← GetResumeMode(g)`, `rv ← resume`, all to the
    // header block, then `continue`.
    let SNode::Stmts(lrun) = loopback else {
        ys_trace("sync-tail:loopback-run");
        return None;
    };
    let header_block = ys_assign_run(loopback)?;
    let mut saw_mode = false;
    let mut saw_value = false;
    for l in lrun {
        let Leaf::Raw(Stmt::PhiAssign { target, value, .. }) = l else {
            return None;
        };
        if *target == rt_name && ys_driver(value, false, g_id) {
            saw_mode = true;
        }
        if *target == rv_name && temp_value(value) == Some(*resume) {
            saw_value = true;
        }
    }
    if !saw_mode || !saw_value {
        ys_trace("sync-tail:loopback-anchors");
        return None;
    }
    let _ = header_block;
    let _ = exit_decl;
    Some(YsLoop {
        rt: (rt, rt_name),
        rv: (rv, rv_name),
        it: (it, it_name),
        g: (
            g_id,
            phis.iter()
                .find(|(_, v)| **v == g_id)
                .map(|(n, _)| n.clone())?,
        ),
        flag: (
            phis.iter()
                .find(|(n, _)| **n == flag_name)
                .map(|(_, v)| *v)?,
            flag_name,
        ),
        exit_phi,
        bind: None,
        continuation: Vec::new(),
    })
}

/// The async driver tail: the call + Await(inner) + pass-through
/// AsyncGeneratorYield machinery, the done test, and the IN-LOOP
/// completion dispatch (the async YieldStar's `iteratorComplete` is
/// inlined in the loop body).
#[allow(clippy::too_many_arguments)]
pub(in crate::folds) fn ys_match_loop_tail_async(
    sig: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    rt: ValueId,
    it: ValueId,
    exit_phi: (ValueId, String),
    rt_name: String,
    rv_name: String,
    it_name: String,
    flag_name: String,
) -> Option<YsLoop> {
    // [header, dispatch, precall, await-dispatch]
    let [_, _, precall, await_if] = sig else {
        ys_trace("a-tail:skeleton");
        return None;
    };
    let pre_phis = ys_phi_decls(precall)?;
    let exit_id = pre_phis.get(&exit_phi.1).copied()?;
    let exit_phi = (exit_id, exit_phi.1);
    let SNode::Stmts(prun) = precall else {
        return None;
    };
    // [phis…, res = methodPhi.call(iter, received), aw = await res
    //  (uncaught), yield aw, resume1 = ResumeGenerator(g)]
    let tail = &prun[pre_phis.len()..];
    let [
        Leaf::Raw(Stmt::Declare {
            value: Expr::Call {
                callee, this, args, ..
            },
            value_id: res,
            ..
        }),
        Leaf::Raw(Stmt::Declare {
            value:
                Expr::Await {
                    value: aw_val,
                    uncaught: true,
                },
            value_id: aw,
            ..
        }),
        Leaf::Raw(Stmt::Expr(Expr::Yield { value: yval })),
        Leaf::Raw(Stmt::Declare {
            value: drv1,
            value_id: resume1,
            ..
        }),
    ] = tail
    else {
        ys_trace("a-tail:precall-shape");
        return None;
    };
    if !pre_phis.values().any(|v| temp_value(callee) == Some(*v)) {
        ys_trace("a-tail:callee");
        return None;
    }
    let Expr::Temp { value: this_t, .. } = this.as_deref()? else {
        return None;
    };
    if *this_t != it {
        return None;
    }
    let [Expr::Temp { value: arg, .. }] = args.as_slice() else {
        return None;
    };
    let rv = *arg;
    if !phis.values().any(|v| *v == rv) {
        return None;
    }
    let rv_name = phis
        .iter()
        .find(|(_, v)| **v == rv)
        .map(|(n, _)| n.clone())
        .unwrap_or(rv_name);
    if temp_value(aw_val) != Some(*res) || temp_value(yval) != Some(*aw) {
        return None;
    }
    let Expr::GeneratorDriver {
        resume: true,
        genobj,
    } = drv1
    else {
        ys_trace("a-tail:drv1");
        return None;
    };
    let Some(g_id) = temp_value(genobj).filter(|g| phis.values().any(|v| v == g)) else {
        ys_trace("a-tail:g");
        return None;
    };

    // The await's THROW-only dispatch: `if (GetResumeMode(g) != THROW)
    // { continuation } else { throw resume1; unreachable; break }`.
    let SNode::If {
        cond,
        then,
        otherwise,
    } = await_if
    else {
        return None;
    };
    if ys_async_throw_dispatch(cond, otherwise, g_id, *resume1).is_none() {
        ys_trace("a-tail:throw-dispatch");
        return None;
    }

    // Continuation: [elided ThrowIfNotObject, done = resume1.done],
    // then the done test.
    let csig = ys_sig(then);
    let [done_run, done_if] = csig.as_slice() else {
        ys_trace("a-tail:continuation");
        return None;
    };
    let SNode::Stmts(drun) = done_run else {
        return None;
    };
    let mut done = None;
    for l in drun {
        match l {
            Leaf::Raw(Stmt::Elided { op, .. }) if *op == "ThrowIfNotObject" => {}
            Leaf::Raw(Stmt::Declare {
                value, value_id, ..
            }) if ys_prop(value, "done") == Some(*resume1) => {
                done = Some(*value_id);
            }
            _ => return None,
        }
    }
    let Some(done) = done else {
        ys_trace("a-tail:done-decl");
        return None;
    };
    let SNode::If {
        cond: dcond,
        then: done_arm,
        otherwise: next_arm,
    } = done_if
    else {
        ys_trace("a-tail:done-if");
        return None;
    };
    if ys_flag_test(dcond) != Some((done, true)) {
        return None;
    }

    // ── done arm: the completion dispatch, then break ──
    let dasig = ys_sig(done_arm);
    let [exit_if, SNode::Break { .. }] = dasig.as_slice() else {
        ys_trace("a-tail:done-arm");
        return None;
    };
    let SNode::If {
        cond: econd,
        then: normal,
        otherwise: retarm,
    } = exit_if
    else {
        return None;
    };
    let Some((et, epos)) = ys_flag_test(econd) else {
        ys_trace("a-tail:exit-cond");
        return None;
    };
    if et != exit_phi.0 || epos {
        // `if (!exitReturn) { normal } else { return-completion }`
        ys_trace("a-tail:exit-phi");
        return None;
    }
    // Normal completion: `value = resume1.value; <continuation>`.
    let nsig = ys_sig(normal);
    let [SNode::Stmts(nrun), nrest @ ..] = nsig.as_slice() else {
        return None;
    };
    let Some((bind_name, bind_id, bind_val)) = nrun.first().and_then(ys_declare_of) else {
        ys_trace("a-tail:bind");
        return None;
    };
    if ys_prop(bind_val, "value") != Some(*resume1) {
        return None;
    }
    let mut continuation: Vec<SNode> = Vec::new();
    if nrun.len() > 1 {
        continuation.push(SNode::Stmts(nrun[1..].to_vec()));
    }
    continuation.extend(nrest.iter().map(|n| (*n).clone()));
    // Return completion: `v = resume1.value; return v` (+ plumbing).
    let rsig = ys_sig(retarm);
    let Some(SNode::Stmts(rrun)) = rsig.first() else {
        return None;
    };
    let [
        Leaf::Raw(Stmt::Declare {
            value: rv_val,
            value_id: rvid,
            ..
        }),
        Leaf::Raw(Stmt::Return(Some(ret_e))),
    ] = rrun.as_slice()
    else {
        return None;
    };
    if ys_prop(rv_val, "value") != Some(*resume1) || temp_value(ret_e) != Some(*rvid) {
        return None;
    }

    // ── not-done arm: value/await/AsyncGeneratorYield + resumption ──
    if ys_match_async_yield(
        &ys_sig(next_arm),
        g_id,
        *resume1,
        rt,
        rv,
        &rt_name,
        &rv_name,
    )
    .is_none()
    {
        ys_trace("a-tail:async-yield");
        return None;
    }

    Some(YsLoop {
        rt: (rt, rt_name),
        rv: (rv, rv_name),
        it: (it, it_name),
        g: (
            g_id,
            phis.iter()
                .find(|(_, v)| **v == g_id)
                .map(|(n, _)| n.clone())?,
        ),
        flag: (
            phis.iter()
                .find(|(n, _)| **n == flag_name)
                .map(|(_, v)| *v)?,
            flag_name,
        ),
        exit_phi,
        bind: Some((bind_name.to_string(), bind_id)),
        continuation,
    })
}

/// The async THROW-only dispatch on an inline `GetResumeMode(g)`
/// cond: `if (mode != THROW) { … } else { throw resume; unreachable;
/// break }` (the cond here is the IsFalse(Eq(driver, 1)) form —
/// positive arm is the continuation).
pub(in crate::folds) fn ys_async_throw_dispatch(
    cond: &Expr,
    otherwise: &[SNode],
    g: ValueId,
    resume: ValueId,
) -> Option<()> {
    let Expr::Unary {
        op: UnOp::IsFalse,
        operand,
    } = cond
    else {
        return None;
    };
    let Expr::Compare {
        op: CmpOp::Eq,
        left,
        right,
    } = operand.as_ref()
    else {
        return None;
    };
    let ok = |d: &Expr, n: &Expr| {
        ys_driver(d, false, g)
            && matches!(n, Expr::Lit(Lit::Number(b)) if f64::from_bits(*b) == 1.0)
    };
    if !ok(left, right) && !ok(right, left) {
        return None;
    }
    let osig = ys_sig(otherwise);
    let [SNode::Stmts(trun), SNode::Break { .. }] = osig.as_slice() else {
        return None;
    };
    let [Leaf::Raw(Stmt::Throw(e)), Leaf::Raw(Stmt::Unreachable)] = trun.as_slice() else {
        return None;
    };
    (temp_value(e) == Some(resume)).then_some(())
}

/// The async not-done arm (AsyncGeneratorYield + the resumption
/// re-entry): `value = inner.value; av = await value; yield av;
/// res2 = ResumeGenerator(g)`; THROW-dispatch; then the three-way
/// resumption re-entry (NEXT: loop back with the mode/value; RETURN:
/// await the resume value, then re-enter with RETURN; the await's own
/// THROW re-enters with THROW).
pub(in crate::folds) fn ys_match_async_yield(
    arm: &[&SNode],
    g: ValueId,
    resume1: ValueId,
    rt: ValueId,
    rv: ValueId,
    rt_name: &str,
    rv_name: &str,
) -> Option<()> {
    let [SNode::Stmts(head), mode_if] = arm else {
        ys_trace("ay:skeleton");
        return None;
    };
    // head: [value = resume1.value, av = await value (uncaught),
    //        yield av, res2 = ResumeGenerator(g)]
    let [
        Leaf::Raw(Stmt::Declare {
            value: vload,
            value_id: value,
            ..
        }),
        Leaf::Raw(Stmt::Declare {
            value:
                Expr::Await {
                    value: awv,
                    uncaught: true,
                },
            value_id: av,
            ..
        }),
        Leaf::Raw(Stmt::Expr(Expr::Yield { value: yv })),
        Leaf::Raw(Stmt::Declare {
            value: drv,
            value_id: res2,
            ..
        }),
    ] = head.as_slice()
    else {
        ys_trace("ay:head-shape");
        return None;
    };
    if ys_prop(vload, "value") != Some(resume1)
        || temp_value(awv) != Some(*value)
        || temp_value(yv) != Some(*av)
        || !ys_driver(drv, true, g)
    {
        return None;
    }
    let SNode::If {
        cond,
        then,
        otherwise,
    } = mode_if
    else {
        ys_trace("ay:mode-if");
        return None;
    };
    if ys_async_throw_dispatch(cond, otherwise, g, *res2).is_none() {
        ys_trace("ay:throw-dispatch");
        return None;
    }
    // The resumption re-entry: [r3 = ResumeGenerator(g), m3 =
    // GetResumeMode(g)]; `if (m3 != RETURN) loop-back`; the RETURN
    // await; `if (m4 == THROW) loop-back(THROW)`; the final
    // loop-back with mode RETURN.
    let rsig = ys_sig(then);
    let [
        SNode::Stmts(pair),
        next_if,
        SNode::Stmts(await_run),
        throw_if,
        loopback_run,
        SNode::Continue { .. },
    ] = rsig.as_slice()
    else {
        ys_trace("ay:resumption-skeleton");
        return None;
    };
    let [
        Leaf::Raw(Stmt::Declare {
            value: d3,
            value_id: r3,
            ..
        }),
        Leaf::Raw(Stmt::Declare {
            value: dm3,
            value_id: m3,
            ..
        }),
    ] = pair.as_slice()
    else {
        return None;
    };
    if !ys_driver(d3, true, g) || !ys_driver(dm3, false, g) {
        return None;
    }
    // `if (m3 != RETURN(0)) { loop-back rt←m3, rv←r3; continue }`.
    let SNode::If {
        cond: c0,
        then: t0,
        otherwise: o0,
    } = next_if
    else {
        return None;
    };
    if ys_mode_neq_test(c0, *m3, 0.0).is_none() {
        ys_trace("ay:m3-test");
        return None;
    }
    if ys_loopback(t0, o0, rt_name, rv_name, Some(*m3), Some(*r3), false).is_none() {
        ys_trace("ay:loopback-next");
        return None;
    }
    // The RETURN await: [aw3 = await r3 (uncaught), yield aw3,
    // r4 = ResumeGenerator(g), m4 = GetResumeMode(g)].
    let [
        Leaf::Raw(Stmt::Declare {
            value:
                Expr::Await {
                    value: aw3v,
                    uncaught: true,
                },
            value_id: aw3,
            ..
        }),
        Leaf::Raw(Stmt::Expr(Expr::Yield { value: y3 })),
        Leaf::Raw(Stmt::Declare {
            value: d4,
            value_id: r4,
            ..
        }),
        Leaf::Raw(Stmt::Declare {
            value: dm4,
            value_id: m4,
            ..
        }),
    ] = await_run.as_slice()
    else {
        return None;
    };
    if temp_value(aw3v) != Some(*r3)
        || temp_value(y3) != Some(*aw3)
        || !ys_driver(d4, true, g)
        || !ys_driver(dm4, false, g)
    {
        return None;
    }
    // `if (m4 == THROW(1)) { loop-back rt←m4, rv←r4; continue }`.
    let SNode::If {
        cond: c1,
        then: t1,
        otherwise: o1,
    } = throw_if
    else {
        return None;
    };
    if ys_mode_eq_test(c1, *m4, 1.0).is_none() {
        ys_trace("ay:m4-test");
        return None;
    }
    if ys_loopback(t1, o1, rt_name, rv_name, Some(*m4), Some(*r4), false).is_none() {
        ys_trace("ay:loopback-throw");
        return None;
    }
    // The final loop-back: rt ← RETURN(0.0), rv ← r4, then continue.
    if ys_loopback(
        std::slice::from_ref(loopback_run),
        &[],
        rt_name,
        rv_name,
        None,
        Some(*r4),
        true,
    )
    .is_none()
    {
        ys_trace("ay:loopback-return");
        return None;
    }
    let _ = rt;
    let _ = rv;
    Some(())
}

/// `IsFalse(Eq(Temp(m), num))` — mode != num.
pub(in crate::folds) fn ys_mode_neq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::Eq)
}

/// `IsFalse(NotEq(Temp(m), num))` — mode == num.
pub(in crate::folds) fn ys_mode_eq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::NotEq)
}

pub(in crate::folds) fn ys_mode_num_test(
    cond: &Expr,
    m: ValueId,
    num: f64,
    op: CmpOp,
) -> Option<()> {
    let Expr::Unary {
        op: UnOp::IsFalse,
        operand,
    } = cond
    else {
        return None;
    };
    let Expr::Compare {
        op: o, left, right, ..
    } = operand.as_ref()
    else {
        return None;
    };
    if *o != op {
        return None;
    }
    let ok = |t: &Expr, n: &Expr| {
        temp_value(t) == Some(m)
            && matches!(n, Expr::Lit(Lit::Number(b)) if f64::from_bits(*b) == num)
    };
    (ok(left, right) || ok(right, left)).then_some(())
}

/// A loop-back assign set: all phi assigns to one block, containing
/// `rt ← mode` (a temp, or the RETURN(0.0) literal when `mode_zero`)
/// and `rv ← value`; then a `Continue`.
pub(in crate::folds) fn ys_loopback(
    then: &[SNode],
    otherwise: &[SNode],
    rt_name: &str,
    rv_name: &str,
    mode: Option<ValueId>,
    value: Option<ValueId>,
    mode_zero: bool,
) -> Option<()> {
    if !otherwise.is_empty() && !ys_sig(otherwise).is_empty() {
        return None;
    }
    let tsig = ys_sig(then);
    let (assigns, is_last) = match tsig.as_slice() {
        [a, SNode::Continue { .. }] => (*a, true),
        [a] => (*a, false),
        _ => return None,
    };
    if !is_last && tsig.len() != 1 {
        return None;
    }
    let SNode::Stmts(run) = assigns else {
        return None;
    };
    if run.is_empty() {
        return None;
    }
    let mut to = None;
    let mut saw_rt = false;
    let mut saw_rv = false;
    for l in run {
        let Leaf::Raw(Stmt::PhiAssign {
            target,
            value: v,
            to: t,
            exceptional,
        }) = l
        else {
            return None;
        };
        if *exceptional {
            // Catch-region context plumbing — interspersed machinery.
            continue;
        }
        if let Some(prev) = to {
            if prev != *t {
                return None;
            }
        } else {
            to = Some(*t);
        }
        if target == rt_name {
            let ok = if mode_zero {
                matches!(v, Expr::Lit(Lit::Number(b)) if f64::from_bits(*b) == 0.0)
            } else {
                temp_value(v) == mode
            };
            if !ok {
                return None;
            }
            saw_rt = true;
        }
        if target == rv_name {
            if temp_value(v) != value {
                return None;
            }
            saw_rv = true;
        }
    }
    (saw_rt && saw_rv).then_some(())
}

// ── the completion dispatch (sync sibling) ─────────────────────────

/// The completion-dispatch match result: the optional completion-value
/// binding (name, id) and the continuation nodes.
pub(in crate::folds) type ExitMatch = (Option<(String, ValueId)>, Vec<SNode>);

/// Match the sync completion dispatch sitting right after the loop:
/// `if (!exitReturn) { value = res.value; <continuation> } else {
/// v2 = res.value; return v2 }`. Returns the binding (when the
/// completion value is used) and the continuation.
pub(in crate::folds) fn ys_match_exit(
    n: &SNode,
    exit_phi: ValueId,
    res: ValueId,
) -> Option<ExitMatch> {
    let SNode::If {
        cond,
        then,
        otherwise,
    } = n
    else {
        return None;
    };
    let (t, positive) = ys_flag_test(cond)?;
    if t != exit_phi || positive {
        return None;
    }
    // Normal arm: first run starts with the completion-value load
    // (a Declare when used, a dead Expr load when unused).
    let tsig = ys_sig(then);
    let [SNode::Stmts(first), rest @ ..] = tsig.as_slice() else {
        return None;
    };
    let (bind, first_rest) = match first.as_slice() {
        [
            Leaf::Raw(Stmt::Declare {
                name,
                value,
                value_id,
                ..
            }),
            tail @ ..,
        ] if ys_prop(value, "value") == Some(res) => (Some((name.clone(), *value_id)), tail),
        [Leaf::Raw(Stmt::Expr(e)), tail @ ..] if ys_prop(e, "value") == Some(res) => (None, tail),
        _ => return None,
    };
    let mut continuation: Vec<SNode> = Vec::new();
    if !first_rest.is_empty() {
        continuation.push(SNode::Stmts(first_rest.to_vec()));
    }
    continuation.extend(rest.iter().map(|n| (*n).clone()));
    // Return arm: `v2 = res.value; return v2` (+ dead plumbing assigns).
    let rsig = ys_sig(otherwise);
    let [SNode::Stmts(rrun)] = rsig.as_slice() else {
        return None;
    };
    let [
        Leaf::Raw(Stmt::Declare {
            value: v2load,
            value_id: v2,
            ..
        }),
        Leaf::Raw(Stmt::Return(Some(ret_e))),
        tail @ ..,
    ] = rrun.as_slice()
    else {
        return None;
    };
    if ys_prop(v2load, "value") != Some(res) || temp_value(ret_e) != Some(*v2) {
        return None;
    }
    if !tail
        .iter()
        .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
    {
        return None;
    }
    Some((bind, continuation))
}

// ── the setup runs ─────────────────────────────────────────────────

/// The setup run directly before the phi-init: its last two declares
/// must be `iter = GetIterator(obj)` (async: GetAsyncIterator) and
/// `next = iter.next`. Returns (delegate obj expr, iter id, next id,
/// prefix leaves).
pub(in crate::folds) fn ys_match_setup(
    n: &SNode,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
) -> Option<(Expr, ValueId, ValueId, Vec<Leaf>)> {
    let SNode::Stmts(run) = n else {
        return None;
    };
    if run.len() < 2 {
        return None;
    }
    let (.., next_id, next_val) = ys_declare_of(&run[run.len() - 1])?;
    let (_, iter_id, iter_val) = ys_declare_of(&run[run.len() - 2])?;
    let Expr::Iter { op, obj, .. } = iter_val else {
        return None;
    };
    let want = if async_ {
        IterOp::GetAsyncIterator
    } else {
        IterOp::GetIterator
    };
    if *op != want {
        return None;
    }
    if ys_prop(next_val, "next") != Some(iter_id) {
        return None;
    }
    let mut delegate = (**obj).clone();
    let mut prefix: Vec<Leaf> = run[..run.len() - 2].to_vec();
    // Inline trailing single-use temp declares into the delegate
    // expr (`t = inner(); yield* t` → `yield* inner()`): the removed
    // pieces between the declare and the yield* are all consumed
    // machinery, so the observable evaluation order is unchanged.
    while let Expr::Temp { value: t, .. } = &delegate {
        let Some(Leaf::Raw(Stmt::Declare {
            value, value_id, ..
        })) = prefix.last()
        else {
            break;
        };
        if value_id != t || uses.get(t).copied().unwrap_or(0) != 1 {
            break;
        }
        delegate = value.clone();
        prefix.pop();
    }
    Some((delegate, iter_id, next_id, prefix))
}

/// The phi-init run: all phi assigns; the non-exceptional ones go to
/// one block and must set mode ← NEXT(2.0), received ← undefined,
/// flag ← false, iter ← the iterator temp, genobj ← its source, and
/// exactly one method ← the next temp.
pub(in crate::folds) fn ys_match_init(
    n: &SNode,
    lp: &YsLoop,
    iter: ValueId,
    next: ValueId,
) -> Option<()> {
    let SNode::Stmts(run) = n else {
        return None;
    };
    if run.is_empty() {
        return None;
    }
    let mut to = None;
    let mut saw_rt = false;
    let mut saw_rv = false;
    let mut saw_flag = false;
    let mut saw_it = false;
    let mut saw_g = false;
    let mut saw_next = 0usize;
    for l in run {
        let Leaf::Raw(Stmt::PhiAssign {
            target,
            value,
            to: t,
            exceptional,
        }) = l
        else {
            return None;
        };
        if *exceptional {
            continue;
        }
        if let Some(prev) = to {
            if prev != *t {
                return None;
            }
        } else {
            to = Some(*t);
        }
        if *target == lp.rt.1 {
            if !matches!(value, Expr::Lit(Lit::Number(b)) if f64::from_bits(*b) == 2.0) {
                return None;
            }
            saw_rt = true;
        } else if *target == lp.rv.1 {
            if !matches!(value, Expr::Lit(Lit::Undefined)) {
                return None;
            }
            saw_rv = true;
        } else if *target == lp.flag.1 {
            if !matches!(value, Expr::Lit(Lit::Bool(false))) {
                return None;
            }
            saw_flag = true;
        } else if *target == lp.it.1 {
            if temp_value(value) != Some(iter) {
                return None;
            }
            saw_it = true;
        } else if *target == lp.g.1 {
            saw_g = true;
        } else if temp_value(value) == Some(next) {
            saw_next += 1;
        } else {
            return None;
        }
    }
    (saw_rt && saw_rv && saw_flag && saw_it && saw_g && saw_next == 1).then_some(())
}

// ── apply ──────────────────────────────────────────────────────────

/// Build the yield* statement node.
pub(in crate::folds) fn ys_stmt(lp: &YsLoop, delegate: Expr) -> SNode {
    let leaf = match &lp.bind {
        Some((name, id)) => Leaf::Raw(Stmt::Declare {
            name: name.clone(),
            mutable: false,
            value: Expr::YieldStar {
                value: Box::new(delegate),
            },
            value_id: *id,
        }),
        None => Leaf::Raw(Stmt::Expr(Expr::YieldStar {
            value: Box::new(delegate),
        })),
    };
    SNode::Stmts(vec![leaf])
}

/// Arrangement A: bare siblings `[…, setup, init, While, exit?]`.
pub(in crate::folds) fn ys_apply_bare(
    nodes: &mut Vec<SNode>,
    i: usize,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) -> bool {
    let Some(mut lp) = ys_match_loop(&nodes[i], async_) else {
        ys_trace("loop");
        return false;
    };
    if i < 2 {
        return false;
    }
    let Some((delegate, iter, next, prefix)) = ys_match_setup(&nodes[i - 2], async_, uses) else {
        ys_trace("setup");
        return false;
    };
    if ys_match_init(&nodes[i - 1], &lp, iter, next).is_none() {
        ys_trace("init");
        return false;
    }
    if !async_ {
        // The sync completion dispatch must be the next sibling.
        let Some(res) = ys_sync_res(&nodes[i]) else {
            return false;
        };
        let Some((bind, continuation)) = nodes
            .get(i + 1)
            .and_then(|n| ys_match_exit(n, lp.exit_phi.0, res))
        else {
            return false;
        };
        lp.bind = bind;
        lp.continuation = continuation;
        let mut new: Vec<SNode> = Vec::new();
        if !prefix.is_empty() {
            new.push(SNode::Stmts(prefix));
        }
        new.push(ys_stmt(&lp, delegate));
        new.extend(lp.continuation);
        nodes.splice(i - 2..i + 2, new);
    } else {
        let mut new: Vec<SNode> = Vec::new();
        if !prefix.is_empty() {
            new.push(SNode::Stmts(prefix));
        }
        new.push(ys_stmt(&lp, delegate));
        new.extend(lp.continuation);
        nodes.splice(i - 2..i + 1, new);
    }
    stats.yield_star_sites += 1;
    if lp.bind.is_some() {
        stats.yield_star_bound += 1;
    }
    true
}

/// The sync loop's call-result temp (re-derived for the exit match).
pub(in crate::folds) fn ys_sync_res(w: &SNode) -> Option<ValueId> {
    let SNode::While { body, .. } = w else {
        return None;
    };
    let sig = ys_sig(body);
    let SNode::Stmts(prun) = sig.get(2)? else {
        return None;
    };
    for l in prun {
        if let Leaf::Raw(Stmt::Declare {
            value: Expr::Call { .. },
            value_id,
            ..
        }) = l
        {
            return Some(*value_id);
        }
    }
    None
}

/// Descend through nested single-child `Try` wrappers to the
/// innermost body sequence.
pub(in crate::folds) fn ys_innermost_body_mut(t: &mut SNode) -> &mut Vec<SNode> {
    let SNode::Try { body, .. } = t else {
        unreachable!()
    };
    if body.len() == 1 && matches!(body[0], SNode::Try { .. }) {
        let inner = &mut body[0];
        return ys_innermost_body_mut(inner);
    }
    body
}

pub(in crate::folds) fn ys_innermost_body(t: &SNode) -> Option<&Vec<SNode>> {
    let SNode::Try { body, .. } = t else {
        return None;
    };
    if body.len() == 1 && matches!(body[0], SNode::Try { .. }) {
        return ys_innermost_body(&body[0]);
    }
    Some(body)
}

/// Arrangement B: try fragments `[Try(setup+init), Try(While),
/// Try(exit)]` (the structurer's non-contiguous-region split).
pub(in crate::folds) fn ys_apply_fragments(
    nodes: &mut [SNode],
    i: usize,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) -> bool {
    // The While sits at the end of nodes[i]'s innermost try body
    // (after Honest noise).
    let loop_body = ys_innermost_body(&nodes[i]).cloned();
    let Some(loop_body) = loop_body else {
        return false;
    };
    let lsig = ys_sig(&loop_body);
    let Some(SNode::While { .. }) = lsig.last() else {
        return false;
    };
    let Some(mut lp) = ys_match_loop(lsig[lsig.len() - 1], async_) else {
        ys_trace("frag:loop");
        return false;
    };
    // nodes[i-1]: the setup+init fragment (tail of its innermost body).
    if i == 0 {
        return false;
    }
    let Some(setup_body) = ys_innermost_body(&nodes[i - 1]).cloned() else {
        ys_trace("frag:setup-body");
        return false;
    };
    let ssig = ys_sig(&setup_body);
    if ssig.len() < 2 {
        return false;
    }
    let Some((delegate, iter, next, prefix)) = ys_match_setup(ssig[ssig.len() - 2], async_, uses)
    else {
        ys_trace("frag:setup");
        return false;
    };
    if ys_match_init(ssig[ssig.len() - 1], &lp, iter, next).is_none() {
        ys_trace("frag:init");
        return false;
    }
    if !async_ {
        // The completion dispatch is the first significant node of
        // nodes[i+1]'s innermost body.
        let Some(exit_body) = nodes.get(i + 1).and_then(ys_innermost_body).cloned() else {
            return false;
        };
        let esig = ys_sig(&exit_body);
        let Some(res) = ys_sync_res(lsig[lsig.len() - 1]) else {
            return false;
        };
        let Some(exit_node) = esig
            .iter()
            .find(|n| !matches!(n, SNode::Honest(_)))
            .copied()
        else {
            return false;
        };
        let Some((bind, continuation)) = ys_match_exit(exit_node, lp.exit_phi.0, res) else {
            ys_trace("frag:exit");
            return false;
        };
        lp.bind = bind;
        lp.continuation = continuation;
    }
    // ── apply ──
    // 1. The loop fragment: replace the While with the yield* stmt (+
    //    the continuation for the async in-loop completion).
    {
        let body = ys_innermost_body_mut(&mut nodes[i]);
        let pos = body
            .iter()
            .rposition(|n| matches!(n, SNode::While { .. }))
            .expect("the matched While");
        let mut new = vec![ys_stmt(&lp, delegate.clone())];
        if async_ {
            new.extend(lp.continuation.clone());
        }
        body.splice(pos..pos + 1, new);
    }
    // 2. The setup fragment: drop the init run; replace the setup run
    //    with its prefix (or drop it when empty).
    {
        let body = ys_innermost_body_mut(&mut nodes[i - 1]);
        let sig_positions: Vec<usize> = body
            .iter()
            .enumerate()
            .filter(|(_, n)| !ys_is_exc_run(n))
            .map(|(p, _)| p)
            .collect();
        let (setup_pos, init_pos) = (
            sig_positions[sig_positions.len() - 2],
            sig_positions[sig_positions.len() - 1],
        );
        body.remove(init_pos);
        if prefix.is_empty() {
            body.remove(setup_pos);
        } else {
            body[setup_pos] = SNode::Stmts(prefix);
        }
    }
    // 3. The completion fragment (sync): replace the exit-If with its
    //    continuation.
    if !async_ {
        let body = ys_innermost_body_mut(&mut nodes[i + 1]);
        let pos = body
            .iter()
            .position(|n| !ys_is_exc_run(n) && !matches!(n, SNode::Honest(_)))
            .expect("the matched exit-If");
        body.splice(pos..pos + 1, lp.continuation);
    }
    stats.yield_star_sites += 1;
    if lp.bind.is_some() {
        stats.yield_star_bound += 1;
    }
    true
}
