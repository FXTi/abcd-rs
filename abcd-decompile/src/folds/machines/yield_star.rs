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
pub(in crate::folds) use super::yield_star_async::*;

pub(in crate::folds) struct YsLoop {
    /// Loop phi: the resumption mode (`receivedType`).
    pub(in crate::folds) rt: (ValueId, String),
    /// Loop phi: the resumption value (`received`).
    pub(in crate::folds) rv: (ValueId, String),
    /// Delegate iterator temp (header phi or outer declare).
    pub(in crate::folds) it: (ValueId, String),
    /// Whether `it` is a loop-header phi (`false` when Braun eliminated its self-phi).
    pub(in crate::folds) it_in_phis: bool,
    /// Generator object temp (header phi or outer declare).
    pub(in crate::folds) g: (ValueId, String),
    /// Whether `g` is a loop-header phi.
    pub(in crate::folds) g_in_phis: bool,
    /// Close-attempt flag temp (header phi or outer `false` declare).
    pub(in crate::folds) flag: (ValueId, String),
    /// Whether `flag` is a loop-header phi.
    pub(in crate::folds) flag_in_phis: bool,
    /// The temp assigned to the method phi in the `NEXT(2.0)` arm.
    pub(in crate::folds) next_method_val: Option<ValueId>,
    /// The `exitReturn` phi tested by the completion dispatch.
    pub(in crate::folds) exit_phi: (ValueId, String),
    /// The completion-value binding + continuation (async: extracted
    /// from the done arm inside the loop; sync: from the sibling
    /// completion dispatch — filled by [`ys_match_exit`]).
    pub(in crate::folds) bind: Option<(String, ValueId)>,
    /// The post-delegation continuation (async or R3-M1 sync: done-arm content).
    pub(in crate::folds) continuation: Vec<SNode>,
    /// Whether `bind` and `continuation` were extracted from an in-loop
    /// completion dispatch inside the `done` arm (always true for async;
    /// true for R3-M1 sync when `ThrowNotExists` has no fallthrough edge).
    pub(in crate::folds) in_loop_exit: bool,
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
    // `async_generator_machine_fold` strips dead catch-context `PhiAssign`
    // leaves in place (`strip_genobj_phi_assigns`), which can leave empty
    // `SNode::Stmts([])` placeholders where an exceptional-only run used to sit.
    fold_snode_vecs_postorder(nodes, |seq| {
        seq.retain(|n| !matches!(n, SNode::Stmts(r) if r.is_empty()));
    });
    let mut uses = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    ys_fold_seq(nodes, async_, &uses, stats);
}

/// The iterative post-order driver: children first, then the sequence scan.
pub(in crate::folds) fn ys_fold_seq(
    nodes: &mut Vec<SNode>,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) {
    fold_snode_vecs_postorder(nodes, |seq| {
        let mut i = 0;
        while i < seq.len() {
            if matches!(&seq[i], SNode::While { cond: None, .. })
                && ys_apply_bare(seq, i, async_, uses, stats)
            {
                continue;
            }
            if matches!(&seq[i], SNode::Try { .. })
                && ys_apply_fragments(seq, i, async_, uses, stats)
            {
                continue;
            }
            i += 1;
        }
    });
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
#[cfg(test)]
pub(in crate::folds) fn ys_mode_test(cond: &Expr, want: f64) -> Option<ValueId> {
    let Expr::Unary {
        op: UnOp::IsFalse | UnOp::JumpEqz,
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

/// An `istrue`/`isfalse`/`jnez`/`jeqz`-wrapped temp test: strips the
/// wrappers and returns (temp, positive).
pub(in crate::folds) fn ys_flag_test(cond: &Expr) -> Option<(ValueId, bool)> {
    let mut e = cond;
    let mut positive = true;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsFalse | UnOp::JumpEqz,
                operand,
            } => {
                positive = !positive;
                e = operand;
            }
            Expr::Unary {
                op: UnOp::IsTrue | UnOp::JumpNez,
                operand,
            } => e = operand,
            _ => break,
        }
    }
    Some((temp_value(e)?, positive))
}

/// Polarity-aware mode test: `(IsFalse|JumpEqz|IsTrue|JumpNez)? StrictEq(Temp(phi), <num>)`.
/// Returns `(phi, positive)` where `positive == true` means the `then` arm is `phi === want`.
pub(in crate::folds) fn ys_mode_test_pol(cond: &Expr, want: f64) -> Option<(ValueId, bool)> {
    let (cmp_expr, positive) = match cond {
        Expr::Unary {
            op: UnOp::IsFalse | UnOp::JumpEqz,
            operand,
        } => (operand.as_ref(), false),
        Expr::Unary {
            op: UnOp::IsTrue | UnOp::JumpNez,
            operand,
        } => (operand.as_ref(), true),
        _ => (cond, true),
    };
    let Expr::Compare {
        op: CmpOp::StrictEq,
        left,
        right,
    } = cmp_expr
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
    (n == want).then_some((t, positive))
}

/// `<temp> == undefined` (either order, `Eq`):
/// - negated (`IsFalse | JumpEqz` over `Eq(t, undefined)`) → `(t, true)` ("t is defined")
/// - positive (`IsTrue | JumpNez` or bare `Eq(t, undefined)`) → `(t, false)` ("t is undefined")
pub(in crate::folds) fn ys_undefined_test(cond: &Expr) -> Option<(ValueId, bool)> {
    let (cmp_expr, defined) = match cond {
        Expr::Unary {
            op: UnOp::IsFalse | UnOp::JumpEqz,
            operand,
        } => (operand.as_ref(), true),
        Expr::Unary {
            op: UnOp::IsTrue | UnOp::JumpNez,
            operand,
        } => (operand.as_ref(), false),
        _ => (cond, false),
    };
    let Expr::Compare {
        op: CmpOp::Eq,
        left,
        right,
    } = cmp_expr
    else {
        return None;
    };
    if matches!(right.as_ref(), Expr::Lit(Lit::Undefined)) {
        temp_value(left).map(|t| (t, defined))
    } else if matches!(left.as_ref(), Expr::Lit(Lit::Undefined)) {
        temp_value(right).map(|t| (t, defined))
    } else {
        None
    }
}

/// No-op stage marker (retained for matcher readability; library code must not
/// read environment variables or write to stderr).
pub(in crate::folds) fn ys_trace(stage: &str) {
    let _ = stage;
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

pub(in crate::folds) fn ys_temp_pair(e: &Expr) -> Option<(ValueId, String)> {
    match e {
        Expr::Temp { value, name } => Some((*value, name.clone())),
        _ => None,
    }
}

pub(in crate::folds) fn ys_prop_temp(e: &Expr, name: &str) -> Option<(ValueId, String)> {
    let Expr::PropName {
        object, name: n, ..
    } = e
    else {
        return None;
    };
    (n == name).then(|| ys_temp_pair(object))?
}

pub(in crate::folds) fn ys_flag_test_pair(cond: &Expr) -> Option<((ValueId, String), bool)> {
    let mut e = cond;
    let mut positive = true;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsFalse | UnOp::JumpEqz,
                operand,
            } => {
                positive = !positive;
                e = operand;
            }
            Expr::Unary {
                op: UnOp::IsTrue | UnOp::JumpNez,
                operand,
            } => e = operand,
            _ => break,
        }
    }
    Some((ys_temp_pair(e)?, positive))
}

pub(in crate::folds) fn ys_unwrap_labeled_arm<'a>(
    arm: &[&'a SNode],
) -> (Option<&'a str>, Vec<&'a SNode>) {
    if let [SNode::Labeled { label, body }] = arm {
        (Some(label.as_str()), ys_sig(body))
    } else {
        (None, arm.to_vec())
    }
}

pub(in crate::folds) fn ys_assign_arm_node<'a>(
    tsig: &[&'a SNode],
    arm_label: Option<&str>,
) -> Option<&'a SNode> {
    match tsig {
        [assigns] => Some(*assigns),
        [assigns, SNode::Break { label: Some(lbl) }] if arm_label == Some(lbl.as_str()) => {
            Some(*assigns)
        }
        _ => None,
    }
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
    let header_sig: Vec<&Leaf> = header
        .iter()
        .filter(|l| !ys_skip_plumbing_leaf(l))
        .collect();
    if header_sig.is_empty() {
        return None;
    }
    let (phis, exit_decl) = {
        let mut phis = BTreeMap::new();
        for &l in &header_sig[..header_sig.len() - 1] {
            let Leaf::Raw(Stmt::PhiDecl { name, value_id }) = l else {
                return None;
            };
            phis.insert(name.clone(), *value_id);
        }
        let (_, id, value) = ys_declare_of(header_sig[header_sig.len() - 1])?;
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
    let Some((rt_id, pos_next)) = ys_mode_test_pol(cond, 2.0).filter(|(id, _)| in_phis(id)) else {
        ys_trace("loop:mode-test");
        return None;
    };
    let rt_name = phis
        .iter()
        .find(|(_, v)| **v == rt_id)
        .map(|(n, _)| n.clone())?;
    let (next_arm_nodes, rest_arm_nodes) = if pos_next {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    let Some(first) = ys_sig(next_arm_nodes).into_iter().next().cloned() else {
        ys_trace("loop:next-arm");
        return None;
    };
    let Some(call_block) = ys_assign_run(&first) else {
        ys_trace("loop:next-arm-assigns");
        return None;
    };
    let dsig = ys_sig(rest_arm_nodes);
    let [
        SNode::If {
            cond: cond2,
            then: arm_a,
            otherwise: arm_b,
        },
    ] = dsig.as_slice()
    else {
        return None;
    };
    let (rt_id2, pos_throw) = ys_mode_test_pol(cond2, 1.0)?;
    if rt_id2 != rt_id {
        return None;
    }
    let (throw_arm, ret_arm) = if pos_throw {
        (arm_a, arm_b)
    } else {
        (arm_b, arm_a)
    };

    // ── RETURN arm: extract the iterator temp, the exitReturn phi,
    // and the received-value phi (the DirectReturn temp) ──
    let rasig = ys_sig(ret_arm);
    let Some(((it_id, it_name), exit_phi, rv_id)) =
        ys_match_return_arm(&rasig, &phis, call_block, async_)
    else {
        ys_trace("loop:return-arm");
        return None;
    };
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
    let next_method_val = {
        let SNode::Stmts(nrun) = &first else {
            return None;
        };
        let mut mv = None;
        for l in nrun {
            if let Leaf::Raw(Stmt::PhiAssign {
                target,
                value,
                exceptional: false,
                ..
            }) = l
                && *target != exit_name
            {
                mv = temp_value(value);
            }
        }
        mv
    };

    // ── THROW arm: `throw` method lookup + the close machinery ──
    let extra_phis: BTreeMap<String, ValueId> = if async_ && phis.len() <= 2 {
        BTreeMap::new()
    } else {
        phis.iter()
            .filter(|(_, v)| **v != rt_id && (async_ || **v != rv_id))
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    };
    let Some((flag_id, flag_name)) = ys_match_throw_arm_pair(
        &ys_sig(throw_arm),
        it_id,
        &exit_name,
        exit_decl,
        call_block,
        &extra_phis,
    ) else {
        ys_trace("loop:throw-arm");
        return None;
    };

    let mut out = if async_ {
        ys_match_loop_tail_async(
            &sig, &phis, rt_id, it_id, exit_decl, flag_id, exit_phi, rt_name, rv_name, it_name,
            flag_name,
        )
    } else {
        ys_match_loop_tail_sync(
            &sig, &phis, rt_id, it_id, rv_id, exit_decl, flag_id, exit_phi, rt_name, rv_name,
            it_name, flag_name,
        )
    };
    if let Some(lp) = &mut out {
        lp.next_method_val = next_method_val;
        // Every header phi in `phis` must be accounted for among the matched
        // YieldStar loop roles `{rt, rv, it, g, flag}`.
        let roles = [lp.rt.0, lp.rv.0, lp.it.0, lp.g.0, lp.flag.0];
        if !phis.values().all(|v| roles.contains(v)) {
            ys_trace("loop:unaccounted-phi");
            return None;
        }
    } else {
        ys_trace("loop:tail");
    }
    out
}

pub(in crate::folds) type YsReturnArmMatch = ((ValueId, String), (ValueId, String), ValueId);

/// The RETURN completion arm (sync shape; async shares the head):
///
/// `[assigns → B_ret, [phis…, T = true, retM = it.return],
///   if (retM !== undefined) { assigns → B_call incl. exitPhi ← T }
///   else { break }, return received]`
///
/// Returns ((it, itName), exitPhi, received).
pub(in crate::folds) fn ys_match_return_arm(
    arm: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    call_block: abcd_ir::BlockId,
    async_: bool,
) -> Option<YsReturnArmMatch> {
    let in_phis = |id: &ValueId| phis.values().any(|v| v == id);
    let (arm_label, arm_nodes) = ys_unwrap_labeled_arm(arm);
    let mut it_info: Option<((ValueId, String), ValueId)> = None;
    let mut true_decl = None;
    let mut exit_phi = None;
    let mut rv_id = None;
    let mut saw_break_if = false;
    for (idx, n) in arm_nodes.iter().enumerate() {
        match n {
            SNode::Stmts(run) => {
                // The decl run: [phis…, T = true, retM = it.return].
                for l in run {
                    if let Some((_, id, value)) = ys_declare_of(l) {
                        if matches!(value, Expr::Lit(Lit::Bool(true))) {
                            true_decl = Some(id);
                        }
                        if let Some(base) = ys_prop_temp(value, "return") {
                            it_info = Some((base, id));
                        }
                    }
                }
                // The propagation return: `return received`.
                if !async_ {
                    let ret_sig: Vec<&Leaf> = run
                        .iter()
                        .filter(|l| {
                            !matches!(
                                l,
                                Leaf::Raw(Stmt::Elided { op, .. }) if *op == "SetGeneratorState"
                            ) && !matches!(
                                l,
                                Leaf::Raw(Stmt::PhiAssign {
                                    exceptional: true,
                                    ..
                                })
                            )
                        })
                        .collect();
                    if let [Leaf::Raw(Stmt::Return(Some(e)))] = ret_sig.as_slice()
                        && let Some(t) = temp_value(e).filter(in_phis)
                    {
                        rv_id = Some(t);
                    }
                }
                let _ = idx;
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                // `if (retM !== undefined) { assigns → B_call } else { break }`
                // or `if (retM == undefined) { break } else { assigns → B_call }`.
                let Some((t, defined)) = ys_undefined_test(cond) else {
                    ys_trace("ret-arm:undefined-test");
                    return None;
                };
                if Some(t) != it_info.as_ref().map(|(_, m)| *m) {
                    ys_trace("ret-arm:method-id");
                    return None;
                }
                let (assign_arm, break_arm) = if defined {
                    (then, otherwise)
                } else {
                    (otherwise, then)
                };
                let tsig = ys_sig(assign_arm);
                let Some(assigns) = ys_assign_arm_node(&tsig, arm_label) else {
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
                let [SNode::Break { .. }] = ys_sig(break_arm).as_slice() else {
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
    if async_ {
        let _ = rv_id;
        Some((it_info?.0, exit_phi?, ValueId::new(u32::MAX)))
    } else {
        Some((it_info?.0, exit_phi?, rv_id?))
    }
}

/// Extract the close-attempt flag `(id, name)` from a labeled close wrapper
/// (`A$k: { L$m: { if (!flag) { … } } throw ReferenceError(…); }`).
pub(in crate::folds) fn ys_labeled_close_flag(n: &SNode) -> Option<(ValueId, String)> {
    if !ys_contains_throw_not_exists(std::slice::from_ref(n)) {
        return None;
    }
    let mut cur = n;
    loop {
        match cur {
            SNode::Labeled { body, .. } => {
                cur = *ys_sig(body).first()?;
            }
            SNode::If { cond, .. } => {
                let (pair, _) = ys_flag_test_pair(cond)?;
                return Some(pair);
            }
            _ => return None,
        }
    }
}

#[cfg(test)]
pub(in crate::folds) fn ys_match_throw_arm(
    arm: &[&SNode],
    it: ValueId,
    exit_name: &str,
    exit_decl: ValueId,
    call_block: abcd_ir::BlockId,
    phis: &BTreeMap<String, ValueId>,
) -> Option<ValueId> {
    ys_match_throw_arm_pair(arm, it, exit_name, exit_decl, call_block, phis).map(|(id, _)| id)
}

/// The THROW completion arm:
///
/// `[throwM = it.throw; (eqM = throwM == undefined)?],
///  if (!eqM | throwM == undefined) { … } ,
///  if (flag | !flag) { close machinery }` (possibly wrapped in Ramsey `A$k` / `L$m`)
///
/// Returns `(flag_id, flag_name)`.
pub(in crate::folds) fn ys_match_throw_arm_pair(
    arm: &[&SNode],
    it: ValueId,
    exit_name: &str,
    exit_decl: ValueId,
    call_block: abcd_ir::BlockId,
    phis: &BTreeMap<String, ValueId>,
) -> Option<(ValueId, String)> {
    let flag_ok = |t: ValueId| phis.is_empty() || phis.values().any(|v| *v == t);
    let (arm_label, arm_nodes) = ys_unwrap_labeled_arm(arm);
    let mut throw_m = None;
    let mut eq_m = None;
    let mut saw_method_if = false;
    let mut flag = None;
    let mut saw_close_if = false;
    let check_assign_arm = |assign_arm: &[SNode]| -> Option<()> {
        let tsig = ys_sig(assign_arm);
        let assigns = ys_assign_arm_node(&tsig, arm_label)?;
        if ys_assign_run(assigns) != Some(call_block) {
            return None;
        }
        let SNode::Stmts(arun) = assigns else {
            return None;
        };
        arun.iter()
            .any(|l| {
                matches!(
                    l,
                    Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                        if target == exit_name && temp_value(value) == Some(exit_decl)
                )
            })
            .then_some(())
    };
    for n in arm_nodes {
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
                if let Some((t, defined)) = ys_undefined_test(cond)
                    && Some(t) == throw_m
                {
                    let (assign_arm, other_arm) = if defined {
                        (then, otherwise)
                    } else {
                        (otherwise, then)
                    };
                    check_assign_arm(assign_arm)?;
                    let osig = ys_sig(other_arm);
                    let other_ok = if defined {
                        osig.is_empty()
                    } else {
                        matches!(osig.as_slice(), [] | [SNode::Break { .. }])
                    };
                    if !other_ok {
                        return None;
                    }
                    saw_method_if = true;
                    continue;
                }
                if let Some(((t, t_name), positive)) = ys_flag_test_pair(cond) {
                    if Some(t) == eq_m {
                        let (assign_arm, other_arm) = if !positive {
                            (then, otherwise)
                        } else {
                            (otherwise, then)
                        };
                        check_assign_arm(assign_arm)?;
                        let osig = ys_sig(other_arm);
                        let other_ok = if !positive {
                            osig.is_empty()
                        } else {
                            matches!(osig.as_slice(), [] | [SNode::Break { .. }])
                        };
                        if !other_ok {
                            return None;
                        }
                        saw_method_if = true;
                        continue;
                    }
                    if flag_ok(t)
                        && (ys_contains_throw_not_exists(then)
                            || ys_contains_throw_not_exists(otherwise))
                    {
                        flag = Some((t, t_name));
                        saw_close_if = true;
                        continue;
                    }
                }
                return None;
            }
            SNode::Labeled { .. } if !saw_close_if => {
                let pair = ys_labeled_close_flag(n)?;
                if !flag_ok(pair.0) {
                    return None;
                }
                flag = Some(pair);
                saw_close_if = true;
            }
            _ => return None,
        }
    }
    throw_m?;
    if !saw_method_if || !saw_close_if {
        return None;
    }
    flag
}

pub(in crate::folds) fn ys_contains_throw_not_exists(nodes: &[SNode]) -> bool {
    if ys_contains_elided(nodes, "ThrowNotExists") {
        return true;
    }
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        for n in slice {
            match n {
                SNode::Stmts(run) => {
                    for l in run {
                        if let Leaf::Raw(Stmt::Throw(Expr::Call {
                            callee,
                            args,
                            kind: abcd_ir::op::CallKind::New,
                            ..
                        })) = l
                            && matches!(callee.as_ref(), Expr::Ident(k) if k == "ReferenceError")
                            && matches!(
                                args.as_slice(),
                                [Expr::Lit(Lit::String(msg))] if msg == "Variable does not exist"
                            )
                        {
                            return true;
                        }
                    }
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::Block(body)
                | SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => stack.push(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        stack.push(fin);
                    }
                    for c in catches {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        stack.push(&c.body);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    false
}

pub(in crate::folds) fn ys_skip_plumbing_leaf(l: &Leaf) -> bool {
    matches!(l, Leaf::Raw(Stmt::Elided { op, .. }) if *op == "SetGeneratorState")
        || matches!(
            l,
            Leaf::Raw(Stmt::PhiAssign {
                exceptional: true,
                ..
            })
        )
}

pub(in crate::folds) fn ys_match_sync_suspend_loopback(
    runs: &[&SNode],
    res: ValueId,
    phis: &BTreeMap<String, ValueId>,
    rt_name: &str,
    rv_name: &str,
) -> Option<(ValueId, String)> {
    let _ = phis;
    let check_loopback = |lrun: &[Leaf], g_id: ValueId, resume: ValueId| -> Option<()> {
        let wrapped = SNode::Stmts(lrun.to_vec());
        let _header_block = ys_assign_run(&wrapped)?;
        let mut saw_mode = false;
        let mut saw_value = false;
        for l in lrun {
            let Leaf::Raw(Stmt::PhiAssign {
                target,
                value,
                exceptional,
                ..
            }) = l
            else {
                return None;
            };
            if *exceptional {
                continue;
            }
            if *target == rt_name && ys_driver(value, false, g_id) {
                saw_mode = true;
            }
            if *target == rv_name && temp_value(value) == Some(resume) {
                saw_value = true;
            }
        }
        (saw_mode && saw_value).then_some(())
    };
    match runs {
        [SNode::Stmts(srun), SNode::Stmts(lrun)] => {
            let srun_sig: Vec<&Leaf> = srun.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
            let [
                Leaf::Raw(Stmt::Expr(Expr::Yield { value })),
                Leaf::Raw(Stmt::Declare {
                    value: drv,
                    value_id: resume,
                    ..
                }),
            ] = srun_sig.as_slice()
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
            let (g_id, g_name) = ys_temp_pair(genobj)?;
            if check_loopback(lrun, g_id, *resume).is_none() {
                ys_trace("sync-tail:loopback-anchors");
                return None;
            }
            Some((g_id, g_name))
        }
        [SNode::Stmts(crun)] => {
            let crun_sig: Vec<Leaf> = crun
                .iter()
                .filter(|l| !ys_skip_plumbing_leaf(l))
                .cloned()
                .collect();
            let [
                Leaf::Raw(Stmt::Expr(Expr::Yield { value })),
                Leaf::Raw(Stmt::Declare {
                    value: drv,
                    value_id: resume,
                    ..
                }),
                lrun @ ..,
            ] = crun_sig.as_slice()
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
            let (g_id, g_name) = ys_temp_pair(genobj)?;
            if check_loopback(lrun, g_id, *resume).is_none() {
                ys_trace("sync-tail:loopback-anchors");
                return None;
            }
            Some((g_id, g_name))
        }
        _ => {
            ys_trace("sync-tail:suspend-run");
            None
        }
    }
}

/// The sync driver tail: pre-call run, done test, pass-through
/// suspend, loop-back assigns, continue.
#[allow(
    clippy::too_many_arguments,
    reason = "sync yield-star tail matcher binds distinct SSA phis and names"
)]
pub(in crate::folds) fn ys_match_loop_tail_sync(
    sig: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    rt: ValueId,
    it: ValueId,
    rv: ValueId,
    exit_decl: ValueId,
    flag_id: ValueId,
    exit_phi: (ValueId, String),
    rt_name: String,
    rv_name: String,
    it_name: String,
    flag_name: String,
) -> Option<YsLoop> {
    if !matches!(sig.len(), 4 | 7) {
        ys_trace("sync-tail:skeleton");
        return None;
    }
    let precall = sig[2];
    let done_if = sig[3];
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
            l if ys_skip_plumbing_leaf(l) => {}
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
    let ((g_id, g_name), bind, continuation, in_loop_exit) = match sig {
        [_, _, _, _, suspend, loopback, SNode::Continue { .. }] => {
            let [SNode::Break { .. }] = ys_sig(then).as_slice() else {
                return None;
            };
            if !ys_sig(otherwise).is_empty() {
                return None;
            }
            let g_pair = ys_match_sync_suspend_loopback(
                &[*suspend, *loopback],
                res,
                phis,
                &rt_name,
                &rv_name,
            )?;
            (g_pair, None, Vec::new(), false)
        }
        [_, _, _, _] => {
            // R3-M1 in-loop completion: `if (done) { exit_if; break; } else { suspend+loopback; continue; }`.
            let then_sig = ys_sig(then);
            let [exit_if, SNode::Break { .. }] = then_sig.as_slice() else {
                return None;
            };
            let (bind, continuation) = ys_match_exit(exit_if, exit_phi.0, res)?;
            let nsig = ys_sig(otherwise);
            let [next_runs @ .., SNode::Continue { .. }] = nsig.as_slice() else {
                return None;
            };
            let g_pair = ys_match_sync_suspend_loopback(next_runs, res, phis, &rt_name, &rv_name)?;
            (g_pair, bind, continuation, true)
        }
        _ => return None,
    };
    let _ = exit_decl;
    let it_in_phis = phis.values().any(|v| *v == it);
    let g_in_phis = phis.values().any(|v| *v == g_id);
    let flag_in_phis = phis.values().any(|v| *v == flag_id);
    Some(YsLoop {
        rt: (rt, rt_name),
        rv: (rv, rv_name),
        it: (it, it_name),
        it_in_phis,
        g: (g_id, g_name),
        g_in_phis,
        flag: (flag_id, flag_name),
        flag_in_phis,
        next_method_val: None,
        exit_phi,
        bind,
        continuation,
        in_loop_exit,
    })
}

/// `mode != num`: `IsFalse|JumpEqz(Eq(m, num))` or `(IsTrue|JumpNez)? NotEq(m, num)`.
pub(in crate::folds) fn ys_mode_neq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::Eq, CmpOp::NotEq)
}

/// `mode == num`: `IsFalse|JumpEqz(NotEq(m, num))` or `(IsTrue|JumpNez)? Eq(m, num)`.
pub(in crate::folds) fn ys_mode_eq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::NotEq, CmpOp::Eq)
}

pub(in crate::folds) fn ys_mode_num_test(
    cond: &Expr,
    m: ValueId,
    num: f64,
    negated_op: CmpOp,
    positive_op: CmpOp,
) -> Option<()> {
    let (cmp_expr, want_op) = match cond {
        Expr::Unary {
            op: UnOp::IsFalse | UnOp::JumpEqz,
            operand,
        } => (operand.as_ref(), negated_op),
        Expr::Unary {
            op: UnOp::IsTrue | UnOp::JumpNez,
            operand,
        } => (operand.as_ref(), positive_op),
        _ => (cond, positive_op),
    };
    let Expr::Compare {
        op: o, left, right, ..
    } = cmp_expr
    else {
        return None;
    };
    if *o != want_op {
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
    let load_idx = first.iter().position(|l| !ys_skip_plumbing_leaf(l))?;
    let (bind, first_rest) = match &first[load_idx] {
        Leaf::Raw(Stmt::Declare {
            name,
            value,
            value_id,
            ..
        }) if ys_prop(value, "value") == Some(res) => {
            (Some((name.clone(), *value_id)), &first[load_idx + 1..])
        }
        Leaf::Raw(Stmt::Expr(e)) if ys_prop(e, "value") == Some(res) => {
            (None, &first[load_idx + 1..])
        }
        _ => return None,
    };
    let mut continuation: Vec<SNode> = Vec::new();
    if !first_rest.is_empty() {
        continuation.push(SNode::Stmts(first_rest.to_vec()));
    }
    continuation.extend(rest.iter().map(|n| (*n).clone()));
    // Return arm: `v2 = res.value; return v2` (+ dead plumbing assigns / SetGeneratorState).
    let rsig = ys_sig(otherwise);
    let [SNode::Stmts(rrun)] = rsig.as_slice() else {
        return None;
    };
    let rrun_sig: Vec<&Leaf> = rrun.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
    let [
        Leaf::Raw(Stmt::Declare {
            value: v2load,
            value_id: v2,
            ..
        }),
        Leaf::Raw(Stmt::Return(Some(ret_e))),
        tail @ ..,
    ] = rrun_sig.as_slice()
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
#[cfg(test)]
pub(in crate::folds) fn ys_match_setup(
    n: &SNode,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
) -> Option<(Expr, ValueId, ValueId, Vec<Leaf>)> {
    ys_match_setup_with_flag(n, async_, uses, None)
}

pub(in crate::folds) fn ys_match_setup_with_flag(
    n: &SNode,
    async_: bool,
    uses: &BTreeMap<ValueId, usize>,
    want_flag: Option<ValueId>,
) -> Option<(Expr, ValueId, ValueId, Vec<Leaf>)> {
    let SNode::Stmts(run) = n else {
        return None;
    };
    let mut sig_indices: Vec<usize> = run
        .iter()
        .enumerate()
        .filter(|(_, l)| !ys_skip_plumbing_leaf(l))
        .map(|(idx, _)| idx)
        .collect();
    if let Some(fid) = want_flag {
        let flag_idx = *sig_indices.last()?;
        let (_, decl_id, decl_val) = ys_declare_of(&run[flag_idx])?;
        if decl_id != fid || !matches!(decl_val, Expr::Lit(Lit::Bool(false))) {
            return None;
        }
        sig_indices.pop();
    }
    if sig_indices.len() < 2 {
        return None;
    }
    let next_idx = sig_indices[sig_indices.len() - 1];
    let iter_idx = sig_indices[sig_indices.len() - 2];
    let (.., next_id, next_val) = ys_declare_of(&run[next_idx])?;
    let (_, iter_id, iter_val) = ys_declare_of(&run[iter_idx])?;
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
    for l in &run[iter_idx + 1..] {
        if let Leaf::Raw(Stmt::PhiAssign { value, .. }) = l
            && (expr_uses_value(value, iter_id) || expr_uses_value(value, next_id))
        {
            return None;
        }
    }
    let mut delegate = (**obj).clone();
    let mut prefix: Vec<Leaf> = run[..iter_idx].to_vec();
    // Inline trailing single-use temp declares into the delegate
    // expr (`t = inner(); yield* t` → `yield* inner()`): the removed
    // pieces between the declare and the yield* are all consumed
    // machinery, so the observable evaluation order is unchanged.
    while let Expr::Temp { value: t, .. } = &delegate {
        let Some(last_sig) = prefix.iter().rposition(|l| !ys_skip_plumbing_leaf(l)) else {
            break;
        };
        let Leaf::Raw(Stmt::Declare {
            value, value_id, ..
        }) = &prefix[last_sig]
        else {
            break;
        };
        if value_id != t || uses.get(t).copied().unwrap_or(0) != 1 {
            break;
        }
        delegate = value.clone();
        prefix.remove(last_sig);
    }
    Some((delegate, iter_id, next_id, prefix))
}

/// The phi-init run: all phi assigns; the non-exceptional ones go to
/// one block and must set mode ← NEXT(2.0) and received ← undefined,
/// plus any loop-header phis still present for flag / iter / genobj / next.
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
        } else if lp.flag_in_phis && *target == lp.flag.1 {
            if !matches!(value, Expr::Lit(Lit::Bool(false))) {
                return None;
            }
            saw_flag = true;
        } else if lp.it_in_phis && *target == lp.it.1 {
            if temp_value(value) != Some(iter) {
                return None;
            }
            saw_it = true;
        } else if lp.g_in_phis && *target == lp.g.1 {
            saw_g = true;
        } else if temp_value(value) == Some(next) {
            saw_next += 1;
        } else {
            return None;
        }
    }
    let flag_ok = if lp.flag_in_phis { saw_flag } else { true };
    let it_ok = if lp.it_in_phis {
        saw_it
    } else {
        lp.it.0 == iter
    };
    let g_ok = if lp.g_in_phis { saw_g } else { true };
    let next_ok = saw_next == 1 || (saw_next == 0 && lp.next_method_val == Some(next));
    (saw_rt && saw_rv && flag_ok && it_ok && g_ok && next_ok).then_some(())
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

/// Arrangement A: bare siblings `[…, setup, Honest*, init, Honest*, While, exit?]`.
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
    let prev_sig_idx = |from: usize| -> Option<usize> {
        let mut j = from;
        while j > 0 {
            j -= 1;
            if !matches!(&nodes[j], SNode::Honest(_)) && !ys_is_exc_run(&nodes[j]) {
                return Some(j);
            }
        }
        None
    };
    let Some(init_idx) = prev_sig_idx(i) else {
        return false;
    };
    let Some(setup_idx) = prev_sig_idx(init_idx) else {
        return false;
    };
    let want_flag = (!lp.flag_in_phis).then_some(lp.flag.0);
    let Some((delegate, iter, next, prefix)) =
        ys_match_setup_with_flag(&nodes[setup_idx], async_, uses, want_flag)
    else {
        ys_trace("setup");
        return false;
    };
    if ys_match_init(&nodes[init_idx], &lp, iter, next).is_none() {
        ys_trace("init");
        return false;
    }
    let kept_honest: Vec<SNode> = nodes[setup_idx + 1..i]
        .iter()
        .filter(|n| matches!(n, SNode::Honest(_)))
        .cloned()
        .collect();
    if !async_ && !lp.in_loop_exit {
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
        new.extend(kept_honest);
        new.push(ys_stmt(&lp, delegate));
        new.extend(lp.continuation);
        nodes.splice(setup_idx..i + 2, new);
    } else {
        let mut new: Vec<SNode> = Vec::new();
        if !prefix.is_empty() {
            new.push(SNode::Stmts(prefix));
        }
        new.extend(kept_honest);
        new.push(ys_stmt(&lp, delegate));
        new.extend(lp.continuation);
        nodes.splice(setup_idx..i + 1, new);
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

/// Descend iteratively through nested single-child `Try` wrappers to the
/// innermost body sequence.
pub(in crate::folds) fn ys_innermost_body_mut(mut t: &mut SNode) -> &mut Vec<SNode> {
    loop {
        let has_single_try = matches!(
            t,
            SNode::Try { body, .. } if body.len() == 1 && matches!(body[0], SNode::Try { .. })
        );
        if has_single_try {
            let SNode::Try { body, .. } = t else {
                unreachable!()
            };
            t = &mut body[0];
        } else {
            let SNode::Try { body, .. } = t else {
                unreachable!()
            };
            return body;
        }
    }
}

pub(in crate::folds) fn ys_innermost_body(mut t: &SNode) -> Option<&Vec<SNode>> {
    loop {
        let SNode::Try { body, .. } = t else {
            return None;
        };
        if body.len() == 1 && matches!(body[0], SNode::Try { .. }) {
            t = &body[0];
        } else {
            return Some(body);
        }
    }
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
    let want_flag = (!lp.flag_in_phis).then_some(lp.flag.0);
    let Some((delegate, iter, next, prefix)) =
        ys_match_setup_with_flag(ssig[ssig.len() - 2], async_, uses, want_flag)
    else {
        ys_trace("frag:setup");
        return false;
    };
    if ys_match_init(ssig[ssig.len() - 1], &lp, iter, next).is_none() {
        ys_trace("frag:init");
        return false;
    }
    if !async_ && !lp.in_loop_exit {
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
    //    the continuation for in-loop completions).
    {
        let body = ys_innermost_body_mut(&mut nodes[i]);
        let pos = body
            .iter()
            .rposition(|n| matches!(n, SNode::While { .. }))
            .expect("the matched While");
        let mut new = vec![ys_stmt(&lp, delegate.clone())];
        if async_ || lp.in_loop_exit {
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
    // 3. The completion fragment (legacy sync): replace the exit-If with its
    //    continuation.
    if !async_ && !lp.in_loop_exit {
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
