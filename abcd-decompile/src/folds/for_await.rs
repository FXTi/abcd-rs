//! Plain-async `for await` driver-loop recovery (`d-P17`, `N70` residual 1).

use super::loops::*;
use super::*;

// The fold re-homes the done-arm tail AFTER the loop and emits the
// literal `for await (const x of …)`. All-or-nothing; any mismatch
// keeps the working while-loop driver.

/// What [`match_for_await_driver`] extracts from a candidate site.
pub(in crate::folds) struct DriverFold {
    /// The iterated expression.
    pub(in crate::folds) iter: Expr,
    /// The iteration binding.
    pub(in crate::folds) binding: String,
    /// The rebuilt loop body.
    pub(in crate::folds) body: Vec<SNode>,
    /// The done-arm's absorbed post-loop tail (re-homed after the loop).
    pub(in crate::folds) tail: Vec<SNode>,
    /// Trailing leaves of the gathered pre-run to consume.
    pub(in crate::folds) pre_cut: usize,
}

/// The adjacent statement leaves immediately before index `i`,
/// skipping honesty comments and empty runs (the driver's dissolved
/// try wrappers sit between the iterator setup and the loop).
pub(in crate::folds) fn gather_driver_pre_leaves(nodes: &[SNode], i: usize) -> Vec<Leaf> {
    let mut segs: Vec<&[Leaf]> = Vec::new();
    let mut j = i;
    while j > 0 {
        match &nodes[j - 1] {
            SNode::Honest(_) => j -= 1,
            SNode::Stmts(leaves) if leaves.is_empty() => j -= 1,
            SNode::Stmts(leaves) => {
                segs.push(leaves);
                j -= 1;
            }
            _ => break,
        }
    }
    let mut out = Vec::new();
    for seg in segs.iter().rev() {
        out.extend(seg.iter().cloned());
    }
    out
}

/// Drop `cut` trailing leaves of the gathered pre-run (walking
/// backwards, skipping honesty comments and empty runs); nodes left
/// empty are removed. Returns how many nodes were removed.
pub(in crate::folds) fn trim_driver_pre_leaves(
    nodes: &mut Vec<SNode>,
    i: usize,
    cut: usize,
) -> usize {
    let mut remaining = cut;
    let mut removed = 0;
    let mut j = i;
    while j > 0 && remaining > 0 {
        match &mut nodes[j - 1] {
            SNode::Honest(_) => j -= 1,
            SNode::Stmts(leaves) => {
                let take = remaining.min(leaves.len());
                leaves.truncate(leaves.len() - take);
                remaining -= take;
                if leaves.is_empty() {
                    nodes.remove(j - 1);
                    removed += 1;
                }
                j -= 1;
            }
            _ => break,
        }
    }
    removed
}

/// Match the plain-async `for await` driver at `nodes[i]` (an
/// unlabeled `while (true)`; see the section comment for the shape).
/// Pure: no mutation until [`apply_for_await_driver`].
pub(in crate::folds) fn match_for_await_driver(nodes: &[SNode], i: usize) -> Option<DriverFold> {
    let SNode::While {
        label: None,
        cond: None,
        body,
    } = &nodes[i]
    else {
        return None;
    };

    // ── Pre-loop: trailing phi assigns over `const it =
    // get-async-iterator(obj)`, `const next = it.next` (the corpus
    // matcher's plumbing, async-only).
    let pre = gather_driver_pre_leaves(nodes, i);
    let mut tail = pre.len();
    let mut assigns: Vec<(String, Expr)> = Vec::new();
    while tail > 0 {
        match &pre[tail - 1] {
            Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => {
                assigns.push((target.clone(), value.clone()));
                tail -= 1;
            }
            _ => break,
        }
    }
    let mut flag_decl: Option<String> = None;
    if tail >= 3
        && let Leaf::Raw(Stmt::Declare {
            name: fname,
            value: Expr::Lit(Lit::Bool(false)),
            ..
        }) = &pre[tail - 1]
        && matches!(
            &pre[tail - 3],
            Leaf::Raw(Stmt::Declare {
                value: Expr::Iter {
                    op: IterOp::GetAsyncIterator,
                    ..
                },
                ..
            })
        )
    {
        flag_decl = Some(fname.clone());
        tail -= 1;
    }
    if tail < 2 {
        return None;
    }
    let (it_name, iter_expr) = match &pre[tail - 2] {
        Leaf::Raw(Stmt::Declare {
            name: it_name,
            value:
                Expr::Iter {
                    op: IterOp::GetAsyncIterator,
                    obj,
                    ..
                },
            ..
        }) => (it_name.clone(), obj.as_ref().clone()),
        _ => return None,
    };
    let next_name = match &pre[tail - 1] {
        Leaf::Raw(Stmt::Declare {
            name: next_name,
            value: Expr::PropName { object, name, .. },
            ..
        }) if name == "next" && temp_name(object) == Some(it_name.as_str()) => next_name.clone(),
        _ => return None,
    };
    let pre_cut = pre.len() - tail + 2;

    // ── Body: the header statement runs (empty runs / honesty
    // comments interleaved), then the break-routed dispatch `if
    // (done) { TAIL; break } else { body; continue }` as the last
    // significant node.
    let mut hdr: Vec<Leaf> = Vec::new();
    let mut k = 0;
    let (cond, then, otherwise) = loop {
        match body.get(k) {
            Some(SNode::Stmts(run)) => {
                hdr.extend(run.iter().cloned());
                k += 1;
            }
            Some(SNode::Honest(_)) => k += 1,
            Some(SNode::If {
                cond,
                then,
                otherwise,
            }) => break (cond, then, otherwise),
            _ => return None,
        }
    };
    if otherwise.is_empty()
        || !body[k + 1..].iter().all(|n| {
            matches!(n, SNode::Honest(_)) || matches!(n, SNode::Stmts(run) if run.is_empty())
        })
    {
        return None;
    }

    // ── Header: [phi decls], `res = next.call(it)` (directly or via phis),
    // the folded dispatch's `tmp = await res` (REQUIRED — for-await awaits
    // the `next()` result; a driver without it is not this shape),
    // elided guards, `done = tmp.done` — and nothing else.
    let mut h = 0;
    let mut phi_names: Vec<String> = Vec::new();
    let mut phi_vids: BTreeMap<String, ValueId> = BTreeMap::new();
    while let Some(Leaf::Raw(Stmt::PhiDecl { name, value_id })) = hdr.get(h) {
        phi_names.push(name.clone());
        phi_vids.insert(name.clone(), *value_id);
        h += 1;
    }
    // Every trailing pre-loop assign must target a header phi (the
    // trim consumes them all — an assign to anything else would be
    // dropped live code).
    if !assigns.iter().all(|(t, _)| phi_names.contains(t)) {
        return None;
    }
    let (res_name, next_phi, recv_phi) = match hdr.get(h) {
        Some(Leaf::Raw(Stmt::Declare {
            name: res,
            value:
                Expr::Call {
                    callee,
                    this: Some(recv),
                    args,
                    kind: abcd_ir::op::CallKind::Dynamic | abcd_ir::op::CallKind::Direct,
                    ..
                },
            ..
        })) if args.is_empty() => {
            let callee = temp_name(callee)?.to_string();
            let recv = temp_name(recv)?.to_string();
            (res.clone(), callee, recv)
        }
        _ => return None,
    };
    let next_ok = if phi_names.contains(&next_phi) {
        assigns
            .iter()
            .any(|(t, v)| *t == next_phi && temp_name(v) == Some(next_name.as_str()))
    } else {
        next_phi == next_name
    };
    let recv_ok = if phi_names.contains(&recv_phi) {
        assigns
            .iter()
            .any(|(t, v)| *t == recv_phi && temp_name(v) == Some(it_name.as_str()))
    } else {
        recv_phi == it_name
    };
    if !next_ok || !recv_ok {
        return None;
    }
    h += 1;
    while matches!(hdr.get(h), Some(Leaf::Raw(Stmt::Elided { .. }))) {
        h += 1;
    }
    let await_name = match hdr.get(h) {
        Some(Leaf::Raw(Stmt::Declare {
            name,
            value:
                Expr::Await {
                    value,
                    uncaught: true,
                },
            ..
        })) if temp_name(value) == Some(res_name.as_str()) => name.clone(),
        _ => return None,
    };
    h += 1;
    while matches!(hdr.get(h), Some(Leaf::Raw(Stmt::Elided { .. }))) {
        h += 1;
    }
    let done_name = match hdr.get(h) {
        Some(Leaf::Raw(Stmt::Declare {
            name: done,
            value: Expr::PropName { object, name, .. },
            ..
        })) if name == "done" && temp_name(object) == Some(await_name.as_str()) => done.clone(),
        _ => return None,
    };
    h += 1;
    if h != hdr.len() {
        return None;
    }

    // ── The dispatch: a POSITIVE done test.
    let mut e = cond;
    let mut positive = true;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsTrue | UnOp::JumpNez,
                operand,
            } => e = operand,
            Expr::Unary {
                op: UnOp::IsFalse | UnOp::JumpEqz | UnOp::LogicalNot,
                operand,
            } => {
                positive = !positive;
                e = operand;
            }
            _ => break,
        }
    }
    if !positive || temp_name(e) != Some(done_name.as_str()) {
        return None;
    }

    // ── The done arm: the absorbed post-loop tail, followed by an
    // unlabeled exit `break` (or already diverging via `return`/`throw`
    // with no escaping breaks).
    let mut tail_nodes = then.clone();
    while matches!(tail_nodes.last(), Some(SNode::Stmts(run)) if run.is_empty()) {
        tail_nodes.pop();
    }
    if matches!(tail_nodes.last(), Some(SNode::Break { label: None })) {
        tail_nodes.pop();
    } else {
        let tf = seq_flow(&tail_nodes);
        if !tf.diverges || tf.live_break || subtree_has_labeled_jump(&tail_nodes) {
            return None;
        }
    }
    tail_nodes.retain(|n| !matches!(n, SNode::Stmts(run) if run.is_empty()));

    // ── The else arm: the loop body, the back-edge self-assigns, and
    // the (optional — falling through a while(true) body IS the
    // back-edge) trailing continue.
    let mut body_nodes = otherwise.clone();
    if matches!(body_nodes.last(), Some(SNode::Continue { label: None })) {
        body_nodes.pop();
    }
    drop_self_assign_tail(&mut body_nodes);
    body_nodes.retain(|n| !matches!(n, SNode::Stmts(run) if run.is_empty()));

    // ── The value binding (`const x = tmp.value`), plain or
    // cleanup-try-wrapped (leading honesty comments tolerated). Under
    // R2-C2, `const x = tmp.value` precedes `try_begin` while the body
    // sits inside the `IteratorClose` cleanup try.
    let mut binding: Option<String> = None;
    let mut splice_idx: Option<usize> = None;
    for (bi, n) in body_nodes.iter_mut().enumerate() {
        match n {
            SNode::Honest(_) => continue,
            SNode::Stmts(leaves) => {
                if let Some(b) = take_value_declare(leaves, &await_name) {
                    binding = Some(b);
                    let empty = leaves.is_empty();
                    let next_idx = if empty {
                        body_nodes.remove(bi);
                        bi
                    } else {
                        bi + 1
                    };
                    let mut ti = next_idx;
                    while matches!(body_nodes.get(ti), Some(SNode::Honest(_))) {
                        ti += 1;
                    }
                    if let Some(SNode::Try { catches, .. }) = body_nodes.get(ti)
                        && body_nodes[ti + 1..]
                            .iter()
                            .all(|tail_n| matches!(tail_n, SNode::Honest(_)))
                        && cleanup_handlers_ok(catches)
                    {
                        splice_idx = Some(ti);
                    }
                }
                break;
            }
            SNode::Try {
                body: tbody,
                catches,
                ..
            } => {
                for n2 in tbody.iter_mut() {
                    if let SNode::Stmts(leaves) = n2
                        && let Some(b) = take_value_declare(leaves, &await_name)
                    {
                        binding = Some(b);
                        break;
                    }
                }
                if binding.is_some() {
                    if !cleanup_handlers_ok(catches) {
                        return None;
                    }
                    splice_idx = Some(bi);
                }
                break;
            }
            _ => break,
        }
    }
    let binding = binding?;
    if let Some(bi) = splice_idx {
        // Replace the cleanup try with its body (loudly) — the
        // for-await protocol runs IteratorClose implicitly.
        let Some(SNode::Try { body: inner, .. }) = body_nodes.get(bi) else {
            unreachable!()
        };
        let inner = inner.clone();
        let mut replacement: Vec<SNode> = vec![SNode::Honest(
            "iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5)"
                .to_string(),
        )];
        replacement.extend(inner);
        body_nodes.splice(bi..bi + 1, replacement);
    }

    // ── Loop-carried bookkeeping phis (everything except the next/iter
    // plumbing): collapse each to its single invariant source by
    // substitution. A phi P folds iff EVERY assign to it (pre-loop
    // entry + back-edges, the only preds a structured natural-loop
    // header has) is either a self-assign (neutral) or the SAME
    // side-effect-free source expr X (a temp/identifier/literal), X is
    // not itself a header phi (no chains), and P is not referenced
    // after the loop. Phi-less bookkeeping (no real source) folds only
    // when entirely unused.
    let mut substs: Vec<(ValueId, Expr)> = Vec::new();
    for p in phi_names
        .iter()
        .filter(|p| **p != next_phi && **p != recv_phi)
    {
        let vid = phi_vids[p];
        let mut source: Option<Expr> = None;
        let mut ok = true;
        let visit_assign = |value: &Expr, source: &mut Option<Expr>, ok: &mut bool| {
            if temp_value(value) == Some(vid) {
                return; // self-assign: neutral
            }
            let legal = matches!(value, Expr::Temp { .. } | Expr::Ident(_) | Expr::Lit(_));
            match (legal, source.as_ref()) {
                (false, _) => *ok = false,
                (true, None) => *source = Some(value.clone()),
                (true, Some(x)) if *x == *value => {}
                (true, Some(_)) => *ok = false,
            }
        };
        for (t, v) in &assigns {
            if t == p {
                visit_assign(v, &mut source, &mut ok);
            }
        }
        walk_leaves(body, &mut |l| {
            if let Leaf::Raw(Stmt::PhiAssign { target, value, .. }) = l
                && target == p
            {
                visit_assign(value, &mut source, &mut ok);
            }
        });
        if !ok {
            return None;
        }
        let Some(x) = source else {
            // No real source: dead bookkeeping — foldable only when the
            // phi is never read.
            if nodes_use_any(&body_nodes, std::slice::from_ref(p))
                || nodes_use_any(&tail_nodes, std::slice::from_ref(p))
                || nodes_use_any(&nodes[i + 1..], std::slice::from_ref(p))
            {
                return None;
            }
            continue;
        };
        if temp_name(&x).is_some_and(|n| phi_names.iter().any(|pn| pn == n)) {
            return None;
        }
        if nodes_use_temp(&nodes[i + 1..], vid) {
            return None;
        }
        substs.push((vid, x));
    }

    // ── Apply the substitutions (value positions only), then the
    // whole-tree plumbing check: after the rebuild no internal temp
    // may be referenced by the kept body, the re-homed tail, or the
    // post-loop siblings (their declares are consumed by the fold).
    for (vid, x) in &substs {
        subst_temp_in_nodes(&mut body_nodes, *vid, x);
        subst_temp_in_nodes(&mut tail_nodes, *vid, x);
    }
    let mut internals: Vec<String> = phi_names.clone();
    internals.extend([it_name.clone(), next_name, res_name, await_name, done_name]);
    if let Some(f) = flag_decl {
        internals.push(f);
    }
    internals.retain(|n| *n != binding);
    if nodes_use_any(&body_nodes, &internals)
        || nodes_use_any(&tail_nodes, &internals)
        || nodes_use_any(&nodes[i + 1..], &internals)
    {
        return None;
    }
    // No residual assigns/decls of the folded phis may survive (a
    // self-assign outside the dropped back-edge run would print as an
    // assignment to an undeclared temp).
    if phi_names.iter().any(|p| {
        nodes_declare_or_assign(&body_nodes, p)
            || nodes_declare_or_assign(&tail_nodes, p)
            || nodes_declare_or_assign(&nodes[i + 1..], p)
    }) {
        return None;
    }
    Some(DriverFold {
        iter: iter_expr,
        binding,
        body: body_nodes,
        tail: tail_nodes,
        pre_cut,
    })
}

/// Apply a matched driver fold: replace the loop with the literal
/// `for await`, re-home the done-arm tail after it, and trim the
/// consumed pre-loop plumbing. Returns the next scan index.
pub(in crate::folds) fn apply_for_await_driver(
    nodes: &mut Vec<SNode>,
    i: usize,
    plan: DriverFold,
    stats: &mut FoldStats,
) -> usize {
    stats.for_await_of += 1;
    let tail_len = plan.tail.len();
    nodes[i] = SNode::ForOf {
        is_await: true,
        binding: plan.binding,
        iter: plan.iter,
        body: plan.body,
    };
    nodes.splice(i + 1..i + 1, plan.tail);
    let removed = trim_driver_pre_leaves(nodes, i, plan.pre_cut);
    i - removed + 1 + tail_len
}
