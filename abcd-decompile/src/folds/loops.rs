//! Iterator loops (`for..of`, `for await..of`, `for..in`) and dead loop-exit throw sweep.

use super::*;

// ── d-P17 (N70 residual 2): dead loop-exit dispatch throw sweep ────
//
// The async machine fold's break-routed dispatch (N70: a loop-internal
// await whose `mode == THROW` arm exits the loop) leaves the after-loop
// `throw <resume temp>` block in place — d-P16 kept it conservatively.
// Post-fold it is dead: the folded `await` rejects inline, so the break
// that routed to the exit block is gone. This pass removes the residue,
// but only under a whole-node unreachability proof; any doubt keeps it.

/// Termination/divergence facts for the unreachability proof.
pub(in crate::folds) struct SeqFlow {
    /// A statically LIVE unlabeled `break` exists (one that would exit
    /// the loop whose body is being analyzed — nested loops'/switches'
    /// breaks are inner-scoped and never reported).
    pub(in crate::folds) live_break: bool,
    /// Control can never pass the end of the sequence.
    pub(in crate::folds) diverges: bool,
}

pub(in crate::folds) const FLOW_FALLTHROUGH: SeqFlow = SeqFlow {
    live_break: false,
    diverges: false,
};

/// Sequence flow: nodes after a diverging node are statically dead —
/// their breaks do not count as live.
pub(in crate::folds) fn seq_flow(nodes: &[SNode]) -> SeqFlow {
    let mut out = FLOW_FALLTHROUGH;
    for n in nodes {
        if out.diverges {
            continue;
        }
        let f = node_flow(n);
        out.live_break |= f.live_break;
        out.diverges = f.diverges;
    }
    out
}

pub(in crate::folds) fn node_flow(n: &SNode) -> SeqFlow {
    match n {
        SNode::Stmts(run) => SeqFlow {
            live_break: false,
            // A `throw`/`return` leaf diverges (later leaves in the run
            // are dead); a bare `unreachable` marker denotes dead code —
            // control never passes it either.
            diverges: run
                .iter()
                .any(|l| matches!(l, Leaf::Raw(Stmt::Throw(_) | Stmt::Return(_))))
                || (!run.is_empty()
                    && run
                        .iter()
                        .all(|l| matches!(l, Leaf::Raw(Stmt::Unreachable)))),
        },
        SNode::Break { .. } => SeqFlow {
            live_break: true,
            diverges: true,
        },
        SNode::Continue { .. } => SeqFlow {
            live_break: false,
            diverges: true,
        },
        SNode::Honest(_) => FLOW_FALLTHROUGH,
        SNode::If {
            then, otherwise, ..
        } => {
            let t = seq_flow(then);
            let o = seq_flow(otherwise);
            SeqFlow {
                live_break: t.live_break || o.live_break,
                diverges: !then.is_empty() && !otherwise.is_empty() && t.diverges && o.diverges,
            }
        }
        // A nested `while (true)` never completes when its own body has
        // no live break; its unlabeled breaks are ITS exits (inner
        // scope), not the analyzed loop's.
        SNode::While {
            cond: None, body, ..
        } => SeqFlow {
            live_break: false,
            diverges: !seq_flow(body).live_break,
        },
        // Conditional loops / for-of / for-in / do-while / switch may
        // complete normally; their unlabeled breaks are inner-scoped.
        SNode::While { .. }
        | SNode::DoWhile { .. }
        | SNode::ForOf { .. }
        | SNode::ForIn { .. }
        | SNode::Switch { .. } => FLOW_FALLTHROUGH,
        // A labeled block does not capture UNLABELED breaks (labeled
        // jumps are pre-bailed by the caller), so it is transparent.
        SNode::Labeled { body, .. } => seq_flow(body),
        // Exceptional edges: a break in the body, any catch, or the
        // finally is live when reachable there (an exception can
        // transfer control at any point, so catch/finally sequences
        // are analyzed from their own entry). The try as a whole may
        // complete normally — conservative: never diverges.
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            let mut live = seq_flow(body).live_break;
            for c in catches {
                live |= seq_flow(&c.body).live_break;
            }
            if let Some(f) = finally {
                live |= seq_flow(f).live_break;
            }
            SeqFlow {
                live_break: live,
                diverges: false,
            }
        }
    }
}

/// Any labeled break/continue anywhere in the subtree → the caller
/// bails (a labeled jump could target a label between the loop and the
/// residue in shapes this pass does not model — doubt keeps the block).
pub(in crate::folds) fn subtree_has_labeled_jump(nodes: &[SNode]) -> bool {
    nodes.iter().any(|n| match n {
        SNode::Break { label: Some(_) } | SNode::Continue { label: Some(_) } => true,
        SNode::If {
            then, otherwise, ..
        } => subtree_has_labeled_jump(then) || subtree_has_labeled_jump(otherwise),
        SNode::While { body, .. }
        | SNode::DoWhile { body, .. }
        | SNode::Labeled { body, .. }
        | SNode::ForOf { body, .. }
        | SNode::ForIn { body, .. } => subtree_has_labeled_jump(body),
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            subtree_has_labeled_jump(body)
                || catches.iter().any(|c| subtree_has_labeled_jump(&c.body))
                || finally
                    .as_ref()
                    .is_some_and(|f| subtree_has_labeled_jump(f))
        }
        SNode::Switch { cases, .. } => cases.iter().any(|c| subtree_has_labeled_jump(&c.body)),
        SNode::Stmts(_)
        | SNode::Break { label: None }
        | SNode::Continue { label: None }
        | SNode::Honest(_) => false,
    })
}

/// Sweep the dead loop-exit dispatch throws. A trailing `throw <t>`
/// run (optionally followed by the `Unreachable` marker) after a
/// `while (true)` loop is removed iff ALL of:
///
/// 1. **Residue shape**: the next significant sibling (skipping
///    honesty comments and empty statement runs) is a single run of
///    exactly `throw <t>` (+ `Unreachable`), where `t` is a temp the
///    loop's own header declares as an uncaught `await` (the folded
///    dispatch's resumption temp — this scopes the sweep to the N70
///    residue; arbitrary dead code is not touched).
/// 2. **No normal exit**: the loop is an unlabeled `while (true)` (no
///    condition — it cannot fall through; no label — a labeled break
///    from inside would land on the residue).
/// 3. **No live exit break (preds)**: every unlabeled `break` in the
///    loop body is statically dead (a diverging statement precedes it
///    in its sequence), and no labeled `break`/`continue` appears
///    anywhere in the subtree.
/// 4. **Exceptional edges**: an exception raised inside the loop
///    propagates to the nearest enclosing CATCH — never to a plain
///    sibling statement — so the residue (a fall-through sibling in
///    the same node sequence, not a handler) is unreachable from the
///    loop's exceptional exits. The region tree is already reflected
///    in the sibling structure this pass runs on (it runs after
///    rethrow-try dissolution in [`fold_seq`]).
///
/// The removed run is replaced by an honesty comment.
pub(in crate::folds) fn sweep_dead_loop_exit_throws(nodes: &mut [SNode], stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let fire = match &nodes[i] {
            SNode::While {
                label: None,
                cond: None,
                body,
            } => residue_match(nodes, i, body),
            _ => None,
        };
        let Some(j) = fire else {
            i += 1;
            continue;
        };
        stats.dead_exit_throw += 1;
        nodes[j] = SNode::Honest(
            "dead loop-exit dispatch residue elided (provably unreachable: unlabeled `while (true)` with no live exit break — the folded await rejects inline; N70 residual)"
                .to_string(),
        );
        i += 1;
    }
}

/// The residue check for one candidate loop at `nodes[i]`: the index
/// of the removable throw run when every proof obligation holds.
pub(in crate::folds) fn residue_match(nodes: &[SNode], i: usize, body: &[SNode]) -> Option<usize> {
    // Obligation 1a: the loop header's own (direct) statement runs
    // declare an uncaught `await` temp — the folded dispatch's
    // resumption temp.
    let mut header_awaits: BTreeSet<ValueId> = BTreeSet::new();
    for n in body {
        let SNode::Stmts(run) = n else { break };
        for l in run {
            if let Leaf::Raw(Stmt::Declare {
                value: Expr::Await { uncaught: true, .. },
                value_id,
                ..
            }) = l
            {
                header_awaits.insert(*value_id);
            }
        }
    }
    if header_awaits.is_empty() {
        return None;
    }
    // Obligation 1b: the next significant sibling is exactly the throw
    // residue run.
    let mut j = i + 1;
    while j < nodes.len() {
        match &nodes[j] {
            SNode::Honest(_) => j += 1,
            SNode::Stmts(run) if run.is_empty() => j += 1,
            _ => break,
        }
    }
    let SNode::Stmts(run) = nodes.get(j)? else {
        return None;
    };
    let thrown = match run.as_slice() {
        [Leaf::Raw(Stmt::Throw(e))] | [Leaf::Raw(Stmt::Throw(e)), Leaf::Raw(Stmt::Unreachable)] => {
            temp_value(e)?
        }
        _ => return None,
    };
    if !header_awaits.contains(&thrown) {
        return None;
    }
    // Obligations 2–3 (the loop shape is checked by the caller): no
    // labeled jumps anywhere, no live unlabeled exit break.
    if subtree_has_labeled_jump(body) || seq_flow(body).live_break {
        return None;
    }
    Some(j)
}

// ── Folds 3+4: iterator loops ────────────────────────────────────────

/// What the for-of/for-in matcher extracts from a candidate site.
pub(in crate::folds) struct LoopFold {
    pub(in crate::folds) is_await: bool,
    pub(in crate::folds) is_in: bool,
    /// The iterated object.
    pub(in crate::folds) iter: Expr,
    /// Trailing leaves of the merged pre-loop run to consume.
    pub(in crate::folds) pre_cut: usize,
    /// The header phi names (plumbing).
    pub(in crate::folds) phi_names: Vec<String>,
    /// The `res = next()` temp (for-of only).
    pub(in crate::folds) res_name: Option<String>,
    /// The `done` temp (for-of only).
    pub(in crate::folds) done_name: Option<String>,
    /// Further internal temps (`it`, `next`, the for-in header phis).
    pub(in crate::folds) extra_internals: Vec<String>,
    /// Extra header-phi wiring to hoist ABOVE the folded loop (for-in
    /// only, N74): `let`-less `var` decl + the pre-loop assign of each
    /// loop-invariant pass-through phi, emitted as one `Stmts` node
    /// immediately before the `ForIn`.
    pub(in crate::folds) hoisted: Vec<Leaf>,
}

/// Normalize the two loop-test emission shapes to `(test, body)`:
/// `while (test) { body }` directly, and the sound d-P4 form
/// `while (true) { wiring…; if (test) break; body }` (emitted when the
/// loop header carries statements the condition reads — the clean form
/// would reference them before their declaration). The `break` node is
/// consumed by the normalization.
pub(in crate::folds) fn normalize_loop_test(body: &[SNode]) -> Option<(Expr, Vec<SNode>)> {
    // The header run, then `if (test) break;` (no else), then the rest.
    let [
        SNode::Stmts(_),
        SNode::If {
            cond,
            then,
            otherwise,
        },
        rest @ ..,
    ] = body
    else {
        return None;
    };
    if !matches!(then.as_slice(), [SNode::Break { label: None }]) || !otherwise.is_empty() {
        return None;
    }
    let mut new_body = body.to_vec();
    new_body.remove(1);
    let _ = rest;
    Some((cond.clone(), new_body))
}

pub(in crate::folds) fn fold_loops(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let normalized: Option<(Expr, Vec<SNode>)> = match &nodes[i] {
            SNode::While {
                label: None,
                cond: Some(wcond),
                body,
            } => Some((wcond.clone(), body.clone())),
            SNode::While {
                label: None,
                cond: None,
                body,
            } => normalize_loop_test(body),
            _ => None,
        };
        let folded = normalized.and_then(|(test, body)| {
            let pre = merged_pre_leaves(nodes, i);
            match_for_of(&pre, &test, &body)
                .or_else(|| match_for_in(&pre, &test, &body))
                .map(|f| (f, body))
        });
        let Some((folded, norm_body)) = folded else {
            // d-P17 (N70 residual 1): the plain-async `for await`
            // driver is not the corpus for-of shape (its loop header
            // carries the folded dispatch's await temp, and the done
            // arm absorbed the post-loop tail) — try the driver
            // sibling matcher.
            if matches!(
                &nodes[i],
                SNode::While {
                    label: None,
                    cond: None,
                    ..
                }
            ) && let Some(plan) = match_for_await_driver(nodes, i)
            {
                i = apply_for_await_driver(nodes, i, plan, stats);
                continue;
            }
            i += 1;
            continue;
        };
        if !matches!(&nodes[i], SNode::While { label: None, .. }) {
            unreachable!()
        }
        let Some((binding, new_body)) = rebuild_loop_body(&norm_body, &folded) else {
            i += 1;
            continue;
        };
        if folded.is_in {
            stats.for_in += 1;
        } else if folded.is_await {
            stats.for_await_of += 1;
        } else {
            stats.for_of += 1;
        }
        // N74: a for-in with extra pass-through header phis re-emits
        // their (loop-invariant) wiring as one `Stmts` node ABOVE the
        // folded loop (LICM — see `match_for_in`).
        let advanced = if folded.is_in && !folded.hoisted.is_empty() {
            let for_in = SNode::ForIn {
                binding,
                obj: folded.iter,
                body: new_body,
            };
            nodes.splice(i..i + 1, [SNode::Stmts(folded.hoisted.clone()), for_in]);
            2
        } else {
            nodes[i] = if folded.is_in {
                SNode::ForIn {
                    binding,
                    obj: folded.iter,
                    body: new_body,
                }
            } else {
                SNode::ForOf {
                    is_await: folded.is_await,
                    binding,
                    iter: folded.iter,
                    body: new_body,
                }
            };
            1
        };
        // Trim the consumed tail of the pre-loop run (this may remove
        // nodes BEFORE i, shifting it left).
        let removed = trim_pre_leaves(nodes, i, folded.pre_cut);
        i = i + advanced - removed;
    }
}

/// N74 residual (test262 `language/statements/labeled/S12.12_A1_T1`):
/// the DEGENERATE for-in. `L: for (k in obj) { body; break L; }` — an
/// unconditional break at the body's tail — compiles (opt-level 0) to
/// a loop head whose ONLY back-edge is unreachable, so the structurer
/// sees an acyclic region and builds no `While` node at all. The
/// iterator machinery is left in straight-line code as siblings:
///
/// ```text
/// … it = GetPropIterator(obj) /* phi-assign ending its Stmts run */
/// var it; /* phi */  const k = NextPropName(it);
/// if (k == undefined) {} else { body }
/// ```
///
/// and the plumbing fallback binds `k` to the OBJECT, not the first
/// key — the body then computes garbage (the labeled row's
/// `result += object[i]` became `0 + object[object]` = NaN and the
/// test's assertion threw). The region provably runs the body AT MOST
/// ONCE, for the FIRST enumerated key (a live back-edge would have
/// produced a `While` — that is exactly why none exists here), so the
/// faithful reconstruction is a for-in whose body breaks at the tail:
/// `for (const k in obj) { body; break; }`.
pub(in crate::folds) fn fold_single_pass_for_ins(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        if let Some(plan) = match_single_pass_for_in(nodes, i) {
            let SinglePassForIn {
                assign,
                binding,
                obj,
                body,
            } = plan;
            // Consume the plumbing phi-assign from its run (drop the
            // run itself when it held only that leaf).
            let SNode::Stmts(pre) = &mut nodes[assign] else {
                unreachable!()
            };
            pre.pop();
            let mut body = body;
            if !seq_flow(&body).diverges {
                body.push(SNode::Break { label: None });
            }
            let for_in = SNode::ForIn { binding, obj, body };
            nodes.splice(i..i + 2, [for_in]);
            if matches!(&nodes[assign], SNode::Stmts(pre) if pre.is_empty()) {
                nodes.remove(assign);
                i = assign;
            } else {
                i = assign + 1;
            }
            stats.for_in += 1;
            continue;
        }
        i += 1;
    }
}

/// The extracted pieces of one degenerate for-in match.
pub(in crate::folds) struct SinglePassForIn {
    /// Index of the `Stmts` run whose LAST leaf is the
    /// `GetPropIterator` phi-assign (the leaf is consumed).
    pub(in crate::folds) assign: usize,
    /// The key binding (the `NextPropName` result temp).
    pub(in crate::folds) binding: String,
    /// The enumerated object.
    pub(in crate::folds) obj: Expr,
    /// The single-pass body (the non-taken exit arm of the test).
    pub(in crate::folds) body: Vec<SNode>,
}

/// Match the degenerate for-in with the header `Stmts` at index `i`:
/// `[PhiDecl it, const k = NextPropName(it)]` at `i`, the
/// `it = GetPropIterator(obj)` phi-assign as the LAST leaf of the
/// nearest previous non-`Honest` `Stmts` run, and the
/// `if (k == undefined) {} else { body }` exit test at `i + 1`.
pub(in crate::folds) fn match_single_pass_for_in(
    nodes: &[SNode],
    i: usize,
) -> Option<SinglePassForIn> {
    let SNode::Stmts(hdr) = &nodes[i] else {
        return None;
    };
    let [
        Leaf::Raw(Stmt::PhiDecl { name: it, .. }),
        Leaf::Raw(Stmt::Declare {
            name: k,
            value:
                Expr::Iter {
                    op: IterOp::NextPropName,
                    obj: it_ref,
                    ..
                },
            ..
        }),
    ] = hdr.as_slice()
    else {
        return None;
    };
    if temp_name(it_ref) != Some(it.as_str()) {
        return None;
    }
    // The iterator wiring: the last leaf of the nearest previous
    // non-`Honest` node (a dissolved rethrow-only try leaves an
    // `Honest` marker between the pre-leaves and the assign).
    let mut a = i;
    while a > 0 && matches!(&nodes[a - 1], SNode::Honest(_)) {
        a -= 1;
    }
    a = a.checked_sub(1)?;
    let SNode::Stmts(pre) = &nodes[a] else {
        return None;
    };
    let Some(Leaf::Raw(Stmt::PhiAssign {
        target,
        value:
            Expr::Iter {
                op: IterOp::GetPropIterator,
                obj,
                ..
            },
        ..
    })) = pre.last()
    else {
        return None;
    };
    if target != it {
        return None;
    }
    // The exit test: `k == undefined` (any polarity/wrapping) with the
    // body on the not-done arm and the other arm empty.
    let Some(SNode::If {
        cond,
        then,
        otherwise,
    }) = nodes.get(i + 1)
    else {
        return None;
    };
    let mut e = cond;
    let mut inverted = false;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsTrue,
                operand,
            } => e = operand,
            Expr::Unary {
                op: UnOp::IsFalse | UnOp::LogicalNot,
                operand,
            } => {
                inverted = !inverted;
                e = operand;
            }
            _ => break,
        }
    }
    let Expr::Compare { op, left, right } = e else {
        return None;
    };
    let eq = matches!(op, CmpOp::Eq | CmpOp::StrictEq);
    let neq = matches!(op, CmpOp::NotEq | CmpOp::StrictNotEq);
    let tests_undef = (matches!(left.as_ref(), Expr::Lit(Lit::Undefined))
        && temp_name(right) == Some(k.as_str()))
        || (matches!(right.as_ref(), Expr::Lit(Lit::Undefined))
            && temp_name(left) == Some(k.as_str()));
    if !tests_undef || !(eq || neq) {
        return None;
    }
    // The body runs when the key is NOT undefined.
    let body_on_otherwise = eq != inverted;
    let (body, empty_arm) = if body_on_otherwise {
        (otherwise, then)
    } else {
        (then, otherwise)
    };
    if !empty_arm.is_empty() {
        return None;
    }
    let internals = [it.clone(), k.clone()];
    // The iterated expression must not reference the internals…
    if internals.iter().any(|n| expr_uses_name(obj, n)) {
        return None;
    }
    // …and NOTHING outside the three matched nodes may use them (the
    // phi-decl/plumbing temps die with the fold; the binding lives on
    // as the for-in binding, so uses inside the body stay valid).
    for (j, n) in nodes.iter().enumerate() {
        if j == a || j == i || j == i + 1 {
            continue;
        }
        if node_uses_any(n, &internals) {
            return None;
        }
    }
    // The assign run's remaining leaves must not use the internals
    // either (they precede the assign, so only a pathological
    // re-declaration could).
    if pre[..pre.len() - 1]
        .iter()
        .any(|l| internals.iter().any(|n| leaf_uses_name(l, n)))
    {
        return None;
    }
    if nodes_use_any(body, &internals[..1]) {
        return None;
    }
    // A stray `continue` would bind to the NEW loop and re-iterate —
    // the acyclic region this shape comes from cannot contain one.
    if subtree_has_continue(body) {
        return None;
    }
    Some(SinglePassForIn {
        assign: a,
        binding: k.clone(),
        obj: obj.as_ref().clone(),
        body: body.clone(),
    })
}

/// A `continue` anywhere in the subtree (the degenerate for-in's body
/// must not grow one — see the matcher's guard).
pub(in crate::folds) fn subtree_has_continue(nodes: &[SNode]) -> bool {
    nodes.iter().any(|n| match n {
        SNode::Continue { .. } => true,
        SNode::If {
            then, otherwise, ..
        } => subtree_has_continue(then) || subtree_has_continue(otherwise),
        // A nested loop's continues target THAT loop — stop the walk.
        SNode::While { .. } | SNode::DoWhile { .. } | SNode::ForOf { .. } | SNode::ForIn { .. } => {
            false
        }
        SNode::Labeled { body, .. } => subtree_has_continue(body),
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            subtree_has_continue(body)
                || catches.iter().any(|c| subtree_has_continue(&c.body))
                || finally.as_ref().is_some_and(|f| subtree_has_continue(f))
        }
        SNode::Switch { cases, .. } => cases.iter().any(|c| subtree_has_continue(&c.body)),
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Honest(_) => false,
    })
}

/// The concatenated leaf run of the adjacent `Stmts` nodes immediately
/// before index `i`.
pub(in crate::folds) fn merged_pre_leaves(nodes: &[SNode], i: usize) -> Vec<Leaf> {
    let mut out: Vec<Leaf> = Vec::new();
    let mut j = i;
    while j > 0 {
        match &nodes[j - 1] {
            SNode::Stmts(leaves) => {
                out.splice(0..0, leaves.iter().cloned());
                j -= 1;
            }
            _ => break,
        }
    }
    out
}

/// Drop `cut` trailing leaves of the merged pre-run (walking backwards
/// through adjacent `Stmts` nodes); removes nodes left empty. Returns
/// how many nodes were removed (the caller's index shifts left).
pub(in crate::folds) fn trim_pre_leaves(nodes: &mut Vec<SNode>, i: usize, cut: usize) -> usize {
    let mut remaining = cut;
    let mut removed = 0;
    let mut j = i;
    while j > 0 && remaining > 0 {
        match &mut nodes[j - 1] {
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

/// for-of / for-await-of: the es2abc shape (probe-verified stable
/// across all 6 corpus es2abc versions).
pub(in crate::folds) fn match_for_of(
    pre: &[Leaf],
    wcond: &Expr,
    body: &[SNode],
) -> Option<LoopFold> {
    // Pre-loop tail: `const it = get-iterator(obj)` (or async),
    // `const next = it.next`, then phi assigns into the header phis.
    let mut tail = pre.len();
    // Trailing phi assigns (their values may be constants — the done
    // flag initializes to `false`; skip those).
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
    if tail < 2 {
        return None;
    }
    let (it_name, iter_expr, is_await) = match &pre[tail - 2] {
        Leaf::Raw(Stmt::Declare {
            name: it_name,
            value:
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj,
                    ..
                },
            ..
        }) => (it_name.clone(), obj.as_ref().clone(), false),
        Leaf::Raw(Stmt::Declare {
            name: it_name,
            value:
                Expr::Iter {
                    op: IterOp::GetAsyncIterator,
                    obj,
                    ..
                },
            ..
        }) => (it_name.clone(), obj.as_ref().clone(), true),
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
    // The header: phi decls, `res = <next-phi>()`, [elided guards],
    // `done = res.done` — and nothing else.
    let SNode::Stmts(hdr) = body.first()? else {
        return None;
    };
    let mut k = 0;
    let mut phi_names: Vec<String> = Vec::new();
    while let Some(Leaf::Raw(Stmt::PhiDecl { name, .. })) = hdr.get(k) {
        phi_names.push(name.clone());
        k += 1;
    }
    if phi_names.is_empty() {
        return None;
    }
    let (res_name, next_phi) = match hdr.get(k) {
        Some(Leaf::Raw(Stmt::Declare {
            name: res,
            value:
                Expr::Call {
                    callee,
                    args,
                    kind: abcd_ir::op::CallKind::Dynamic | abcd_ir::op::CallKind::Direct,
                    ..
                },
            ..
        })) if args.is_empty() => {
            let callee = temp_name(callee)?.to_string();
            if !phi_names.contains(&callee) {
                return None;
            }
            (res.clone(), callee)
        }
        _ => return None,
    };
    k += 1;
    while matches!(hdr.get(k), Some(Leaf::Raw(Stmt::Elided { .. }))) {
        k += 1;
    }
    let done_name = match hdr.get(k) {
        Some(Leaf::Raw(Stmt::Declare {
            name: done,
            value: Expr::PropName { object, name, .. },
            ..
        })) if name == "done" && temp_name(object) == Some(res_name.as_str()) => done.clone(),
        _ => return None,
    };
    k += 1;
    if k != hdr.len() {
        return None;
    }
    // The while condition must be the done test.
    if temp_name(strip_cond(wcond))? != done_name {
        return None;
    }
    // The pre-loop phi assigns must wire `next` and `it` into the
    // header phis.
    let it_phi = assigns
        .iter()
        .find(|(_, v)| temp_name(v) == Some(it_name.as_str()))
        .map(|(t, _)| t.clone());
    if !assigns
        .iter()
        .any(|(t, v)| *t == next_phi && temp_name(v) == Some(next_name.as_str()))
    {
        return None;
    }
    let mut extra = vec![it_name, next_name, done_name.clone()];
    if let Some(p) = it_phi {
        extra.push(p);
    }
    Some(LoopFold {
        is_await,
        is_in: false,
        iter: iter_expr,
        pre_cut: pre.len() - tail + 2,
        phi_names,
        res_name: Some(res_name),
        done_name: Some(done_name),
        extra_internals: extra,
        hoisted: Vec::new(),
    })
}

/// for-in: `it = get-prop-iterator(obj)` (phi at the header),
/// `k = next-prop-name(it)`, `undefined == k` exit test.
///
/// N74: the header may carry EXTRA phis besides the iterator — any
/// register live across the loop gets a pass-through phi (e.g. the
/// OUTER for-in's iterator in nested loops: its value never changes
/// inside, so the back-edge is a self-assign). Those extra phis are
/// loop-invariant bindings: the fold hoists their decl + pre-loop
/// wiring assign ABOVE the folded `for…in` (LICM — the value is the
/// same on every iteration), so no use of them can dangle afterwards.
pub(in crate::folds) fn match_for_in(
    pre: &[Leaf],
    wcond: &Expr,
    body: &[SNode],
) -> Option<LoopFold> {
    // The header: one or more phi decls, then `const k = next-prop-name(it)`
    // reading one of them — and nothing else.
    let SNode::Stmts(hdr) = body.first()? else {
        return None;
    };
    let mut k = 0;
    let mut phi_names: Vec<String> = Vec::new();
    while let Some(Leaf::Raw(Stmt::PhiDecl { name, .. })) = hdr.get(k) {
        phi_names.push(name.clone());
        k += 1;
    }
    if phi_names.is_empty() || k + 1 != hdr.len() {
        return None;
    }
    let (binding, it_phi) = match &hdr[k] {
        Leaf::Raw(Stmt::Declare {
            name,
            value:
                Expr::Iter {
                    op: IterOp::NextPropName,
                    obj: it,
                    ..
                },
            ..
        }) => {
            let it = temp_name(it)?.to_string();
            if !phi_names.contains(&it) {
                return None;
            }
            (name.clone(), it)
        }
        _ => return None,
    };
    // The pre-loop tail: exactly one wiring phi-assign per header phi
    // (any order). The iterator's value must be the `GetPropIterator`.
    let mut tail = pre.len();
    let mut wiring: BTreeMap<String, Leaf> = BTreeMap::new();
    while tail > 0 {
        match &pre[tail - 1] {
            Leaf::Raw(Stmt::PhiAssign { target, .. })
                if phi_names.contains(target) && !wiring.contains_key(target) =>
            {
                wiring.insert(target.clone(), pre[tail - 1].clone());
                tail -= 1;
            }
            _ => break,
        }
    }
    if wiring.len() != phi_names.len() {
        return None;
    }
    let obj = match wiring.remove(&it_phi) {
        Some(Leaf::Raw(Stmt::PhiAssign {
            value:
                Expr::Iter {
                    op: IterOp::GetPropIterator,
                    obj,
                    ..
                },
            ..
        })) => obj.as_ref().clone(),
        _ => return None,
    };
    // The extra phis' initial values must not reference any header
    // internal — the hoisted assign is emitted ABOVE the loop, where
    // those temps no longer exist (the fold consumes their decls).
    if wiring.values().any(|l| {
        let Leaf::Raw(Stmt::PhiAssign { value, .. }) = l else {
            unreachable!()
        };
        phi_names.iter().any(|n| expr_uses_name(value, n))
    }) {
        return None;
    }
    // The hoisted wiring, in header order: the phi decl + its pre-loop
    // assign (the iterator's own wiring is consumed by the fold).
    let mut hoisted: Vec<Leaf> = Vec::new();
    for (idx, name) in phi_names.iter().enumerate() {
        if *name == it_phi {
            continue;
        }
        hoisted.push(hdr[idx].clone());
        hoisted.push(wiring[name].clone());
    }
    // The condition: `undefined == k` (any wrapper depth, any equality).
    let eq_ok = match strip_cond(wcond) {
        Expr::Compare {
            op:
                abcd_ir::op::CmpOp::Eq
                | abcd_ir::op::CmpOp::NotEq
                | abcd_ir::op::CmpOp::StrictEq
                | abcd_ir::op::CmpOp::StrictNotEq,
            left,
            right,
        } => {
            (matches!(left.as_ref(), Expr::Lit(Lit::Undefined))
                && temp_name(right) == Some(binding.as_str()))
                || (matches!(right.as_ref(), Expr::Lit(Lit::Undefined))
                    && temp_name(left) == Some(binding.as_str()))
        }
        _ => false,
    };
    if !eq_ok {
        return None;
    }
    Some(LoopFold {
        is_await: false,
        is_in: true,
        iter: obj,
        pre_cut: pre.len() - tail,
        phi_names: phi_names.clone(),
        res_name: None,
        done_name: None,
        extra_internals: phi_names,
        hoisted,
    })
}

/// Rebuild the folded loop body: remove the header plumbing, extract
/// the value binding, drop the back-edge self-assigns and (checked)
/// the iterator-cleanup try. Returns `(binding, new_body)`.
pub(in crate::folds) fn rebuild_loop_body(
    body: &[SNode],
    folded: &LoopFold,
) -> Option<(String, Vec<SNode>)> {
    if folded.is_in {
        let Some(SNode::Stmts(hdr)) = &body.first() else {
            return None;
        };
        // The header phi temps (the iterator + any pass-through phis)
        // with their SSA provenance — the copy-elimination roots.
        let mut roots: BTreeMap<String, Expr> = BTreeMap::new();
        for l in hdr.iter() {
            if let Leaf::Raw(Stmt::PhiDecl { name, value_id }) = l {
                roots.insert(
                    name.clone(),
                    Expr::Temp {
                        name: name.clone(),
                        value: *value_id,
                    },
                );
            }
        }
        let binding = match hdr.last() {
            Some(Leaf::Raw(Stmt::Declare { name, .. })) => name.clone(),
            _ => return None,
        };
        let mut out: Vec<SNode> = body.to_vec();
        out.remove(0);
        // N74: the for-in iterator is a stateful, loop-invariant object
        // (`NextPropName` advances it internally) and any extra header
        // phi is a loop-invariant pass-through by construction — but
        // es2abc merges their registers through the loop body's branch
        // joins, leaving redundant copy phis (`v335 = phi(v325, v325)`)
        // and self-assign back-edges (`v325 = v325`, possibly nested in
        // an early-continue arm). Their assigns veto the fold via the
        // internal-temp use check below, and the fallback emission's
        // self-assign back-edge stalls the loop forever. Eliminate the
        // identity copies and no-op self-assigns first.
        elim_internal_copy_phis(&mut out, &roots);
        drop_self_assign_tail(&mut out);
        if nodes_use_any(&out, &folded.extra_internals) {
            return None;
        }
        return Some((binding, out));
    }
    let res_name = folded.res_name.clone()?;
    let mut out: Vec<SNode> = body.to_vec();
    if out.is_empty() {
        return None;
    }
    out.remove(0); // the header stmts (matched exhaustively)
    drop_self_assign_tail(&mut out);
    // The value binding: first declare of the first remaining node
    // (plain or cleanup-try-wrapped; leading honesty comments / empty
    // runs tolerated). Under R2-C2, `const x = res.value` sits just
    // before `try_begin` while the rest of the loop body is wrapped in
    // the `IteratorClose` cleanup try.
    let mut binding: Option<String> = None;
    let mut splice_idx: Option<usize> = None;
    for (bi, n) in out.iter_mut().enumerate() {
        match n {
            SNode::Honest(_) => continue,
            SNode::Stmts(leaves) if leaves.is_empty() => continue,
            SNode::Stmts(leaves) => {
                if let Some(b) = take_value_declare(leaves, &res_name) {
                    binding = Some(b);
                    let empty = leaves.is_empty();
                    let next_idx = if empty {
                        out.remove(bi);
                        bi
                    } else {
                        bi + 1
                    };
                    let mut ti = next_idx;
                    while ti < out.len()
                        && matches!(
                            &out[ti],
                            SNode::Honest(_) | SNode::Stmts(_)
                                if matches!(&out[ti], SNode::Honest(_))
                                    || matches!(&out[ti], SNode::Stmts(r) if r.is_empty())
                        )
                    {
                        ti += 1;
                    }
                    if let Some(SNode::Try { catches, .. }) = out.get(ti)
                        && out[ti + 1..].iter().all(|tail_n| {
                            matches!(tail_n, SNode::Honest(_) | SNode::Continue { label: None })
                                || matches!(tail_n, SNode::Stmts(r) if r.is_empty())
                        })
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
                // The try body may lead with honesty comments (cut-boundary
                // placement) — find the first `Stmts` node.
                for n2 in tbody.iter_mut() {
                    if let SNode::Stmts(leaves) = n2
                        && let Some(b) = take_value_declare(leaves, &res_name)
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
    if let Some(ti) = splice_idx {
        // Replace the cleanup try with its body (loudly).
        let Some(SNode::Try { body: inner, .. }) = out.get(ti).cloned() else {
            unreachable!()
        };
        let mut replacement: Vec<SNode> = vec![SNode::Honest(
            "iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5)"
                .to_string(),
        )];
        replacement.extend(inner);
        out.splice(ti..ti + 1, replacement);
    }
    // No remaining uses of the loop's internal temps.
    let mut internals: Vec<String> = folded.phi_names.clone();
    internals.extend(folded.extra_internals.iter().cloned());
    if let Some(d) = &folded.done_name {
        internals.push(d.clone());
    }
    internals.retain(|n| n != &binding);
    if nodes_use_any(&out, &internals) {
        return None;
    }
    Some((binding, out))
}

// ── d-P17 (N70 residual 1): the plain-async `for await` driver ──────
//
// A plain-async function driving `for await (const x of …)` lowers to
// the corpus for-of shape PLUS the async suspend/resume machinery;
// after [`async_machine_fold`] (N70, d-P16) the loop is a working
// `while (true)` driver with plain awaits — but not the literal source
// form. The corpus matcher ([`match_for_of`]) cannot take it from
// there: the driver's shape differs on every axis:
//
// - the header carries the folded dispatch's await temp
//   (`res = next.call(it); tmp = await res; done = tmp.done`) — the
//   corpus shape reads `done` off the call result directly;
// - the header is split across several statement runs (empty runs and
//   elided guards interleaved);
// - the call goes through the phis as `next_phi.call(iter_phi)` (a
//   `this`-carrying call), not a bare `next_phi()`;
// - the loop test is the break-routed dispatch `if (done) { TAIL;
//   break } else { body; continue }` whose done arm ABSORBED the
//   post-loop tail (print + return) — the structurer placed the
//   loop's nominal continuation (the dead dispatch throw, swept by
//   [`sweep_dead_loop_exit_throws`]) after the loop instead;
// - extra loop-carried bookkeeping phis (the accumulated array, the
//   not-no-iter flag) are USED in the body — they collapse to their
//   single invariant source by substitution.
//
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

    // ── Header: phi decls, `res = next_phi.call(iter_phi)`, the
    // folded dispatch's `tmp = await res` (REQUIRED — for-await awaits
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
    if phi_names.is_empty() {
        return None;
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
            if !phi_names.contains(&callee) || !phi_names.contains(&recv) {
                return None;
            }
            (res.clone(), callee, recv)
        }
        _ => return None,
    };
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
    // The pre-loop assigns wire `next` and `it` into the call's phis.
    if !assigns
        .iter()
        .any(|(t, v)| *t == next_phi && temp_name(v) == Some(next_name.as_str()))
        || !assigns
            .iter()
            .any(|(t, v)| *t == recv_phi && temp_name(v) == Some(it_name.as_str()))
    {
        return None;
    }

    // ── The dispatch: a POSITIVE done test.
    let mut e = cond;
    let mut positive = true;
    loop {
        match e {
            Expr::Unary {
                op: UnOp::IsTrue,
                operand,
            } => e = operand,
            Expr::Unary {
                op: UnOp::IsFalse | UnOp::LogicalNot,
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

    // ── The done arm: the absorbed post-loop tail, then the exit
    // break (trailing empty runs tolerated).
    let mut tail_nodes = then.clone();
    while matches!(tail_nodes.last(), Some(SNode::Stmts(run)) if run.is_empty()) {
        tail_nodes.pop();
    }
    if !matches!(tail_nodes.pop(), Some(SNode::Break { label: None })) {
        return None;
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
        let Some(SNode::Try { body: inner, .. }) = body_nodes.get(bi).cloned() else {
            unreachable!()
        };
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

/// Substitute every reference to temp `vid` by a clone of
/// `replacement` (value positions only — binding sites are names).
pub(in crate::folds) fn subst_temp_in_expr(e: &mut Expr, vid: ValueId, replacement: &Expr) {
    if temp_value(e) == Some(vid) {
        *e = replacement.clone();
        return;
    }
    for c in expr_children_mut(e) {
        subst_temp_in_expr(c, vid, replacement);
    }
}

pub(in crate::folds) fn subst_temp_in_leaf(l: &mut Leaf, vid: ValueId, replacement: &Expr) {
    match l {
        Leaf::Raw(s) => match s {
            Stmt::Declare { value, .. }
            | Stmt::PhiAssign { value, .. }
            | Stmt::Expr(value)
            | Stmt::Throw(value) => subst_temp_in_expr(value, vid, replacement),
            Stmt::Return(Some(e)) => subst_temp_in_expr(e, vid, replacement),
            Stmt::StoreProp { object, value, .. } => {
                subst_temp_in_expr(object, vid, replacement);
                subst_temp_in_expr(value, vid, replacement);
            }
            Stmt::StoreIndex {
                object,
                index,
                value,
                ..
            } => {
                subst_temp_in_expr(object, vid, replacement);
                subst_temp_in_expr(index, vid, replacement);
                subst_temp_in_expr(value, vid, replacement);
            }
            Stmt::StoreDyn {
                object, key, value, ..
            } => {
                subst_temp_in_expr(object, vid, replacement);
                subst_temp_in_expr(key, vid, replacement);
                subst_temp_in_expr(value, vid, replacement);
            }
            Stmt::DefineMethod { object, func, .. } => {
                subst_temp_in_expr(object, vid, replacement);
                subst_temp_in_expr(func, vid, replacement);
            }
            Stmt::StorePrivate { object, value, .. } => {
                subst_temp_in_expr(object, vid, replacement);
                subst_temp_in_expr(value, vid, replacement);
            }
            Stmt::StoreSuper { key, value, .. } => {
                if let Some(k) = key {
                    subst_temp_in_expr(k, vid, replacement);
                }
                subst_temp_in_expr(value, vid, replacement);
            }
            Stmt::LexStore { value, .. }
            | Stmt::GlobalStore { value, .. }
            | Stmt::ModuleStore { value, .. } => subst_temp_in_expr(value, vid, replacement),
            Stmt::CondBranch { cond, .. } => subst_temp_in_expr(cond, vid, replacement),
            _ => {}
        },
        Leaf::Destructure { obj, .. } => subst_temp_in_expr(obj, vid, replacement),
        Leaf::Decl { value: Some(v), .. } => subst_temp_in_expr(v, vid, replacement),
        Leaf::Decl { value: None, .. } => {}
        Leaf::Assign { value, .. } => subst_temp_in_expr(value, vid, replacement),
    }
}

pub(in crate::folds) fn subst_temp_in_nodes(nodes: &mut [SNode], vid: ValueId, replacement: &Expr) {
    for n in nodes {
        match n {
            SNode::Stmts(run) => {
                for l in run {
                    subst_temp_in_leaf(l, vid, replacement);
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                subst_temp_in_expr(cond, vid, replacement);
                subst_temp_in_nodes(then, vid, replacement);
                subst_temp_in_nodes(otherwise, vid, replacement);
            }
            SNode::While { cond, body, .. } => {
                if let Some(c) = cond {
                    subst_temp_in_expr(c, vid, replacement);
                }
                subst_temp_in_nodes(body, vid, replacement);
            }
            SNode::DoWhile { body, cond, .. } => {
                subst_temp_in_nodes(body, vid, replacement);
                subst_temp_in_expr(cond, vid, replacement);
            }
            SNode::Labeled { body, .. } => subst_temp_in_nodes(body, vid, replacement),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                subst_temp_in_nodes(body, vid, replacement);
                for c in catches {
                    subst_temp_in_nodes(&mut c.body, vid, replacement);
                }
                if let Some(f) = finally {
                    subst_temp_in_nodes(f, vid, replacement);
                }
            }
            SNode::ForOf { iter, body, .. } => {
                subst_temp_in_expr(iter, vid, replacement);
                subst_temp_in_nodes(body, vid, replacement);
            }
            SNode::ForIn { obj, body, .. } => {
                subst_temp_in_expr(obj, vid, replacement);
                subst_temp_in_nodes(body, vid, replacement);
            }
            SNode::Switch { disc, cases } => {
                subst_temp_in_expr(disc, vid, replacement);
                for c in cases {
                    for t in &mut c.tests {
                        subst_temp_in_expr(t, vid, replacement);
                    }
                    subst_temp_in_nodes(&mut c.body, vid, replacement);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// Any surviving declare/phi-decl/phi-assign of `name` (binding sites
/// of a temp the fold consumed).
pub(in crate::folds) fn nodes_declare_or_assign(nodes: &[SNode], name: &str) -> bool {
    let mut found = false;
    walk_leaves(nodes, &mut |l| {
        if found {
            return;
        }
        found = match l {
            Leaf::Raw(Stmt::Declare { name: n, .. })
            | Leaf::Raw(Stmt::PhiDecl { name: n, .. })
            | Leaf::Raw(Stmt::PhiAssign { target: n, .. })
            | Leaf::Decl { name: n, .. }
            | Leaf::Assign { target: n, .. } => n == name,
            _ => false,
        };
    });
    found
}

/// Take the leading `const v = res.value` declare out of a leaf list.
pub(in crate::folds) fn take_value_declare(
    leaves: &mut Vec<Leaf>,
    res_name: &str,
) -> Option<String> {
    match leaves.first() {
        Some(Leaf::Raw(Stmt::Declare {
            name,
            value: Expr::PropName {
                object, name: prop, ..
            },
            ..
        })) if prop == "value" && temp_name(object) == Some(res_name) => {
            let name = name.clone();
            leaves.remove(0);
            Some(name)
        }
        _ => None,
    }
}

/// Drop a trailing `Stmts` node consisting only of self-copy phi
/// assigns (the back-edge plumbing), tolerating a `continue`/`break`
/// trailer after it.
pub(in crate::folds) fn drop_self_assign_tail(out: &mut Vec<SNode>) {
    let idx = match out.last() {
        Some(SNode::Continue { .. } | SNode::Break { .. }) if out.len() >= 2 => out.len() - 2,
        _ => out.len().saturating_sub(1),
    };
    if out.is_empty() {
        return;
    }
    if let Some(SNode::Stmts(tail)) = out.get(idx)
        && !tail.is_empty()
        && tail.iter().all(|l| {
            matches!(l, Leaf::Raw(Stmt::PhiAssign { target, value, .. }) if temp_name(value) == Some(target.as_str()))
        })
    {
        out.remove(idx);
    }
}

/// N74: eliminate the redundant identity copies of the for-in loop's
/// header-internal temps inside the loop body. The header internals
/// (`roots`: the iterator phi + any pass-through phis) are loop-
/// invariant by construction — the iterator is a stateful object that
/// `NextPropName` advances INTERNALLY (its register value never
/// changes), and a pass-through phi's only in-body assigns are
/// self-assigns. es2abc keeps those registers live across the loop
/// body's branch joins, and out-of-SSA recovery renders each join as a
/// merge phi (`v335 = phi(v325, v325)`) — an identity copy of a root.
///
/// A body phi whose EVERY incoming value resolves (transitively) to the
/// SAME root is such an identity copy: every use of it is substituted
/// by the root temp (sound for ANY use position), then the plumbing is
/// stripped — the copy phis' assigns/decls and the roots' (post-
/// substitution) self-assigns, which are no-ops at ANY position (a
/// branch arm's early-continue back-edge included, not just the loop
/// tail). A phi whose incoming values are anything else (a real merge)
/// keeps its uses; remaining assigns/uses of an internal likewise keep
/// the caller's `nodes_use_any` veto authoritative. Everything runs on
/// the caller's CLONE of the body, so a rejected fold leaves the tree
/// untouched.
pub(in crate::folds) fn elim_internal_copy_phis(
    out: &mut Vec<SNode>,
    roots: &BTreeMap<String, Expr>,
) {
    // Collect the body's phi decls and phi-assign sources.
    let mut decls: Vec<(String, ValueId)> = Vec::new();
    let mut sources: Vec<(String, Option<String>)> = Vec::new();
    walk_leaves(out, &mut |l| match l {
        Leaf::Raw(Stmt::PhiDecl { name, value_id }) => decls.push((name.clone(), *value_id)),
        Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => {
            sources.push((target.clone(), temp_name(value).map(str::to_string)))
        }
        _ => {}
    });
    // Fixpoint: a phi joins the copy set when it has at least one
    // assign and EVERY assign source resolves to the SAME root (a root
    // temp, or an already-classified copy of it). A non-temp source — a
    // real value — or sources resolving to different roots disqualify
    // the phi.
    let mut copy_root: BTreeMap<String, (ValueId, String)> = BTreeMap::new();
    loop {
        let mut grew = false;
        for (name, vid) in &decls {
            if roots.contains_key(name.as_str()) || copy_root.contains_key(name.as_str()) {
                continue;
            }
            let feeds: Vec<Option<&str>> = sources
                .iter()
                .filter(|(t, _)| t == name)
                .map(|(_, s)| s.as_deref())
                .collect();
            if feeds.is_empty() {
                continue;
            }
            let mut root: Option<&str> = None;
            let mut ok = true;
            for f in feeds {
                let r = match f {
                    Some(s) if roots.contains_key(s) => Some(s),
                    Some(s) => copy_root.get(s).map(|(_, r)| r.as_str()),
                    None => None,
                };
                match r {
                    Some(r) if root.is_none() || root == Some(r) => root = Some(r),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && let Some(r) = root {
                copy_root.insert(name.clone(), (*vid, r.to_string()));
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    for (vid, r) in copy_root.values() {
        subst_temp_in_nodes(out, *vid, &roots[r]);
    }
    let copy_names: BTreeSet<&str> = copy_root.keys().map(String::as_str).collect();
    let root_names: BTreeSet<&str> = roots.keys().map(String::as_str).collect();
    strip_internal_phi_plumbing(out, &root_names, &copy_names);
}

/// Strip the plumbing leaves of the eliminated internal-copy phis
/// (N74): the copy phis' own assigns and decls, plus the internal
/// temps' self-assigns (no-op back-edges at ANY body position). Nested
/// bodies are recursed into (the branch joins feeding a copy phi sit
/// inside the body's if/switch arms); statement runs left empty are
/// removed.
pub(in crate::folds) fn strip_internal_phi_plumbing(
    out: &mut Vec<SNode>,
    roots: &BTreeSet<&str>,
    copies: &BTreeSet<&str>,
) {
    out.retain_mut(|n| match n {
        SNode::Stmts(run) => {
            run.retain(|l| match l {
                Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => {
                    !(copies.contains(target.as_str())
                        || roots.contains(target.as_str())
                            && temp_name(value) == Some(target.as_str()))
                }
                Leaf::Raw(Stmt::PhiDecl { name, .. }) => !copies.contains(name.as_str()),
                _ => true,
            });
            !run.is_empty()
        }
        SNode::If {
            then, otherwise, ..
        } => {
            strip_internal_phi_plumbing(then, roots, copies);
            strip_internal_phi_plumbing(otherwise, roots, copies);
            true
        }
        SNode::While { body, .. }
        | SNode::DoWhile { body, .. }
        | SNode::Labeled { body, .. }
        | SNode::ForOf { body, .. }
        | SNode::ForIn { body, .. } => {
            strip_internal_phi_plumbing(body, roots, copies);
            true
        }
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            strip_internal_phi_plumbing(body, roots, copies);
            for c in catches {
                strip_internal_phi_plumbing(&mut c.body, roots, copies);
            }
            if let Some(f) = finally {
                strip_internal_phi_plumbing(f, roots, copies);
            }
            true
        }
        SNode::Switch { cases, .. } => {
            for c in cases {
                strip_internal_phi_plumbing(&mut c.body, roots, copies);
            }
            true
        }
        SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => true,
    });
}

/// Whether any node mentions any of the temp names.
pub(in crate::folds) fn nodes_use_any(nodes: &[SNode], names: &[String]) -> bool {
    nodes.iter().any(|n| node_uses_any(n, names))
}

pub(in crate::folds) fn node_uses_any(n: &SNode, names: &[String]) -> bool {
    match n {
        SNode::Stmts(leaves) => names.iter().any(|n| leaves_use_name(leaves, n)),
        SNode::If {
            cond,
            then,
            otherwise,
        } => {
            names.iter().any(|n| expr_uses_name(cond, n))
                || nodes_use_any(then, names)
                || nodes_use_any(otherwise, names)
        }
        SNode::While { cond, body, .. } => {
            cond.as_ref()
                .is_some_and(|c| names.iter().any(|n| expr_uses_name(c, n)))
                || nodes_use_any(body, names)
        }
        SNode::DoWhile { body, cond, .. } => {
            names.iter().any(|n| expr_uses_name(cond, n)) || nodes_use_any(body, names)
        }
        SNode::Labeled { body, .. } => nodes_use_any(body, names),
        SNode::Try { body, catches, .. } => {
            nodes_use_any(body, names) || catches.iter().any(|c| nodes_use_any(&c.body, names))
        }
        SNode::ForOf { iter, body, .. } => {
            names.iter().any(|n| expr_uses_name(iter, n)) || nodes_use_any(body, names)
        }
        SNode::ForIn { obj, body, .. } => {
            names.iter().any(|n| expr_uses_name(obj, n)) || nodes_use_any(body, names)
        }
        SNode::Switch { disc, cases } => {
            names.iter().any(|n| expr_uses_name(disc, n))
                || cases.iter().any(|c| {
                    c.tests
                        .iter()
                        .any(|t| names.iter().any(|n| expr_uses_name(t, n)))
                        || nodes_use_any(&c.body, names)
                })
        }
        SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => false,
    }
}

/// The iterator-cleanup handler check (loose, documented): every
/// handler body contains a rethrow of its catch binding AND a
/// `"return"`-keyed load, and NO side-effecting stores.
pub(in crate::folds) fn cleanup_handlers_ok(catches: &[crate::structure::CatchClause]) -> bool {
    !catches.is_empty()
        && catches.iter().all(|c| {
            let binding = c.binding.clone().unwrap_or_default();
            let mut has_rethrow = false;
            let mut has_return_load = false;
            let mut bad = false;
            walk_cleanup(
                &c.body,
                &binding,
                &mut has_rethrow,
                &mut has_return_load,
                &mut bad,
            );
            has_rethrow && has_return_load && !bad
        })
}

pub(in crate::folds) fn walk_cleanup(
    nodes: &[SNode],
    binding: &str,
    rethrow: &mut bool,
    return_load: &mut bool,
    bad: &mut bool,
) {
    // Rethrow aliases: temps assigned (phi or declare) from the
    // binding — one hop, then transitively.
    let mut aliases: Vec<String> = vec![binding.to_string()];
    let mut grew = true;
    while grew {
        grew = false;
        collect_aliases(nodes, &mut aliases, &mut grew);
    }
    for n in nodes {
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    match l {
                        Leaf::Raw(Stmt::Throw(e))
                            if temp_name(e).is_some_and(|n| aliases.iter().any(|a| a == n)) =>
                        {
                            *rethrow = true
                        }
                        Leaf::Raw(Stmt::Throw(_)) => *bad = true,
                        Leaf::Raw(Stmt::Declare { value, .. }) if expr_has_return_load(value) => {
                            *return_load = true
                        }
                        Leaf::Raw(
                            Stmt::StoreProp { .. }
                            | Stmt::StoreIndex { .. }
                            | Stmt::StoreDyn { .. }
                            | Stmt::StorePrivate { .. }
                            | Stmt::StoreSuper { .. }
                            | Stmt::LexStore { .. }
                            | Stmt::GlobalStore { .. }
                            | Stmt::ModuleStore { .. },
                        ) => *bad = true,
                        _ => {}
                    }
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                walk_cleanup(then, binding, rethrow, return_load, bad);
                walk_cleanup(otherwise, binding, rethrow, return_load, bad);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. } => walk_cleanup(body, binding, rethrow, return_load, bad),
            SNode::Try { body, .. } => walk_cleanup(body, binding, rethrow, return_load, bad),
            _ => {}
        }
    }
}

/// Grow the rethrow-alias set through phi/declare copies.
pub(in crate::folds) fn collect_aliases(
    nodes: &[SNode],
    aliases: &mut Vec<String>,
    grew: &mut bool,
) {
    for n in nodes {
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    let (target, value) = match l {
                        Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => (target, value),
                        Leaf::Raw(Stmt::Declare { name, value, .. }) => (name, value),
                        _ => continue,
                    };
                    if temp_name(value).is_some_and(|v| aliases.iter().any(|a| a == v))
                        && !aliases.iter().any(|a| a == target)
                    {
                        aliases.push(target.clone());
                        *grew = true;
                    }
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                collect_aliases(then, aliases, grew);
                collect_aliases(otherwise, aliases, grew);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::Try { body, .. } => collect_aliases(body, aliases, grew),
            _ => {}
        }
    }
}

/// Whether the expression contains a `"return"`-keyed load.
pub(in crate::folds) fn expr_has_return_load(e: &Expr) -> bool {
    match e {
        Expr::PropDyn { key, .. } | Expr::PropIndex { index: key, .. } => {
            matches!(key.as_ref(), Expr::Lit(Lit::String(s)) if s == "return")
                || expr_children(e).into_iter().any(expr_has_return_load)
        }
        Expr::PropName { name, .. } if name == "return" => true,
        _ => expr_children(e).into_iter().any(expr_has_return_load),
    }
}
