//! Generator (`function*`) state-machine driver fold.

use crate::folds::*;

// ── Generator driver fold (R4, d-P11) ──────────────────────────────
//
// VENDOR LOWERING MODEL (es2panda
// `compiler/function/generatorFunctionBuilder.cpp` +
// `functionBuilder.cpp` `SuspendResumeExecution`/`resumeGenerator`/
// `HandleCompletion`; runtime mode enum
// `ecmascript/js_generator_object.h` `GeneratorResumeMode { RETURN=0,
// THROW=1, NEXT=2 }`):
//
// - `Prepare` (function entry): `CreateGeneratorObj(callee)` → funcObj;
//   `LoadConst(undefined)`; `SuspendGenerator(funcObj)`; then the
//   completion pair `ResumeGenerator(funcObj)` → completionValue,
//   `GetResumeMode(funcObj)` → completionType, and `HandleCompletion`:
//   `if (type == RETURN) return value; if (type == THROW) throw value;`
//   otherwise `value` is the resumption value. This is the generator
//   protocol's initial suspend — invisible in JS source.
// - `Yield`: `CreateIterResultObject(value, false)`;
//   `SuspendGenerator(funcObj)`; the same completion pair +
//   `HandleCompletion`. Source form: `yield value` (the resumption
//   value is the yield expression's result).
// - `CleanUp`: a catch-all that rethrows (already dissolved by
//   [`dissolve_rethrow_trys`]).
//
// The fold eliminates the plumbing per site: the iter-result wrap
// opens up (`yield {value:v, done:false}` → `yield v`), the
// ResumeGenerator/GetResumeMode pair and the mode dispatch dissolve
// (the dispatch's default/continuation arm is the real control flow),
// the entry suspend and the CreateGenerator temp go away when every
// use was consumed, and a USED resumption value binds as
// `const t = yield v`.
//
// SOUNDNESS / HONESTY (design §8 R4 budget): the fold is per-function
// all-or-nothing gated on the ENTRY site — a generator whose entry
// dispatch does not match the vendor shape keeps ALL of its machinery
// as documented fallbacks (today's behavior). With the entry folded,
// any later non-matching site simply keeps its own fallback comments
// (loud, counted). Recompiled by es2abc, the folded body re-lowers to
// the same state machine — the dream gate is the proof.

/// Fold context for one generator function body.
pub(in crate::folds) struct GenDriverCx {
    /// The single `CreateGenerator` result value (the funcObj temp).
    pub(in crate::folds) genobj: ValueId,
    /// Pure number-constant temps (`const t = 0.0` — the optimized
    /// profile materializes the mode immediates) by value id.
    pub(in crate::folds) const_env: BTreeMap<ValueId, u64>,
    /// Const temps a successful dispatch match resolved (sweep
    /// candidates once their uses are gone).
    pub(in crate::folds) consumed_consts: BTreeSet<ValueId>,
}

/// Fold the es2abc generator state machine back into a plain
/// `function*` body. No-op for non-Generator kinds (the async family
/// is IR-gap G6 — see the module doc).
pub fn generator_machine_fold(nodes: &mut Vec<SNode>, kind: FunctionKind, stats: &mut FoldStats) {
    if kind != FunctionKind::Generator {
        return;
    }
    // The single CreateGenerator temp (es2abc emits exactly one per
    // generator function — `Prepare`). Zero: nothing to fold. More
    // than one: not the vendor shape — bail entirely.
    let mut genobjs = Vec::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::Declare {
            value: Expr::CreateGenerator { .. },
            value_id,
            ..
        }) = l
        {
            genobjs.push(*value_id);
        }
    });
    let [genobj] = genobjs[..] else {
        return;
    };
    let mut const_env = BTreeMap::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::Declare {
            value: Expr::Lit(Lit::Number(bits)),
            value_id,
            ..
        }) = l
        {
            const_env.insert(*value_id, *bits);
        }
    });
    let mut cx = GenDriverCx {
        genobj,
        const_env,
        consumed_consts: BTreeSet::new(),
    };
    // The entry gate: the site's run carries the CreateGenerator decl
    // and a bare `yield undefined` tail suspend; its resume value must
    // be dead past the dispatch (es2abc never reads it — the first
    // `next(v)` argument is dropped per spec). No entry, no fold.
    if !entry_site_matches(nodes, &mut cx) {
        return;
    }
    gen_fold_seq(nodes, &mut cx, stats);
    // Sweep the temps the fold made dead: the CreateGenerator funcObj
    // and the resolved mode-immediate consts — only when NO use
    // remains anywhere (a partially folded function keeps them, and
    // the surviving sites keep their loud fallbacks).
    let mut uses: BTreeMap<ValueId, usize> = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    let mut dead: BTreeSet<ValueId> = cx.consumed_consts.clone();
    dead.insert(cx.genobj);
    let dead: BTreeSet<ValueId> = dead
        .into_iter()
        .filter(|v| uses.get(v).copied().unwrap_or(0) == 0)
        .collect();
    if !dead.is_empty() {
        sweep_dead_decls(nodes, &dead);
    }
}

/// The entry-site validity check (immutable, iterative): find the sequence
/// where the run declaring the CreateGenerator temp sits next to its
/// dispatch, and verify the full site shape.
pub(in crate::folds) fn entry_site_matches(nodes: &[SNode], cx: &mut GenDriverCx) -> bool {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        for i in 0..slice.len().saturating_sub(1) {
            if let Some(site) = match_driver_site(slice, i, cx)
                && site.entry
                && site.genobj == cx.genobj
                && !nodes_use_temp(&site.continuation, site.resume)
            {
                return true;
            }
        }
        for n in slice.iter().rev() {
            match n {
                SNode::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::While { body, .. }
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
                    if let Some(f) = finally {
                        stack.push(f);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::Switch { cases, .. } => {
                    for c in cases.iter().rev() {
                        stack.push(&c.body);
                    }
                }
                SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
        }
    }
    false
}

/// One matched driver site (immutable match; applied separately).
pub(in crate::folds) struct DriverSite {
    /// The funcObj temp the site's pair resumes (`== cx.genobj`).
    pub(in crate::folds) genobj: ValueId,
    /// The `ResumeGenerator` temp (the completion value).
    pub(in crate::folds) resume: ValueId,
    /// The resume temp's legalized name (for the `x = yield v` bind).
    pub(in crate::folds) resume_name: String,
    /// `true` for the entry protocol suspend (bare `yield undefined`
    /// next to the CreateGenerator decl).
    pub(in crate::folds) entry: bool,
    /// The folded yield value for real yield points (the opened
    /// iter-result); `None` at the entry site.
    pub(in crate::folds) yield_value: Option<Expr>,
    /// Index of the `SuspendGenerator` (`Yield`) leaf in `run`.
    pub(in crate::folds) pre_idx: usize,
    /// Indices of `[resume_idx, mode_idx]` in `run` (ascending).
    pub(in crate::folds) pair_indices: [usize; 2],
    /// The dispatch's continuation (the real control flow).
    pub(in crate::folds) continuation: Vec<SNode>,
}

fn is_set_gen_state(l: &Leaf) -> bool {
    matches!(l, Leaf::Raw(Stmt::Elided { op, .. }) if *op == "SetGeneratorState")
}

fn is_gen_plumbing(l: &Leaf) -> bool {
    is_set_gen_state(l)
        || matches!(
            l,
            Leaf::Raw(Stmt::PhiAssign {
                exceptional: true,
                ..
            })
        )
}

/// Match `nodes[i]` (a `Stmts` run ending in
/// `[yield-stmt, decl r = ResumeGenerator(g), decl m =
/// GetResumeMode(g)]`) + `nodes[i+1]` (the mode dispatch on `m`).
pub(in crate::folds) fn match_driver_site(
    nodes: &[SNode],
    i: usize,
    cx: &mut GenDriverCx,
) -> Option<DriverSite> {
    let SNode::Stmts(run) = &nodes[i] else {
        return None;
    };
    let mut cur = run.len();
    let prev_sig = |cur: &mut usize| -> Option<usize> {
        while *cur > 0 {
            *cur -= 1;
            if !is_gen_plumbing(&run[*cur]) {
                return Some(*cur);
            }
        }
        None
    };
    let mode_idx = prev_sig(&mut cur)?;
    let resume_idx = prev_sig(&mut cur)?;
    let pre_idx = prev_sig(&mut cur)?;
    let (
        pre,
        Leaf::Raw(Stmt::Declare {
            name: resume_name,
            value:
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: rg,
                },
            value_id: resume,
            ..
        }),
        Leaf::Raw(Stmt::Declare {
            value:
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: mg,
                },
            value_id: mode,
            ..
        }),
    ) = (&run[pre_idx], &run[resume_idx], &run[mode_idx])
    else {
        return None;
    };
    let genobj = temp_value(rg)?;
    if temp_value(mg) != Some(genobj) {
        return None;
    }
    let (entry, yield_value) = match pre {
        Leaf::Raw(Stmt::Expr(Expr::Yield { value })) => match value.as_ref() {
            // A real yield point: `CreateIterResultObject(v, false)`.
            Expr::IterResultObj { value: v, done }
                if matches!(done.as_ref(), Expr::Lit(Lit::Bool(false))) =>
            {
                (false, Some((**v).clone()))
            }
            // The entry protocol suspend: bare undefined, and the run
            // declares the funcObj it suspends.
            Expr::Lit(Lit::Undefined)
                if run.iter().any(|l| {
                    matches!(
                        l,
                        Leaf::Raw(Stmt::Declare {
                            value: Expr::CreateGenerator { .. },
                            value_id,
                            ..
                        }) if *value_id == genobj
                    )
                }) =>
            {
                (true, None)
            }
            _ => return None,
        },
        _ => return None,
    };
    let continuation = match_dispatch(
        nodes.get(i + 1)?,
        *mode,
        *resume,
        &cx.const_env,
        &mut cx.consumed_consts,
    )?;
    Some(DriverSite {
        genobj,
        resume: *resume,
        resume_name: resume_name.clone(),
        entry,
        yield_value,
        pre_idx,
        pair_indices: [resume_idx, mode_idx],
        continuation,
    })
}

/// Match the resume-mode dispatch (`HandleCompletion`): a chain of
/// `mode == RETURN(0)` / `mode == THROW(1)` tests (either polarity,
/// either order, immediates inline or via pure const temps) whose case
/// arms are exactly `return <resume>` / `throw <resume>`; the
/// remaining arm after both tests is the continuation.
pub(in crate::folds) fn match_dispatch(
    n: &SNode,
    mode: ValueId,
    resume: ValueId,
    const_env: &BTreeMap<ValueId, u64>,
    consumed: &mut BTreeSet<ValueId>,
) -> Option<Vec<SNode>> {
    let mut seen_return = false;
    let mut seen_throw = false;
    let mut cur = n;
    loop {
        let SNode::If {
            cond,
            then,
            otherwise,
        } = cur
        else {
            return None;
        };
        let (bits, positive) = mode_test(cond, mode, const_env, consumed)?;
        let (case_arm, cont) = if positive {
            (then, otherwise)
        } else {
            (otherwise, then)
        };
        match f64::from_bits(bits) {
            0.0 if !seen_return => {
                check_return_arm(case_arm, resume)?;
                seen_return = true;
            }
            1.0 if !seen_throw => {
                check_throw_arm(case_arm, resume)?;
                seen_throw = true;
            }
            _ => return None,
        }
        if seen_return && seen_throw {
            return Some(cont.clone());
        }
        // Descend the chain: the continuation of a not-yet-complete
        // dispatch is exactly the next test, optionally preceded by
        // plumbing/honest runs or pure number-const decls (the optimized
        // profile materializes the second immediate there).
        let mut k = 0;
        while k < cont.len()
            && (matches!(&cont[k], SNode::Honest(_))
                || matches!(
                    &cont[k],
                    SNode::Stmts(run)
                        if run.iter().all(|l| {
                            is_gen_plumbing(l)
                                || matches!(
                                    l,
                                    Leaf::Raw(Stmt::Declare {
                                        value: Expr::Lit(Lit::Number(_)),
                                        ..
                                    })
                                )
                        })
                ))
        {
            k += 1;
        }
        cur = match &cont[k..] {
            [SNode::If { .. }] => &cont[k],
            _ => return None,
        };
    }
}

/// A dispatch test: `(isfalse|istrue)* (mode == <number>)` in either
/// operand order; returns the immediate's bits and the polarity
/// (`true` = the case body is the THEN arm).
pub(in crate::folds) fn mode_test(
    cond: &Expr,
    mode: ValueId,
    const_env: &BTreeMap<ValueId, u64>,
    consumed: &mut BTreeSet<ValueId>,
) -> Option<(u64, bool)> {
    let mut positive = true;
    let mut e = cond;
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
            } => {
                e = operand;
            }
            _ => break,
        }
    }
    let Expr::Compare {
        op: CmpOp::Eq,
        left,
        right,
    } = e
    else {
        return None;
    };
    let num = if temp_value(left) == Some(mode) {
        resolve_num(right, const_env, consumed)
    } else if temp_value(right) == Some(mode) {
        resolve_num(left, const_env, consumed)
    } else {
        None
    }?;
    Some((num, positive))
}

/// Resolve a dispatch-test immediate: an inline number literal or a
/// pure number-const temp (recorded as consumed on success).
pub(in crate::folds) fn resolve_num(
    e: &Expr,
    const_env: &BTreeMap<ValueId, u64>,
    consumed: &mut BTreeSet<ValueId>,
) -> Option<u64> {
    match e {
        Expr::Lit(Lit::Number(bits)) => Some(*bits),
        Expr::Temp { value, .. } => {
            let bits = *const_env.get(value)?;
            consumed.insert(*value);
            Some(bits)
        }
        _ => None,
    }
}

/// The RETURN arm: exactly `return <resume>;` — the structurer may
/// append loop-bookkeeping `break`s after the dominating `return`
/// (dead control points; d-P11 g04: yield inside a loop body).
pub(in crate::folds) fn check_return_arm(arm: &[SNode], resume: ValueId) -> Option<()> {
    let mut k = 0;
    while k < arm.len()
        && matches!(&arm[k], SNode::Stmts(r) if !r.is_empty() && r.iter().all(is_gen_plumbing))
    {
        k += 1;
    }
    let [SNode::Stmts(run), rest @ ..] = &arm[k..] else {
        return None;
    };
    if !rest.iter().all(|n| {
        matches!(n, SNode::Break { .. })
            || matches!(n, SNode::Stmts(r) if r.iter().all(is_gen_plumbing))
    }) {
        return None;
    }
    let sig: Vec<&Leaf> = run.iter().filter(|l| !is_gen_plumbing(l)).collect();
    let [Leaf::Raw(Stmt::Return(Some(value)))] = sig.as_slice() else {
        return None;
    };
    (temp_value(value) == Some(resume)).then_some(())
}

/// The THROW arm: exactly `throw <resume>;` (+ the dead `Unreachable`
/// and any dead loop-bookkeeping `break`s).
pub(in crate::folds) fn check_throw_arm(arm: &[SNode], resume: ValueId) -> Option<()> {
    let mut k = 0;
    while k < arm.len()
        && matches!(&arm[k], SNode::Stmts(r) if !r.is_empty() && r.iter().all(is_gen_plumbing))
    {
        k += 1;
    }
    let [SNode::Stmts(run), rest @ ..] = &arm[k..] else {
        return None;
    };
    if !rest.iter().all(|n| {
        matches!(n, SNode::Break { .. })
            || matches!(n, SNode::Stmts(r) if r.iter().all(is_gen_plumbing))
    }) {
        return None;
    }
    let sig: Vec<&Leaf> = run.iter().filter(|l| !is_gen_plumbing(l)).collect();
    match sig.as_slice() {
        [Leaf::Raw(Stmt::Throw(value))]
        | [Leaf::Raw(Stmt::Throw(value)), Leaf::Raw(Stmt::Unreachable)] => {
            (temp_value(value) == Some(resume)).then_some(())
        }
        _ => None,
    }
}

/// The rewrite pass: children first (inner sites fold before the
/// outer sites that contain them), then the sequence scan.
pub(in crate::folds) fn gen_fold_seq(
    nodes: &mut Vec<SNode>,
    cx: &mut GenDriverCx,
    stats: &mut FoldStats,
) {
    fold_snode_vecs_postorder(nodes, |seq| {
        let mut i = 0;
        while i + 1 < seq.len() {
            let site = match_driver_site(seq, i, cx);
            match site {
                Some(site) if site.genobj == cx.genobj => {
                    let SNode::Stmts(run) = &mut seq[i] else {
                        unreachable!()
                    };
                    run.remove(site.pair_indices[1]);
                    run.remove(site.pair_indices[0]);
                    if site.entry {
                        run.remove(site.pre_idx);
                        stats.gen_driver_entry += 1;
                    } else {
                        let Some(v) = site.yield_value else {
                            i += 1;
                            continue;
                        };
                        let leaf = &mut run[site.pre_idx];
                        if nodes_use_temp(&site.continuation, site.resume) {
                            *leaf = Leaf::Raw(Stmt::Declare {
                                name: site.resume_name,
                                mutable: false,
                                value: Expr::Yield { value: Box::new(v) },
                                value_id: site.resume,
                            });
                            stats.gen_driver_bound += 1;
                        } else {
                            *leaf = Leaf::Raw(Stmt::Expr(Expr::Yield { value: Box::new(v) }));
                        }
                    }
                    stats.gen_driver_sites += 1;
                    seq.splice(i + 1..i + 2, site.continuation);
                    i += 1;
                }
                _ => i += 1,
            }
        }
    });
}
