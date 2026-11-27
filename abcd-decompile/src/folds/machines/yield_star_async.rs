//! Async `yield*` driver tail & yield-delegation protocol matching (`d-P15`).

use super::yield_star::*;
use crate::expr::{Expr, Lit};
use crate::folds::temp_value;
use crate::recover::Stmt;
use crate::structure::{Leaf, SNode};
use abcd_ir::id::ValueId;
use abcd_ir::op::{CmpOp, UnOp};
use std::collections::BTreeMap;

/// The async driver tail: the call + Await(inner) + pass-through
/// AsyncGeneratorYield machinery, the done test, and the IN-LOOP
/// completion dispatch (the async YieldStar's `iteratorComplete` is
/// inlined in the loop body).
#[allow(
    clippy::too_many_arguments,
    reason = "async yield-star tail matcher binds distinct SSA phis and names"
)]
pub(in crate::folds) fn ys_match_loop_tail_async(
    sig: &[&SNode],
    phis: &BTreeMap<String, ValueId>,
    rt: ValueId,
    it: ValueId,
    exit_decl: ValueId,
    flag_id: ValueId,
    exit_phi: (ValueId, String),
    rt_name: String,
    rv_name: String,
    it_name: String,
    flag_name: String,
) -> Option<YsLoop> {
    let precall = *sig.get(2)?;
    let pre_phis = ys_phi_decls(precall)?;
    let exit_id = pre_phis.get(&exit_phi.1).copied()?;
    let exit_phi = (exit_id, exit_phi.1);
    let SNode::Stmts(prun) = precall else {
        return None;
    };
    let tail: Vec<&Leaf> = prun[pre_phis.len()..]
        .iter()
        .filter(|l| !ys_skip_plumbing_leaf(l))
        .collect();

    // Pre-call + done-test extraction supports both:
    // 1. Unfolded pre-call await (`[_, _, precall, await_if]` where `g` was a loop phi);
    // 2. Folded pre-call await (`[_, _, precall, done_run, done_if]` or
    //    `[_, _, precall_with_done, done_if]` when `async_generator_machine_fold`
    //    already folded `const resume1 = await res`).
    let (rv, rv_name, resume1, done, done_if, pre_g): (
        ValueId,
        String,
        ValueId,
        ValueId,
        &SNode,
        Option<(ValueId, String)>,
    ) = match tail.as_slice() {
        [
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
        ] => {
            let [_, _, _, await_if] = sig else {
                ys_trace("a-tail:skeleton");
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
            let (g_id, g_name) = ys_temp_pair(genobj)?;
            let SNode::If {
                cond,
                then,
                otherwise,
            } = await_if
            else {
                return None;
            };
            let Some(cont_arm) =
                ys_async_throw_dispatch_arms(cond, then, otherwise, g_id, *resume1)
            else {
                ys_trace("a-tail:throw-dispatch");
                return None;
            };
            let csig = ys_sig(cont_arm);
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
                    l if ys_skip_plumbing_leaf(l) => {}
                    Leaf::Raw(Stmt::Declare {
                        value, value_id, ..
                    }) if ys_prop(value, "done") == Some(*resume1) => {
                        done = Some(*value_id);
                    }
                    _ => return None,
                }
            }
            let done = done?;
            (rv, rv_name, *resume1, done, *done_if, Some((g_id, g_name)))
        }
        [
            Leaf::Raw(Stmt::Declare {
                value: Expr::Call {
                    callee, this, args, ..
                },
                value_id: res,
                ..
            }),
            Leaf::Raw(Stmt::Declare {
                value: Expr::Await { value: aw_val, .. },
                value_id: resume1,
                ..
            }),
            rest_tail @ ..,
        ] => {
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
            let rv = *arg;
            if !phis.values().any(|v| *v == rv) || temp_value(aw_val) != Some(*res) {
                return None;
            }
            let rv_name = phis
                .iter()
                .find(|(_, v)| **v == rv)
                .map(|(n, _)| n.clone())
                .unwrap_or(rv_name);
            let (done_leaves, done_if): (Vec<&Leaf>, &SNode) = match sig {
                [_, _, _, SNode::Stmts(drun), done_if @ SNode::If { .. }]
                    if rest_tail.is_empty() =>
                {
                    (drun.iter().collect(), *done_if)
                }
                [_, _, _, done_if @ SNode::If { .. }] if !rest_tail.is_empty() => {
                    (rest_tail.to_vec(), *done_if)
                }
                _ => return None,
            };
            let mut done = None;
            for l in done_leaves {
                match l {
                    Leaf::Raw(Stmt::Elided { op, .. }) if *op == "ThrowIfNotObject" => {}
                    l if ys_skip_plumbing_leaf(l) => {}
                    Leaf::Raw(Stmt::Declare {
                        value, value_id, ..
                    }) if ys_prop(value, "done") == Some(*resume1) => {
                        done = Some(*value_id);
                    }
                    _ => return None,
                }
            }
            let done = done?;
            (rv, rv_name, *resume1, done, done_if, None)
        }
        _ => {
            ys_trace("a-tail:precall-shape");
            return None;
        }
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
    let bind_idx = nrun.iter().position(|l| !ys_skip_plumbing_leaf(l))?;
    let Some((bind_name, bind_id, bind_val)) = ys_declare_of(&nrun[bind_idx]) else {
        ys_trace("a-tail:bind");
        return None;
    };
    if ys_prop(bind_val, "value") != Some(resume1) {
        return None;
    }
    let mut continuation: Vec<SNode> = Vec::new();
    if bind_idx + 1 < nrun.len() {
        continuation.push(SNode::Stmts(nrun[bind_idx + 1..].to_vec()));
    }
    continuation.extend(nrest.iter().map(|n| (*n).clone()));
    // Return completion: `v = resume1.value; return v` (+ plumbing).
    let rsig = ys_sig(retarm);
    let Some(SNode::Stmts(rrun)) = rsig.first() else {
        return None;
    };
    let rrun_sig: Vec<&Leaf> = rrun.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
    let [
        Leaf::Raw(Stmt::Declare {
            value: rv_val,
            value_id: rvid,
            ..
        }),
        Leaf::Raw(Stmt::Return(Some(ret_e))),
        tail @ ..,
    ] = rrun_sig.as_slice()
    else {
        return None;
    };
    if ys_prop(rv_val, "value") != Some(resume1)
        || temp_value(ret_e) != Some(*rvid)
        || !tail
            .iter()
            .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
    {
        return None;
    }

    // ── not-done arm: value/await/AsyncGeneratorYield + resumption ──
    let next_sig = ys_sig(next_arm);
    let (g_id, g_name) = match pre_g {
        Some(pair) => pair,
        None => {
            let SNode::Stmts(head) = *next_sig.first()? else {
                return None;
            };
            let head_sig: Vec<&Leaf> = head.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
            let [
                _,
                _,
                _,
                Leaf::Raw(Stmt::Declare {
                    value:
                        Expr::GeneratorDriver {
                            resume: true,
                            genobj,
                        },
                    ..
                }),
            ] = head_sig.as_slice()
            else {
                return None;
            };
            ys_temp_pair(genobj)?
        }
    };
    if ys_match_async_yield_with_false(
        &next_sig,
        g_id,
        resume1,
        rt,
        rv,
        &rt_name,
        &rv_name,
        &[exit_decl, flag_id],
    )
    .is_none()
    {
        ys_trace("a-tail:async-yield");
        return None;
    }

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
        bind: Some((bind_name.to_string(), bind_id)),
        continuation,
        in_loop_exit: true,
    })
}

/// Polarity-aware async THROW-only dispatch on an inline `GetResumeMode(g)`:
/// returns the continuation arm slice when the THROW(1) arm matches
/// `[throw resume; unreachable; break?]`.
pub(in crate::folds) fn ys_async_throw_dispatch_arms<'a>(
    cond: &Expr,
    then: &'a [SNode],
    otherwise: &'a [SNode],
    g: ValueId,
    resume: ValueId,
) -> Option<&'a [SNode]> {
    let (cmp_expr, throw_first) = match cond {
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
        op: CmpOp::Eq,
        left,
        right,
    } = cmp_expr
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
    let (throw_arm, cont_arm) = if throw_first {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    let osig = ys_sig(throw_arm);
    let trun = match osig.as_slice() {
        [SNode::Stmts(trun)] | [SNode::Stmts(trun), SNode::Break { .. }] => trun,
        _ => return None,
    };
    let tsig: Vec<&Leaf> = trun.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
    let [Leaf::Raw(Stmt::Throw(e)), Leaf::Raw(Stmt::Unreachable)] = tsig.as_slice() else {
        return None;
    };
    (temp_value(e) == Some(resume)).then_some(cont_arm)
}

#[cfg(test)]
pub(in crate::folds) fn ys_async_throw_dispatch(
    cond: &Expr,
    otherwise: &[SNode],
    g: ValueId,
    resume: ValueId,
) -> Option<()> {
    ys_async_throw_dispatch_arms(cond, &[], otherwise, g, resume).map(|_| ())
}

/// The async not-done arm (AsyncGeneratorYield + the resumption
/// re-entry): `value = inner.value; av = await value; yield av;
/// res2 = ResumeGenerator(g)`; THROW-dispatch; then the three-way
/// resumption re-entry (NEXT: loop back with the mode/value; RETURN:
/// await the resume value, then re-enter with RETURN; the await's own
/// THROW re-enters with THROW).
#[allow(
    clippy::too_many_arguments,
    reason = "async yield matcher threads SSA ids, loop-back names, and known false-literal temps"
)]
pub(in crate::folds) fn ys_match_async_yield_with_false(
    arm: &[&SNode],
    g: ValueId,
    resume1: ValueId,
    rt: ValueId,
    rv: ValueId,
    rt_name: &str,
    rv_name: &str,
    extra_false: &[ValueId],
) -> Option<()> {
    let [SNode::Stmts(head), mode_if] = arm else {
        ys_trace("ay:skeleton");
        return None;
    };
    // head: [value = resume1.value, av = await value (uncaught),
    //        yield av, res2 = ResumeGenerator(g)]
    let head_sig: Vec<&Leaf> = head.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
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
    ] = head_sig.as_slice()
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
    let Some(cont_arm) = ys_async_throw_dispatch_arms(cond, then, otherwise, g, *res2) else {
        ys_trace("ay:throw-dispatch");
        return None;
    };
    // The resumption re-entry: [r3 = ResumeGenerator(g), m3 =
    // GetResumeMode(g)]; `if (m3 != RETURN) loop-back`; the RETURN
    // await; `if (m4 == THROW) loop-back(THROW)`; the final
    // loop-back with mode RETURN.
    let rsig = ys_sig(cont_arm);
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
    let mut pair_leaves: Vec<&Leaf> = pair.iter().filter(|l| !ys_skip_plumbing_leaf(l)).collect();
    let mut false_id = None;
    if let Some(Leaf::Raw(Stmt::Declare {
        value: Expr::Lit(Lit::Bool(false)),
        value_id,
        ..
    })) = pair_leaves.first().copied()
    {
        false_id = Some(*value_id);
        pair_leaves.remove(0);
    }
    let is_ag_resolve = |e: &Expr| {
        matches!(
            e,
            Expr::AsyncGeneratorResolve {
                genobj: ag_g,
                value: ag_v,
                done: ag_d,
            } if temp_value(ag_g) == Some(g)
                && temp_value(ag_v) == Some(*res2)
                && (matches!(ag_d.as_ref(), Expr::Lit(Lit::Bool(false)))
                    || false_id.is_some_and(|fid| temp_value(ag_d) == Some(fid))
                    || extra_false.iter().any(|&fid| temp_value(ag_d) == Some(fid)))
        )
    };
    if let Some(Leaf::Raw(Stmt::Expr(e))) = pair_leaves.first().copied()
        && (is_ag_resolve(e) || matches!(e, Expr::Yield { value } if is_ag_resolve(value)))
    {
        pair_leaves.remove(0);
    } else if let [
        Leaf::Raw(Stmt::Declare {
            value: ag_e,
            value_id: agr,
            ..
        }),
        Leaf::Raw(Stmt::Expr(Expr::Yield { value: yv })),
        ..,
    ] = pair_leaves.as_slice()
        && is_ag_resolve(ag_e)
        && temp_value(yv) == Some(*agr)
    {
        pair_leaves.drain(0..2);
    }
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
    ] = pair_leaves.as_slice()
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
    let await_sig: Vec<&Leaf> = await_run
        .iter()
        .filter(|l| !ys_skip_plumbing_leaf(l))
        .collect();
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
    ] = await_sig.as_slice()
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
