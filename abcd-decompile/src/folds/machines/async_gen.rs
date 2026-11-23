//! Async-generator (`async function*`) state-machine fold.

use crate::folds::machines::async_fn::{
    AsyncMachineCx, AsyncSite, check_async_throw_arm, match_await_site, prev_non_phi,
    sweep_async_machinery,
};
use crate::folds::machines::generator::resolve_num;
use crate::folds::*;

// ── Async-generator machine fold (d-P14, R4) ───────────────────────
//
// VENDOR LOWERING MODEL (es2panda
// `compiler/function/asyncGeneratorFunctionBuilder.cpp` `Prepare`/
// `Yield`/`DirectReturn`/`ImplicitReturn`/`ExplicitReturn`/`CleanUp` +
// `compiler/function/functionBuilder.cpp` `Await`/`AsyncYield`/
// `SuspendResumeExecution`/`resumeGenerator`/`HandleCompletion`;
// `enum class ResumeMode { RETURN=0, THROW=1, NEXT=2 }` in
// `functionBuilder.h`; runtime
// `ecmascript/interpreter/interpreter-inl.cpp`
// `ASYNCGENERATORRESOLVE_V8_V8_V8` (v0 = generator object, v1 = value,
// v2 = done flag) and `ecmascript/js_generator_object.h`
// `GeneratorResumeMode`):
//
// - `Prepare` (entry): `CreateAsyncGeneratorObj(callee)` → genObj
//   (lifted to `Op::CreateGenerator`; NOT the async
//   `AsyncFunctionEnter`) + the entry `SuspendGenerator(undefined)` +
//   the resumption pair, whose values are dead (es2abc never reads
//   them — the first `next(v)` argument is dropped per spec). No
//   dispatch on the entry mode.
// - `Yield(v)` (per source `yield v`):
//   1. `Await(v)` — `AsyncFunctionAwaitUncaught(genObj)` +
//      `SuspendGenerator` + the resumption pair + the THROW-only
//      `HandleCompletion` (27.6.3.8.5: the yielded value is awaited
//      FIRST). Identical in shape to a source-level await (d-P13's
//      site); the awaited result is the value actually yielded.
//   2. `AsyncYield` — `AsyncGeneratorResolve(genObj, awaited, false)`
//      (27.6.3.8.9; the yield point — the resolve itself suspends, no
//      `SuspendGenerator` bytecode follows) + the resumption pair.
//      The lift folds `asyncgeneratorresolve v0,v1,v2` to
//      `CreateIterResultObj { value: v0, done: v1 }` (v0.1 parity —
//      the GENERATOR object in the `value` slot, the resolved value
//      in the `done` slot; the v2 done flag is not modeled), and the
//      yield-point result is dead (the accumulator is overwritten by
//      the resumption pair), so it drops at Stage A.
//   3. The THREE-way dispatch on the resume mode:
//      - `RETURN(0)`: `AsyncFunctionAwait(resumeValue)` +
//        `SuspendResumeExecution` + a THROW-only dispatch, then
//        `AsyncGeneratorResolve(genObj, awaited, true)` + return
//        (27.6.3.8.8.b-e: `.return(v)` completes the generator with
//        `await v`). Source-invisible — dissolved with the dispatch.
//      - `THROW(1)`: `throw resumeValue` (`.throw(v)`).
//      - `NEXT(2)`: fall through; the resumption value is the yield
//        expression's result (`x = yield v`).
// - A source-level `await` inside the body: the same `Await` +
//   THROW-only `HandleCompletion` shape as d-P13 (the ASYNC_GENERATOR
//   builder kind also emits no RETURN arm there).
// - `return v` (`ExplicitReturn`): `AsyncFunctionAwait(genObj)` +
//   `SuspendResumeExecution` (NO `HandleCompletion` — a throw
//   completion propagates to the catch-all) +
//   `AsyncGeneratorResolve(genObj, resumeValue, true)` + return.
// - Falling off the end (`ImplicitReturn`): `DirectReturn(undefined)`
//   — `AsyncGeneratorResolve(genObj, undefined, true)` + return,
//   surviving in the tree as `return { value: genobj, done: undefined
//   }` (the lifted form above) and folding to `return undefined`.
// - `CleanUp` (catch-all): `AsyncGeneratorReject(genObj)` + return —
//   lifted to `Op::AsyncReject` and folded by [`async_driver_fold`]
//   (its kind gate already covers `AsyncGenerator`).
//
// SOUNDNESS / HONESTY (design §8 R4 budget, mirroring d-P11/d-P13):
// per-function all-or-nothing gated on the ENTRY protocol — exactly
// one `CreateGenerator` temp must exist, every visible use of it must
// be machinery (a `GeneratorDriver` genobj operand, an `IterResultObj`
// value slot — the lifted completion resolves, or a catch-region
// context phi assign), and the entry suspend site must match. A
// function failing the gate keeps ALL of its machinery as documented
// fallbacks; with the gate passed, a non-matching site keeps its own
// loud fallbacks (counted). In particular the pre-yield await is
// never folded to a bare `await` when the yield point behind it did
// not match (the yield-point guard) — that would silently drop the
// yield.

/// Fold the es2abc async-generator machinery back into a plain
/// `async function*` body. No-op for other kinds.
pub fn async_generator_machine_fold(
    nodes: &mut Vec<SNode>,
    kind: FunctionKind,
    stats: &mut FoldStats,
) {
    if kind != FunctionKind::AsyncGenerator {
        return;
    }
    // Exactly one `CreateGenerator` temp (es2abc emits exactly one per
    // async-generator function — `Prepare`). Zero: nothing to fold.
    // More than one: not the vendor shape — bail entirely.
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
    // Every visible use of the genObj temp must be machinery: a
    // `GeneratorDriver` genobj operand, an `IterResultObj` value slot
    // (the lifted `AsyncGeneratorResolve` completions), or a
    // catch-region context phi assign. Any other use is not the vendor
    // shape — bail, keeping everything loud.
    if !agen_uses_are_machinery(nodes, genobj) {
        return;
    }
    // The entry gate: the entry protocol suspend must sit in the
    // `CreateGenerator` decl's run (possibly behind pure const decls
    // the profile hoisted there) and elide cleanly. No entry, no fold.
    if !agen_entry_elide(nodes, genobj, stats) {
        return;
    }
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
    let mut uses = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    // N70 note: the async-GENERATOR body keeps the d-P14 singleton
    // genobj (no phi-alias closure, no break-routed dispatch) — its
    // corpus coverage is exact; extending it is future work if a
    // loop-driving async-generator body shows the same routing.
    let mut cx = AsyncMachineCx {
        genobj,
        aliases: [genobj].into_iter().collect(),
        exit_throws: BTreeSet::new(),
        const_env,
        consumed_consts: BTreeSet::new(),
        uses,
    };
    agen_fold_seq(nodes, &mut cx, stats);
    // Sweep the temps the fold made dead: resolved mode-immediate
    // consts, and the genObj temp itself once its remaining uses are
    // only dead catch-region phi assigns. A partially folded function
    // keeps the temp — and the surviving sites keep their loud
    // fallbacks.
    sweep_async_machinery(nodes, genobj, &cx.aliases, &cx.consumed_consts);
}

/// The machinery-use gate: every occurrence of the genObj temp is a
/// `GeneratorDriver` genobj operand, an `IterResultObj` value slot
/// (the lifted `AsyncGeneratorResolve` completion form), or a phi
/// assign of the temp.
pub(in crate::folds) fn agen_uses_are_machinery(nodes: &[SNode], genobj: ValueId) -> bool {
    /// `slot` marks the legal direct-operand positions (the
    /// `GeneratorDriver::genobj` operand, the `IterResultObj::value`
    /// operand).
    fn expr_ok(e: &Expr, genobj: ValueId, slot: bool) -> bool {
        if temp_value(e) == Some(genobj) {
            return slot;
        }
        match e {
            Expr::GeneratorDriver { genobj: g, .. } => expr_ok(g, genobj, true),
            Expr::IterResultObj { value, done } => {
                expr_ok(value, genobj, true) && expr_ok(done, genobj, false)
            }
            _ => expr_children(e).iter().all(|c| expr_ok(c, genobj, false)),
        }
    }
    let mut ok = true;
    walk_leaves(nodes, &mut |l| {
        if !ok {
            return;
        }
        if let Leaf::Raw(Stmt::PhiAssign { value, .. }) = l {
            ok = !expr_uses_value(value, genobj) || temp_value(value) == Some(genobj);
            return;
        }
        for e in leaf_exprs(l) {
            if !expr_ok(e, genobj, false) {
                ok = false;
                return;
            }
        }
    });
    ok
}

/// The entry-site elision (the entry gate): find the run declaring the
/// `CreateGenerator` temp; behind any pure const decls the profile
/// hoisted there, the entry protocol suspend (`yield undefined` — the
// entry `SuspendGenerator`, recovered as a `Yield` expression) plus
/// the optional dead entry resume/mode expression statements must
/// follow. Elide them. Returns false (no fold at all) when the site
/// does not match.
pub(in crate::folds) fn agen_entry_elide(
    nodes: &mut [SNode],
    genobj: ValueId,
    stats: &mut FoldStats,
) -> bool {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => {
                let decl_at = run.iter().position(|l| {
                    matches!(
                        l,
                        Leaf::Raw(Stmt::Declare {
                            value: Expr::CreateGenerator { .. },
                            value_id,
                            ..
                        }) if *value_id == genobj
                    )
                });
                if let Some(j) = decl_at {
                    // Skip pure const decls (the optimized profile
                    // materializes the mode immediates early).
                    let mut k = j + 1;
                    while k < run.len()
                        && matches!(
                            run[k],
                            Leaf::Raw(Stmt::Declare {
                                value: Expr::Lit(_),
                                ..
                            })
                        )
                    {
                        k += 1;
                    }
                    // The entry protocol suspend: bare `yield
                    // undefined`.
                    if !matches!(
                        run.get(k),
                        Some(Leaf::Raw(Stmt::Expr(Expr::Yield { value })))
                            if matches!(value.as_ref(), Expr::Lit(Lit::Undefined))
                    ) {
                        return false;
                    }
                    let mut elide = vec![k];
                    k += 1;
                    // The dead entry resume/mode results, when they
                    // survived as expression statements (impure ops
                    // with dead results; at most one each).
                    let mut seen_resume = false;
                    let mut seen_mode = false;
                    loop {
                        match run.get(k) {
                            Some(Leaf::Raw(Stmt::Expr(Expr::GeneratorDriver {
                                resume: true,
                                genobj: g,
                            }))) if temp_value(g) == Some(genobj) && !seen_resume => {
                                seen_resume = true;
                                elide.push(k);
                                k += 1;
                            }
                            Some(Leaf::Raw(Stmt::Expr(Expr::GeneratorDriver {
                                resume: false,
                                genobj: g,
                            }))) if temp_value(g) == Some(genobj) && !seen_mode => {
                                seen_mode = true;
                                elide.push(k);
                                k += 1;
                            }
                            _ => break,
                        }
                    }
                    for &idx in elide.iter().rev() {
                        run.remove(idx);
                    }
                    stats.agen_entry += 1;
                    return true;
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                if agen_entry_elide(then, genobj, stats)
                    || agen_entry_elide(otherwise, genobj, stats)
                {
                    return true;
                }
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // async_generator_machine_fold (emit.rs:524 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => {
                if agen_entry_elide(body, genobj, stats) {
                    return true;
                }
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                // unreachable (finally conjunct): Try.finally is Some only
                // after fold_finally (folds.rs:4143/4154) inside fold(),
                // which runs after async_generator_machine_fold — c-COV diagnosis
                if agen_entry_elide(body, genobj, stats)
                    || catches
                        .iter_mut()
                        .any(|c| agen_entry_elide(&mut c.body, genobj, stats))
                    || finally
                        .as_mut()
                        .is_some_and(|f| agen_entry_elide(f, genobj, stats))
                {
                    return true;
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_generator_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    if agen_entry_elide(&mut c.body, genobj, stats) {
                        return true;
                    }
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    false
}

/// One matched yield site (immutable match; applied separately).
pub(in crate::folds) struct AGYieldSite {
    /// The matched pre-yield await site (machinery leaf indices,
    /// dispatch offset, awaited operand).
    pub(in crate::folds) await_site: AsyncSite,
    /// The yield-point resumption value temp and its legalized name
    /// (for the `x = yield v` bind).
    pub(in crate::folds) ry: ValueId,
    /// `ry`'s declared name.
    pub(in crate::folds) ry_name: String,
    /// The NEXT arm (the real control flow).
    pub(in crate::folds) continuation: Vec<SNode>,
}

/// The rewrite pass: children first (inner sites fold before the
/// outer sites whose continuations contain them), then per-run
/// completion folds, then the sequence scan (yield site →
/// explicit-return site → plain await site).
pub(in crate::folds) fn agen_fold_seq(
    nodes: &mut Vec<SNode>,
    cx: &mut AsyncMachineCx,
    stats: &mut FoldStats,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                agen_fold_seq(then, cx, stats);
                agen_fold_seq(otherwise, cx, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // async_generator_machine_fold (emit.rs:524 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => agen_fold_seq(body, cx, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                agen_fold_seq(body, cx, stats);
                for c in catches {
                    agen_fold_seq(&mut c.body, cx, stats);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // async_generator_machine_fold — c-COV diagnosis
                if let Some(f) = finally {
                    agen_fold_seq(f, cx, stats);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_generator_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    agen_fold_seq(&mut c.body, cx, stats);
                }
            }
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    // Per-run rewrites: the completion resolves
    // (`return { value: genobj, done: X }` — the lifted
    // `AsyncGeneratorResolve(gen, X, true)` + return) fold to
    // `return X`, and the explicit-return await sites fold with them.
    for n in nodes.iter_mut() {
        if let SNode::Stmts(run) = n {
            agen_fold_run(run, cx.genobj, stats);
        }
    }
    let mut i = 0;
    while i + 1 < nodes.len() {
        // The yield site first: the pre-yield await must fold with its
        // yield machinery, never as a bare `await`.
        if let Some(site) = match_ag_yield(nodes, i, cx) {
            let SNode::Stmts(run) = &mut nodes[i] else {
                unreachable!()
            };
            let insert_at = *site
                .await_site
                .remove
                .iter()
                .min()
                .expect("the suspend leaf");
            for &j in &site.await_site.remove {
                run.remove(j);
            }
            let insert_at = insert_at.min(run.len());
            let y = Expr::Yield {
                value: Box::new(site.await_site.awaited),
            };
            if nodes_use_temp(&site.continuation, site.ry) {
                // `x = yield v` — the resumption value has real uses
                // in the NEXT continuation; bind the temp.
                run.insert(
                    insert_at,
                    Leaf::Raw(Stmt::Declare {
                        name: site.ry_name,
                        mutable: false,
                        value: y,
                        value_id: site.ry,
                    }),
                );
                stats.agen_bound += 1;
            } else {
                run.insert(insert_at, Leaf::Raw(Stmt::Expr(y)));
            }
            stats.agen_yields += 1;
            nodes.splice(
                i + site.await_site.dispatch_off..i + site.await_site.dispatch_off + 1,
                site.continuation,
            );
            i += 1;
            continue;
        }
        // A source-level await (d-P13's site shape) — guarded: a
        // continuation opening with the resumption pair on the same
        // genObj is yield machinery, not a source await's
        // continuation. If the yield match refused it, the whole site
        // stays loud.
        if let Some(site) = match_ag_await(nodes, i, cx) {
            let SNode::Stmts(run) = &mut nodes[i] else {
                unreachable!()
            };
            let insert_at = *site.remove.iter().min().expect("the suspend leaf");
            for &j in &site.remove {
                run.remove(j);
            }
            let insert_at = insert_at.min(run.len());
            let aw = Expr::Await {
                value: Box::new(site.awaited),
                uncaught: true,
            };
            match site.resume {
                Some((r, name)) if cx.uses.get(&r).copied().unwrap_or(0) > 1 => {
                    run.insert(
                        insert_at,
                        Leaf::Raw(Stmt::Declare {
                            name,
                            mutable: false,
                            value: aw,
                            value_id: r,
                        }),
                    );
                    stats.agen_await_bound += 1;
                }
                _ => run.insert(insert_at, Leaf::Raw(Stmt::Expr(aw))),
            }
            stats.agen_awaits += 1;
            nodes.splice(
                i + site.dispatch_off..i + site.dispatch_off + 1,
                site.continuation,
            );
            i += 1;
            continue;
        }
        i += 1;
    }
}

/// Per-run completion folds: `return { value: genobj, done: X }` (the
/// lifted `AsyncGeneratorResolve(gen, X, true)` + return of
/// `DirectReturn`) → `return X`; and the explicit-return await site
/// (`ExplicitReturn`: `AsyncFunctionAwait(v)` + `SuspendGenerator` +
/// the resumption pair — NO `HandleCompletion` — then the `done=true`
/// resolve + return) → `return v`.
pub(in crate::folds) fn agen_fold_run(run: &mut Vec<Leaf>, genobj: ValueId, stats: &mut FoldStats) {
    // The completion resolve fold.
    for l in run.iter_mut() {
        if let Leaf::Raw(Stmt::Return(Some(Expr::IterResultObj { value, done }))) = l
            && temp_value(value) == Some(genobj)
        {
            let x = (**done).clone();
            *l = Leaf::Raw(Stmt::Return(Some(x)));
            stats.agen_returns += 1;
        }
    }
    // The explicit-return await site (run-local, phi assigns skipped):
    // `[decl a = await v, suspend-stmt(a), decl r = ResumeGenerator(g),
    //   return r]` → `return v`.
    let Some(ret_at) = run.iter().position(|l| {
        matches!(
            l,
            Leaf::Raw(Stmt::Return(Some(e))) if matches!(e, Expr::Temp { .. })
        )
    }) else {
        return;
    };
    let mut cur = ret_at;
    // The resume decl.
    let Some(j) = prev_non_phi(run, &mut cur) else {
        return;
    };
    let Leaf::Raw(Stmt::Declare {
        value: Expr::GeneratorDriver {
            resume: true,
            genobj: g,
        },
        value_id: rv,
        ..
    }) = &run[j]
    else {
        return;
    };
    if temp_value(g) != Some(genobj) {
        return;
    }
    let Leaf::Raw(Stmt::Return(Some(Expr::Temp { value: rt, .. }))) = &run[ret_at] else {
        unreachable!()
    };
    if rt != rv {
        return;
    }
    // The suspend stmt + the await decl.
    let Some(j2) = prev_non_phi(run, &mut cur) else {
        return;
    };
    let Leaf::Raw(Stmt::Expr(Expr::Yield { value })) = &run[j2] else {
        return;
    };
    let Expr::Temp { value: at, .. } = value.as_ref() else {
        return;
    };
    let at = *at;
    let Some(j3) = prev_non_phi(run, &mut cur) else {
        return;
    };
    let Leaf::Raw(Stmt::Declare {
        value: Expr::Await {
            value: x,
            uncaught: true,
        },
        value_id,
        ..
    }) = &run[j3]
    else {
        return;
    };
    if value_id != &at {
        return;
    }
    let awaited = (**x).clone();
    // All four machinery leaves fold to the plain return.
    run.remove(ret_at);
    run.remove(j);
    run.remove(j2);
    run.remove(j3);
    run.insert(j3, Leaf::Raw(Stmt::Return(Some(awaited))));
    stats.agen_returns += 1;
}

/// Match a full yield site at `nodes[i]`: the pre-yield await
/// machinery + its THROW-only dispatch (d-P13's await-site shape),
/// whose continuation opens with the yield-point resumption pair and
/// the THREE-way resume-mode dispatch.
pub(in crate::folds) fn match_ag_yield(
    nodes: &[SNode],
    i: usize,
    cx: &mut AsyncMachineCx,
) -> Option<AGYieldSite> {
    let site = match_await_site(nodes, i, cx)?;
    // The pre-yield resume value: when declared, its only use may be
    // the (removed) throw arm — the yielded value is the await's
    // awaited operand, and an escaped resume is not the vendor shape.
    if let Some((r, _)) = &site.resume
        && cx.uses.get(r).copied().unwrap_or(0) != 1
    {
        return None;
    }
    // The continuation: leading phi-partition runs, the resumption
    // pair decl run, more phi runs, then the three-way dispatch.
    let cont = &site.continuation;
    let mut at = 0;
    while at < cont.len() && phi_only_run(&cont[at]) {
        at += 1;
    }
    let SNode::Stmts(decl_run) = cont.get(at)? else {
        return None;
    };
    let mut sig = decl_run
        .iter()
        .filter(|l| !matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })));
    // The yield-point resume decl (required).
    let (ry, ry_name) = match sig.next() {
        Some(Leaf::Raw(Stmt::Declare {
            name,
            value:
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: rg,
                },
            value_id,
            ..
        })) if temp_value(rg) == Some(cx.genobj) => (*value_id, name.clone()),
        _ => return None,
    };
    // The yield-point mode decl (optional — it may be inlined into
    // the dispatch tests).
    let mut my = None;
    let mut rest = sig.clone();
    if let Some(Leaf::Raw(Stmt::Declare {
        value: Expr::GeneratorDriver {
            resume: false,
            genobj: mg,
        },
        value_id,
        ..
    })) = rest.next()
        && temp_value(mg) == Some(cx.genobj)
    {
        my = Some(*value_id);
        sig.next();
    }
    if sig.next().is_some() {
        return None;
    }
    at += 1;
    while at < cont.len() && phi_only_run(&cont[at]) {
        at += 1;
    }
    let dispatch = cont.get(at)?;
    if at + 1 != cont.len() {
        return None;
    }
    let continuation = match_ag_three_way(dispatch, my, ry, cx)?;
    Some(AGYieldSite {
        await_site: site,
        ry,
        ry_name,
        continuation,
    })
}

/// A `Stmts` run carrying only phi assigns (block-end bookkeeping).
pub(in crate::folds) fn phi_only_run(n: &SNode) -> bool {
    matches!(
        n,
        SNode::Stmts(run)
            if !run.is_empty()
                && run
                    .iter()
                    .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
    )
}

/// Match the yield-point three-way dispatch (27.6.3.8.8): a chain of
/// `mode == RETURN(0)` / `mode == THROW(1)` tests (either polarity,
/// either order, immediates inline or via pure const temps, the mode
/// operand a `Temp` of the matched mode decl or an inlined
/// `GetResumeMode`) whose RETURN arm awaits the resumption value and
/// completes (already folded to `const a = await ry; return a;` by the
/// child passes) and whose THROW arm is exactly `throw ry`; the
/// remaining arm after both tests is the NEXT continuation.
pub(in crate::folds) fn match_ag_three_way(
    n: &SNode,
    my: Option<ValueId>,
    ry: ValueId,
    cx: &mut AsyncMachineCx,
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
        let (bits, positive) = ag_mode_test(cond, my, cx)?;
        let (case_arm, cont) = if positive {
            (then, otherwise)
        } else {
            (otherwise, then)
        };
        match f64::from_bits(bits) {
            0.0 if !seen_return => {
                check_ag_return_arm(case_arm, ry)?;
                seen_return = true;
            }
            1.0 if !seen_throw => {
                check_async_throw_arm(case_arm, Some(ry), &[cx.genobj].into_iter().collect())?;
                seen_throw = true;
            }
            _ => return None,
        }
        if seen_return && seen_throw {
            return Some(cont.clone());
        }
        // Descend the chain: the continuation of a not-yet-complete
        // dispatch is exactly the next test, optionally preceded by
        // phi-partition runs or pure number-const decls.
        let mut k = 0;
        while k < cont.len()
            && (phi_only_run(&cont[k])
                || matches!(
                    &cont[k],
                    SNode::Stmts(run)
                        if run.iter().all(|l| matches!(
                            l,
                            Leaf::Raw(Stmt::Declare {
                                value: Expr::Lit(Lit::Number(_)),
                                ..
                            })
                        ))
                ))
        {
            k += 1;
        }
        cur = match cont[k..] {
            [SNode::If { .. }] => &cont[k],
            _ => return None,
        };
    }
}

/// A three-way dispatch test: `(isfalse|istrue)* (mode == <number>)`
/// in either operand order, where `mode` is the matched mode temp or
/// an inlined `GetResumeMode` on the genObj; returns the immediate's
/// bits and the polarity (`true` = the case body is the THEN arm).
pub(in crate::folds) fn ag_mode_test(
    cond: &Expr,
    my: Option<ValueId>,
    cx: &mut AsyncMachineCx,
) -> Option<(u64, bool)> {
    let mut positive = true;
    let mut e = cond;
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
    let genobj = cx.genobj;
    let is_mode = |e: &Expr| match my {
        Some(md) => temp_value(e) == Some(md),
        None => matches!(
            e,
            Expr::GeneratorDriver {
                resume: false,
                genobj: mg,
            } if temp_value(mg) == Some(genobj)
        ),
    };
    let bits = if is_mode(left) {
        resolve_num(right, &cx.const_env, &mut cx.consumed_consts)
    } else if is_mode(right) {
        resolve_num(left, &cx.const_env, &mut cx.consumed_consts)
    } else {
        None
    }?;
    Some((bits, positive))
}

/// The RETURN arm (already child-folded): exactly `const a = await
/// ry; return a;` (+ phi-partition runs and dead loop-bookkeeping
/// breaks).
pub(in crate::folds) fn check_ag_return_arm(arm: &[SNode], ry: ValueId) -> Option<()> {
    let mut awaited = None;
    let mut returned = false;
    for n in arm {
        match n {
            SNode::Stmts(_) if phi_only_run(n) => {}
            SNode::Stmts(run) => {
                let significant: Vec<&Leaf> = run
                    .iter()
                    .filter(|l| !matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
                    .collect();
                match (awaited, returned, significant.as_slice()) {
                    (
                        None,
                        false,
                        [
                            Leaf::Raw(Stmt::Declare {
                                value:
                                    Expr::Await {
                                        value,
                                        uncaught: true,
                                    },
                                value_id,
                                ..
                            }),
                        ],
                    ) if temp_value(value) == Some(ry) => {
                        awaited = Some(*value_id);
                    }
                    (Some(a), false, [Leaf::Raw(Stmt::Return(Some(e)))])
                        if temp_value(e) == Some(a) =>
                    {
                        returned = true;
                    }
                    _ => return None,
                }
            }
            SNode::Break { .. } => {}
            _ => return None,
        }
    }
    returned.then_some(())
}

/// Match a source-level await site (d-P13's shape) — refusing the
/// pre-yield await of an unmatched yield point (the yield-point
/// guard): a continuation opening with the resumption pair on the
/// same genObj is yield machinery, and folding the await there would
/// orphan the yield.
pub(in crate::folds) fn match_ag_await(
    nodes: &[SNode],
    i: usize,
    cx: &mut AsyncMachineCx,
) -> Option<AsyncSite> {
    let site = match_await_site(nodes, i, cx)?;
    let mut at = 0;
    while at < site.continuation.len() && phi_only_run(&site.continuation[at]) {
        at += 1;
    }
    if let Some(SNode::Stmts(run)) = site.continuation.get(at) {
        let first = run
            .iter()
            .find(|l| !matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })));
        if let Some(Leaf::Raw(Stmt::Declare {
            value:
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: g,
                },
            ..
        })) = first
            && temp_value(g) == Some(cx.genobj)
        {
            return None;
        }
    }
    Some(site)
}
