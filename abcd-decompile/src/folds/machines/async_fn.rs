//! Plain `async` completion driver and suspend/resume state-machine folds.

use crate::folds::machines::generator::resolve_num;
use crate::folds::*;

// ── Fold 7: async driver completion (N68/G6, R4) ─────────────────────

/// Fold the es2abc async-completion pair back to source-level control
/// flow: an `AsyncResolve(v)` whose result is immediately returned is
/// the async function's completion — `return v`; an `AsyncReject(v)`
/// whose result is immediately returned is the catch-all rejection
/// wrapper — `throw v`. Runs only inside async kinds (the
/// `AsyncResolve`/`AsyncReject` ops are async-completion semantics; the
/// kind gate keeps a hypothetical stray op in a non-async body LOUD
/// rather than folded).
///
/// Two shapes are matched (both adjacency-strict, the es2abc shape —
/// `asyncfunctionresolve v` + `return` are consecutive bytecodes):
///
/// - temp form: `const t = asyncDriver(v); return t;` with `t` used
///   exactly once in the whole tree;
/// - inlined form: `return asyncDriver(v);` directly.
///
/// Everything else (a dead result, a multi-use result, a non-adjacent
/// use) keeps the documented hard-fallback node. Runs BEFORE
/// [`fold`]'s `dissolve_rethrow_trys`, so the folded catch-all
/// (`catch (e) { throw e; }`) dissolves as the semantic no-op it is.
pub fn async_driver_fold(nodes: &mut [SNode], kind: FunctionKind, stats: &mut FoldStats) {
    if !matches!(
        kind,
        FunctionKind::Async | FunctionKind::AsyncArrow | FunctionKind::AsyncGenerator
    ) {
        return;
    }
    // Whole-tree use counts, computed once up front: the fold moves the
    // AsyncDriver's value expression from the declare into the
    // return/throw, which preserves every OTHER temp's reference count,
    // so the counts stay valid across the mutations.
    let mut uses = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    // N70: whole-tree Declare counts per temp. The structurer's
    // finally-style try fragmentation DUPLICATES the catch-all handler
    // body (the copies share SSA value ids), so a folded temp's use
    // count is N copies × 1 use, not 1 — the temp-form fold pairs each
    // declare with its adjacent return when uses == declares (each
    // copy is self-contained).
    let mut decls: BTreeMap<ValueId, usize> = BTreeMap::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::Declare { value_id, .. }) = l {
            *decls.entry(*value_id).or_insert(0) += 1;
        }
    });
    async_fold_seq(nodes, &uses, &decls, stats);
}

pub(in crate::folds) fn async_fold_seq(
    nodes: &mut [SNode],
    uses: &BTreeMap<ValueId, usize>,
    decls: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => fold_async_run(run, uses, decls, stats),
            SNode::If {
                then, otherwise, ..
            } => {
                async_fold_seq(then, uses, decls, stats);
                async_fold_seq(otherwise, uses, decls, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after async_driver_fold
            // (emit.rs:512 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => async_fold_seq(body, uses, decls, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                async_fold_seq(body, uses, decls, stats);
                for c in catches {
                    async_fold_seq(&mut c.body, uses, decls, stats);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // async_driver_fold — c-COV diagnosis
                if let Some(f) = finally {
                    async_fold_seq(f, uses, decls, stats);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_driver_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    async_fold_seq(&mut c.body, uses, decls, stats);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// One leaf run: fold adjacent AsyncDriver declares into their
/// return/throw consumer.
pub(in crate::folds) fn fold_async_run(
    run: &mut Vec<Leaf>,
    uses: &BTreeMap<ValueId, usize>,
    decls: &BTreeMap<ValueId, usize>,
    stats: &mut FoldStats,
) {
    let mut i = 0;
    while i < run.len() {
        // Inlined form: `return asyncDriver(v)` directly.
        if let Leaf::Raw(Stmt::Return(Some(Expr::AsyncDriver { resolve, value }))) = &run[i] {
            let (resolve, value) = (*resolve, (**value).clone());
            run[i] = Leaf::Raw(if resolve {
                Stmt::Return(Some(value))
            } else {
                Stmt::Throw(value)
            });
            stats.async_driver += 1;
            i += 1;
            continue;
        }
        // Temp form: `const t = asyncDriver(v); return t;` — adjacent,
        // and `t` used exactly once in the whole tree (the return).
        if let Leaf::Raw(Stmt::Declare {
            value: Expr::AsyncDriver { resolve, value },
            value_id,
            ..
        }) = &run[i]
        {
            let (resolve, value, vid) = (*resolve, (**value).clone(), *value_id);
            let adjacent_return = matches!(
                run.get(i + 1),
                Some(Leaf::Raw(Stmt::Return(Some(e)))) if temp_value(e) == Some(vid)
            );
            // uses == declares: exactly one use per declare — each
            // (possibly duplicated) copy is consumed by its own
            // adjacent return. The pre-duplication shape is 1 == 1.
            if adjacent_return
                && uses.get(&vid).copied().unwrap_or(0) == decls.get(&vid).copied().unwrap_or(0)
            {
                run.remove(i);
                run[i] = Leaf::Raw(if resolve {
                    Stmt::Return(Some(value))
                } else {
                    Stmt::Throw(value)
                });
                stats.async_driver += 1;
                continue; // re-examine index i
            }
        }
        i += 1;
    }
}

// ── Async suspend/resume fold (N68 remainder, R4) ──────────────────
//
// VENDOR LOWERING MODEL (es2panda
// `compiler/function/asyncFunctionBuilder.cpp` `Prepare`/
// `DirectReturn`/`CleanUp` + `compiler/function/functionBuilder.cpp`
// `Await`/`SuspendResumeExecution`/`resumeGenerator`/`HandleCompletion`;
// `enum class ResumeMode { RETURN=0, THROW=1, NEXT=2 }` in
// `functionBuilder.h`; runtime `ecmascript/interpreter/
// interpreter-inl.cpp` `ASYNCFUNCTIONAWAITUNCAUGHT_V8` :5357-5366,
// `SUSPENDGENERATOR_V8` :5279):
//
// - `Prepare` (async function entry): `AsyncFunctionEnter()` → funcObj
//   (elided at Stage A — §5 row 72; invisible in JS source) + the
//   catch-all `AsyncFunctionReject` wrapper (folded by
//   [`async_driver_fold`], N68/G6).
// - `Await` (per `await v`): `AsyncFunctionAwaitUncaught(funcObj)`
//   awaiting the acc value; `SuspendGenerator(funcObj)` suspending with
//   the acc; then the completion pair `ResumeGenerator(funcObj)` →
//   completionValue, `GetResumeMode(funcObj)` → completionType, and
//   `HandleCompletion` — for the ASYNC builder kind this is the THROW
//   test ONLY (no RETURN arm): `if (type == THROW) throw value;`
//   otherwise `value` is the await's resumption value and the body
//   continues. Source form: `await v` — the await expression's value
//   IS the resumption value, and a rejected promise throws.
//
// The fold eliminates the plumbing per await site: the await decl +
// the suspend stmt + the ResumeGenerator/GetResumeMode pair + the
// mode dispatch dissolve into `await v` (binding the resumption value
// at the await site when it has real uses); the dispatch's
// continuation (the real control flow) is spliced in place.
//
// SOUNDNESS / HONESTY (design §8 R4 budget, mirroring d-P11): the fold
// is per-function all-or-nothing gated on the ENTRY protocol — the
// unique `AsyncFunctionEnter` fallback temp (the funcObj) must exist
// and every visible use of it must be machinery (the `GeneratorDriver`
// genobj operand or a catch-region context phi assign). A function
// failing the gate keeps ALL of its machinery as documented fallbacks
// (today's behavior); with the gate passed, a non-matching site keeps
// its own loud fallbacks (counted). `FunctionKind::AsyncGenerator`
// carries no `AsyncFunctionEnter` (its entry is the generator
// `CreateGeneratorObj` protocol and its yields the
// `AsyncGeneratorResolve` machinery) and is a no-op here by
// construction — [`async_generator_machine_fold`] (d-P14) owns that
// kind.

/// Fold context for one async function body.
pub(in crate::folds) struct AsyncMachineCx {
    /// The unique `AsyncFunctionEnter` fallback temp (the funcObj).
    pub(in crate::folds) genobj: ValueId,
    /// N70: the funcObj plus its loop-header phi aliases (the constant
    /// funcObj routed through bookkeeping phis in loop-driving bodies).
    pub(in crate::folds) aliases: BTreeSet<ValueId>,
    /// N70: temps thrown at some loop's structural continuation (the
    /// verified break-routing targets for the loop-exit dispatch).
    pub(in crate::folds) exit_throws: BTreeSet<ValueId>,
    /// Pure number-constant temps (the mode immediate, when the
    /// profile materializes it) by value id.
    pub(in crate::folds) const_env: BTreeMap<ValueId, u64>,
    /// Const temps a successful dispatch match resolved.
    pub(in crate::folds) consumed_consts: BTreeSet<ValueId>,
    /// Whole-tree temp use counts, computed once up front (the fold
    /// only REMOVES the counted machinery uses, so the counts stay
    /// valid for the per-site dead-resume decisions).
    pub(in crate::folds) uses: BTreeMap<ValueId, usize>,
}

/// Fold the es2abc async suspend/resume machinery back into plain
/// `await` control flow. No-op for non-async kinds; the
/// async-generator kind is a no-op here (no `AsyncFunctionEnter`) —
/// [`async_generator_machine_fold`] (d-P14) owns it.
pub fn async_machine_fold(nodes: &mut Vec<SNode>, kind: FunctionKind, stats: &mut FoldStats) {
    if !matches!(kind, FunctionKind::Async | FunctionKind::AsyncArrow) {
        return;
    }
    // The entry gate: exactly one `AsyncFunctionEnter` fallback temp
    // (the funcObj). Zero: nothing to fold (a hypothetical machinery
    // user without the temp keeps its fallbacks). More than one: not
    // the vendor shape — bail entirely.
    let mut enters = Vec::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::Declare {
            value: Expr::Fallback { op, .. },
            value_id,
            ..
        }) = l
            && *op == "AsyncFunctionEnter"
        {
            enters.push(*value_id);
        }
    });
    let [genobj] = enters[..] else {
        return;
    };
    // N70: the funcObj is a per-invocation constant, but in loop-driving
    // bodies (the plain-async `for await` driver shape) es2abc's
    // try-region/loop bookkeeping routes it through header phi temps —
    // the machinery's genobj operand reads the phi, not the entry temp.
    // Compute the alias closure: phi temps whose every assign is the
    // funcObj or another alias (self-assigns are neutral), with at
    // least one real funcObj-source assign.
    let aliases = funcobj_aliases(nodes, genobj);
    // Every visible use of the funcObj (and of each alias) must be
    // machinery: a `GeneratorDriver` genobj operand, or a catch-region
    // context phi assign (`phi = funcobj` — the es2abc try-region
    // bookkeeping the rethrow-only handler never reads). Any other use
    // is not the vendor shape — bail, keeping everything loud.
    if !funcobj_uses_are_machinery(nodes, &aliases) {
        return;
    }
    // N70: the loop-internal await's mode dispatch may exit the loop
    // (`if (mode == THROW) break;`) to a `throw <resume>` block the
    // structurer places AFTER the loop (canonical loop-exit emission)
    // instead of the inline-throw arm the straight-line shape uses.
    // Pre-verify the routing: the temp thrown at each loop's structural
    // continuation. A break-routed dispatch matches only when its
    // resume temp's exit throw is found here.
    let exit_throws = collect_loop_exit_throws(nodes);
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
    let mut cx = AsyncMachineCx {
        genobj,
        aliases,
        exit_throws,
        const_env,
        consumed_consts: BTreeSet::new(),
        uses,
    };
    async_machine_seq(nodes, &mut cx, stats);
    // Sweep the temps the fold made dead: resolved mode-immediate
    // consts, and the funcObj fallback temp itself once its remaining
    // uses are only dead catch-region phi assigns (N68 remainder item:
    // the `AsyncFunctionEnter` elided-value fallback resolves when the
    // machinery that consumed the value is gone). A partially folded
    // function keeps the temp — and the surviving sites keep their
    // loud fallbacks.
    sweep_async_machinery(nodes, genobj, &cx.aliases, &cx.consumed_consts);
}

/// N70: the alias closure of the funcObj temp — phi temps whose every
/// assign is the funcObj or another alias (loop-header bookkeeping
/// routing the constant funcObj through phis; self-assigns are
/// neutral). An alias must have at least one assign from a DIFFERENT
/// alias (a real funcObj source — a phi fed only by itself is dead
/// bookkeeping, not the funcObj). The returned set includes `genobj`.
pub(in crate::folds) fn funcobj_aliases(nodes: &[SNode], genobj: ValueId) -> BTreeSet<ValueId> {
    // Phi temp name → value id (PhiAssign targets are name-linked).
    let mut phi_ids: BTreeMap<String, ValueId> = BTreeMap::new();
    // Phi target name → assigned value exprs.
    let mut assigns: BTreeMap<String, Vec<Expr>> = BTreeMap::new();
    walk_leaves(nodes, &mut |l| match l {
        Leaf::Raw(Stmt::PhiDecl { name, value_id }) => {
            phi_ids.insert(name.clone(), *value_id);
        }
        Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => {
            assigns
                .entry(target.clone())
                .or_default()
                .push(value.clone());
        }
        _ => {}
    });
    let mut aliases: BTreeSet<ValueId> = [genobj].into_iter().collect();
    loop {
        let mut grew = false;
        for (name, vid) in &phi_ids {
            if aliases.contains(vid) {
                continue;
            }
            let Some(vals) = assigns.get(name) else {
                continue; // assign-less phi: dead bookkeeping, not an alias
            };
            let mut has_real_source = false;
            let ok = vals.iter().all(|v| match temp_value(v) {
                Some(src) if src == *vid => true, // self-assign: neutral
                Some(src) if aliases.contains(&src) => {
                    has_real_source = true;
                    true
                }
                _ => false,
            });
            if ok && has_real_source {
                aliases.insert(*vid);
                grew = true;
            }
        }
        if !grew {
            return aliases;
        }
    }
}

/// N70: the temps thrown at each loop's structural continuation (the
/// first significant statement after the loop, descending through
/// finally-style try wrappers). Used to verify the break-routed
/// mode==THROW dispatch of the for-await driver shape: the folded
/// `await`'s implicit rejection throw is equivalent only when the
/// removed `break` routed to `throw <resume temp>`.
pub(in crate::folds) fn collect_loop_exit_throws(nodes: &[SNode]) -> BTreeSet<ValueId> {
    fn first_significant_stmt(nodes: &[SNode]) -> Option<&Stmt> {
        for n in nodes {
            match n {
                SNode::Honest(_) => continue,
                SNode::Stmts(run) => {
                    let sig = run.iter().find(|l| {
                        !matches!(l, Leaf::Raw(Stmt::PhiAssign { .. } | Stmt::PhiDecl { .. }))
                    });
                    match sig {
                        None => continue,
                        Some(Leaf::Raw(s)) => return Some(s),
                        Some(_) => return None, // synthetic leaf: not a throw
                    }
                }
                SNode::Try { body, .. } => match first_significant_stmt(body) {
                    None => continue, // empty try: fall to next sibling
                    some => return some,
                },
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                // unreachable: ForOf/ForIn nodes are created only inside
                // fold() (folds.rs:1418/1433/2577), which runs after
                // async_machine_fold (emit.rs:517 vs 531) — c-COV diagnosis
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => return first_significant_stmt(body),
                // If/Switch/Break/Continue: the first executed statement
                // is not statically unique (or not a fall-through).
                _ => return None,
            }
        }
        None
    }
    fn continuation_throw(stack: &[&[SNode]]) -> Option<ValueId> {
        for level in stack.iter().rev() {
            match first_significant_stmt(level) {
                Some(Stmt::Throw(e)) => return temp_value(e),
                Some(_) => return None,
                None => continue, // nothing significant here — one level up
            }
        }
        None
    }
    fn visit<'a>(nodes: &'a [SNode], stack: &mut Vec<&'a [SNode]>, out: &mut BTreeSet<ValueId>) {
        for (k, n) in nodes.iter().enumerate() {
            stack.push(&nodes[k + 1..]);
            match n {
                SNode::While { body, .. } | SNode::DoWhile { body, .. } => {
                    if let Some(t) = continuation_throw(stack) {
                        out.insert(t);
                    }
                    visit(body, stack, out);
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    visit(then, stack, out);
                    visit(otherwise, stack, out);
                }
                SNode::Labeled { body, .. }
                // unreachable: ForOf/ForIn nodes are created only inside
                // fold(), which runs after async_machine_fold (emit.rs:517
                // vs 531) — c-COV diagnosis
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => visit(body, stack, out),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    visit(body, stack, out);
                    for c in catches {
                        visit(&c.body, stack, out);
                    }
                    // unreachable: Try.finally is Some only after
                    // fold_finally (folds.rs:4143/4154) inside fold(),
                    // which runs after async_machine_fold — c-COV diagnosis
                    if let Some(f) = finally {
                        visit(f, stack, out);
                    }
                }
                // unreachable: SNode::Switch is created only by
                // fold_switches (folds.rs:3115/3183) inside fold(), which
                // runs after async_machine_fold — c-COV diagnosis
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        visit(&c.body, stack, out);
                    }
                }
                SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
            stack.pop();
        }
    }
    let mut out = BTreeSet::new();
    visit(nodes, &mut Vec::new(), &mut out);
    out
}

/// The entry-gate check: every occurrence of the funcObj temp (and of
/// each N70 phi alias of it) is a `GeneratorDriver` genobj operand or
/// a phi assign of the temp.
pub(in crate::folds) fn funcobj_uses_are_machinery(
    nodes: &[SNode],
    aliases: &BTreeSet<ValueId>,
) -> bool {
    /// `in_genobj_slot` marks the `GeneratorDriver::genobj` operand
    /// position (the only legal expression use of the temp).
    fn expr_ok(e: &Expr, aliases: &BTreeSet<ValueId>, in_genobj_slot: bool) -> bool {
        if let Some(v) = temp_value(e)
            && aliases.contains(&v)
        {
            return in_genobj_slot;
        }
        match e {
            Expr::GeneratorDriver { genobj: g, .. } => expr_ok(g, aliases, true),
            _ => expr_children(e).iter().all(|c| expr_ok(c, aliases, false)),
        }
    }
    let mut ok = true;
    walk_leaves(nodes, &mut |l| {
        if !ok {
            return;
        }
        if let Leaf::Raw(Stmt::PhiAssign { value, .. }) = l {
            // `phi = funcobj` (the catch-region context phi) and the
            // N70 alias wiring (`phi = alias`, self-assigns) are
            // machinery bookkeeping; anything richer is not.
            ok = !aliases.iter().any(|a| expr_uses_value(value, *a))
                || temp_value(value).is_some_and(|v| aliases.contains(&v));
            return;
        }
        for e in leaf_exprs(l) {
            if !expr_ok(e, aliases, false) {
                ok = false;
                return;
            }
        }
    });
    ok
}

/// One matched await site (immutable match; applied separately).
pub(in crate::folds) struct AsyncSite {
    /// Run leaf indices of the machinery leaves (descending).
    pub(in crate::folds) remove: Vec<usize>,
    /// Offset of the dispatch node from the machinery run (1 + the
    /// number of intervening phi-partition runs).
    pub(in crate::folds) dispatch_off: usize,
    /// The awaited value expression (moved into the folded `await`).
    pub(in crate::folds) awaited: Expr,
    /// The resume temp binding, when the `ResumeGenerator` result was
    /// a declared temp (always in practice: its uses live in sibling
    /// blocks, so Stage A never inlines it).
    pub(in crate::folds) resume: Option<(ValueId, String)>,
    /// The dispatch's continuation (the real control flow).
    pub(in crate::folds) continuation: Vec<SNode>,
}

/// The index of the previous non-phi-assign leaf before `cur`
/// (block-end phi materializations interleave with the machinery).
pub(in crate::folds) fn prev_non_phi(run: &[Leaf], cur: &mut usize) -> Option<usize> {
    while *cur > 0 {
        *cur -= 1;
        if !matches!(run[*cur], Leaf::Raw(Stmt::PhiAssign { .. })) {
            return Some(*cur);
        }
    }
    None
}

/// Match `nodes[i]` (a `Stmts` run ending in the await site:
/// `[decl a = AwaitUncaught(v), SuspendGenerator-stmt(a), decl r =
/// ResumeGenerator(g)?, decl m = GetResumeMode(g)?]`, phi assigns
/// skipped) + `nodes[i+1]` (the `mode == THROW` dispatch).
pub(in crate::folds) fn match_await_site(
    nodes: &[SNode],
    i: usize,
    cx: &mut AsyncMachineCx,
) -> Option<AsyncSite> {
    let SNode::Stmts(run) = &nodes[i] else {
        return None;
    };
    let mut remove: Vec<usize> = Vec::new();
    let mut cur = run.len();
    // Optional mode decl (tail-most machinery decl).
    let mut mode: Option<ValueId> = None;
    let mut save = cur;
    if let Some(j) = prev_non_phi(run, &mut cur) {
        match &run[j] {
            Leaf::Raw(Stmt::Declare {
                value:
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: mg,
                    },
                value_id,
                ..
            }) if temp_value(mg).is_some_and(|v| cx.aliases.contains(&v)) => {
                mode = Some(*value_id);
                remove.push(j);
            }
            _ => cur = save,
        }
    }
    // Optional resume decl.
    let mut resume: Option<(ValueId, String)> = None;
    save = cur;
    if let Some(j) = prev_non_phi(run, &mut cur) {
        match &run[j] {
            Leaf::Raw(Stmt::Declare {
                name,
                value:
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: rg,
                    },
                value_id,
                ..
            }) if temp_value(rg).is_some_and(|v| cx.aliases.contains(&v)) => {
                resume = Some((*value_id, name.clone()));
                remove.push(j);
            }
            _ => cur = save,
        }
    }
    // Required: the suspend stmt (`SuspendGenerator` — recovered as a
    // `Yield` expression; in an async body that is never a source
    // yield).
    let j = prev_non_phi(run, &mut cur)?;
    let Leaf::Raw(Stmt::Expr(Expr::Yield { value })) = &run[j] else {
        return None;
    };
    let awaited: Expr;
    match value.as_ref() {
        // Declared form: `const a = await v;` then the suspend of `a`.
        Expr::Temp { value: at, .. } => {
            // The await temp's only use may be the suspend.
            if cx.uses.get(at).copied().unwrap_or(0) != 1 {
                return None;
            }
            let k = prev_non_phi(run, &mut cur)?;
            let Leaf::Raw(Stmt::Declare {
                value:
                    Expr::Await {
                        value: x,
                        uncaught: true,
                    },
                value_id,
                ..
            }) = &run[k]
            else {
                return None;
            };
            if value_id != at {
                return None;
            }
            awaited = (**x).clone();
            remove.push(j);
            remove.push(k);
        }
        // Inlined form: the suspend carries the `await` directly.
        Expr::Await {
            value: x,
            uncaught: true,
        } => {
            awaited = (**x).clone();
            remove.push(j);
        }
        _ => return None,
    }
    // The dispatch follows, separated from the machinery run by any
    // number of phi-partition runs (the structurer splits block-end phi
    // materializations into their own `Stmts` runs).
    let mut dispatch_off = 1;
    while matches!(
        nodes.get(i + dispatch_off),
        Some(SNode::Stmts(run))
            if !run.is_empty()
                && run
                    .iter()
                    .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
    ) {
        dispatch_off += 1;
    }
    let continuation = match_async_dispatch(
        nodes.get(i + dispatch_off)?,
        mode,
        resume.as_ref().map(|(r, _)| *r),
        cx,
    )?;
    Some(AsyncSite {
        remove,
        dispatch_off,
        awaited,
        resume,
        continuation,
    })
}

/// Match the async resume-mode dispatch (`HandleCompletion`, ASYNC
/// builder kind): a single `mode == THROW(1)` test (either polarity,
/// either operand order, the immediate inline or via a pure const
/// temp, the mode operand a `Temp` of the matched mode decl or an
/// inlined `GetResumeMode`) whose THROW arm is exactly
/// `throw <resume>;`; the other arm is the continuation.
pub(in crate::folds) fn match_async_dispatch(
    n: &SNode,
    mode: Option<ValueId>,
    resume: Option<ValueId>,
    cx: &mut AsyncMachineCx,
) -> Option<Vec<SNode>> {
    let SNode::If {
        cond,
        then,
        otherwise,
    } = n
    else {
        return None;
    };
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
    let genobj = &cx.aliases;
    let is_mode = |e: &Expr| match mode {
        // Declared mode temp: the condition must reference it.
        Some(md) => temp_value(e) == Some(md),
        // Inlined `GetResumeMode` directly in the condition.
        None => matches!(
            e,
            Expr::GeneratorDriver {
                resume: false,
                genobj: mg,
            } if temp_value(mg).is_some_and(|v| genobj.contains(&v))
        ),
    };
    let bits = if is_mode(left) {
        resolve_num(right, &cx.const_env, &mut cx.consumed_consts)
    } else if is_mode(right) {
        resolve_num(left, &cx.const_env, &mut cx.consumed_consts)
    } else {
        None
    }?;
    // The ASYNC `HandleCompletion` tests THROW(1) only.
    if f64::from_bits(bits) != 1.0 {
        return None;
    }
    let (throw_arm, cont) = if positive {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    if check_async_throw_arm(throw_arm, resume, genobj).is_some() {
        return Some(cont.clone());
    }
    // N70: the loop-exit routing (break arm) — the continuation arm is
    // spliced in place exactly as for the inline-throw shape. The exit
    // throw the `break` routed to stays in place (dead post-fold: the
    // loop's remaining exits are terminal).
    if check_async_break_arm(throw_arm, resume, cx).is_some() {
        return Some(cont.clone());
    }
    None
}

/// The THROW arm: exactly `throw <resume>;` (+ the dead `Unreachable`,
/// any dead loop-bookkeeping `break`s, and any phi-partition runs — the
/// es2abc try-region bookkeeping assigns, which the parent block's own
/// assigns replicate for the folded await's throw), where `<resume>` is
/// the matched resume temp — or the inlined `ResumeGenerator` when the
/// result was never declared.
pub(in crate::folds) fn check_async_throw_arm(
    arm: &[SNode],
    resume: Option<ValueId>,
    genobj: &BTreeSet<ValueId>,
) -> Option<()> {
    let mut found = false;
    for n in arm {
        match n {
            // Phi partitions are block-end bookkeeping — skip.
            SNode::Stmts(run)
                if run
                    .iter()
                    .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. }))) => {}
            SNode::Stmts(run) => {
                if found {
                    return None;
                }
                // (A mixed run with interleaved phi assigns is fine
                // too.)
                let significant: Vec<&Leaf> = run
                    .iter()
                    .filter(|l| !matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))
                    .collect();
                match significant.as_slice() {
                    [Leaf::Raw(Stmt::Throw(value))]
                    | [Leaf::Raw(Stmt::Throw(value)), Leaf::Raw(Stmt::Unreachable)] => {
                        let ok = match resume {
                            Some(r) => temp_value(value) == Some(r),
                            None => matches!(
                                value,
                                Expr::GeneratorDriver {
                                    resume: true,
                                    genobj: rg,
                                } if temp_value(rg).is_some_and(|v| genobj.contains(&v))
                            ),
                        };
                        if !ok {
                            return None;
                        }
                        found = true;
                    }
                    _ => return None,
                }
            }
            // Dead loop-bookkeeping breaks after the diverging throw.
            SNode::Break { .. } => {}
            _ => return None,
        }
    }
    found.then_some(())
}

/// N70: the loop-internal dispatch's THROW arm when the structurer
/// routes the throw out of the loop — exactly one unlabeled `break`
/// (+ phi partitions). Sound only when the loop's continuation is
/// verified to be `throw <resume temp>` (the pre-pass
/// [`collect_loop_exit_throws`]): the folded `await`'s implicit
/// rejection throw then replaces the routing.
pub(in crate::folds) fn check_async_break_arm(
    arm: &[SNode],
    resume: Option<ValueId>,
    cx: &AsyncMachineCx,
) -> Option<()> {
    let r = resume?;
    if !cx.exit_throws.contains(&r) {
        return None;
    }
    let mut found = false;
    for n in arm {
        match n {
            SNode::Stmts(run)
                if run
                    .iter()
                    .all(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. }))) => {}
            SNode::Break { label: None } if !found => found = true,
            _ => return None,
        }
    }
    found.then_some(())
}

/// The rewrite pass: children first (inner sites fold before the
/// outer sites whose continuations contain them), then the scan.
pub(in crate::folds) fn async_machine_seq(
    nodes: &mut Vec<SNode>,
    cx: &mut AsyncMachineCx,
    stats: &mut FoldStats,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                async_machine_seq(then, cx, stats);
                async_machine_seq(otherwise, cx, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // async_machine_fold (emit.rs:517 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => async_machine_seq(body, cx, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                async_machine_seq(body, cx, stats);
                for c in catches {
                    async_machine_seq(&mut c.body, cx, stats);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // async_machine_fold — c-COV diagnosis
                if let Some(f) = finally {
                    async_machine_seq(f, cx, stats);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    async_machine_seq(&mut c.body, cx, stats);
                }
            }
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    let mut i = 0;
    while i + 1 < nodes.len() {
        let site = match_await_site(nodes, i, cx);
        match site {
            Some(site) => {
                let SNode::Stmts(run) = &mut nodes[i] else {
                    unreachable!()
                };
                // The machinery leaves were collected tail-first
                // (descending indices) — removal in order is safe.
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
                    // The resumption value has real uses beyond the
                    // (removed) throw arm: bind it — `const t = await v`.
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
                        stats.async_machine_bound += 1;
                    }
                    _ => run.insert(insert_at, Leaf::Raw(Stmt::Expr(aw))),
                }
                stats.async_machine_sites += 1;
                nodes.splice(
                    i + site.dispatch_off..i + site.dispatch_off + 1,
                    site.continuation,
                );
                i += 1;
            }
            None => i += 1,
        }
    }
}

/// Post-fold sweep: remove the resolved mode-immediate consts, and the
/// funcObj fallback temp once its remaining uses are only dead
/// catch-region phi assigns (`phi = funcobj` where the phi temp is
/// never read — es2abc try-region bookkeeping the rethrow-only handler
/// does not consume). Those phi assigns go with it, and a phi decl
/// left with no assigns and no reads goes too. Any other surviving
/// use keeps everything (loud partial fold).
pub(in crate::folds) fn sweep_async_machinery(
    nodes: &mut [SNode],
    genobj: ValueId,
    aliases: &BTreeSet<ValueId>,
    consumed: &BTreeSet<ValueId>,
) {
    let mut uses: BTreeMap<ValueId, usize> = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    // Phi temps by name (PhiAssign targets are name-linked).
    let mut phi_ids: BTreeMap<String, ValueId> = BTreeMap::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::PhiDecl { name, value_id }) = l {
            phi_ids.insert(name.clone(), *value_id);
        }
    });
    // Classify alias uses: a `phi = <alias>` assign FEEDS the phi
    // target (bookkeeping); any other occurrence is a REAL use. An
    // alias is dead bookkeeping when it has no real use and every phi
    // it feeds is dead bookkeeping too (the es2abc try-region chains —
    // N70: `v62 = v65; v65 = v7` — transitive, so a fixpoint).
    let mut feeds: BTreeMap<ValueId, Vec<ValueId>> = BTreeMap::new();
    let mut real_use: BTreeSet<ValueId> = BTreeSet::new();
    // Alias-valued assigns into DEAD non-alias phi temps lose just the
    // assign (the temp keeps its other sources) — the pre-N70 behavior.
    let mut strip_only: BTreeSet<String> = BTreeSet::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::PhiAssign { target, value, .. }) = l {
            let Some(v) = temp_value(value) else {
                // A richer phi-assign value may still read an alias.
                for a in aliases {
                    if expr_uses_value(value, *a) {
                        real_use.insert(*a);
                    }
                }
                return;
            };
            if !aliases.contains(&v) {
                return;
            }
            match phi_ids.get(target) {
                Some(tv) if aliases.contains(tv) => {
                    feeds.entry(v).or_default().push(*tv);
                }
                Some(tv) if uses.get(tv).copied().unwrap_or(0) == 0 => {
                    strip_only.insert(target.clone());
                }
                _ => {
                    real_use.insert(v);
                }
            }
            return;
        }
        for e in leaf_exprs(l) {
            for a in aliases {
                if expr_uses_value(e, *a) {
                    real_use.insert(*a);
                }
            }
        }
    });
    // Backward fixpoint: an alias is alive when it has a real use or
    // feeds an alive alias.
    let mut alive: BTreeSet<ValueId> = real_use;
    loop {
        let mut grew = false;
        for (a, targets) in &feeds {
            if !alive.contains(a) && targets.iter().any(|t| alive.contains(t)) {
                alive.insert(*a);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    let mut dead: BTreeSet<ValueId> = consumed
        .iter()
        .copied()
        .filter(|v| uses.get(v).copied().unwrap_or(0) == 0)
        .collect();
    if alive.is_empty() {
        // The whole bookkeeping web is dead: strip every assign into a
        // dead alias (all alias-valued by construction) and the
        // alias-valued assigns into dead non-alias phi temps, then the
        // decls left assign-less (and unread).
        let dead_alias_names: BTreeSet<String> = phi_ids
            .iter()
            .filter(|(_, vid)| aliases.contains(*vid) && !alive.contains(*vid))
            .map(|(n, _)| n.clone())
            .collect();
        let mut phi_targets = dead_alias_names.clone();
        phi_targets.extend(strip_only);
        dead.insert(genobj);
        if !phi_targets.is_empty() {
            strip_genobj_phi_assigns(nodes, aliases, &phi_targets);
            let mut remaining: BTreeSet<String> = BTreeSet::new();
            walk_leaves(nodes, &mut |l| {
                if let Leaf::Raw(Stmt::PhiAssign { target, .. }) = l {
                    remaining.insert(target.clone());
                }
            });
            // The pre-computed use counts still charge dead aliases
            // for the (removed) feed assigns — zero them for the decl
            // sweep.
            let mut uses_adj = uses.clone();
            for vid in aliases.iter().filter(|v| !alive.contains(*v)) {
                uses_adj.insert(*vid, 0);
            }
            strip_dead_phi_decls(nodes, &phi_targets, &remaining, &uses_adj);
        }
    }
    if !dead.is_empty() {
        sweep_dead_decls(nodes, &dead);
    }
}

/// Remove `PhiAssign` leaves assigning a funcObj-alias temp to one of
/// the dead phi targets.
pub(in crate::folds) fn strip_genobj_phi_assigns(
    nodes: &mut [SNode],
    aliases: &BTreeSet<ValueId>,
    targets: &BTreeSet<String>,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => run.retain(|l| {
                !matches!(
                    l,
                    Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                        if targets.contains(target)
                            && temp_value(value).is_some_and(|v| aliases.contains(&v))
                )
            }),
            SNode::If {
                then, otherwise, ..
            } => {
                strip_genobj_phi_assigns(then, aliases, targets);
                strip_genobj_phi_assigns(otherwise, aliases, targets);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // async_machine_fold (emit.rs:517 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => strip_genobj_phi_assigns(body, aliases, targets),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                strip_genobj_phi_assigns(body, aliases, targets);
                for c in catches {
                    strip_genobj_phi_assigns(&mut c.body, aliases, targets);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // async_machine_fold — c-COV diagnosis
                if let Some(f) = finally {
                    strip_genobj_phi_assigns(f, aliases, targets);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    strip_genobj_phi_assigns(&mut c.body, aliases, targets);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// Remove `PhiDecl`s for stripped targets that have no remaining
/// assigns and no reads.
pub(in crate::folds) fn strip_dead_phi_decls(
    nodes: &mut [SNode],
    targets: &BTreeSet<String>,
    remaining: &BTreeSet<String>,
    uses: &BTreeMap<ValueId, usize>,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => run.retain(|l| {
                !matches!(
                    l,
                    Leaf::Raw(Stmt::PhiDecl { name, value_id })
                        if targets.contains(name)
                            && !remaining.contains(name)
                            && uses.get(value_id).copied().unwrap_or(0) == 0
                )
            }),
            SNode::If {
                then, otherwise, ..
            } => {
                strip_dead_phi_decls(then, targets, remaining, uses);
                strip_dead_phi_decls(otherwise, targets, remaining, uses);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // async_machine_fold (emit.rs:517 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => strip_dead_phi_decls(body, targets, remaining, uses),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                strip_dead_phi_decls(body, targets, remaining, uses);
                for c in catches {
                    strip_dead_phi_decls(&mut c.body, targets, remaining, uses);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // async_machine_fold — c-COV diagnosis
                if let Some(f) = finally {
                    strip_dead_phi_decls(f, targets, remaining, uses);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // async_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    strip_dead_phi_decls(&mut c.body, targets, remaining, uses);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}
