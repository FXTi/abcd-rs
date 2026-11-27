//! Stage-B desugar fold rules (design/decompile.md §4.2 item 6): tree
//! rewrites over the structured [`SNode`] tree, run AFTER structuring —
//! pattern-matching here is safe by design (it post-processes a
//! correctly structured tree; it does not drive structuring).
//!
//! Landed folds:
//!
//! 1. **Object/array literal builders** (`AllocObject`/`AllocArray`
//!    shape + the consecutive own-store/spread/proto/method sequence
//!    the Stage-A [`crate::recover::builder_hook`] exposes) →
//!    [`Expr::ObjectBuild`]/[`Expr::ArrayBuild`] literals with spreads.
//! 2. **Rest destructuring**: `CreateObjectWithExcludedKeys` + the
//!    sibling excluded-key loads → `const {a, b, ...rest} = obj`.
//! 3. **Iterator loops → `for…of` / `for await…of`**: the es2abc
//!    shape (probe-verified on the corpus, stable across all 6 es2abc
//!    versions): pre-header `it = GetIterator(obj)` + `next = it.next`,
//!    header phis, `res = next()`, `done = res.done` test, body
//!    `v = res.value`, back-edge self-assigns — plus the optional
//!    iterator-cleanup try/catch (the `it.return()` protocol), which is
//!    dropped when the handler is cleanup-shaped.
//! 4. **`GetPropIterator`+`NextPropName` → `for…in`** (same probe).
//! 5. **Compare/branch chains → `switch`** (cosmetic re-detection; the
//!    IR lowers switch cascades to compare/branch chains by design —
//!    `design/ir.md`, `design/decisions.md`).
//! 6. **Generator driver machinery → plain `yield` bodies** (d-P11,
//!    R4): [`generator_machine_fold`] eliminates the es2abc generator
//!    state-machine plumbing (`CreateGenerator` + entry
//!    `SuspendGenerator(undefined)` + per-yield
//!    `CreateIterResultObj(v,false)` wrap + the
//!    `ResumeGenerator`/`GetResumeMode` completion pair + the
//!    resume-mode dispatch `if mode==RETURN return v; if mode==THROW
//!    throw v;`) back into the source-level `function*` body.
//!
//! `SuspendGenerator`→`yield` and `Await*`→`await` landed in Stage A
//! ([`Expr::Yield`]/[`Expr::Await`]); the emitter prints them.
//!
//! 7. **Async driver completion → `return`/`throw`** (N68/G6, R4):
//!    [`async_driver_fold`] rewrites the es2abc async-completion pair —
//!    `t = AsyncResolve(v); return t;` becomes `return v` (async
//!    completion IS the source-level return of an async body) and
//!    `t = AsyncReject(v); return t;` becomes `throw v` (the catch-all
//!    rejection wrapper IS the source-level uncaught throw). Sound
//!    since N68: the modern `asyncfunctionawaituncaught`/
//!    `asyncfunctionresolve`/`asyncfunctionreject` bytecodes carry the
//!    value in the ACCUMULATOR (isa.yaml `acc: inout:top`; runtime
//!    `ecmascript/interpreter/interpreter-inl.cpp`
//!    `ASYNCFUNCTIONAWAITUNCAUGHT_V8` :5357-5366,
//!    `ASYNCFUNCTIONRESOLVE_V8` :6577-6589, `ASYNCFUNCTIONREJECT_V8`
//!    :6605-6617) and the lift now models both operands
//!    (`Op::AwaitUncaught`/`AsyncResolve`/`AsyncReject` carry `funcobj`
//!    + `value`). Non-adjacent shapes keep the loud hard-fallback.
//! 8. **Async suspend/resume machinery → plain `await` control flow**
//!    (N68 remainder, R4): [`async_machine_fold`] eliminates the es2abc
//!    async-body state-machine plumbing (the entry `AsyncFunctionEnter`
//!    protocol + per-await `AsyncFunctionAwaitUncaught` +
//!    `SuspendGenerator` + the `ResumeGenerator`/`GetResumeMode`
//!    completion pair + the `mode == THROW → throw` dispatch — the
//!    ASYNC `HandleCompletion` kind, THROW test only) back into the
//!    source-level `await`: the resumption value binds at the await
//!    site (`const t = await v`) when used, the dispatch dissolves, and
//!    the funcObj temp is swept once nothing but dead catch-region phi
//!    assigns reference it. All-or-nothing per function, gated on the
//!    entry protocol; `AsyncGenerator` kinds are a no-op here (their
//!    `CreateGeneratorObj`/`AsyncGeneratorResolve` lowering is fold 9).
//! 9. **Async-generator machinery → plain `async function*` bodies**
//!    (d-P14, R4): [`async_generator_machine_fold`] eliminates the
//!    es2abc async-generator state-machine plumbing — the
//!    `CreateAsyncGeneratorObj` entry protocol (the entry suspend, NOT
//!    `AsyncFunctionEnter`), the per-yield pre-await (`yield v` awaits
//!    `v` first), the `AsyncGeneratorResolve(gen, awaited, false)`
//!    yield point, the THREE-way resume-mode dispatch (`RETURN(0)`:
//!    await the resume value and complete; `THROW(1)`: throw it;
//!    `NEXT(2)`: the yield's result value), source-level awaits
//!    (`HandleCompletion`, THROW-only like d-P13), the
//!    `AsyncGeneratorResolve(gen, v, true)` completions (explicit and
//!    implicit returns), and the catch-all `AsyncGeneratorReject`
//!    (folded by [`async_driver_fold`]) — back into the source-level
//!    `async function*` body. All-or-nothing per function, gated on
//!    the entry protocol; non-matching sites keep their loud
//!    fallbacks.
//! 10. **YieldStar driver loops → `yield* <expr>`** (d-P15, R4):
//!     [`yield_star_fold`] eliminates the es2abc yield-delegation
//!     machinery (`FunctionBuilder::YieldStar`): the
//!     `GetIterator`/`GetAsyncIterator` setup, the resume-mode
//!     dispatch (`NEXT`/`THROW`/`RETURN` with the delegate `throw`/
//!     `return` method lookups and the IteratorClose plumbing), the
//!     `method.call(iter, received)`, the pass-through suspend (the
//!     delegate's result object yields AS-IS — no iter-result wrap),
//!     the `done` test, and the completion dispatch (the delegation
//!     value vs the `.return()` propagation) — back into
//!     `yield* <expr>` (`const ret = yield* <expr>` when the
//!     delegate's completion value is used). Async (`async function*`)
//!     carries awaits around every protocol step and keeps the
//!     completion dispatch inside the loop's done arm. All-or-nothing
//!     per site; non-matching shapes keep their loud fallbacks.
//! 11. **Plain-async `for await` driver loops → literal `for await
//!    (const x of …)`** (d-P17, N70 residual 1):
//!     `match_for_await_driver` extends fold 3's iterator-loop
//!     recovery to the post-N70 driver shape — the header's folded
//!     dispatch await temp, the `next.call(it)` phi call, the
//!     break-routed `if (done) { TAIL; break } else { body; continue }`
//!     dispatch whose done arm absorbed the post-loop tail (re-homed
//!     AFTER the loop), and loop-carried bookkeeping phis collapsed to
//!     their invariant sources by substitution. The companion sweep
//!     `sweep_dead_loop_exit_throws` (N70 residual 2) removes the
//!     dead after-loop `throw <resume temp>` the break-routed dispatch
//!     left behind, under a whole-node unreachability proof (any doubt
//!     keeps it).

use crate::expr::{ArrayElem, Expr, IterOp, Lit, ObjEntry};
use crate::recover::Stmt;
use crate::structure::{Leaf, SNode, SwitchCase};
use abcd_ir::id::ValueId;
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{CmpOp, UnOp};
use std::collections::{BTreeMap, BTreeSet};

mod control;
mod for_await;
mod literals;
mod loops;
pub(crate) mod machines;
mod scope;

#[cfg(test)]
mod tests;

use control::{fold_finally, fold_switches};
use literals::fold_tagged_templates;
use loops::{fold_loops, fold_single_pass_for_ins, sweep_dead_loop_exit_throws};

pub use machines::{
    async_driver_fold, async_generator_machine_fold, async_machine_fold, generator_machine_fold,
    yield_star_fold,
};
pub use scope::{late_decl_fold, rest_param_fold, scope_fold};

/// Fold firing counters (the corpus gate prints them verbatim).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FoldStats {
    /// `for…of` loops folded.
    pub for_of: usize,
    /// `for await…of` loops folded.
    pub for_await_of: usize,
    /// `for…in` loops folded.
    pub for_in: usize,
    /// Object literals completed from builder sequences.
    pub object_lit: usize,
    /// Array literals completed from builder sequences.
    pub array_lit: usize,
    /// Rest destructurings folded.
    pub rest: usize,
    /// Compare/branch chains re-detected as `switch`.
    pub switch: usize,
    /// Duplicated-finally idioms re-factored into `finally { … }` (d-P8).
    pub finally_fold: usize,
    /// Lexenv slot initializations reconstructed as block-scoped
    /// `let` declarations (d-P8).
    pub scope_fold: usize,
    /// Late declaration-site reconstructions (N74-W4): a binding whose
    /// textually first store sits in a root-level statement run becomes
    /// `let n = v;` AT that store, restoring the TDZ/undeclared window
    /// the function-top hoisted `let`/`var` destroyed.
    pub late_decl: usize,
    /// Rest-parameter reconstructions (N74-W4): `CopyRestArgs` → a real
    /// `...rest` parameter.
    pub rest_param: usize,
    /// Generator resume-mode dispatch sites folded away (d-P11, R4;
    /// includes the entry site).
    pub gen_driver_sites: usize,
    /// Generator entry protocol suspends elided (d-P11).
    pub gen_driver_entry: usize,
    /// Yield results bound to a temp (`x = yield v` — the resume value
    /// has real uses; d-P11).
    pub gen_driver_bound: usize,
    /// Async-completion pairs folded to `return v` / `throw v`
    /// (N68/G6, R4).
    pub async_driver: usize,
    /// Async suspend/resume sites folded back to plain `await`
    /// control flow (N68 remainder, R4).
    pub async_machine_sites: usize,
    /// Async resumption values bound to a temp (`const t = await v` —
    /// the resumed value has real uses; N68 remainder).
    pub async_machine_bound: usize,
    /// Async-generator entry protocol suspends elided (d-P14).
    pub agen_entry: usize,
    /// Async-generator yield sites folded back to plain `yield`
    /// (d-P14).
    pub agen_yields: usize,
    /// Async-generator yield results bound to a temp (`x = yield v` —
    /// the resumption value has real uses; d-P14).
    pub agen_bound: usize,
    /// Async-generator source-level await sites folded back to plain
    /// `await` control flow (d-P14).
    pub agen_awaits: usize,
    /// Async-generator await resumption values bound to a temp
    /// (`const t = await v`; d-P14).
    pub agen_await_bound: usize,
    /// Async-generator completions folded to `return v` (d-P14;
    /// includes the explicit-return await sites).
    pub agen_returns: usize,
    /// YieldStar driver loops folded back to `yield* <expr>` (d-P15,
    /// R4; one per delegation site).
    pub yield_star_sites: usize,
    /// Delegation results bound to a temp (`const ret = yield* f()` —
    /// the delegate's completion value has real uses; d-P15).
    pub yield_star_bound: usize,
    /// Dead loop-exit dispatch throws swept (d-P17, N70 residual 2):
    /// the after-loop `throw <resume temp>` the async machine fold's
    /// break-routed dispatch left behind, removed only after a
    /// whole-node unreachability proof (`sweep_dead_loop_exit_throws`).
    pub dead_exit_throw: usize,
}

/// Run every fold over a structured body.
pub fn fold(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    fold_seq(nodes, stats);
    fold_tagged_templates(nodes);
}

/// Visit every `SNode::Stmts` leaf run in exact left-to-right DFS pre-order
/// (matching `scope_fold` Pass 1 and `Emitter`) using an explicit heap stack.
pub(in crate::folds) fn walk_stmts_runs_mut(
    nodes: &mut [SNode],
    mut f: impl FnMut(&mut Vec<Leaf>),
) {
    let mut stack: Vec<&mut [SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        let Some((first, rest)) = slice.split_first_mut() else {
            continue;
        };
        if !rest.is_empty() {
            stack.push(rest);
        }
        match first {
            SNode::Stmts(leaves) => f(leaves),
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
                for c in catches.iter_mut().rev() {
                    stack.push(&mut c.body);
                }
                stack.push(body);
            }
            SNode::Switch { cases, .. } => {
                for c in cases.iter_mut().rev() {
                    stack.push(&mut c.body);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// Apply `f` to every `Vec<SNode>` sequence in left-to-right depth-first
/// post-order (children before their enclosing sequence) without call-stack
/// recursion.
pub(in crate::folds) fn fold_snode_vecs_postorder(
    nodes: &mut Vec<SNode>,
    mut f: impl FnMut(&mut Vec<SNode>),
) {
    enum PostTask {
        EnterSeq(Vec<SNode>),
        FinishNode { shell: SNode, child_count: usize },
        FinishSeq(usize),
    }
    let mut tasks = vec![PostTask::EnterSeq(std::mem::take(nodes))];
    let mut done_seqs: Vec<Vec<SNode>> = Vec::new();
    let mut done_nodes: Vec<SNode> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            PostTask::EnterSeq(mut seq) => {
                let has_compound = seq.iter().any(|n| {
                    !matches!(
                        n,
                        SNode::Stmts(_)
                            | SNode::Break { .. }
                            | SNode::Continue { .. }
                            | SNode::Honest(_)
                    )
                });
                if !has_compound {
                    f(&mut seq);
                    done_seqs.push(seq);
                    continue;
                }
                tasks.push(PostTask::FinishSeq(seq.len()));
                for mut n in seq.into_iter().rev() {
                    match &mut n {
                        SNode::Stmts(_)
                        | SNode::Break { .. }
                        | SNode::Continue { .. }
                        | SNode::Honest(_) => {
                            tasks.push(PostTask::FinishNode {
                                shell: n,
                                child_count: 0,
                            });
                        }
                        SNode::If {
                            then, otherwise, ..
                        } => {
                            let t = std::mem::take(then);
                            let o = std::mem::take(otherwise);
                            tasks.push(PostTask::FinishNode {
                                shell: n,
                                child_count: 2,
                            });
                            tasks.push(PostTask::EnterSeq(o));
                            tasks.push(PostTask::EnterSeq(t));
                        }
                        SNode::Block(body)
                        | SNode::While { body, .. }
                        | SNode::DoWhile { body, .. }
                        | SNode::Labeled { body, .. }
                        | SNode::ForOf { body, .. }
                        | SNode::ForIn { body, .. } => {
                            let b = std::mem::take(body);
                            tasks.push(PostTask::FinishNode {
                                shell: n,
                                child_count: 1,
                            });
                            tasks.push(PostTask::EnterSeq(b));
                        }
                        SNode::Try {
                            body,
                            catches,
                            finally,
                            ..
                        } => {
                            let b = std::mem::take(body);
                            let mut c_seqs: Vec<Vec<SNode>> = catches
                                .iter_mut()
                                .map(|c| std::mem::take(&mut c.body))
                                .collect();
                            let fin = finally.as_mut().map(std::mem::take);
                            let child_count = 1 + c_seqs.len() + usize::from(fin.is_some());
                            tasks.push(PostTask::FinishNode {
                                shell: n,
                                child_count,
                            });
                            if let Some(fseq) = fin {
                                tasks.push(PostTask::EnterSeq(fseq));
                            }
                            while let Some(cseq) = c_seqs.pop() {
                                tasks.push(PostTask::EnterSeq(cseq));
                            }
                            tasks.push(PostTask::EnterSeq(b));
                        }
                        SNode::Switch { cases, .. } => {
                            let mut c_seqs: Vec<Vec<SNode>> = cases
                                .iter_mut()
                                .map(|c| std::mem::take(&mut c.body))
                                .collect();
                            let child_count = c_seqs.len();
                            tasks.push(PostTask::FinishNode {
                                shell: n,
                                child_count,
                            });
                            while let Some(cseq) = c_seqs.pop() {
                                tasks.push(PostTask::EnterSeq(cseq));
                            }
                        }
                    }
                }
            }
            PostTask::FinishNode {
                mut shell,
                child_count,
            } => {
                if child_count > 0 {
                    let mut children = done_seqs.split_off(done_seqs.len() - child_count);
                    let mut it = children.drain(..);
                    match &mut shell {
                        SNode::If {
                            then, otherwise, ..
                        } => {
                            *then = it.next().unwrap_or_default();
                            *otherwise = it.next().unwrap_or_default();
                        }
                        SNode::Block(body)
                        | SNode::While { body, .. }
                        | SNode::DoWhile { body, .. }
                        | SNode::Labeled { body, .. }
                        | SNode::ForOf { body, .. }
                        | SNode::ForIn { body, .. } => {
                            *body = it.next().unwrap_or_default();
                        }
                        SNode::Try {
                            body,
                            catches,
                            finally,
                            ..
                        } => {
                            *body = it.next().unwrap_or_default();
                            for c in catches.iter_mut() {
                                c.body = it.next().unwrap_or_default();
                            }
                            if let Some(fin) = finally.as_mut() {
                                *fin = it.next().unwrap_or_default();
                            }
                        }
                        SNode::Switch { cases, .. } => {
                            for c in cases.iter_mut() {
                                c.body = it.next().unwrap_or_default();
                            }
                        }
                        _ => {}
                    }
                }
                done_nodes.push(shell);
            }
            PostTask::FinishSeq(len) => {
                let mut seq = done_nodes.split_off(done_nodes.len() - len);
                f(&mut seq);
                done_seqs.push(seq);
            }
        }
    }
    *nodes = done_seqs.pop().unwrap_or_default();
}

fn fold_all_rest_destructure(nodes: &mut [SNode], stats: &mut FoldStats) {
    walk_stmts_runs_mut(nodes, |leaves| {
        literals::fold_rest_destructure(leaves, stats);
    });
}

pub(in crate::folds) fn fold_seq(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    fold_all_rest_destructure(nodes, stats);
    let mut use_counts = BTreeMap::new();
    count_temp_uses(nodes, &mut use_counts);
    fold_seq_with_uses(nodes, Some(&use_counts), stats);
}

fn fold_seq_with_uses(
    nodes: &mut Vec<SNode>,
    global_uses: Option<&BTreeMap<ValueId, usize>>,
    stats: &mut FoldStats,
) {
    walk_stmts_runs_mut(nodes, |leaves| {
        literals::fold_leaves_with_uses(leaves, global_uses, stats);
    });
    fold_snode_vecs_postorder(nodes, |seq| {
        dissolve_rethrow_trys(seq);
        sweep_dead_loop_exit_throws(seq, stats);
        fold_loops(seq, stats);
        fold_single_pass_for_ins(seq, stats);
        fold_switches(seq, stats);
        fold_finally(seq, stats);
    });
}

/// Dissolve `try { X } catch (e) { throw e; }` wrappers — a semantic
/// no-op es2abc emits around protected entry sequences (probe-verified;
/// the handler is a bare rethrow).
pub(in crate::folds) fn dissolve_rethrow_trys(nodes: &mut Vec<SNode>) {
    let mut i = 0;
    while i < nodes.len() {
        let dissolve = match &nodes[i] {
            SNode::Try { body, catches, .. } => {
                !body.is_empty()
                    && catches.iter().all(|c| {
                        let binding = c.binding.clone().unwrap_or_default();
                        let mut saw_rethrow = false;
                        c.body.iter().all(|n| match n {
                            SNode::Stmts(leaves) => leaves.iter().all(|l| match l {
                                Leaf::Raw(Stmt::Throw(e))
                                    if temp_name(e) == Some(binding.as_str()) =>
                                {
                                    saw_rethrow = true;
                                    true
                                }
                                Leaf::Raw(Stmt::Unreachable) => true,
                                Leaf::Raw(Stmt::Elided { op, .. })
                                    if *op == "SetGeneratorState" =>
                                {
                                    true
                                }
                                _ => false,
                            }),
                            _ => false,
                        }) && saw_rethrow
                    })
            }
            _ => false,
        };
        if dissolve {
            let mut removed = nodes.remove(i);
            let SNode::Try { body, .. } = &mut removed else {
                unreachable!()
            };
            let mut replacement: Vec<SNode> = vec![SNode::Honest(
                "rethrow-only try/catch dissolved (semantic no-op)".to_string(),
            )];
            replacement.extend(std::mem::take(body));
            nodes.splice(i..i, replacement);
            i += 1;
        } else {
            i += 1;
        }
    }
}

// ── Shared matching helpers ──────────────────────────────────────────

/// The name a plain value-reference expression refers to (a Stage-A
/// temp, or an identifier — catch bindings print as [`Expr::Ident`]).
pub(in crate::folds) fn temp_name(e: &Expr) -> Option<&str> {
    match e {
        Expr::Temp { name, .. } | Expr::Ident(name) => Some(name),
        _ => None,
    }
}

/// The temp VALUE id an expression refers to.
pub(in crate::folds) fn temp_value(e: &Expr) -> Option<abcd_ir::ValueId> {
    match e {
        Expr::Temp { value, .. } => Some(*value),
        _ => None,
    }
}

/// Whether the expression mentions a temp with SSA value `vid` (iterative).
pub(in crate::folds) fn expr_uses_value(e: &Expr, vid: abcd_ir::ValueId) -> bool {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        if temp_value(cur) == Some(vid) {
            return true;
        }
        stack.extend(expr_children(cur));
    }
    false
}

/// Whether any leaf in the list mentions a temp named `name`.
pub(in crate::folds) fn leaves_use_name(leaves: &[Leaf], name: &str) -> bool {
    leaves.iter().any(|l| leaf_uses_name(l, name))
}

pub(in crate::folds) fn leaf_uses_name(l: &Leaf, name: &str) -> bool {
    match l {
        Leaf::Raw(s) => stmt_uses_name(s, name),
        Leaf::Destructure { obj, .. } => expr_uses_name(obj, name),
        Leaf::Decl { value, .. } => value.as_ref().is_some_and(|v| expr_uses_name(v, name)),
        Leaf::Assign { value, target } => target == name || expr_uses_name(value, name),
    }
}

pub(in crate::folds) fn stmt_uses_name(s: &Stmt, name: &str) -> bool {
    match s {
        Stmt::Declare { value, name: n, .. } => n == name || expr_uses_name(value, name),
        Stmt::PhiDecl { name: n, .. } => n == name,
        Stmt::PhiAssign { target, value, .. } => target == name || expr_uses_name(value, name),
        Stmt::Expr(e) | Stmt::Throw(e) => expr_uses_name(e, name),
        Stmt::Return(Some(e)) => expr_uses_name(e, name),
        Stmt::StoreProp { object, value, .. } => {
            expr_uses_name(object, name) || expr_uses_name(value, name)
        }
        Stmt::StoreIndex {
            object,
            index,
            value,
            ..
        } => {
            expr_uses_name(object, name)
                || expr_uses_name(index, name)
                || expr_uses_name(value, name)
        }
        Stmt::StoreDyn {
            object, key, value, ..
        } => {
            expr_uses_name(object, name) || expr_uses_name(key, name) || expr_uses_name(value, name)
        }
        Stmt::DefineMethod { object, func, .. } => {
            expr_uses_name(object, name) || expr_uses_name(func, name)
        }
        Stmt::StorePrivate { object, value, .. } => {
            expr_uses_name(object, name) || expr_uses_name(value, name)
        }
        Stmt::StoreSuper { key, value, .. } => {
            key.as_ref().is_some_and(|k| expr_uses_name(k, name)) || expr_uses_name(value, name)
        }
        Stmt::LexStore { value, name: n, .. } => n == name || expr_uses_name(value, name),
        Stmt::GlobalStore { value, .. } | Stmt::ModuleStore { value, .. } => {
            expr_uses_name(value, name)
        }
        Stmt::CondBranch { cond, .. } => expr_uses_name(cond, name),
        _ => false,
    }
}

/// Whether an expression mentions a temp/ident with `name` (iterative).
pub(in crate::folds) fn expr_uses_name(e: &Expr, name: &str) -> bool {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Temp { name: n, .. } | Expr::Ident(n) if n == name => return true,
            _ => stack.extend(expr_children(cur)),
        }
    }
    false
}

/// All direct child expressions (for the name walker).
pub(crate) fn expr_children(e: &Expr) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match e {
        Expr::PropName { object, .. } => out.push(object),
        Expr::PropIndex { object, index } => {
            out.push(object);
            out.push(index);
        }
        Expr::PropDyn { object, key } => {
            out.push(object);
            out.push(key);
        }
        Expr::PrivateLoad { object, .. } | Expr::PrivateTest { object, .. } => out.push(object),
        Expr::SuperProp { key: Some(k), .. } => out.push(k),
        Expr::Call {
            callee, this, args, ..
        } => {
            out.push(callee);
            if let Some(t) = this {
                out.push(t);
            }
            out.extend(args.iter());
        }
        Expr::TaggedTemplate { tag, exprs, .. } => {
            out.push(tag);
            out.extend(exprs.iter());
        }
        Expr::DynamicImport { specifier } => out.push(specifier),
        Expr::Unary { operand, .. } => out.push(operand),
        Expr::Delete { target } => out.push(target),
        Expr::Binary { left, right, .. } | Expr::Compare { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        Expr::Yield { value } | Expr::YieldStar { value } | Expr::Await { value, .. } => {
            out.push(value)
        }
        Expr::IterResultObj { value, done } => {
            out.push(value);
            out.push(done);
        }
        Expr::Iter { obj, .. } => out.push(obj),
        Expr::CreateGenerator { func } => out.push(func),
        Expr::GeneratorDriver { genobj, .. } => out.push(genobj),
        Expr::AsyncDriver { value, .. } => out.push(value),
        Expr::AsyncGeneratorResolve {
            genobj,
            value,
            done,
        } => {
            out.push(genobj);
            out.push(value);
            out.push(done);
        }
        Expr::CopyDataProps { dst, src } => {
            out.push(dst);
            out.push(src);
        }
        Expr::SetObjectWithProto { obj, proto } => {
            out.push(obj);
            out.push(proto);
        }
        Expr::ArraySpread { dst, index, src } => {
            out.push(dst);
            out.push(index);
            out.push(src);
        }
        Expr::RestObject { obj, excluded } => {
            out.push(obj);
            out.extend(excluded.iter());
        }
        Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        } => {
            out.push(obj);
            out.push(key);
            out.push(getter);
            out.push(setter);
        }
        Expr::Closure { captures, .. } => out.extend(captures.iter().map(|(_, v)| v)),
        Expr::Class {
            heritage: Some(h), ..
        } => out.push(h),
        Expr::ObjectBuild { entries } => {
            for e in entries {
                match e {
                    ObjEntry::KeyValue(_, v) => out.push(v),
                    ObjEntry::Computed(k, v) => {
                        out.push(k);
                        out.push(v);
                    }
                    ObjEntry::Spread(s) | ObjEntry::Proto(s) => out.push(s),
                    ObjEntry::Method(_, f) => out.push(f),
                    ObjEntry::Getter(k, f) | ObjEntry::Setter(k, f) => {
                        if let crate::expr::ObjKey::Computed(c) = k {
                            out.push(c);
                        }
                        out.push(f);
                    }
                }
            }
        }
        Expr::ArrayBuild { elements } => {
            for e in elements {
                match e {
                    ArrayElem::Item(i) | ArrayElem::Spread(i) => out.push(i),
                }
            }
        }
        Expr::Fallback { operands, .. } => out.extend(operands.iter()),
        _ => {}
    }
    out
}

/// Strip `istrue`/`isfalse`/`!` wrappers from a condition; returns the
/// core expression (parity irrelevant for the fold patterns here).
pub(in crate::folds) fn strip_cond(mut e: &Expr) -> &Expr {
    loop {
        match e {
            Expr::Unary {
                op:
                    abcd_ir::op::UnOp::IsTrue
                    | abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::JumpNez
                    | abcd_ir::op::UnOp::JumpEqz
                    | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => e = operand,
            _ => return e,
        }
    }
}

pub(crate) fn expr_children_mut(e: &mut Expr) -> Vec<&mut Expr> {
    let mut out: Vec<&mut Expr> = Vec::new();
    match e {
        Expr::PropName { object, .. } => out.push(object),
        Expr::PropIndex { object, index } => {
            out.push(object);
            out.push(index);
        }
        Expr::PropDyn { object, key } => {
            out.push(object);
            out.push(key);
        }
        Expr::PrivateLoad { object, .. } | Expr::PrivateTest { object, .. } => out.push(object),
        Expr::SuperProp { key: Some(k), .. } => out.push(k),
        Expr::Call {
            callee, this, args, ..
        } => {
            out.push(callee);
            if let Some(t) = this {
                out.push(t);
            }
            out.extend(args.iter_mut());
        }
        Expr::TaggedTemplate { tag, exprs, .. } => {
            out.push(tag);
            out.extend(exprs.iter_mut());
        }
        Expr::DynamicImport { specifier } => out.push(specifier),
        Expr::Unary { operand, .. } => out.push(operand),
        Expr::Delete { target } => out.push(target),
        Expr::Binary { left, right, .. } | Expr::Compare { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        Expr::Yield { value } | Expr::YieldStar { value } | Expr::Await { value, .. } => {
            out.push(value)
        }
        Expr::IterResultObj { value, done } => {
            out.push(value);
            out.push(done);
        }
        Expr::Iter { obj, .. } => out.push(obj),
        Expr::CreateGenerator { func } => out.push(func),
        Expr::GeneratorDriver { genobj, .. } => out.push(genobj),
        Expr::AsyncDriver { value, .. } => out.push(value),
        Expr::AsyncGeneratorResolve {
            genobj,
            value,
            done,
        } => {
            out.push(genobj);
            out.push(value);
            out.push(done);
        }
        Expr::CopyDataProps { dst, src } => {
            out.push(dst);
            out.push(src);
        }
        Expr::SetObjectWithProto { obj, proto } => {
            out.push(obj);
            out.push(proto);
        }
        Expr::ArraySpread { dst, index, src } => {
            out.push(dst);
            out.push(index);
            out.push(src);
        }
        Expr::RestObject { obj, excluded } => {
            out.push(obj);
            out.extend(excluded.iter_mut());
        }
        Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        } => {
            out.push(obj);
            out.push(key);
            out.push(getter);
            out.push(setter);
        }
        Expr::Closure { captures, .. } => out.extend(captures.iter_mut().map(|(_, v)| v)),
        Expr::Class {
            heritage: Some(h), ..
        } => out.push(h),
        Expr::ObjectBuild { entries } => {
            for e in entries {
                match e {
                    ObjEntry::KeyValue(_, v) => out.push(v),
                    ObjEntry::Computed(k, v) => {
                        out.push(k);
                        out.push(v);
                    }
                    ObjEntry::Spread(s) | ObjEntry::Proto(s) => out.push(s),
                    ObjEntry::Method(_, f) => out.push(f),
                    ObjEntry::Getter(k, f) | ObjEntry::Setter(k, f) => {
                        if let crate::expr::ObjKey::Computed(c) = k {
                            out.push(c);
                        }
                        out.push(f);
                    }
                }
            }
        }
        Expr::ArrayBuild { elements } => {
            for e in elements {
                match e {
                    ArrayElem::Item(i) | ArrayElem::Spread(i) => out.push(i),
                }
            }
        }
        Expr::Fallback { operands, .. } => out.extend(operands.iter_mut()),
        _ => {}
    }
    out
}

/// Walk every leaf of a structured tree in pre-order (iterative).
pub(in crate::folds) fn walk_leaves(nodes: &[SNode], f: &mut impl FnMut(&Leaf)) {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        if slice.is_empty() {
            continue;
        }
        let n = &slice[0];
        let rest = &slice[1..];
        if !rest.is_empty() {
            stack.push(rest);
        }
        match n {
            SNode::Stmts(run) => run.iter().for_each(&mut *f),
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
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// Does any expression in the tree reference the given temp value? (iterative)
pub(in crate::folds) fn nodes_use_temp(nodes: &[SNode], id: ValueId) -> bool {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        for n in slice {
            match n {
                SNode::Stmts(run) => {
                    if run
                        .iter()
                        .any(|l| leaf_exprs(l).iter().any(|e| expr_uses_value(e, id)))
                    {
                        return true;
                    }
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    if expr_uses_value(cond, id) {
                        return true;
                    }
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::While { cond, body, .. } => {
                    if cond.as_ref().is_some_and(|c| expr_uses_value(c, id)) {
                        return true;
                    }
                    stack.push(body);
                }
                SNode::DoWhile { body, cond, .. } => {
                    if expr_uses_value(cond, id) {
                        return true;
                    }
                    stack.push(body);
                }
                SNode::Labeled { body, .. } | SNode::Block(body) => stack.push(body),
                SNode::ForOf { iter, body, .. } => {
                    if expr_uses_value(iter, id) {
                        return true;
                    }
                    stack.push(body);
                }
                SNode::ForIn { obj, body, .. } => {
                    if expr_uses_value(obj, id) {
                        return true;
                    }
                    stack.push(body);
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        stack.push(fin);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::Switch { disc, cases } => {
                    if expr_uses_value(disc, id) {
                        return true;
                    }
                    for c in cases.iter().rev() {
                        if c.tests.iter().any(|t| expr_uses_value(t, id)) {
                            return true;
                        }
                        stack.push(&c.body);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    false
}

/// Count temp references over the whole `SNode` tree, including all control
/// header expressions (`If.cond`, `While.cond`, `DoWhile.cond`, `ForOf.iter`,
/// `ForIn.obj`, `Switch.disc`, `SwitchCase.tests`), `Try.{body, catches, finally}`,
/// and `Leaf` expressions (`#87.1`, iterative with zero recursion).
pub(in crate::folds) fn count_temp_uses(nodes: &[SNode], uses: &mut BTreeMap<ValueId, usize>) {
    fn count_expr(root: &Expr, uses: &mut BTreeMap<ValueId, usize>) {
        let mut estack = vec![root];
        while let Some(e) = estack.pop() {
            if let Expr::Temp { value, .. } = e {
                *uses.entry(*value).or_insert(0) += 1;
            }
            estack.extend(expr_children(e));
        }
    }
    let mut nstack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = nstack.pop() {
        for n in slice {
            match n {
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        for e in leaf_exprs(l) {
                            count_expr(e, uses);
                        }
                    }
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    count_expr(cond, uses);
                    nstack.push(otherwise);
                    nstack.push(then);
                }
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        count_expr(c, uses);
                    }
                    nstack.push(body);
                }
                SNode::DoWhile { body, cond, .. } => {
                    count_expr(cond, uses);
                    nstack.push(body);
                }
                SNode::ForOf { iter, body, .. } => {
                    count_expr(iter, uses);
                    nstack.push(body);
                }
                SNode::ForIn { obj, body, .. } => {
                    count_expr(obj, uses);
                    nstack.push(body);
                }
                SNode::Labeled { body, .. } | SNode::Block(body) => nstack.push(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        nstack.push(fin);
                    }
                    for c in catches {
                        nstack.push(&c.body);
                    }
                    nstack.push(body);
                }
                SNode::Switch { disc, cases } => {
                    count_expr(disc, uses);
                    for c in cases {
                        for t in &c.tests {
                            count_expr(t, uses);
                        }
                        nstack.push(&c.body);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
}

/// Remove `Declare` leaves whose SSA value is in `dead` (callers prove
/// zero remaining uses first).
pub(in crate::folds) fn sweep_dead_decls(nodes: &mut [SNode], dead: &BTreeSet<ValueId>) {
    walk_stmts_runs_mut(nodes, |run| {
        run.retain(|l| {
            !matches!(
                l,
                Leaf::Raw(Stmt::Declare { value_id, .. }) if dead.contains(value_id)
            )
        });
    });
}

/// The expressions a leaf carries (for temp-use walks).
pub(crate) fn leaf_exprs(l: &Leaf) -> Vec<&Expr> {
    match l {
        Leaf::Raw(s) => match s {
            Stmt::Declare { value, .. } | Stmt::PhiAssign { value, .. } => vec![value],
            Stmt::Expr(e) => vec![e],
            Stmt::StoreProp { object, value, .. } => vec![object, value],
            Stmt::StoreIndex {
                object,
                index,
                value,
                ..
            } => vec![object, index, value],
            Stmt::StoreDyn {
                object, key, value, ..
            } => vec![object, key, value],
            Stmt::DefineMethod { object, func, .. } => vec![object, func],
            Stmt::StorePrivate { object, value, .. } => vec![object, value],
            Stmt::StoreSuper { key, value, .. } => {
                key.iter().chain(std::iter::once(value)).collect()
            }
            Stmt::LexStore { value, .. }
            | Stmt::GlobalStore { value, .. }
            | Stmt::ModuleStore { value, .. } => vec![value],
            Stmt::Throw(e) => vec![e],
            Stmt::Return(Some(e)) => vec![e],
            Stmt::CondBranch { cond, .. } => vec![cond],
            _ => Vec::new(),
        },
        Leaf::Destructure { obj, .. } => vec![obj],
        Leaf::Decl { value, .. } => value.iter().collect(),
        Leaf::Assign { value, .. } => vec![value],
    }
}
