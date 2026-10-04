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
//!    IR has no `Switch` op by design — ir-v0.2 §9 resolution 2).
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
//!     [`match_for_await_driver`] extends fold 3's iterator-loop
//!     recovery to the post-N70 driver shape — the header's folded
//!     dispatch await temp, the `next.call(it)` phi call, the
//!     break-routed `if (done) { TAIL; break } else { body; continue }`
//!     dispatch whose done arm absorbed the post-loop tail (re-homed
//!     AFTER the loop), and loop-carried bookkeeping phis collapsed to
//!     their invariant sources by substitution. The companion sweep
//!     [`sweep_dead_loop_exit_throws`] (N70 residual 2) removes the
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
    /// whole-node unreachability proof ([`sweep_dead_loop_exit_throws`]).
    pub dead_exit_throw: usize,
}

/// Run every fold over a structured body (recursive driver).
pub fn fold(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    fold_seq(nodes, stats);
}

fn fold_seq(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    for n in nodes.iter_mut() {
        fold_children(n, stats);
    }
    dissolve_rethrow_trys(nodes);
    // d-P17 (N70 residual 2): after dissolution the async machine
    // fold's dead loop-exit dispatch throw is a direct sibling of its
    // loop — sweep it when provably unreachable (before the loop
    // folds, while the header await temp the residue throws is still
    // visible).
    sweep_dead_loop_exit_throws(nodes, stats);
    fold_loops(nodes, stats);
    fold_single_pass_for_ins(nodes, stats);
    fold_switches(nodes, stats);
    fold_finally(nodes, stats);
}

/// Dissolve `try { X } catch (e) { throw e; }` wrappers — a semantic
/// no-op es2abc emits around protected entry sequences (probe-verified;
/// the handler is a bare rethrow).
fn dissolve_rethrow_trys(nodes: &mut Vec<SNode>) {
    let mut i = 0;
    while i < nodes.len() {
        let dissolve = match &nodes[i] {
            SNode::Try { body, catches, .. } => {
                !body.is_empty()
                    && catches.iter().all(|c| {
                        let binding = c.binding.clone().unwrap_or_default();
                        c.body.iter().all(|n| match n {
                            SNode::Stmts(leaves) => leaves.iter().all(|l| {
                                matches!(l, Leaf::Raw(Stmt::Throw(e)) if temp_name(e) == Some(binding.as_str()))
                                    || matches!(l, Leaf::Raw(Stmt::Unreachable))
                            }),
                            _ => false,
                        }) && !c.body.is_empty()
                    })
            }
            _ => false,
        };
        if dissolve {
            let SNode::Try { body, .. } = nodes.remove(i) else {
                unreachable!()
            };
            let mut replacement: Vec<SNode> = vec![SNode::Honest(
                "rethrow-only try/catch dissolved (semantic no-op)".to_string(),
            )];
            replacement.extend(body);
            nodes.splice(i..i, replacement);
            i += 1;
        } else {
            i += 1;
        }
    }
}

fn fold_children(n: &mut SNode, stats: &mut FoldStats) {
    match n {
        SNode::Stmts(leaves) => fold_leaves(leaves, stats),
        SNode::If {
            then, otherwise, ..
        } => {
            fold_seq(then, stats);
            fold_seq(otherwise, stats);
        }
        SNode::While { body, .. } | SNode::DoWhile { body, .. } | SNode::Labeled { body, .. } => {
            fold_seq(body, stats)
        }
        SNode::Try { body, catches, .. } => {
            fold_seq(body, stats);
            for c in catches {
                fold_seq(&mut c.body, stats);
            }
        }
        // unreachable: fold_children runs per-list strictly BEFORE the list
        // folds that create ForOf/ForIn/Switch nodes (folds.rs:200-213), and
        // no list is re-walked — c-COV diagnosis
        SNode::ForOf { body, .. } | SNode::ForIn { body, .. } => fold_seq(body, stats),
        SNode::Switch { cases, .. } => {
            for c in cases {
                fold_seq(&mut c.body, stats);
            }
        }
        SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
    }
}

// ── Shared matching helpers ──────────────────────────────────────────

/// The name a plain value-reference expression refers to (a Stage-A
/// temp, or an identifier — catch bindings print as [`Expr::Ident`]).
fn temp_name(e: &Expr) -> Option<&str> {
    match e {
        Expr::Temp { name, .. } | Expr::Ident(name) => Some(name),
        _ => None,
    }
}

/// The temp VALUE id an expression refers to.
fn temp_value(e: &Expr) -> Option<abcd_ir::ValueId> {
    match e {
        Expr::Temp { value, .. } => Some(*value),
        _ => None,
    }
}

/// Whether the expression mentions a temp with SSA value `vid`.
fn expr_uses_value(e: &Expr, vid: abcd_ir::ValueId) -> bool {
    temp_value(e) == Some(vid)
        || expr_children(e)
            .into_iter()
            .any(|c| expr_uses_value(c, vid))
}

/// Whether any leaf in the list mentions a temp named `name`.
fn leaves_use_name(leaves: &[Leaf], name: &str) -> bool {
    leaves.iter().any(|l| leaf_uses_name(l, name))
}

fn leaf_uses_name(l: &Leaf, name: &str) -> bool {
    match l {
        Leaf::Raw(s) => stmt_uses_name(s, name),
        Leaf::Destructure { obj, .. } => expr_uses_name(obj, name),
        Leaf::Decl { value, .. } => value.as_ref().is_some_and(|v| expr_uses_name(v, name)),
        Leaf::Assign { value, target } => target == name || expr_uses_name(value, name),
    }
}

fn stmt_uses_name(s: &Stmt, name: &str) -> bool {
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

/// Whether an expression mentions a temp/ident with `name`.
fn expr_uses_name(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Temp { name: n, .. } | Expr::Ident(n) => n == name,
        _ => expr_children(e)
            .into_iter()
            .any(|c| expr_uses_name(c, name)),
    }
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
fn strip_cond(mut e: &Expr) -> &Expr {
    loop {
        match e {
            Expr::Unary {
                op:
                    abcd_ir::op::UnOp::IsTrue
                    | abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => e = operand,
            _ => return e,
        }
    }
}

// ── Fold 1: literal builders ─────────────────────────────────────────

fn fold_leaves(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    fold_rest_destructure(leaves, stats);
    fold_literal_builders(leaves, stats);
}

fn fold_literal_builders(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < leaves.len() {
        let (vid, is_array) = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                value: Expr::ObjectLit { .. },
                value_id,
                ..
            }) => (*value_id, false),
            Leaf::Raw(Stmt::Declare {
                value: Expr::ArrayLit { .. },
                value_id,
                ..
            }) => (*value_id, true),
            _ => {
                i += 1;
                continue;
            }
        };
        // Absorb the consecutive builder sequence at i+1…
        // N74-W4: the array shape's own element count seeds the
        // contiguity index — a store to index N is absorbable only when
        // N is exactly the next slot (a gap would silently drop the
        // hole and shift every later element left: test262 `[, 1, 2]`
        // decompiled to `[1, 2]`).
        let shape_len = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                value: Expr::ArrayLit { elements },
                ..
            }) => elements.len() as u64,
            _ => 0,
        };
        let mut absorbed: Vec<Absorb> = Vec::new();
        let mut absorbed_idx: Vec<usize> = Vec::new();
        let mut skipped_idx: Vec<usize> = Vec::new();
        // N74-W4: pure-literal declares interleaved in the builder
        // sequence (the computed-key temporaries of an accessor
        // definition) do not end it — they are RE-EMITTED above the
        // folded declaration (pure, so the reorder is free).
        let mut skipped: Vec<Leaf> = Vec::new();
        let mut j = i + 1;
        while j < leaves.len() {
            match absorb_one(&leaves[j], vid, is_array, &absorbed, shape_len) {
                Some(a) => {
                    absorbed.push(a);
                    absorbed_idx.push(j);
                    j += 1;
                }
                // N74-W4: a declare interleaved in the builder sequence
                // (an accessor's computed-key temporary, possibly a
                // call — key evaluation order inside the literal matches
                // the original statement order) does not end the
                // sequence; single-use temps inline into the entries at
                // rebuild, unused pure ones drop.
                None if matches!(&leaves[j], Leaf::Raw(Stmt::Declare { .. })) => {
                    skipped.push(leaves[j].clone());
                    skipped_idx.push(j);
                    j += 1;
                }
                None => break,
            }
        }
        if absorbed.is_empty() {
            i += 1;
            continue;
        }
        // N74-W4: resolve the skipped interleaved declares BEFORE
        // rebuilding: a temp used exactly ONCE across the absorbed
        // entries (or another skipped declare's value) inlines at that
        // use — inside the literal the computed-key evaluation order is
        // the original statement order; an unused pure-literal declare
        // drops; any other shape re-seats ABOVE the folded declaration.
        let mut bail = false;
        {
            // (vid, value, keep?) per skipped declare.
            let mut skip_vals: Vec<(abcd_ir::ValueId, Expr, bool)> = Vec::new();
            for leaf in &skipped {
                let Leaf::Raw(Stmt::Declare {
                    value, value_id, ..
                }) = leaf
                else {
                    unreachable!()
                };
                skip_vals.push((*value_id, value.clone(), true));
            }
            let count_uses =
                |vid: abcd_ir::ValueId,
                 absorbed: &[Absorb],
                 skip_vals: &[(abcd_ir::ValueId, Expr, bool)]| {
                    let mut n = 0usize;
                    for a in absorbed {
                        for e in absorb_exprs(a) {
                            n += expr_count_value(e, vid);
                        }
                    }
                    for (_, v, _) in skip_vals {
                        n += expr_count_value(v, vid);
                    }
                    n
                };
            let mut inline: Vec<(abcd_ir::ValueId, Expr)> = Vec::new();
            for k in 0..skip_vals.len() {
                let (vid, value, _) = &skip_vals[k];
                let (vid, is_lit, value) = (*vid, matches!(value, Expr::Lit(_)), value.clone());
                match count_uses(vid, &absorbed, &skip_vals) {
                    0 if is_lit => skip_vals[k].2 = false, // dead pure: drop
                    1 => {
                        inline.push((vid, value));
                        skip_vals[k].2 = false;
                    }
                    // Multi-use or used elsewhere: reordering the
                    // declare is unprovable — bail the WHOLE fold
                    // (nothing is mutated yet).
                    _ => {
                        bail = true;
                    }
                }
            }
            // Inline in decision order: an earlier inline may feed a
            // later one (temp chains), so substitute into the later
            // inline values too.
            for pos in 0..inline.len() {
                let (vid, value) = inline[pos].clone();
                for later in inline.iter_mut().skip(pos + 1) {
                    subst_temp_in_expr(&mut later.1, vid, &value);
                }
                for (_, v, _) in skip_vals.iter_mut() {
                    subst_temp_in_expr(v, vid, &value);
                }
                for a in absorbed.iter_mut() {
                    for e in absorb_exprs_mut(a) {
                        subst_temp_in_expr(e, vid, &value);
                    }
                }
            }
            if bail {
                i += 1;
                continue;
            }
        }
        if is_array {
            stats.array_lit += 1;
        } else {
            stats.object_lit += 1;
        }
        let new_value = match leaves.remove(i) {
            Leaf::Raw(Stmt::Declare {
                name,
                mutable,
                value,
                value_id,
            }) => {
                let folded = match value {
                    Expr::ObjectLit { entries } => {
                        let mut out: Vec<ObjEntry> = entries
                            .into_iter()
                            .map(|(k, v)| ObjEntry::KeyValue(k, Expr::Lit(v)))
                            .collect();
                        for a in absorbed {
                            match a {
                                Absorb::ObjKV(k, v) => out.push(ObjEntry::KeyValue(k, v)),
                                Absorb::ObjComputed(k, v) => out.push(ObjEntry::Computed(k, v)),
                                Absorb::ObjSpread(s) => out.push(ObjEntry::Spread(s)),
                                Absorb::ObjProto(p) => out.push(ObjEntry::Proto(p)),
                                Absorb::ObjMethod(n, f) => out.push(ObjEntry::Method(n, f)),
                                Absorb::ObjAccessors {
                                    key,
                                    getter,
                                    setter,
                                } => {
                                    let k = match key {
                                        Expr::Lit(Lit::String(s)) => crate::expr::ObjKey::Name(s),
                                        other => crate::expr::ObjKey::Computed(Box::new(other)),
                                    };
                                    if let Some(g) = getter {
                                        out.push(ObjEntry::Getter(k.clone(), g));
                                    }
                                    if let Some(st) = setter {
                                        out.push(ObjEntry::Setter(k, st));
                                    }
                                }
                                Absorb::ArrItem(_) | Absorb::ArrSpread(_) => {
                                    unreachable!("object fold absorbed an array entry")
                                }
                            }
                        }
                        Expr::ObjectBuild { entries: out }
                    }
                    Expr::ArrayLit { elements } => {
                        let mut out: Vec<ArrayElem> = elements
                            .into_iter()
                            .map(|e| ArrayElem::Item(Expr::Lit(e)))
                            .collect();
                        for a in absorbed {
                            match a {
                                Absorb::ArrItem(v) => out.push(ArrayElem::Item(v)),
                                Absorb::ArrSpread(s) => out.push(ArrayElem::Spread(s)),
                                _ => unreachable!("array fold absorbed an object entry"),
                            }
                        }
                        Expr::ArrayBuild { elements: out }
                    }
                    _ => unreachable!("filtered above"),
                };
                Leaf::Raw(Stmt::Declare {
                    name,
                    mutable,
                    value: folded,
                    value_id,
                })
            }
            other => other,
        };
        // Remove the absorbed AND skipped statements by index
        // (descending; the `leaves.remove(i)` above shifted everything
        // past `i` down by one), then re-seat the skipped declares that
        // survived immediately above the folded declaration.
        let mut gone: Vec<usize> = absorbed_idx
            .iter()
            .chain(skipped_idx.iter())
            .map(|x| x - 1)
            .collect();
        gone.sort_unstable_by(|a, b| b.cmp(a));
        for idx in gone {
            leaves.remove(idx);
        }
        leaves.insert(i, new_value);
        i += 1;
    }
}

/// One absorbed builder statement.
enum Absorb {
    ObjKV(Lit, Expr),
    ObjComputed(Expr, Expr),
    ObjSpread(Expr),
    ObjProto(Expr),
    ObjMethod(String, Expr),
    /// A `DefineGetterSetterByValue` against the object being built
    /// (N74-W4) — key + optional getter/setter closures. Folding it
    /// into the literal is BOTH more idiomatic and the only form whose
    /// accessors carry a [[HomeObject]] (super-using bodies) — and the
    /// literal's accessors are enumerable like the source's (the
    /// defineProperty emission's `enumerable: false` default was not).
    ObjAccessors {
        key: Expr,
        getter: Option<Expr>,
        setter: Option<Expr>,
    },
    ArrItem(Expr),
    ArrSpread(Expr),
}

/// The expression positions of an absorbed builder statement
/// (immutable — the use census).
fn absorb_exprs(a: &Absorb) -> Vec<&Expr> {
    match a {
        Absorb::ObjKV(_, v) => vec![v],
        Absorb::ObjComputed(k, v) => vec![k, v],
        Absorb::ObjSpread(s) | Absorb::ObjProto(s) => vec![s],
        Absorb::ObjMethod(_, f) => vec![f],
        Absorb::ObjAccessors {
            key,
            getter,
            setter,
        } => {
            let mut out = vec![key];
            out.extend(getter.iter());
            out.extend(setter.iter());
            out
        }
        Absorb::ArrItem(v) | Absorb::ArrSpread(v) => vec![v],
    }
}

/// The mutable counterpart of [`absorb_exprs`] (the inline rewrite).
fn absorb_exprs_mut(a: &mut Absorb) -> Vec<&mut Expr> {
    match a {
        Absorb::ObjKV(_, v) => vec![v],
        Absorb::ObjComputed(k, v) => vec![k, v],
        Absorb::ObjSpread(s) | Absorb::ObjProto(s) => vec![s],
        Absorb::ObjMethod(_, f) => vec![f],
        Absorb::ObjAccessors {
            key,
            getter,
            setter,
        } => {
            let mut out = vec![key];
            out.extend(getter.iter_mut());
            out.extend(setter.iter_mut());
            out
        }
        Absorb::ArrItem(v) | Absorb::ArrSpread(v) => vec![v],
    }
}

/// How often an expression references a temp by SSA value.
fn expr_count_value(e: &Expr, vid: abcd_ir::ValueId) -> usize {
    let mut n = usize::from(expr_uses_value(e, vid) && temp_value(e) == Some(vid));
    for c in expr_children(e) {
        n += expr_count_value(c, vid);
    }
    n
}

/// Whether leaf `l` is a builder statement targeting temp `vid` that
/// can be absorbed (self-reference-free). `shape_len` is the array
/// shape's own element count (0 for objects) — the array absorb index
/// is checked against `shape_len + <absorbed items>` exactly.
fn absorb_one(
    l: &Leaf,
    vid: abcd_ir::ValueId,
    is_array: bool,
    so_far: &[Absorb],
    shape_len: u64,
) -> Option<Absorb> {
    let is_target = |e: &Expr| temp_value(e) == Some(vid);
    let clean = |e: &Expr| !expr_uses_value(e, vid);
    match l {
        Leaf::Raw(Stmt::StoreProp {
            object,
            name,
            value,
            own: true,
            ..
        }) if !is_array && is_target(object) && clean(value) => {
            Some(Absorb::ObjKV(Lit::String(name.clone()), value.clone()))
        }
        Leaf::Raw(Stmt::StoreDyn {
            object,
            key,
            value,
            own: true,
        }) if !is_array && is_target(object) && clean(key) && clean(value) => Some(match key {
            Expr::Lit(l @ (Lit::String(_) | Lit::Number(_))) => {
                Absorb::ObjKV(l.clone(), value.clone())
            }
            _ => Absorb::ObjComputed(key.clone(), value.clone()),
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object,
            index,
            value,
            own,
        }) if is_target(object) && clean(index) && clean(value) => {
            if is_array {
                // Strict contiguity (N74-W4): the store's integer index
                // must be EXACTLY the next slot — shape elements plus
                // already-absorbed items. Anything else (a hole gap, an
                // out-of-order store) stays a statement, which preserves
                // the sparse semantics the literal form would destroy.
                // A spread makes the running index unknowable — absorb
                // no items after one.
                let base = match &index {
                    Expr::Lit(Lit::Number(bits)) => {
                        let v = f64::from_bits(*bits);
                        (v.fract() == 0.0 && v >= 0.0).then_some(v as u64)
                    }
                    _ => None,
                };
                let next = if so_far.iter().any(|a| matches!(a, Absorb::ArrSpread(_))) {
                    None
                } else {
                    Some(
                        shape_len
                            + so_far
                                .iter()
                                .filter(|a| matches!(a, Absorb::ArrItem(_)))
                                .count() as u64,
                    )
                };
                match base {
                    Some(idx) if *own && Some(idx) == next => Some(Absorb::ArrItem(value.clone())),
                    _ => None,
                }
            } else if *own {
                match index {
                    Expr::Lit(l @ (Lit::String(_) | Lit::Number(_))) => {
                        Some(Absorb::ObjKV(l.clone(), value.clone()))
                    }
                    _ => Some(Absorb::ObjComputed(index.clone(), value.clone())),
                }
            } else {
                None
            }
        }
        Leaf::Raw(Stmt::Expr(Expr::CopyDataProps { dst, src }))
            if !is_array && is_target(dst) && clean(src) =>
        {
            Some(Absorb::ObjSpread(src.as_ref().clone()))
        }
        Leaf::Raw(Stmt::Expr(Expr::SetObjectWithProto { obj, proto }))
            if !is_array && is_target(obj) && clean(proto) =>
        {
            Some(Absorb::ObjProto(proto.as_ref().clone()))
        }
        Leaf::Raw(Stmt::Expr(Expr::ArraySpread { dst, src, .. }))
            if is_array && is_target(dst) && clean(src) =>
        {
            Some(Absorb::ArrSpread(src.as_ref().clone()))
        }
        Leaf::Raw(Stmt::DefineMethod {
            object, name, func, ..
        }) if !is_array && is_target(object) && clean(func) => {
            Some(Absorb::ObjMethod(name.clone(), func.clone()))
        }
        // Accessor definition against the object being built. The
        // getter/setter slots must be closures or the `undefined`
        // absence marker (the recover.rs undef-through resolution).
        Leaf::Raw(Stmt::Expr(Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        })) if !is_array
            && is_target(obj)
            && clean(key)
            && clean(getter)
            && clean(setter)
            && matches!(
                getter.as_ref(),
                Expr::Closure { .. } | Expr::Lit(Lit::Undefined)
            )
            && matches!(
                setter.as_ref(),
                Expr::Closure { .. } | Expr::Lit(Lit::Undefined)
            ) =>
        {
            let getter = match getter.as_ref() {
                Expr::Lit(Lit::Undefined) => None,
                g => Some(g.clone()),
            };
            let setter = match setter.as_ref() {
                Expr::Lit(Lit::Undefined) => None,
                st => Some(st.clone()),
            };
            if getter.is_none() && setter.is_none() {
                return None;
            }
            Some(Absorb::ObjAccessors {
                key: key.as_ref().clone(),
                getter,
                setter,
            })
        }
        _ => None,
    }
}

// ── Fold 2: rest destructuring ───────────────────────────────────────

fn fold_rest_destructure(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < leaves.len() {
        let (rest_name, obj, keys) = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                name,
                value: Expr::RestObject { obj, excluded },
                ..
            }) => {
                let keys: Option<Vec<String>> = excluded
                    .iter()
                    .map(|k| match k {
                        Expr::Lit(Lit::String(s)) => Some(s.clone()),
                        _ => None,
                    })
                    .collect();
                match keys {
                    Some(keys) if !keys.is_empty() => (name.clone(), obj.as_ref().clone(), keys),
                    _ => {
                        i += 1;
                        continue;
                    }
                }
            }
            _ => {
                i += 1;
                continue;
            }
        };
        // Find one sibling declare per excluded key: `const t = obj.k`
        // (or `obj["k"]`) with a structurally equal object expression.
        let mut found: Vec<(usize, String, String)> = Vec::new(); // (leaf idx, key, target)
        let mut ok = true;
        for key in &keys {
            let hit = leaves.iter().enumerate().find(|(idx, l)| {
                *idx != i
                    && matches!(l, Leaf::Raw(Stmt::Declare { value, .. }) if key_load_target(value, &obj) == Some(key))
            });
            match hit {
                Some((idx, Leaf::Raw(Stmt::Declare { name, .. }))) => {
                    found.push((idx, key.clone(), name.clone()))
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            i += 1;
            continue;
        }
        stats.rest += 1;
        let pairs: Vec<(String, String)> = found
            .iter()
            .map(|(_, k, t)| (k.clone(), t.clone()))
            .collect();
        let mut drop: Vec<usize> = found.iter().map(|(idx, _, _)| *idx).collect();
        drop.sort_unstable_by(|a, b| b.cmp(a));
        for d in drop {
            leaves.remove(d);
            if d < i {
                i -= 1;
            }
        }
        leaves[i] = Leaf::Destructure {
            obj,
            keys: pairs,
            rest: rest_name,
        };
        i += 1;
    }
}

/// The key a `obj.k` / `obj["k"]` load extracts, when `value` is such
/// a load on `obj`.
fn key_load_target<'v>(value: &'v Expr, obj: &Expr) -> Option<&'v String> {
    match value {
        Expr::PropName { object, name, .. } if object.as_ref() == obj => Some(name),
        Expr::PropDyn { object, key } if object.as_ref() == obj => match key.as_ref() {
            Expr::Lit(Lit::String(s)) => Some(s),
            _ => None,
        },
        Expr::PropIndex { object, index } if object.as_ref() == obj => match index.as_ref() {
            Expr::Lit(Lit::String(s)) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

// ── d-P17 (N70 residual 2): dead loop-exit dispatch throw sweep ────
//
// The async machine fold's break-routed dispatch (N70: a loop-internal
// await whose `mode == THROW` arm exits the loop) leaves the after-loop
// `throw <resume temp>` block in place — d-P16 kept it conservatively.
// Post-fold it is dead: the folded `await` rejects inline, so the break
// that routed to the exit block is gone. This pass removes the residue,
// but only under a whole-node unreachability proof; any doubt keeps it.

/// Termination/divergence facts for the unreachability proof.
struct SeqFlow {
    /// A statically LIVE unlabeled `break` exists (one that would exit
    /// the loop whose body is being analyzed — nested loops'/switches'
    /// breaks are inner-scoped and never reported).
    live_break: bool,
    /// Control can never pass the end of the sequence.
    diverges: bool,
}

const FLOW_FALLTHROUGH: SeqFlow = SeqFlow {
    live_break: false,
    diverges: false,
};

/// Sequence flow: nodes after a diverging node are statically dead —
/// their breaks do not count as live.
fn seq_flow(nodes: &[SNode]) -> SeqFlow {
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

fn node_flow(n: &SNode) -> SeqFlow {
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
fn subtree_has_labeled_jump(nodes: &[SNode]) -> bool {
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
fn sweep_dead_loop_exit_throws(nodes: &mut [SNode], stats: &mut FoldStats) {
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
fn residue_match(nodes: &[SNode], i: usize, body: &[SNode]) -> Option<usize> {
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
struct LoopFold {
    is_await: bool,
    is_in: bool,
    /// The iterated object.
    iter: Expr,
    /// Trailing leaves of the merged pre-loop run to consume.
    pre_cut: usize,
    /// The header phi names (plumbing).
    phi_names: Vec<String>,
    /// The `res = next()` temp (for-of only).
    res_name: Option<String>,
    /// The `done` temp (for-of only).
    done_name: Option<String>,
    /// Further internal temps (`it`, `next`, the for-in header phis).
    extra_internals: Vec<String>,
    /// Extra header-phi wiring to hoist ABOVE the folded loop (for-in
    /// only, N74): `let`-less `var` decl + the pre-loop assign of each
    /// loop-invariant pass-through phi, emitted as one `Stmts` node
    /// immediately before the `ForIn`.
    hoisted: Vec<Leaf>,
}

/// Normalize the two loop-test emission shapes to `(test, body)`:
/// `while (test) { body }` directly, and the sound d-P4 form
/// `while (true) { wiring…; if (test) break; body }` (emitted when the
/// loop header carries statements the condition reads — the clean form
/// would reference them before their declaration). The `break` node is
/// consumed by the normalization.
fn normalize_loop_test(body: &[SNode]) -> Option<(Expr, Vec<SNode>)> {
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

fn fold_loops(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
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
fn fold_single_pass_for_ins(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
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
struct SinglePassForIn {
    /// Index of the `Stmts` run whose LAST leaf is the
    /// `GetPropIterator` phi-assign (the leaf is consumed).
    assign: usize,
    /// The key binding (the `NextPropName` result temp).
    binding: String,
    /// The enumerated object.
    obj: Expr,
    /// The single-pass body (the non-taken exit arm of the test).
    body: Vec<SNode>,
}

/// Match the degenerate for-in with the header `Stmts` at index `i`:
/// `[PhiDecl it, const k = NextPropName(it)]` at `i`, the
/// `it = GetPropIterator(obj)` phi-assign as the LAST leaf of the
/// nearest previous non-`Honest` `Stmts` run, and the
/// `if (k == undefined) {} else { body }` exit test at `i + 1`.
fn match_single_pass_for_in(nodes: &[SNode], i: usize) -> Option<SinglePassForIn> {
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
fn subtree_has_continue(nodes: &[SNode]) -> bool {
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
fn merged_pre_leaves(nodes: &[SNode], i: usize) -> Vec<Leaf> {
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
fn trim_pre_leaves(nodes: &mut Vec<SNode>, i: usize, cut: usize) -> usize {
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
fn match_for_of(pre: &[Leaf], wcond: &Expr, body: &[SNode]) -> Option<LoopFold> {
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
fn match_for_in(pre: &[Leaf], wcond: &Expr, body: &[SNode]) -> Option<LoopFold> {
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
fn rebuild_loop_body(body: &[SNode], folded: &LoopFold) -> Option<(String, Vec<SNode>)> {
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
    // (plain or cleanup-try-wrapped).
    let mut binding: Option<String> = None;
    let mut splice_try = false;
    match out.first_mut() {
        Some(SNode::Stmts(leaves)) => {
            if let Some(b) = take_value_declare(leaves, &res_name) {
                binding = Some(b);
            }
        }
        Some(SNode::Try {
            body: tbody,
            catches,
            ..
        }) => {
            // The try body may lead with honesty comments (cut-boundary
            // placement) — find the first `Stmts` node.
            for n in tbody.iter_mut() {
                if let SNode::Stmts(leaves) = n
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
                splice_try = true;
            }
        }
        _ => {}
    }
    let binding = binding?;
    if splice_try {
        // Replace the cleanup try with its body (loudly).
        let Some(SNode::Try { body: inner, .. }) = out.first().cloned() else {
            unreachable!()
        };
        let mut replacement: Vec<SNode> = vec![SNode::Honest(
            "iterator-cleanup try/catch folded into for-of's implicit cleanup (ECMA-262 §14.7.5)"
                .to_string(),
        )];
        replacement.extend(inner);
        out.splice(0..1, replacement);
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
struct DriverFold {
    /// The iterated expression.
    iter: Expr,
    /// The iteration binding.
    binding: String,
    /// The rebuilt loop body.
    body: Vec<SNode>,
    /// The done-arm's absorbed post-loop tail (re-homed after the loop).
    tail: Vec<SNode>,
    /// Trailing leaves of the gathered pre-run to consume.
    pre_cut: usize,
}

/// The adjacent statement leaves immediately before index `i`,
/// skipping honesty comments and empty runs (the driver's dissolved
/// try wrappers sit between the iterator setup and the loop).
fn gather_driver_pre_leaves(nodes: &[SNode], i: usize) -> Vec<Leaf> {
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
fn trim_driver_pre_leaves(nodes: &mut Vec<SNode>, i: usize, cut: usize) -> usize {
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
fn match_for_await_driver(nodes: &[SNode], i: usize) -> Option<DriverFold> {
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
    // cleanup-try-wrapped (leading honesty comments tolerated).
    let mut binding: Option<String> = None;
    let mut splice_idx: Option<usize> = None;
    for (bi, n) in body_nodes.iter_mut().enumerate() {
        match n {
            SNode::Honest(_) => continue,
            SNode::Stmts(leaves) => {
                binding = take_value_declare(leaves, &await_name);
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
fn apply_for_await_driver(
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
fn subst_temp_in_expr(e: &mut Expr, vid: ValueId, replacement: &Expr) {
    if temp_value(e) == Some(vid) {
        *e = replacement.clone();
        return;
    }
    for c in expr_children_mut(e) {
        subst_temp_in_expr(c, vid, replacement);
    }
}

fn subst_temp_in_leaf(l: &mut Leaf, vid: ValueId, replacement: &Expr) {
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

fn subst_temp_in_nodes(nodes: &mut [SNode], vid: ValueId, replacement: &Expr) {
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
fn nodes_declare_or_assign(nodes: &[SNode], name: &str) -> bool {
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
fn take_value_declare(leaves: &mut Vec<Leaf>, res_name: &str) -> Option<String> {
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
fn drop_self_assign_tail(out: &mut Vec<SNode>) {
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
fn elim_internal_copy_phis(out: &mut Vec<SNode>, roots: &BTreeMap<String, Expr>) {
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
fn strip_internal_phi_plumbing(
    out: &mut Vec<SNode>,
    roots: &BTreeSet<&str>,
    copies: &BTreeSet<&str>,
) {
    out.retain_mut(|n| match n {
        SNode::Stmts(run) => {
            run.retain(|l| match l {
                Leaf::Raw(Stmt::PhiAssign { target, value, .. }) => {
                    !copies.contains(target.as_str())
                        && !(roots.contains(target.as_str())
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
fn nodes_use_any(nodes: &[SNode], names: &[String]) -> bool {
    nodes.iter().any(|n| node_uses_any(n, names))
}

fn node_uses_any(n: &SNode, names: &[String]) -> bool {
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
fn cleanup_handlers_ok(catches: &[crate::structure::CatchClause]) -> bool {
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

fn walk_cleanup(
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
fn collect_aliases(nodes: &[SNode], aliases: &mut Vec<String>, grew: &mut bool) {
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
fn expr_has_return_load(e: &Expr) -> bool {
    match e {
        Expr::PropDyn { key, .. } | Expr::PropIndex { index: key, .. } => {
            matches!(key.as_ref(), Expr::Lit(Lit::String(s)) if s == "return")
                || expr_children(e).into_iter().any(expr_has_return_load)
        }
        Expr::PropName { name, .. } if name == "return" => true,
        _ => expr_children(e).into_iter().any(expr_has_return_load),
    }
}

// ── Fold 5: switch re-detection ──────────────────────────────────────

fn fold_switches(nodes: &mut [SNode], stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let Some((disc, cases)) = match_switch_chain(&nodes[i]) else {
            i += 1;
            continue;
        };
        if cases.len() < 2 {
            i += 1;
            continue;
        }
        stats.switch += 1;
        nodes[i] = SNode::Switch { disc, cases };
        i += 1;
    }
}

/// Match an `if (x === lit) {…} else if (x === lit) {…} …` chain.
fn match_switch_chain(n: &SNode) -> Option<(Expr, Vec<SwitchCase>)> {
    let SNode::If {
        cond,
        then,
        otherwise,
    } = n
    else {
        return None;
    };
    // Polarity-aware: a `isfalse(x === lit)` / `!(x === lit)` test puts
    // the case body in the FALSE arm and the chain continuation in the
    // true arm (dream gate: the polarity-blind form swapped the arms of
    // `x ?? y` — local/optional-chain).
    let (disc, lit, positive) = switch_test(cond)?;
    let (case_body, cont) = if positive {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    // An unlabeled `break` in a case arm changes meaning under the
    // fold: before the fold it exits the enclosing LOOP; inside a
    // `switch` it would exit the switch (dream gate:
    // opt-try-catch-func/test-nested-try-catch hung —
    // `case 5.0: break` fell back into the loop, d-P5). The fold is
    // cosmetic; keep the if-chain instead. (Labeled breaks name their
    // target and `continue` ignores switches, so both are safe.)
    if arm_has_loop_break(case_body) {
        return None;
    }
    let mut cases = vec![SwitchCase {
        tests: vec![lit],
        body: with_break(case_body.clone()),
    }];
    let mut rest = cont;
    loop {
        match rest.as_slice() {
            [
                SNode::If {
                    cond: c2,
                    then: t2,
                    otherwise: o2,
                },
            ] => {
                let (d2, lit2, pos2) = switch_test(c2)?;
                if d2 != disc {
                    return None;
                }
                let (body2, cont2) = if pos2 { (t2, o2) } else { (o2, t2) };
                if arm_has_loop_break(body2) {
                    return None;
                }
                cases.push(SwitchCase {
                    tests: vec![lit2],
                    body: with_break(body2.clone()),
                });
                rest = cont2;
            }
            [] => break,
            // A nested switch on the SAME discriminant (a chain folded
            // bottom-up, or the state-machine dispatch chain) flattens
            // into this one's cases.
            [
                SNode::Switch {
                    disc: d2,
                    cases: c2,
                },
            ] if *d2 == disc => {
                cases.extend(c2.iter().cloned());
                break;
            }
            other => {
                if arm_has_loop_break(other) {
                    return None;
                }
                cases.push(SwitchCase {
                    tests: vec![],
                    body: other.to_vec(),
                });
                break;
            }
        }
    }
    Some((disc, cases))
}

/// Whether an arm of a foldable if-chain contains an unlabeled `break`
/// at case-arm depth — a loop exit that a `switch` wrapper would
/// reinterpret as a switch exit. Nested loops/switches intercept their
/// own breaks, so the walk does not descend into them.
fn arm_has_loop_break(nodes: &[SNode]) -> bool {
    nodes.iter().any(|n| match n {
        SNode::Break { label: None } => true,
        SNode::If {
            then, otherwise, ..
        } => arm_has_loop_break(then) || arm_has_loop_break(otherwise),
        SNode::Labeled { body, .. } => arm_has_loop_break(body),
        SNode::Try { body, catches, .. } => {
            arm_has_loop_break(body) || catches.iter().any(|c| arm_has_loop_break(&c.body))
        }
        SNode::While { .. }
        | SNode::DoWhile { .. }
        | SNode::ForOf { .. }
        | SNode::ForIn { .. }
        | SNode::Switch { .. } => false,
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => false,
    })
}

/// The `(discriminant, case-literal)` of a POSITIVE `x === lit`
/// condition. Only the truth-preserving `istrue` wrapper may be
/// stripped — `isfalse`/`!` invert the arms and a `case lit:` body
/// would run on the WRONG polarity (d-P4 dream gate: `x ?? y`'s
/// `isfalse(x === undefined)` chain folded into a switch with the
/// undefined/default arms swapped — local/optional-chain).
fn switch_test(cond: &Expr) -> Option<(Expr, Expr, bool)> {
    let mut c = cond;
    let mut positive = true;
    loop {
        match c {
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsTrue,
                operand,
            } => c = operand,
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsFalse | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => {
                positive = !positive;
                c = operand;
            }
            _ => break,
        }
    }
    match c {
        Expr::Compare {
            op: abcd_ir::op::CmpOp::StrictEq | abcd_ir::op::CmpOp::Eq,
            left,
            right,
        } => {
            let is_disc = |e: &Expr| matches!(e, Expr::Temp { .. } | Expr::Ident(_));
            if is_disc(left) && matches!(right.as_ref(), Expr::Lit(_)) {
                Some((left.as_ref().clone(), right.as_ref().clone(), positive))
            } else if is_disc(right) && matches!(left.as_ref(), Expr::Lit(_)) {
                Some((right.as_ref().clone(), left.as_ref().clone(), positive))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Append a `break` to a case body unless it already ends terminal.
fn with_break(mut body: Vec<SNode>) -> Vec<SNode> {
    let terminal = body.last().is_some_and(crate::structure::is_terminal_node);
    if !terminal {
        body.push(SNode::Break { label: None });
    }
    body
}

// ── d-P8: the finally fold (design/decompile.md §4.2 item 5) ───────
//
// es2abc has no `finally` marker: it duplicates the finally body onto
// every exit path of the protected construct and registers an
// exception DISPATCH handler that runs the finally body once and
// rethrows. d-P3's try machinery emits that faithfully but verbosely:
// a handler-protecting outer `try` (the "finally idiom" note) whose
// catch is a phi dispatch — a switch on a phi temp whose
// `case undefined:` arm holds the finally body, followed by a
// rethrow-unless-hole conditional — plus the finally body inlined
// before every `return`/exiting `break`/`continue` and on the
// normal-completion fall-through path.
//
// This fold recognizes that exact shape and re-factors it into
// `try { … } catch … finally { F }`. The equivalence is the JS
// finally completion semantics: F runs on normal completion, before
// any return/break/continue completes, and on exceptional exit —
// exactly the paths es2abc duplicated F onto. The dispatch's
// `default:` arm (skip F when the exception came from F itself)
// matches the finally clause's run-F-once semantics.
//
// Every check is conservative: any shape doubt keeps the duplicated
// form with its honesty notes (the fallback-honesty rule).

/// A flattened statement-list token for the finally fold: one leaf, or
/// one whole nested node (nested nodes never appear in a foldable
/// finally template, so they never match — conservatism for free).
#[derive(Clone, Debug, PartialEq)]
enum FTok {
    /// A single statement.
    Leaf(Leaf),
    /// A nested structured node.
    Node(SNode),
}

/// Flatten a statement list to tokens (a `Stmts` run becomes one token
/// per leaf; any other node is one opaque token).
fn ft_flatten(nodes: &[SNode]) -> Vec<FTok> {
    let mut out = Vec::new();
    for n in nodes {
        match n {
            SNode::Stmts(ls) => out.extend(ls.iter().cloned().map(FTok::Leaf)),
            other => out.push(FTok::Node(other.clone())),
        }
    }
    out
}

/// Regroup tokens into a statement list (consecutive leaves share one
/// `Stmts` node; empty runs are dropped). Semantics-neutral: emission
/// iterates leaves regardless of grouping.
fn ft_regroup(toks: Vec<FTok>) -> Vec<SNode> {
    let mut out: Vec<SNode> = Vec::new();
    let mut run: Vec<Leaf> = Vec::new();
    for t in toks {
        match t {
            FTok::Leaf(l) => run.push(l),
            FTok::Node(n) => {
                if !run.is_empty() {
                    out.push(SNode::Stmts(std::mem::take(&mut run)));
                }
                out.push(n);
            }
        }
    }
    if !run.is_empty() {
        out.push(SNode::Stmts(run));
    }
    out
}

/// The definition-site names of a token run (first-occurrence order) —
/// the names each duplicated finally copy binds for itself (the
/// legalizer disambiguates the copies: `print$1`/`print$2`/…).
fn ftok_def_names(toks: &[FTok]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut push = |n: &String| {
        if !out.contains(n) {
            out.push(n.clone());
        }
    };
    for t in toks {
        let FTok::Leaf(l) = t else { continue };
        match l {
            Leaf::Raw(Stmt::Declare { name, .. })
            | Leaf::Raw(Stmt::PhiDecl { name, .. })
            | Leaf::Raw(Stmt::CatchBind { name })
            | Leaf::Decl { name, .. } => push(name),
            Leaf::Destructure { keys, rest, .. } => {
                for (_, target) in keys {
                    push(target);
                }
                push(rest);
            }
            _ => {}
        }
    }
    out
}

/// Rename a temp/ident occurrence when it is one of the run's own
/// definition-site names.
fn canon_name(name: &mut String, map: &std::collections::HashMap<String, String>) {
    if let Some(r) = map.get(name) {
        *name = r.clone();
    }
}

/// Mutable child walk mirroring [`expr_children`].
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

/// Alpha-rename a run-local name inside an expression and erase the
/// SSA provenance of temp references (copies sit at different SSA
/// values; their NAMES carry the identity).
fn canon_expr(e: &mut Expr, map: &std::collections::HashMap<String, String>) {
    match e {
        Expr::Temp { value, name } => {
            canon_name(name, map);
            *value = abcd_ir::ValueId::new(0);
        }
        Expr::Ident(name) => canon_name(name, map),
        _ => {}
    }
    for c in expr_children_mut(e) {
        canon_expr(c, map);
    }
}

/// Alpha-rename/provenance-erase one statement.
fn canon_stmt(s: &mut Stmt, map: &std::collections::HashMap<String, String>) {
    match s {
        Stmt::Declare {
            name,
            value,
            value_id,
            ..
        } => {
            canon_name(name, map);
            canon_expr(value, map);
            *value_id = abcd_ir::ValueId::new(0);
        }
        Stmt::PhiDecl { name, value_id } => {
            canon_name(name, map);
            *value_id = abcd_ir::ValueId::new(0);
        }
        Stmt::PhiAssign {
            target, value, to, ..
        } => {
            canon_name(target, map);
            canon_expr(value, map);
            *to = abcd_ir::BlockId::new(0);
        }
        Stmt::Expr(e) | Stmt::Throw(e) => canon_expr(e, map),
        Stmt::Return(Some(e)) => canon_expr(e, map),
        Stmt::StoreProp { object, value, .. } => {
            canon_expr(object, map);
            canon_expr(value, map);
        }
        Stmt::StoreIndex {
            object,
            index,
            value,
            ..
        } => {
            canon_expr(object, map);
            canon_expr(index, map);
            canon_expr(value, map);
        }
        Stmt::StoreDyn {
            object, key, value, ..
        } => {
            canon_expr(object, map);
            canon_expr(key, map);
            canon_expr(value, map);
        }
        Stmt::DefineMethod { object, func, .. } => {
            canon_expr(object, map);
            canon_expr(func, map);
        }
        Stmt::StorePrivate { object, value, .. } => {
            canon_expr(object, map);
            canon_expr(value, map);
        }
        Stmt::StoreSuper { key, value, .. } => {
            if let Some(k) = key {
                canon_expr(k, map);
            }
            canon_expr(value, map);
        }
        Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => canon_expr(value, map),
        Stmt::CatchBind { name } => canon_name(name, map),
        Stmt::Elided { loc, .. } | Stmt::Fallback { loc, .. } => *loc = None,
        _ => {}
    }
}

/// Alpha-rename/provenance-erase one token.
fn canon_tok(t: &mut FTok, map: &std::collections::HashMap<String, String>) {
    let FTok::Leaf(l) = t else { return };
    match l {
        Leaf::Raw(s) => canon_stmt(s, map),
        Leaf::Destructure { obj, keys, rest } => {
            canon_expr(obj, map);
            for (_, target) in keys {
                canon_name(target, map);
            }
            canon_name(rest, map);
        }
        Leaf::Decl { name, value, .. } => {
            canon_name(name, map);
            if let Some(v) = value {
                canon_expr(v, map);
            }
        }
        Leaf::Assign { target, value } => {
            canon_name(target, map);
            canon_expr(value, map);
        }
    }
}

/// The canonical form of a token run: run-local definition names
/// replaced by first-occurrence placeholders (`#d0`, `#d1`, …) and SSA
/// provenance erased. Two duplicated finally copies are structurally
/// equal IFF their canonical forms are equal (external names — same
/// SSA temps, same literals — compare verbatim).
fn ft_canon(toks: &[FTok]) -> Vec<FTok> {
    let mut out = toks.to_vec();
    let map: std::collections::HashMap<String, String> = ftok_def_names(toks)
        .into_iter()
        .enumerate()
        .map(|(i, n)| (n, format!("#d{i}")))
        .collect();
    for t in out.iter_mut() {
        canon_tok(t, &map);
    }
    out
}

/// Bookkeeping-only leaf of the es2abc finally dispatch: phi wiring
/// whose value is a plain temp/identifier/literal copy. Anything
/// effectful (calls, stores, real computation) is NOT bookkeeping.
fn ft_bookkeeping(l: &Leaf) -> bool {
    let simple = |e: &Expr| matches!(e, Expr::Temp { .. } | Expr::Ident(_) | Expr::Lit(_));
    match l {
        Leaf::Raw(Stmt::PhiDecl { .. })
        | Leaf::Raw(Stmt::Unreachable)
        | Leaf::Raw(Stmt::CatchBind { .. }) => true,
        Leaf::Raw(Stmt::PhiAssign { value, .. }) => simple(value),
        Leaf::Raw(Stmt::Declare { value, .. }) => simple(value),
        _ => false,
    }
}

/// The extracted finally idiom.
struct FinallyIdiom {
    /// The finally body, as raw tokens (emitted verbatim).
    body: Vec<FTok>,
    /// Its canonical form (the match template).
    canon: Vec<FTok>,
    /// The phi declarations the dissolved dispatch owned (re-hoisted
    /// before the folded try so surviving dead phi assigns still
    /// resolve to a `var` — module mode is strict).
    decls: Vec<Leaf>,
}

/// Extract the finally body from a dispatch-shaped handler body (the
/// outer wrapper's catch): phi bookkeeping + exactly one switch whose
/// `case undefined:` arm holds the finally body (default arm pure
/// bookkeeping) + the rethrow-unless-hole conditional whose thrown
/// temp traces through the copy chain to the catch binding.
fn ft_extract_dispatch(body: &[SNode], binding: &str) -> Option<FinallyIdiom> {
    let toks = ft_flatten(body);
    let mut switch_idx = None;
    let mut rethrow_idx = None;
    for (i, t) in toks.iter().enumerate() {
        match t {
            FTok::Node(SNode::Switch { .. }) => {
                if switch_idx.is_some() {
                    return None; // one dispatch switch only
                }
                switch_idx = Some(i);
            }
            FTok::Node(SNode::If { .. }) => {
                if rethrow_idx.is_some() {
                    return None; // one rethrow conditional only
                }
                rethrow_idx = Some(i);
            }
            FTok::Leaf(l) if ft_bookkeeping(l) => {}
            _ => return None, // anything else is real handler code
        }
    }
    let si = switch_idx?;
    let ri = rethrow_idx?;
    if ri < si {
        return None; // the rethrow follows the dispatch
    }
    // The dispatch switch: disc is a temp/ident; exactly two cases —
    // `case undefined:` (the finally run arm) and `default:` (pure
    // bookkeeping, no re-run of F — matches run-once semantics).
    let FTok::Node(SNode::Switch { disc, cases }) = &toks[si] else {
        unreachable!()
    };
    temp_name(disc)?;
    if cases.len() != 2 {
        return None;
    }
    let run = cases
        .iter()
        .find(|c| c.tests.len() == 1 && matches!(&c.tests[0], Expr::Lit(Lit::Undefined)))?;
    let default = cases.iter().find(|c| c.tests.is_empty())?;
    let run_toks = ft_flatten(&run.body);
    let default_toks = ft_flatten(&default.body);
    // The default arm: pure bookkeeping plus an optional closing break.
    let default_ok = default_toks.iter().all(|t| match t {
        FTok::Leaf(l) => ft_bookkeeping(l),
        FTok::Node(SNode::Break { label: None }) => true,
        _ => false,
    });
    if !default_ok {
        return None;
    }
    // The run arm: [finally body] [trailing bookkeeping] [break?].
    let mut f_len = run_toks.len();
    while f_len > 0 {
        let bk = match &run_toks[f_len - 1] {
            FTok::Leaf(l) => ft_bookkeeping(l),
            FTok::Node(SNode::Break { label: None }) => true,
            _ => false,
        };
        if bk {
            f_len -= 1;
        } else {
            break;
        }
    }
    let fbody: Vec<FTok> = run_toks[..f_len].to_vec();
    if fbody.is_empty() {
        return None;
    }
    // The template: flat statements only, no control transfers, no
    // nested nodes (v1 conservatism — copies must match leaf-for-leaf).
    let template_ok = fbody.iter().all(|t| match t {
        FTok::Leaf(Leaf::Raw(
            Stmt::Return(_) | Stmt::Throw(_) | Stmt::Branch { .. } | Stmt::CondBranch { .. },
        )) => false,
        FTok::Leaf(_) => true,
        FTok::Node(_) => false,
    });
    if !template_ok {
        return None;
    }
    // The rethrow conditional: `if (!(hole != X)) { return; } else {
    // throw X; }` (either polarity), and X must trace through the
    // bookkeeping copy chain to the catch binding.
    let FTok::Node(SNode::If {
        cond,
        then,
        otherwise,
    }) = &toks[ri]
    else {
        unreachable!()
    };
    let thrown = ft_rethrow_temp(cond, then, otherwise)?;
    // Copy chain: target <- source over all bookkeeping assigns.
    let mut edges: Vec<(String, String)> = Vec::new();
    for t in &toks {
        if let FTok::Leaf(l) = t {
            match l {
                Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                | Leaf::Assign { target, value } => {
                    if let Some(src) = temp_name(value) {
                        edges.push((target.clone(), src.to_string()));
                    }
                }
                Leaf::Raw(Stmt::Declare { name, value, .. }) => {
                    if let Some(src) = temp_name(value) {
                        edges.push((name.clone(), src.to_string()));
                    }
                }
                _ => {}
            }
        }
    }
    // BFS from the thrown temp to the binding.
    let mut frontier = vec![thrown];
    let mut seen = std::collections::HashSet::new();
    let mut reaches = false;
    while let Some(x) = frontier.pop() {
        if x == binding {
            reaches = true;
            break;
        }
        if !seen.insert(x.clone()) {
            continue;
        }
        for (t, s) in &edges {
            if *t == x {
                frontier.push(s.clone());
            }
        }
    }
    if !reaches {
        return None;
    }
    // Hoist the dispatch's phi declarations (dead assigns elsewhere in
    // the function still reference them).
    let decls: Vec<Leaf> = toks
        .iter()
        .filter_map(|t| match t {
            FTok::Leaf(l @ Leaf::Raw(Stmt::PhiDecl { .. })) => Some(l.clone()),
            _ => None,
        })
        .collect();
    let canon = ft_canon(&fbody);
    Some(FinallyIdiom {
        body: fbody,
        canon,
        decls,
    })
}

/// The `(hole != X)` rethrow conditional, either polarity; returns the
/// rethrown temp's name when the shape is `{ return; }` vs `{ throw X; }`.
fn ft_rethrow_temp(cond: &Expr, then: &[SNode], otherwise: &[SNode]) -> Option<String> {
    let mut e = cond;
    let mut negated = false;
    loop {
        match e {
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsTrue,
                operand,
            } => e = operand,
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsFalse | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => {
                negated = !negated;
                e = operand;
            }
            _ => break,
        }
    }
    let Expr::Compare {
        op: abcd_ir::op::CmpOp::NotEq | abcd_ir::op::CmpOp::StrictNotEq,
        left,
        right,
    } = e
    else {
        return None;
    };
    let x = if matches!(left.as_ref(), Expr::Lit(Lit::Hole)) {
        temp_name(right)?
    } else if matches!(right.as_ref(), Expr::Lit(Lit::Hole)) {
        temp_name(left)?
    } else {
        return None;
    };
    // `!(hole != X)`: then = return, else = throw. Un-negated, swapped.
    let (ret_arm, throw_arm) = if negated {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    // `Ok(None)` = the return arm is clean; `Ok(Some(name))` = the
    // throw arm rethrows `name`.
    let arm_ok = |arm: &[SNode], want_throw: bool| -> Option<Option<String>> {
        let toks = ft_flatten(arm);
        let mut thrown = None;
        let mut saw_terminal = false;
        for t in &toks {
            match t {
                FTok::Leaf(Leaf::Raw(Stmt::Return(None))) if !want_throw => {
                    saw_terminal = true;
                }
                FTok::Leaf(Leaf::Raw(Stmt::Throw(v))) if want_throw => {
                    thrown = Some(temp_name(v)?.to_string());
                    saw_terminal = true;
                }
                FTok::Leaf(l) if ft_bookkeeping(l) => {}
                _ => return None,
            }
        }
        if !saw_terminal {
            return None;
        }
        Some(thrown)
    };
    arm_ok(ret_arm, false)?;
    let thrown = arm_ok(throw_arm, true)??;
    if thrown != x {
        return None; // the hole-guard and the rethrow must agree
    }
    Some(thrown)
}

/// May this statement list complete normally (fall through to whatever
/// follows)? Conservative: any doubt answers `true` (the fold then
/// REQUIRES the normal-completion finally copy — absence bails).
fn ft_list_fallthrough(nodes: &[SNode]) -> bool {
    nodes.iter().all(ft_node_fallthrough)
}

fn ft_node_fallthrough(n: &SNode) -> bool {
    match n {
        SNode::Stmts(ls) => !ls.iter().any(|l| {
            matches!(
                l,
                Leaf::Raw(Stmt::Return(_))
                    | Leaf::Raw(Stmt::Throw(_))
                    | Leaf::Raw(Stmt::Branch { .. })
                    | Leaf::Raw(Stmt::CondBranch { .. })
            )
        }),
        SNode::If {
            then, otherwise, ..
        } => ft_list_fallthrough(then) && ft_list_fallthrough(otherwise),
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            let body_ft = ft_list_fallthrough(body);
            let catch_ft =
                catches.is_empty() || catches.iter().any(|c| ft_list_fallthrough(&c.body));
            // An exceptional path is not a NORMAL completion; a
            // finally clause runs either way and changes nothing.
            let _ = finally;
            body_ft || catch_ft && !catches.is_empty()
        }
        SNode::Break { .. } | SNode::Continue { .. } => false,
        // Loops, switches, labeled blocks, honesty comments: may
        // complete (a loop can break out, a comment says nothing).
        SNode::While { .. }
        | SNode::DoWhile { .. }
        | SNode::ForOf { .. }
        | SNode::ForIn { .. }
        | SNode::Switch { .. }
        | SNode::Labeled { .. }
        | SNode::Honest(_) => true,
    }
}

/// Loop/switch nesting context for exit classification within the
/// protected construct C (a `break`/`continue` intercepted INSIDE C
/// needs no finally copy; one leaving C does).
#[derive(Clone, Copy)]
struct FtCtx {
    /// Enclosing loops within C.
    loops: usize,
    /// Enclosing loops + switches within C.
    breakables: usize,
}

/// Strip the inlined finally copies preceding every exit of the
/// protected construct. `Err(())` = an exit without its copy — the
/// fold bails and the duplicated form stays (honesty rule).
fn ft_strip_exits(
    nodes: &mut Vec<SNode>,
    idiom: &FinallyIdiom,
    ctx: FtCtx,
    labels: &mut Vec<String>,
    strips: &mut usize,
) -> Result<(), ()> {
    // Recurse into nested constructs first (their internal exits are
    // classified against the ADJUSTED context).
    for n in nodes.iter_mut() {
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                ft_strip_exits(then, idiom, ctx, labels, strips)?;
                ft_strip_exits(otherwise, idiom, ctx, labels, strips)?;
            }
            SNode::While { label, body, .. } | SNode::DoWhile { label, body, .. } => {
                let inner = FtCtx {
                    loops: ctx.loops + 1,
                    breakables: ctx.breakables + 1,
                };
                let pushed = label.is_some();
                if let Some(l) = label {
                    labels.push(l.clone());
                }
                let r = ft_strip_exits(body, idiom, inner, labels, strips);
                if pushed {
                    labels.pop();
                }
                r?;
            }
            SNode::ForOf { body, .. } | SNode::ForIn { body, .. } => {
                let inner = FtCtx {
                    loops: ctx.loops + 1,
                    breakables: ctx.breakables + 1,
                };
                ft_strip_exits(body, idiom, inner, labels, strips)?;
            }
            SNode::Switch { cases, .. } => {
                let inner = FtCtx {
                    loops: ctx.loops,
                    breakables: ctx.breakables + 1,
                };
                for c in cases {
                    ft_strip_exits(&mut c.body, idiom, inner, labels, strips)?;
                }
            }
            SNode::Labeled { label, body } => {
                labels.push(label.clone());
                let r = ft_strip_exits(body, idiom, ctx, labels, strips);
                labels.pop();
                r?;
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                ft_strip_exits(body, idiom, ctx, labels, strips)?;
                for c in catches {
                    ft_strip_exits(&mut c.body, idiom, ctx, labels, strips)?;
                }
                if let Some(f) = finally {
                    ft_strip_exits(f, idiom, ctx, labels, strips)?;
                }
            }
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    // Flatten this level and strip the copies preceding its own exits.
    let k = idiom.canon.len();
    let toks = ft_flatten(nodes);
    let mut remove: Vec<usize> = Vec::new(); // token indices
    for j in 0..toks.len() {
        let needs = match &toks[j] {
            FTok::Leaf(Leaf::Raw(Stmt::Return(_))) => true,
            FTok::Node(SNode::Break { label }) => match label {
                None => ctx.breakables == 0,
                Some(l) => !labels.contains(l),
            },
            FTok::Node(SNode::Continue { label }) => match label {
                None => ctx.loops == 0,
                Some(l) => !labels.contains(l),
            },
            _ => false,
        };
        if !needs {
            continue;
        }
        if j < k {
            return Err(()); // an exit without room for its copy
        }
        let cand = &toks[j - k..j];
        if ft_canon(cand) != idiom.canon {
            return Err(()); // an exit whose copy is missing/different
        }
        // The return-value guard: in `F; return v` F runs BEFORE v is
        // read; in `try { return v } finally { F }` v is read first.
        // Equivalent only when F cannot rebind anything v mentions.
        if let FTok::Leaf(Leaf::Raw(Stmt::Return(Some(v)))) = &toks[j] {
            let mut assigned: Vec<&str> = Vec::new();
            for t in cand {
                if let FTok::Leaf(
                    Leaf::Raw(Stmt::PhiAssign { target, .. }) | Leaf::Assign { target, .. },
                ) = t
                {
                    assigned.push(target);
                }
            }
            if assigned.iter().any(|n| expr_uses_name(v, n)) {
                return Err(());
            }
        }
        remove.extend(j - k..j);
        *strips += 1;
    }
    if remove.is_empty() {
        return Ok(());
    }
    let kept: Vec<FTok> = toks
        .into_iter()
        .enumerate()
        .filter_map(|(i, t)| (!remove.contains(&i)).then_some(t))
        .collect();
    *nodes = ft_regroup(kept);
    Ok(())
}

/// Attempt the finally fold at `nodes[i]` (a handler-protecting outer
/// try carrying the "finally idiom" note). Returns the replacement for
/// `nodes[i..]` on success — the fold may also consume the
/// normal-completion finally copy in the following siblings.
fn ft_fold_at(nodes: &[SNode], i: usize) -> Option<Vec<SNode>> {
    let SNode::Try {
        body,
        catches,
        note,
        finally: None,
    } = &nodes[i]
    else {
        return None;
    };
    if !note.as_deref().is_some_and(|n| n.contains("finally idiom")) {
        return None;
    }
    if catches.len() != 1 {
        return None;
    }
    let binding = catches[0].binding.clone()?;
    let idiom = ft_extract_dispatch(&catches[0].body, &binding)?;

    // Strip the inlined copies inside the protected construct.
    let mut stripped_body = body.clone();
    let mut labels: Vec<String> = Vec::new();
    let mut strips = 0usize;
    ft_strip_exits(
        &mut stripped_body,
        &idiom,
        FtCtx {
            loops: 0,
            breakables: 0,
        },
        &mut labels,
        &mut strips,
    )
    .ok()?;

    // Unwrap a sole inner try/catch: `try { try{A} catch{B} } finally{F}`
    // reads as `try { A } catch { B } finally { F }`.
    let unwrap = stripped_body.len() == 1
        && matches!(
            &stripped_body[0],
            SNode::Try {
                finally: None,
                catches,
                ..
            } if !catches.is_empty()
        );
    let (folded_try, construct_ft) = if unwrap {
        let SNode::Try {
            body: ibody,
            catches: icatches,
            note: inote,
            finally: None,
        } = stripped_body.into_iter().next().unwrap()
        else {
            unreachable!()
        };
        let ft =
            ft_list_fallthrough(&ibody) || icatches.iter().any(|c| ft_list_fallthrough(&c.body));
        (
            SNode::Try {
                body: ibody,
                catches: icatches,
                note: inote,
                finally: Some(ft_regroup(idiom.body.clone())),
            },
            ft,
        )
    } else {
        let ft = ft_list_fallthrough(&stripped_body);
        (
            SNode::Try {
                body: stripped_body,
                catches: Vec::new(),
                note: None,
                finally: Some(ft_regroup(idiom.body.clone())),
            },
            ft,
        )
    };

    // The normal-completion copy: when the construct can fall through,
    // es2abc placed its finally copy right after the protected span —
    // the immediately following siblings. Consume it, or bail.
    let mut tail = ft_flatten(&nodes[i + 1..]);
    if construct_ft {
        if tail.len() < idiom.canon.len() || ft_canon(&tail[..idiom.canon.len()]) != idiom.canon {
            return None;
        }
        tail.drain(..idiom.canon.len());
    }

    let mut out: Vec<SNode> = Vec::new();
    if !idiom.decls.is_empty() {
        out.push(SNode::Stmts(idiom.decls.clone()));
    }
    out.push(SNode::Honest(format!(
        "finally recovered from es2abc's duplicated-finally idiom (the dispatch handler was finally+rethrow; {strips} inlined copy/copies folded)"
    )));
    out.push(folded_try);
    out.extend(ft_regroup(tail));
    Some(out)
}

/// The finally fold driver over one statement list.
fn fold_finally(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let idiom = matches!(
            &nodes[i],
            SNode::Try {
                note: Some(n),
                catches,
                finally: None,
                ..
            } if n.contains("finally idiom") && catches.len() == 1
        );
        if idiom && let Some(replacement) = ft_fold_at(nodes, i) {
            nodes.splice(i.., replacement);
            stats.finally_fold += 1;
            // Do not advance: the replacement's own nested trys were
            // already folded by the children-first recursion.
            continue;
        }
        i += 1;
    }
}

// ── d-P8: LexStore scope reconstruction (design §4.3 "Names") ──────
//
// v1 (d-P4) printed every lexical binding as a function-top `let n;`
// plus plain `n = value;` assignments, with `/* scope-push […] */`
// comments marking the `NewLexEnv*` sites. This fold reconstructs the
// declaration site where provable: es2abc initializes a pushed frame's
// slots with `stlexvar 0, slot` IMMEDIATELY after the push (the TDZ
// hole + the elided `ThrowUndefinedIfHoleWithName` guard prove every
// read is post-init), so the first store to a slot right after its
// push IS the source's `let` declaration.
//
// Provable means ALL of:
//   - the store sits in the same statement run as the push, at level 0
//     (the just-pushed frame), with a slot index inside the frame;
//   - every store to the same NAME anywhere in the function lives in
//     that same run after the push (a store elsewhere would become an
//     assignment to a binding the block declaration does not cover);
//   - the name is not a parameter (redeclaration is a SyntaxError) and
//     was not already block-declared by this fold (same-named frames
//     stay comments + plain assignments — the honesty rule).
//
// `const` is deliberately NOT inferred: a capturing closure can
// reassign the slot from a nested function body (cross-function proof
// is out of scope) — declarations are uniformly `let`.
//
// Where the shape is unprovable the `/* scope-push […] */` comment and
// the plain assignments stay, unchanged.

/// One LexStore occurrence: which `Stmts` run (walk order) and leaf.
struct LexStoreSite {
    /// The run's walk-order id.
    run: usize,
    /// The leaf index within the run.
    index: usize,
}

/// Reconstruct block-scoped declarations at provable lexenv push
/// sites. Runs AFTER the desugar folds (it consumes their output).
pub fn scope_fold(nodes: &mut [SNode], params: &[String], stats: &mut FoldStats) {
    // Pass 1: census of every LexStore name → its sites.
    fn census(
        nodes: &[SNode],
        runs: &mut usize,
        stores: &mut std::collections::HashMap<String, Vec<LexStoreSite>>,
    ) {
        for n in nodes {
            match n {
                SNode::Stmts(leaves) => {
                    let run = *runs;
                    *runs += 1;
                    for (index, l) in leaves.iter().enumerate() {
                        if let Leaf::Raw(Stmt::LexStore { name, .. }) = l {
                            stores
                                .entry(name.clone())
                                .or_default()
                                .push(LexStoreSite { run, index });
                        }
                    }
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    census(then, runs, stores);
                    census(otherwise, runs, stores);
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => census(body, runs, stores),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    census(body, runs, stores);
                    for c in catches {
                        census(&c.body, runs, stores);
                    }
                    if let Some(f) = finally {
                        census(f, runs, stores);
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        census(&c.body, runs, stores);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    let mut runs = 0usize;
    let mut stores: std::collections::HashMap<String, Vec<LexStoreSite>> =
        std::collections::HashMap::new();
    census(nodes, &mut runs, &mut stores);

    // Pass 2: convert the provable initializations.
    let mut converted: std::collections::HashSet<String> = std::collections::HashSet::new();
    fn convert(
        nodes: &mut [SNode],
        runs: &mut usize,
        stores: &std::collections::HashMap<String, Vec<LexStoreSite>>,
        params: &[String],
        converted: &mut std::collections::HashSet<String>,
        stats: &mut FoldStats,
    ) {
        for n in nodes.iter_mut() {
            match n {
                SNode::Stmts(leaves) => {
                    let run = *runs;
                    *runs += 1;
                    convert_run(leaves, run, stores, params, converted, stats);
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    convert(then, runs, stores, params, converted, stats);
                    convert(otherwise, runs, stores, params, converted, stats);
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => {
                    convert(body, runs, stores, params, converted, stats)
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    convert(body, runs, stores, params, converted, stats);
                    for c in catches {
                        convert(&mut c.body, runs, stores, params, converted, stats);
                    }
                    if let Some(f) = finally {
                        convert(f, runs, stores, params, converted, stats);
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        convert(&mut c.body, runs, stores, params, converted, stats);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn convert_run(
        leaves: &mut Vec<Leaf>,
        run: usize,
        stores: &std::collections::HashMap<String, Vec<LexStoreSite>>,
        params: &[String],
        converted: &mut std::collections::HashSet<String>,
        stats: &mut FoldStats,
    ) {
        let mut push_at: Vec<usize> = Vec::new();
        for (i, l) in leaves.iter().enumerate() {
            if matches!(l, Leaf::Raw(Stmt::ScopePush { .. })) {
                push_at.push(i);
            }
        }
        // Apply edits back-to-front so indices stay valid.
        for &p in push_at.iter().rev() {
            let Leaf::Raw(Stmt::ScopePush { names }) = &leaves[p] else {
                unreachable!()
            };
            let slot_count = names.len();
            // The immediate initialization run: level-0 slot stores
            // (re-stores of already-initialized slots, elided-guard
            // markers, and honesty comments may interleave).
            let mut inits: Vec<(usize, u16)> = Vec::new(); // (leaf index, slot)
            let mut j = p + 1;
            while j < leaves.len() {
                match &leaves[j] {
                    Leaf::Raw(Stmt::LexStore { level, slot, .. })
                        if *level == 0 && (*slot as usize) < slot_count =>
                    {
                        if inits.iter().any(|&(_, s)| s == *slot) {
                            // A re-store of an initialized slot ends the
                            // initialization run (conservative).
                            break;
                        }
                        inits.push((j, *slot));
                        j += 1;
                    }
                    Leaf::Raw(Stmt::Elided { .. } | Stmt::Fallback { .. }) => {
                        j += 1;
                    }
                    _ => break,
                }
            }
            if inits.is_empty() {
                continue;
            }
            // Which inits are provable declarations?
            let mut declared_slots: Vec<u16> = Vec::new();
            let mut decl_edits: Vec<(usize, Leaf)> = Vec::new();
            for &(idx, slot) in &inits {
                let Leaf::Raw(Stmt::LexStore { name, .. }) = &leaves[idx] else {
                    unreachable!()
                };
                let name = name.clone();
                if params.contains(&name) || converted.contains(&name) {
                    continue;
                }
                // Same-name slots within this push: only the first may
                // become a declaration (a second `let n` in one scope is
                // a SyntaxError).
                if decl_edits.iter().any(|(_, l)| {
                    matches!(l, Leaf::Decl { name: dn, .. } if *dn == crate::legalize::sanitize(&name))
                }) {
                    continue;
                }
                // Every store to this name must live in THIS run after
                // the push (else the block declaration would not cover
                // it — strict-mode ReferenceError, or a shadowed
                // binding).
                let ok = stores
                    .get(&name)
                    .into_iter()
                    .flatten()
                    .all(|s| s.run == run && s.index > p);
                if !ok {
                    continue;
                }
                let Leaf::Raw(Stmt::LexStore { value, .. }) = &leaves[idx] else {
                    unreachable!()
                };
                decl_edits.push((
                    idx,
                    Leaf::Decl {
                        name: crate::legalize::sanitize(&name),
                        mutable: true,
                        value: Some(value.clone()),
                    },
                ));
                declared_slots.push(slot);
                converted.insert(name);
            }
            if decl_edits.is_empty() {
                continue;
            }
            let mut declared_raw: Vec<String> = Vec::new();
            for (idx, leaf) in decl_edits {
                if let Leaf::Decl { name, .. } = &leaf {
                    declared_raw.push(name.clone());
                }
                leaves[idx] = leaf;
                stats.scope_fold += 1;
            }
            // The name's OTHER stores in this run (the `ok` check above
            // proved they all live here, after the push) print as plain
            // assignments — but left as raw `LexStore` leaves they still
            // count toward emit's hoisted `lex_decls` whenever the push
            // comment survives (an unprovable sibling slot keeps
            // `own > level`), printing a second `let n;` at the function
            // top — a same-scope redeclaration (SyntaxError; wild-smoke
            // Bug B). Rewrite them to plain assignment leaves so the
            // block declaration is the ONLY declaration of the name.
            for l in leaves.iter_mut().skip(p + 1) {
                if let Leaf::Raw(Stmt::LexStore { name, value, .. }) = l
                    && declared_raw
                        .iter()
                        .any(|d| *d == crate::legalize::sanitize(name))
                {
                    *l = Leaf::Assign {
                        target: crate::legalize::sanitize(name),
                        value: value.clone(),
                    };
                }
            }
            // The push comment: consumed when every slot was declared;
            // otherwise it stays, listing the undeclared slots only.
            let Leaf::Raw(Stmt::ScopePush { names }) = &mut leaves[p] else {
                unreachable!()
            };
            let remaining: Vec<Option<String>> = names
                .iter()
                .enumerate()
                .filter(|&(i, _)| !declared_slots.contains(&(i as u16)))
                .map(|(_, n)| n.clone())
                .collect();
            if remaining.is_empty() {
                // Back-to-front push processing makes removal safe.
                leaves.remove(p);
            } else {
                *names = remaining;
            }
        }
    }
    let mut runs = 0usize;
    convert(nodes, &mut runs, &stores, params, &mut converted, stats);
}

// ── N74-W4: late declaration-site reconstruction (TDZ honesty) ─────
//
// The v1 scope model hoists every lexical/global binding: `let n;`
// from emit's `lex_decls`, `var g;` at module top for global stores
// (es2abc compiles function bodies STRICT — an undeclared STORE is a
// ReferenceError, so the hoist cannot simply be dropped). Hoisting is
// sound for value flow but DESTROYS the initialization window: a read
// or closure call between scope entry and the first store sees
// `undefined` where the original program's binding was still the TDZ
// hole (lexical: `ldlexvar` + `ThrowUndefinedIfHoleWithName` →
// ReferenceError) or did not exist at all (sloppy global:
// undeclared-read ReferenceError). test262's `*-before-initialization`
// rows and the "undeclared variable" operator rows (`x > (x = 1)`)
// observe exactly this window.
//
// This fold reconstructs the window when it is PROVABLY faithful: the
// binding's textually first store sits in a DECLARATION-CAPABLE run —
// the function body's root statement run, or the root run of a `try`
// BODY (a try body executes unconditionally up to the first throw, and
// block-scope is safe there only when nothing references the name
// outside that try body — checked). The first store becomes
// `let n = <value>;` at that exact position; all other stores become
// plain assignments; the hoisted `let n;` vanishes because
// `lex_decls` only counts remaining `LexStore` leaves (the module-top
// `var g;` stays — a function-scope `let` legally shadows it, and the
// shadow IS the binding every in-function reference resolves to).
// Every access executing before the declaration line then hits the JS
// TDZ — the same ReferenceError the original program produced — and
// every access after sees the stored value. Stores in nested functions
// are capture-assignments to the same binding and stay assignments
// (each function body is folded separately; their stores fail the
// level/ownership check).
//
// Provable means ALL of:
//   - the name is stored by exactly one KIND of store (lexical or
//     global — a mix means the scope model is inconsistent);
//   - for lexical stores, every store targets an OWN frame slot
//     (level < own-push count, the `lex_decls` rule) — a capture store
//     at level ≥ own belongs to an ancestor's binding;
//   - global stores convert only at the TOP LEVEL (a `let` inside a
//     nested function would shadow the global — dream gate:
//     params-dflt-gen-meth's `callCount` died to exactly that);
//   - the textually first store sits in a declaration-capable run, and
//     when that run is inside a `try` body, NO reference to the name
//     exists outside that try body (an outside reference would
//     silently read the module-top `var` instead);
//   - the name is not a parameter, was not already declared by
//     [`scope_fold`], and is not a read-only global name
//     (`undefined`/`NaN`/`Infinity` — the read-only-global collision
//     lane owns those).
//
// Where the shape is unprovable the hoisted-`let`/hoisted-`var`
// emission stays, unchanged (the honesty rule).

/// One store occurrence for the late-decl fold.
struct LateStore {
    /// Sanitized binding name.
    name: String,
    /// The store's value defines a function/class (the module's PUBLIC
    /// surface: an external reader — e.g. a test driver appended after
    /// `func_main_0.call(this)` — reads the module-scope binding, so the
    /// store must NOT become a shadowing local `let`; N74 yield-star
    /// golden/node regression).
    func_valued: bool,
    /// Lexical store (vs global store).
    lexical: bool,
    /// The scope-chain level (lexical only; 0 for globals).
    level: u16,
    /// The innermost DECLARATION-CAPABLE region: `Some(0)` at the root
    /// list, `Some(try-id)` inside a chain of `try` bodies; `None` when
    /// the store sits in a run no declaration may occupy (an `if` arm,
    /// a loop body, a `catch`/`finally`, …).
    region: Option<usize>,
    /// The enclosing try-body ids (innermost last) — the nesting check.
    stack: Vec<usize>,
    /// Whole-tree pre-order sequence number.
    seq: usize,
}

/// The fold's whole-tree context.
struct LateDeclCx {
    /// Own lexenv pushes (the `lex_decls` ownership rule).
    pushes: usize,
    /// Names already declared (`scope_fold` conversions, params).
    declared: std::collections::HashSet<String>,
    /// Store sites, in pre-order.
    stores: Vec<LateStore>,
    /// `(name, try-stack-membership)`: a name read (or store target)
    /// that appears OUTSIDE some try body — per try-id disqualifiers.
    /// We record for every name-use the full try-stack; a candidate
    /// with `try_id = Some(t)` dies if any use's stack lacks `t`.
    uses: Vec<(String, Vec<usize>)>,
    /// Monotonic try-body ids.
    next_try: usize,
    /// Pre-order counter.
    seq: usize,
    /// Sequence positions of every ScopePush/ScopePop (a name whose
    /// use/store SPAN contains one may be re-pushed mid-span — a
    /// different binding with the same name; N74-W4 corpus regression
    /// for-update-continue-1: `let v2_0` declared twice for two
    /// iterations' slots, the inner shadowing the outer's read).
    scope_edges: Vec<usize>,
}

impl LateDeclCx {
    fn new() -> Self {
        Self {
            pushes: 0,
            declared: std::collections::HashSet::new(),
            stores: Vec::new(),
            uses: Vec::new(),
            next_try: 1,
            seq: 0,
            scope_edges: Vec::new(),
        }
    }
}

/// Whether `e` mentions `name` as an identifier (a read of the
/// binding; declaration sites and store targets are recorded by the
/// caller).
fn collect_ident_uses(e: &Expr, try_stack: &[usize], out: &mut Vec<(String, Vec<usize>)>) {
    if let Expr::Ident(name) = e {
        out.push((name.clone(), try_stack.to_vec()));
    }
    for c in expr_children(e) {
        collect_ident_uses(c, try_stack, out);
    }
}

/// Census for the late-decl fold. `region_stack` = enclosing
/// DECLARATION-CAPABLE region ids (root list, try bodies, `if` arms,
/// catch/finally bodies, labeled blocks — innermost last; loops and
/// switch cases are NOT capable: a `let` there is per-iteration /
/// fallthrough-unsafe). A store may become a declaration only when its
/// run sits directly in a capable container (`capable_here`).
fn late_decl_census(
    nodes: &[SNode],
    capable_here: bool,
    region_stack: &mut Vec<usize>,
    cx: &mut LateDeclCx,
) {
    for n in nodes {
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    cx.seq += 1;
                    match l {
                        Leaf::Raw(Stmt::ScopePush { .. }) => {
                            cx.pushes += 1;
                            cx.scope_edges.push(cx.seq);
                        }
                        Leaf::Raw(Stmt::LexStore {
                            level, name, value, ..
                        }) => {
                            let name = crate::legalize::sanitize(name);
                            collect_ident_uses(value, region_stack, &mut cx.uses);
                            cx.uses.push((name.clone(), region_stack.clone()));
                            cx.stores.push(LateStore {
                                func_valued: matches!(
                                    value,
                                    Expr::Closure { .. } | Expr::Class { .. }
                                ),
                                name,
                                lexical: true,
                                level: *level,
                                region: capable_here
                                    .then(|| region_stack.last().copied().unwrap_or(0)),
                                stack: region_stack.clone(),
                                seq: cx.seq,
                            });
                        }
                        Leaf::Raw(Stmt::GlobalStore { name, value, .. }) => {
                            let name = crate::legalize::sanitize(name);
                            collect_ident_uses(value, region_stack, &mut cx.uses);
                            cx.uses.push((name.clone(), region_stack.clone()));
                            cx.stores.push(LateStore {
                                func_valued: matches!(
                                    value,
                                    Expr::Closure { .. } | Expr::Class { .. }
                                ),
                                name,
                                lexical: false,
                                level: 0,
                                region: capable_here
                                    .then(|| region_stack.last().copied().unwrap_or(0)),
                                stack: region_stack.clone(),
                                seq: cx.seq,
                            });
                        }
                        Leaf::Decl { name, value, .. } => {
                            cx.declared.insert(name.clone());
                            if let Some(v) = value {
                                collect_ident_uses(v, region_stack, &mut cx.uses);
                            }
                        }
                        Leaf::Raw(Stmt::ScopePop) => {
                            cx.scope_edges.push(cx.seq);
                        }
                        Leaf::Assign { target, value } => {
                            collect_ident_uses(value, region_stack, &mut cx.uses);
                            cx.uses.push((target.clone(), region_stack.clone()));
                        }
                        Leaf::Raw(s) => {
                            for e in stmt_exprs_of(s) {
                                collect_ident_uses(e, region_stack, &mut cx.uses);
                            }
                        }
                        Leaf::Destructure { obj, .. } => {
                            collect_ident_uses(obj, region_stack, &mut cx.uses);
                        }
                    }
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                collect_ident_uses(cond, region_stack, &mut cx.uses);
                for arm in [then, otherwise] {
                    let id = cx.next_try;
                    cx.next_try += 1;
                    region_stack.push(id);
                    late_decl_census(arm, true, region_stack, cx);
                    region_stack.pop();
                }
            }
            SNode::While { cond, body, .. } => {
                if let Some(c) = cond {
                    collect_ident_uses(c, region_stack, &mut cx.uses);
                }
                late_decl_census(body, false, region_stack, cx);
            }
            SNode::DoWhile { body, cond, .. } => {
                late_decl_census(body, false, region_stack, cx);
                collect_ident_uses(cond, region_stack, &mut cx.uses);
            }
            SNode::Labeled { body, .. } => {
                let id = cx.next_try;
                cx.next_try += 1;
                region_stack.push(id);
                late_decl_census(body, true, region_stack, cx);
                region_stack.pop();
            }
            SNode::ForOf { iter, body, .. } => {
                collect_ident_uses(iter, region_stack, &mut cx.uses);
                late_decl_census(body, false, region_stack, cx);
            }
            SNode::ForIn { obj, body, .. } => {
                collect_ident_uses(obj, region_stack, &mut cx.uses);
                late_decl_census(body, false, region_stack, cx);
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                // Body, catches, and finally are all capable regions
                // (a `let` confined to any of them is scoped to it).
                let id = cx.next_try;
                cx.next_try += 1;
                region_stack.push(id);
                late_decl_census(body, true, region_stack, cx);
                region_stack.pop();
                for c in catches {
                    let id = cx.next_try;
                    cx.next_try += 1;
                    region_stack.push(id);
                    late_decl_census(&c.body, true, region_stack, cx);
                    region_stack.pop();
                }
                if let Some(f) = finally {
                    let id = cx.next_try;
                    cx.next_try += 1;
                    region_stack.push(id);
                    late_decl_census(f, true, region_stack, cx);
                    region_stack.pop();
                }
            }
            SNode::Switch { disc, cases } => {
                collect_ident_uses(disc, region_stack, &mut cx.uses);
                for c in cases {
                    for t in &c.tests {
                        collect_ident_uses(t, region_stack, &mut cx.uses);
                    }
                    late_decl_census(&c.body, false, region_stack, cx);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// All expression positions of a raw statement (for the use census).
fn stmt_exprs_of(s: &Stmt) -> Vec<&Expr> {
    match s {
        Stmt::Declare { value, .. } => vec![value],
        Stmt::PhiAssign { value, .. } => vec![value],
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
        Stmt::StoreSuper { key, value, .. } => key.iter().chain(std::iter::once(value)).collect(),
        Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => vec![value],
        Stmt::Throw(e) => vec![e],
        Stmt::Return(Some(e)) => vec![e],
        Stmt::CondBranch { cond, .. } => vec![cond],
        _ => Vec::new(),
    }
}

/// See the section comment. Runs AFTER [`scope_fold`] (it consumes the
/// stores scope_fold could not turn into declarations). `top_level`
/// gates the global-store half (nested functions would shadow).
pub fn late_decl_fold(
    nodes: &mut [SNode],
    params: &[String],
    top_level: bool,
    stats: &mut FoldStats,
) {
    let mut cx = LateDeclCx::new();
    late_decl_census(nodes, true, &mut Vec::new(), &mut cx);

    // Group by name; the qualifying set.
    let mut names: Vec<String> = cx.stores.iter().map(|s| s.name.clone()).collect();
    names.sort();
    names.dedup();
    let mut convert: std::collections::HashMap<String, Vec<usize>> =
        std::collections::HashMap::new();
    for name in names {
        let sites: Vec<&LateStore> = cx.stores.iter().filter(|s| s.name == name).collect();
        // One store kind only (a lexical/global mix means the scope
        // model is inconsistent — the honest fallback stays).
        if sites.iter().any(|s| s.lexical) && sites.iter().any(|s| !s.lexical) {
            continue;
        }
        // Lexical stores must all target OWN frame slots (the
        // `lex_decls` rule); a capture store belongs to an ancestor.
        if sites
            .iter()
            .any(|s| s.lexical && s.level as usize >= cx.pushes)
        {
            continue;
        }
        // Global stores convert only at the top level.
        if sites.iter().any(|s| !s.lexical) && !top_level {
            continue;
        }
        // A function/class-valued binding AT THE MODULE TOP is the
        // module's public surface: converting its first store to a local
        // `let` shadows the module-scope `var` hoist and external readers
        // (e.g. a test driver appended after `func_main_0.call(this)`)
        // see `undefined` (the yield-star golden/node regression).
        // Function-local closures keep the `let` conversion (s38).
        if top_level && sites.iter().any(|s| s.func_valued) {
            continue;
        }
        // Not a parameter, not already declared by scope_fold, not a
        // read-only global name (the sister lane's collision class).
        if params.contains(&name)
            || cx.declared.contains(&name)
            || matches!(name.as_str(), "undefined" | "NaN" | "Infinity")
        {
            continue;
        }
        // Coverage model (N74-W4). When the root run holds a store the
        // declaration goes to the root (a function-scope `let` covering
        // everything; nested stores stay assignments). Otherwise each
        // declaration-capable region holding a store gets its own `let`
        // (sibling `try` bodies etc. — S13.2.1_A7_T4's independent
        // `x = x` probes), provided:
        //   - every OTHER store and every READ of the name is COVERED
        //     by a converted region — the reference's region stack
        //     contains the region id (region 0, the root, covers
        //     everything) — otherwise that reference would silently
        //     read the module-top `var`/outer binding instead;
        //   - no converted region nests inside another (an inner `let`
        //     would shadow the outer region's binding mid-window).
        let root_has = sites.iter().any(|s| s.region == Some(0));
        if root_has {
            // Same-name re-push mid-span → distinct bindings; bail.
            let span_lo = sites.iter().map(|s| s.seq).min().unwrap_or(0);
            let mut span_hi = span_lo;
            for (n, _) in cx.uses.iter().filter(|(n, _)| *n == name) {
                let _ = n;
            }
            for s in sites.iter() {
                span_hi = span_hi.max(s.seq);
            }
            if cx.scope_edges.iter().any(|e| *e > span_lo && *e < span_hi) {
                continue;
            }
            convert.insert(name, vec![0]);
            continue;
        }
        let store_regions: std::collections::HashSet<usize> =
            sites.iter().filter_map(|s| s.region).collect();
        if store_regions.is_empty() {
            continue;
        }
        let nested = cx.stores.iter().filter(|st| st.name == name).any(|st| {
            st.region.is_some()
                && st
                    .stack
                    .iter()
                    .any(|t| store_regions.contains(t) && Some(*t) != st.region)
        });
        if nested {
            continue;
        }
        let covered = |stack: &Vec<usize>| {
            store_regions.contains(&0) || stack.iter().any(|t| store_regions.contains(t))
        };
        if cx
            .uses
            .iter()
            .filter(|(n, _)| *n == name)
            .any(|(_, stack)| !covered(stack))
        {
            continue;
        }
        // Same-name re-push mid-span → distinct bindings; bail.
        let span_lo = sites.iter().map(|s| s.seq).min().unwrap_or(0);
        let mut span_hi = span_lo;
        for s in sites.iter() {
            span_hi = span_hi.max(s.seq);
        }
        if cx.scope_edges.iter().any(|e| *e > span_lo && *e < span_hi) {
            continue;
        }
        convert.insert(name, store_regions.iter().copied().collect());
    }
    if convert.is_empty() {
        return;
    }

    // Rewrite: per (name, region), the first store becomes the `let`;
    // every other store becomes a plain assignment. Region ids are
    // recomputed with the census's traversal (same walk, same ids).
    let mut declared_now: std::collections::HashSet<(String, usize)> =
        std::collections::HashSet::new();
    #[allow(clippy::too_many_arguments)]
    fn rewrite(
        nodes: &mut [SNode],
        capable_here: bool,
        region_stack: &mut Vec<usize>,
        next_try: &mut usize,
        convert: &std::collections::HashMap<String, Vec<usize>>,
        declared_now: &mut std::collections::HashSet<(String, usize)>,
        stats: &mut FoldStats,
    ) {
        for n in nodes.iter_mut() {
            match n {
                SNode::Stmts(leaves) => {
                    let region = capable_here.then(|| region_stack.last().copied().unwrap_or(0));
                    for l in leaves.iter_mut() {
                        let name_regions = match l {
                            Leaf::Raw(Stmt::LexStore { name, .. })
                            | Leaf::Raw(Stmt::GlobalStore { name, .. }) => convert
                                .get(&crate::legalize::sanitize(name))
                                .map(|r| (crate::legalize::sanitize(name), r)),
                            _ => None,
                        };
                        let Some((name, regions)) = name_regions else {
                            continue;
                        };
                        let value = match l {
                            Leaf::Raw(Stmt::LexStore { value, .. })
                            | Leaf::Raw(Stmt::GlobalStore { value, .. }) => value.clone(),
                            _ => unreachable!(),
                        };
                        // A declaration only in the name's DECL regions;
                        // other capable stores (and non-capable runs)
                        // stay plain assignments to it.
                        let key = region.map(|r| (name.clone(), r));
                        if let Some(key) = key
                            && regions.contains(&key.1)
                            && !declared_now.contains(&key)
                        {
                            declared_now.insert(key);
                            *l = Leaf::Decl {
                                name,
                                mutable: true,
                                value: Some(value),
                            };
                            stats.late_decl += 1;
                        } else {
                            *l = Leaf::Assign {
                                target: name,
                                value,
                            };
                        }
                    }
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    for arm in [then, otherwise] {
                        let id = *next_try;
                        *next_try += 1;
                        region_stack.push(id);
                        rewrite(
                            arm,
                            true,
                            region_stack,
                            next_try,
                            convert,
                            declared_now,
                            stats,
                        );
                        region_stack.pop();
                    }
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => rewrite(
                    body,
                    false,
                    region_stack,
                    next_try,
                    convert,
                    declared_now,
                    stats,
                ),
                SNode::Labeled { body, .. } => {
                    let id = *next_try;
                    *next_try += 1;
                    region_stack.push(id);
                    rewrite(
                        body,
                        true,
                        region_stack,
                        next_try,
                        convert,
                        declared_now,
                        stats,
                    );
                    region_stack.pop();
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    let id = *next_try;
                    *next_try += 1;
                    region_stack.push(id);
                    rewrite(
                        body,
                        true,
                        region_stack,
                        next_try,
                        convert,
                        declared_now,
                        stats,
                    );
                    region_stack.pop();
                    for c in catches {
                        let id = *next_try;
                        *next_try += 1;
                        region_stack.push(id);
                        rewrite(
                            &mut c.body,
                            true,
                            region_stack,
                            next_try,
                            convert,
                            declared_now,
                            stats,
                        );
                        region_stack.pop();
                    }
                    if let Some(f) = finally {
                        let id = *next_try;
                        *next_try += 1;
                        region_stack.push(id);
                        rewrite(
                            f,
                            true,
                            region_stack,
                            next_try,
                            convert,
                            declared_now,
                            stats,
                        );
                        region_stack.pop();
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        rewrite(
                            &mut c.body,
                            false,
                            region_stack,
                            next_try,
                            convert,
                            declared_now,
                            stats,
                        );
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    let mut next_try = 1usize;
    rewrite(
        nodes,
        true,
        &mut Vec::new(),
        &mut next_try,
        &convert,
        &mut declared_now,
        stats,
    );
}

// ── N74-W4: rest-parameter reconstruction ──────────────────────────
//
// es2abc lowers `(...rest)` / `(a, ...rest)` to `copyrestargs k` (k =
// the named-parameter count) plus ONE extra frame slot past the named
// params (the rest array's staging slot — recover sees it as a spurious
// trailing visible parameter `pN`). The generic emission prints
// `[...arguments].slice(k) /*CopyRestArgs*/` — wrong in arrows and
// closures (`arguments` is the OUTER function's; test262's
// arrowparameters-cover-rest rows read the outer script's empty
// arguments) and wrong for `.length` (the spurious slot inflates it —
// rest-parameters/expected-argument-count). When the body holds exactly
// one `CopyRestArgs` shape, rewrite it to a real rest parameter: every
// `Expr::RestArgs` becomes the rest name, the visible params at-or-past
// `k` drop (the staging slot), and `...<name>` joins the printed
// signature. Bails — keeping the loud approximation — when any dropped
// parameter is referenced in the body.

/// Apply `f` to every expression position in the tree (leaves AND
/// node conditions — the mutation counterpart of the use-census walk).
fn map_exprs_mut(nodes: &mut [SNode], f: &mut impl FnMut(&mut Expr)) {
    fn one_expr(e: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
        f(e);
        for c in expr_children_mut(e) {
            one_expr(c, f);
        }
    }
    fn one_leaf(l: &mut Leaf, f: &mut impl FnMut(&mut Expr)) {
        match l {
            Leaf::Raw(s) => match s {
                Stmt::Declare { value, .. }
                | Stmt::PhiAssign { value, .. }
                | Stmt::Expr(value)
                | Stmt::Throw(value) => one_expr(value, f),
                Stmt::Return(Some(e)) => one_expr(e, f),
                Stmt::StoreProp { object, value, .. } => {
                    one_expr(object, f);
                    one_expr(value, f);
                }
                Stmt::StoreIndex {
                    object,
                    index,
                    value,
                    ..
                } => {
                    one_expr(object, f);
                    one_expr(index, f);
                    one_expr(value, f);
                }
                Stmt::StoreDyn {
                    object, key, value, ..
                } => {
                    one_expr(object, f);
                    one_expr(key, f);
                    one_expr(value, f);
                }
                Stmt::DefineMethod { object, func, .. } => {
                    one_expr(object, f);
                    one_expr(func, f);
                }
                Stmt::StorePrivate { object, value, .. } => {
                    one_expr(object, f);
                    one_expr(value, f);
                }
                Stmt::StoreSuper { key, value, .. } => {
                    if let Some(k) = key {
                        one_expr(k, f);
                    }
                    one_expr(value, f);
                }
                Stmt::LexStore { value, .. }
                | Stmt::GlobalStore { value, .. }
                | Stmt::ModuleStore { value, .. } => one_expr(value, f),
                Stmt::CondBranch { cond, .. } => one_expr(cond, f),
                _ => {}
            },
            Leaf::Destructure { obj, .. } => one_expr(obj, f),
            Leaf::Decl { value: Some(v), .. } => one_expr(v, f),
            Leaf::Decl { value: None, .. } => {}
            Leaf::Assign { value, .. } => one_expr(value, f),
        }
    }
    for n in nodes {
        match n {
            SNode::Stmts(run) => {
                for l in run {
                    one_leaf(l, f);
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                one_expr(cond, f);
                map_exprs_mut(then, f);
                map_exprs_mut(otherwise, f);
            }
            SNode::While { cond, body, .. } => {
                if let Some(c) = cond {
                    one_expr(c, f);
                }
                map_exprs_mut(body, f);
            }
            SNode::DoWhile { body, cond, .. } => {
                map_exprs_mut(body, f);
                one_expr(cond, f);
            }
            SNode::Labeled { body, .. } => map_exprs_mut(body, f),
            SNode::ForOf { iter, body, .. } => {
                one_expr(iter, f);
                map_exprs_mut(body, f);
            }
            SNode::ForIn { obj, body, .. } => {
                one_expr(obj, f);
                map_exprs_mut(body, f);
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                map_exprs_mut(body, f);
                for c in catches {
                    map_exprs_mut(&mut c.body, f);
                }
                if let Some(fin) = finally {
                    map_exprs_mut(fin, f);
                }
            }
            SNode::Switch { disc, cases } => {
                one_expr(disc, f);
                for c in cases {
                    for t in &mut c.tests {
                        one_expr(t, f);
                    }
                    map_exprs_mut(&mut c.body, f);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// See the section comment. Mutates `params` (drops the staging slots,
/// appends `...<rest>`) and rewrites the body's `RestArgs` exprs.
/// `hidden` is the ABI-slot count (`params[hidden..]` are visible).
pub fn rest_param_fold(
    nodes: &mut [SNode],
    params: &mut Vec<String>,
    hidden: usize,
    stats: &mut FoldStats,
) {
    // Exactly one CopyRestArgs shape?
    let mut starts = BTreeSet::new();
    map_exprs_mut(nodes, &mut |e| {
        if let Expr::RestArgs { start_index } = e {
            starts.insert(*start_index);
        }
    });
    let collected: Vec<u16> = starts.into_iter().collect();
    let [k] = collected[..] else {
        return;
    };
    let k = k as usize;
    let visible = params.len() - hidden.min(params.len());
    if visible < k {
        return; // shape mismatch — keep the approximation
    }
    // The dropped slots (the staging slot + anything past it) must be
    // unreferenced.
    let dropped: Vec<String> = params[hidden + k..].to_vec();
    let mut dropped_used = false;
    map_exprs_mut(nodes, &mut |e| {
        if let Expr::Ident(n) = e
            && dropped.iter().any(|d| d == n)
        {
            dropped_used = true;
        }
    });
    if dropped_used {
        return;
    }
    // Mint a collision-free rest name over every name the body knows.
    let mut taken: BTreeSet<String> = params.iter().cloned().collect();
    map_exprs_mut(nodes, &mut |e| match e {
        Expr::Ident(n) => {
            taken.insert(n.clone());
        }
        Expr::Temp { name, .. } => {
            taken.insert(name.clone());
        }
        _ => {}
    });
    walk_leaves(nodes, &mut |l| match l {
        Leaf::Raw(Stmt::Declare { name, .. }) | Leaf::Raw(Stmt::PhiDecl { name, .. }) => {
            taken.insert(name.clone());
        }
        Leaf::Raw(Stmt::PhiAssign { target, .. }) => {
            taken.insert(target.clone());
        }
        Leaf::Raw(Stmt::LexStore { name, .. }) | Leaf::Raw(Stmt::GlobalStore { name, .. }) => {
            taken.insert(crate::legalize::sanitize(name));
        }
        Leaf::Decl { name, .. } => {
            taken.insert(name.clone());
        }
        Leaf::Assign { target, .. } => {
            taken.insert(target.clone());
        }
        _ => {}
    });
    let mut rest = "rest".to_string();
    let mut i = 1usize;
    while taken.contains(&rest) {
        rest = format!("rest${i}");
        i += 1;
    }
    // Rewrite. A bare `rest;` expression-statement (an unused
    // CopyRestArgs result — keep-alive evidence, recover.rs) is
    // consumed, not rewritten.
    let rest_expr = Expr::Ident(rest.clone());
    fn strip_bare_rest(nodes: &mut [SNode]) {
        for n in nodes.iter_mut() {
            match n {
                SNode::Stmts(run) => {
                    run.retain(|l| !matches!(l, Leaf::Raw(Stmt::Expr(Expr::RestArgs { .. }))));
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    strip_bare_rest(then);
                    strip_bare_rest(otherwise);
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => strip_bare_rest(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    strip_bare_rest(body);
                    for c in catches {
                        strip_bare_rest(&mut c.body);
                    }
                    if let Some(f) = finally {
                        strip_bare_rest(f);
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        strip_bare_rest(&mut c.body);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    strip_bare_rest(nodes);
    map_exprs_mut(nodes, &mut |e| {
        if matches!(e, Expr::RestArgs { .. }) {
            *e = rest_expr.clone();
        }
    });
    params.truncate(hidden + k);
    params.push(format!("...{rest}"));
    stats.rest_param += 1;
}

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
struct GenDriverCx {
    /// The single `CreateGenerator` result value (the funcObj temp).
    genobj: ValueId,
    /// Pure number-constant temps (`const t = 0.0` — the optimized
    /// profile materializes the mode immediates) by value id.
    const_env: BTreeMap<ValueId, u64>,
    /// Const temps a successful dispatch match resolved (sweep
    /// candidates once their uses are gone).
    consumed_consts: BTreeSet<ValueId>,
}

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

fn async_fold_seq(
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
fn fold_async_run(
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

/// The entry-site validity check (immutable): find the sequence where
/// the run declaring the CreateGenerator temp sits next to its
/// dispatch, and verify the full site shape.
fn entry_site_matches(nodes: &[SNode], cx: &mut GenDriverCx) -> bool {
    for i in 0..nodes.len().saturating_sub(1) {
        if let Some(site) = match_driver_site(nodes, i, cx)
            && site.entry
            && site.genobj == cx.genobj
            && !nodes_use_temp(&site.continuation, site.resume)
        {
            return true;
        }
    }
    nodes.iter().any(|n| match n {
        SNode::If {
            then, otherwise, ..
        } => entry_site_matches(then, cx) || entry_site_matches(otherwise, cx),
        SNode::While { body, .. }
        | SNode::DoWhile { body, .. }
        | SNode::Labeled { body, .. }
        // unreachable: ForOf/ForIn nodes are created only inside fold()
        // (folds.rs:1418/1433/2577), which runs after
        // generator_machine_fold (emit.rs:508 vs 531) — c-COV diagnosis
        | SNode::ForOf { body, .. }
        | SNode::ForIn { body, .. } => entry_site_matches(body, cx),
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            entry_site_matches(body, cx)
                || catches.iter().any(|c| entry_site_matches(&c.body, cx))
                || finally.as_ref().is_some_and(|f| entry_site_matches(f, cx))
        }
        // unreachable: SNode::Switch is created only by fold_switches
        // (folds.rs:3115/3183) inside fold(), which runs after
        // generator_machine_fold — c-COV diagnosis
        SNode::Switch { cases, .. } => cases.iter().any(|c| entry_site_matches(&c.body, cx)),
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => false,
    })
}

/// One matched driver site (immutable match; applied separately).
struct DriverSite {
    /// The funcObj temp the site's pair resumes (`== cx.genobj`).
    genobj: ValueId,
    /// The `ResumeGenerator` temp (the completion value).
    resume: ValueId,
    /// The resume temp's legalized name (for the `x = yield v` bind).
    resume_name: String,
    /// `true` for the entry protocol suspend (bare `yield undefined`
    /// next to the CreateGenerator decl).
    entry: bool,
    /// The folded yield value for real yield points (the opened
    /// iter-result); `None` at the entry site.
    yield_value: Option<Expr>,
    /// The dispatch's continuation (the real control flow).
    continuation: Vec<SNode>,
}

/// Match `nodes[i]` (a `Stmts` run ending in
/// `[yield-stmt, decl r = ResumeGenerator(g), decl m =
/// GetResumeMode(g)]`) + `nodes[i+1]` (the mode dispatch on `m`).
fn match_driver_site(nodes: &[SNode], i: usize, cx: &mut GenDriverCx) -> Option<DriverSite> {
    let SNode::Stmts(run) = &nodes[i] else {
        return None;
    };
    let [
        ..,
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
    ] = run.as_slice()
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
        continuation,
    })
}

/// Match the resume-mode dispatch (`HandleCompletion`): a chain of
/// `mode == RETURN(0)` / `mode == THROW(1)` tests (either polarity,
/// either order, immediates inline or via pure const temps) whose case
/// arms are exactly `return <resume>` / `throw <resume>`; the
/// remaining arm after both tests is the continuation.
fn match_dispatch(
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
        // dispatch is exactly the next test, optionally preceded by a
        // run of pure number-const decls (the optimized profile
        // materializes the second immediate there).
        cur = match cont.as_slice() {
            [SNode::If { .. }] => &cont[0],
            [SNode::Stmts(run), SNode::If { .. }]
                if run.iter().all(|l| {
                    matches!(
                        l,
                        Leaf::Raw(Stmt::Declare {
                            value: Expr::Lit(Lit::Number(_)),
                            ..
                        })
                    )
                }) =>
            {
                &cont[1]
            }
            _ => return None,
        };
    }
}

/// A dispatch test: `(isfalse|istrue)* (mode == <number>)` in either
/// operand order; returns the immediate's bits and the polarity
/// (`true` = the case body is the THEN arm).
fn mode_test(
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
fn resolve_num(
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
fn check_return_arm(arm: &[SNode], resume: ValueId) -> Option<()> {
    let [SNode::Stmts(run), rest @ ..] = arm else {
        return None;
    };
    if !rest.iter().all(|n| matches!(n, SNode::Break { .. })) {
        return None;
    }
    let [Leaf::Raw(Stmt::Return(Some(value)))] = run.as_slice() else {
        return None;
    };
    (temp_value(value) == Some(resume)).then_some(())
}

/// The THROW arm: exactly `throw <resume>;` (+ the dead `Unreachable`
/// and any dead loop-bookkeeping `break`s).
fn check_throw_arm(arm: &[SNode], resume: ValueId) -> Option<()> {
    let [SNode::Stmts(run), rest @ ..] = arm else {
        return None;
    };
    if !rest.iter().all(|n| matches!(n, SNode::Break { .. })) {
        return None;
    }
    match run.as_slice() {
        [Leaf::Raw(Stmt::Throw(value))]
        | [Leaf::Raw(Stmt::Throw(value)), Leaf::Raw(Stmt::Unreachable)] => {
            (temp_value(value) == Some(resume)).then_some(())
        }
        _ => None,
    }
}

/// The rewrite pass: children first (inner sites fold before the
/// outer sites that contain them), then the sequence scan.
fn gen_fold_seq(nodes: &mut Vec<SNode>, cx: &mut GenDriverCx, stats: &mut FoldStats) {
    for n in nodes.iter_mut() {
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                gen_fold_seq(then, cx, stats);
                gen_fold_seq(otherwise, cx, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577), which runs after
            // generator_machine_fold (emit.rs:508 vs 531) — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => gen_fold_seq(body, cx, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                gen_fold_seq(body, cx, stats);
                for c in catches {
                    gen_fold_seq(&mut c.body, cx, stats);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after
                // generator_machine_fold — c-COV diagnosis
                if let Some(f) = finally {
                    gen_fold_seq(f, cx, stats);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after
            // generator_machine_fold — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    gen_fold_seq(&mut c.body, cx, stats);
                }
            }
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
    let mut i = 0;
    while i + 1 < nodes.len() {
        let site = match_driver_site(nodes, i, cx);
        match site {
            Some(site) if site.genobj == cx.genobj => {
                let SNode::Stmts(run) = &mut nodes[i] else {
                    unreachable!()
                };
                // Pop the GetResumeMode/ResumeGenerator decl pair.
                run.pop();
                run.pop();
                if site.entry {
                    // The entry protocol suspend is invisible in
                    // source; its resume value is dead (entry gate).
                    run.pop();
                    stats.gen_driver_entry += 1;
                } else {
                    let v = site.yield_value.expect("yield site carries a value");
                    let leaf = run.last_mut().expect("the yield stmt");
                    if nodes_use_temp(&site.continuation, site.resume) {
                        // `x = yield v` — the resumption value has
                        // real uses; bind the temp at the yield site.
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
                nodes.splice(i + 1..i + 2, site.continuation);
                i += 1;
            }
            _ => i += 1,
        }
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
struct AsyncMachineCx {
    /// The unique `AsyncFunctionEnter` fallback temp (the funcObj).
    genobj: ValueId,
    /// N70: the funcObj plus its loop-header phi aliases (the constant
    /// funcObj routed through bookkeeping phis in loop-driving bodies).
    aliases: BTreeSet<ValueId>,
    /// N70: temps thrown at some loop's structural continuation (the
    /// verified break-routing targets for the loop-exit dispatch).
    exit_throws: BTreeSet<ValueId>,
    /// Pure number-constant temps (the mode immediate, when the
    /// profile materializes it) by value id.
    const_env: BTreeMap<ValueId, u64>,
    /// Const temps a successful dispatch match resolved.
    consumed_consts: BTreeSet<ValueId>,
    /// Whole-tree temp use counts, computed once up front (the fold
    /// only REMOVES the counted machinery uses, so the counts stay
    /// valid for the per-site dead-resume decisions).
    uses: BTreeMap<ValueId, usize>,
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
fn funcobj_aliases(nodes: &[SNode], genobj: ValueId) -> BTreeSet<ValueId> {
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
fn collect_loop_exit_throws(nodes: &[SNode]) -> BTreeSet<ValueId> {
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
fn funcobj_uses_are_machinery(nodes: &[SNode], aliases: &BTreeSet<ValueId>) -> bool {
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
struct AsyncSite {
    /// Run leaf indices of the machinery leaves (descending).
    remove: Vec<usize>,
    /// Offset of the dispatch node from the machinery run (1 + the
    /// number of intervening phi-partition runs).
    dispatch_off: usize,
    /// The awaited value expression (moved into the folded `await`).
    awaited: Expr,
    /// The resume temp binding, when the `ResumeGenerator` result was
    /// a declared temp (always in practice: its uses live in sibling
    /// blocks, so Stage A never inlines it).
    resume: Option<(ValueId, String)>,
    /// The dispatch's continuation (the real control flow).
    continuation: Vec<SNode>,
}

/// The index of the previous non-phi-assign leaf before `cur`
/// (block-end phi materializations interleave with the machinery).
fn prev_non_phi(run: &[Leaf], cur: &mut usize) -> Option<usize> {
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
fn match_await_site(nodes: &[SNode], i: usize, cx: &mut AsyncMachineCx) -> Option<AsyncSite> {
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
fn match_async_dispatch(
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
fn check_async_throw_arm(
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
fn check_async_break_arm(
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
fn async_machine_seq(nodes: &mut Vec<SNode>, cx: &mut AsyncMachineCx, stats: &mut FoldStats) {
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
fn sweep_async_machinery(
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
fn strip_genobj_phi_assigns(
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
fn strip_dead_phi_decls(
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
fn agen_uses_are_machinery(nodes: &[SNode], genobj: ValueId) -> bool {
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
fn agen_entry_elide(nodes: &mut [SNode], genobj: ValueId, stats: &mut FoldStats) -> bool {
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
struct AGYieldSite {
    /// The matched pre-yield await site (machinery leaf indices,
    /// dispatch offset, awaited operand).
    await_site: AsyncSite,
    /// The yield-point resumption value temp and its legalized name
    /// (for the `x = yield v` bind).
    ry: ValueId,
    /// `ry`'s declared name.
    ry_name: String,
    /// The NEXT arm (the real control flow).
    continuation: Vec<SNode>,
}

/// The rewrite pass: children first (inner sites fold before the
/// outer sites whose continuations contain them), then per-run
/// completion folds, then the sequence scan (yield site →
/// explicit-return site → plain await site).
fn agen_fold_seq(nodes: &mut Vec<SNode>, cx: &mut AsyncMachineCx, stats: &mut FoldStats) {
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
fn agen_fold_run(run: &mut Vec<Leaf>, genobj: ValueId, stats: &mut FoldStats) {
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
fn match_ag_yield(nodes: &[SNode], i: usize, cx: &mut AsyncMachineCx) -> Option<AGYieldSite> {
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
fn phi_only_run(n: &SNode) -> bool {
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
fn match_ag_three_way(
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
fn ag_mode_test(cond: &Expr, my: Option<ValueId>, cx: &mut AsyncMachineCx) -> Option<(u64, bool)> {
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
fn check_ag_return_arm(arm: &[SNode], ry: ValueId) -> Option<()> {
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
fn match_ag_await(nodes: &[SNode], i: usize, cx: &mut AsyncMachineCx) -> Option<AsyncSite> {
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

/// Walk every leaf of a structured tree (immutable).
fn walk_leaves(nodes: &[SNode], f: &mut impl FnMut(&Leaf)) {
    for n in nodes {
        match n {
            SNode::Stmts(run) => run.iter().for_each(&mut *f),
            SNode::If {
                then, otherwise, ..
            } => {
                walk_leaves(then, f);
                walk_leaves(otherwise, f);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => walk_leaves(body, f),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                walk_leaves(body, f);
                for c in catches {
                    walk_leaves(&c.body, f);
                }
                if let Some(fin) = finally {
                    walk_leaves(fin, f);
                }
            }
            SNode::Switch { cases, .. } => {
                for c in cases {
                    walk_leaves(&c.body, f);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// Does any expression in the tree reference the given temp value?
/// N74-W4: node CONDITION/discriminant expressions count too —
/// `walk_leaves` never visits them, which dropped the `const t = yield
/// v` binding when the resumption value was only read by an `if`/`while`
/// test (test262 methods-gen-yield-as-expression-*: `if (!v388)`).
fn nodes_use_temp(nodes: &[SNode], id: ValueId) -> bool {
    fn expr_uses(e: &Expr, id: ValueId) -> bool {
        if temp_value(e) == Some(id) {
            return true;
        }
        expr_children(e).iter().any(|c| expr_uses(c, id))
    }
    fn node_uses(n: &SNode, id: ValueId) -> bool {
        match n {
            SNode::Stmts(run) => run
                .iter()
                .any(|l| leaf_exprs(l).iter().any(|e| expr_uses(e, id))),
            SNode::If {
                cond,
                then,
                otherwise,
            } => expr_uses(cond, id) || nodes_use_temp(then, id) || nodes_use_temp(otherwise, id),
            SNode::While { cond, body, .. } => {
                cond.as_ref().is_some_and(|c| expr_uses(c, id)) || nodes_use_temp(body, id)
            }
            SNode::DoWhile { body, cond, .. } => nodes_use_temp(body, id) || expr_uses(cond, id),
            SNode::Labeled { body, .. } => nodes_use_temp(body, id),
            SNode::ForOf { iter, body, .. } => expr_uses(iter, id) || nodes_use_temp(body, id),
            SNode::ForIn { obj, body, .. } => expr_uses(obj, id) || nodes_use_temp(body, id),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                nodes_use_temp(body, id)
                    || catches.iter().any(|c| nodes_use_temp(&c.body, id))
                    || finally.as_ref().is_some_and(|f| nodes_use_temp(f, id))
            }
            SNode::Switch { disc, cases } => {
                expr_uses(disc, id)
                    || cases.iter().any(|c| {
                        c.tests.iter().any(|t| expr_uses(t, id)) || nodes_use_temp(&c.body, id)
                    })
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => false,
        }
    }
    nodes.iter().any(|n| node_uses(n, id))
}

/// Count temp references over the whole tree (for the dead-decl sweep).
fn count_temp_uses(nodes: &[SNode], uses: &mut BTreeMap<ValueId, usize>) {
    fn count_expr(e: &Expr, uses: &mut BTreeMap<ValueId, usize>) {
        if let Expr::Temp { value, .. } = e {
            *uses.entry(*value).or_insert(0) += 1;
        }
        for c in expr_children(e) {
            count_expr(c, uses);
        }
    }
    walk_leaves(nodes, &mut |l| {
        for e in leaf_exprs(l) {
            count_expr(e, uses);
        }
    });
}

/// Remove `Declare` leaves whose SSA value is in `dead` (callers prove
/// zero remaining uses first).
fn sweep_dead_decls(nodes: &mut [SNode], dead: &BTreeSet<ValueId>) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => run.retain(|l| {
                !matches!(
                    l,
                    Leaf::Raw(Stmt::Declare { value_id, .. }) if dead.contains(value_id)
                )
            }),
            SNode::If {
                then, otherwise, ..
            } => {
                sweep_dead_decls(then, dead);
                sweep_dead_decls(otherwise, dead);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            // unreachable: ForOf/ForIn nodes are created only inside fold()
            // (folds.rs:1418/1433/2577); sweep_dead_decls runs only from the
            // generator/async machine folds, all before fold() — c-COV diagnosis
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => sweep_dead_decls(body, dead),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                sweep_dead_decls(body, dead);
                for c in catches {
                    sweep_dead_decls(&mut c.body, dead);
                }
                // unreachable: Try.finally is Some only after fold_finally
                // (folds.rs:4143/4154) inside fold(), which runs after the
                // generator/async machine folds — c-COV diagnosis
                if let Some(f) = finally {
                    sweep_dead_decls(f, dead);
                }
            }
            // unreachable: SNode::Switch is created only by fold_switches
            // (folds.rs:3115/3183) inside fold(), which runs after the
            // generator/async machine folds — c-COV diagnosis
            SNode::Switch { cases, .. } => {
                for c in cases {
                    sweep_dead_decls(&mut c.body, dead);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// The expressions a leaf carries (for temp-use walks).
fn leaf_exprs(l: &Leaf) -> Vec<&Expr> {
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
struct YsLoop {
    /// Loop phi: the resumption mode (`receivedType`).
    rt: (ValueId, String),
    /// Loop phi: the resumption value (`received`).
    rv: (ValueId, String),
    /// Loop phi: the delegate iterator.
    it: (ValueId, String),
    /// Loop phi: the generator object.
    g: (ValueId, String),
    /// Loop phi: the close-attempt flag.
    flag: (ValueId, String),
    /// The `exitReturn` phi tested by the completion dispatch.
    exit_phi: (ValueId, String),
    /// The completion-value binding + continuation (async: extracted
    /// from the done arm inside the loop; sync: from the sibling
    /// completion dispatch — filled by [`ys_match_exit`]).
    bind: Option<(String, ValueId)>,
    /// The post-delegation continuation (async: done-arm content).
    continuation: Vec<SNode>,
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
fn ys_fold_seq(
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
fn ys_is_exc_run(n: &SNode) -> bool {
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
fn ys_sig(nodes: &[SNode]) -> Vec<&SNode> {
    nodes.iter().filter(|n| !ys_is_exc_run(n)).collect()
}

/// A run of phi assigns whose NON-exceptional members all target one
/// block (exceptional catch-context assigns may be interspersed —
/// they are machinery plumbing); returns that block.
fn ys_assign_run(n: &SNode) -> Option<abcd_ir::BlockId> {
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
fn ys_phi_decls(n: &SNode) -> Option<BTreeMap<String, ValueId>> {
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
fn ys_mode_test(cond: &Expr, want: f64) -> Option<ValueId> {
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
fn ys_flag_test(cond: &Expr) -> Option<(ValueId, bool)> {
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
fn ys_undefined_test(cond: &Expr) -> Option<(ValueId, bool)> {
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
fn ys_trace(stage: &str) {
    if std::env::var_os("YS_DEBUG").is_some() {
        eprintln!("yield-star: bail at {stage}");
    }
}

/// A `GeneratorDriver` expr with the given resume flag and genobj temp.
fn ys_driver(e: &Expr, resume: bool, g: ValueId) -> bool {
    matches!(
        e,
        Expr::GeneratorDriver { resume: r, genobj }
            if *r == resume && temp_value(genobj) == Some(g)
    )
}

/// A `PropName` load `<base>.<name>`; returns the base temp.
fn ys_prop(e: &Expr, name: &str) -> Option<ValueId> {
    let Expr::PropName {
        object, name: n, ..
    } = e
    else {
        return None;
    };
    (n == name).then(|| temp_value(object))?
}

/// A Declare leaf with the given value shape; returns (name, id).
fn ys_declare_of(l: &Leaf) -> Option<(&str, ValueId, &Expr)> {
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
fn ys_contains_elided(nodes: &[SNode], op: &str) -> bool {
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
fn ys_match_loop(w: &SNode, async_: bool) -> Option<YsLoop> {
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
fn ys_match_return_arm(
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
fn ys_match_throw_arm(
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
fn ys_match_loop_tail_sync(
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
fn ys_match_loop_tail_async(
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
fn ys_async_throw_dispatch(
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
fn ys_match_async_yield(
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
fn ys_mode_neq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::Eq)
}

/// `IsFalse(NotEq(Temp(m), num))` — mode == num.
fn ys_mode_eq_test(cond: &Expr, m: ValueId, num: f64) -> Option<()> {
    ys_mode_num_test(cond, m, num, CmpOp::NotEq)
}

fn ys_mode_num_test(cond: &Expr, m: ValueId, num: f64, op: CmpOp) -> Option<()> {
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
fn ys_loopback(
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
type ExitMatch = (Option<(String, ValueId)>, Vec<SNode>);

/// Match the sync completion dispatch sitting right after the loop:
/// `if (!exitReturn) { value = res.value; <continuation> } else {
/// v2 = res.value; return v2 }`. Returns the binding (when the
/// completion value is used) and the continuation.
fn ys_match_exit(n: &SNode, exit_phi: ValueId, res: ValueId) -> Option<ExitMatch> {
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
fn ys_match_setup(
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
fn ys_match_init(n: &SNode, lp: &YsLoop, iter: ValueId, next: ValueId) -> Option<()> {
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
fn ys_stmt(lp: &YsLoop, delegate: Expr) -> SNode {
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
fn ys_apply_bare(
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
fn ys_sync_res(w: &SNode) -> Option<ValueId> {
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
fn ys_innermost_body_mut(t: &mut SNode) -> &mut Vec<SNode> {
    let SNode::Try { body, .. } = t else {
        unreachable!()
    };
    if body.len() == 1 && matches!(body[0], SNode::Try { .. }) {
        let inner = &mut body[0];
        return ys_innermost_body_mut(inner);
    }
    body
}

fn ys_innermost_body(t: &SNode) -> Option<&Vec<SNode>> {
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
fn ys_apply_fragments(
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

// ── c-COV W7: coverage tests ─────────────────────────────────────────
//
// In-module unit tests for the fold internals: hand-built SNode/Leaf
// trees driven through the private matchers and the public fold entry
// points. Organized by fixture family (see the c-COV folds diagnosis):
// the finally-idiom family, the for-await driver family, rest-param and
// late-decl control-flow variants, the switch-chain extension loop,
// do-while/labeled walker co-occurrence, optimized-profile async
// shapes, computed-key/`__proto__` literal builders, and per-matcher
// near-miss bail pins (one mutation per checkpoint group, not per
// line).
#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{ArrayElem, NodeStatus, ObjKey};
    use crate::structure::CatchClause;
    use abcd_ir::op::{BinOp, CallKind};
    use abcd_ir::{BlockId, ConstId, FuncId};

    // ── shape builders ─────────────────────────────────────────────

    fn bx(e: Expr) -> Box<Expr> {
        Box::new(e)
    }
    /// A temp reference (name + SSA id kept consistent by convention).
    fn tm(name: &str, vid: u32) -> Expr {
        Expr::Temp {
            value: ValueId::new(vid),
            name: name.to_string(),
        }
    }
    fn ident(name: &str) -> Expr {
        Expr::Ident(name.to_string())
    }
    fn num(x: f64) -> Expr {
        Expr::Lit(Lit::Number(x.to_bits()))
    }
    fn boolean(b: bool) -> Expr {
        Expr::Lit(Lit::Bool(b))
    }
    fn strlit(s: &str) -> Expr {
        Expr::Lit(Lit::String(s.to_string()))
    }
    fn undef() -> Expr {
        Expr::Lit(Lit::Undefined)
    }
    fn decl(name: &str, vid: u32, value: Expr) -> Leaf {
        Leaf::Raw(Stmt::Declare {
            name: name.to_string(),
            mutable: false,
            value,
            value_id: ValueId::new(vid),
        })
    }
    fn phi_decl(name: &str, vid: u32) -> Leaf {
        Leaf::Raw(Stmt::PhiDecl {
            name: name.to_string(),
            value_id: ValueId::new(vid),
        })
    }
    fn phi_assign(target: &str, value: Expr) -> Leaf {
        Leaf::Raw(Stmt::PhiAssign {
            target: target.to_string(),
            value,
            to: BlockId::new(7),
            exceptional: false,
        })
    }
    fn exc_assign(target: &str, value: Expr) -> Leaf {
        Leaf::Raw(Stmt::PhiAssign {
            target: target.to_string(),
            value,
            to: BlockId::new(9),
            exceptional: true,
        })
    }
    fn expr_stmt(e: Expr) -> Leaf {
        Leaf::Raw(Stmt::Expr(e))
    }
    fn elided(op: &'static str) -> Leaf {
        Leaf::Raw(Stmt::Elided {
            op,
            reason: "test guard",
            loc: None,
        })
    }
    fn run(leaves: Vec<Leaf>) -> SNode {
        SNode::Stmts(leaves)
    }
    fn if_node(cond: Expr, then: Vec<SNode>, otherwise: Vec<SNode>) -> SNode {
        SNode::If {
            cond,
            then,
            otherwise,
        }
    }
    fn isfalse(e: Expr) -> Expr {
        Expr::Unary {
            op: UnOp::IsFalse,
            operand: bx(e),
        }
    }
    fn istrue(e: Expr) -> Expr {
        Expr::Unary {
            op: UnOp::IsTrue,
            operand: bx(e),
        }
    }
    fn cmp(op: CmpOp, l: Expr, r: Expr) -> Expr {
        Expr::Compare {
            op,
            left: bx(l),
            right: bx(r),
        }
    }
    fn prop(base: Expr, name: &str) -> Expr {
        Expr::PropName {
            object: bx(base),
            name: name.to_string(),
            dot_legal: true,
        }
    }
    fn call0(callee: Expr) -> Expr {
        Expr::Call {
            callee: bx(callee),
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        }
    }
    fn call1(callee: Expr, arg: Expr) -> Expr {
        Expr::Call {
            callee: bx(callee),
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        }
    }
    fn catch(binding: &str, body: Vec<SNode>) -> CatchClause {
        CatchClause {
            binding: Some(binding.to_string()),
            body,
        }
    }
    fn try_node(body: Vec<SNode>, catches: Vec<CatchClause>) -> SNode {
        SNode::Try {
            body,
            catches,
            note: None,
            finally: None,
        }
    }

    // ── name/expr walkers: every statement & expression kind ───────

    /// Statements carrying one temp `x`/42 in each expression position.
    fn stmts_with_x() -> Vec<Stmt> {
        let x = || tm("x", 42);
        vec![
            Stmt::Declare {
                name: "d".to_string(),
                mutable: false,
                value: x(),
                value_id: ValueId::new(1),
            },
            Stmt::PhiAssign {
                target: "p".to_string(),
                value: x(),
                to: BlockId::new(3),
                exceptional: false,
            },
            Stmt::Expr(x()),
            Stmt::Throw(x()),
            Stmt::Return(Some(x())),
            Stmt::StoreProp {
                object: x(),
                name: "k".to_string(),
                dot_legal: true,
                value: ident("y"),
                own: false,
            },
            Stmt::StoreIndex {
                object: ident("y"),
                index: x(),
                value: ident("y"),
                own: false,
            },
            Stmt::StoreDyn {
                object: ident("y"),
                key: ident("y"),
                value: x(),
                own: false,
            },
            Stmt::DefineMethod {
                object: x(),
                name: "m".to_string(),
                func: ident("f"),
                length: 0,
            },
            Stmt::StorePrivate {
                object: ident("y"),
                name: "p".to_string(),
                value: x(),
                define: false,
            },
            Stmt::StoreSuper {
                name: None,
                key: Some(x()),
                value: ident("y"),
            },
            Stmt::StoreSuper {
                name: Some("k".to_string()),
                key: None,
                value: x(),
            },
            Stmt::LexStore {
                level: 0,
                slot: 0,
                name: "l".to_string(),
                value: x(),
            },
            Stmt::GlobalStore {
                name: "g".to_string(),
                value: x(),
                tolerant: false,
            },
            Stmt::ModuleStore {
                index: 0,
                name: "m0".to_string(),
                value: x(),
            },
            Stmt::CondBranch {
                cond: x(),
                true_dest: BlockId::new(1),
                false_dest: BlockId::new(2),
            },
        ]
    }

    #[test]
    fn name_use_walkers_cover_every_statement_kind() {
        for s in stmts_with_x() {
            assert!(stmt_uses_name(&s, "x"), "{s:?}");
            assert!(!stmt_uses_name(&s, "absent"), "{s:?}");
        }
        // Binding-position name matches.
        assert!(stmt_uses_name(
            &Stmt::Declare {
                name: "x".to_string(),
                mutable: true,
                value: ident("y"),
                value_id: ValueId::new(1),
            },
            "x"
        ));
        assert!(stmt_uses_name(
            &Stmt::PhiDecl {
                name: "x".to_string(),
                value_id: ValueId::new(1),
            },
            "x"
        ));
        assert!(stmt_uses_name(
            &Stmt::PhiAssign {
                target: "x".to_string(),
                value: ident("y"),
                to: BlockId::new(3),
                exceptional: false,
            },
            "x"
        ));
        assert!(stmt_uses_name(
            &Stmt::LexStore {
                level: 0,
                slot: 0,
                name: "x".to_string(),
                value: ident("y"),
            },
            "x"
        ));
        // The catch-all arm: statements without expression positions.
        for s in [
            Stmt::Return(None),
            Stmt::ScopePop,
            Stmt::Unreachable,
            Stmt::Debugger,
            Stmt::Branch {
                dest: BlockId::new(0),
            },
            Stmt::CatchBind {
                name: "x".to_string(),
            },
        ] {
            assert!(!stmt_uses_name(&s, "x"), "{s:?}");
        }
        // Leaf-level dispatch arms.
        assert!(leaf_uses_name(
            &Leaf::Destructure {
                obj: tm("x", 42),
                keys: vec![("k".to_string(), "t".to_string())],
                rest: "r".to_string(),
            },
            "x"
        ));
        assert!(!leaf_uses_name(
            &Leaf::Destructure {
                obj: ident("y"),
                keys: vec![],
                rest: "x".to_string(),
            },
            "x"
        ));
        assert!(leaf_uses_name(
            &Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: Some(tm("x", 42)),
            },
            "x"
        ));
        assert!(!leaf_uses_name(
            &Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: None,
            },
            "x"
        ));
        assert!(leaf_uses_name(
            &Leaf::Assign {
                target: "x".to_string(),
                value: ident("y"),
            },
            "x"
        ));
        assert!(leaf_uses_name(
            &Leaf::Assign {
                target: "z".to_string(),
                value: tm("x", 42),
            },
            "x"
        ));
        assert!(leaves_use_name(
            &[Leaf::Assign {
                target: "z".to_string(),
                value: tm("x", 42),
            }],
            "x"
        ));
        // temp_name / temp_value / expr_uses_value primitives.
        assert_eq!(temp_name(&tm("x", 42)), Some("x"));
        assert_eq!(temp_name(&ident("x")), Some("x"));
        assert_eq!(temp_name(&num(1.0)), None);
        assert_eq!(temp_value(&tm("x", 42)), Some(ValueId::new(42)));
        assert_eq!(temp_value(&ident("x")), None);
        assert!(expr_uses_value(&call0(tm("x", 42)), ValueId::new(42)));
        assert!(!expr_uses_value(&call0(tm("x", 42)), ValueId::new(7)));
        assert!(expr_uses_name(&call0(ident("x")), "x"));
        assert!(!expr_uses_name(&num(1.0), "x"));
    }

    /// One specimen per `Expr` variant, with its direct-child count.
    fn all_exprs() -> Vec<(Expr, usize)> {
        vec![
            (Expr::Lit(Lit::Null), 0),
            (ident("a"), 0),
            (tm("t", 1), 0),
            (prop(ident("o"), "n"), 1),
            (
                Expr::PropIndex {
                    object: bx(ident("o")),
                    index: bx(num(0.0)),
                },
                2,
            ),
            (
                Expr::PropDyn {
                    object: bx(ident("o")),
                    key: bx(ident("k")),
                },
                2,
            ),
            (
                Expr::PrivateLoad {
                    object: bx(ident("o")),
                    name: "p".to_string(),
                },
                1,
            ),
            (
                Expr::PrivateTest {
                    object: bx(ident("o")),
                    name: "p".to_string(),
                },
                1,
            ),
            (
                Expr::SuperProp {
                    name: Some("n".to_string()),
                    key: None,
                },
                0,
            ),
            (
                Expr::SuperProp {
                    name: None,
                    key: Some(bx(ident("k"))),
                },
                1,
            ),
            (
                Expr::Call {
                    callee: bx(ident("f")),
                    this: Some(bx(ident("t"))),
                    args: vec![ident("a")],
                    kind: CallKind::Direct,
                },
                3,
            ),
            (call0(ident("f")), 1),
            (Expr::SuperMarker, 0),
            (
                Expr::DynamicImport {
                    specifier: bx(strlit("m")),
                },
                1,
            ),
            (
                Expr::Unary {
                    op: UnOp::LogicalNot,
                    operand: bx(ident("a")),
                },
                1,
            ),
            (
                Expr::Delete {
                    target: bx(ident("a")),
                },
                1,
            ),
            (
                Expr::Binary {
                    op: BinOp::Add,
                    left: bx(ident("a")),
                    right: bx(num(1.0)),
                },
                2,
            ),
            (cmp(CmpOp::Eq, ident("a"), ident("b")), 2),
            (
                Expr::RegExp {
                    pattern: "x".to_string(),
                    flags: "g".to_string(),
                },
                0,
            ),
            (Expr::ObjectLit { entries: vec![] }, 0),
            (Expr::ArrayLit { elements: vec![] }, 0),
            (
                Expr::Closure {
                    body: FuncId::new(0),
                    name: "f".to_string(),
                    kind: FunctionKind::Function,
                    captures: vec![("c".to_string(), ident("cap"))],
                },
                1,
            ),
            (
                Expr::Class {
                    ctor: FuncId::new(0),
                    name: "C".to_string(),
                    heritage: Some(bx(ident("B"))),
                    members: ConstId::new(0),
                    member_attrs: vec![],
                    sendable: false,
                },
                1,
            ),
            (
                Expr::Class {
                    ctor: FuncId::new(0),
                    name: "C".to_string(),
                    heritage: None,
                    members: ConstId::new(0),
                    member_attrs: vec![],
                    sendable: false,
                },
                0,
            ),
            (
                Expr::Yield {
                    value: bx(ident("v")),
                },
                1,
            ),
            (
                Expr::YieldStar {
                    value: bx(ident("v")),
                },
                1,
            ),
            (
                Expr::Await {
                    value: bx(ident("v")),
                    uncaught: false,
                },
                1,
            ),
            (Expr::NewTarget, 0),
            (Expr::GlobalThis, 0),
            (Expr::SelfFunction("f".to_string()), 0),
            (Expr::Arguments, 0),
            (Expr::RestArgs { start_index: 0 }, 0),
            (
                Expr::TemplateObject {
                    raw: None,
                    cooked: None,
                },
                0,
            ),
            (
                Expr::IterResultObj {
                    value: bx(ident("v")),
                    done: bx(boolean(false)),
                },
                2,
            ),
            (
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(ident("o")),
                    status: NodeStatus::Plumbing,
                },
                1,
            ),
            (
                Expr::CreateGenerator {
                    func: bx(ident("f")),
                },
                1,
            ),
            (
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(ident("g")),
                },
                1,
            ),
            (
                Expr::AsyncDriver {
                    resolve: true,
                    value: bx(ident("v")),
                },
                1,
            ),
            (
                Expr::CopyDataProps {
                    dst: bx(ident("d")),
                    src: bx(ident("s")),
                },
                2,
            ),
            (
                Expr::SetObjectWithProto {
                    obj: bx(ident("o")),
                    proto: bx(ident("p")),
                },
                2,
            ),
            (
                Expr::ArraySpread {
                    dst: bx(ident("d")),
                    index: bx(num(0.0)),
                    src: bx(ident("s")),
                },
                3,
            ),
            (
                Expr::RestObject {
                    obj: bx(ident("o")),
                    excluded: vec![strlit("k")],
                },
                2,
            ),
            (
                Expr::DefineGetterSetter {
                    obj: bx(ident("o")),
                    key: bx(strlit("k")),
                    getter: bx(ident("g")),
                    setter: bx(ident("s")),
                },
                4,
            ),
            (Expr::ModuleNamespace { index: 0 }, 0),
            (
                Expr::ObjectBuild {
                    entries: vec![
                        ObjEntry::KeyValue(Lit::String("a".to_string()), ident("v1")),
                        ObjEntry::Computed(ident("k"), ident("v2")),
                        ObjEntry::Spread(ident("s")),
                        ObjEntry::Proto(ident("p")),
                        ObjEntry::Method("m".to_string(), ident("f")),
                        ObjEntry::Getter(ObjKey::Computed(bx(ident("gk"))), ident("gf")),
                        ObjEntry::Setter(ObjKey::Name("sn".to_string()), ident("sf")),
                    ],
                },
                9,
            ),
            (
                Expr::ArrayBuild {
                    elements: vec![ArrayElem::Item(ident("i")), ArrayElem::Spread(ident("s"))],
                },
                2,
            ),
            (
                Expr::Fallback {
                    op: "op",
                    note: "n",
                    operands: vec![ident("o")],
                },
                1,
            ),
        ]
    }

    #[test]
    fn expr_children_tables_cover_every_expr_kind() {
        for (e, want) in all_exprs() {
            assert_eq!(expr_children(&e).len(), want, "{e:?}");
        }
        for (mut e, want) in all_exprs() {
            {
                let kids = expr_children_mut(&mut e);
                assert_eq!(kids.len(), want, "{e:?}");
                for k in kids {
                    *k = Expr::Lit(Lit::Null);
                }
            }
            // Every enumerated child was mutable in place.
            assert_eq!(
                expr_children(&e)
                    .iter()
                    .filter(|c| matches!(c, Expr::Lit(Lit::Null)))
                    .count(),
                want,
                "{e:?}"
            );
        }
    }

    /// One specimen per leaf/statement kind, with its expression count.
    fn all_leaves() -> Vec<(Leaf, usize)> {
        vec![
            (decl("d", 1, ident("v")), 1),
            (phi_assign("p", ident("v")), 1),
            (expr_stmt(ident("e")), 1),
            (
                Leaf::Raw(Stmt::StoreProp {
                    object: ident("o"),
                    name: "n".to_string(),
                    dot_legal: true,
                    value: ident("v"),
                    own: false,
                }),
                2,
            ),
            (
                Leaf::Raw(Stmt::StoreIndex {
                    object: ident("o"),
                    index: num(0.0),
                    value: ident("v"),
                    own: false,
                }),
                3,
            ),
            (
                Leaf::Raw(Stmt::StoreDyn {
                    object: ident("o"),
                    key: ident("k"),
                    value: ident("v"),
                    own: false,
                }),
                3,
            ),
            (
                Leaf::Raw(Stmt::DefineMethod {
                    object: ident("o"),
                    name: "m".to_string(),
                    func: ident("f"),
                    length: 0,
                }),
                2,
            ),
            (
                Leaf::Raw(Stmt::StorePrivate {
                    object: ident("o"),
                    name: "p".to_string(),
                    value: ident("v"),
                    define: false,
                }),
                2,
            ),
            (
                Leaf::Raw(Stmt::StoreSuper {
                    name: None,
                    key: Some(ident("k")),
                    value: ident("v"),
                }),
                2,
            ),
            (
                Leaf::Raw(Stmt::StoreSuper {
                    name: Some("n".to_string()),
                    key: None,
                    value: ident("v"),
                }),
                1,
            ),
            (
                Leaf::Raw(Stmt::LexStore {
                    level: 0,
                    slot: 0,
                    name: "l".to_string(),
                    value: ident("v"),
                }),
                1,
            ),
            (
                Leaf::Raw(Stmt::GlobalStore {
                    name: "g".to_string(),
                    value: ident("v"),
                    tolerant: false,
                }),
                1,
            ),
            (
                Leaf::Raw(Stmt::ModuleStore {
                    index: 0,
                    name: "m".to_string(),
                    value: ident("v"),
                }),
                1,
            ),
            (Leaf::Raw(Stmt::Throw(ident("e"))), 1),
            (Leaf::Raw(Stmt::Return(Some(ident("v")))), 1),
            (
                Leaf::Raw(Stmt::CondBranch {
                    cond: ident("c"),
                    true_dest: BlockId::new(1),
                    false_dest: BlockId::new(2),
                }),
                1,
            ),
            (phi_decl("p", 1), 0),
            (Leaf::Raw(Stmt::Return(None)), 0),
            (Leaf::Raw(Stmt::ScopePop), 0),
            (
                Leaf::Destructure {
                    obj: ident("o"),
                    keys: vec![],
                    rest: "r".to_string(),
                },
                1,
            ),
            (
                Leaf::Decl {
                    name: "d".to_string(),
                    mutable: true,
                    value: Some(ident("v")),
                },
                1,
            ),
            (
                Leaf::Decl {
                    name: "d".to_string(),
                    mutable: true,
                    value: None,
                },
                0,
            ),
            (
                Leaf::Assign {
                    target: "a".to_string(),
                    value: ident("v"),
                },
                1,
            ),
        ]
    }

    #[test]
    fn leaf_expr_tables_cover_every_leaf_kind() {
        for (l, want) in all_leaves() {
            assert_eq!(leaf_exprs(&l).len(), want, "{l:?}");
            if let Leaf::Raw(s) = &l {
                assert_eq!(stmt_exprs_of(s).len(), want, "{s:?}");
            }
        }
    }

    #[test]
    fn subst_temp_covers_every_leaf_and_node_kind() {
        let repl = ident("replacement");
        // Every leaf kind with an expression position routes through.
        for (l, _) in all_leaves() {
            let mut l = l;
            subst_temp_in_leaf(&mut l, ValueId::new(9), &repl);
            let _ = l;
        }
        // The substitution actually rewrites each position.
        let cases: Vec<Leaf> = stmts_with_x()
            .into_iter()
            .map(Leaf::Raw)
            .chain([
                Leaf::Destructure {
                    obj: tm("x", 42),
                    keys: vec![],
                    rest: "r".to_string(),
                },
                Leaf::Decl {
                    name: "d".to_string(),
                    mutable: true,
                    value: Some(tm("x", 42)),
                },
                Leaf::Assign {
                    target: "a".to_string(),
                    value: tm("x", 42),
                },
            ])
            .collect();
        for mut l in cases {
            subst_temp_in_leaf(&mut l, ValueId::new(42), &repl);
            assert!(
                !leaf_exprs(&l)
                    .iter()
                    .any(|e| expr_uses_value(e, ValueId::new(42))),
                "{l:?}"
            );
        }
        // No-op arms: binding-only leaves stay untouched.
        let untouched = [
            phi_decl("p", 42),
            Leaf::Raw(Stmt::CatchBind {
                name: "x".to_string(),
            }),
            Leaf::Raw(Stmt::Return(None)),
            Leaf::Raw(Stmt::ScopePop),
            Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: None,
            },
        ];
        for l in untouched {
            let mut m = l.clone();
            subst_temp_in_leaf(&mut m, ValueId::new(42), &repl);
            assert_eq!(m, l);
        }
        // Every node kind routes the substitution through.
        let tree = vec![
            run(vec![decl("d", 1, tm("v", 42))]),
            if_node(tm("v", 42), vec![], vec![]),
            SNode::While {
                label: None,
                cond: Some(tm("v", 42)),
                body: vec![],
            },
            SNode::DoWhile {
                label: None,
                body: vec![],
                cond: tm("v", 42),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![run(vec![expr_stmt(tm("v", 42))])],
            },
            SNode::Try {
                body: vec![run(vec![expr_stmt(tm("v", 42))])],
                catches: vec![catch("e", vec![run(vec![expr_stmt(tm("v", 42))])])],
                note: None,
                finally: Some(vec![run(vec![expr_stmt(tm("v", 42))])]),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: tm("v", 42),
                body: vec![],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: tm("v", 42),
                body: vec![],
            },
            SNode::Switch {
                disc: tm("v", 42),
                cases: vec![SwitchCase {
                    tests: vec![tm("v", 42)],
                    body: vec![run(vec![expr_stmt(tm("v", 42))])],
                }],
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ];
        let mut t = tree.clone();
        subst_temp_in_nodes(&mut t, ValueId::new(42), &repl);
        assert!(!nodes_use_temp(&t, ValueId::new(42)));
        // The control-transfer nodes are untouched.
        assert_eq!(t[9], tree[9]);
        assert_eq!(t[10], tree[10]);
        assert_eq!(t[11], tree[11]);
    }

    /// A tree carrying the temp `v`/77 in every node-kind position.
    fn rich_tree() -> Vec<SNode> {
        vec![
            run(vec![decl("d", 1, tm("v", 77))]),
            if_node(
                tm("v", 77),
                vec![run(vec![expr_stmt(ident("a"))])],
                vec![run(vec![expr_stmt(tm("v", 77))])],
            ),
            SNode::While {
                label: None,
                cond: Some(tm("v", 77)),
                body: vec![run(vec![expr_stmt(ident("a"))])],
            },
            SNode::DoWhile {
                label: None,
                body: vec![run(vec![expr_stmt(ident("a"))])],
                cond: tm("v", 77),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![run(vec![expr_stmt(tm("v", 77))])],
            },
            SNode::Try {
                body: vec![run(vec![expr_stmt(ident("b"))])],
                catches: vec![catch("e", vec![run(vec![expr_stmt(tm("v", 77))])])],
                note: None,
                finally: Some(vec![run(vec![expr_stmt(tm("v", 77))])]),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: tm("v", 77),
                body: vec![],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: tm("v", 77),
                body: vec![],
            },
            SNode::Switch {
                disc: tm("v", 77),
                cases: vec![SwitchCase {
                    tests: vec![tm("v", 77)],
                    body: vec![run(vec![expr_stmt(tm("v", 77))])],
                }],
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ]
    }

    #[test]
    fn node_use_walkers_cover_every_node_kind() {
        let names: Vec<String> = vec!["v".to_string()];
        let tree = rich_tree();
        // Every kind mentions the temp; a fresh tree does not.
        assert!(nodes_use_any(&tree, &names));
        assert!(nodes_use_temp(&tree, ValueId::new(77)));
        let clean = vec![
            run(vec![decl("d", 1, ident("d0"))]),
            if_node(ident("c"), vec![], vec![]),
            SNode::While {
                label: None,
                cond: Some(ident("c")),
                body: vec![],
            },
            SNode::DoWhile {
                label: None,
                body: vec![],
                cond: ident("c"),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![],
            },
            SNode::Try {
                body: vec![],
                catches: vec![],
                note: None,
                finally: None,
            },
            SNode::ForOf {
                is_await: true,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![],
            },
            SNode::Switch {
                disc: ident("d"),
                cases: vec![],
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ];
        assert!(!nodes_use_any(&clean, &names));
        assert!(!nodes_use_temp(&clean, ValueId::new(77)));
        // Node-level dispatch: each kind answers through node_uses_any.
        for n in &tree[..9] {
            assert!(node_uses_any(n, &names), "{n:?}");
        }
        for n in &clean {
            assert!(!node_uses_any(n, &names), "{n:?}");
        }
        // walk_leaves visits every leaf exactly once.
        let mut seen = 0usize;
        walk_leaves(&tree, &mut |_| seen += 1);
        assert_eq!(seen, 10);
        // nodes_declare_or_assign: binding sites by name.
        assert!(nodes_declare_or_assign(
            &[run(vec![phi_assign("q", ident("z"))])],
            "q"
        ));
        assert!(nodes_declare_or_assign(
            &[run(vec![Leaf::Decl {
                name: "q".to_string(),
                mutable: true,
                value: None,
            }])],
            "q"
        ));
        assert!(nodes_declare_or_assign(
            &[run(vec![Leaf::Assign {
                target: "q".to_string(),
                value: ident("z"),
            }])],
            "q"
        ));
        assert!(!nodes_declare_or_assign(
            &[run(vec![expr_stmt(tm("q", 5))])],
            "q"
        ));
        assert!(!nodes_declare_or_assign(
            &[SNode::Honest("h".to_string())],
            "q"
        ));
    }

    #[test]
    fn flow_analysis_covers_every_node_kind() {
        let throw_run = || run(vec![Leaf::Raw(Stmt::Throw(ident("e")))]);
        let plain_run = || run(vec![expr_stmt(ident("a"))]);
        // Statement runs.
        assert!(node_flow(&throw_run()).diverges);
        assert!(node_flow(&run(vec![Leaf::Raw(Stmt::Return(None))])).diverges);
        assert!(node_flow(&run(vec![Leaf::Raw(Stmt::Unreachable)])).diverges);
        let f = node_flow(&plain_run());
        assert!(!f.diverges && !f.live_break);
        let f = node_flow(&run(vec![
            expr_stmt(ident("a")),
            Leaf::Raw(Stmt::Unreachable),
        ]));
        assert!(!f.diverges, "mixed run falls through");
        // Exits.
        let f = node_flow(&SNode::Break { label: None });
        assert!(f.live_break && f.diverges);
        let f = node_flow(&SNode::Continue { label: None });
        assert!(!f.live_break && f.diverges);
        let f = node_flow(&SNode::Honest("h".to_string()));
        assert!(!f.live_break && !f.diverges);
        // If: diverges only when both non-empty arms diverge.
        let f = node_flow(&if_node(ident("c"), vec![throw_run()], vec![throw_run()]));
        assert!(f.diverges && !f.live_break);
        let f = node_flow(&if_node(ident("c"), vec![throw_run()], vec![]));
        assert!(!f.diverges);
        let f = node_flow(&if_node(
            ident("c"),
            vec![SNode::Break { label: None }],
            vec![plain_run()],
        ));
        assert!(f.live_break && !f.diverges);
        // while (true) with no live break diverges; a live break completes it.
        let f = node_flow(&SNode::While {
            label: None,
            cond: None,
            body: vec![plain_run()],
        });
        assert!(f.diverges && !f.live_break);
        let f = node_flow(&SNode::While {
            label: None,
            cond: None,
            body: vec![SNode::Break { label: None }],
        });
        assert!(!f.diverges && !f.live_break);
        // Conditional loops / for-of / for-in / switch may complete.
        for n in [
            SNode::While {
                label: None,
                cond: Some(ident("c")),
                body: vec![SNode::Break { label: None }],
            },
            SNode::DoWhile {
                label: None,
                body: vec![SNode::Break { label: None }],
                cond: ident("c"),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![SNode::Break { label: None }],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![SNode::Break { label: None }],
            },
            SNode::Switch {
                disc: ident("d"),
                cases: vec![SwitchCase {
                    tests: vec![],
                    body: vec![SNode::Break { label: None }],
                }],
            },
        ] {
            let f = node_flow(&n);
            assert!(!f.live_break && !f.diverges, "{n:?}");
        }
        // A labeled block is transparent to its body's flow.
        let f = node_flow(&SNode::Labeled {
            label: "l".to_string(),
            body: vec![SNode::Break { label: None }],
        });
        assert!(f.live_break && f.diverges);
        // Try: breaks in body/catch/finally are live; never diverges.
        let f = node_flow(&SNode::Try {
            body: vec![SNode::Break { label: None }],
            catches: vec![],
            note: None,
            finally: None,
        });
        assert!(f.live_break && !f.diverges);
        let f = node_flow(&SNode::Try {
            body: vec![throw_run()],
            catches: vec![catch("e", vec![SNode::Break { label: None }])],
            note: None,
            finally: Some(vec![plain_run()]),
        });
        assert!(f.live_break && !f.diverges);
        // Sequence flow: nodes after a diverging node are dead.
        let f = seq_flow(&[throw_run(), SNode::Break { label: None }]);
        assert!(!f.live_break && f.diverges);
        let f = seq_flow(&[plain_run(), SNode::Break { label: None }]);
        assert!(f.live_break && f.diverges);
        let f = seq_flow(&[]);
        assert!(!f.live_break && !f.diverges);
    }

    #[test]
    fn subtree_jump_scans_cover_every_node_kind() {
        // subtree_has_continue: any continue, except inside nested loops.
        assert!(subtree_has_continue(&[SNode::Continue { label: None }]));
        assert!(subtree_has_continue(&[if_node(
            ident("c"),
            vec![],
            vec![SNode::Continue { label: None }],
        )]));
        assert!(subtree_has_continue(&[SNode::Labeled {
            label: "l".to_string(),
            body: vec![SNode::Continue { label: None }],
        }]));
        assert!(subtree_has_continue(&[SNode::Try {
            body: vec![],
            catches: vec![catch("e", vec![SNode::Continue { label: None }])],
            note: None,
            finally: None,
        }]));
        assert!(subtree_has_continue(&[SNode::Try {
            body: vec![],
            catches: vec![],
            note: None,
            finally: Some(vec![SNode::Continue { label: None }]),
        }]));
        assert!(subtree_has_continue(&[SNode::Switch {
            disc: ident("d"),
            cases: vec![SwitchCase {
                tests: vec![],
                body: vec![SNode::Continue { label: None }],
            }],
        }]));
        for n in [
            SNode::While {
                label: None,
                cond: None,
                body: vec![SNode::Continue { label: None }],
            },
            SNode::DoWhile {
                label: None,
                body: vec![SNode::Continue { label: None }],
                cond: ident("c"),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![SNode::Continue { label: None }],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![SNode::Continue { label: None }],
            },
        ] {
            let msg = format!("{n:?}");
            assert!(!subtree_has_continue(&[n]), "{msg}");
        }
        assert!(!subtree_has_continue(&[
            run(vec![]),
            SNode::Break { label: None },
            SNode::Honest("h".to_string()),
        ]));
        // subtree_has_labeled_jump: labeled exits anywhere.
        assert!(subtree_has_labeled_jump(&[SNode::Break {
            label: Some("l".to_string()),
        }]));
        assert!(subtree_has_labeled_jump(&[SNode::Continue {
            label: Some("l".to_string()),
        }]));
        assert!(subtree_has_labeled_jump(&[if_node(
            ident("c"),
            vec![SNode::Break {
                label: Some("l".to_string()),
            }],
            vec![],
        )]));
        for n in [
            SNode::While {
                label: None,
                cond: None,
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            },
            SNode::DoWhile {
                label: None,
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
                cond: ident("c"),
            },
            SNode::Labeled {
                label: "m".to_string(),
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            },
            SNode::Try {
                body: vec![],
                catches: vec![catch(
                    "e",
                    vec![SNode::Break {
                        label: Some("l".to_string()),
                    }],
                )],
                note: None,
                finally: None,
            },
            SNode::Try {
                body: vec![],
                catches: vec![],
                note: None,
                finally: Some(vec![SNode::Break {
                    label: Some("l".to_string()),
                }]),
            },
            SNode::Switch {
                disc: ident("d"),
                cases: vec![SwitchCase {
                    tests: vec![],
                    body: vec![SNode::Break {
                        label: Some("l".to_string()),
                    }],
                }],
            },
        ] {
            let msg = format!("{n:?}");
            assert!(subtree_has_labeled_jump(&[n]), "{msg}");
        }
        assert!(!subtree_has_labeled_jump(&[
            run(vec![]),
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ]));
    }

    #[test]
    fn cleanup_walker_and_alias_collection() {
        // A cleanup-shaped handler: the alias declares and the rethrow
        // are siblings at the handler's top level (walk_cleanup
        // re-collects aliases per recursion level), with the return
        // load and benign nested structures alongside.
        let good = vec![catch(
            "e",
            vec![
                run(vec![
                    decl("a", 50, tm("e", 49)),   // alias of the binding
                    phi_assign("b", tm("a", 50)), // transitive alias
                    decl(
                        "r",
                        51,
                        Expr::PropDyn {
                            object: bx(tm("it", 52)),
                            key: bx(strlit("return")),
                        },
                    ),
                    Leaf::Raw(Stmt::Throw(tm("b", 53))),
                ]),
                if_node(ident("c"), vec![run(vec![expr_stmt(ident("x"))])], vec![]),
                SNode::While {
                    label: None,
                    cond: Some(ident("w")),
                    body: vec![run(vec![expr_stmt(ident("y"))])],
                },
                SNode::Labeled {
                    label: "l".to_string(),
                    body: vec![run(vec![expr_stmt(ident("z"))])],
                },
                try_node(vec![run(vec![expr_stmt(ident("w"))])], vec![]),
            ],
        )];
        assert!(cleanup_handlers_ok(&good));
        // expr_has_return_load forms.
        assert!(expr_has_return_load(&prop(ident("o"), "return")));
        assert!(expr_has_return_load(&Expr::PropIndex {
            object: bx(ident("o")),
            index: bx(strlit("return")),
        }));
        assert!(expr_has_return_load(&call1(
            ident("f"),
            prop(ident("o"), "return")
        )));
        assert!(!expr_has_return_load(&prop(ident("o"), "other")));
        assert!(!expr_has_return_load(&ident("return")));
        // A handler without the return load.
        assert!(!cleanup_handlers_ok(&[catch(
            "e",
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("e", 49)))])],
        )]));
        // A handler with a foreign throw / a side-effecting store is bad.
        assert!(!cleanup_handlers_ok(&[catch(
            "e",
            vec![
                run(vec![decl("r", 51, prop(tm("it", 52), "return"))]),
                run(vec![Leaf::Raw(Stmt::Throw(ident("other")))]),
            ],
        )]));
        assert!(!cleanup_handlers_ok(&[catch(
            "e",
            vec![
                run(vec![
                    decl("r", 51, prop(tm("it", 52), "return")),
                    Leaf::Raw(Stmt::StoreProp {
                        object: ident("o"),
                        name: "p".to_string(),
                        dot_legal: true,
                        value: ident("v"),
                        own: false,
                    },)
                ]),
                run(vec![Leaf::Raw(Stmt::Throw(tm("e", 49)))]),
            ],
        )]));
        // No catch at all.
        assert!(!cleanup_handlers_ok(&[]));
    }

    #[test]
    fn absorb_expr_pairs_enumerate_every_variant() {
        let cases: Vec<(Absorb, usize)> = vec![
            (Absorb::ObjKV(Lit::String("k".to_string()), ident("v")), 1),
            (Absorb::ObjComputed(ident("k"), ident("v")), 2),
            (Absorb::ObjSpread(ident("s")), 1),
            (Absorb::ObjProto(ident("p")), 1),
            (Absorb::ObjMethod("m".to_string(), ident("f")), 1),
            (
                Absorb::ObjAccessors {
                    key: ident("k"),
                    getter: Some(ident("g")),
                    setter: Some(ident("s")),
                },
                3,
            ),
            (
                Absorb::ObjAccessors {
                    key: ident("k"),
                    getter: None,
                    setter: None,
                },
                1,
            ),
            (Absorb::ArrItem(ident("v")), 1),
            (Absorb::ArrSpread(ident("s")), 1),
        ];
        for (a, want) in cases {
            assert_eq!(absorb_exprs(&a).len(), want);
            let mut a = a;
            assert_eq!(absorb_exprs_mut(&mut a).len(), want);
        }
        // expr_count_value counts occurrences transitively.
        let e = call1(ident("f"), tm("x", 42));
        assert_eq!(expr_count_value(&e, ValueId::new(42)), 1);
        assert_eq!(expr_count_value(&tm("x", 42), ValueId::new(42)), 1);
        assert_eq!(expr_count_value(&call0(tm("x", 42)), ValueId::new(1)), 0);
    }

    // ── the finally fold's canonicalization helpers ────────────────

    fn canon_map() -> std::collections::HashMap<String, String> {
        [("a".to_string(), "#d0".to_string())].into_iter().collect()
    }

    #[test]
    fn canon_stmt_covers_every_statement_kind() {
        let map = canon_map();
        // Declare: name renamed, value canon'd, provenance erased.
        let mut s = Stmt::Declare {
            name: "a".to_string(),
            mutable: false,
            value: tm("a", 5),
            value_id: ValueId::new(5),
        };
        canon_stmt(&mut s, &map);
        assert_eq!(
            s,
            Stmt::Declare {
                name: "#d0".to_string(),
                mutable: false,
                value: tm("#d0", 0),
                value_id: ValueId::new(0),
            }
        );
        let mut s = Stmt::PhiDecl {
            name: "a".to_string(),
            value_id: ValueId::new(5),
        };
        canon_stmt(&mut s, &map);
        assert_eq!(
            s,
            Stmt::PhiDecl {
                name: "#d0".to_string(),
                value_id: ValueId::new(0),
            }
        );
        let mut s = Stmt::PhiAssign {
            target: "a".to_string(),
            value: tm("a", 5),
            to: BlockId::new(9),
            exceptional: true,
        };
        canon_stmt(&mut s, &map);
        assert_eq!(
            s,
            Stmt::PhiAssign {
                target: "#d0".to_string(),
                value: tm("#d0", 0),
                to: BlockId::new(0),
                exceptional: true,
            }
        );
        // Expression-carrying arms.
        let value_arms: Vec<fn(Expr) -> Stmt> = vec![
            Stmt::Expr,
            Stmt::Throw,
            |e| Stmt::Return(Some(e)),
            |e| Stmt::LexStore {
                level: 0,
                slot: 0,
                name: "l".to_string(),
                value: e,
            },
            |e| Stmt::GlobalStore {
                name: "g".to_string(),
                value: e,
                tolerant: false,
            },
            |e| Stmt::ModuleStore {
                index: 0,
                name: "m".to_string(),
                value: e,
            },
        ];
        for mk in value_arms {
            let mut s = mk(tm("a", 5));
            canon_stmt(&mut s, &map);
            let exprs = stmt_exprs_of(&s);
            assert_eq!(exprs, vec![&tm("#d0", 0)]);
        }
        // Store arms rewrite every expression field.
        let mut s = Stmt::StoreProp {
            object: tm("a", 5),
            name: "k".to_string(),
            dot_legal: true,
            value: tm("a", 6),
            own: false,
        };
        canon_stmt(&mut s, &map);
        assert_eq!(
            s,
            Stmt::StoreProp {
                object: tm("#d0", 0),
                name: "k".to_string(),
                dot_legal: true,
                value: tm("#d0", 0),
                own: false,
            }
        );
        let mut s = Stmt::StoreIndex {
            object: tm("a", 5),
            index: tm("a", 6),
            value: ident("v"),
            own: false,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::StoreIndex { object, index, .. }
                if object == tm("#d0", 0) && index == tm("#d0", 0)
        ));
        let mut s = Stmt::StoreDyn {
            object: tm("a", 5),
            key: tm("a", 6),
            value: ident("v"),
            own: false,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::StoreDyn { object, key, .. }
                if object == tm("#d0", 0) && key == tm("#d0", 0)
        ));
        let mut s = Stmt::DefineMethod {
            object: tm("a", 5),
            name: "m".to_string(),
            func: tm("a", 6),
            length: 0,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::DefineMethod { object, func, .. }
                if object == tm("#d0", 0) && func == tm("#d0", 0)
        ));
        let mut s = Stmt::StorePrivate {
            object: tm("a", 5),
            name: "p".to_string(),
            value: tm("a", 6),
            define: true,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::StorePrivate { object, value, .. }
                if object == tm("#d0", 0) && value == tm("#d0", 0)
        ));
        let mut s = Stmt::StoreSuper {
            name: None,
            key: Some(tm("a", 5)),
            value: tm("a", 6),
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::StoreSuper {
                key: Some(k),
                value,
                ..
            } if k == tm("#d0", 0) && value == tm("#d0", 0)
        ));
        let mut s = Stmt::StoreSuper {
            name: Some("k".to_string()),
            key: None,
            value: tm("a", 6),
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(
            s,
            Stmt::StoreSuper { key: None, value, .. } if value == tm("#d0", 0)
        ));
        // CatchBind renames the binding.
        let mut s = Stmt::CatchBind {
            name: "a".to_string(),
        };
        canon_stmt(&mut s, &map);
        assert_eq!(
            s,
            Stmt::CatchBind {
                name: "#d0".to_string()
            }
        );
        // Elided/Fallback lose their source locations.
        let loc = Some(abcd_ir::function::Loc {
            line: 1,
            column: Some(2),
        });
        let mut s = Stmt::Elided {
            op: "op",
            reason: "r",
            loc,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(s, Stmt::Elided { loc: None, .. }));
        let mut s = Stmt::Fallback {
            op: "op",
            note: "n",
            loc,
        };
        canon_stmt(&mut s, &map);
        assert!(matches!(s, Stmt::Fallback { loc: None, .. }));
        // The catch-all arm leaves the statement alone.
        for s in [
            Stmt::Return(None),
            Stmt::ScopePop,
            Stmt::Unreachable,
            Stmt::Branch {
                dest: BlockId::new(0),
            },
            Stmt::CondBranch {
                cond: tm("a", 5),
                true_dest: BlockId::new(1),
                false_dest: BlockId::new(2),
            },
        ] {
            let mut m = s.clone();
            canon_stmt(&mut m, &map);
            assert_eq!(m, s);
        }
    }

    #[test]
    fn canon_tok_and_def_names_cover_every_leaf_kind() {
        let map = canon_map();
        // A nested node token is opaque to canonicalization.
        let mut t = FTok::Node(SNode::Break { label: None });
        canon_tok(&mut t, &map);
        assert_eq!(t, FTok::Node(SNode::Break { label: None }));
        // Destructure: object canon'd, key targets + rest renamed.
        let mut t = FTok::Leaf(Leaf::Destructure {
            obj: tm("a", 5),
            keys: vec![("k".to_string(), "a".to_string())],
            rest: "a".to_string(),
        });
        canon_tok(&mut t, &map);
        assert_eq!(
            t,
            FTok::Leaf(Leaf::Destructure {
                obj: tm("#d0", 0),
                keys: vec![("k".to_string(), "#d0".to_string())],
                rest: "#d0".to_string(),
            })
        );
        // Synthetic decl / assign.
        let mut t = FTok::Leaf(Leaf::Decl {
            name: "a".to_string(),
            mutable: true,
            value: Some(tm("a", 5)),
        });
        canon_tok(&mut t, &map);
        assert_eq!(
            t,
            FTok::Leaf(Leaf::Decl {
                name: "#d0".to_string(),
                mutable: true,
                value: Some(tm("#d0", 0)),
            })
        );
        let mut t = FTok::Leaf(Leaf::Decl {
            name: "a".to_string(),
            mutable: true,
            value: None,
        });
        canon_tok(&mut t, &map);
        assert!(matches!(
            t,
            FTok::Leaf(Leaf::Decl { name, value: None, .. }) if name == "#d0"
        ));
        let mut t = FTok::Leaf(Leaf::Assign {
            target: "a".to_string(),
            value: tm("a", 5),
        });
        canon_tok(&mut t, &map);
        assert_eq!(
            t,
            FTok::Leaf(Leaf::Assign {
                target: "#d0".to_string(),
                value: tm("#d0", 0),
            })
        );
        // Definition-site census: first-occurrence order, nodes skipped.
        let toks = vec![
            FTok::Leaf(decl("a", 1, ident("v"))),
            FTok::Node(SNode::Honest("h".to_string())),
            FTok::Leaf(phi_decl("b", 2)),
            FTok::Leaf(Leaf::Raw(Stmt::CatchBind {
                name: "c".to_string(),
            })),
            FTok::Leaf(Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: None,
            }),
            FTok::Leaf(Leaf::Destructure {
                obj: ident("o"),
                keys: vec![("k".to_string(), "t1".to_string())],
                rest: "r".to_string(),
            }),
            FTok::Leaf(decl("a", 9, ident("w"))),
            FTok::Leaf(expr_stmt(ident("x"))),
        ];
        assert_eq!(ftok_def_names(&toks), vec!["a", "b", "c", "d", "t1", "r"]);
        // ft_canon placeholders follow that order.
        let out = ft_canon(&[
            FTok::Leaf(decl("a", 1, tm("a", 1))),
            FTok::Leaf(decl("b", 2, tm("a", 1))),
        ]);
        assert_eq!(
            out,
            vec![
                FTok::Leaf(decl("#d0", 0, tm("#d0", 0))),
                FTok::Leaf(decl("#d1", 0, tm("#d0", 0))),
            ]
        );
    }

    #[test]
    fn ft_regroup_interleaves_nodes_and_runs() {
        let out = ft_regroup(vec![
            FTok::Node(SNode::Honest("h".to_string())),
            FTok::Leaf(expr_stmt(ident("a"))),
            FTok::Leaf(expr_stmt(ident("b"))),
            FTok::Node(SNode::Break { label: None }),
            FTok::Leaf(expr_stmt(ident("c"))),
        ]);
        assert_eq!(
            out,
            vec![
                SNode::Honest("h".to_string()),
                run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
                SNode::Break { label: None },
                run(vec![expr_stmt(ident("c"))]),
            ]
        );
        assert!(ft_regroup(vec![]).is_empty());
        // ft_flatten is the inverse view.
        let flat = ft_flatten(&out);
        assert_eq!(flat.len(), 5);
        assert!(matches!(flat[0], FTok::Node(SNode::Honest(_))));
    }

    #[test]
    fn ft_fallthrough_covers_every_node_kind() {
        let plain = || run(vec![expr_stmt(ident("a"))]);
        // Statement runs: control-transfer leaves end fall-through.
        assert!(ft_node_fallthrough(&plain()));
        for l in [
            Stmt::Return(None),
            Stmt::Throw(ident("e")),
            Stmt::Branch {
                dest: BlockId::new(0),
            },
            Stmt::CondBranch {
                cond: ident("c"),
                true_dest: BlockId::new(1),
                false_dest: BlockId::new(2),
            },
        ] {
            let msg = format!("{l:?}");
            assert!(!ft_node_fallthrough(&run(vec![Leaf::Raw(l)])), "{msg}");
        }
        // If: both arms must fall through.
        assert!(ft_node_fallthrough(&if_node(
            ident("c"),
            vec![plain()],
            vec![plain()]
        )));
        assert!(!ft_node_fallthrough(&if_node(
            ident("c"),
            vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            vec![plain()],
        )));
        // Try: body falls through, or a catch does (catches required).
        assert!(ft_node_fallthrough(&SNode::Try {
            body: vec![plain()],
            catches: vec![],
            note: None,
            finally: None,
        }));
        assert!(ft_node_fallthrough(&SNode::Try {
            body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            catches: vec![catch("e", vec![plain()])],
            note: None,
            finally: Some(vec![plain()]),
        }));
        assert!(!ft_node_fallthrough(&SNode::Try {
            body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            catches: vec![],
            note: None,
            finally: None,
        }));
        // Exits do not fall through; everything else may complete.
        assert!(!ft_node_fallthrough(&SNode::Break { label: None }));
        assert!(!ft_node_fallthrough(&SNode::Continue { label: None }));
        for n in [
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            SNode::DoWhile {
                label: None,
                body: vec![],
                cond: ident("c"),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![],
            },
            SNode::Switch {
                disc: ident("d"),
                cases: vec![],
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![],
            },
            SNode::Honest("h".to_string()),
        ] {
            assert!(ft_node_fallthrough(&n), "{n:?}");
        }
        assert!(ft_list_fallthrough(&[
            plain(),
            SNode::Honest("h".to_string())
        ]));
        assert!(!ft_list_fallthrough(&[
            plain(),
            SNode::Break { label: None }
        ]));
    }

    // ── iterator-loop folds (for-of / for-in / degenerate for-in) ──

    /// The corpus for-of shape: `it`/`next` plumbing, header phis,
    /// `res = next()`, `done = res.done`, the done-tested while, the
    /// value binding, and back-edge self-assigns.
    fn for_of_site() -> Vec<SNode> {
        vec![
            run(vec![
                decl(
                    "it",
                    10,
                    Expr::Iter {
                        op: IterOp::GetIterator,
                        obj: bx(ident("src")),
                        status: NodeStatus::Plumbing,
                    },
                ),
                decl("next", 11, prop(tm("it", 10), "next")),
                phi_assign("np", tm("next", 11)),
                phi_assign("ip", tm("it", 10)),
            ]),
            SNode::While {
                label: None,
                cond: Some(istrue(tm("done", 25))),
                body: vec![
                    run(vec![
                        phi_decl("np", 20),
                        phi_decl("ip", 21),
                        decl("res", 23, call0(tm("np", 20))),
                        decl("done", 25, prop(tm("res", 23), "done")),
                    ]),
                    run(vec![
                        decl("v", 26, prop(tm("res", 23), "value")),
                        expr_stmt(call1(ident("print"), tm("v", 26))),
                    ]),
                    run(vec![
                        phi_assign("np", tm("np", 20)),
                        phi_assign("ip", tm("ip", 21)),
                    ]),
                ],
            },
        ]
    }

    #[test]
    fn for_of_fold_positive_and_normalized_test_form() {
        let mut nodes = for_of_site();
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_of, 1);
        assert_eq!(
            nodes,
            vec![SNode::ForOf {
                is_await: false,
                binding: "v".to_string(),
                iter: ident("src"),
                body: vec![run(vec![expr_stmt(call1(ident("print"), tm("v", 26)))])],
            }]
        );
        // The `while (true) { wiring; if (t) break; … }` emission form
        // normalizes to the same fold: the loop test becomes an
        // `if (done) break` after the header wiring run.
        let mut nodes = for_of_site();
        let SNode::While { body, cond, .. } = &mut nodes[1] else {
            unreachable!()
        };
        let test_if = if_node(
            cond.take().unwrap(),
            vec![SNode::Break { label: None }],
            vec![],
        );
        body.insert(1, test_if);
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_of, 1);
        assert!(matches!(&nodes[0], SNode::ForOf { .. }));
        // An async iterator marks the folded loop `for await…of`.
        let mut nodes = for_of_site();
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[0] = decl(
            "it",
            10,
            Expr::Iter {
                op: IterOp::GetAsyncIterator,
                obj: bx(ident("src")),
                status: NodeStatus::Plumbing,
            },
        );
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_await_of, 1);
        assert!(matches!(&nodes[0], SNode::ForOf { is_await: true, .. }));
    }

    #[test]
    fn for_of_match_bail_pins() {
        let site = for_of_site();
        let (pre, wcond, body) = {
            let SNode::While { cond, body, .. } = &site[1] else {
                unreachable!()
            };
            let pre = match &site[0] {
                SNode::Stmts(l) => l.clone(),
                _ => unreachable!(),
            };
            (pre, cond.clone().unwrap(), body.clone())
        };
        assert!(match_for_of(&pre, &wcond, &body).is_some());
        // Truncated pre-run: no room for the iterator pair.
        assert!(match_for_of(&pre[..1], &wcond, &body).is_none());
        // The iterator declare must be GetIterator/GetAsyncIterator.
        let mut bad = pre.clone();
        bad[0] = decl("it", 10, ident("notiter"));
        assert!(match_for_of(&bad, &wcond, &body).is_none());
        // The `next` declare must load `.next` off the iterator.
        let mut bad = pre.clone();
        bad[1] = decl("next", 11, prop(tm("it", 10), "previous"));
        assert!(match_for_of(&bad, &wcond, &body).is_none());
        // The header must be a statement run.
        let mut bbody = body.clone();
        bbody[0] = SNode::Honest("h".to_string());
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        // … and carry at least one phi.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr.remove(0);
        hdr.remove(0);
        // (phi decls removed; res call's callee is then no phi)
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        // The res call must be an argument-free call of a header phi.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr[2] = decl("res", 23, call1(tm("np", 20), ident("x")));
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr[2] = decl("res", 23, call0(tm("other", 99)));
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        // Elided guards between the call and the done decl are skipped.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr.insert(3, elided("Guard"));
        assert!(match_for_of(&pre, &wcond, &bbody).is_some());
        // The done decl must read `.done` off the res temp.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr[3] = decl("done", 25, prop(tm("res", 23), "finished"));
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        // Trailing header junk bails.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr.push(expr_stmt(ident("extra")));
        assert!(match_for_of(&pre, &wcond, &bbody).is_none());
        // The while test must be the done temp (wrappers stripped).
        assert!(match_for_of(&pre, &isfalse(tm("done", 25)), &body).is_some());
        assert!(match_for_of(&pre, &ident("other"), &body).is_none());
        assert!(match_for_of(&pre, &num(1.0), &body).is_none());
        // The pre-loop assigns must wire `next` into the call's phi.
        let mut bad = pre.clone();
        bad[2] = phi_assign("np", tm("it", 10));
        assert!(match_for_of(&bad, &wcond, &body).is_none());
    }

    /// The corpus for-in shape, with one extra pass-through header phi
    /// (hoisted above the folded loop) and an identity-copy phi chain
    /// in the body (eliminated by `elim_internal_copy_phis`).
    fn for_in_site() -> Vec<SNode> {
        vec![
            run(vec![
                phi_assign(
                    "ip",
                    Expr::Iter {
                        op: IterOp::GetPropIterator,
                        obj: bx(ident("src")),
                        status: NodeStatus::Plumbing,
                    },
                ),
                phi_assign("xp", ident("invariant")),
            ]),
            SNode::While {
                label: None,
                cond: Some(cmp(CmpOp::Eq, undef(), tm("k", 31))),
                body: vec![
                    run(vec![
                        phi_decl("ip", 20),
                        phi_decl("xp", 21),
                        decl(
                            "k",
                            31,
                            Expr::Iter {
                                op: IterOp::NextPropName,
                                obj: bx(tm("ip", 20)),
                                status: NodeStatus::Plumbing,
                            },
                        ),
                    ]),
                    run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
                    // A branch join's identity-copy phi chain (never
                    // read after elimination).
                    if_node(
                        ident("c"),
                        vec![run(vec![
                            phi_decl("cp", 40),
                            phi_assign("cp", tm("ip", 20)),
                        ])],
                        vec![run(vec![
                            phi_decl("dp", 41),
                            phi_assign("dp", tm("cp", 40)),
                        ])],
                    ),
                    run(vec![
                        phi_assign("ip", tm("ip", 20)),
                        phi_assign("xp", tm("xp", 21)),
                    ]),
                ],
            },
        ]
    }

    #[test]
    fn for_in_fold_positive_with_hoisted_phi_and_copy_elimination() {
        let mut nodes = for_in_site();
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_in, 1);
        // The pass-through phi's wiring is hoisted above the loop.
        assert_eq!(
            nodes[0],
            run(vec![
                phi_decl("xp", 21),
                phi_assign("xp", ident("invariant"))
            ])
        );
        let SNode::ForIn { binding, obj, body } = &nodes[1] else {
            panic!("expected ForIn: {nodes:?}")
        };
        assert_eq!(binding, "k");
        assert_eq!(obj, &ident("src"));
        // The copy-phi chain and self-assigns are gone.
        assert_eq!(
            body.as_slice(),
            [
                run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
                if_node(ident("c"), vec![], vec![]),
            ]
        );
    }

    #[test]
    fn for_in_match_bail_pins() {
        let site = for_in_site();
        let (pre, wcond, body) = {
            let SNode::While { cond, body, .. } = &site[1] else {
                unreachable!()
            };
            let pre = match &site[0] {
                SNode::Stmts(l) => l.clone(),
                _ => unreachable!(),
            };
            (pre, cond.clone().unwrap(), body.clone())
        };
        assert!(match_for_in(&pre, &wcond, &body).is_some());
        // Header: phi decls then exactly the NextPropName declare.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr.push(expr_stmt(ident("extra")));
        assert!(match_for_in(&pre, &wcond, &bbody).is_none());
        // NextPropName must read a header phi.
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr[2] = decl(
            "k",
            31,
            Expr::Iter {
                op: IterOp::NextPropName,
                obj: bx(tm("other", 99)),
                status: NodeStatus::Plumbing,
            },
        );
        assert!(match_for_in(&pre, &wcond, &bbody).is_none());
        // Every header phi needs exactly one wiring assign.
        let mut bad = pre.clone();
        bad.remove(1);
        assert!(match_for_in(&bad, &wcond, &body).is_none());
        // The iterator phi's value must be the GetPropIterator.
        let mut bad = pre.clone();
        bad[0] = phi_assign("ip", ident("src"));
        assert!(match_for_in(&bad, &wcond, &body).is_none());
        // An extra phi's initial value must not reference the internals.
        let mut bad = pre.clone();
        bad[1] = phi_assign("xp", tm("ip", 20));
        assert!(match_for_in(&bad, &wcond, &body).is_none());
        // The condition must be `undefined == k` (either order/op).
        assert!(match_for_in(&pre, &cmp(CmpOp::NotEq, tm("k", 31), undef()), &body).is_some());
        assert!(match_for_in(&pre, &cmp(CmpOp::Eq, ident("u"), tm("k", 31)), &body).is_none());
        assert!(match_for_in(&pre, &ident("k"), &body).is_none());
    }

    #[test]
    fn elim_internal_copy_phis_bail_pins() {
        let mut roots: BTreeMap<String, Expr> = BTreeMap::new();
        roots.insert("r".to_string(), tm("r", 60));
        // A phi with a non-temp source is not a copy.
        let mut out = vec![run(vec![
            phi_decl("cp", 40),
            phi_assign("cp", num(1.0)),
            expr_stmt(tm("cp", 40)),
        ])];
        elim_internal_copy_phis(&mut out, &roots);
        assert!(nodes_use_any(&out, &["cp".to_string()]));
        // Sources resolving to different roots disqualify the phi.
        roots.insert("s".to_string(), tm("s", 61));
        let mut out = vec![run(vec![
            phi_decl("cp", 40),
            phi_assign("cp", tm("r", 60)),
            phi_assign("cp", tm("s", 61)),
        ])];
        elim_internal_copy_phis(&mut out, &roots);
        let SNode::Stmts(kept) = &out[0] else {
            unreachable!()
        };
        assert!(kept.len() == 3, "not a copy: {kept:?}");
        // An assign-less phi is skipped entirely.
        let mut out = vec![run(vec![phi_decl("cp", 40)])];
        elim_internal_copy_phis(&mut out, &roots);
        assert_eq!(out.len(), 1);
        // drop_self_assign_tail shapes.
        let mut out: Vec<SNode> = vec![];
        drop_self_assign_tail(&mut out);
        let mut out = vec![SNode::Continue { label: None }];
        drop_self_assign_tail(&mut out);
        assert_eq!(out.len(), 1);
        let mut out = vec![run(vec![phi_assign("q", ident("z"))])];
        drop_self_assign_tail(&mut out);
        assert_eq!(out.len(), 1, "not a self-assign run");
        let mut out = vec![
            run(vec![expr_stmt(ident("a"))]),
            run(vec![phi_assign("q", tm("q", 5))]),
            SNode::Break { label: None },
        ];
        drop_self_assign_tail(&mut out);
        assert_eq!(out.len(), 2, "the self-assign run before a break drops");
        // take_value_declare: only a leading `.value` load declare.
        let mut leaves = vec![decl("v", 1, prop(tm("res", 2), "value"))];
        assert_eq!(
            take_value_declare(&mut leaves, "res"),
            Some("v".to_string())
        );
        assert!(leaves.is_empty());
        let mut leaves = vec![decl("v", 1, prop(tm("res", 2), "other"))];
        assert_eq!(take_value_declare(&mut leaves, "res"), None);
    }

    /// The degenerate (single-pass) for-in site: acyclic plumbing, the
    /// exit test, and the one-shot body in the not-done arm.
    fn single_pass_for_in_site(cond: Expr) -> Vec<SNode> {
        vec![
            run(vec![
                expr_stmt(call0(ident("setup"))),
                phi_assign(
                    "it",
                    Expr::Iter {
                        op: IterOp::GetPropIterator,
                        obj: bx(ident("src")),
                        status: NodeStatus::Plumbing,
                    },
                ),
            ]),
            run(vec![
                phi_decl("it", 30),
                decl(
                    "k",
                    31,
                    Expr::Iter {
                        op: IterOp::NextPropName,
                        obj: bx(tm("it", 30)),
                        status: NodeStatus::Plumbing,
                    },
                ),
            ]),
            if_node(
                cond,
                vec![],
                vec![run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))])],
            ),
        ]
    }

    #[test]
    fn single_pass_for_in_positive_and_bail_pins() {
        let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_in, 1);
        // The assign run survives (its other leaves stay); the folded
        // ForIn replaces the header run + exit test.
        assert!(matches!(&nodes[0], SNode::Stmts(_)));
        let SNode::ForIn { binding, obj, body } = &nodes[1] else {
            panic!("expected ForIn: {nodes:?}")
        };
        assert_eq!(binding, "k");
        assert_eq!(obj, &ident("src"));
        // The non-diverging one-shot body gains a trailing break.
        assert_eq!(body.last(), Some(&SNode::Break { label: None }), "{body:?}");
        // Polarity variants: NotEq puts the body on the then arm.
        let mut site = single_pass_for_in_site(cmp(CmpOp::NotEq, tm("k", 31), undef()));
        let SNode::If {
            then, otherwise, ..
        } = &mut site[2]
        else {
            unreachable!()
        };
        let body_nodes = std::mem::take(otherwise);
        *then = body_nodes;
        assert!(match_single_pass_for_in(&site, 1).is_some());
        // Wrapped tests (isfalse/isnot invert the arms).
        let mut site = single_pass_for_in_site(isfalse(cmp(CmpOp::Eq, tm("k", 31), undef())));
        let SNode::If {
            then, otherwise, ..
        } = &mut site[2]
        else {
            unreachable!()
        };
        let body_nodes = std::mem::take(otherwise);
        *then = body_nodes;
        assert!(match_single_pass_for_in(&site, 1).is_some());
        let site = single_pass_for_in_site(istrue(cmp(CmpOp::StrictEq, undef(), tm("k", 31))));
        assert!(match_single_pass_for_in(&site, 1).is_some());

        let good = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
        // The header must be exactly [PhiDecl it, NextPropName declare].
        let mut bad = good.clone();
        bad[1] = SNode::Honest("h".to_string());
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        let mut bad = good.clone();
        let SNode::Stmts(hdr) = &mut bad[1] else {
            unreachable!()
        };
        hdr.push(expr_stmt(ident("x")));
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // The NextPropName must read the phi-declared iterator.
        let mut bad = good.clone();
        let SNode::Stmts(hdr) = &mut bad[1] else {
            unreachable!()
        };
        hdr[1] = decl(
            "k",
            31,
            Expr::Iter {
                op: IterOp::NextPropName,
                obj: bx(tm("other", 99)),
                status: NodeStatus::Plumbing,
            },
        );
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // There must be a previous non-Honest statement run…
        assert!(match_single_pass_for_in(&good[1..], 0).is_none());
        // … whose last leaf is the GetPropIterator phi-assign…
        let mut bad = good.clone();
        bad[0] = SNode::Honest("h".to_string());
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        let mut bad = good.clone();
        let SNode::Stmts(pre) = &mut bad[0] else {
            unreachable!()
        };
        pre[1] = phi_assign("it", ident("src"));
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // … targeting the same iterator temp.
        let mut bad = good.clone();
        let SNode::Stmts(pre) = &mut bad[0] else {
            unreachable!()
        };
        pre[1] = phi_assign(
            "other",
            Expr::Iter {
                op: IterOp::GetPropIterator,
                obj: bx(ident("src")),
                status: NodeStatus::Plumbing,
            },
        );
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // The exit test must be an if…
        let mut bad = good.clone();
        bad[2] = SNode::Honest("h".to_string());
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // … a compare against undefined …
        let mut bad = good.clone();
        bad[2] = if_node(ident("k"), vec![], vec![run(vec![])]);
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        let mut bad = good.clone();
        bad[2] = if_node(cmp(CmpOp::Eq, ident("u"), ident("v")), vec![], vec![]);
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // … with the body on the not-done arm and the other arm empty.
        let mut bad = good.clone();
        bad[2] = if_node(
            cmp(CmpOp::Eq, tm("k", 31), undef()),
            vec![run(vec![expr_stmt(ident("x"))])],
            vec![run(vec![expr_stmt(ident("y"))])],
        );
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // The iterated expression must not reference the internals.
        let mut bad = good.clone();
        let SNode::Stmts(pre) = &mut bad[0] else {
            unreachable!()
        };
        pre[1] = phi_assign(
            "it",
            Expr::Iter {
                op: IterOp::GetPropIterator,
                obj: bx(tm("k", 31)),
                status: NodeStatus::Plumbing,
            },
        );
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // Nothing outside the matched trio may use the internals.
        let mut bad = good.clone();
        bad.push(run(vec![expr_stmt(tm("k", 31))]));
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // The assign run's earlier leaves must not use them either.
        let mut bad = good.clone();
        let SNode::Stmts(pre) = &mut bad[0] else {
            unreachable!()
        };
        pre[0] = expr_stmt(tm("it", 30));
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // The body must not reference the iterator plumbing…
        let mut bad = good.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        otherwise[0] = run(vec![expr_stmt(tm("it", 30))]);
        assert!(match_single_pass_for_in(&bad, 1).is_none());
        // … nor grow a stray continue.
        let mut bad = good.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        otherwise.push(SNode::Continue { label: None });
        assert!(match_single_pass_for_in(&bad, 1).is_none());
    }

    #[test]
    fn normalize_loop_test_and_pre_leaf_trims() {
        // normalize_loop_test shape guards.
        let body = vec![
            run(vec![expr_stmt(ident("a"))]),
            if_node(ident("t"), vec![SNode::Break { label: None }], vec![]),
            run(vec![expr_stmt(ident("b"))]),
        ];
        let (test, new_body) = normalize_loop_test(&body).expect("the d-P4 form");
        assert_eq!(test, ident("t"));
        assert_eq!(new_body.len(), 2);
        // Not [Stmts, If, ..].
        assert!(normalize_loop_test(&[run(vec![])]).is_none());
        assert!(
            normalize_loop_test(&[SNode::Honest("h".to_string()), SNode::Break { label: None }])
                .is_none()
        );
        // The break arm must be exactly an unlabeled break with no else.
        assert!(
            normalize_loop_test(&[run(vec![]), if_node(ident("t"), vec![run(vec![])], vec![]),])
                .is_none()
        );
        assert!(
            normalize_loop_test(&[
                run(vec![]),
                if_node(
                    ident("t"),
                    vec![SNode::Break { label: None }],
                    vec![run(vec![])]
                ),
            ])
            .is_none()
        );
        // merged_pre_leaves concatenates adjacent runs only.
        let nodes = vec![
            SNode::Honest("h".to_string()),
            run(vec![expr_stmt(ident("a"))]),
            run(vec![expr_stmt(ident("b"))]),
            SNode::Break { label: None },
        ];
        assert_eq!(merged_pre_leaves(&nodes, 3).len(), 2);
        assert!(merged_pre_leaves(&nodes, 1).is_empty());
        // trim_pre_leaves walks backwards, removing emptied nodes and
        // stopping at a non-run node.
        let mut nodes = vec![
            SNode::Honest("h".to_string()),
            run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
            run(vec![expr_stmt(ident("c"))]),
            SNode::Break { label: None },
        ];
        let removed = trim_pre_leaves(&mut nodes, 3, 3);
        assert_eq!(removed, 2);
        assert_eq!(
            nodes,
            vec![SNode::Honest("h".to_string()), SNode::Break { label: None }]
        );
        // An Honest node stops the backwards walk before the cut
        // completes; already-empty runs still count as removals.
        let mut nodes = vec![
            SNode::Honest("h".to_string()),
            run(vec![expr_stmt(ident("a"))]),
            SNode::Break { label: None },
        ];
        let removed = trim_pre_leaves(&mut nodes, 2, 5);
        assert_eq!(removed, 1);
        assert_eq!(nodes.len(), 2);
        // trim_driver_pre_leaves skips honesty comments and empty runs.
        let mut nodes = vec![
            run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
            SNode::Honest("h".to_string()),
            run(vec![]),
            run(vec![expr_stmt(ident("c"))]),
            SNode::Break { label: None },
        ];
        let removed = trim_driver_pre_leaves(&mut nodes, 4, 3);
        assert_eq!(removed, 3);
        assert_eq!(nodes.len(), 2, "{nodes:?}");
        assert!(matches!(&nodes[0], SNode::Honest(_)));
        // gather_driver_pre_leaves likewise skips comments/empty runs.
        let nodes = vec![
            run(vec![expr_stmt(ident("a"))]),
            SNode::Honest("h".to_string()),
            run(vec![]),
            run(vec![expr_stmt(ident("b"))]),
            SNode::Break { label: None },
        ];
        let got = gather_driver_pre_leaves(&nodes, 4);
        assert_eq!(got.len(), 2);
    }

    #[test]
    fn dead_loop_exit_throw_sweep() {
        // The N70 residue: an unlabeled `while (true)` whose header
        // declares an uncaught-await temp, followed by `throw <temp>`.
        let site = || {
            vec![
                SNode::While {
                    label: None,
                    cond: None,
                    body: vec![
                        run(vec![decl(
                            "a",
                            50,
                            Expr::Await {
                                value: bx(ident("p")),
                                uncaught: true,
                            },
                        )]),
                        SNode::Honest("h".to_string()),
                    ],
                },
                run(vec![Leaf::Raw(Stmt::Throw(tm("a", 50)))]),
            ]
        };
        let mut nodes = site();
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 1);
        assert!(matches!(&nodes[1], SNode::Honest(_)));
        // A trailing `Unreachable` marker rides along.
        let mut nodes = site();
        let SNode::Stmts(tail) = &mut nodes[1] else {
            unreachable!()
        };
        tail.push(Leaf::Raw(Stmt::Unreachable));
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 1);
        // Bails: a loop with a label is never a candidate.
        let mut nodes = site();
        let SNode::While { label, .. } = &mut nodes[0] else {
            unreachable!()
        };
        *label = Some("l".to_string());
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // The residue must be a sibling run…
        let mut nodes = site();
        nodes.pop();
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // … of exactly the throw (+marker) shape…
        let mut nodes = site();
        nodes[1] = run(vec![expr_stmt(ident("x"))]);
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // … throwing a header await temp…
        let mut nodes = site();
        nodes[1] = run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))]);
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // … with no header await, nothing is swept.
        let mut nodes = site();
        let SNode::While { body, .. } = &mut nodes[0] else {
            unreachable!()
        };
        body[0] = run(vec![decl("a", 50, ident("p"))]);
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // A live exit break keeps the residue.
        let mut nodes = site();
        let SNode::While { body, .. } = &mut nodes[0] else {
            unreachable!()
        };
        body.push(SNode::Break { label: None });
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // A labeled jump anywhere in the subtree keeps it too.
        let mut nodes = site();
        let SNode::While { body, .. } = &mut nodes[0] else {
            unreachable!()
        };
        body.push(SNode::Break {
            label: Some("l".to_string()),
        });
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // Honest markers and empty runs between the loop and the
        // residue are skipped by the sibling scan.
        let mut nodes = site();
        nodes.insert(1, SNode::Honest("cut".to_string()));
        nodes.insert(2, run(vec![]));
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 1);
        // A caught await (uncaught: false) is not the dispatch temp.
        let mut nodes = site();
        let SNode::While { body, .. } = &mut nodes[0] else {
            unreachable!()
        };
        body[0] = run(vec![decl(
            "a",
            50,
            Expr::Await {
                value: bx(ident("p")),
                uncaught: false,
            },
        )]);
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
    }

    // ── fold 5: the switch re-detection ────────────────────────────

    fn chain_3_no_else() -> SNode {
        if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![expr_stmt(call0(ident("a")))])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
                vec![run(vec![expr_stmt(call0(ident("b")))])],
                vec![if_node(
                    cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
                    vec![run(vec![expr_stmt(call0(ident("c")))])],
                    vec![],
                )],
            )],
        )
    }

    #[test]
    fn switch_chain_extension_loop_and_default_arm() {
        // The no-else chain: the ONLY route through the extension loop.
        let mut nodes = vec![chain_3_no_else()];
        let mut stats = FoldStats::default();
        fold_switches(&mut nodes, &mut stats);
        assert_eq!(stats.switch, 1);
        let SNode::Switch { disc, cases } = &nodes[0] else {
            panic!("expected Switch: {nodes:?}")
        };
        assert_eq!(disc, &tm("x", 1));
        assert_eq!(cases.len(), 3);
        assert_eq!(cases[0].tests, vec![num(1.0)]);
        // Each folded case body gains a trailing break.
        assert_eq!(cases[0].body.last(), Some(&SNode::Break { label: None }));
        // A terminal case body keeps its own ending.
        let single = if_node(
            cmp(CmpOp::Eq, tm("x", 1), num(9.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            vec![],
        );
        let (disc, cases) = match_switch_chain(&single).expect("one case");
        assert_eq!(disc, tm("x", 1));
        assert_eq!(cases.len(), 1);
        assert!(!matches!(cases[0].body.last(), Some(SNode::Break { .. })));
        // … but a lone case never becomes a switch.
        let mut nodes = vec![single];
        let mut stats = FoldStats::default();
        fold_switches(&mut nodes, &mut stats);
        assert_eq!(stats.switch, 0);
        // A trailing else becomes the default case.
        let mut chain = chain_3_no_else();
        let SNode::If { otherwise, .. } = &mut chain else {
            unreachable!()
        };
        let SNode::If {
            otherwise: inner, ..
        } = &mut otherwise[0]
        else {
            unreachable!()
        };
        inner[0] = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
            vec![run(vec![expr_stmt(call0(ident("c")))])],
            vec![run(vec![expr_stmt(call0(ident("d")))])],
        );
        let mut nodes = vec![chain];
        let mut stats = FoldStats::default();
        fold_switches(&mut nodes, &mut stats);
        assert_eq!(stats.switch, 1);
        let SNode::Switch { cases, .. } = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(cases.len(), 4);
        assert!(cases[3].tests.is_empty(), "default arm: {cases:?}");
        // A nested switch on the same discriminant flattens (the inner
        // chain folds first when driving the full `fold` recursion).
        let nested = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![expr_stmt(call0(ident("a")))])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
                vec![run(vec![expr_stmt(call0(ident("b")))])],
                vec![if_node(
                    cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
                    vec![run(vec![expr_stmt(call0(ident("c")))])],
                    vec![],
                )],
            )],
        );
        let mut nodes = vec![nested];
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.switch, 2);
        let SNode::Switch { cases, .. } = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(cases.len(), 3, "flattened: {cases:?}");
        // A nested switch on a FOREIGN discriminant becomes the default
        // case (the flatten guard refuses it, the default arm takes it).
        let mixed = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![expr_stmt(call0(ident("a")))])],
            vec![SNode::Switch {
                disc: tm("y", 2),
                cases: vec![SwitchCase {
                    tests: vec![num(1.0)],
                    body: vec![],
                }],
            }],
        );
        let mut nodes = vec![mixed];
        let mut stats = FoldStats::default();
        fold_switches(&mut nodes, &mut stats);
        assert_eq!(stats.switch, 1);
        let SNode::Switch { cases, .. } = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(cases.len(), 2);
        assert!(
            cases[1].tests.is_empty(),
            "the foreign switch is the default"
        );
        assert!(matches!(cases[1].body[0], SNode::Switch { .. }));
    }

    #[test]
    fn switch_chain_bail_pins() {
        // The case body must not hold an unlabeled (loop) break.
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![SNode::Break { label: None }],
            vec![],
        );
        assert!(match_switch_chain(&bad).is_none());
        // … even nested inside an if/labeled/try in the arm…
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![SNode::Labeled {
                label: "l".to_string(),
                body: vec![SNode::Break { label: None }],
            }],
            vec![],
        );
        assert!(match_switch_chain(&bad).is_none());
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![try_node(
                vec![],
                vec![catch("e", vec![SNode::Break { label: None }])],
            )],
            vec![],
        );
        assert!(match_switch_chain(&bad).is_none());
        // … while a nested loop intercepts its own breaks.
        let ok = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![SNode::While {
                label: None,
                cond: None,
                body: vec![SNode::Break { label: None }],
            }],
            vec![],
        );
        assert!(match_switch_chain(&ok).is_some());
        // A nested chain on a DIFFERENT discriminant kills the fold
        // (the extension loop refuses the mismatched if).
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("y", 2), num(2.0)),
                vec![run(vec![])],
                vec![],
            )],
        );
        assert!(match_switch_chain(&bad).is_none());
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
                vec![SNode::Break { label: None }],
                vec![],
            )],
        );
        assert!(match_switch_chain(&bad).is_none());
        // Non-if / non-chain nodes are not chains.
        assert!(match_switch_chain(&SNode::Honest("h".to_string())).is_none());
        assert!(match_switch_chain(&if_node(ident("c"), vec![], vec![])).is_none());
        // switch_test: polarity and operand-order variants.
        let (d, l, pos) = switch_test(&cmp(CmpOp::StrictEq, tm("x", 1), num(1.0))).unwrap();
        assert!(pos && d == tm("x", 1) && l == num(1.0));
        let (d, l, pos) = switch_test(&cmp(CmpOp::Eq, num(1.0), tm("x", 1))).unwrap();
        assert!(pos && d == tm("x", 1) && l == num(1.0));
        let (.., pos) = switch_test(&isfalse(cmp(CmpOp::Eq, tm("x", 1), num(1.0)))).unwrap();
        assert!(!pos);
        let (.., pos) =
            switch_test(&isfalse(isfalse(cmp(CmpOp::Eq, tm("x", 1), num(1.0))))).unwrap();
        assert!(pos);
        assert!(switch_test(&cmp(CmpOp::NotEq, tm("x", 1), num(1.0))).is_none());
        assert!(switch_test(&cmp(CmpOp::Eq, num(1.0), num(2.0))).is_none());
        assert!(switch_test(&cmp(CmpOp::Eq, tm("x", 1), tm("y", 2))).is_none());
        assert!(switch_test(&ident("c")).is_none());
        // A negative-polarity head swaps the case/continuation arms.
        let swapped = if_node(
            isfalse(cmp(CmpOp::StrictEq, tm("x", 1), num(1.0))),
            vec![run(vec![expr_stmt(call0(ident("cont")))])],
            vec![run(vec![expr_stmt(call0(ident("case")))])],
        );
        let (.., cases) = match_switch_chain(&swapped).expect("polarity-swapped chain");
        assert_eq!(cases.len(), 2, "case + default: {cases:?}");
        // arm_has_loop_break: the remaining direct arms.
        assert!(arm_has_loop_break(&[SNode::Break { label: None }]));
        assert!(!arm_has_loop_break(&[SNode::Break {
            label: Some("l".to_string()),
        }]));
        assert!(arm_has_loop_break(&[if_node(
            ident("c"),
            vec![],
            vec![SNode::Break { label: None }],
        )]));
        assert!(!arm_has_loop_break(&[SNode::Switch {
            disc: ident("d"),
            cases: vec![SwitchCase {
                tests: vec![],
                body: vec![SNode::Break { label: None }],
            }],
        }]));
        assert!(!arm_has_loop_break(&[SNode::Continue { label: None }]));
        assert!(!arm_has_loop_break(&[SNode::Honest("h".to_string())]));
        assert!(!arm_has_loop_break(&[run(vec![])]));
    }

    // ── d-P8: the finally-idiom family ─────────────────────────────

    /// The finally-body template shared by the dispatch's run arm and
    /// every inlined copy. Rich enough to walk every canon arm.
    fn finally_template() -> Vec<Leaf> {
        vec![
            decl("f1", 70, call0(ident("notify"))),
            phi_decl("f2", 71),
            phi_assign("f3", ident("w")),
            Leaf::Raw(Stmt::StoreProp {
                object: ident("o"),
                name: "p".to_string(),
                dot_legal: true,
                value: tm("f1", 70),
                own: false,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: ident("o"),
                index: num(1.0),
                value: ident("v"),
                own: false,
            }),
            Leaf::Raw(Stmt::StoreDyn {
                object: ident("o"),
                key: ident("k"),
                value: ident("v"),
                own: false,
            }),
            Leaf::Raw(Stmt::DefineMethod {
                object: ident("o"),
                name: "m".to_string(),
                func: ident("f"),
                length: 0,
            }),
            Leaf::Raw(Stmt::StorePrivate {
                object: ident("o"),
                name: "q".to_string(),
                value: ident("v"),
                define: true,
            }),
            Leaf::Raw(Stmt::StoreSuper {
                name: None,
                key: Some(ident("k")),
                value: ident("v"),
            }),
            Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot: 0,
                name: "lx".to_string(),
                value: ident("v"),
            }),
            Leaf::Raw(Stmt::GlobalStore {
                name: "g".to_string(),
                value: ident("v"),
                tolerant: false,
            }),
            Leaf::Raw(Stmt::ModuleStore {
                index: 0,
                name: "m0".to_string(),
                value: ident("v"),
            }),
            Leaf::Raw(Stmt::CatchBind {
                name: "cb".to_string(),
            }),
            elided("ThrowIfTypeError"),
            Leaf::Destructure {
                obj: ident("o"),
                keys: vec![("k".to_string(), "dt".to_string())],
                rest: "dr".to_string(),
            },
            Leaf::Decl {
                name: "ld".to_string(),
                mutable: true,
                value: Some(ident("v")),
            },
            Leaf::Assign {
                target: "la".to_string(),
                value: ident("v"),
            },
        ]
    }

    /// The dispatch-shaped catch body: bookkeeping, the phi-dispatch
    /// switch (`case undefined:` runs the finally body; default is pure
    /// bookkeeping), then the rethrow-unless-hole conditional.
    fn dispatch_body() -> Vec<SNode> {
        vec![
            run(vec![phi_decl("pd", 60), phi_assign("x", tm("e", 61))]),
            SNode::Switch {
                disc: tm("d", 62),
                cases: vec![
                    SwitchCase {
                        tests: vec![undef()],
                        body: vec![
                            run(finally_template()),
                            run(vec![phi_assign("pz", ident("w"))]),
                            SNode::Break { label: None },
                        ],
                    },
                    SwitchCase {
                        tests: vec![],
                        body: vec![
                            run(vec![phi_assign("pz2", ident("z"))]),
                            SNode::Break { label: None },
                        ],
                    },
                ],
            },
            if_node(
                cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
                vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            ),
        ]
    }

    /// The protected construct: every region kind nesting an inlined
    /// finally copy before its exits. All regions fall through after
    /// stripping, so the fold also consumes the normal-completion copy
    /// in the tail.
    fn protected_body() -> Vec<SNode> {
        let copy = || run(finally_template());
        let ret = || run(vec![Leaf::Raw(Stmt::Return(Some(ident("retv"))))]);
        vec![
            SNode::While {
                label: Some("wl".to_string()),
                cond: Some(ident("wc")),
                body: vec![copy(), ret()],
            },
            SNode::Labeled {
                label: "lbl".to_string(),
                body: vec![
                    copy(),
                    SNode::Break {
                        label: Some("outer".to_string()),
                    },
                ],
            },
            SNode::DoWhile {
                label: None,
                body: vec![
                    run(vec![expr_stmt(ident("x"))]),
                    SNode::Break { label: None },
                ],
                cond: ident("dc"),
            },
            SNode::Switch {
                disc: ident("sd"),
                cases: vec![SwitchCase {
                    tests: vec![num(1.0)],
                    body: vec![copy(), ret()],
                }],
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("it"),
                body: vec![copy(), ret()],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("ob"),
                body: vec![copy(), ret()],
            },
            SNode::Try {
                body: vec![copy(), ret()],
                catches: vec![
                    catch("e2", vec![copy(), ret()]),
                    catch("e3", vec![run(vec![expr_stmt(ident("ok"))])]),
                ],
                note: None,
                finally: Some(vec![
                    copy(),
                    SNode::Break {
                        label: Some("outer".to_string()),
                    },
                ]),
            },
        ]
    }

    /// The full idiom site: the handler-protecting outer try, the
    /// normal-completion copy, and a post-copy tail mixing a leaf run
    /// and a control-flow node.
    fn finally_site() -> Vec<SNode> {
        vec![
            SNode::Try {
                body: protected_body(),
                catches: vec![catch("e", dispatch_body())],
                note: Some("protected body (finally idiom)".to_string()),
                finally: None,
            },
            run(finally_template()),
            run(vec![expr_stmt(ident("mid"))]),
            if_node(
                ident("tailc"),
                vec![run(vec![expr_stmt(ident("tc"))])],
                vec![],
            ),
            run(vec![expr_stmt(ident("tailend"))]),
        ]
    }

    /// The dispatch's finally body as tokens (for expectations).
    fn finally_template_tokens() -> Vec<FTok> {
        finally_template().into_iter().map(FTok::Leaf).collect()
    }

    #[test]
    fn finally_fold_non_unwrap_construct_with_tail_consumption() {
        let mut nodes = finally_site();
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.finally_fold, 1);
        // [hoisted phi decls, honesty note, try{…}finally{F}, tail…]
        assert_eq!(nodes[0], run(vec![phi_decl("pd", 60)]));
        assert!(matches!(&nodes[1], SNode::Honest(_)));
        let SNode::Try {
            body,
            catches,
            finally: Some(fin),
            ..
        } = &nodes[2]
        else {
            panic!("expected the folded try/finally: {nodes:?}")
        };
        assert!(catches.is_empty());
        assert_eq!(fin, &ft_regroup(finally_template_tokens()));
        // The inlined copies are gone from every region.
        let SNode::While { body: wbody, .. } = &body[0] else {
            unreachable!()
        };
        assert_eq!(
            wbody.as_slice(),
            [run(vec![Leaf::Raw(Stmt::Return(Some(ident("retv"))))])]
        );
        // The tail survived past the consumed normal-completion copy.
        assert_eq!(nodes[3], run(vec![expr_stmt(ident("mid"))]));
        assert!(matches!(&nodes[4], SNode::If { .. }));
        assert_eq!(nodes[5], run(vec![expr_stmt(ident("tailend"))]));
        assert_eq!(nodes.len(), 6);
    }

    #[test]
    fn ft_extract_dispatch_bail_pins() {
        let ok = dispatch_body();
        let idiom = ft_extract_dispatch(&ok, "e").expect("the corpus dispatch");
        assert_eq!(idiom.decls, vec![phi_decl("pd", 60)]);
        assert_eq!(idiom.canon, ft_canon(&idiom.body));
        // Only one dispatch switch may be present.
        let mut bad = ok.clone();
        bad.insert(2, ok[1].clone());
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // Only one rethrow conditional may be present.
        let mut bad = ok.clone();
        bad.push(ok[2].clone());
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // Real handler code (a non-bookkeeping leaf) bails.
        let mut bad = ok.clone();
        bad.insert(0, run(vec![expr_stmt(call0(ident("side_effect")))]));
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // A declare with an effectful initializer is not bookkeeping.
        let mut bad = ok.clone();
        bad.insert(0, run(vec![decl("eff", 65, call0(ident("f")))]));
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The rethrow must FOLLOW the dispatch.
        let mut bad = ok.clone();
        bad.swap(1, 2);
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The dispatch switch must have exactly two cases…
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases.push(SwitchCase {
            tests: vec![num(1.0)],
            body: vec![],
        });
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … one keyed `undefined` …
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[0].tests = vec![num(1.0)];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … and one default.
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[1].tests = vec![num(2.0)];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The default arm must be pure bookkeeping (+ a break).
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[1].body = vec![run(vec![expr_stmt(call0(ident("f")))])];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … while a labeled break there is not bookkeeping.
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[1].body = vec![SNode::Break {
            label: Some("l".to_string()),
        }];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The run arm must contain a non-bookkeeping finally body.
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[0].body = vec![
            run(vec![phi_assign("pz", ident("w"))]),
            SNode::Break { label: None },
        ];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The finally template forbids control transfers.
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[0].body = vec![
            run(vec![
                expr_stmt(ident("x")),
                Leaf::Raw(Stmt::Return(Some(ident("v")))),
            ]),
            SNode::Break { label: None },
        ];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … and nested control-flow nodes.
        let mut bad = ok.clone();
        let SNode::Switch { cases, .. } = &mut bad[1] else {
            unreachable!()
        };
        cases[0].body = vec![
            run(vec![expr_stmt(ident("x"))]),
            if_node(ident("c"), vec![], vec![]),
            SNode::Break { label: None },
        ];
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // The rethrow conditional must be a `hole != X` compare…
        let mut bad = ok.clone();
        bad[2] = if_node(ident("c"), vec![], vec![]);
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … with a hole operand…
        let mut bad = ok.clone();
        bad[2] = if_node(
            cmp(CmpOp::StrictNotEq, tm("x", 63), tm("y", 64)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
            vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        );
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … and the guard and rethrow must agree on the temp…
        let mut bad = ok.clone();
        bad[2] = if_node(
            cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))])],
            vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        );
        assert!(ft_extract_dispatch(&bad, "e").is_none());
        // … which must trace through the copy chain to the binding.
        let mut bad = ok.clone();
        let SNode::Stmts(bk) = &mut bad[0] else {
            unreachable!()
        };
        bk[1] = phi_assign("x", tm("note", 98));
        assert!(ft_extract_dispatch(&bad, "e").is_none());
    }

    #[test]
    fn ft_rethrow_temp_polarities_and_bails() {
        let ret_arm = || vec![run(vec![Leaf::Raw(Stmt::Return(None))])];
        let throw_arm = || vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])];
        // Un-negated: `hole != x` → then throws, else returns.
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &throw_arm(),
                &ret_arm(),
            ),
            Some("x".to_string())
        );
        // Hole on the right, NotEq, bookkeeping tolerated in the arms.
        let mut padded_ret = ret_arm();
        padded_ret.insert(0, run(vec![phi_assign("p", ident("q"))]));
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::NotEq, tm("x", 63), Expr::Lit(Lit::Hole)),
                &throw_arm(),
                &padded_ret,
            ),
            Some("x".to_string())
        );
        // Negated: `!(hole != x)` swaps the arms.
        assert_eq!(
            ft_rethrow_temp(
                &isfalse(cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63))),
                &ret_arm(),
                &throw_arm(),
            ),
            Some("x".to_string())
        );
        // The condition must be a != compare against the hole.
        assert_eq!(ft_rethrow_temp(&ident("c"), &throw_arm(), &ret_arm()), None);
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::Eq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &throw_arm(),
                &ret_arm(),
            ),
            None
        );
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Null), tm("x", 63)),
                &throw_arm(),
                &ret_arm(),
            ),
            None
        );
        // The return arm must contain a bare return…
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &throw_arm(),
                &[run(vec![Leaf::Raw(Stmt::Return(Some(ident("v"))))])],
            ),
            None
        );
        // … and no foreign leaves…
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &throw_arm(),
                &[run(vec![
                    expr_stmt(call0(ident("f"))),
                    Leaf::Raw(Stmt::Return(None)),
                ])],
            ),
            None
        );
        // … and the throw arm must throw a temp/ident…
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), ident("x")),
                &[run(vec![Leaf::Raw(Stmt::Throw(ident("x")))])],
                &ret_arm(),
            ),
            Some("x".to_string()),
            "idents rethrow fine"
        );
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &[run(vec![Leaf::Raw(Stmt::Throw(num(1.0)))])],
                &ret_arm(),
            ),
            None
        );
        // An arm without a terminal at all bails.
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &[run(vec![expr_stmt(ident("x"))])],
                &ret_arm(),
            ),
            None
        );
    }

    /// A minimal idiom for driving `ft_strip_exits` directly.
    fn test_idiom() -> FinallyIdiom {
        let body = vec![
            FTok::Leaf(decl("f1", 70, ident("v"))),
            FTok::Leaf(phi_assign("f3", ident("w"))),
        ];
        FinallyIdiom {
            canon: ft_canon(&body),
            body,
            decls: vec![],
        }
    }

    fn strip(nodes: &mut Vec<SNode>, idiom: &FinallyIdiom) -> (Result<(), ()>, usize) {
        let mut labels = Vec::new();
        let mut strips = 0;
        let r = ft_strip_exits(
            nodes,
            idiom,
            FtCtx {
                loops: 0,
                breakables: 0,
            },
            &mut labels,
            &mut strips,
        );
        (r, strips)
    }

    #[test]
    fn ft_strip_exits_exit_kinds_and_mismatch_bails() {
        let idiom = test_idiom();
        let copy = || {
            run(vec![
                decl("f1", 70, ident("v")),
                phi_assign("f3", ident("w")),
            ])
        };
        // An unlabeled break/continue at construct level needs a copy.
        let mut nodes = vec![copy(), SNode::Break { label: None }];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 1);
        assert_eq!(nodes.len(), 1);
        let mut nodes = vec![copy(), SNode::Continue { label: None }];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 1);
        // A copy-free construct is untouched.
        let mut nodes = vec![run(vec![expr_stmt(ident("a"))])];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 0);
        // If arms recurse.
        let mut nodes = vec![if_node(
            ident("c"),
            vec![copy(), run(vec![Leaf::Raw(Stmt::Return(None))])],
            vec![copy(), run(vec![Leaf::Raw(Stmt::Return(None))])],
        )];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 2);
        // An exit without room for its copy.
        let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(None))])];
        let (r, _) = strip(&mut nodes, &idiom);
        assert!(r.is_err());
        // An exit whose copy differs.
        let mut nodes = vec![
            run(vec![decl("f1", 70, ident("v"))]),
            run(vec![Leaf::Raw(Stmt::Return(None))]),
        ];
        let (r, _) = strip(&mut nodes, &idiom);
        assert!(r.is_err());
        // The return-value guard: the copy rebinds a name the return
        // reads.
        let mut nodes = vec![
            run(vec![
                decl("f1", 70, ident("v")),
                phi_assign("f3", ident("w")),
            ]),
            run(vec![Leaf::Raw(Stmt::Return(Some(tm("f3", 71))))]),
        ];
        let (r, _) = strip(&mut nodes, &idiom);
        assert!(r.is_err());
        // … but a copy assigning names the value does not read is fine.
        let mut nodes = vec![
            copy(),
            run(vec![Leaf::Raw(Stmt::Return(Some(ident("safe"))))]),
        ];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 1);
        // Loop-intercepted exits need no copy.
        let mut nodes = vec![SNode::While {
            label: None,
            cond: None,
            body: vec![
                run(vec![expr_stmt(ident("x"))]),
                SNode::Break { label: None },
                SNode::Continue { label: None },
            ],
        }];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 0);
        // A labeled exit naming an enclosing (pushed) label needs none.
        let mut nodes = vec![SNode::While {
            label: Some("wl".to_string()),
            cond: None,
            body: vec![
                run(vec![expr_stmt(ident("x"))]),
                SNode::Continue {
                    label: Some("wl".to_string()),
                },
            ],
        }];
        let (r, strips) = strip(&mut nodes, &idiom);
        assert!(r.is_ok() && strips == 0);
    }

    #[test]
    fn ft_fold_at_bail_pins() {
        // A catch body that is not the dispatch shape.
        let nodes = vec![SNode::Try {
            body: vec![],
            catches: vec![catch("e", vec![run(vec![expr_stmt(ident("x"))])])],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        }];
        assert!(ft_fold_at(&nodes, 0).is_none());
        // An exit in the protected construct without its copy.
        let nodes = vec![SNode::Try {
            body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        }];
        assert!(ft_fold_at(&nodes, 0).is_none());
        // A fall-through construct whose tail lacks the copy.
        let mut nodes = vec![SNode::Try {
            body: vec![run(vec![expr_stmt(ident("a"))])],
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        }];
        assert!(ft_fold_at(&nodes, 0).is_none());
        // … and with the right tail, the bare construct folds.
        nodes.push(run(finally_template()));
        let out = ft_fold_at(&nodes, 0).expect("tail copy consumed");
        assert!(matches!(&out[1], SNode::Honest(_)));
        let SNode::Try {
            finally: Some(fin), ..
        } = &out[2]
        else {
            unreachable!()
        };
        assert_eq!(fin.len(), 1, "the template regroups to one run");
        // A copy differing in the tail position bails.
        let mut nodes = vec![SNode::Try {
            body: vec![run(vec![expr_stmt(ident("a"))])],
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        }];
        nodes.push(run(vec![decl("f1", 70, ident("DIFFERENT"))]));
        assert!(ft_fold_at(&nodes, 0).is_none());
        // The unwrap form (sole inner try/catch) also folds; the inner
        // catch falls through, so the tail copy is consumed too.
        let inner = try_node(
            vec![
                run(finally_template()),
                run(vec![Leaf::Raw(Stmt::Return(None))]),
            ],
            vec![catch("ie", vec![run(vec![expr_stmt(ident("h"))])])],
        );
        let nodes = vec![
            SNode::Try {
                body: vec![inner],
                catches: vec![catch("e", dispatch_body())],
                note: Some("protected body (finally idiom)".to_string()),
                finally: None,
            },
            run(finally_template()),
        ];
        let out = ft_fold_at(&nodes, 0).expect("the unwrap construct");
        let SNode::Try {
            catches,
            finally: Some(_),
            ..
        } = &out[2]
        else {
            unreachable!()
        };
        assert_eq!(catches.len(), 1, "the inner catch survives the unwrap");
        // The idiom note is required (the driver pre-filter).
        let mut nodes = vec![SNode::Try {
            body: vec![],
            catches: vec![catch("e", dispatch_body())],
            note: Some("some other note".to_string()),
            finally: None,
        }];
        let mut stats = FoldStats::default();
        fold_finally(&mut nodes, &mut stats);
        assert_eq!(stats.finally_fold, 0);
        // … and a `finally: Some` try is never re-folded.
        let mut nodes = vec![SNode::Try {
            body: vec![],
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: Some(vec![]),
        }];
        let mut stats = FoldStats::default();
        fold_finally(&mut nodes, &mut stats);
        assert_eq!(stats.finally_fold, 0);
    }

    // ── d-P17: the plain-async for-await driver family ─────────────

    /// The N70 driver site: [pre-loop wiring, the `while (true)`
    /// driver]. Covers the variant arms the corpus never produces:
    /// interleaved honesty comments, elided guards, an
    /// `istrue`-wrapped done test, a plain-`Stmts` value binding, a
    /// trailing empty run in the done arm, and a store-carried
    /// bookkeeping phi collapsed by substitution.
    fn driver_shape() -> Vec<SNode> {
        vec![
            // The iterator setup + header wiring (pre-loop).
            run(vec![
                decl(
                    "it",
                    10,
                    Expr::Iter {
                        op: IterOp::GetAsyncIterator,
                        obj: bx(ident("src")),
                        status: NodeStatus::Plumbing,
                    },
                ),
                decl("next", 11, prop(tm("it", 10), "next")),
                phi_assign("np", tm("next", 11)),
                phi_assign("ip", tm("it", 10)),
                phi_assign("bk", ident("out")),
            ]),
            SNode::While {
                label: None,
                cond: None,
                body: vec![
                    run(vec![
                        phi_decl("np", 20),
                        phi_decl("ip", 21),
                        phi_decl("bk", 22),
                    ]),
                    SNode::Honest("dissolved wrapper".to_string()),
                    run(vec![
                        decl(
                            "res",
                            23,
                            Expr::Call {
                                callee: bx(tm("np", 20)),
                                this: Some(bx(tm("ip", 21))),
                                args: vec![],
                                kind: CallKind::Direct,
                            },
                        ),
                        elided("ThrowIfNotObject"),
                        decl(
                            "aw",
                            24,
                            Expr::Await {
                                value: bx(tm("res", 23)),
                                uncaught: true,
                            },
                        ),
                        elided("Guard"),
                        decl("done", 25, prop(tm("aw", 24), "done")),
                    ]),
                    if_node(
                        istrue(tm("done", 25)),
                        vec![
                            run(vec![expr_stmt(call1(ident("print"), ident("out")))]),
                            SNode::Break { label: None },
                            run(vec![]),
                        ],
                        vec![
                            run(vec![
                                decl("x", 26, prop(tm("aw", 24), "value")),
                                Leaf::Raw(Stmt::StoreProp {
                                    object: tm("bk", 22),
                                    name: "items".to_string(),
                                    dot_legal: true,
                                    value: tm("x", 26),
                                    own: false,
                                }),
                            ]),
                            run(vec![
                                phi_assign("np", tm("np", 20)),
                                phi_assign("ip", tm("ip", 21)),
                                phi_assign("bk", tm("bk", 22)),
                            ]),
                            SNode::Continue { label: None },
                        ],
                    ),
                    SNode::Honest("trailing".to_string()),
                ],
            },
        ]
    }

    /// The While body of a driver shape (for near-miss mutations).
    fn driver_body(nodes: &mut [SNode]) -> &mut Vec<SNode> {
        let SNode::While { body, .. } = &mut nodes[1] else {
            unreachable!()
        };
        body
    }

    /// A near-miss pin: one mutation of the valid driver shape must
    /// leave the fold unmatched.
    fn driver_bails(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = driver_shape();
        mutate(&mut nodes);
        assert!(
            match_for_await_driver(&nodes, 1).is_none(),
            "near-miss unexpectedly matched"
        );
    }

    #[test]
    fn for_await_driver_positive_fold() {
        let mut nodes = driver_shape();
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_await_of, 1);
        let SNode::ForOf {
            is_await: true,
            binding,
            iter,
            body,
        } = &nodes[0]
        else {
            panic!("expected the folded for-await: {nodes:?}")
        };
        assert_eq!(binding, "x");
        assert_eq!(iter, &ident("src"));
        // The bookkeeping phi collapsed to its invariant source.
        assert_eq!(
            body.as_slice(),
            [run(vec![Leaf::Raw(Stmt::StoreProp {
                object: ident("out"),
                name: "items".to_string(),
                dot_legal: true,
                value: tm("x", 26),
                own: false,
            })])]
        );
        // The done-arm tail was re-homed after the loop.
        assert_eq!(
            nodes[1],
            run(vec![expr_stmt(call1(ident("print"), ident("out")))])
        );
        assert_eq!(nodes.len(), 2);
    }

    #[test]
    fn for_await_driver_try_wrapped_binding() {
        let mut nodes = driver_shape();
        let body = driver_body(&mut nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        otherwise[0] = SNode::Try {
            body: vec![run(vec![
                decl("x", 26, prop(tm("aw", 24), "value")),
                Leaf::Raw(Stmt::StoreProp {
                    object: tm("bk", 22),
                    name: "items".to_string(),
                    dot_legal: true,
                    value: tm("x", 26),
                    own: false,
                }),
            ])],
            catches: vec![catch(
                "ce",
                vec![run(vec![
                    decl("rr", 55, prop(ident("it2"), "return")),
                    Leaf::Raw(Stmt::Throw(tm("ce", 56))),
                ])],
            )],
            note: None,
            finally: None,
        };
        assert!(match_for_await_driver(&nodes, 1).is_some());
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_await_of, 1);
        let SNode::ForOf { body, .. } = &nodes[0] else {
            unreachable!()
        };
        // The cleanup try dissolved loudly; the store survived.
        assert!(matches!(&body[0], SNode::Honest(_)), "{body:?}");
        assert!(matches!(&body[1], SNode::Stmts(_)));
        // A handler that is NOT the cleanup shape bails the fold.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            otherwise[0] = SNode::Try {
                body: vec![run(vec![decl("x", 26, prop(tm("aw", 24), "value"))])],
                catches: vec![catch("ce", vec![run(vec![expr_stmt(ident("x"))])])],
                note: None,
                finally: None,
            };
        });
    }

    #[test]
    fn for_await_driver_bail_pins() {
        // The iterator setup must be a GetAsyncIterator declare…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[0] = decl(
                "it",
                10,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            );
        });
        // … followed by the `.next` load on it.
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[1] = decl("next", 11, prop(tm("it", 10), "previous"));
        });
        // Every trailing assign must target a header phi.
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre.push(phi_assign("stray", ident("v")));
        });
        // The body scan accepts only runs / honesty comments before the
        // dispatch.
        driver_bails(|nodes| {
            driver_body(nodes).insert(1, SNode::Break { label: None });
        });
        // Nothing significant may follow the dispatch.
        driver_bails(|nodes| {
            driver_body(nodes).push(run(vec![expr_stmt(ident("extra"))]));
        });
        // The header must open with phi decls.
        driver_bails(|nodes| {
            driver_body(nodes)[0] = run(vec![]);
        });
        // The res call must be an argument-free call…
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[0] = decl(
                "res",
                23,
                Expr::Call {
                    callee: bx(tm("np", 20)),
                    this: Some(bx(tm("ip", 21))),
                    args: vec![ident("x")],
                    kind: CallKind::Direct,
                },
            );
        });
        // … of a header phi…
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[0] = decl("res", 23, call0(tm("other", 99)));
        });
        // … with the receiver phi as `this`.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[0] = decl("res", 23, call0(tm("np", 20)));
        });
        // The folded dispatch's await of `res` is required…
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[2] = decl(
                "aw",
                24,
                Expr::Await {
                    value: bx(tm("res", 23)),
                    uncaught: false,
                },
            );
        });
        // … and `done` must load `.done` off the await temp.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[4] = decl("done", 25, prop(tm("aw", 24), "finished"));
        });
        // No trailing header junk.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr.push(expr_stmt(ident("extra")));
        });
        // The wiring must feed both call phis.
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[2] = phi_assign("np", tm("it", 10));
        });
        // The done test is a POSITIVE test of the done temp: an
        // inverted or foreign test bails.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { cond, .. } = &mut body[3] else {
                unreachable!()
            };
            *cond = isfalse(tm("done", 25));
        });
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { cond, .. } = &mut body[3] else {
                unreachable!()
            };
            *cond = istrue(tm("other", 99));
        });
        // The done arm must end in the exit break.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            then.retain(|n| !matches!(n, SNode::Break { .. }));
        });
        // The else arm must yield the value binding…
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(bind) = &mut otherwise[0] else {
                unreachable!()
            };
            bind.remove(0);
        });
        // … from a run or cleanup try, not an arbitrary node.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            otherwise[0] = SNode::While {
                label: None,
                cond: None,
                body: vec![],
            };
        });
        // A bookkeeping phi with two different sources…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre.push(phi_assign("bk", ident("other")));
        });
        // … or an effectful source…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[4] = phi_assign("bk", call0(ident("f")));
        });
        // … or a phi-valued source…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[4] = phi_assign("bk", tm("np", 20));
        });
        // … bails. So does an unread-source phi still read in the body…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre.remove(4);
        });
        // … or referenced after the loop.
        driver_bails(|nodes| {
            nodes.push(run(vec![expr_stmt(tm("bk", 22))]));
        });
        // An internal temp surviving in the kept body bails.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(bind) = &mut otherwise[0] else {
                unreachable!()
            };
            bind.push(expr_stmt(tm("res", 23)));
        });
        // A surviving declare of a folded phi bails (without counting
        // as a use — the synthetic decl is name-only).
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(bind) = &mut otherwise[0] else {
                unreachable!()
            };
            bind.push(Leaf::Decl {
                name: "np".to_string(),
                mutable: true,
                value: None,
            });
        });
    }

    // ── N74-W4: rest-parameter reconstruction ──────────────────────

    /// A body with one CopyRestArgs shape, spread through every
    /// control-flow region (bare keep-alive statements plus one real
    /// use), a `rest` name collision, and every census leaf kind.
    fn rest_param_body() -> Vec<SNode> {
        let bare = || run(vec![expr_stmt(Expr::RestArgs { start_index: 1 })]);
        vec![
            run(vec![
                phi_assign("p", ident("z")),
                Leaf::Raw(Stmt::LexStore {
                    level: 0,
                    slot: 0,
                    name: "lx".to_string(),
                    value: ident("v"),
                }),
                Leaf::Raw(Stmt::GlobalStore {
                    name: "g".to_string(),
                    value: ident("v"),
                    tolerant: false,
                }),
                Leaf::Decl {
                    name: "ld".to_string(),
                    mutable: true,
                    value: None,
                },
                Leaf::Assign {
                    target: "la".to_string(),
                    value: ident("v"),
                },
                phi_decl("pd", 61),
                // The collision: `rest` is already taken.
                expr_stmt(ident("rest")),
                // The one real use of the rest array.
                decl("args", 60, Expr::RestArgs { start_index: 1 }),
            ]),
            if_node(ident("c"), vec![bare()], vec![bare()]),
            SNode::While {
                label: None,
                cond: Some(ident("w")),
                body: vec![bare()],
            },
            SNode::DoWhile {
                label: None,
                body: vec![bare()],
                cond: ident("dw"),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![bare()],
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![bare()],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![bare()],
            },
            SNode::Try {
                body: vec![bare()],
                catches: vec![catch("e", vec![bare()])],
                note: None,
                finally: Some(vec![bare()]),
            },
            SNode::Switch {
                disc: ident("s"),
                cases: vec![SwitchCase {
                    tests: vec![num(1.0)],
                    body: vec![bare()],
                }],
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ]
    }

    #[test]
    fn rest_param_fold_with_control_flow_and_name_collision() {
        let mut nodes = rest_param_body();
        let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
        assert_eq!(stats.rest_param, 1);
        // The staging slot dropped; the collision-free name joined.
        assert_eq!(params, vec!["h0", "a", "...rest$1"]);
        // The real use now reads the rest parameter…
        let SNode::Stmts(first) = &nodes[0] else {
            unreachable!()
        };
        assert!(
            first.iter().any(
                |l| matches!(l, Leaf::Raw(Stmt::Declare { value, .. }) if *value == ident("rest$1"))
            ),
            "{first:?}"
        );
        // … and every bare keep-alive statement is gone.
        let mut bare = 0usize;
        map_exprs_mut(&mut nodes, &mut |e| {
            if matches!(e, Expr::RestArgs { .. }) {
                bare += 1;
            }
        });
        assert_eq!(bare, 0);
        let mut leaves = 0usize;
        walk_leaves(&nodes, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::Expr(_))) {
                leaves += 1;
            }
        });
        assert_eq!(leaves, 1, "only the collision probe remains");
    }

    #[test]
    fn rest_param_fold_bail_pins() {
        // More than one CopyRestArgs shape.
        let mut nodes = vec![run(vec![
            decl("a", 60, Expr::RestArgs { start_index: 1 }),
            decl("b", 61, Expr::RestArgs { start_index: 2 }),
        ])];
        let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
        let before = params.clone();
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
        assert_eq!(stats.rest_param, 0);
        assert_eq!(params, before);
        // Fewer visible params than the rest index.
        let mut nodes = vec![run(vec![decl("a", 60, Expr::RestArgs { start_index: 1 })])];
        let mut params = vec!["h0".to_string()];
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
        assert_eq!(stats.rest_param, 0);
        // A dropped staging slot referenced in the body.
        let mut nodes = vec![run(vec![
            decl("a", 60, Expr::RestArgs { start_index: 1 }),
            expr_stmt(ident("p2")),
        ])];
        let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
        assert_eq!(stats.rest_param, 0);
        // The no-collision fast path keeps the plain name.
        let mut nodes = vec![run(vec![decl("a", 60, Expr::RestArgs { start_index: 1 })])];
        let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
        assert_eq!(stats.rest_param, 1);
        assert_eq!(params, vec!["h0", "a", "...rest"]);
    }

    // ── N74-W4: late declaration-site reconstruction ───────────────

    /// A conversion-candidate body touching every declaration-capable
    /// and non-capable region.
    fn late_decl_body() -> Vec<SNode> {
        let store = |slot: u16, name: &str| {
            Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot,
                name: name.to_string(),
                value: ident("v"),
            })
        };
        vec![
            run(vec![Leaf::Raw(Stmt::ScopePush {
                names: vec![Some("a".to_string())],
            })]),
            // Root: converted (function-scope let).
            run(vec![store(0, "r"), expr_stmt(ident("r"))]),
            // A labeled block is declaration-capable.
            SNode::Labeled {
                label: "lbl".to_string(),
                body: vec![run(vec![store(0, "l")])],
            },
            // So are the try body, catch, and finally regions.
            SNode::Try {
                body: vec![run(vec![store(0, "t")])],
                catches: vec![catch("e", vec![run(vec![store(0, "c")])])],
                note: None,
                finally: Some(vec![run(vec![store(0, "f")])]),
            },
            // Loops and switch cases are not capable: stores there stay
            // plain assignments (the name is also declared at the root
            // so the coverage model is satisfied).
            SNode::While {
                label: None,
                cond: None,
                body: vec![run(vec![store(0, "w")])],
            },
            SNode::DoWhile {
                label: None,
                body: vec![run(vec![store(0, "dw")])],
                cond: ident("dc"),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("it"),
                body: vec![run(vec![store(0, "fo")])],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("ob"),
                body: vec![run(vec![store(0, "fi")])],
            },
            SNode::Switch {
                disc: ident("sd"),
                cases: vec![SwitchCase {
                    tests: vec![num(1.0)],
                    body: vec![run(vec![store(0, "sw")])],
                }],
            },
            // An if arm is a capable region of its own.
            if_node(ident("ic"), vec![run(vec![store(0, "ia")])], vec![]),
            // Census-only leaf kinds (uses feeding the coverage model).
            run(vec![
                Leaf::Raw(Stmt::ScopePop),
                Leaf::Assign {
                    target: "asg".to_string(),
                    value: ident("v"),
                },
                Leaf::Raw(Stmt::Throw(ident("th"))),
                Leaf::Destructure {
                    obj: ident("ob"),
                    keys: vec![],
                    rest: "rest".to_string(),
                },
            ]),
            SNode::Break { label: None },
            SNode::Honest("h".to_string()),
        ]
    }

    #[test]
    fn late_decl_fold_regions_and_conversions() {
        let mut nodes = late_decl_body();
        let mut stats = FoldStats::default();
        late_decl_fold(&mut nodes, &[], true, &mut stats);
        // r (root) + l (labeled) + t/c/f (try regions) + ia (if arm).
        assert_eq!(stats.late_decl, 6, "{stats:?}");
        // The labeled-region store became the declaration.
        let SNode::Labeled { body, .. } = &nodes[2] else {
            unreachable!()
        };
        assert!(
            matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "l"))
        );
        // The try regions converted too.
        let SNode::Try {
            body,
            catches,
            finally: Some(fin),
            ..
        } = &nodes[3]
        else {
            unreachable!()
        };
        assert!(
            matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "t"))
        );
        assert!(
            matches!(&catches[0].body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "c"))
        );
        assert!(
            matches!(&fin[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "f"))
        );
        // The loop store is NOT declaration-capable: unchanged.
        let SNode::While { body, .. } = &nodes[4] else {
            unreachable!()
        };
        assert!(matches!(
            &body[0],
            SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::LexStore { name, .. }) if name == "w")
        ));
        // The root store became a declaration; its read is intact.
        let SNode::Stmts(root) = &nodes[1] else {
            unreachable!()
        };
        assert!(matches!(&root[0], Leaf::Decl { name, .. } if name == "r"));
    }

    #[test]
    fn late_decl_fold_bail_pins() {
        let store = |name: &str| {
            Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot: 0,
                name: name.to_string(),
                value: ident("v"),
            })
        };
        let push = || {
            run(vec![Leaf::Raw(Stmt::ScopePush {
                names: vec![Some("a".to_string())],
            })])
        };
        let bail = |nodes: Vec<SNode>, params: &[String], top: bool| {
            let mut nodes = nodes;
            let mut stats = FoldStats::default();
            late_decl_fold(&mut nodes, params, top, &mut stats);
            assert_eq!(stats.late_decl, 0, "{nodes:?}");
            nodes
        };
        // A lexical/global mix for one name.
        bail(
            vec![
                push(),
                run(vec![
                    store("m"),
                    Leaf::Raw(Stmt::GlobalStore {
                        name: "m".to_string(),
                        value: ident("v"),
                        tolerant: false,
                    }),
                ]),
            ],
            &[],
            true,
        );
        // A capture-level store (level >= own pushes).
        bail(
            vec![
                push(),
                run(vec![Leaf::Raw(Stmt::LexStore {
                    level: 5,
                    slot: 0,
                    name: "cap".to_string(),
                    value: ident("v"),
                })]),
            ],
            &[],
            true,
        );
        // A global store below the top level.
        bail(
            vec![run(vec![Leaf::Raw(Stmt::GlobalStore {
                name: "g".to_string(),
                value: ident("v"),
                tolerant: false,
            })])],
            &[],
            false,
        );
        // A function-valued binding at the module top.
        bail(
            vec![
                push(),
                run(vec![Leaf::Raw(Stmt::LexStore {
                    level: 0,
                    slot: 0,
                    name: "fv".to_string(),
                    value: Expr::Closure {
                        body: FuncId::new(0),
                        name: "f".to_string(),
                        kind: FunctionKind::Function,
                        captures: vec![],
                    },
                })]),
            ],
            &[],
            true,
        );
        // A parameter / an already-declared name.
        bail(
            vec![push(), run(vec![store("p")])],
            &["p".to_string()],
            true,
        );
        bail(
            vec![
                push(),
                run(vec![
                    Leaf::Decl {
                        name: "d".to_string(),
                        mutable: true,
                        value: None,
                    },
                    store("d"),
                ]),
            ],
            &[],
            true,
        );
        // A read outside the store's region is not covered.
        bail(
            vec![
                push(),
                SNode::Labeled {
                    label: "l".to_string(),
                    body: vec![run(vec![store("u")])],
                },
                run(vec![expr_stmt(ident("u"))]),
            ],
            &[],
            true,
        );
        // Nested converted regions (store in a try body AND in an if
        // arm inside it).
        bail(
            vec![
                push(),
                SNode::Try {
                    body: vec![
                        run(vec![store("n")]),
                        if_node(ident("c"), vec![run(vec![store("n")])], vec![]),
                    ],
                    catches: vec![],
                    note: None,
                    finally: None,
                },
            ],
            &[],
            true,
        );
        // A same-name re-push mid-span splits the binding.
        bail(
            vec![push(), run(vec![store("s")]), push(), run(vec![store("s")])],
            &[],
            true,
        );
        // The root fast path: one store covering everything converts.
        let mut nodes = vec![push(), run(vec![store("ok")])];
        let mut stats = FoldStats::default();
        late_decl_fold(&mut nodes, &[], true, &mut stats);
        assert_eq!(stats.late_decl, 1);
        // A second store of a converted name becomes an assignment.
        let mut nodes = vec![push(), run(vec![store("ok"), store("ok")])];
        let mut stats = FoldStats::default();
        late_decl_fold(&mut nodes, &[], true, &mut stats);
        assert_eq!(stats.late_decl, 1);
        let SNode::Stmts(got) = &nodes[1] else {
            unreachable!()
        };
        assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "ok"));
        assert!(matches!(&got[1], Leaf::Assign { target, .. } if target == "ok"));
    }

    #[test]
    fn scope_fold_push_site_variants() {
        let push = |names: &[&str]| {
            Leaf::Raw(Stmt::ScopePush {
                names: names.iter().map(|n| Some(n.to_string())).collect(),
            })
        };
        let store = |slot: u16, name: &str| {
            Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot,
                name: name.to_string(),
                value: ident("v"),
            })
        };
        // Both slots declared: the push is consumed.
        let mut nodes = vec![run(vec![push(&["a", "b"]), store(0, "a"), store(1, "b")])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 2);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "a"));
        assert_eq!(got.len(), 2, "the push was consumed: {got:?}");
        // A re-store of an initialized slot ends the init run; the
        // later re-store becomes a plain assignment.
        let mut nodes = vec![run(vec![push(&["a"]), store(0, "a"), store(0, "a")])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 1);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(matches!(&got[1], Leaf::Assign { target, .. } if target == "a"));
        // Elided/fallback markers interleave with the init run.
        let mut nodes = vec![run(vec![push(&["a"]), elided("Guard"), store(0, "a")])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 1);
        // A non-store leaf ends the init run: nothing converts.
        let mut nodes = vec![run(vec![
            push(&["a"]),
            expr_stmt(ident("x")),
            store(0, "a"),
        ])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 0);
        // A parameter name is never redeclared.
        let mut nodes = vec![run(vec![push(&["a"]), store(0, "a")])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &["a".to_string()], &mut stats);
        assert_eq!(stats.scope_fold, 0);
        // Two same-named slots in one push: only the first declares;
        // the push stays for the other slot.
        let mut nodes = vec![run(vec![push(&["n", "n"]), store(0, "n"), store(1, "n")])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 1);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(
            matches!(&got[0], Leaf::Raw(Stmt::ScopePush { names }) if names.len() == 1),
            "the undeclared slot keeps the push: {got:?}"
        );
        // A store of the same name in ANOTHER run blocks the fold.
        let mut nodes = vec![
            run(vec![push(&["a"]), store(0, "a")]),
            run(vec![store(0, "a")]),
        ];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 0);
        // A second push of an already-converted name skips it (same
        // run: the name declares at its first push only).
        let mut nodes = vec![run(vec![
            push(&["a"]),
            store(0, "a"),
            push(&["a"]),
            store(0, "a"),
        ])];
        let mut stats = FoldStats::default();
        scope_fold(&mut nodes, &[], &mut stats);
        assert_eq!(stats.scope_fold, 1, "a once: {nodes:?}");
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        // The first push was consumed (its slot declared); the second
        // push stays (its re-store was not an init-run candidate).
        assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "a"));
        assert!(
            got.iter()
                .any(|l| matches!(l, Leaf::Assign { target, .. } if target == "a"))
        );
    }

    // ── folds 1+2: literal builders / rest destructuring ───────────

    fn closure(name: &str) -> Expr {
        Expr::Closure {
            body: FuncId::new(0),
            name: name.to_string(),
            kind: FunctionKind::Function,
            captures: vec![],
        }
    }

    #[test]
    fn object_literal_full_absorb_matrix() {
        // One builder sequence with every absorbable statement kind:
        // literal-key dynamic store, computed dynamic store, literal
        // and computed index stores, spread, __proto__, a method, and
        // both accessor forms — plus an interleaved key temp that
        // inlines into the folded literal.
        let leaves = vec![
            decl(
                "o",
                10,
                Expr::ObjectLit {
                    entries: vec![(Lit::String("a".to_string()), Lit::Number(1.0f64.to_bits()))],
                },
            ),
            decl("ck", 11, call0(ident("key_fn"))), // skipped, used once
            Leaf::Raw(Stmt::StoreDyn {
                object: tm("o", 10),
                key: tm("ck", 11),
                value: num(2.0),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreDyn {
                object: tm("o", 10),
                key: strlit("lit"),
                value: num(3.0),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("o", 10),
                index: num(7.0),
                value: num(4.0),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("o", 10),
                index: tm("ix", 12),
                value: num(5.0),
                own: true,
            }),
            expr_stmt(Expr::CopyDataProps {
                dst: bx(tm("o", 10)),
                src: bx(ident("src")),
            }),
            expr_stmt(Expr::SetObjectWithProto {
                obj: bx(tm("o", 10)),
                proto: bx(ident("proto")),
            }),
            Leaf::Raw(Stmt::DefineMethod {
                object: tm("o", 10),
                name: "m".to_string(),
                func: closure("mf"),
                length: 0,
            }),
            expr_stmt(Expr::DefineGetterSetter {
                obj: bx(tm("o", 10)),
                key: bx(strlit("acc")),
                getter: bx(closure("ag")),
                setter: bx(Expr::Lit(Lit::Undefined)),
            }),
            expr_stmt(Expr::DefineGetterSetter {
                obj: bx(tm("o", 10)),
                key: bx(num(9.0)),
                getter: bx(Expr::Lit(Lit::Undefined)),
                setter: bx(closure("as")),
            }),
            expr_stmt(call0(ident("unrelated"))),
        ];
        let mut leaves = leaves;
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 1);
        let [
            Leaf::Raw(Stmt::Declare { value, .. }),
            Leaf::Raw(Stmt::Expr(_)),
        ] = leaves.as_slice()
        else {
            panic!("declare + trailing stmt: {leaves:?}")
        };
        let Expr::ObjectBuild { entries } = value else {
            panic!("folded literal: {value:?}")
        };
        let kinds: Vec<&str> = entries
            .iter()
            .map(|e| match e {
                ObjEntry::KeyValue(..) => "kv",
                ObjEntry::Computed(..) => "computed",
                ObjEntry::Spread(..) => "spread",
                ObjEntry::Proto(..) => "proto",
                ObjEntry::Method(..) => "method",
                ObjEntry::Getter(..) => "getter",
                ObjEntry::Setter(..) => "setter",
            })
            .collect();
        assert_eq!(
            kinds,
            [
                "kv", "computed", "kv", "kv", "computed", "spread", "proto", "method", "getter",
                "setter"
            ]
        );
        // The skipped key temp inlined into the computed entry.
        assert_eq!(
            entries[1],
            ObjEntry::Computed(call0(ident("key_fn")), num(2.0))
        );
        // Literal keys via StoreDyn/StoreIndex keep the literal form.
        assert_eq!(
            entries[2],
            ObjEntry::KeyValue(Lit::String("lit".to_string()), num(3.0))
        );
        assert_eq!(
            entries[3],
            ObjEntry::KeyValue(Lit::Number(7.0f64.to_bits()), num(4.0))
        );
        // The accessor keys: a literal name and a computed expression.
        assert!(matches!(&entries[8], ObjEntry::Getter(ObjKey::Name(n), _) if n == "acc"));
        assert!(matches!(
            &entries[9],
            ObjEntry::Setter(ObjKey::Computed(_), _)
        ));
    }

    #[test]
    fn array_literal_contiguity_and_spread() {
        // Strict contiguity from the shape length; a spread ends the
        // absorbable run of items.
        let leaves = vec![
            decl(
                "a",
                20,
                Expr::ArrayLit {
                    elements: vec![Lit::Number(0.0f64.to_bits())],
                },
            ),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(1.0),
                value: ident("e1"),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(2.0),
                value: ident("e2"),
                own: true,
            }),
            expr_stmt(Expr::ArraySpread {
                dst: bx(tm("a", 20)),
                index: bx(num(3.0)),
                src: bx(ident("rest")),
            }),
            // Past a spread the running index is unknowable: stays.
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(3.0),
                value: ident("e3"),
                own: true,
            }),
        ];
        let mut leaves = leaves;
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.array_lit, 1);
        let Leaf::Raw(Stmt::Declare { value, .. }) = &leaves[0] else {
            unreachable!()
        };
        let Expr::ArrayBuild { elements } = value else {
            panic!("folded array: {value:?}")
        };
        assert_eq!(elements.len(), 4);
        assert!(matches!(&elements[3], ArrayElem::Spread(e) if *e == ident("rest")));
        assert!(
            matches!(&leaves[1], Leaf::Raw(Stmt::StoreIndex { .. })),
            "the post-spread store stays: {leaves:?}"
        );
        // A gap index keeps the store out of the literal.
        let mut leaves = vec![
            decl("a", 20, Expr::ArrayLit { elements: vec![] }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(5.0),
                value: ident("e1"),
                own: true,
            }),
        ];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.array_lit, 0);
        assert_eq!(leaves.len(), 2);
        // A non-literal index / a non-own store are never items.
        let mut leaves = vec![
            decl("a", 20, Expr::ArrayLit { elements: vec![] }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: ident("i"),
                value: ident("e1"),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(0.0),
                value: ident("e2"),
                own: false,
            }),
        ];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.array_lit, 0);
        // A fractional/negative index is not an array slot.
        let mut leaves = vec![
            decl("a", 20, Expr::ArrayLit { elements: vec![] }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(1.5),
                value: ident("e1"),
                own: true,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: tm("a", 20),
                index: num(-1.0),
                value: ident("e2"),
                own: true,
            }),
        ];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.array_lit, 0);
    }

    #[test]
    fn literal_builder_bail_pins() {
        let obj = || decl("o", 10, Expr::ObjectLit { entries: vec![] });
        // absorb_one guards, one per arm.
        let vid = ValueId::new(10);
        // A non-own store is not a literal entry.
        assert!(
            absorb_one(
                &Leaf::Raw(Stmt::StoreProp {
                    object: tm("o", 10),
                    name: "k".to_string(),
                    dot_legal: true,
                    value: ident("v"),
                    own: false,
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // A self-referential value can never be reordered.
        assert!(
            absorb_one(
                &Leaf::Raw(Stmt::StoreProp {
                    object: tm("o", 10),
                    name: "k".to_string(),
                    dot_legal: true,
                    value: tm("o", 10),
                    own: true,
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // A computed-key store whose KEY mentions the object.
        assert!(
            absorb_one(
                &Leaf::Raw(Stmt::StoreDyn {
                    object: tm("o", 10),
                    key: tm("o", 10),
                    value: ident("v"),
                    own: true,
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // A spread whose source mentions the object.
        assert!(
            absorb_one(
                &expr_stmt(Expr::CopyDataProps {
                    dst: bx(tm("o", 10)),
                    src: bx(tm("o", 10)),
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // A proto set on a different object.
        assert!(
            absorb_one(
                &expr_stmt(Expr::SetObjectWithProto {
                    obj: bx(ident("other")),
                    proto: bx(ident("p")),
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // An array spread is not an object entry (and vice versa).
        assert!(
            absorb_one(
                &expr_stmt(Expr::ArraySpread {
                    dst: bx(tm("o", 10)),
                    index: bx(num(0.0)),
                    src: bx(ident("s")),
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // Accessors must be closures or the undefined absence marker…
        assert!(
            absorb_one(
                &expr_stmt(Expr::DefineGetterSetter {
                    obj: bx(tm("o", 10)),
                    key: bx(strlit("k")),
                    getter: bx(call0(ident("not_a_closure_value"))),
                    setter: bx(Expr::Lit(Lit::Undefined)),
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // … and at least one of them must exist.
        assert!(
            absorb_one(
                &expr_stmt(Expr::DefineGetterSetter {
                    obj: bx(tm("o", 10)),
                    key: bx(strlit("k")),
                    getter: bx(Expr::Lit(Lit::Undefined)),
                    setter: bx(Expr::Lit(Lit::Undefined)),
                }),
                vid,
                false,
                &[],
                0,
            )
            .is_none()
        );
        // An unrelated statement is never absorbable.
        assert!(absorb_one(&expr_stmt(ident("x")), vid, false, &[], 0).is_none());
        let _ = obj;

        // The skipped-declare resolution (N74-W4).
        // A pure unused declare interleaved in the sequence drops.
        let mut leaves = vec![
            obj(),
            decl("dead", 11, strlit("pure")),
            Leaf::Raw(Stmt::StoreProp {
                object: tm("o", 10),
                name: "k".to_string(),
                dot_legal: true,
                value: ident("v"),
                own: true,
            }),
        ];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 1);
        assert_eq!(leaves.len(), 1, "the dead declare dropped: {leaves:?}");
        // A temp chain inlines in decision order (k1 → k2 → the entry).
        let mut leaves = vec![
            obj(),
            decl("k1", 11, strlit("one")),
            decl("k2", 12, tm("k1", 11)),
            Leaf::Raw(Stmt::StoreDyn {
                object: tm("o", 10),
                key: tm("k2", 12),
                value: ident("v"),
                own: true,
            }),
        ];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 1);
        let Leaf::Raw(Stmt::Declare { value, .. }) = &leaves[0] else {
            unreachable!()
        };
        let Expr::ObjectBuild { entries } = value else {
            unreachable!()
        };
        assert_eq!(
            entries[0],
            ObjEntry::Computed(strlit("one"), ident("v")),
            "chained inline: {entries:?}"
        );
        // A temp used twice cannot inline: the whole fold bails.
        let mut leaves = vec![
            obj(),
            decl("ck", 11, call0(ident("key_fn"))),
            Leaf::Raw(Stmt::StoreDyn {
                object: tm("o", 10),
                key: tm("ck", 11),
                value: tm("ck", 11),
                own: true,
            }),
        ];
        let before = leaves.clone();
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 0);
        assert_eq!(leaves, before);
        // An impure skipped declare used nowhere also bails the fold.
        let mut leaves = vec![
            obj(),
            decl("ck", 11, call0(ident("key_fn"))),
            Leaf::Raw(Stmt::StoreProp {
                object: tm("o", 10),
                name: "k".to_string(),
                dot_legal: true,
                value: ident("v"),
                own: true,
            }),
        ];
        let before = leaves.clone();
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 0);
        assert_eq!(leaves, before);
        // A declare of a non-literal value is not a builder start.
        let mut leaves = vec![decl("o", 10, ident("not_a_literal"))];
        let mut stats = FoldStats::default();
        fold_literal_builders(&mut leaves, &mut stats);
        assert_eq!(stats.object_lit, 0);
    }

    #[test]
    fn rest_destructure_key_forms_and_bails() {
        // The excluded keys resolve through PropName / PropDyn /
        // PropIndex loads (literals only for the computed forms).
        let mut leaves = vec![
            decl("x", 21, prop(ident("o"), "a")),
            decl(
                "rest",
                20,
                Expr::RestObject {
                    obj: bx(ident("o")),
                    excluded: vec![strlit("a"), strlit("b"), strlit("c")],
                },
            ),
            decl(
                "y",
                22,
                Expr::PropDyn {
                    object: bx(ident("o")),
                    key: bx(strlit("b")),
                },
            ),
            decl(
                "z",
                23,
                Expr::PropIndex {
                    object: bx(ident("o")),
                    index: bx(strlit("c")),
                },
            ),
        ];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 1);
        assert_eq!(
            leaves,
            vec![Leaf::Destructure {
                obj: ident("o"),
                keys: vec![
                    ("a".to_string(), "x".to_string()),
                    ("b".to_string(), "y".to_string()),
                    ("c".to_string(), "z".to_string()),
                ],
                rest: "rest".to_string(),
            }]
        );
        // A non-string excluded key is not a destructure.
        let mut leaves = vec![decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![num(1.0)],
            },
        )];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 0);
        // An empty exclusion list is not this shape.
        let mut leaves = vec![decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![],
            },
        )];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 0);
        // A missing sibling declare keeps the shape loud.
        let mut leaves = vec![decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![strlit("a")],
            },
        )];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 0);
        // A computed load with a non-literal key is no key load.
        let mut leaves = vec![
            decl(
                "rest",
                20,
                Expr::RestObject {
                    obj: bx(ident("o")),
                    excluded: vec![strlit("a")],
                },
            ),
            decl(
                "y",
                22,
                Expr::PropDyn {
                    object: bx(ident("o")),
                    key: bx(ident("k")),
                },
            ),
        ];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 0);
        // The load's object must be the rest source (structurally).
        let mut leaves = vec![
            decl(
                "rest",
                20,
                Expr::RestObject {
                    obj: bx(ident("o")),
                    excluded: vec![strlit("a")],
                },
            ),
            decl("y", 22, prop(ident("OTHER"), "a")),
        ];
        let mut stats = FoldStats::default();
        fold_rest_destructure(&mut leaves, &mut stats);
        assert_eq!(stats.rest, 0);
        // key_load_target directly: the catch-all arm.
        assert_eq!(key_load_target(&call0(ident("f")), &ident("o")), None);
        assert_eq!(
            key_load_target(&prop(ident("o"), "k"), &ident("o")),
            Some(&"k".to_string())
        );
    }

    // ── d-P11: the generator driver fold ───────────────────────────

    /// The mode dispatch on `m`: `if (m == 0) return r; if (m == 1)
    /// throw r; <continuation>`.
    fn gen_dispatch(m: &str, mv: u32, r: &str, rv: u32, cont: Vec<SNode>) -> SNode {
        if_node(
            cmp(CmpOp::Eq, tm(m, mv), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm(r, rv))))])],
            vec![if_node(
                cmp(CmpOp::Eq, tm(m, mv), num(1.0)),
                vec![run(vec![
                    Leaf::Raw(Stmt::Throw(tm(r, rv))),
                    Leaf::Raw(Stmt::Unreachable),
                ])],
                cont,
            )],
        )
    }

    /// A generator body: the entry site, one yield point whose resume
    /// value is used (`const r1 = yield v`), and one whose is not.
    /// Each site is ONE run: `[yield-stmt, r = ResumeGenerator(g),
    /// m = GetResumeMode(g)]` followed by the mode dispatch sibling.
    fn generator_body() -> Vec<SNode> {
        let site = |pre: Leaf, r: &str, rv: u32, m: &str, mv: u32| {
            run(vec![
                pre,
                decl(
                    r,
                    rv,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 50)),
                    },
                ),
                decl(
                    m,
                    mv,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 50)),
                    },
                ),
            ])
        };
        let yield_stmt = |v: &str| {
            expr_stmt(Expr::Yield {
                value: bx(Expr::IterResultObj {
                    value: bx(ident(v)),
                    done: bx(boolean(false)),
                }),
            })
        };
        vec![
            run(vec![
                decl(
                    "g",
                    50,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
                decl(
                    "r0",
                    51,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 50)),
                    },
                ),
                decl(
                    "m0",
                    52,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 50)),
                    },
                ),
            ]),
            gen_dispatch("m0", 52, "r0", 51, vec![]),
            site(yield_stmt("v"), "r1", 53, "m1", 54),
            gen_dispatch("m1", 54, "r1", 53, vec![run(vec![expr_stmt(tm("r1", 53))])]),
            site(yield_stmt("w"), "r2", 55, "m2", 56),
            gen_dispatch(
                "m2",
                56,
                "r2",
                55,
                vec![run(vec![expr_stmt(ident("cont"))])],
            ),
        ]
    }

    #[test]
    fn generator_machine_fold_positive() {
        let mut nodes = generator_body();
        let mut stats = FoldStats::default();
        generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.gen_driver_entry, 1);
        assert_eq!(stats.gen_driver_sites, 3);
        assert_eq!(stats.gen_driver_bound, 1);
        // The funcObj temp is swept once nothing references it.
        assert!(!nodes_use_temp(&nodes, ValueId::new(50)));
        // The bound yield keeps its resume temp as a declare.
        let bound = nodes.iter().any(|n| {
            matches!(
                n,
                SNode::Stmts(run) if run.iter().any(|l| matches!(
                    l,
                    Leaf::Raw(Stmt::Declare {
                        name,
                        value: Expr::Yield { .. },
                        ..
                    }) if name == "r1"
                ))
            )
        });
        assert!(bound, "{nodes:?}");
        // The unbound yield is a bare expression statement.
        let bare = nodes.iter().any(|n| {
            matches!(
                n,
                SNode::Stmts(run) if run.iter().any(|l| matches!(
                    l,
                    Leaf::Raw(Stmt::Expr(Expr::Yield { value }))
                        if value.as_ref() == &ident("w")
                ))
            )
        });
        assert!(bare, "{nodes:?}");
        // Non-generator kinds are a no-op.
        let mut nodes = generator_body();
        let before = nodes.clone();
        let mut stats = FoldStats::default();
        generator_machine_fold(&mut nodes, FunctionKind::Function, &mut stats);
        assert_eq!(nodes, before);
        assert_eq!(stats.gen_driver_sites, 0);
        // Two CreateGenerator temps are not the vendor shape.
        let mut nodes = generator_body();
        let SNode::Stmts(entry) = &mut nodes[0] else {
            unreachable!()
        };
        entry.push(decl(
            "g2",
            90,
            Expr::CreateGenerator {
                func: bx(closure("h")),
            },
        ));
        let mut stats = FoldStats::default();
        generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.gen_driver_sites, 0);
        // The entry gate: the dispatch must follow the pair.
        let mut nodes = generator_body();
        nodes[1] = run(vec![expr_stmt(ident("not_a_dispatch"))]);
        let mut stats = FoldStats::default();
        generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.gen_driver_entry, 0);
    }

    #[test]
    fn generator_entry_nested_in_regions() {
        // entry_site_matches recurses through if/loop/try regions.
        for wrap in [
            |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::While {
                    label: None,
                    cond: Some(ident("c")),
                    body: site,
                }]
            },
            |site: Vec<SNode>| {
                vec![SNode::Labeled {
                    label: "l".to_string(),
                    body: site,
                }]
            },
            |site: Vec<SNode>| vec![try_node(site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::Try {
                    body: vec![],
                    catches: vec![catch("e", site)],
                    note: None,
                    finally: Some(vec![]),
                }]
            },
        ] {
            let mut nodes = wrap(generator_body());
            let mut stats = FoldStats::default();
            generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
            assert_eq!(stats.gen_driver_entry, 1, "nested entry gate");
        }
    }

    #[test]
    fn generator_driver_site_bail_pins() {
        let body = generator_body();
        let mut cx = GenDriverCx {
            genobj: ValueId::new(50),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
        };
        assert!(match_driver_site(&body, 0, &mut cx).is_some());
        assert!(match_driver_site(&body, 2, &mut cx).is_some());
        // The site must be a statement run…
        assert!(match_driver_site(&[SNode::Honest("h".to_string())], 0, &mut cx).is_none());
        // … ending in the ResumeGenerator/GetResumeMode pair.
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site.pop();
        assert!(match_driver_site(&bad, 0, &mut cx).is_none());
        // … on the SAME genobj temp.
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site[3] = decl(
            "m0",
            52,
            Expr::GeneratorDriver {
                resume: false,
                genobj: bx(tm("other", 99)),
            },
        );
        assert!(match_driver_site(&bad, 0, &mut cx).is_none());
        // The pre leaf must be a yield…
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site[1] = expr_stmt(ident("x"));
        assert!(match_driver_site(&bad, 0, &mut cx).is_none());
        // … wrapping a `done: false` iter-result at a real yield point…
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[2] else {
            unreachable!()
        };
        site[0] = expr_stmt(Expr::Yield {
            value: bx(Expr::IterResultObj {
                value: bx(ident("v")),
                done: bx(boolean(true)),
            }),
        });
        assert!(match_driver_site(&bad, 2, &mut cx).is_none());
        // … or the entry undefined, and the entry's run must declare the
        // genobj it suspends.
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site.remove(0);
        assert!(!entry_site_matches(&bad, &mut cx));
    }

    #[test]
    fn generator_dispatch_bail_pins() {
        let mut consumed = BTreeSet::new();
        let env = BTreeMap::new();
        let ok = gen_dispatch("m", 52, "r", 51, vec![run(vec![expr_stmt(ident("cont"))])]);
        let cont = match_dispatch(&ok, ValueId::new(52), ValueId::new(51), &env, &mut consumed);
        assert_eq!(cont, Some(vec![run(vec![expr_stmt(ident("cont"))])]));
        // The dispatch node must be an if.
        assert!(
            match_dispatch(
                &SNode::Honest("h".to_string()),
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed,
            )
            .is_none()
        );
        // … on a `mode == number` test…
        let bad = if_node(ident("c"), vec![], vec![]);
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // … of the matched mode temp…
        let bad = if_node(
            cmp(CmpOp::Eq, tm("other", 99), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // … with a resolvable immediate (a literal or known const temp).
        let bad = if_node(
            cmp(CmpOp::Eq, tm("m", 52), tm("c", 98)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        let bad = if_node(
            cmp(CmpOp::Eq, tm("m", 52), call0(ident("f"))),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // Only RETURN(0)/THROW(1) cases…
        let bad = if_node(
            cmp(CmpOp::Eq, tm("m", 52), num(5.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // … each once: a second RETURN test mid-chain bails.
        let bad = if_node(
            cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![if_node(
                cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
                vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
                vec![],
            )],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // The chain descends through a pure-const run (the optimized
        // profile) but nothing else.
        let env: BTreeMap<ValueId, u64> =
            [(ValueId::new(98), 1.0f64.to_bits())].into_iter().collect();
        let good = if_node(
            cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![
                run(vec![decl("c1", 98, num(1.0))]),
                if_node(
                    cmp(CmpOp::Eq, tm("m", 52), tm("c1", 98)),
                    vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 51)))])],
                    vec![run(vec![expr_stmt(ident("cont"))])],
                ),
            ],
        );
        let cont = match_dispatch(
            &good,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed,
        );
        assert_eq!(cont, Some(vec![run(vec![expr_stmt(ident("cont"))])]));
        assert!(consumed.contains(&ValueId::new(98)));
        let bad = if_node(
            cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![run(vec![decl("c1", 98, ident("not_a_const"))])],
        );
        assert!(
            match_dispatch(
                &bad,
                ValueId::new(52),
                ValueId::new(51),
                &env,
                &mut consumed
            )
            .is_none()
        );
        // mode_test: polarity wraps and operand order.
        let (bits, pos) = mode_test(
            &isfalse(cmp(CmpOp::Eq, num(1.0), tm("m", 52))),
            ValueId::new(52),
            &env,
            &mut consumed,
        )
        .expect("wrapped reversed");
        assert_eq!(f64::from_bits(bits), 1.0);
        assert!(!pos);
        let (.., pos) = mode_test(
            &istrue(cmp(CmpOp::Eq, tm("m", 52), num(0.0))),
            ValueId::new(52),
            &env,
            &mut consumed,
        )
        .unwrap();
        assert!(pos);
        assert!(mode_test(&ident("c"), ValueId::new(52), &env, &mut consumed).is_none());
        // check_return_arm / check_throw_arm shapes.
        let resume = ValueId::new(51);
        assert!(
            check_return_arm(
                &[run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
                resume
            )
            .is_some()
        );
        // … with dead loop-bookkeeping breaks after the return.
        assert!(
            check_return_arm(
                &[
                    run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))]),
                    SNode::Break { label: None },
                ],
                resume,
            )
            .is_some()
        );
        assert!(check_return_arm(&[SNode::Honest("h".to_string())], resume).is_none());
        assert!(
            check_return_arm(
                &[
                    run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))]),
                    run(vec![expr_stmt(ident("x"))]),
                ],
                resume,
            )
            .is_none()
        );
        assert!(
            check_return_arm(
                &[run(vec![Leaf::Raw(Stmt::Return(Some(tm("x", 99))))])],
                resume
            )
            .is_none()
        );
        assert!(check_return_arm(&[run(vec![expr_stmt(ident("x"))])], resume).is_none());
        assert!(
            check_throw_arm(&[run(vec![Leaf::Raw(Stmt::Throw(tm("r", 51)))])], resume).is_some()
        );
        assert!(
            check_throw_arm(
                &[run(vec![
                    Leaf::Raw(Stmt::Throw(tm("r", 51))),
                    Leaf::Raw(Stmt::Unreachable),
                ])],
                resume,
            )
            .is_some()
        );
        assert!(check_throw_arm(&[SNode::Honest("h".to_string())], resume).is_none());
        assert!(
            check_throw_arm(&[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 99)))])], resume).is_none()
        );
        assert!(check_throw_arm(&[run(vec![expr_stmt(ident("x"))])], resume).is_none());
        // resolve_num directly.
        assert_eq!(
            resolve_num(&num(2.0), &env, &mut consumed),
            Some(2.0f64.to_bits())
        );
        assert_eq!(
            resolve_num(&tm("c1", 98), &env, &mut consumed),
            Some(1.0f64.to_bits())
        );
        assert_eq!(resolve_num(&tm("unknown", 97), &env, &mut consumed), None);
        assert_eq!(resolve_num(&ident("x"), &env, &mut consumed), None);
    }

    // ── N68/G6: the async-completion fold ──────────────────────────

    #[test]
    fn async_driver_fold_direct_and_temp_forms() {
        // The inlined form: `return asyncDriver(v)` directly.
        for (resolve, is_throw) in [(true, false), (false, true)] {
            let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
                Expr::AsyncDriver {
                    resolve,
                    value: bx(ident("v")),
                },
            )))])];
            let mut stats = FoldStats::default();
            async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
            assert_eq!(stats.async_driver, 1);
            let SNode::Stmts(run) = &nodes[0] else {
                unreachable!()
            };
            if is_throw {
                assert!(matches!(&run[0], Leaf::Raw(Stmt::Throw(e)) if *e == ident("v")));
            } else {
                assert!(matches!(&run[0], Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("v")));
            }
        }
        // The temp form: `const t = asyncDriver(v); return t;`.
        let mut nodes = vec![run(vec![
            decl(
                "t",
                60,
                Expr::AsyncDriver {
                    resolve: true,
                    value: bx(ident("v")),
                },
            ),
            Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
        ])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_driver, 1);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(matches!(&got[0], Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("v")));
        assert_eq!(got.len(), 1);
        // … and `reject` + `throw t`.
        let mut nodes = vec![run(vec![
            decl(
                "t",
                60,
                Expr::AsyncDriver {
                    resolve: false,
                    value: bx(ident("e")),
                },
            ),
            Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
        ])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.async_driver, 1);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(matches!(&got[0], Leaf::Raw(Stmt::Throw(e)) if *e == ident("e")));
        // The temp form requires the adjacent return…
        let mut nodes = vec![run(vec![
            decl(
                "t",
                60,
                Expr::AsyncDriver {
                    resolve: true,
                    value: bx(ident("v")),
                },
            ),
            expr_stmt(ident("gap")),
            Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
        ])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_driver, 0);
        // … and no other uses of the temp.
        let mut nodes = vec![run(vec![
            decl(
                "t",
                60,
                Expr::AsyncDriver {
                    resolve: true,
                    value: bx(ident("v")),
                },
            ),
            Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
            expr_stmt(tm("t", 60)),
        ])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_driver, 0);
        // Non-async kinds are a no-op.
        let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
        )))])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.async_driver, 0);
    }

    // ── N68: the async suspend/resume machine fold ─────────────────

    /// An async body: the entry temp, an optimized-profile mode
    /// immediate (a pure const declare), one await site with the full
    /// machinery tail, and the THROW dispatch on the mode temp.
    fn async_body() -> Vec<SNode> {
        vec![
            run(vec![
                decl(
                    "g",
                    10,
                    Expr::Fallback {
                        op: "AsyncFunctionEnter",
                        note: "entry protocol",
                        operands: vec![],
                    },
                ),
                decl("cn", 11, num(1.0)),
                decl(
                    "a",
                    12,
                    Expr::Await {
                        value: bx(ident("p")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 12)),
                }),
                decl(
                    "r",
                    13,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 10)),
                    },
                ),
                decl(
                    "m",
                    14,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 10)),
                    },
                ),
            ]),
            if_node(
                cmp(CmpOp::Eq, tm("m", 14), tm("cn", 11)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
                vec![run(vec![expr_stmt(ident("cont"))])],
            ),
        ]
    }

    #[test]
    fn async_machine_fold_positive_with_const_env() {
        let mut nodes = async_body();
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 1);
        // The machinery, the entry temp, AND the consumed mode const
        // are all swept; the folded await + the continuation remain.
        assert_eq!(
            nodes,
            vec![
                run(vec![expr_stmt(Expr::Await {
                    value: bx(ident("p")),
                    uncaught: true,
                })]),
                run(vec![expr_stmt(ident("cont"))]),
            ],
            "{nodes:?}"
        );
        // A used resume temp binds at the await site (`const r = await p`).
        let mut nodes = async_body();
        let SNode::If { otherwise, .. } = &mut nodes[1] else {
            unreachable!()
        };
        otherwise[0] = run(vec![expr_stmt(tm("r", 13))]);
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 1);
        assert_eq!(stats.async_machine_bound, 1);
        assert!(matches!(
            &nodes[0],
            SNode::Stmts(run)
                if matches!(&run[0], Leaf::Raw(Stmt::Declare { name, value: Expr::Await { .. }, .. }) if name == "r")
        ));
        // The inlined form: the suspend carries the await directly.
        let mut nodes = async_body();
        let SNode::Stmts(site) = &mut nodes[0] else {
            unreachable!()
        };
        site.remove(2); // the await decl
        site[2] = expr_stmt(Expr::Yield {
            value: bx(Expr::Await {
                value: bx(ident("p")),
                uncaught: true,
            }),
        });
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 1);
        // The inlined mode test: no mode decl, GetResumeMode inline in
        // the condition; the throw arm throws an inlined ResumeGenerator.
        let mut nodes = async_body();
        let SNode::Stmts(site) = &mut nodes[0] else {
            unreachable!()
        };
        site.pop(); // the mode decl
        site.remove(4); // and the resume decl (the throw is inlined too)
        let SNode::If { cond, then, .. } = &mut nodes[1] else {
            unreachable!()
        };
        *cond = cmp(
            CmpOp::Eq,
            Expr::GeneratorDriver {
                resume: false,
                genobj: bx(tm("g", 10)),
            },
            tm("cn", 11),
        );
        then[0] = run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
            resume: true,
            genobj: bx(tm("g", 10)),
        }))]);
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 1);
        // Kind gate + entry gate.
        let mut nodes = async_body();
        let before = nodes.clone();
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Function, &mut stats);
        assert_eq!(nodes, before);
        let mut nodes = async_body();
        let SNode::Stmts(site) = &mut nodes[0] else {
            unreachable!()
        };
        site.remove(0); // no AsyncFunctionEnter temp
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 0);
        // Two entry temps are not the vendor shape.
        let mut nodes = async_body();
        let SNode::Stmts(site) = &mut nodes[0] else {
            unreachable!()
        };
        site.insert(
            1,
            decl(
                "g2",
                19,
                Expr::Fallback {
                    op: "AsyncFunctionEnter",
                    note: "entry protocol",
                    operands: vec![],
                },
            ),
        );
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 0);
        // A funcObj use outside the machinery keeps everything loud.
        let mut nodes = async_body();
        nodes.push(run(vec![expr_stmt(call1(ident("f"), tm("g", 10)))]));
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 0);
    }

    #[test]
    fn async_machine_await_site_and_dispatch_bails() {
        let mk_cx = |nodes: &Vec<SNode>| {
            let mut uses = BTreeMap::new();
            count_temp_uses(nodes, &mut uses);
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
            AsyncMachineCx {
                genobj: ValueId::new(10),
                aliases: [ValueId::new(10)].into_iter().collect(),
                exit_throws: BTreeSet::new(),
                const_env,
                consumed_consts: BTreeSet::new(),
                uses,
            }
        };
        let body = async_body();
        let mut cx = mk_cx(&body);
        assert!(match_await_site(&body, 0, &mut cx).is_some());
        // The site must be a statement run.
        assert!(match_await_site(&[SNode::Honest("h".to_string())], 0, &mut cx).is_none());
        // … with a suspend before the pair…
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site.remove(3);
        let mut cx = mk_cx(&bad);
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // … whose declared await temp is used only by the suspend.
        let mut bad = body.clone();
        bad.push(run(vec![expr_stmt(tm("a", 12))]));
        let mut cx = mk_cx(&bad);
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // … and the await declare must precede it.
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site[2] = decl("a", 12, ident("p"));
        let mut cx = mk_cx(&bad);
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // The dispatch must follow (past phi-partition runs).
        let mut bad = body.clone();
        bad[1] = run(vec![expr_stmt(ident("not_a_dispatch"))]);
        let mut cx = mk_cx(&bad);
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // A phi-partition run between the site and the dispatch is
        // skipped by the offset walk.
        let mut good = body.clone();
        good.insert(1, run(vec![phi_assign("pb", tm("a", 12))]));
        // (the phi-assign use of `a` breaks the single-use rule, so
        // drop the check by using an unrelated value)
        let SNode::Stmts(part) = &mut good[1] else {
            unreachable!()
        };
        part[0] = phi_assign("pb", ident("z"));
        let mut cx = mk_cx(&good);
        let site = match_await_site(&good, 0, &mut cx).expect("dispatch past a phi partition");
        assert_eq!(site.dispatch_off, 2);

        // match_async_dispatch, directly.
        let mut cx = mk_cx(&body);
        let dispatch = if_node(
            cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
            vec![run(vec![expr_stmt(ident("cont"))])],
        );
        assert!(
            match_async_dispatch(
                &dispatch,
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx
            )
            .is_some()
        );
        // The negative-polarity form puts the throw in the else arm.
        let dispatch_neg = if_node(
            isfalse(cmp(CmpOp::Eq, tm("m", 14), num(1.0))),
            vec![run(vec![expr_stmt(ident("cont"))])],
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
        );
        assert!(
            match_async_dispatch(
                &dispatch_neg,
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx
            )
            .is_some()
        );
        // Not an if / not a compare / not the mode operand / not THROW.
        assert!(
            match_async_dispatch(
                &SNode::Honest("h".to_string()),
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_none()
        );
        assert!(
            match_async_dispatch(
                &if_node(ident("c"), vec![], vec![]),
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_none()
        );
        assert!(
            match_async_dispatch(
                &if_node(cmp(CmpOp::Eq, tm("x", 99), num(1.0)), vec![], vec![]),
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_none()
        );
        assert!(
            match_async_dispatch(
                &if_node(
                    cmp(CmpOp::Eq, tm("m", 14), num(0.0)),
                    vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
                    vec![],
                ),
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_none()
        );
        // A THROW arm matching neither check refuses the site.
        assert!(
            match_async_dispatch(
                &if_node(
                    cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
                    vec![run(vec![expr_stmt(ident("x"))])],
                    vec![],
                ),
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_none()
        );
    }

    #[test]
    fn async_machine_throw_and_break_arms() {
        let genobj: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        // check_async_throw_arm shapes.
        assert!(
            check_async_throw_arm(
                &[run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
                Some(ValueId::new(13)),
                &genobj,
            )
            .is_some()
        );
        // … with the dead marker, phi partitions, and dead breaks.
        assert!(
            check_async_throw_arm(
                &[
                    run(vec![phi_assign("p", ident("z"))]),
                    run(vec![
                        Leaf::Raw(Stmt::Throw(tm("r", 13))),
                        Leaf::Raw(Stmt::Unreachable),
                    ]),
                    SNode::Break { label: None },
                ],
                Some(ValueId::new(13)),
                &genobj,
            )
            .is_some()
        );
        // … or the inlined ResumeGenerator when nothing was declared.
        assert!(
            check_async_throw_arm(
                &[run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 10)),
                }))])],
                None,
                &genobj,
            )
            .is_some()
        );
        // Two significant runs / a wrong temp / no throw at all bail.
        assert!(
            check_async_throw_arm(
                &[
                    run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))]),
                    run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))]),
                ],
                Some(ValueId::new(13)),
                &genobj,
            )
            .is_none()
        );
        assert!(
            check_async_throw_arm(
                &[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 99)))])],
                Some(ValueId::new(13)),
                &genobj,
            )
            .is_none()
        );
        assert!(check_async_throw_arm(&[], Some(ValueId::new(13)), &genobj).is_none());
        assert!(
            check_async_throw_arm(
                &[if_node(ident("c"), vec![], vec![])],
                Some(ValueId::new(13)),
                &genobj,
            )
            .is_none()
        );
        // check_async_break_arm: the loop-exit routing needs the
        // pre-verified continuation throw.
        let cx = AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: genobj.clone(),
            exit_throws: [ValueId::new(13)].into_iter().collect(),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
            uses: BTreeMap::new(),
        };
        assert!(
            check_async_break_arm(
                &[
                    run(vec![phi_assign("p", ident("z"))]),
                    SNode::Break { label: None }
                ],
                Some(ValueId::new(13)),
                &cx,
            )
            .is_some()
        );
        assert!(check_async_break_arm(&[], Some(ValueId::new(13)), &cx).is_none());
        assert!(
            check_async_break_arm(
                &[SNode::Break {
                    label: Some("l".to_string()),
                }],
                Some(ValueId::new(13)),
                &cx,
            )
            .is_none()
        );
        assert!(
            check_async_break_arm(
                &[run(vec![expr_stmt(ident("x"))])],
                Some(ValueId::new(13)),
                &cx,
            )
            .is_none()
        );
        let cx_missing = AsyncMachineCx {
            exit_throws: BTreeSet::new(),
            ..cx
        };
        assert!(
            check_async_break_arm(
                &[SNode::Break { label: None }],
                Some(ValueId::new(13)),
                &cx_missing,
            )
            .is_none()
        );
        assert!(
            check_async_break_arm(&[SNode::Break { label: None }], None, &cx_missing).is_none()
        );
    }

    #[test]
    fn async_machine_alias_and_sweep_machinery() {
        // funcobj_aliases: the phi-alias closure of the funcObj.
        let nodes = vec![run(vec![
            phi_decl("p1", 20),
            phi_decl("p2", 21),
            phi_decl("p3", 22),
            phi_decl("dead", 23),
            phi_assign("p1", tm("g", 10)),  // real source
            phi_assign("p2", tm("p1", 20)), // chained alias
            phi_assign("p2", tm("p2", 21)), // self-assign: neutral
            phi_assign("p3", ident("x")),   // foreign source: not an alias
        ])];
        let aliases = funcobj_aliases(&nodes, ValueId::new(10));
        assert!(aliases.contains(&ValueId::new(20)));
        assert!(aliases.contains(&ValueId::new(21)));
        assert!(!aliases.contains(&ValueId::new(22)));
        assert!(!aliases.contains(&ValueId::new(23)));
        // funcobj_uses_are_machinery: genobj-slot operands and phi
        // routing are machinery; anything richer is not.
        let ok = vec![
            run(vec![decl(
                "r",
                30,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 10)),
                },
            )]),
            run(vec![phi_assign("p1", tm("g", 10))]),
        ];
        assert!(funcobj_uses_are_machinery(&ok, &aliases));
        let bad = vec![run(vec![expr_stmt(call1(ident("f"), tm("g", 10)))])];
        assert!(!funcobj_uses_are_machinery(&bad, &aliases));
        let bad = vec![run(vec![phi_assign("p1", call1(ident("f"), tm("g", 10)))])];
        assert!(!funcobj_uses_are_machinery(&bad, &aliases));
        let bad = vec![run(vec![decl(
            "r",
            30,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(call1(ident("f"), tm("g", 10))),
            },
        )])];
        assert!(!funcobj_uses_are_machinery(&bad, &aliases));
        // sweep_async_machinery: the dead bookkeeping web goes away.
        let mut nodes = vec![run(vec![
            phi_decl("pa", 20),
            phi_assign("pa", tm("g", 10)),
            decl("c0", 24, num(1.0)),
        ])];
        let consumed: BTreeSet<ValueId> = [ValueId::new(24)].into_iter().collect();
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &consumed);
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(got.is_empty(), "the whole web stripped: {got:?}");
        // A live alias (a phi read elsewhere) keeps the web.
        let mut nodes = vec![run(vec![
            phi_decl("pa", 20),
            phi_assign("pa", tm("g", 10)),
            expr_stmt(tm("pa", 20)),
        ])];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10), ValueId::new(20)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(got.len(), 3, "live alias keeps everything: {got:?}");
        // A chain feeding a live alias stays alive transitively.
        let mut nodes = vec![run(vec![
            phi_decl("pa", 20),
            phi_decl("pb", 21),
            phi_assign("pa", tm("g", 10)),
            phi_assign("pb", tm("pa", 20)),
            expr_stmt(tm("pb", 21)),
        ])];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10), ValueId::new(20), ValueId::new(21)]
            .into_iter()
            .collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(got.len(), 5, "transitively alive: {got:?}");
        // An alias-valued assign into a dead non-alias phi loses just
        // the assign.
        let mut nodes = vec![
            run(vec![phi_decl("pa", 20), phi_assign("pa", tm("g", 10))]),
            run(vec![phi_decl("pb", 21), phi_assign("pb", tm("g", 10))]),
        ];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(got.is_empty(), "dead alias phi stripped: {got:?}");
        // The non-alias phi run kept its assign-less decl… wait: `pb`
        // has no PhiDecl — only the assign, which is stripped.
        let SNode::Stmts(got) = &nodes[1] else {
            unreachable!()
        };
        assert!(got.is_empty(), "{got:?}");
        // A richer phi-assign value reading an alias is a real use.
        let mut nodes = vec![run(vec![phi_assign("pa", call1(ident("f"), tm("g", 10)))])];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(got.len(), 1, "a real use keeps the assign");
    }

    #[test]
    fn loop_exit_throw_collection() {
        // The continuation-throw collector descends past phi partitions
        // and try wrappers, and recurses into every region kind.
        let t = || tm("rt", 40);
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            SNode::Honest("h".to_string()),
            run(vec![phi_assign("p", ident("z"))]),
            run(vec![Leaf::Raw(Stmt::Throw(t()))]),
        ];
        let out = collect_loop_exit_throws(&nodes);
        assert!(out.contains(&ValueId::new(40)), "{out:?}");
        // A loop inside a region whose OWN continuation has nothing:
        // the search ascends the stack.
        let nodes = vec![
            SNode::Try {
                body: vec![
                    SNode::If {
                        cond: ident("c"),
                        then: vec![SNode::While {
                            label: None,
                            cond: None,
                            body: vec![],
                        }],
                        otherwise: vec![],
                    },
                    SNode::DoWhile {
                        label: None,
                        body: vec![],
                        cond: ident("d"),
                    },
                    SNode::Labeled {
                        label: "l".to_string(),
                        body: vec![SNode::While {
                            label: None,
                            cond: None,
                            body: vec![],
                        }],
                    },
                ],
                catches: vec![catch(
                    "e",
                    vec![SNode::While {
                        label: None,
                        cond: None,
                        body: vec![],
                    }],
                )],
                note: None,
                finally: Some(vec![SNode::While {
                    label: None,
                    cond: None,
                    body: vec![],
                }]),
            },
            run(vec![Leaf::Raw(Stmt::Throw(t()))]),
        ];
        let out = collect_loop_exit_throws(&nodes);
        // The nested loops' continuation (the try's catch-less tail)
        // is not a throw; only the sibling-after-try reading differs.
        let _ = out;
        // first_significant_stmt shapes, via the collector's result:
        // a loop followed by a non-throw significant statement yields
        // nothing.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            run(vec![expr_stmt(ident("x"))]),
        ];
        assert!(collect_loop_exit_throws(&nodes).is_empty());
        // A synthetic leaf is not a throw.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            run(vec![Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: None,
            }]),
        ];
        assert!(collect_loop_exit_throws(&nodes).is_empty());
        // An if/switch after the loop: no unique first statement.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            if_node(ident("c"), vec![], vec![]),
        ];
        assert!(collect_loop_exit_throws(&nodes).is_empty());
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            SNode::Switch {
                disc: ident("d"),
                cases: vec![],
            },
        ];
        assert!(collect_loop_exit_throws(&nodes).is_empty());
        // An empty try wrapper falls through to the next sibling.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            try_node(vec![], vec![]),
            run(vec![Leaf::Raw(Stmt::Throw(t()))]),
        ];
        let out = collect_loop_exit_throws(&nodes);
        assert!(out.contains(&ValueId::new(40)));
        // A try whose body's first significant statement is a throw.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![],
            },
            try_node(vec![run(vec![Leaf::Raw(Stmt::Throw(t()))])], vec![]),
        ];
        let out = collect_loop_exit_throws(&nodes);
        assert!(out.contains(&ValueId::new(40)));
    }

    // ── d-P14: the async-generator machine fold ────────────────────

    /// An async-generator body: the entry protocol with
    /// optimized-profile const decls and BOTH dead entry results
    /// (resume + mode), then one full yield site (the pre-yield await,
    /// the THROW dispatch, the yield-point resumption pair, the
    /// three-way mode dispatch with a phi-partition run before the
    /// THROW test), and a completion resolve.
    fn agen_body() -> Vec<SNode> {
        let driver = |r: &str, rv: u32, m: &str, mv: u32| {
            [
                decl(
                    r,
                    rv,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 20)),
                    },
                ),
                decl(
                    m,
                    mv,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 20)),
                    },
                ),
            ]
        };
        let [r1, m1] = driver("r1", 31, "m1", 32);
        let [ry, my] = driver("ry", 33, "my", 34);
        vec![
            run(vec![
                decl(
                    "g",
                    20,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                decl("c0", 21, num(0.0)),
                decl("c1", 22, num(1.0)),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
                expr_stmt(Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                }),
                expr_stmt(Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                }),
            ]),
            // The pre-yield await machinery (d-P13's site shape).
            run(vec![
                decl(
                    "a",
                    30,
                    Expr::Await {
                        value: bx(ident("v")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 30)),
                }),
                r1,
                m1,
            ]),
            // Its THROW-only dispatch; the continuation carries the
            // yield-point resumption pair + the three-way dispatch.
            if_node(
                cmp(CmpOp::Eq, tm("m1", 32), num(1.0)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r1", 31)))])],
                vec![
                    run(vec![phi_assign("pp", ident("z"))]),
                    run(vec![ry, my]),
                    if_node(
                        cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
                        vec![
                            run(vec![decl(
                                "a2",
                                35,
                                Expr::Await {
                                    value: bx(tm("ry", 33)),
                                    uncaught: true,
                                },
                            )]),
                            run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]),
                        ],
                        vec![
                            run(vec![phi_assign("pp2", ident("z"))]),
                            if_node(
                                cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                                vec![run(vec![expr_stmt(ident("next_cont"))])],
                            ),
                        ],
                    ),
                ],
            ),
            // The completion resolve: `return { value: g, done: X }`.
            run(vec![Leaf::Raw(Stmt::Return(Some(Expr::IterResultObj {
                value: bx(tm("g", 20)),
                done: bx(ident("undefinedv")),
            })))]),
        ]
    }

    #[test]
    fn async_generator_fold_entry_yield_and_completion() {
        let mut nodes = agen_body();
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 1);
        assert_eq!(stats.agen_yields, 1);
        assert_eq!(stats.agen_returns, 1);
        // The yield point folded to a bare `yield v`; the completion
        // resolve to `return undefinedv`.
        let yield_stmt = nodes.iter().any(|n| {
            matches!(
                n,
                SNode::Stmts(run) if run.iter().any(|l| matches!(
                    l,
                    Leaf::Raw(Stmt::Expr(Expr::Yield { value }))
                        if value.as_ref() == &ident("v")
                ))
            )
        });
        assert!(yield_stmt, "{nodes:?}");
        let ret = nodes.iter().any(|n| {
            matches!(
                n,
                SNode::Stmts(run) if run.iter().any(|l| matches!(
                    l,
                    Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("undefinedv")
                ))
            )
        });
        assert!(ret, "{nodes:?}");
        // The genobj temp is swept.
        assert!(!nodes_use_temp(&nodes, ValueId::new(20)));
        // The kind gate: only async generators.
        let mut nodes = agen_body();
        let before = nodes.clone();
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(nodes, before);
        // Two genobj temps are not the vendor shape.
        let mut nodes = agen_body();
        let SNode::Stmts(entry) = &mut nodes[0] else {
            unreachable!()
        };
        entry.push(decl(
            "g2",
            90,
            Expr::CreateGenerator {
                func: bx(closure("h")),
            },
        ));
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 0);
        // A non-machinery genobj use keeps everything loud.
        let mut nodes = agen_body();
        nodes.push(run(vec![expr_stmt(call1(ident("f"), tm("g", 20)))]));
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 0);
    }

    #[test]
    fn agen_entry_elision_variants_and_bails() {
        // The entry site elides inside if/loop/catch regions too.
        for wrap in [
            |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::While {
                    label: None,
                    cond: Some(ident("c")),
                    body: site,
                }]
            },
            |site: Vec<SNode>| {
                vec![SNode::Labeled {
                    label: "l".to_string(),
                    body: site,
                }]
            },
            |site: Vec<SNode>| vec![try_node(site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::Try {
                    body: vec![run(vec![expr_stmt(ident("x"))])],
                    catches: vec![catch("e", site)],
                    note: None,
                    finally: None,
                }]
            },
        ] {
            let mut nodes = wrap(vec![run(vec![
                decl(
                    "g",
                    20,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
            ])]);
            let mut stats = FoldStats::default();
            async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
            assert_eq!(stats.agen_entry, 1, "nested entry elision");
        }
        // The entry suspend must follow the decl (past const decls).
        let mut nodes = vec![run(vec![
            decl(
                "g",
                20,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            expr_stmt(ident("not_a_suspend")),
        ])];
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 0);
        // No CreateGenerator decl at all.
        let mut nodes = vec![run(vec![expr_stmt(ident("x"))])];
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 0);
        // agen_uses_are_machinery directly: slot positions only.
        assert!(agen_uses_are_machinery(&agen_body(), ValueId::new(20)));
        let bad = vec![run(vec![expr_stmt(call1(ident("f"), tm("g", 20)))])];
        assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
        // … the IterResultObj done slot is not a legal position…
        let bad = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
            Expr::IterResultObj {
                value: bx(ident("x")),
                done: bx(tm("g", 20)),
            },
        )))])];
        assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
        // … and a rich phi-assign value reading the genobj is not
        // machinery (a plain `phi = g` self-route is).
        let ok = vec![run(vec![phi_assign("p", tm("g", 20))])];
        assert!(agen_uses_are_machinery(&ok, ValueId::new(20)));
        let bad = vec![run(vec![phi_assign("p", call1(ident("f"), tm("g", 20)))])];
        assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
    }

    /// A fold context for the d-P14 matchers (genobj 20).
    fn agen_cx(nodes: &[SNode]) -> AsyncMachineCx {
        let mut uses = BTreeMap::new();
        count_temp_uses(nodes, &mut uses);
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
        AsyncMachineCx {
            genobj: ValueId::new(20),
            aliases: [ValueId::new(20)].into_iter().collect(),
            exit_throws: BTreeSet::new(),
            const_env,
            consumed_consts: BTreeSet::new(),
            uses,
        }
    }

    #[test]
    fn agen_fold_run_explicit_return_and_bails() {
        // The explicit-return site: `[decl a = await v, suspend(a),
        // decl r = ResumeGenerator(g), return r]` → `return v`.
        let site_run = || {
            vec![
                decl(
                    "a",
                    40,
                    Expr::Await {
                        value: bx(ident("v")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 40)),
                }),
                decl(
                    "r",
                    41,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 20)),
                    },
                ),
                Leaf::Raw(Stmt::Return(Some(tm("r", 41)))),
            ]
        };
        let mut leaves = site_run();
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 1);
        assert_eq!(
            leaves,
            vec![Leaf::Raw(Stmt::Return(Some(ident("v"))))],
            "{leaves:?}"
        );
        // Phi assigns interleave freely.
        let mut leaves = site_run();
        leaves.insert(2, phi_assign("p", ident("z")));
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 1);
        // Bails: no return-of-temp …
        let mut leaves = vec![expr_stmt(ident("x"))];
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // … the resume decl must precede the return…
        let mut leaves = site_run();
        leaves.remove(2);
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // … on the same genobj…
        let mut leaves = site_run();
        leaves[2] = decl(
            "r",
            41,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("other", 99)),
            },
        );
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // … and return ITS temp.
        let mut leaves = site_run();
        leaves[3] = Leaf::Raw(Stmt::Return(Some(tm("other", 99))));
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // The suspend must be a yield of the await temp…
        let mut leaves = site_run();
        leaves[1] = expr_stmt(ident("x"));
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        let mut leaves = site_run();
        leaves[1] = expr_stmt(Expr::Yield {
            value: bx(ident("not_a_temp")),
        });
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // … and the await declare must be THAT temp's.
        let mut leaves = site_run();
        leaves.remove(0);
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        let mut leaves = site_run();
        leaves[0] = decl(
            "a",
            99,
            Expr::Await {
                value: bx(ident("v")),
                uncaught: true,
            },
        );
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // A caught (non-uncaught) await is not this shape.
        let mut leaves = site_run();
        leaves[0] = decl(
            "a",
            40,
            Expr::Await {
                value: bx(ident("v")),
                uncaught: false,
            },
        );
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
    }

    #[test]
    fn agen_yield_site_and_three_way_bails() {
        let body = agen_body();
        let mut cx = agen_cx(&body);
        assert!(match_ag_yield(&body, 1, &mut cx).is_some());
        // The pre-yield resume value's only use may be the throw arm.
        let mut bad = body.clone();
        let SNode::Stmts(site) = &mut bad[1] else {
            unreachable!()
        };
        site.push(expr_stmt(tm("r1", 31)));
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
        // The continuation must open with the resumption pair run.
        let mut bad = body.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        otherwise[0] = SNode::Honest("h".to_string());
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
        let mut bad = body.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        otherwise[1] = run(vec![phi_assign("pp", ident("z"))]);
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
        // The yield-point resume decl must read the genobj…
        let mut bad = body.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        let SNode::Stmts(pair) = &mut otherwise[1] else {
            unreachable!()
        };
        pair[0] = decl(
            "ry",
            33,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("other", 99)),
            },
        );
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
        // … and a non-pair trailing leaf bails.
        let mut bad = body.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        let SNode::Stmts(pair) = &mut otherwise[1] else {
            unreachable!()
        };
        pair.push(expr_stmt(ident("extra")));
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
        // The three-way dispatch ends the continuation.
        let mut bad = body.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        otherwise.push(run(vec![expr_stmt(ident("extra"))]));
        let mut cx = agen_cx(&bad);
        assert!(match_ag_yield(&bad, 1, &mut cx).is_none());

        // match_ag_three_way directly.
        let three_way = |ret: SNode, throw: SNode, next: SNode| {
            if_node(
                cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
                vec![ret],
                vec![if_node(
                    cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                    vec![throw],
                    vec![next],
                )],
            )
        };
        let ret_arm = || {
            run(vec![decl(
                "a2",
                35,
                Expr::Await {
                    value: bx(tm("ry", 33)),
                    uncaught: true,
                },
            )])
        };
        let ret_done = || run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]);
        let throw_arm = || run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))]);
        let next = || run(vec![expr_stmt(ident("next_cont"))]);
        // The RETURN arm carries the folded await+return pair.
        let good = if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
            vec![ret_arm(), ret_done()],
            vec![if_node(
                cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                vec![throw_arm()],
                vec![next()],
            )],
        );
        let mut cx = agen_cx(&body);
        assert!(
            match_ag_three_way(&good, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_some()
        );
        // Must be an if; the tests must be mode tests; RETURN before
        // THROW, each once.
        assert!(
            match_ag_three_way(
                &SNode::Honest("h".to_string()),
                Some(ValueId::new(34)),
                ValueId::new(33),
                &mut cx,
            )
            .is_none()
        );
        let bad = three_way(if_node(ident("c"), vec![], vec![]), throw_arm(), next());
        assert!(
            match_ag_three_way(&bad, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_none()
        );
        // A NEXT(2) test is not part of the dispatch chain.
        let bad = if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(2.0)),
            vec![ret_arm()],
            vec![next()],
        );
        assert!(
            match_ag_three_way(&bad, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_none()
        );
        // check_ag_return_arm shapes: phi partitions and dead breaks
        // ride along; a wrong await or return temp bails.
        let mut cx = agen_cx(&body);
        assert!(
            check_ag_return_arm(
                &[
                    run(vec![phi_assign("p", ident("z"))]),
                    ret_arm(),
                    SNode::Break { label: None },
                    ret_done(),
                ],
                ValueId::new(33),
            )
            .is_some()
        );
        assert!(check_ag_return_arm(&[ret_arm()], ValueId::new(33)).is_none());
        assert!(
            check_ag_return_arm(
                &[
                    run(vec![decl(
                        "a2",
                        35,
                        Expr::Await {
                            value: bx(tm("other", 99)),
                            uncaught: true,
                        },
                    )]),
                    ret_done()
                ],
                ValueId::new(33),
            )
            .is_none()
        );
        assert!(
            check_ag_return_arm(
                &[
                    ret_arm(),
                    run(vec![Leaf::Raw(Stmt::Return(Some(tm("x", 99))))])
                ],
                ValueId::new(33),
            )
            .is_none()
        );
        assert!(
            check_ag_return_arm(&[SNode::Continue { label: None }], ValueId::new(33)).is_none()
        );
        let _ = &mut cx;
        // ag_mode_test: wrappers, operand order, the inlined form.
        let (bits, pos) = ag_mode_test(
            &cmp(CmpOp::Eq, tm("my", 34), num(2.0)),
            Some(ValueId::new(34)),
            &mut agen_cx(&body),
        )
        .unwrap();
        assert_eq!(f64::from_bits(bits), 2.0);
        assert!(pos);
        let (.., pos) = ag_mode_test(
            &isfalse(cmp(CmpOp::Eq, num(1.0), tm("my", 34))),
            Some(ValueId::new(34)),
            &mut agen_cx(&body),
        )
        .unwrap();
        assert!(!pos);
        let (bits, ..) = ag_mode_test(
            &cmp(
                CmpOp::Eq,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                },
                num(1.0),
            ),
            None,
            &mut agen_cx(&body),
        )
        .expect("inlined GetResumeMode");
        assert_eq!(f64::from_bits(bits), 1.0);
        assert!(ag_mode_test(&ident("c"), Some(ValueId::new(34)), &mut agen_cx(&body)).is_none());
        assert!(
            ag_mode_test(
                &cmp(CmpOp::Eq, tm("other", 99), num(1.0)),
                Some(ValueId::new(34)),
                &mut agen_cx(&body),
            )
            .is_none()
        );
        // The yield-point guard: a source-level await whose
        // continuation opens with the resumption pair on the same
        // genobj is yield machinery, not an await site.
        let guard_body = vec![
            run(vec![
                decl(
                    "a",
                    30,
                    Expr::Await {
                        value: bx(ident("v")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 30)),
                }),
            ]),
            if_node(
                cmp(
                    CmpOp::Eq,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 20)),
                    },
                    num(1.0),
                ),
                vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                }))])],
                vec![run(vec![decl(
                    "ry",
                    33,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("g", 20)),
                    },
                )])],
            ),
        ];
        let mut cx = agen_cx(&guard_body);
        assert!(match_await_site(&guard_body, 0, &mut cx).is_some());
        assert!(match_ag_await(&guard_body, 0, &mut cx).is_none());
    }

    // ── d-P15: the YieldStar driver fold ───────────────────────────
    //
    // The full vendor shapes, probe-verified against the matchers:
    // header phis {rt, rv, it, g, flag} + the exitReturn decl, the
    // NEXT/THROW mode dispatch, the RETURN arm (method lookup +
    // undefined test + exit-phi wiring), the THROW arm (method lookup
    // + close machinery with the elided ThrowNotExists), then the
    // per-kind tail.

    /// The shared ys header run.
    fn ys_header() -> SNode {
        run(vec![
            phi_decl("vrt", 100),
            phi_decl("vrv", 101),
            phi_decl("vit", 102),
            phi_decl("vg", 103),
            phi_decl("vflag", 104),
            decl("vexit0", 105, boolean(false)),
        ])
    }

    /// The shared mode dispatch: `if (rt !== NEXT) { if (rt !== THROW)
    /// { RETURN arm } else { THROW arm } } else { assigns → call }`.
    fn ys_dispatch(ret_arm: Vec<SNode>, throw_arm: Vec<SNode>) -> SNode {
        if_node(
            isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(2.0))),
            vec![if_node(
                isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(1.0))),
                ret_arm,
                throw_arm,
            )],
            vec![run(vec![phi_assign("vm0", tm("vnext", 201))])],
        )
    }

    /// The shared RETURN arm (`async_` skips the propagation return).
    fn ys_ret_arm(async_: bool) -> Vec<SNode> {
        let mut out = vec![run(vec![
            decl("vt", 120, boolean(true)),
            decl("vret", 121, prop(tm("vit", 102), "return")),
        ])];
        if !async_ {
            out.push(run(vec![Leaf::Raw(Stmt::Return(Some(tm("vrv", 101))))]));
        }
        out.push(if_node(
            isfalse(cmp(CmpOp::Eq, tm("vret", 121), undef())),
            vec![run(vec![
                phi_assign("vexit", tm("vt", 120)),
                phi_assign("vm1", tm("vnext", 201)),
            ])],
            vec![SNode::Break { label: None }],
        ));
        out
    }

    /// The shared THROW arm.
    fn ys_throw_arm() -> Vec<SNode> {
        vec![
            run(vec![
                decl("vthrow", 130, prop(tm("vit", 102), "throw")),
                decl("veq", 131, cmp(CmpOp::Eq, tm("vthrow", 130), undef())),
            ]),
            if_node(
                isfalse(tm("veq", 131)),
                vec![run(vec![phi_assign("vexit", tm("vexit0", 105))])],
                vec![],
            ),
            if_node(
                istrue(tm("vflag", 104)),
                vec![run(vec![elided("ThrowNotExists")])],
                vec![run(vec![])],
            ),
        ]
    }

    /// The sync tail: precall, done test, pass-through suspend,
    /// loop-back assigns, continue.
    fn ys_sync_tail() -> Vec<SNode> {
        vec![
            run(vec![
                phi_decl("vexit", 110),
                phi_decl("vm", 111),
                decl(
                    "vres",
                    112,
                    Expr::Call {
                        callee: bx(tm("vm", 111)),
                        this: Some(bx(tm("vit", 102))),
                        args: vec![tm("vrv", 101)],
                        kind: CallKind::Dynamic,
                    },
                ),
                decl("vdone", 113, prop(tm("vres", 112), "done")),
            ]),
            if_node(
                istrue(tm("vdone", 113)),
                vec![SNode::Break { label: None }],
                vec![],
            ),
            run(vec![
                expr_stmt(Expr::Yield {
                    value: bx(tm("vres", 112)),
                }),
                decl(
                    "vresume",
                    140,
                    Expr::GeneratorDriver {
                        resume: true,
                        genobj: bx(tm("vg", 103)),
                    },
                ),
            ]),
            run(vec![
                phi_assign(
                    "vrt",
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("vg", 103)),
                    },
                ),
                phi_assign("vrv", tm("vresume", 140)),
            ]),
            SNode::Continue { label: None },
        ]
    }

    /// The setup + init runs (`yield* <obj>` plumbing).
    fn ys_setup_init(async_: bool) -> [SNode; 2] {
        let op = if async_ {
            IterOp::GetAsyncIterator
        } else {
            IterOp::GetIterator
        };
        [
            run(vec![
                decl(
                    "vit0",
                    200,
                    Expr::Iter {
                        op,
                        obj: bx(ident("src")),
                        status: NodeStatus::Plumbing,
                    },
                ),
                decl("vnext", 201, prop(tm("vit0", 200), "next")),
            ]),
            run(vec![
                phi_assign("vrt", num(2.0)),
                phi_assign("vrv", undef()),
                phi_assign("vflag", boolean(false)),
                phi_assign("vit", tm("vit0", 200)),
                phi_assign("vg", tm("vg0", 202)),
                phi_assign("vm", tm("vnext", 201)),
            ]),
        ]
    }

    /// The full sync site: [setup, init, While, exit dispatch].
    fn ys_sync_shape() -> Vec<SNode> {
        let [setup, init] = ys_setup_init(false);
        vec![
            setup,
            init,
            SNode::While {
                label: None,
                cond: None,
                body: {
                    let mut b = vec![ys_header(), ys_dispatch(ys_ret_arm(false), ys_throw_arm())];
                    b.extend(ys_sync_tail());
                    b
                },
            },
            // The completion dispatch: `if (!exitReturn) { v =
            // res.value; <cont> } else { v2 = res.value; return v2 }`.
            if_node(
                isfalse(tm("vexit", 110)),
                vec![run(vec![
                    decl("vval", 150, prop(tm("vres", 112), "value")),
                    expr_stmt(tm("vval", 150)),
                ])],
                vec![run(vec![
                    decl("vv2", 151, prop(tm("vres", 112), "value")),
                    Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
                ])],
            ),
        ]
    }

    /// The While node of a ys shape (for near-miss mutations).
    fn ys_while(nodes: &mut [SNode]) -> &mut SNode {
        &mut nodes[2]
    }

    #[test]
    fn yield_star_sync_positive() {
        let mut nodes = ys_sync_shape();
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(stats.yield_star_bound, 1);
        assert_eq!(
            nodes,
            vec![
                run(vec![decl(
                    "vval",
                    150,
                    Expr::YieldStar {
                        value: bx(ident("src")),
                    },
                )]),
                run(vec![expr_stmt(tm("vval", 150))]),
            ],
            "{nodes:?}"
        );
        // The kind gate: only Generator/AsyncGenerator.
        let mut nodes = ys_sync_shape();
        let before = nodes.clone();
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(nodes, before);
    }

    #[test]
    fn ys_match_loop_bail_pins() {
        // A helper: mutate the While of the sync shape; the loop match
        // must fail.
        fn bail(mutate: impl FnOnce(&mut SNode)) {
            let mut nodes = ys_sync_shape();
            mutate(ys_while(&mut nodes));
            assert!(
                ys_match_loop(&nodes[2], false).is_none(),
                "near-miss matched"
            );
        }
        // The candidate must be a `while (true)`.
        bail(|w| {
            let SNode::While { cond, .. } = w else {
                unreachable!()
            };
            *cond = Some(ident("c"));
        });
        // The significant-node skeleton: [header, dispatch, precall, …].
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body.truncate(2);
        });
        // The header must be a statement run…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body[0] = SNode::Honest("h".to_string());
        });
        // … non-empty…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body[0] = run(vec![]);
        });
        // … of phi decls…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body[0] = run(vec![
                expr_stmt(ident("x")),
                decl("vexit0", 105, boolean(false)),
            ]);
        });
        // … closed by the `exitReturn = false` declare.
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::Stmts(hdr) = &mut body[0] else {
                unreachable!()
            };
            hdr[5] = decl("vexit0", 105, boolean(true));
        });
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::Stmts(hdr) = &mut body[0] else {
                unreachable!()
            };
            hdr[5] = phi_decl("vexit0", 105);
        });
        // The dispatch must be an if…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body[1] = run(vec![phi_assign("vm0", tm("vnext", 201))]);
        });
        // … testing the mode phi…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut body[1] else {
                unreachable!()
            };
            *cond = istrue(tm("vrt", 100));
        });
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut body[1] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::StrictEq, tm("other", 99), num(2.0)));
        });
        // … whose NEXT arm opens with the call-block assigns.
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut body[1] else {
                unreachable!()
            };
            otherwise[0] = SNode::Honest("h".to_string());
        });
        // The THROW/RETURN split must be a single if…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[1] else {
                unreachable!()
            };
            *then = vec![];
        });
        // … testing the same mode temp for THROW(1).
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut then[0] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(2.0)));
        });
        // The RETURN arm must match…
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[1] else {
                unreachable!()
            };
            let SNode::If { then: ret, .. } = &mut then[0] else {
                unreachable!()
            };
            *ret = vec![];
        });
        // … and so must the THROW arm.
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[1] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut then[0] else {
                unreachable!()
            };
            *otherwise = vec![];
        });
        // … and the tail must match.
        bail(|w| {
            let SNode::While { body, .. } = w else {
                unreachable!()
            };
            body.truncate(6); // drop the trailing continue
        });
    }

    #[test]
    fn ys_match_return_arm_bail_pins() {
        let phis: BTreeMap<String, ValueId> = [
            ("vrt".to_string(), ValueId::new(100)),
            ("vrv".to_string(), ValueId::new(101)),
            ("vit".to_string(), ValueId::new(102)),
        ]
        .into_iter()
        .collect();
        let arm: Vec<SNode> = ys_ret_arm(false);
        let refs: Vec<&SNode> = arm.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_some());
        // The undefined test must be a `method == undefined` test…
        let mut bad = arm.clone();
        let SNode::If { cond, .. } = &mut bad[2] else {
            unreachable!()
        };
        *cond = isfalse(tm("vret", 121));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // … on the looked-up method temp.
        let mut bad = arm.clone();
        let SNode::If { cond, .. } = &mut bad[2] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::Eq, tm("other", 99), undef()));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // The method-exists arm must be exactly one assign run…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[2] else {
            unreachable!()
        };
        *then = vec![];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // … to the call block…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[2] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut then[0] else {
            unreachable!()
        };
        assigns[0] = Leaf::Raw(Stmt::PhiAssign {
            target: "vexit".to_string(),
            value: tm("vt", 120),
            to: BlockId::new(8),
            exceptional: false,
        });
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // … wiring the exitReturn phi to the `true` decl…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[2] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut then[0] else {
            unreachable!()
        };
        assigns[0] = phi_assign("vexit", tm("other", 99));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // … with the not-exists arm being exactly `break`.
        let mut bad = arm.clone();
        let SNode::If { otherwise, .. } = &mut bad[2] else {
            unreachable!()
        };
        *otherwise = vec![];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // The arm contains only runs and the method-test if.
        let mut bad = arm.clone();
        bad.push(SNode::Continue { label: None });
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // No method test at all.
        let bad = [arm[0].clone(), arm[1].clone()];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // The sync propagation return must read a header phi.
        let mut bad = arm.clone();
        bad[1] = run(vec![Leaf::Raw(Stmt::Return(Some(tm("other", 99))))]);
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
        // The async form: no propagation return needed.
        let arm: Vec<SNode> = ys_ret_arm(true);
        let refs: Vec<&SNode> = arm.iter().collect();
        assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), true).is_some());
    }

    #[test]
    fn ys_match_throw_arm_bail_pins() {
        let phis: BTreeMap<String, ValueId> = [("vflag".to_string(), ValueId::new(104))]
            .into_iter()
            .collect();
        let arm: Vec<SNode> = ys_throw_arm();
        let refs: Vec<&SNode> = arm.iter().collect();
        let ok = ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis,
        );
        assert_eq!(ok, Some(ValueId::new(104)));
        // The method lookup must read `it.throw`…
        let mut bad = arm.clone();
        let SNode::Stmts(decls) = &mut bad[0] else {
            unreachable!()
        };
        decls[0] = decl("vthrow", 130, prop(tm("other", 99), "throw"));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // … with the `throwM == undefined` temp tested next.
        let mut bad = arm.clone();
        let SNode::Stmts(decls) = &mut bad[0] else {
            unreachable!()
        };
        decls[1] = decl("veq", 131, cmp(CmpOp::Eq, tm("other", 99), undef()));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // The method-exists if must test `!eqM`…
        let mut bad = arm.clone();
        let SNode::If { cond, .. } = &mut bad[1] else {
            unreachable!()
        };
        *cond = istrue(tm("veq", 131));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // … its then being exactly the call-block assigns…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[1] else {
            unreachable!()
        };
        *then = vec![];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // … to the right block…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[1] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut then[0] else {
            unreachable!()
        };
        assigns[0] = Leaf::Raw(Stmt::PhiAssign {
            target: "vexit".to_string(),
            value: tm("vexit0", 105),
            to: BlockId::new(8),
            exceptional: false,
        });
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // … wiring the exit phi to the exitReturn decl…
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[1] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut then[0] else {
            unreachable!()
        };
        assigns[0] = phi_assign("vexit", tm("other", 99));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // … with an empty else.
        let mut bad = arm.clone();
        let SNode::If { otherwise, .. } = &mut bad[1] else {
            unreachable!()
        };
        *otherwise = vec![SNode::Break { label: None }];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // The close if must contain the elided ThrowNotExists.
        let mut bad = arm.clone();
        let SNode::If { then, .. } = &mut bad[2] else {
            unreachable!()
        };
        *then = vec![run(vec![expr_stmt(ident("x"))])];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // No close if at all.
        let bad = [arm[0].clone(), arm[1].clone()];
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // An if on a non-phi temp is neither dispatch.
        let mut bad = arm.clone();
        let SNode::If { cond, .. } = &mut bad[2] else {
            unreachable!()
        };
        *cond = istrue(tm("other", 99));
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
        // The arm contains only runs and ifs.
        let mut bad = arm.clone();
        bad.push(SNode::Break { label: None });
        let refs: Vec<&SNode> = bad.iter().collect();
        assert!(
            ys_match_throw_arm(
                &refs,
                ValueId::new(102),
                "vexit",
                ValueId::new(105),
                BlockId::new(7),
                &phis
            )
            .is_none()
        );
    }

    #[test]
    fn ys_match_loop_tail_sync_bail_pins() {
        fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_sync_shape();
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            mutate(body);
            assert!(
                ys_match_loop(&nodes[2], false).is_none(),
                "near-miss matched"
            );
        }
        // The precall run opens with the phi decls incl. the exit phi.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.remove(0); // the exitReturn phi decl
        });
        // The call's callee must be a precall phi…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl("vres", 112, call1(tm("other", 99), tm("vrv", 101)));
        });
        // … its `this` must be the iterator phi…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("other", 99))),
                    args: vec![tm("vrv", 101)],
                    kind: CallKind::Dynamic,
                },
            );
        });
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl("vres", 112, call0(tm("vm", 111)));
        });
        // … and its single argument the received-value phi.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("vit", 102))),
                    args: vec![tm("other", 99)],
                    kind: CallKind::Dynamic,
                },
            );
        });
        // `done` must read `.done` off the call result.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[3] = decl("vdone", 113, prop(tm("vres", 112), "finished"));
        });
        // Foreign precall leaves bail.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.push(expr_stmt(ident("extra")));
        });
        // The done test must be a positive flag test of `done`…
        bail(|body| {
            let SNode::If { cond, .. } = &mut body[3] else {
                unreachable!()
            };
            *cond = isfalse(tm("vdone", 113));
        });
        bail(|body| {
            let SNode::If { cond, .. } = &mut body[3] else {
                unreachable!()
            };
            *cond = istrue(tm("other", 99));
        });
        // … whose then arm is exactly `break`…
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            *then = vec![];
        });
        // … with an empty else.
        bail(|body| {
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            *otherwise = vec![run(vec![expr_stmt(ident("x"))])];
        });
        // The suspend run: `[yield res, resume = ResumeGenerator(g)]`.
        bail(|body| {
            let SNode::Stmts(susp) = &mut body[4] else {
                unreachable!()
            };
            susp[0] = expr_stmt(Expr::Yield {
                value: bx(tm("other", 99)),
            });
        });
        bail(|body| {
            let SNode::Stmts(susp) = &mut body[4] else {
                unreachable!()
            };
            susp[1] = decl("vresume", 140, ident("not_a_driver"));
        });
        bail(|body| {
            let SNode::Stmts(susp) = &mut body[4] else {
                unreachable!()
            };
            susp[1] = decl(
                "vresume",
                140,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("other", 99)),
                },
            );
        });
        // The loop-back assigns must carry both the mode and the value.
        bail(|body| {
            let SNode::Stmts(lb) = &mut body[5] else {
                unreachable!()
            };
            lb.remove(0);
        });
        bail(|body| {
            let SNode::Stmts(lb) = &mut body[5] else {
                unreachable!()
            };
            lb[1] = phi_assign("vrv", tm("other", 99));
        });
    }

    /// The async tail: [precall (call + inner await + pass-through
    /// yield + resume), the await's THROW dispatch with the in-loop
    /// completion].
    fn ys_async_tail() -> Vec<SNode> {
        let drv = |resume: bool| Expr::GeneratorDriver {
            resume,
            genobj: bx(tm("vg", 103)),
        };
        vec![
            // precall: phis, `res = vm.call(it, rv)`, `aw = await res`,
            // `yield aw`, `res1 = ResumeGenerator(g)`.
            run(vec![
                phi_decl("vexit", 110),
                phi_decl("vm", 111),
                decl(
                    "vres",
                    112,
                    Expr::Call {
                        callee: bx(tm("vm", 111)),
                        this: Some(bx(tm("vit", 102))),
                        args: vec![tm("vrv", 101)],
                        kind: CallKind::Dynamic,
                    },
                ),
                decl(
                    "aw0",
                    141,
                    Expr::Await {
                        value: bx(tm("vres", 112)),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("aw0", 141)),
                }),
                decl("vres1", 142, drv(true)),
            ]),
            // The await's THROW dispatch.
            if_node(
                isfalse(cmp(CmpOp::Eq, drv(false), num(1.0))),
                // Continuation: done load + the done test with the
                // in-loop completion dispatch.
                vec![
                    run(vec![
                        elided("ThrowIfNotObject"),
                        decl("vdone", 113, prop(tm("vres1", 142), "done")),
                    ]),
                    if_node(
                        istrue(tm("vdone", 113)),
                        vec![
                            if_node(
                                isfalse(tm("vexit", 110)),
                                vec![run(vec![
                                    decl("vval", 150, prop(tm("vres1", 142), "value")),
                                    expr_stmt(tm("vval", 150)),
                                ])],
                                vec![run(vec![
                                    decl("vv2", 151, prop(tm("vres1", 142), "value")),
                                    Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
                                ])],
                            ),
                            SNode::Break { label: None },
                        ],
                        // Not done: the AsyncGeneratorYield + the
                        // resumption re-entry.
                        vec![
                            run(vec![
                                decl("v2", 143, prop(tm("vres1", 142), "value")),
                                decl(
                                    "av2",
                                    144,
                                    Expr::Await {
                                        value: bx(tm("v2", 143)),
                                        uncaught: true,
                                    },
                                ),
                                expr_stmt(Expr::Yield {
                                    value: bx(tm("av2", 144)),
                                }),
                                decl("vres2", 145, drv(true)),
                            ]),
                            if_node(
                                isfalse(cmp(CmpOp::Eq, drv(false), num(1.0))),
                                vec![
                                    run(vec![
                                        decl("r3", 146, drv(true)),
                                        decl("m3", 147, drv(false)),
                                    ]),
                                    // `if (m3 != RETURN) { loop back }`.
                                    if_node(
                                        isfalse(cmp(CmpOp::Eq, tm("m3", 147), num(0.0))),
                                        vec![
                                            run(vec![
                                                phi_assign("vrt", tm("m3", 147)),
                                                phi_assign("vrv", tm("r3", 146)),
                                            ]),
                                            SNode::Continue { label: None },
                                        ],
                                        vec![],
                                    ),
                                    // The RETURN await.
                                    run(vec![
                                        decl(
                                            "aw3",
                                            148,
                                            Expr::Await {
                                                value: bx(tm("r3", 146)),
                                                uncaught: true,
                                            },
                                        ),
                                        expr_stmt(Expr::Yield {
                                            value: bx(tm("aw3", 148)),
                                        }),
                                        decl("r4", 152, drv(true)),
                                        decl("m4", 153, drv(false)),
                                    ]),
                                    // `if (m4 == THROW) { loop back }`.
                                    if_node(
                                        isfalse(cmp(CmpOp::NotEq, tm("m4", 153), num(1.0))),
                                        vec![
                                            run(vec![
                                                phi_assign("vrt", tm("m4", 153)),
                                                phi_assign("vrv", tm("r4", 152)),
                                            ]),
                                            SNode::Continue { label: None },
                                        ],
                                        vec![],
                                    ),
                                    // The final loop-back (RETURN).
                                    run(vec![
                                        phi_assign("vrt", num(0.0)),
                                        phi_assign("vrv", tm("r4", 152)),
                                    ]),
                                    SNode::Continue { label: None },
                                ],
                                vec![
                                    run(vec![
                                        Leaf::Raw(Stmt::Throw(tm("vres2", 145))),
                                        Leaf::Raw(Stmt::Unreachable),
                                    ]),
                                    SNode::Break { label: None },
                                ],
                            ),
                        ],
                    ),
                ],
                vec![
                    run(vec![
                        Leaf::Raw(Stmt::Throw(tm("vres1", 142))),
                        Leaf::Raw(Stmt::Unreachable),
                    ]),
                    SNode::Break { label: None },
                ],
            ),
        ]
    }

    /// The full async site: [setup, init, While] (the completion lives
    /// inside the loop).
    fn ys_async_shape() -> Vec<SNode> {
        let [setup, init] = ys_setup_init(true);
        vec![
            setup,
            init,
            SNode::While {
                label: None,
                cond: None,
                body: {
                    let mut b = vec![ys_header(), ys_dispatch(ys_ret_arm(true), ys_throw_arm())];
                    b.extend(ys_async_tail());
                    b
                },
            },
        ]
    }

    #[test]
    fn yield_star_async_positive() {
        let mut nodes = ys_async_shape();
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(stats.yield_star_bound, 1);
        assert_eq!(
            nodes,
            vec![
                run(vec![decl(
                    "vval",
                    150,
                    Expr::YieldStar {
                        value: bx(ident("src")),
                    },
                )]),
                run(vec![expr_stmt(tm("vval", 150))]),
            ],
            "{nodes:?}"
        );
    }

    #[test]
    fn ys_match_loop_tail_async_bail_pins() {
        fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_async_shape();
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            mutate(body);
            assert!(
                ys_match_loop(&nodes[2], true).is_none(),
                "near-miss matched"
            );
        }
        // The async tail is exactly [precall, await-dispatch] past the
        // header + dispatch.
        bail(|body| {
            body.truncate(3);
        });
        // The precall's exit phi must be declared there.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.remove(0);
        });
        // The call must name a precall phi…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl("vres", 112, call1(tm("other", 99), tm("vrv", 101)));
        });
        // … with the iterator as `this`…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("other", 99))),
                    args: vec![tm("vrv", 101)],
                    kind: CallKind::Dynamic,
                },
            );
        });
        // … and a phi as the argument.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("vit", 102))),
                    args: vec![tm("other", 99)],
                    kind: CallKind::Dynamic,
                },
            );
        });
        // The inner await must read the call result…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[3] = decl(
                "aw0",
                141,
                Expr::Await {
                    value: bx(tm("other", 99)),
                    uncaught: true,
                },
            );
        });
        // … and the pass-through yield must yield the awaited value.
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[4] = expr_stmt(Expr::Yield {
                value: bx(tm("other", 99)),
            });
        });
        // The resume decl must be ResumeGenerator on a header genobj…
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[5] = decl("vres1", 142, ident("not_a_driver"));
        });
        bail(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[5] = decl(
                "vres1",
                142,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("other", 99)),
                },
            );
        });
        // The await-dispatch must be an if.
        bail(|body| {
            body[3] = run(vec![]);
        });
        // … testing THROW on an inline GetResumeMode…
        bail(|body| {
            let SNode::If { cond, .. } = &mut body[3] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::Eq, tm("vg", 103), num(1.0)));
        });
        // … whose else arm is `throw res1; unreachable; break`.
        bail(|body| {
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            *otherwise = vec![];
        });
        bail(|body| {
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(tr) = &mut otherwise[0] else {
                unreachable!()
            };
            tr[0] = Leaf::Raw(Stmt::Throw(tm("other", 99)));
        });
        // The continuation: [done run, done test].
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            then.remove(0);
        });
        // The done run loads `res1.done` (the elided guard rides free).
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(dr) = &mut then[0] else {
                unreachable!()
            };
            dr[1] = decl("vdone", 113, prop(tm("other", 99), "done"));
        });
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(dr) = &mut then[0] else {
                unreachable!()
            };
            dr.push(expr_stmt(ident("extra")));
        });
        // The done test must be a positive flag test of `done`.
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut then[1] else {
                unreachable!()
            };
            *cond = isfalse(tm("vdone", 113));
        });
        // The done arm is [exit dispatch, break].
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            done.remove(1); // no break
        });
        // The exit test must be `!exitReturn`.
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut done[0] else {
                unreachable!()
            };
            *cond = istrue(tm("vexit", 110));
        });
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut done[0] else {
                unreachable!()
            };
            *cond = isfalse(tm("other", 99));
        });
        // The normal arm opens with the completion-value load…
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { then: normal, .. } = &mut done[0] else {
                unreachable!()
            };
            let SNode::Stmts(nr) = &mut normal[0] else {
                unreachable!()
            };
            nr[0] = decl("vval", 150, prop(tm("other", 99), "value"));
        });
        // … and the return arm is `v2 = res1.value; return v2`.
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut done[0] else {
                unreachable!()
            };
            let SNode::Stmts(rr) = &mut otherwise[0] else {
                unreachable!()
            };
            rr[1] = Leaf::Raw(Stmt::Return(Some(tm("other", 99))));
        });
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut done[0] else {
                unreachable!()
            };
            otherwise[0] = run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))]);
        });
        // The not-done arm must be the async yield machinery.
        bail(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut then[1] else {
                unreachable!()
            };
            *otherwise = vec![];
        });
    }

    #[test]
    fn ys_match_async_yield_bail_pins() {
        // A near-miss pin: mutate the not-done arm of the async shape;
        // the loop match must fail.
        fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_async_shape();
            {
                let SNode::While { body, .. } = ys_while(&mut nodes) else {
                    unreachable!()
                };
                let SNode::If { then, .. } = &mut body[3] else {
                    unreachable!()
                };
                let SNode::If { otherwise, .. } = &mut then[1] else {
                    unreachable!()
                };
                mutate(otherwise);
            }
            assert!(
                ys_match_loop(&nodes[2], true).is_none(),
                "near-miss matched"
            );
        }
        // Baseline: the shape matches.
        let nodes = ys_async_shape();
        assert!(ys_match_loop(&nodes[2], true).is_some());
        // The not-done arm is [head run, mode if].
        bail(|next| {
            next.truncate(1);
        });
        // The head: `[value = res1.value, av = await value, yield av,
        // res2 = ResumeGenerator(g)]`.
        bail(|next| {
            let SNode::Stmts(head) = &mut next[0] else {
                unreachable!()
            };
            head[0] = decl("v2", 143, prop(tm("other", 99), "value"));
        });
        bail(|next| {
            let SNode::Stmts(head) = &mut next[0] else {
                unreachable!()
            };
            head[1] = decl(
                "av2",
                144,
                Expr::Await {
                    value: bx(tm("other", 99)),
                    uncaught: true,
                },
            );
        });
        bail(|next| {
            let SNode::Stmts(head) = &mut next[0] else {
                unreachable!()
            };
            head[2] = expr_stmt(Expr::Yield {
                value: bx(tm("other", 99)),
            });
        });
        bail(|next| {
            let SNode::Stmts(head) = &mut next[0] else {
                unreachable!()
            };
            head[3] = decl("vres2", 145, ident("not_a_driver"));
        });
        // The mode if: the THROW dispatch on the new pair…
        bail(|next| {
            let SNode::If { cond, .. } = &mut next[1] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::Eq, tm("vg", 103), num(1.0)));
        });
        // … with `throw res2; unreachable; break` in the else.
        bail(|next| {
            let SNode::If { otherwise, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(tr) = &mut otherwise[0] else {
                unreachable!()
            };
            tr[0] = Leaf::Raw(Stmt::Throw(tm("other", 99)));
        });
        // The resumption re-entry skeleton: [pair, next-if, await run,
        // throw-if, loopback, continue].
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            then.truncate(1);
        });
        // The pair: `[r3 = ResumeGenerator(g), m3 = GetResumeMode(g)]`.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(pair) = &mut then[0] else {
                unreachable!()
            };
            pair[1] = decl("m3", 147, ident("not_a_driver"));
        });
        // The NEXT test: `if (m3 != RETURN) { loop back; continue }`.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut then[1] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::Eq, tm("other", 99), num(0.0)));
        });
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::If { then: lb, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::Stmts(assigns) = &mut lb[0] else {
                unreachable!()
            };
            assigns[1] = phi_assign("vrv", tm("other", 99));
        });
        // The RETURN await run shape.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(ar) = &mut then[2] else {
                unreachable!()
            };
            ar[0] = decl(
                "aw3",
                148,
                Expr::Await {
                    value: bx(tm("other", 99)),
                    uncaught: true,
                },
            );
        });
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(ar) = &mut then[2] else {
                unreachable!()
            };
            ar[3] = decl("m4", 153, ident("not_a_driver"));
        });
        // The THROW test: `if (m4 == THROW) { loop back; continue }`.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut then[3] else {
                unreachable!()
            };
            *cond = isfalse(cmp(CmpOp::NotEq, tm("other", 99), num(1.0)));
        });
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::If { then: lb, .. } = &mut then[3] else {
                unreachable!()
            };
            let SNode::Stmts(assigns) = &mut lb[0] else {
                unreachable!()
            };
            assigns[0] = phi_assign("vrt", tm("other", 99));
        });
        // The final loop-back: `rt ← RETURN(0)`, `rv ← r4`.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(fin) = &mut then[4] else {
                unreachable!()
            };
            fin[0] = phi_assign("vrt", num(1.0));
        });
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(fin) = &mut then[4] else {
                unreachable!()
            };
            fin[1] = phi_assign("vrv", tm("other", 99));
        });
    }

    #[test]
    fn ys_apply_bare_bail_pins() {
        // The loop must match…
        let mut nodes = ys_sync_shape();
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        body.truncate(2);
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
        // … and sit at index ≥ 2 (setup + init precede it).
        let mut full = ys_sync_shape();
        let mut nodes = full.split_off(2);
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
        // The setup run must match.
        let mut nodes = ys_sync_shape();
        nodes[0] = run(vec![expr_stmt(ident("x"))]);
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
        // The init run must match.
        let mut nodes = ys_sync_shape();
        nodes[1] = run(vec![expr_stmt(ident("x"))]);
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
        // The sync completion dispatch must be the next sibling.
        let mut nodes = ys_sync_shape();
        nodes.pop();
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
        let mut nodes = ys_sync_shape();
        nodes[3] = SNode::Honest("h".to_string());
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0);
    }

    #[test]
    fn ys_apply_fragments_sync_positive_and_bails() {
        // Arrangement B: the structurer's try-fragment split.
        let sync_fragments = || {
            let [setup, init] = ys_setup_init(false);
            let full = ys_sync_shape();
            let w = full[2].clone();
            let exit = full[3].clone();
            vec![
                try_node(vec![setup, init], vec![]),
                try_node(vec![w], vec![]),
                try_node(vec![exit], vec![]),
            ]
        };
        let mut nodes = sync_fragments();
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(stats.yield_star_bound, 1);
        // The loop fragment now holds the yield* stmt; the setup
        // fragment dropped both plumbing runs; the exit fragment holds
        // the continuation.
        let SNode::Try { body, .. } = &nodes[1] else {
            unreachable!()
        };
        assert!(
            matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::Declare { value: Expr::YieldStar { .. }, .. }))),
            "{body:?}"
        );
        let SNode::Try { body, .. } = &nodes[0] else {
            unreachable!()
        };
        assert!(body.is_empty(), "{body:?}");
        let SNode::Try { body, .. } = &nodes[2] else {
            unreachable!()
        };
        assert!(
            matches!(&body[0], SNode::Stmts(run) if run.len() == 1),
            "the exit fragment holds the continuation: {body:?}"
        );
        // Nested single-child try wrappers descend to the innermost.
        let mut nodes = sync_fragments();
        nodes[1] = try_node(vec![nodes[1].clone()], vec![]);
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        // Bail pins (each refuses the fold).
        let bail = |mut nodes: Vec<SNode>| {
            let mut stats = FoldStats::default();
            yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
            assert_eq!(stats.yield_star_sites, 0, "{nodes:?}");
        };
        // The loop fragment must be a try holding a While…
        bail(vec![SNode::Honest("h".to_string())]);
        // … at the END of its innermost body.
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[1] else {
            unreachable!()
        };
        body.push(SNode::Honest("h".to_string()));
        bail(bad);
        // … matching the full driver shape.
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[1] else {
            unreachable!()
        };
        body[0] = SNode::While {
            label: None,
            cond: None,
            body: vec![],
        };
        bail(bad);
        // The setup fragment must exist…
        let bad = sync_fragments().split_off(1);
        bail(bad);
        // … be a try…
        let mut bad = sync_fragments();
        bad[0] = run(vec![]);
        bail(bad);
        // … with at least the setup + init runs…
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[0] else {
            unreachable!()
        };
        body.truncate(1);
        bail(bad);
        // … whose setup matches…
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[0] else {
            unreachable!()
        };
        body[0] = run(vec![expr_stmt(ident("x"))]);
        bail(bad);
        // … and whose init matches.
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[0] else {
            unreachable!()
        };
        body[1] = run(vec![expr_stmt(ident("x"))]);
        bail(bad);
        // The sync exit fragment must exist…
        let mut bad = sync_fragments();
        bad.pop();
        bail(bad);
        // … and match the completion dispatch.
        let mut bad = sync_fragments();
        let SNode::Try { body, .. } = &mut bad[2] else {
            unreachable!()
        };
        body[0] = run(vec![expr_stmt(ident("x"))]);
        bail(bad);
    }

    #[test]
    fn ys_apply_fragments_async_positive() {
        let [setup, init] = ys_setup_init(true);
        let full = ys_async_shape();
        let w = full[2].clone();
        let mut nodes = vec![
            try_node(vec![setup, init], vec![]),
            try_node(vec![w], vec![]),
        ];
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(stats.yield_star_bound, 1);
        // The loop fragment holds the yield* stmt + the in-loop
        // continuation; no exit fragment is needed for async.
        let SNode::Try { body, .. } = &nodes[1] else {
            unreachable!()
        };
        assert!(
            matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::Declare { value: Expr::YieldStar { .. }, .. }))),
            "{body:?}"
        );
        assert!(
            body.len() == 2,
            "yield* + the done-arm continuation: {body:?}"
        );
    }

    #[test]
    fn ys_setup_init_exit_matchers() {
        let full = ys_sync_shape();
        let mut uses = BTreeMap::new();
        count_temp_uses(&full, &mut uses);
        // ys_match_setup.
        let (delegate, iter, next, prefix) =
            ys_match_setup(&full[0], false, &uses).expect("the setup run");
        assert_eq!(delegate, ident("src"));
        assert_eq!(iter, ValueId::new(200));
        assert_eq!(next, ValueId::new(201));
        assert!(prefix.is_empty());
        // Not a run; too short; the last two must be the declares…
        assert!(ys_match_setup(&SNode::Honest("h".to_string()), false, &uses).is_none());
        assert!(ys_match_setup(&run(vec![]), false, &uses).is_none());
        assert!(ys_match_setup(&run(vec![expr_stmt(ident("x"))]), false, &uses).is_none());
        let bad = run(vec![
            expr_stmt(ident("x")),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]);
        assert!(ys_match_setup(&bad, false, &uses).is_none());
        // … the second-to-last an Iter of the right kind…
        let bad = run(vec![
            decl("vit0", 200, ident("not_iter")),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]);
        assert!(ys_match_setup(&bad, false, &uses).is_none());
        let bad = run(vec![
            decl(
                "vit0",
                200,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]);
        assert!(
            ys_match_setup(&bad, true, &uses).is_none(),
            "sync op in an async fold"
        );
        assert!(ys_match_setup(&bad, false, &uses).is_some());
        // … and `next` must load `.next` off the iterator.
        let bad = run(vec![
            decl(
                "vit0",
                200,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("vnext", 201, prop(tm("vit0", 200), "previous")),
        ]);
        assert!(ys_match_setup(&bad, false, &uses).is_none());
        // A single-use temp delegate inlines into the yield*.
        let with_temp_delegate = run(vec![
            decl("td", 205, call0(ident("make_iter"))),
            decl(
                "vit0",
                200,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(tm("td", 205)),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]);
        let mut uses = BTreeMap::new();
        uses.insert(ValueId::new(205), 1);
        let (delegate, .., prefix) =
            ys_match_setup(&with_temp_delegate, false, &uses).expect("temp delegate");
        assert_eq!(delegate, call0(ident("make_iter")));
        assert!(prefix.is_empty());
        // A shared temp stays a delegate reference with the prefix kept.
        let mut uses = BTreeMap::new();
        uses.insert(ValueId::new(205), 2);
        let (delegate, .., prefix) =
            ys_match_setup(&with_temp_delegate, false, &uses).expect("shared temp");
        assert_eq!(delegate, tm("td", 205));
        assert_eq!(prefix.len(), 1);

        // ys_match_init (against the loop match's extracted phis).
        let lp = ys_match_loop(&full[2], false).expect("the sync loop");
        assert!(ys_match_init(&full[1], &lp, ValueId::new(200), ValueId::new(201)).is_some());
        // Not a run / empty.
        assert!(
            ys_match_init(
                &SNode::Honest("h".to_string()),
                &lp,
                ValueId::new(200),
                ValueId::new(201)
            )
            .is_none()
        );
        assert!(ys_match_init(&run(vec![]), &lp, ValueId::new(200), ValueId::new(201)).is_none());
        // A non-assign leaf…
        let bad = run(vec![phi_assign("vrt", num(2.0)), expr_stmt(ident("x"))]);
        assert!(ys_match_init(&bad, &lp, ValueId::new(200), ValueId::new(201)).is_none());
        // … assigns split across blocks…
        let bad = run(vec![
            phi_assign("vrt", num(2.0)),
            phi_assign("vrv", undef()),
            phi_assign("vflag", boolean(false)),
            phi_assign("vit", tm("vit0", 200)),
            phi_assign("vg", tm("vg0", 202)),
            phi_assign("vm", tm("vnext", 201)),
            Leaf::Raw(Stmt::PhiAssign {
                target: "vx".to_string(),
                value: ident("x"),
                to: BlockId::new(8),
                exceptional: false,
            }),
        ]);
        assert!(ys_match_init(&bad, &lp, ValueId::new(200), ValueId::new(201)).is_none());
        // … and must anchor mode=2, received=undefined, flag=false,
        // the iterator, the genobj, and exactly one method.
        for (i, leaf) in [
            phi_assign("vrt", num(1.0)),
            phi_assign("vrv", boolean(false)),
            phi_assign("vflag", boolean(true)),
            phi_assign("vit", tm("other", 99)),
            phi_assign("vm", tm("other", 99)),
        ]
        .into_iter()
        .enumerate()
        {
            let SNode::Stmts(init) = &full[1] else {
                unreachable!()
            };
            let mut bad = init.clone();
            bad[i] = leaf;
            assert!(
                ys_match_init(&run(bad), &lp, ValueId::new(200), ValueId::new(201)).is_none(),
                "mutation {i}"
            );
        }
        // The genobj assign is required.
        let SNode::Stmts(init) = &full[1] else {
            unreachable!()
        };
        let mut bad = init.clone();
        bad.remove(4);
        assert!(ys_match_init(&run(bad), &lp, ValueId::new(200), ValueId::new(201)).is_none());
        // An exceptional assign rides along free.
        let mut good = init.clone();
        good.push(exc_assign("vx", ident("z")));
        assert!(ys_match_init(&run(good), &lp, ValueId::new(200), ValueId::new(201)).is_some());

        // ys_match_exit.
        let res = ys_sync_res(&full[2]).expect("the res temp");
        assert_eq!(res, ValueId::new(112));
        let exit = ys_match_exit(&full[3], lp.exit_phi.0, res).expect("the exit dispatch");
        assert_eq!(exit.0, Some(("vval".to_string(), ValueId::new(150))));
        // Must be an if…
        assert!(ys_match_exit(&SNode::Honest("h".to_string()), lp.exit_phi.0, res).is_none());
        // … testing `!exitReturn`…
        let bad = if_node(istrue(tm("vexit", 110)), vec![], vec![]);
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        let bad = if_node(isfalse(tm("other", 99)), vec![], vec![]);
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // … with the completion load opening the normal arm…
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![SNode::Honest("h".to_string())],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            ])],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(ident("x"))])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            ])],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // … (a dead Expr load instead of a declare is the unused form)…
        let unused = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            ])],
        );
        let exit = ys_match_exit(&unused, lp.exit_phi.0, res).expect("unused completion value");
        assert_eq!(exit.0, None);
        // … and the return arm returning what it loaded…
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("other", 99)))),
            ])],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // … in exactly one run…
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![
                run(vec![decl("vv2", 151, prop(tm("vres", 112), "value"))]),
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))]),
            ],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // … with only dead plumbing assigns trailing.
        let with_plumbing = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
                phi_assign("pz", ident("z")),
            ])],
        );
        assert!(ys_match_exit(&with_plumbing, lp.exit_phi.0, res).is_some());
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
                expr_stmt(ident("x")),
            ])],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // ys_sync_res: the loop's call-result temp.
        assert!(ys_sync_res(&SNode::Honest("h".to_string())).is_none());
        assert!(ys_sync_res(&full[0]).is_none());
        let no_call = SNode::While {
            label: None,
            cond: None,
            body: vec![run(vec![]), run(vec![]), run(vec![])],
        };
        assert!(ys_sync_res(&no_call).is_none());
        // ys_innermost_body: non-try / single / nested wrappers.
        assert!(ys_innermost_body(&SNode::Honest("h".to_string())).is_none());
        let t = try_node(vec![run(vec![expr_stmt(ident("x"))])], vec![]);
        assert_eq!(ys_innermost_body(&t).map(Vec::len), Some(1));
        let t2 = try_node(vec![t], vec![]);
        assert_eq!(ys_innermost_body(&t2).map(Vec::len), Some(1));
    }

    #[test]
    fn ys_small_matcher_tables() {
        // ys_is_exc_run / ys_sig.
        let exc = || {
            run(vec![
                exc_assign("a", ident("x")),
                exc_assign("b", ident("y")),
            ])
        };
        assert!(ys_is_exc_run(&exc()));
        assert!(!ys_is_exc_run(&run(vec![])));
        assert!(!ys_is_exc_run(&run(vec![phi_assign("a", ident("x"))])));
        assert!(!ys_is_exc_run(&SNode::Honest("h".to_string())));
        let nodes = vec![exc(), run(vec![expr_stmt(ident("a"))])];
        assert_eq!(ys_sig(&nodes).len(), 1);
        // ys_assign_run: phi assigns to ONE block (exceptional skipped).
        assert_eq!(
            ys_assign_run(&run(vec![
                phi_assign("a", ident("x")),
                exc_assign("b", ident("y")),
                phi_assign("c", ident("z")),
            ])),
            Some(BlockId::new(7))
        );
        assert!(ys_assign_run(&SNode::Honest("h".to_string())).is_none());
        assert!(ys_assign_run(&run(vec![])).is_none());
        assert!(ys_assign_run(&run(vec![expr_stmt(ident("x"))])).is_none());
        assert!(
            ys_assign_run(&run(vec![
                phi_assign("a", ident("x")),
                Leaf::Raw(Stmt::PhiAssign {
                    target: "b".to_string(),
                    value: ident("y"),
                    to: BlockId::new(8),
                    exceptional: false,
                }),
            ]))
            .is_none()
        );
        // ys_phi_decls: the leading phi decls, by name.
        let got = ys_phi_decls(&run(vec![
            phi_decl("a", 1),
            phi_decl("b", 2),
            expr_stmt(ident("x")),
            phi_decl("c", 3),
        ]));
        assert_eq!(got.map(|m| m.len()), Some(2));
        assert!(ys_phi_decls(&SNode::Honest("h".to_string())).is_none());
        // ys_mode_test: `IsFalse(StrictEq(t, num))` in either order.
        assert_eq!(
            ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), num(2.0))), 2.0),
            Some(ValueId::new(5))
        );
        assert_eq!(
            ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, num(2.0), tm("t", 5))), 2.0),
            Some(ValueId::new(5))
        );
        assert!(ys_mode_test(&cmp(CmpOp::StrictEq, tm("t", 5), num(2.0)), 2.0).is_none());
        assert!(ys_mode_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), num(2.0))), 2.0).is_none());
        assert!(ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, ident("t"), num(2.0))), 2.0).is_none());
        assert!(
            ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, ident("t"), ident("u"))), 2.0).is_none()
        );
        assert!(ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), num(1.0))), 2.0).is_none());
        // ys_flag_test: wrapper polarity.
        assert_eq!(ys_flag_test(&tm("t", 5)), Some((ValueId::new(5), true)));
        assert_eq!(
            ys_flag_test(&istrue(tm("t", 5))),
            Some((ValueId::new(5), true))
        );
        assert_eq!(
            ys_flag_test(&isfalse(tm("t", 5))),
            Some((ValueId::new(5), false))
        );
        assert_eq!(
            ys_flag_test(&isfalse(isfalse(tm("t", 5)))),
            Some((ValueId::new(5), true))
        );
        assert_eq!(ys_flag_test(&ident("t")), None);
        // ys_undefined_test: `IsFalse(Eq(t, undefined))` in either order.
        assert_eq!(
            ys_undefined_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), undef()))),
            Some((ValueId::new(5), true))
        );
        assert_eq!(
            ys_undefined_test(&isfalse(cmp(CmpOp::Eq, undef(), tm("t", 5)))),
            Some((ValueId::new(5), true))
        );
        assert!(ys_undefined_test(&cmp(CmpOp::Eq, tm("t", 5), undef())).is_none());
        assert!(ys_undefined_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), undef()))).is_none());
        assert!(ys_undefined_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), ident("u")))).is_none());
        // ys_driver / ys_prop / ys_declare_of.
        let drv = Expr::GeneratorDriver {
            resume: true,
            genobj: bx(tm("g", 7)),
        };
        assert!(ys_driver(&drv, true, ValueId::new(7)));
        assert!(!ys_driver(&drv, false, ValueId::new(7)));
        assert!(!ys_driver(&drv, true, ValueId::new(8)));
        assert!(!ys_driver(&ident("x"), true, ValueId::new(7)));
        assert_eq!(
            ys_prop(&prop(tm("o", 5), "next"), "next"),
            Some(ValueId::new(5))
        );
        assert_eq!(ys_prop(&prop(tm("o", 5), "next"), "done"), None);
        assert_eq!(ys_prop(&ident("o"), "next"), None);
        let d = decl("x", 5, ident("v"));
        assert_eq!(
            ys_declare_of(&d).map(|(n, i, _)| (n, i)),
            Some(("x", ValueId::new(5)))
        );
        assert_eq!(ys_declare_of(&expr_stmt(ident("x"))), None);
        // ys_contains_elided.
        assert!(ys_contains_elided(
            &[run(vec![elided("ThrowNotExists")])],
            "ThrowNotExists"
        ));
        assert!(!ys_contains_elided(
            &[run(vec![elided("Other")])],
            "ThrowNotExists"
        ));
        // ys_mode_num_test via the eq/neq wrappers + the wrong-op arm.
        assert!(
            ys_mode_neq_test(
                &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(0.0))),
                ValueId::new(5),
                0.0
            )
            .is_some()
        );
        assert!(
            ys_mode_eq_test(
                &isfalse(cmp(CmpOp::NotEq, tm("m", 5), num(1.0))),
                ValueId::new(5),
                1.0
            )
            .is_some()
        );
        assert!(
            ys_mode_eq_test(
                &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(1.0))),
                ValueId::new(5),
                1.0
            )
            .is_none()
        );
        assert!(
            ys_mode_neq_test(&cmp(CmpOp::Eq, tm("m", 5), num(0.0)), ValueId::new(5), 0.0).is_none()
        );
        assert!(ys_mode_neq_test(&isfalse(ident("c")), ValueId::new(5), 0.0).is_none());
        assert!(
            ys_mode_neq_test(
                &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(1.0))),
                ValueId::new(5),
                0.0
            )
            .is_none()
        );
        // ys_loopback directly.
        let lb = |tail: Vec<Leaf>| vec![run(tail)];
        assert!(
            ys_loopback(
                &{
                    let mut v = lb(vec![
                        phi_assign("rt", tm("m", 5)),
                        phi_assign("rv", tm("r", 6)),
                    ]);
                    v.push(SNode::Continue { label: None });
                    v
                },
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_some()
        );
        // … without the trailing continue…
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", tm("m", 5)),
                    phi_assign("rv", tm("r", 6))
                ]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_some()
        );
        // … with exceptional plumbing interspersed…
        assert!(
            ys_loopback(
                &lb(vec![
                    exc_assign("x", ident("y")),
                    phi_assign("rt", tm("m", 5)),
                    phi_assign("rv", tm("r", 6)),
                ]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_some()
        );
        // … or with mode as the RETURN literal.
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", num(0.0)),
                    phi_assign("rv", tm("r", 6))
                ]),
                &[],
                "rt",
                "rv",
                None,
                Some(ValueId::new(6)),
                true,
            )
            .is_some()
        );
        // Bails: non-empty else / bad skeleton / not a run / empty run /
        // foreign leaf / mixed blocks / wrong mode / wrong value /
        // missing anchors.
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", tm("m", 5)),
                    phi_assign("rv", tm("r", 6))
                ]),
                &[run(vec![expr_stmt(ident("x"))])],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_none()
        );
        assert!(ys_loopback(&[], &[], "rt", "rv", None, None, false).is_none());
        assert!(
            ys_loopback(
                &[
                    SNode::Honest("h".to_string()),
                    SNode::Honest("i".to_string())
                ],
                &[],
                "rt",
                "rv",
                None,
                None,
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &[SNode::Honest("h".to_string())],
                &[],
                "rt",
                "rv",
                None,
                None,
                false
            )
            .is_none()
        );
        assert!(ys_loopback(&lb(vec![]), &[], "rt", "rv", None, None, false).is_none());
        assert!(
            ys_loopback(
                &lb(vec![expr_stmt(ident("x"))]),
                &[],
                "rt",
                "rv",
                None,
                None,
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", tm("m", 5)),
                    Leaf::Raw(Stmt::PhiAssign {
                        target: "rv".to_string(),
                        value: tm("r", 6),
                        to: BlockId::new(8),
                        exceptional: false,
                    }),
                ]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", tm("other", 9)),
                    phi_assign("rv", tm("r", 6))
                ]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", tm("m", 5)),
                    phi_assign("rv", tm("other", 9))
                ]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &lb(vec![phi_assign("rt", tm("m", 5))]),
                &[],
                "rt",
                "rv",
                Some(ValueId::new(5)),
                Some(ValueId::new(6)),
                false,
            )
            .is_none()
        );
        assert!(
            ys_loopback(
                &lb(vec![
                    phi_assign("rt", num(1.0)),
                    phi_assign("rv", tm("r", 6))
                ]),
                &[],
                "rt",
                "rv",
                None,
                Some(ValueId::new(6)),
                true,
            )
            .is_none()
        );
        // ys_async_throw_dispatch directly.
        let drv_g = |resume: bool| Expr::GeneratorDriver {
            resume,
            genobj: bx(tm("g", 7)),
        };
        let throw_else = vec![
            run(vec![
                Leaf::Raw(Stmt::Throw(tm("r", 6))),
                Leaf::Raw(Stmt::Unreachable),
            ]),
            SNode::Break { label: None },
        ];
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6),
            )
            .is_some()
        );
        // … the driver on either side of the Eq…
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, num(1.0), drv_g(false))),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6),
            )
            .is_some()
        );
        assert!(
            ys_async_throw_dispatch(
                &cmp(CmpOp::Eq, drv_g(false), num(1.0)),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6)
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(ident("c")),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6)
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(false), num(2.0))),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6)
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(true), num(1.0))),
                &throw_else,
                ValueId::new(7),
                ValueId::new(6)
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
                &[],
                ValueId::new(7),
                ValueId::new(6)
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
                &[run(vec![Leaf::Raw(Stmt::Throw(tm("other", 9)))])],
                ValueId::new(7),
                ValueId::new(6),
            )
            .is_none()
        );
        assert!(
            ys_async_throw_dispatch(
                &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
                &[
                    run(vec![expr_stmt(ident("x"))]),
                    SNode::Break { label: None }
                ],
                ValueId::new(7),
                ValueId::new(6),
            )
            .is_none()
        );
    }

    #[test]
    fn dissolve_rethrow_trys_variants() {
        // The bare-rethrow wrapper dissolves loudly (Honest + body).
        let mut nodes = vec![try_node(
            vec![run(vec![expr_stmt(ident("protected"))])],
            vec![catch(
                "e",
                vec![run(vec![
                    Leaf::Raw(Stmt::Throw(tm("e", 60))),
                    Leaf::Raw(Stmt::Unreachable),
                ])],
            )],
        )];
        dissolve_rethrow_trys(&mut nodes);
        assert_eq!(
            nodes,
            vec![
                SNode::Honest("rethrow-only try/catch dissolved (semantic no-op)".to_string()),
                run(vec![expr_stmt(ident("protected"))]),
            ]
        );
        // An empty try body stays; so does a catch doing anything else.
        let mut nodes = vec![try_node(
            vec![],
            vec![catch(
                "e",
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("e", 60)))])],
            )],
        )];
        dissolve_rethrow_trys(&mut nodes);
        assert_eq!(nodes.len(), 1);
        let mut nodes = vec![try_node(
            vec![run(vec![expr_stmt(ident("protected"))])],
            vec![catch(
                "e",
                vec![run(vec![
                    Leaf::Raw(Stmt::Throw(tm("e", 60))),
                    expr_stmt(ident("extra")),
                ])],
            )],
        )];
        dissolve_rethrow_trys(&mut nodes);
        assert!(matches!(&nodes[0], SNode::Try { .. }));
        // A catch throwing a DIFFERENT temp is not a bare rethrow.
        let mut nodes = vec![try_node(
            vec![run(vec![expr_stmt(ident("protected"))])],
            vec![catch(
                "e",
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))])],
            )],
        )];
        dissolve_rethrow_trys(&mut nodes);
        assert!(matches!(&nodes[0], SNode::Try { .. }));
        // A non-run catch body stays.
        let mut nodes = vec![try_node(
            vec![run(vec![expr_stmt(ident("protected"))])],
            vec![catch("e", vec![SNode::Break { label: None }])],
        )];
        dissolve_rethrow_trys(&mut nodes);
        assert!(matches!(&nodes[0], SNode::Try { .. }));
        // A bare throw of the binding with NO body…
        let mut nodes = vec![try_node(
            vec![run(vec![expr_stmt(ident("protected"))])],
            vec![CatchClause {
                binding: None,
                body: vec![run(vec![Leaf::Raw(Stmt::Throw(ident("e")))])],
            }],
        )];
        dissolve_rethrow_trys(&mut nodes);
        // binding None → "" — the thrown ident "e" ≠ "" → kept.
        assert!(matches!(&nodes[0], SNode::Try { .. }));
    }

    #[test]
    fn sweep_walkers_recurse_into_every_region() {
        // Drive the strip/sweep walkers over a fully nested tree.
        let nested = |leaf: Leaf| -> Vec<SNode> {
            vec![
                if_node(ident("c"), vec![run(vec![leaf.clone()])], vec![]),
                SNode::While {
                    label: None,
                    cond: None,
                    body: vec![run(vec![leaf.clone()])],
                },
                SNode::DoWhile {
                    label: None,
                    body: vec![run(vec![leaf.clone()])],
                    cond: ident("d"),
                },
                SNode::Labeled {
                    label: "l".to_string(),
                    body: vec![run(vec![leaf.clone()])],
                },
                SNode::Try {
                    body: vec![run(vec![leaf.clone()])],
                    catches: vec![catch("e", vec![run(vec![leaf.clone()])])],
                    note: None,
                    finally: Some(vec![run(vec![leaf.clone()])]),
                },
                SNode::Switch {
                    disc: ident("s"),
                    cases: vec![SwitchCase {
                        tests: vec![],
                        body: vec![run(vec![leaf.clone()])],
                    }],
                },
                SNode::ForOf {
                    is_await: false,
                    binding: "k".to_string(),
                    iter: ident("i"),
                    body: vec![run(vec![leaf.clone()])],
                },
                SNode::ForIn {
                    binding: "k".to_string(),
                    obj: ident("o"),
                    body: vec![run(vec![leaf.clone()])],
                },
                SNode::Break { label: None },
                SNode::Continue { label: None },
                SNode::Honest("h".to_string()),
            ]
        };
        // sweep_dead_decls: the dead declare disappears everywhere.
        let mut nodes = nested(decl("dead", 42, ident("v")));
        sweep_dead_decls(&mut nodes, &[ValueId::new(42)].into_iter().collect());
        assert!(!nodes_use_temp(&nodes, ValueId::new(42)));
        let mut found = false;
        walk_leaves(&nodes, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::Declare { name, .. }) if name == "dead") {
                found = true;
            }
        });
        assert!(!found);
        // strip_genobj_phi_assigns: target-name + alias-value pairs go.
        let mut nodes = nested(phi_assign("victim", tm("g", 10)));
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        strip_genobj_phi_assigns(
            &mut nodes,
            &aliases,
            &["victim".to_string()].into_iter().collect(),
        );
        let mut found = false;
        walk_leaves(&nodes, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "victim") {
                found = true;
            }
        });
        assert!(!found);
        // strip_dead_phi_decls: only decls with no remaining assigns
        // and no reads.
        let mut nodes = nested(phi_decl("victim", 42));
        strip_dead_phi_decls(
            &mut nodes,
            &["victim".to_string()].into_iter().collect(),
            &BTreeSet::new(),
            &BTreeMap::new(),
        );
        let mut found = false;
        walk_leaves(&nodes, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::PhiDecl { name, .. }) if name == "victim") {
                found = true;
            }
        });
        assert!(!found);
        // … but a decl with surviving assigns stays.
        let mut nodes = nested(phi_decl("victim", 42));
        strip_dead_phi_decls(
            &mut nodes,
            &["victim".to_string()].into_iter().collect(),
            &["victim".to_string()].into_iter().collect(),
            &BTreeMap::new(),
        );
        let mut found = false;
        walk_leaves(&nodes, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::PhiDecl { name, .. }) if name == "victim") {
                found = true;
            }
        });
        assert!(found);
        // map_exprs_mut reaches every expression position incl. node
        // conditions, discriminants, and case tests.
        let mut nodes = vec![
            if_node(ident("a"), vec![], vec![]),
            SNode::While {
                label: None,
                cond: Some(ident("b")),
                body: vec![],
            },
            SNode::DoWhile {
                label: None,
                body: vec![],
                cond: ident("c"),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("d"),
                body: vec![],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("e"),
                body: vec![],
            },
            SNode::Switch {
                disc: ident("f"),
                cases: vec![SwitchCase {
                    tests: vec![ident("g")],
                    body: vec![run(vec![expr_stmt(ident("h"))])],
                }],
            },
            run(vec![decl("i", 1, ident("j"))]),
        ];
        map_exprs_mut(&mut nodes, &mut |e| {
            if let Expr::Ident(n) = e {
                *n = format!("{n}_mapped");
            }
        });
        let names = ["a", "b", "c", "d", "e", "f", "g", "h", "j"];
        for n in names {
            assert!(
                nodes_use_any(&nodes, &[format!("{n}_mapped")]),
                "{n} not mapped"
            );
        }
    }

    #[test]
    fn for_of_cleanup_try_binding() {
        // The value binding may sit inside the iterator-cleanup try
        // (which dissolves loudly when the handlers are cleanup-shaped).
        let mut nodes = for_of_site();
        let SNode::While { body, .. } = &mut nodes[1] else {
            unreachable!()
        };
        let binding_run = body[1].clone();
        body[1] = SNode::Try {
            body: vec![SNode::Honest("cut".to_string()), binding_run],
            catches: vec![catch(
                "ce",
                vec![run(vec![
                    decl("rr", 55, prop(tm("it", 10), "return")),
                    Leaf::Raw(Stmt::Throw(tm("ce", 56))),
                ])],
            )],
            note: None,
            finally: None,
        };
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_of, 1);
        let SNode::ForOf { body, .. } = &nodes[0] else {
            unreachable!()
        };
        assert!(matches!(&body[0], SNode::Honest(_)), "{body:?}");
        assert!(
            body.iter().any(|n| matches!(n, SNode::Stmts(_))),
            "{body:?}"
        );
        // A non-cleanup handler keeps the loop unfolded.
        let mut nodes = for_of_site();
        let SNode::While { body, .. } = &mut nodes[1] else {
            unreachable!()
        };
        let binding_run = body[1].clone();
        body[1] = SNode::Try {
            body: vec![binding_run],
            catches: vec![catch("ce", vec![run(vec![expr_stmt(ident("x"))])])],
            note: None,
            finally: None,
        };
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_of, 0);
        // A try whose body lacks the binding is just the body.
        let mut nodes = for_of_site();
        let SNode::While { body, .. } = &mut nodes[1] else {
            unreachable!()
        };
        body[1] = SNode::Try {
            body: vec![run(vec![expr_stmt(ident("unrelated"))])],
            catches: vec![],
            note: None,
            finally: None,
        };
        let mut nodes2 = body.clone();
        // rebuild_loop_body with the binding still in the NEXT run.
        let mut stats = FoldStats::default();
        fold(&mut nodes2, &mut stats);
        let _ = nodes;
        let _ = stats;
    }

    #[test]
    fn machine_folds_recurse_into_regions() {
        // async_machine_fold: an await site nested in an if arm and in
        // a catch body.
        for wrap in [
            |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::DoWhile {
                    label: None,
                    body: site,
                    cond: ident("d"),
                }]
            },
            |site: Vec<SNode>| {
                vec![SNode::Labeled {
                    label: "l".to_string(),
                    body: site,
                }]
            },
            |site: Vec<SNode>| vec![try_node(site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::Try {
                    body: vec![run(vec![expr_stmt(ident("x"))])],
                    catches: vec![catch("e", site)],
                    note: None,
                    finally: None,
                }]
            },
        ] {
            let mut nodes = wrap(async_body());
            let mut stats = FoldStats::default();
            async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
            assert_eq!(stats.async_machine_sites, 1, "nested await site");
        }
        // async_driver_fold through nested regions.
        for wrap in [
            |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
            |site: Vec<SNode>| {
                vec![SNode::DoWhile {
                    label: None,
                    body: site,
                    cond: ident("d"),
                }]
            },
            |site: Vec<SNode>| vec![try_node(site, vec![])],
        ] {
            let mut nodes = wrap(vec![run(vec![Leaf::Raw(Stmt::Return(Some(
                Expr::AsyncDriver {
                    resolve: true,
                    value: bx(ident("v")),
                },
            )))])]);
            let mut stats = FoldStats::default();
            async_driver_fold(&mut nodes, FunctionKind::AsyncArrow, &mut stats);
            assert_eq!(stats.async_driver, 1, "nested async driver site");
        }
        // yield_star_fold through an if arm.
        let mut nodes = vec![if_node(ident("c"), ys_sync_shape(), vec![])];
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1, "nested yield* site");
        // async_generator_machine_fold through a try body.
        let mut nodes = vec![try_node(agen_body(), vec![])];
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_yields, 1, "nested yield site");
    }

    #[test]
    fn for_await_driver_same_source_backedge() {
        // A bookkeeping phi fed the SAME invariant source by two
        // pre-loop assigns (the try-splitting duplicates regions).
        let mut nodes = driver_shape();
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.push(phi_assign("bk", ident("out")));
        assert!(match_for_await_driver(&nodes, 1).is_some());
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_await_of, 1);
    }

    #[test]
    fn agen_plain_await_site() {
        // A source-level await inside an async generator (d-P13's site
        // — no resumption pair in its continuation).
        let mut nodes = vec![
            run(vec![
                decl(
                    "g",
                    20,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
            ]),
            run(vec![
                decl(
                    "a",
                    30,
                    Expr::Await {
                        value: bx(ident("x")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 30)),
                }),
            ]),
            if_node(
                cmp(
                    CmpOp::Eq,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 20)),
                    },
                    num(1.0),
                ),
                vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                }))])],
                vec![run(vec![expr_stmt(ident("cont"))])],
            ),
        ];
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 1);
        assert_eq!(stats.agen_awaits, 1);
        assert_eq!(stats.agen_yields, 0);
        // The folded `await x` sits in the site run.
        let SNode::Stmts(site) = &nodes[1] else {
            unreachable!()
        };
        assert!(
            matches!(&site[0], Leaf::Raw(Stmt::Expr(Expr::Await { value, .. })) if value.as_ref() == &ident("x")),
            "{site:?}"
        );
    }

    #[test]
    fn residual_driver_checkpoint_pins() {
        // The candidate node must be an unlabeled `while (true)`.
        let mut nodes = driver_shape();
        nodes[1] = SNode::Honest("h".to_string());
        assert!(match_for_await_driver(&nodes, 1).is_none());
        let mut nodes = driver_shape();
        let SNode::While { label, .. } = &mut nodes[1] else {
            unreachable!()
        };
        *label = Some("l".to_string());
        assert!(match_for_await_driver(&nodes, 1).is_none());
        // The call's receiver must be a header phi (callee covered
        // elsewhere).
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::Stmts(hdr) = &mut body[2] else {
                unreachable!()
            };
            hdr[0] = decl(
                "res",
                23,
                Expr::Call {
                    callee: bx(tm("np", 20)),
                    this: Some(bx(tm("not_a_phi", 99))),
                    args: vec![],
                    kind: CallKind::Direct,
                },
            );
        });
        // The binding scan skips leading honesty comments in the body.
        let mut nodes = driver_shape();
        {
            let body = driver_body(&mut nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            otherwise.insert(0, SNode::Honest("note".to_string()));
        }
        assert!(match_for_await_driver(&nodes, 1).is_some());
        // A cleanup try WITHOUT the value binding ends the scan with
        // none.
        driver_bails(|nodes| {
            let body = driver_body(nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            otherwise[0] = try_node(vec![run(vec![expr_stmt(ident("x"))])], vec![]);
        });
        // A no-source bookkeeping phi is foldable only when unused:
        // unused folds (dropped assigns)…
        let mut nodes = driver_shape();
        {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre.remove(4); // the bk ← out entry assign
            let body = driver_body(&mut nodes);
            let SNode::If { otherwise, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(bind) = &mut otherwise[0] else {
                unreachable!()
            };
            bind.remove(1); // and the store reading bk
        }
        assert!(match_for_await_driver(&nodes, 1).is_some());
        // … used in the re-homed tail bails…
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre.remove(4);
            let body = driver_body(nodes);
            let SNode::If {
                otherwise, then, ..
            } = &mut body[3]
            else {
                unreachable!()
            };
            let SNode::Stmts(bind) = &mut otherwise[0] else {
                unreachable!()
            };
            bind.remove(1);
            let SNode::Stmts(tail) = &mut then[0] else {
                unreachable!()
            };
            tail.push(expr_stmt(tm("bk", 22)));
        });
        // … and a phi source that is itself a header phi bails (no
        // chains).
        driver_bails(|nodes| {
            let SNode::Stmts(pre) = &mut nodes[0] else {
                unreachable!()
            };
            pre[4] = phi_assign("bk", tm("ip", 21));
        });
    }

    #[test]
    fn rebuild_loop_body_shape_bails() {
        let folded = || LoopFold {
            is_await: false,
            is_in: false,
            iter: ident("src"),
            pre_cut: 0,
            phi_names: vec!["np".to_string()],
            res_name: Some("res".to_string()),
            done_name: Some("done".to_string()),
            extra_internals: vec!["it".to_string(), "next".to_string()],
            hoisted: vec![],
        };
        let hdr = || {
            run(vec![
                phi_decl("np", 20),
                decl("res", 23, call0(tm("np", 20))),
                decl("done", 25, prop(tm("res", 23), "done")),
            ])
        };
        let binding = || {
            run(vec![
                decl("v", 26, prop(tm("res", 23), "value")),
                expr_stmt(call1(ident("print"), tm("v", 26))),
            ])
        };
        // The positive: header + binding run.
        let body = vec![hdr(), binding()];
        let (b, out) = rebuild_loop_body(&body, &folded()).expect("corpus shape");
        assert_eq!(b, "v");
        assert_eq!(out.len(), 1);
        // The body must outlive its header.
        assert!(rebuild_loop_body(&[], &folded()).is_none());
        // The binding must be a `.value` declare…
        assert!(rebuild_loop_body(&[hdr(), run(vec![expr_stmt(ident("x"))])], &folded()).is_none());
        // … in a run or cleanup try, not an arbitrary node.
        assert!(rebuild_loop_body(&[hdr(), SNode::Honest("h".to_string())], &folded()).is_none());
        // Internal temps must not survive in the kept body.
        assert!(
            rebuild_loop_body(
                &[hdr(), {
                    let mut b = binding();
                    let SNode::Stmts(r) = &mut b else {
                        unreachable!()
                    };
                    r.push(expr_stmt(tm("np", 20)));
                    b
                }],
                &folded(),
            )
            .is_none()
        );
        // The for-in rebuild: header must be a run, and the binding is
        // its last declare.
        let folded_in = || LoopFold {
            is_await: false,
            is_in: true,
            iter: ident("src"),
            pre_cut: 0,
            phi_names: vec!["ip".to_string()],
            res_name: None,
            done_name: None,
            extra_internals: vec!["ip".to_string()],
            hoisted: vec![],
        };
        let in_hdr = || {
            run(vec![
                phi_decl("ip", 20),
                decl(
                    "k",
                    31,
                    Expr::Iter {
                        op: IterOp::NextPropName,
                        obj: bx(tm("ip", 20)),
                        status: NodeStatus::Plumbing,
                    },
                ),
            ])
        };
        let (b, out) = rebuild_loop_body(
            &[
                in_hdr(),
                run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
            ],
            &folded_in(),
        )
        .expect("for-in rebuild");
        assert_eq!(b, "k");
        assert_eq!(out.len(), 1);
        assert!(rebuild_loop_body(&[SNode::Honest("h".to_string())], &folded_in()).is_none());
        assert!(rebuild_loop_body(&[run(vec![phi_decl("ip", 20)])], &folded_in()).is_none());
        // … and the internals must not be read post-elimination.
        assert!(
            rebuild_loop_body(
                &[in_hdr(), run(vec![expr_stmt(tm("ip", 20))])],
                &folded_in(),
            )
            .is_none()
        );
        // fold_loops leaves a non-matching loop alone.
        let mut nodes = vec![SNode::While {
            label: Some("l".to_string()),
            cond: Some(ident("c")),
            body: vec![],
        }];
        let before = nodes.clone();
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(nodes, before);
    }

    #[test]
    fn residual_ft_extract_and_strip_pins() {
        // Copy-chain edges through Declare leaves trace too (Assign
        // leaves are never bookkeeping, so that edge arm is filtered
        // out upstream).
        let mut body = dispatch_body();
        let SNode::Stmts(bk) = &mut body[0] else {
            unreachable!()
        };
        // y ← e via a Declare, x ← y via the phi assign: x traces.
        bk[1] = decl("y", 66, tm("e", 61));
        bk.push(phi_assign("x", tm("y", 66)));
        assert!(ft_extract_dispatch(&body, "e").is_some());
        // … but the guard/rethrow temp must still trace to the binding:
        // with the phi assign gone and no Declare edge, x dangles.
        let mut body = dispatch_body();
        let SNode::Stmts(bk) = &mut body[0] else {
            unreachable!()
        };
        bk.remove(1);
        assert!(ft_extract_dispatch(&body, "e").is_none());
        // A cyclic copy chain still terminates the BFS.
        let mut body = dispatch_body();
        let SNode::Stmts(bk) = &mut body[0] else {
            unreachable!()
        };
        bk[1] = phi_assign("x", tm("y", 97));
        bk.push(phi_assign("y", tm("x", 63)));
        assert!(ft_extract_dispatch(&body, "e").is_none());
        // ft_rethrow_temp: an arm of pure bookkeeping has no terminal.
        assert_eq!(
            ft_rethrow_temp(
                &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
                &[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
                &[run(vec![phi_assign("p", ident("q"))])],
            ),
            None
        );
        // ft_fold_at's own entry guards (the driver normally
        // pre-filters; the matcher is total on its own).
        let not_try = vec![SNode::Honest("h".to_string())];
        assert!(ft_fold_at(&not_try, 0).is_none());
        let no_note = vec![SNode::Try {
            body: vec![],
            catches: vec![catch("e", dispatch_body())],
            note: None,
            finally: None,
        }];
        assert!(ft_fold_at(&no_note, 0).is_none());
        let two_catches = vec![SNode::Try {
            body: vec![],
            catches: vec![catch("e", dispatch_body()), catch("e2", vec![])],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        }];
        assert!(ft_fold_at(&two_catches, 0).is_none());
        // ft_strip_exits: a DIFFERENT copy at a far-enough exit hits
        // the canon comparison (not the room check).
        let idiom = test_idiom();
        let mut nodes = vec![
            run(vec![
                decl("f1", 70, ident("DIFFERENT")),
                phi_assign("f3", ident("w")),
            ]),
            run(vec![Leaf::Raw(Stmt::Return(None))]),
        ];
        let (r, _) = strip(&mut nodes, &idiom);
        assert!(r.is_err());
    }

    #[test]
    fn residual_walker_and_sweep_pins() {
        // nodes_declare_or_assign: the Declare/PhiDecl arms and the
        // early exit.
        assert!(nodes_declare_or_assign(
            &[
                run(vec![decl("q", 1, ident("v"))]),
                run(vec![decl("q", 1, ident("v"))]),
            ],
            "q"
        ));
        assert!(nodes_declare_or_assign(&[run(vec![phi_decl("q", 1)])], "q"));
        // walk_cleanup: the do-while recursion arm and the catch-all.
        let mut bad = false;
        let (mut rt, mut rl) = (false, false);
        walk_cleanup(
            &[
                SNode::DoWhile {
                    label: None,
                    body: vec![run(vec![decl("r", 51, prop(tm("it", 52), "return"))])],
                    cond: ident("c"),
                },
                SNode::Break { label: None },
                SNode::Continue { label: None },
                SNode::Honest("h".to_string()),
                SNode::Switch {
                    disc: ident("d"),
                    cases: vec![],
                },
            ],
            "e",
            &mut rt,
            &mut rl,
            &mut bad,
        );
        assert!(rl && !rt && !bad);
        // collect_aliases: the do-while arm and the catch-all.
        let mut aliases = vec!["e".to_string()];
        let mut grew = true;
        while grew {
            grew = false;
            collect_aliases(
                &[
                    SNode::DoWhile {
                        label: None,
                        body: vec![run(vec![decl("a", 50, tm("e", 49))])],
                        cond: ident("c"),
                    },
                    SNode::Break { label: None },
                    SNode::Switch {
                        disc: ident("d"),
                        cases: vec![],
                    },
                ],
                &mut aliases,
                &mut grew,
            );
        }
        assert!(aliases.contains(&"a".to_string()));
        // expr_has_return_load: a "return" load nested under a
        // non-matching PropDyn key.
        assert!(expr_has_return_load(&Expr::PropDyn {
            object: bx(prop(ident("o"), "return")),
            key: bx(strlit("other")),
        }));
        // residue_match: a non-run significant sibling bails.
        let nodes = vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![run(vec![decl(
                    "a",
                    50,
                    Expr::Await {
                        value: bx(ident("p")),
                        uncaught: true,
                    },
                )])],
            },
            SNode::Break { label: None },
        ];
        let mut nodes = nodes;
        let mut stats = FoldStats::default();
        sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
        assert_eq!(stats.dead_exit_throw, 0);
        // sweep_async_machinery: non-alias phi values pass through;
        // alias-valued assigns into LIVE phis count as real uses; a
        // surviving foreign assign keeps the decl census honest.
        let mut nodes = vec![run(vec![
            phi_decl("pa", 20),
            phi_decl("live", 21),
            phi_assign("foreign", ident("z")),
            phi_assign("pa", tm("g", 10)),
            phi_assign("live", tm("g", 10)),
            expr_stmt(tm("live", 21)),
        ])];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        // The foreign assign stays; the live phi's machinery assign
        // stays (it is a real use); the dead alias phi's decl stays
        // (its assign was stripped but the alias web is alive).
        assert!(got.iter().any(
            |l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "foreign")
        ));
        assert!(
            got.iter().any(
                |l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "live")
            )
        );
    }

    #[test]
    fn residual_match_arm_pins() {
        // match_for_in: the header's last leaf must be the NextPropName
        // declare…
        let site = for_in_site();
        let (pre, wcond, body) = {
            let SNode::While { cond, body, .. } = &site[1] else {
                unreachable!()
            };
            let pre = match &site[0] {
                SNode::Stmts(l) => l.clone(),
                _ => unreachable!(),
            };
            (pre, cond.clone().unwrap(), body.clone())
        };
        let mut bbody = body.clone();
        let SNode::Stmts(hdr) = &mut bbody[0] else {
            unreachable!()
        };
        hdr[2] = decl("k", 31, ident("not_nextpropname"));
        assert!(match_for_in(&pre, &wcond, &bbody).is_none());
        // … and the wiring scan stops at the first non-assign leaf.
        let mut pre2 = vec![decl("prelude", 5, ident("x"))];
        pre2.extend(pre.clone());
        assert!(match_for_in(&pre2, &wcond, &body).is_some());
        // A for-in whose internals are still read after elimination
        // vetoes the fold.
        let mut nodes = for_in_site();
        let SNode::While { body, .. } = &mut nodes[1] else {
            unreachable!()
        };
        let SNode::Stmts(use_run) = &mut body[1] else {
            unreachable!()
        };
        use_run.push(expr_stmt(tm("ip", 20)));
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_in, 0);
        // match_await_site: the await declare must be THE suspended
        // temp's…
        let mut bad = async_body();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site[2] = decl(
            "a",
            99,
            Expr::Await {
                value: bx(ident("p")),
                uncaught: true,
            },
        );
        let mut uses = BTreeMap::new();
        count_temp_uses(&bad, &mut uses);
        let mut cx = AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: [ValueId::new(10)].into_iter().collect(),
            exit_throws: BTreeSet::new(),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
            uses,
        };
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // … and the suspend value is a temp or an inlined await.
        let mut bad = async_body();
        let SNode::Stmts(site) = &mut bad[0] else {
            unreachable!()
        };
        site[3] = expr_stmt(Expr::Yield {
            value: bx(ident("neither")),
        });
        let mut uses = BTreeMap::new();
        count_temp_uses(&bad, &mut uses);
        let mut cx = AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: [ValueId::new(10)].into_iter().collect(),
            exit_throws: BTreeSet::new(),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
            uses,
        };
        assert!(match_await_site(&bad, 0, &mut cx).is_none());
        // match_async_dispatch: the istrue wrapper keeps polarity.
        let mut cx = AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: [ValueId::new(10)].into_iter().collect(),
            exit_throws: BTreeSet::new(),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
            uses: BTreeMap::new(),
        };
        let dispatch = if_node(
            istrue(cmp(CmpOp::Eq, tm("m", 14), num(1.0))),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
            vec![run(vec![expr_stmt(ident("cont"))])],
        );
        assert!(
            match_async_dispatch(
                &dispatch,
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_some()
        );
        // The break-routed throw arm: the dispatch falls back to the
        // break check when the inline-throw check refuses.
        let mut cx = AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: [ValueId::new(10)].into_iter().collect(),
            exit_throws: [ValueId::new(13)].into_iter().collect(),
            const_env: BTreeMap::new(),
            consumed_consts: BTreeSet::new(),
            uses: BTreeMap::new(),
        };
        let dispatch = if_node(
            cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
            vec![SNode::Break { label: None }],
            vec![run(vec![expr_stmt(ident("cont"))])],
        );
        assert!(
            match_async_dispatch(
                &dispatch,
                Some(ValueId::new(14)),
                Some(ValueId::new(13)),
                &mut cx,
            )
            .is_some()
        );
    }

    #[test]
    fn map_exprs_mut_store_arms() {
        // The store-kind arms of the map walker (via rest_param_fold's
        // census walks).
        let mut nodes = vec![run(vec![
            Leaf::Raw(Stmt::StoreProp {
                object: ident("o"),
                name: "p".to_string(),
                dot_legal: true,
                value: ident("v"),
                own: false,
            }),
            Leaf::Raw(Stmt::StoreIndex {
                object: ident("o"),
                index: ident("i"),
                value: ident("v"),
                own: false,
            }),
            Leaf::Raw(Stmt::StoreDyn {
                object: ident("o"),
                key: ident("k"),
                value: ident("v"),
                own: false,
            }),
            Leaf::Raw(Stmt::DefineMethod {
                object: ident("o"),
                name: "m".to_string(),
                func: ident("f"),
                length: 0,
            }),
            Leaf::Raw(Stmt::StorePrivate {
                object: ident("o"),
                name: "q".to_string(),
                value: ident("v"),
                define: false,
            }),
            Leaf::Raw(Stmt::StoreSuper {
                name: None,
                key: Some(ident("k")),
                value: ident("v"),
            }),
            Leaf::Raw(Stmt::StoreSuper {
                name: Some("s".to_string()),
                key: None,
                value: ident("v"),
            }),
            Leaf::Raw(Stmt::CondBranch {
                cond: ident("c"),
                true_dest: BlockId::new(1),
                false_dest: BlockId::new(2),
            }),
            decl("args", 60, Expr::RestArgs { start_index: 0 }),
            expr_stmt(tm("temp", 61)),
        ])];
        let mut params = vec!["p2".to_string()];
        let mut stats = FoldStats::default();
        rest_param_fold(&mut nodes, &mut params, 0, &mut stats);
        assert_eq!(stats.rest_param, 1);
    }

    #[test]
    fn ys_tail_residual_pins() {
        // ── sync tail residuals ──
        fn bail_sync(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_sync_shape();
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            mutate(body);
            assert!(
                ys_match_loop(&nodes[2], false).is_none(),
                "near-miss matched"
            );
        }
        // The call must carry `this` (a temp receiver)…
        bail_sync(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl("vres", 112, call0(tm("vm", 111)));
        });
        // … and a temp as its only argument.
        bail_sync(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("vit", 102))),
                    args: vec![ident("not_a_temp")],
                    kind: CallKind::Dynamic,
                },
            );
        });
        // The precall must contain the call at all.
        bail_sync(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.remove(2);
        });
        // The done test must be an if.
        bail_sync(|body| {
            body[3] = run(vec![]);
        });
        // The suspend must be a statement run of the exact pair shape.
        bail_sync(|body| {
            body[4] = SNode::Honest("h".to_string());
        });
        bail_sync(|body| {
            let SNode::Stmts(susp) = &mut body[4] else {
                unreachable!()
            };
            susp.push(elided("Guard"));
        });
        // The loop-back must be a statement run of phi assigns.
        bail_sync(|body| {
            body[5] = SNode::Honest("h".to_string());
        });
        bail_sync(|body| {
            let SNode::Stmts(lb) = &mut body[5] else {
                unreachable!()
            };
            lb.push(expr_stmt(ident("x")));
        });
        // Positive: an elided ThrowIfNotObject guard rides the precall.
        let mut nodes = ys_sync_shape();
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.insert(3, elided("ThrowIfNotObject"));
        }
        assert!(ys_match_loop(&nodes[2], false).is_some());

        // ── async tail residuals ──
        fn bail_async(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_async_shape();
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            mutate(body);
            assert!(
                ys_match_loop(&nodes[2], true).is_none(),
                "near-miss matched"
            );
        }
        // The async skeleton is exactly [header, dispatch, precall,
        // await-dispatch].
        bail_async(|body| {
            body.push(run(vec![]));
        });
        // The precall tail must be the exact four-leaf shape.
        bail_async(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre.push(elided("Extra"));
        });
        // The call carries `this` and a temp argument.
        bail_async(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl("vres", 112, call0(tm("vm", 111)));
        });
        bail_async(|body| {
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(tm("vit", 102))),
                    args: vec![ident("not_a_temp")],
                    kind: CallKind::Dynamic,
                },
            );
        });
        // The continuation must open with the done run…
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            then[0] = SNode::Honest("h".to_string());
        });
        // … containing the done load…
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::Stmts(dr) = &mut then[0] else {
                unreachable!()
            };
            dr.remove(1);
        });
        // … and the done test must be an if.
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            then[1] = run(vec![]);
        });
        // The done arm's exit dispatch must be an if…
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            done[0] = run(vec![]);
        });
        // … testing the exit phi flag.
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { cond, .. } = &mut done[0] else {
                unreachable!()
            };
            *cond = cmp(CmpOp::Eq, tm("vexit", 110), undef());
        });
        // The normal arm opens with a run holding the value declare…
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { then: normal, .. } = &mut done[0] else {
                unreachable!()
            };
            normal[0] = SNode::Honest("h".to_string());
        });
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { then: normal, .. } = &mut done[0] else {
                unreachable!()
            };
            let SNode::Stmts(nr) = &mut normal[0] else {
                unreachable!()
            };
            nr[0] = expr_stmt(ident("x"));
        });
        // … and the return arm opens with a run.
        bail_async(|body| {
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { then: done, .. } = &mut then[1] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut done[0] else {
                unreachable!()
            };
            otherwise[0] = SNode::Honest("h".to_string());
        });
    }

    #[test]
    fn ys_async_yield_residual_pins() {
        fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
            let mut nodes = ys_async_shape();
            {
                let SNode::While { body, .. } = ys_while(&mut nodes) else {
                    unreachable!()
                };
                let SNode::If { then, .. } = &mut body[3] else {
                    unreachable!()
                };
                let SNode::If { otherwise, .. } = &mut then[1] else {
                    unreachable!()
                };
                mutate(otherwise);
            }
            assert!(
                ys_match_loop(&nodes[2], true).is_none(),
                "near-miss matched"
            );
        }
        // The head's four leaves are exactly [declare, declare, yield
        // expr, declare]…
        bail(|next| {
            let SNode::Stmts(head) = &mut next[0] else {
                unreachable!()
            };
            head[0] = expr_stmt(ident("x"));
        });
        // … then the mode dispatch is an if…
        bail(|next| {
            next[1] = run(vec![]);
        });
        // … the resumption pair is exactly two declares…
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(pair) = &mut then[0] else {
                unreachable!()
            };
            pair[0] = expr_stmt(ident("x"));
        });
        // … the NEXT test is an if…
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            then[1] = run(vec![]);
        });
        // … the RETURN await run keeps its four-leaf shape…
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            let SNode::Stmts(ar) = &mut then[2] else {
                unreachable!()
            };
            ar[0] = expr_stmt(ident("x"));
        });
        // … and the THROW test is an if.
        bail(|next| {
            let SNode::If { then, .. } = &mut next[1] else {
                unreachable!()
            };
            then[3] = run(vec![]);
        });
    }

    #[test]
    fn ys_unbound_and_prefixed_positives() {
        // The unbound form: the completion value unused → bare
        // `yield* src;`.
        let mut nodes = ys_sync_shape();
        let SNode::If { then, .. } = &mut nodes[3] else {
            unreachable!()
        };
        *then = vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])];
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(stats.yield_star_bound, 0);
        assert_eq!(
            nodes[0],
            run(vec![expr_stmt(Expr::YieldStar {
                value: bx(ident("src")),
            })])
        );
        // A setup prefix survives the fold, hoisted above the yield*.
        let mut nodes = ys_sync_shape();
        let SNode::Stmts(setup) = &mut nodes[0] else {
            unreachable!()
        };
        setup.insert(0, expr_stmt(call0(ident("warmup"))));
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(nodes[0], run(vec![expr_stmt(call0(ident("warmup")))]));
        // … and likewise through the fragments arrangement.
        let mut nodes = ys_sync_shape();
        let SNode::Stmts(setup) = &mut nodes[0] else {
            unreachable!()
        };
        setup.insert(0, expr_stmt(call0(ident("warmup"))));
        let mut nodes = vec![
            try_node(vec![nodes[0].clone(), nodes[1].clone()], vec![]),
            try_node(vec![nodes[2].clone()], vec![]),
            try_node(vec![nodes[3].clone()], vec![]),
        ];
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        let SNode::Try { body, .. } = &nodes[0] else {
            unreachable!()
        };
        assert_eq!(body.len(), 1, "the prefix replaced the setup run: {body:?}");
        // A temp delegate with an empty prefix stops the inline walk.
        let run0 = run(vec![
            decl(
                "vit0",
                200,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(tm("td", 205)),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]);
        let uses: BTreeMap<ValueId, usize> = [(ValueId::new(205), 1)].into_iter().collect();
        let (delegate, ..) = ys_match_setup(&run0, false, &uses).expect("temp delegate, no prefix");
        assert_eq!(delegate, tm("td", 205));
        // ys_match_exit: the return arm's run must be the load+return pair.
        let full = ys_sync_shape();
        let lp = ys_match_loop(&full[2], false).expect("loop");
        let res = ys_sync_res(&full[2]).unwrap();
        let bad = if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))])],
        );
        assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
        // ys_apply_fragments directly: the entry guards.
        let mut nodes = vec![SNode::Honest("h".to_string())];
        let uses = BTreeMap::new();
        let mut stats = FoldStats::default();
        assert!(!ys_apply_fragments(&mut nodes, 0, false, &uses, &mut stats));
        let mut nodes = vec![try_node(vec![], vec![])];
        assert!(!ys_apply_fragments(&mut nodes, 0, false, &uses, &mut stats));
        // The setup fragment must be a try.
        let mut full = vec![
            try_node(
                vec![
                    ys_setup_init(false)[0].clone(),
                    ys_setup_init(false)[1].clone(),
                ],
                vec![],
            ),
            try_node(vec![ys_sync_shape()[2].clone()], vec![]),
            try_node(vec![ys_sync_shape()[3].clone()], vec![]),
        ];
        full[0] = SNode::Honest("h".to_string());
        assert!(!ys_apply_fragments(&mut full, 1, false, &uses, &mut stats));
        // The exit fragment's innermost body must hold a significant
        // node.
        let mut full = vec![
            try_node(
                vec![
                    ys_setup_init(false)[0].clone(),
                    ys_setup_init(false)[1].clone(),
                ],
                vec![],
            ),
            try_node(vec![ys_sync_shape()[2].clone()], vec![]),
            try_node(vec![SNode::Honest("h".to_string())], vec![]),
        ];
        assert!(!ys_apply_fragments(&mut full, 1, false, &uses, &mut stats));
    }

    #[test]
    fn single_pass_residual_pins() {
        // A pre-run holding ONLY the wiring assign is consumed whole.
        let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.remove(0); // drop the setup call; only the assign remains
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_in, 1);
        assert_eq!(nodes.len(), 1, "the emptied run is removed: {nodes:?}");
        // The nearest previous non-Honest node must be a statement run.
        let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
        nodes[0] = SNode::Break { label: None };
        assert!(match_single_pass_for_in(&nodes, 1).is_none());
        // Honest markers between the assign run and the header are
        // skipped by the backward scan.
        let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
        nodes.insert(1, SNode::Honest("dissolved".to_string()));
        assert!(match_single_pass_for_in(&nodes, 2).is_some());
    }

    #[test]
    fn agen_residual_pins() {
        // The phi-partition skip between the pair run and the dispatch.
        let mut nodes = agen_body();
        let SNode::If { otherwise, .. } = &mut nodes[2] else {
            unreachable!()
        };
        otherwise.insert(2, run(vec![phi_assign("pp3", ident("z"))]));
        let mut cx = agen_cx(&nodes);
        assert!(match_ag_yield(&nodes, 1, &mut cx).is_some());
        // agen_entry_elide: the if arm's otherwise side recurses too.
        for wrap in [
            |site: Vec<SNode>| vec![if_node(ident("c"), vec![], site)],
            |site: Vec<SNode>| {
                vec![SNode::DoWhile {
                    label: None,
                    body: site,
                    cond: ident("d"),
                }]
            },
        ] {
            let mut nodes = wrap(vec![run(vec![
                decl(
                    "g",
                    20,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
            ])]);
            let mut stats = FoldStats::default();
            async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
            assert_eq!(stats.agen_entry, 1);
        }
    }

    #[test]
    fn machine_fold_seq_region_wraps() {
        // The *_seq recursion arms for While/DoWhile/Labeled (the
        // If/Try wraps live in machine_folds_recurse_into_regions).
        for wrap in [
            |site: Vec<SNode>| {
                vec![SNode::While {
                    label: None,
                    cond: Some(ident("c")),
                    body: site,
                }]
            },
            |site: Vec<SNode>| {
                vec![SNode::DoWhile {
                    label: None,
                    body: site,
                    cond: ident("d"),
                }]
            },
            |site: Vec<SNode>| {
                vec![SNode::Labeled {
                    label: "l".to_string(),
                    body: site,
                }]
            },
        ] {
            let mut nodes = wrap(ys_sync_shape());
            let mut stats = FoldStats::default();
            yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
            assert_eq!(stats.yield_star_sites, 1, "wrapped yield* site");
            let mut nodes = wrap(agen_body());
            let mut stats = FoldStats::default();
            async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
            assert_eq!(stats.agen_yields, 1, "wrapped agen yield site");
        }
        // A stray Honest sibling exercises the scan's no-op arm.
        let mut nodes = vec![
            SNode::Honest("stray".to_string()),
            try_node(
                vec![run(vec![
                    decl(
                        "g",
                        20,
                        Expr::CreateGenerator {
                            func: bx(closure("f")),
                        },
                    ),
                    expr_stmt(Expr::Yield { value: bx(undef()) }),
                ])],
                vec![],
            ),
        ];
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 1);
    }

    #[test]
    fn final_residual_pins() {
        // ys_match_loop: the NEXT arm must hold at least one
        // significant node.
        let mut nodes = ys_sync_shape();
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut body[1] else {
                unreachable!()
            };
            otherwise.clear();
        }
        assert!(ys_match_loop(&nodes[2], false).is_none());
        // … and its first significant node must be the assign run.
        let mut nodes = ys_sync_shape();
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut body[1] else {
                unreachable!()
            };
            otherwise[0] = run(vec![exc_assign("vx", ident("z"))]);
        }
        assert!(ys_match_loop(&nodes[2], false).is_none());
        // The sync/async call's `this` must be a TEMP (not just
        // present).
        for async_ in [false, true] {
            let mut nodes = if async_ {
                ys_async_shape()
            } else {
                ys_sync_shape()
            };
            {
                let SNode::While { body, .. } = ys_while(&mut nodes) else {
                    unreachable!()
                };
                let SNode::Stmts(pre) = &mut body[2] else {
                    unreachable!()
                };
                pre[2] = decl(
                    "vres",
                    112,
                    Expr::Call {
                        callee: bx(tm("vm", 111)),
                        this: Some(bx(ident("not_a_temp"))),
                        args: vec![tm("vrv", 101)],
                        kind: CallKind::Dynamic,
                    },
                );
            }
            assert!(ys_match_loop(&nodes[2], async_).is_none());
        }
        // ys_apply_bare (async): a setup prefix is re-homed above the
        // yield* statement.
        let mut nodes = ys_async_shape();
        {
            let SNode::Stmts(setup) = &mut nodes[0] else {
                unreachable!()
            };
            setup.insert(0, expr_stmt(call0(ident("warmup"))));
        }
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1);
        assert_eq!(nodes[0], run(vec![expr_stmt(call0(ident("warmup")))]));
        // ag_mode_test: the istrue wrapper keeps polarity.
        let body = agen_body();
        let (.., pos) = ag_mode_test(
            &istrue(cmp(CmpOp::Eq, tm("my", 34), num(2.0))),
            Some(ValueId::new(34)),
            &mut agen_cx(&body),
        )
        .unwrap();
        assert!(pos);
        // match_ag_three_way: a foreign run before the next test bails
        // the descent.
        let bad = if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
            vec![
                run(vec![decl(
                    "a2",
                    35,
                    Expr::Await {
                        value: bx(tm("ry", 33)),
                        uncaught: true,
                    },
                )]),
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]),
            ],
            vec![
                run(vec![expr_stmt(ident("junk"))]),
                if_node(
                    cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                    vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                    vec![run(vec![expr_stmt(ident("next_cont"))])],
                ),
            ],
        );
        assert!(
            match_ag_three_way(
                &bad,
                Some(ValueId::new(34)),
                ValueId::new(33),
                &mut agen_cx(&body)
            )
            .is_none()
        );
        // … and a pure-const run before it is skipped.
        let good = if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
            vec![
                run(vec![decl(
                    "a2",
                    35,
                    Expr::Await {
                        value: bx(tm("ry", 33)),
                        uncaught: true,
                    },
                )]),
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]),
            ],
            vec![
                run(vec![decl("c1", 90, num(1.0))]),
                if_node(
                    cmp(CmpOp::Eq, tm("my", 34), tm("c1", 90)),
                    vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                    vec![run(vec![expr_stmt(ident("next_cont"))])],
                ),
            ],
        );
        let mut cx = agen_cx(&body);
        cx.const_env.insert(ValueId::new(90), 1.0f64.to_bits());
        assert!(
            match_ag_three_way(&good, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_some()
        );
        // sweep_async_machinery: a non-alias temp value passes the walk;
        // a foreign assign survives the strip and keeps the decl census.
        let mut nodes = vec![run(vec![
            phi_decl("pa", 20),
            phi_assign("pa", tm("g", 10)),
            phi_assign("other", tm("q", 77)),
        ])];
        let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
        sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
        let SNode::Stmts(got) = &nodes[0] else {
            unreachable!()
        };
        assert!(
            got.iter().any(
                |l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "other")
            ),
            "the foreign assign survives: {got:?}"
        );
        assert!(
            !got.iter()
                .any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "pa"))
        );
        // match_ag_await: phi-partition runs at the continuation head
        // are skipped by the yield-point guard.
        let guard_body = vec![
            run(vec![
                decl(
                    "a",
                    30,
                    Expr::Await {
                        value: bx(ident("v")),
                        uncaught: true,
                    },
                ),
                expr_stmt(Expr::Yield {
                    value: bx(tm("a", 30)),
                }),
            ]),
            if_node(
                cmp(
                    CmpOp::Eq,
                    Expr::GeneratorDriver {
                        resume: false,
                        genobj: bx(tm("g", 20)),
                    },
                    num(1.0),
                ),
                vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                }))])],
                vec![
                    run(vec![phi_assign("pp", ident("z"))]),
                    run(vec![expr_stmt(ident("cont"))]),
                ],
            ),
        ];
        let mut cx = agen_cx(&guard_body);
        assert!(match_ag_await(&guard_body, 0, &mut cx).is_some());
        // agen_fold_run: nothing before the resume decl.
        let mut leaves = vec![
            decl(
                "r",
                41,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                },
            ),
            Leaf::Raw(Stmt::Return(Some(tm("r", 41)))),
        ];
        let mut stats = FoldStats::default();
        agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
        assert_eq!(stats.agen_returns, 0);
        // absorb_one: a non-own index store on the object is no entry.
        assert!(
            absorb_one(
                &Leaf::Raw(Stmt::StoreIndex {
                    object: tm("o", 10),
                    index: num(0.0),
                    value: ident("v"),
                    own: false,
                }),
                ValueId::new(10),
                false,
                &[],
                0,
            )
            .is_none()
        );
        // key_load_target: a PropIndex with a non-literal index is no
        // key load.
        assert_eq!(
            key_load_target(
                &Expr::PropIndex {
                    object: bx(ident("o")),
                    index: bx(ident("k")),
                },
                &ident("o"),
            ),
            None
        );
    }

    #[test]
    fn strip_internal_phi_plumbing_recursion() {
        // Copy plumbing nested inside every region kind is stripped.
        let mut roots: BTreeMap<String, Expr> = BTreeMap::new();
        roots.insert("ip".to_string(), tm("ip", 60));
        let plumbing = || {
            vec![run(vec![
                phi_decl("cp", 40),
                phi_assign("cp", tm("ip", 60)),
                phi_assign("ip", tm("ip", 60)),
            ])]
        };
        let mut out = vec![
            if_node(ident("c"), plumbing(), plumbing()),
            SNode::While {
                label: None,
                cond: None,
                body: plumbing(),
            },
            SNode::DoWhile {
                label: None,
                body: plumbing(),
                cond: ident("d"),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: plumbing(),
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: plumbing(),
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: plumbing(),
            },
            SNode::Try {
                body: plumbing(),
                catches: vec![catch("e", plumbing())],
                note: None,
                finally: Some(plumbing()),
            },
            SNode::Switch {
                disc: ident("s"),
                cases: vec![SwitchCase {
                    tests: vec![],
                    body: plumbing(),
                }],
            },
            plumbing()[0].clone(),
            SNode::Honest("h".to_string()),
        ];
        elim_internal_copy_phis(&mut out, &roots);
        // Every copy phi and self-assign vanished, leaving empty
        // regions behind.
        let mut assigns = 0usize;
        walk_leaves(&out, &mut |l| {
            if matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })) {
                assigns += 1;
            }
            if matches!(l, Leaf::Raw(Stmt::PhiDecl { .. })) {
                assigns += 1;
            }
        });
        assert_eq!(assigns, 0, "{out:?}");
    }

    #[test]
    fn last_residual_pins() {
        // The driver pre-run walks stop at a non-run, non-comment
        // sibling.
        let mut nodes = driver_shape();
        nodes.insert(0, SNode::Break { label: None });
        // (the While now sits at index 2; match directly)
        assert!(match_for_await_driver(&nodes, 2).is_some());
        let mut stats = FoldStats::default();
        fold(&mut nodes, &mut stats);
        assert_eq!(stats.for_await_of, 1);
        assert!(matches!(&nodes[0], SNode::Break { .. }), "{nodes:?}");
        // match_switch_chain: a loop break inside the trailing-else
        // (default) arm refuses the fold.
        let bad = if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
            vec![run(vec![expr_stmt(call0(ident("a")))])],
            vec![SNode::Break { label: None }],
        );
        assert!(match_switch_chain(&bad).is_none());
    }
}
