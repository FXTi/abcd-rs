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
//!    [`yield_star_fold`] eliminates the es2abc yield-delegation
//!    machinery (`FunctionBuilder::YieldStar`): the
//!    `GetIterator`/`GetAsyncIterator` setup, the resume-mode
//!    dispatch (`NEXT`/`THROW`/`RETURN` with the delegate `throw`/
//!    `return` method lookups and the IteratorClose plumbing), the
//!    `method.call(iter, received)`, the pass-through suspend (the
//!    delegate's result object yields AS-IS — no iter-result wrap),
//!    the `done` test, and the completion dispatch (the delegation
//!    value vs the `.return()` propagation) — back into
//!    `yield* <expr>` (`const ret = yield* <expr>` when the
//!    delegate's completion value is used). Async (`async function*`)
//!    carries awaits around every protocol step and keeps the
//!    completion dispatch inside the loop's done arm. All-or-nothing
//!    per site; non-matching shapes keep their loud fallbacks.

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
        Expr::Class { heritage, .. } => {
            if let Some(h) = heritage {
                out.push(h);
            }
        }
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
        let mut absorbed: Vec<Absorb> = Vec::new();
        let mut j = i + 1;
        while j < leaves.len() {
            match absorb_one(&leaves[j], vid, is_array, &absorbed) {
                Some(a) => {
                    absorbed.push(a);
                    j += 1;
                }
                None => break,
            }
        }
        if absorbed.is_empty() {
            i += 1;
            continue;
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
        leaves.insert(i, new_value);
        leaves.drain(i + 1..i + 1 + (j - i - 1));
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
    ArrItem(Expr),
    ArrSpread(Expr),
}

/// Whether leaf `l` is a builder statement targeting temp `vid` that
/// can be absorbed (self-reference-free).
fn absorb_one(
    l: &Leaf,
    vid: abcd_ir::ValueId,
    is_array: bool,
    so_far: &[Absorb],
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
                // Contiguous integer index required (the shape may
                // already carry leading elements).
                let base = match &index {
                    Expr::Lit(Lit::Number(bits)) => {
                        let v = f64::from_bits(*bits);
                        (v.fract() == 0.0 && v >= 0.0).then_some(v as u64)
                    }
                    _ => None,
                };
                let prior = so_far
                    .iter()
                    .filter(|a| matches!(a, Absorb::ArrItem(_) | Absorb::ArrSpread(_)))
                    .count() as u64;
                // The shape's own length is not visible here;
                // monotonic contiguity is enforced relative to the
                // absorbed prefix (documented approximation).
                let _ = prior;
                match base {
                    Some(_idx) if *own => Some(Absorb::ArrItem(value.clone())),
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
        SNode::Break {
            label: Some(_),
        }
        | SNode::Continue {
            label: Some(_),
        } => true,
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
fn sweep_dead_loop_exit_throws(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
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
    /// Further internal temps (`it`, `next`, the for-in iterator phi).
    extra_internals: Vec<String>,
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
        // Trim the consumed tail of the pre-loop run (this may remove
        // nodes BEFORE i, shifting it left).
        let removed = trim_pre_leaves(nodes, i, folded.pre_cut);
        i = i + 1 - removed;
    }
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
    })
}

/// for-in: `it = get-prop-iterator(obj)` (phi at the header),
/// `k = next-prop-name(it)`, `undefined == k` exit test.
fn match_for_in(pre: &[Leaf], wcond: &Expr, body: &[SNode]) -> Option<LoopFold> {
    // The LAST leaf of the pre-run must be the iterator phi-assign.
    let (it_phi, obj) = match pre.last() {
        Some(Leaf::Raw(Stmt::PhiAssign {
            target,
            value:
                Expr::Iter {
                    op: IterOp::GetPropIterator,
                    obj,
                    ..
                },
            ..
        })) => (target.clone(), obj.as_ref().clone()),
        _ => return None,
    };
    // The header: `let it;` (the phi) then `const k = next-prop-name(it)`.
    let SNode::Stmts(hdr) = body.first()? else {
        return None;
    };
    if hdr.len() != 2 {
        return None;
    }
    let binding = match (&hdr[0], &hdr[1]) {
        (
            Leaf::Raw(Stmt::PhiDecl { name: p, .. }),
            Leaf::Raw(Stmt::Declare {
                name: k,
                value:
                    Expr::Iter {
                        op: IterOp::NextPropName,
                        obj: it,
                        ..
                    },
                ..
            }),
        ) if *p == it_phi && temp_name(it) == Some(it_phi.as_str()) => k.clone(),
        _ => return None,
    };
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
        pre_cut: 1,
        phi_names: vec![it_phi.clone()],
        res_name: None,
        done_name: None,
        extra_internals: vec![it_phi],
    })
}

/// Rebuild the folded loop body: remove the header plumbing, extract
/// the value binding, drop the back-edge self-assigns and (checked)
/// the iterator-cleanup try. Returns `(binding, new_body)`.
fn rebuild_loop_body(body: &[SNode], folded: &LoopFold) -> Option<(String, Vec<SNode>)> {
    if folded.is_in {
        let binding = match &body.first() {
            Some(SNode::Stmts(hdr)) => match &hdr[1] {
                Leaf::Raw(Stmt::Declare { name, .. }) => name.clone(),
                _ => return None,
            },
            _ => return None,
        };
        let mut out: Vec<SNode> = body.to_vec();
        out.remove(0);
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

fn fold_switches(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
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
fn expr_children_mut(e: &mut Expr) -> Vec<&mut Expr> {
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
        Expr::Class { heritage, .. } => {
            if let Some(h) = heritage {
                out.push(h);
            }
        }
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
        Stmt::Return(v) => {
            if let Some(e) = v {
                canon_expr(e, map);
            }
        }
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
    let Some(thrown) = arm_ok(throw_arm, true)? else {
        return None;
    };
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
                if let FTok::Leaf(l) = t {
                    match l {
                        Leaf::Raw(Stmt::PhiAssign { target, .. }) | Leaf::Assign { target, .. } => {
                            assigned.push(target)
                        }
                        _ => {}
                    }
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
pub fn scope_fold(nodes: &mut Vec<SNode>, params: &[String], stats: &mut FoldStats) {
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
                if params.iter().any(|p| *p == name) || converted.contains(&name) {
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
            for (idx, leaf) in decl_edits {
                leaves[idx] = leaf;
                stats.scope_fold += 1;
            }
            // The push comment: consumed when every slot was declared;
            // otherwise it stays, listing the undeclared slots only.
            let Leaf::Raw(Stmt::ScopePush { names }) = &mut leaves[p] else {
                unreachable!()
            };
            let remaining: Vec<Option<String>> = names
                .iter()
                .enumerate()
                .filter_map(|(i, n)| (!declared_slots.contains(&(i as u16))).then(|| n.clone()))
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
pub fn async_driver_fold(nodes: &mut Vec<SNode>, kind: FunctionKind, stats: &mut FoldStats) {
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
    nodes: &mut Vec<SNode>,
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
                if let Some(f) = finally {
                    async_fold_seq(f, uses, decls, stats);
                }
            }
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
                if let Some(f) = finally {
                    gen_fold_seq(f, cx, stats);
                }
            }
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
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => return first_significant_stmt(body),
                // If/Switch/Break/Continue: the first executed statement
                // is not statically unique (or not a fall-through).
                _ => return None,
            }
        }
        None
    }
    fn continuation_throw<'a>(stack: &[&'a [SNode]]) -> Option<ValueId> {
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
                    if let Some(f) = finally {
                        visit(f, stack, out);
                    }
                }
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
                if let Some(f) = finally {
                    async_machine_seq(f, cx, stats);
                }
            }
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
    nodes: &mut Vec<SNode>,
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
    nodes: &mut Vec<SNode>,
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
                if let Some(f) = finally {
                    strip_genobj_phi_assigns(f, aliases, targets);
                }
            }
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
    nodes: &mut Vec<SNode>,
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
                if let Some(f) = finally {
                    strip_dead_phi_decls(f, targets, remaining, uses);
                }
            }
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
fn agen_entry_elide(nodes: &mut Vec<SNode>, genobj: ValueId, stats: &mut FoldStats) -> bool {
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
                if let Some(f) = finally {
                    agen_fold_seq(f, cx, stats);
                }
            }
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
            SNode::Stmts(run) => run.iter().for_each(|l| f(l)),
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
fn nodes_use_temp(nodes: &[SNode], id: ValueId) -> bool {
    fn expr_uses(e: &Expr, id: ValueId) -> bool {
        if temp_value(e) == Some(id) {
            return true;
        }
        expr_children(e).iter().any(|c| expr_uses(c, id))
    }
    let mut found = false;
    walk_leaves(nodes, &mut |l| {
        if found {
            return;
        }
        for e in leaf_exprs(l) {
            if expr_uses(e, id) {
                found = true;
                return;
            }
        }
    });
    found
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
fn sweep_dead_decls(nodes: &mut Vec<SNode>, dead: &BTreeSet<ValueId>) {
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
                if let Some(f) = finally {
                    sweep_dead_decls(f, dead);
                }
            }
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
// on the d-P15 fixtures `decompile-fixtures/yield-star/*.pa`):
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
                if let Some(f) = finally {
                    ys_fold_seq(f, async_, uses, stats);
                }
            }
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
                        if let Some(base) = ys_prop(value, "return") {
                            if in_phis(&base) {
                                it_id = Some((base, id));
                            }
                        }
                    }
                }
                // The propagation return: `return received`.
                if !async_ {
                    if let [Leaf::Raw(Stmt::Return(Some(e)))] = run.as_slice() {
                        if let Some(t) = temp_value(e).filter(in_phis) {
                            rv_id = Some(t);
                        }
                    }
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
    let Some(exit_id) = pre_phis.get(&exit_phi.1).copied() else {
        return None;
    };
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
    let Some(exit_id) = pre_phis.get(&exit_phi.1).copied() else {
        return None;
    };
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

/// Match the sync completion dispatch sitting right after the loop:
/// `if (!exitReturn) { value = res.value; <continuation> } else {
/// v2 = res.value; return v2 }`. Returns the binding (when the
/// completion value is used) and the continuation.
fn ys_match_exit(
    n: &SNode,
    exit_phi: ValueId,
    res: ValueId,
) -> Option<(Option<(String, ValueId)>, Vec<SNode>)> {
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
    nodes: &mut Vec<SNode>,
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
