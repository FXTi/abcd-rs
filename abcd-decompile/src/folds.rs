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
//!    entry protocol; `AsyncGenerator` kinds bail (their
//!    `CreateGeneratorObj`/`AsyncGeneratorResolve` lowering is a
//!    separate, still-documented fallback).

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
        Expr::Yield { value } | Expr::Await { value, .. } => out.push(value),
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
        Expr::Yield { value } | Expr::Await { value, .. } => out.push(value),
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
    async_fold_seq(nodes, &uses, stats);
}

fn async_fold_seq(nodes: &mut Vec<SNode>, uses: &BTreeMap<ValueId, usize>, stats: &mut FoldStats) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => fold_async_run(run, uses, stats),
            SNode::If {
                then, otherwise, ..
            } => {
                async_fold_seq(then, uses, stats);
                async_fold_seq(otherwise, uses, stats);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => async_fold_seq(body, uses, stats),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                async_fold_seq(body, uses, stats);
                for c in catches {
                    async_fold_seq(&mut c.body, uses, stats);
                }
                if let Some(f) = finally {
                    async_fold_seq(f, uses, stats);
                }
            }
            SNode::Switch { cases, .. } => {
                for c in cases {
                    async_fold_seq(&mut c.body, uses, stats);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

/// One leaf run: fold adjacent AsyncDriver declares into their
/// return/throw consumer.
fn fold_async_run(run: &mut Vec<Leaf>, uses: &BTreeMap<ValueId, usize>, stats: &mut FoldStats) {
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
            if adjacent_return && uses.get(&vid).copied().unwrap_or(0) == 1 {
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
// `AsyncGeneratorResolve` machinery — a separate lowering) and bails
// at the gate by construction.

/// Fold context for one async function body.
struct AsyncMachineCx {
    /// The unique `AsyncFunctionEnter` fallback temp (the funcObj).
    genobj: ValueId,
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
/// `await` control flow. No-op for non-async kinds; the async-generator
/// kind bails at the entry gate (no `AsyncFunctionEnter`).
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
    // Every visible use of the funcObj must be machinery: a
    // `GeneratorDriver` genobj operand, or a catch-region context phi
    // assign (`phi = funcobj` — the es2abc try-region bookkeeping the
    // rethrow-only handler never reads). Any other use is not the
    // vendor shape — bail, keeping everything loud.
    if !funcobj_uses_are_machinery(nodes, genobj) {
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
    let mut cx = AsyncMachineCx {
        genobj,
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
    sweep_async_machinery(nodes, genobj, &cx.consumed_consts);
}

/// The entry-gate check: every occurrence of the funcObj temp is a
/// `GeneratorDriver` genobj operand or a phi assign of the temp.
fn funcobj_uses_are_machinery(nodes: &[SNode], genobj: ValueId) -> bool {
    /// `in_genobj_slot` marks the `GeneratorDriver::genobj` operand
    /// position (the only legal expression use of the temp).
    fn expr_ok(e: &Expr, genobj: ValueId, in_genobj_slot: bool) -> bool {
        if temp_value(e) == Some(genobj) {
            return in_genobj_slot;
        }
        match e {
            Expr::GeneratorDriver { genobj: g, .. } => expr_ok(g, genobj, true),
            _ => expr_children(e)
                .iter()
                .all(|c| expr_ok(c, genobj, false)),
        }
    }
    let mut ok = true;
    walk_leaves(nodes, &mut |l| {
        if !ok {
            return;
        }
        if let Leaf::Raw(Stmt::PhiAssign { value, .. }) = l {
            // `phi = funcobj` (the catch-region context phi) is
            // machinery bookkeeping; anything richer is not.
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
            }) if temp_value(mg) == Some(cx.genobj) => {
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
            }) if temp_value(rg) == Some(cx.genobj) => {
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
                value: Expr::Await {
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
    let genobj = cx.genobj;
    let is_mode = |e: &Expr| match mode {
        // Declared mode temp: the condition must reference it.
        Some(md) => temp_value(e) == Some(md),
        // Inlined `GetResumeMode` directly in the condition.
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
    // The ASYNC `HandleCompletion` tests THROW(1) only.
    if f64::from_bits(bits) != 1.0 {
        return None;
    }
    let (throw_arm, cont) = if positive {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    check_async_throw_arm(throw_arm, resume, genobj)?;
    Some(cont.clone())
}

/// The THROW arm: exactly `throw <resume>;` (+ the dead `Unreachable`,
/// any dead loop-bookkeeping `break`s, and any phi-partition runs — the
/// es2abc try-region bookkeeping assigns, which the parent block's own
/// assigns replicate for the folded await's throw), where `<resume>` is
/// the matched resume temp — or the inlined `ResumeGenerator` when the
/// result was never declared.
fn check_async_throw_arm(arm: &[SNode], resume: Option<ValueId>, genobj: ValueId) -> Option<()> {
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
                                } if temp_value(rg) == Some(genobj)
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
fn sweep_async_machinery(nodes: &mut Vec<SNode>, genobj: ValueId, consumed: &BTreeSet<ValueId>) {
    let mut uses: BTreeMap<ValueId, usize> = BTreeMap::new();
    count_temp_uses(nodes, &mut uses);
    // Phi temps by name (PhiAssign targets are name-linked).
    let mut phi_ids: BTreeMap<String, ValueId> = BTreeMap::new();
    walk_leaves(nodes, &mut |l| {
        if let Leaf::Raw(Stmt::PhiDecl { name, value_id }) = l {
            phi_ids.insert(name.clone(), *value_id);
        }
    });
    let mut phi_targets: BTreeSet<String> = BTreeSet::new();
    let mut funcobj_survives = false;
    walk_leaves(nodes, &mut |l| {
        if funcobj_survives {
            return;
        }
        if let Leaf::Raw(Stmt::PhiAssign { target, value, .. }) = l
            && temp_value(value) == Some(genobj)
        {
            let dead = phi_ids
                .get(target)
                .is_some_and(|vid| uses.get(vid).copied().unwrap_or(0) == 0);
            if dead {
                phi_targets.insert(target.clone());
            } else {
                funcobj_survives = true;
            }
            return;
        }
        for e in leaf_exprs(l) {
            if expr_uses_value(e, genobj) {
                funcobj_survives = true;
                return;
            }
        }
    });
    let mut dead: BTreeSet<ValueId> = consumed
        .iter()
        .copied()
        .filter(|v| uses.get(v).copied().unwrap_or(0) == 0)
        .collect();
    if !funcobj_survives {
        dead.insert(genobj);
        if !phi_targets.is_empty() {
            // Remove the `phi = funcobj` assigns, then the phi decls
            // left assign-less (and unread).
            strip_genobj_phi_assigns(nodes, genobj, &phi_targets);
            let mut remaining: BTreeSet<String> = BTreeSet::new();
            walk_leaves(nodes, &mut |l| {
                if let Leaf::Raw(Stmt::PhiAssign { target, .. }) = l {
                    remaining.insert(target.clone());
                }
            });
            strip_dead_phi_decls(nodes, &phi_targets, &remaining, &uses);
        }
    }
    if !dead.is_empty() {
        sweep_dead_decls(nodes, &dead);
    }
}

/// Remove `PhiAssign` leaves assigning the funcObj temp to one of the
/// dead phi targets.
fn strip_genobj_phi_assigns(nodes: &mut Vec<SNode>, genobj: ValueId, targets: &BTreeSet<String>) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(run) => run.retain(|l| {
                !matches!(
                    l,
                    Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                        if targets.contains(target) && temp_value(value) == Some(genobj)
                )
            }),
            SNode::If {
                then, otherwise, ..
            } => {
                strip_genobj_phi_assigns(then, genobj, targets);
                strip_genobj_phi_assigns(otherwise, genobj, targets);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => strip_genobj_phi_assigns(body, genobj, targets),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                strip_genobj_phi_assigns(body, genobj, targets);
                for c in catches {
                    strip_genobj_phi_assigns(&mut c.body, genobj, targets);
                }
                if let Some(f) = finally {
                    strip_genobj_phi_assigns(f, genobj, targets);
                }
            }
            SNode::Switch { cases, .. } => {
                for c in cases {
                    strip_genobj_phi_assigns(&mut c.body, genobj, targets);
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
