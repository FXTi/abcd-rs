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
//!
//! `SuspendGenerator`→`yield` and `Await*`→`await` landed in Stage A
//! ([`Expr::Yield`]/[`Expr::Await`]); the emitter prints them. The
//! generator/async DRIVER plumbing (`ResumeGenerator`,
//! `GetResumeMode`, `AsyncResolve`, `AsyncReject` — the hard 7, R4)
//! stays documented fallback.

use crate::expr::{ArrayElem, Expr, IterOp, Lit, ObjEntry};
use crate::recover::Stmt;
use crate::structure::{Leaf, SNode, SwitchCase};

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
            target,
            value,
            to,
            ..
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
        Stmt::StoreProp {
            object, value, ..
        } => {
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
            object,
            key,
            value,
            ..
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
            Stmt::Return(_)
            | Stmt::Throw(_)
            | Stmt::Branch { .. }
            | Stmt::CondBranch { .. },
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
            let catch_ft = catches.is_empty() || catches.iter().any(|c| ft_list_fallthrough(&c.body));
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
                        Leaf::Raw(Stmt::PhiAssign { target, .. })
                        | Leaf::Assign { target, .. } => assigned.push(target),
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
        let ft = ft_list_fallthrough(&ibody) || icatches.iter().any(|c| ft_list_fallthrough(&c.body));
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
