//! Callee-name resolution through the global-load def chain — the
//! matcher that makes summaries and sinks work when the call graph says
//! `UnknownCallees` (corpus reality: ~97% of call sites load their
//! callee via `TryGetGlobal`, mutable across scripts, so the edge is
//! never resolved — but the NAME is static).
//!
//! A call `print(x)` lifts to `%f = TryGetGlobal("print"); call %f`.
//! The callee value's def chain statically carries the global's name, so
//! name-keyed summaries/sinks fire independently of call-graph
//! resolution. Qualified names are built through property loads:
//! `console.log(x)` lifts to `%g = TryGetGlobal("console"); %f =
//! LoadProp(%g, "log"); call %f` → candidate `"console.log"`.
//!
//! Candidates are returned most-qualified first. Bare property names
//! (`"log"` alone) are deliberately NOT emitted: a bare-method registry
//! key would collide across every object with a same-named method.
//! Resolved-callee [`FunctionData`] names are matched by the driver on
//! top of these candidates (directly-resolved internal functions).

use abcd_ir::{Const, Module, Op, Sym, ValueDef, ValueId};

/// All candidate names for a callee value, most-qualified first, in
/// deterministic def-chain order. Recursion is cycle-guarded.
pub fn callee_name_candidates(module: &Module, callee: ValueId) -> Vec<String> {
    let mut out = Vec::new();
    let mut visiting = std::collections::HashSet::new();
    resolve_into(module, callee, &mut visiting, &mut out);
    out
}

/// The recursive worker.
fn resolve_into(
    module: &Module,
    value: ValueId,
    visiting: &mut std::collections::HashSet<ValueId>,
    out: &mut Vec<String>,
) {
    if !visiting.insert(value) {
        return;
    }
    let Some(v) = module.value(value) else {
        return;
    };
    match v.def {
        ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => resolve_into(module, *src, visiting, out),
            Some(Op::Phi { entries }) => {
                for (_, incoming) in entries {
                    resolve_into(module, *incoming, visiting, out);
                }
            }
            Some(Op::TryGetGlobal { name, .. }) => {
                if let Some(s) = module.sym.resolve(*name) {
                    push_unique(out, s.to_owned());
                }
            }
            Some(Op::LoadProp { object, name }) => {
                // Qualified names through the receiver chain:
                // `TryGetGlobal("console").log` → "console.log".
                if let Some(leaf) = module.sym.resolve(*name) {
                    let mut prefix = Vec::new();
                    resolve_into(module, *object, visiting, &mut prefix);
                    for base in &prefix {
                        push_unique(out, format!("{base}.{leaf}"));
                    }
                }
            }
            Some(Op::LoadConst(c)) => {
                if let Some(Const::MethodRef(f)) = module.consts.get(*c) {
                    if let Some(fd) = module.func(*f) {
                        if let Some(s) = module.sym.resolve(fd.name) {
                            push_unique(out, s.to_owned());
                        }
                    }
                }
            }
            Some(Op::DefineFunc { body, .. }) => {
                if let Some(fd) = module.func(*body) {
                    if let Some(s) = module.sym.resolve(fd.name) {
                        push_unique(out, s.to_owned());
                    }
                }
            }
            Some(Op::AllocClosure { func }) | Some(Op::CreateGenerator { func }) => {
                resolve_into(module, *func, visiting, out)
            }
            _ => {}
        },
        _ => {}
    }
}

fn push_unique(out: &mut Vec<String>, s: String) {
    if !s.is_empty() && !out.contains(&s) {
        out.push(s);
    }
}

/// The base (receiver) value of a call: the explicit `this`, or — for
/// the `obj.m()` shape where `Dynamic` calls carry no `this` — the
/// object of the `LoadProp` that produced the callee value.
pub fn call_base_value(module: &Module, call: &abcd_ir::Inst) -> Option<ValueId> {
    let Op::Call { callee, this, .. } = &call.op else {
        return None;
    };
    if let Some(t) = this {
        return Some(*t);
    }
    let mut visiting = std::collections::HashSet::new();
    base_through_movs(module, *callee, &mut visiting)
}

fn base_through_movs(
    module: &Module,
    value: ValueId,
    visiting: &mut std::collections::HashSet<ValueId>,
) -> Option<ValueId> {
    if !visiting.insert(value) {
        return None;
    }
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::Mov { src } => base_through_movs(module, *src, visiting),
        // Loop rotation: the callee phi merges the pre-loop LoadProp
        // with the phi itself; every entry reaches the same LoadProp
        // in that shape (first-found is exact there, may otherwise).
        Op::Phi { entries } => entries
            .iter()
            .find_map(|(_, incoming)| base_through_movs(module, *incoming, visiting)),
        Op::LoadProp { object, .. } => Some(*object),
        _ => None,
    }
}

/// The method leaf of a call whose callee came through a `LoadProp`
/// chain: `a.pop(...)` → `"pop"`. This is the key the prototype
/// resolution path (t-P3, `crate::prototype`) qualifies with the
/// receiver's family — `TryGetGlobal("a").pop` + receiver family
/// `Array` ⇒ candidate `Array.prototype.pop`. Returns `None` when the
/// callee is not a property load (bare global calls, direct calls).
pub fn call_method_leaf(module: &Module, call: &abcd_ir::Inst) -> Option<Sym> {
    let Op::Call { callee, .. } = &call.op else {
        return None;
    };
    let mut visiting = std::collections::HashSet::new();
    leaf_through_movs(module, *callee, &mut visiting)
}

fn leaf_through_movs(
    module: &Module,
    value: ValueId,
    visiting: &mut std::collections::HashSet<ValueId>,
) -> Option<Sym> {
    if !visiting.insert(value) {
        return None;
    }
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::Mov { src } => leaf_through_movs(module, *src, visiting),
        // Loop-rotated method calls: the callee phi merges the
        // pre-loop LoadProp with the phi itself (for-of's `next`).
        Op::Phi { entries } => entries
            .iter()
            .find_map(|(_, incoming)| leaf_through_movs(module, *incoming, visiting)),
        Op::LoadProp { name, .. } => Some(*name),
        _ => None,
    }
}
