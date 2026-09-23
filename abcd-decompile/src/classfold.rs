//! B2: the es2abc instance-initializer class-field fold.
//!
//! es2abc lowers class field initializers (`class A { #x = 4; … }`)
//! into a synthetic `instance_initializer` function: the constructor
//! invokes it through the lexical environment
//! (`ldlexvar` + `callruntime.callinit`), and its body is a sequence of
//! `this.#name = <constant>` definitions
//! (`callruntime.defineprivateproperty`). The v0.2 IR models that
//! lowering faithfully (the ctor's `Call`, the initializer's
//! `DefinePrivate`), so the decompiled class READ the private field but
//! never INITIALIZED it — the store stayed in the out-of-class
//! initializer (`this["p0_0"] = 4.0` — a PUBLIC property, a semantics
//! divergence the VM oracle catches: `private-field` printed
//! `undefined` instead of `4`).
//!
//! This module reverses the lowering (a structuring-side fold, design
//! decompile.md §6): when the pattern is EXACT, the initializer's
//! constant private definitions become `#name = <const>;` class-field
//! declarations and the ctor's initializer call is elided. The pattern
//! (every condition must hold — otherwise `None`, the status quo):
//!
//! 1. the ctor calls a value loaded from the lexical environment with
//!    `this` = the ctor's this-role frame slot and no arguments (the
//!    `callinit` shape), and the call result is unused;
//! 2. exactly ONE function body module-wide is stored into that
//!    (level, slot) through a `DefineFunc`/`AllocClosure`/
//!    `DefineMethod` chain (the es2abc wiring);
//! 3. that body is a single block of only constant materializations,
//!    `DefinePrivate` definitions on ITS this-role slot with constant
//!    values, and a return (no observable side effects beyond the field
//!    definitions — eliding the call is then semantics-preserving: JS
//!    class fields initialize at construction, which is when the ctor
//!    ran the initializer).
//!
//! The fold is a pure function of the module (deterministic, no emitter
//! state): recover consults it to elide the ctor call, emission
//! consults it to print the field declarations.

use std::collections::BTreeSet;

use abcd_ir::frame::this_param_index;
use abcd_ir::op::Op;
use abcd_ir::{ConstId, FuncId, InstId, Module, ValueDef};

use crate::names::NameScopes;

/// One class's folded field initializers plus the elided ctor calls.
#[derive(Clone, Debug)]
pub struct ClassFieldFold {
    /// `#name = value;` initializers, in initializer-body order.
    pub fields: Vec<(String, ConstId)>,
    /// The ctor's initializer-call instructions the fold elides.
    pub call_insts: BTreeSet<InstId>,
}

/// Compute the fold for the class whose constructor is `ctor` (see the
/// module docs for the exact pattern); `None` when any condition fails.
pub fn plan(module: &Module, ctor: FuncId) -> Option<ClassFieldFold> {
    // 0. `ctor` is the constructor of a DefineClass/DefineSendableClass
    // in the module — the fold pairs recover's elision with emission's
    // field declarations, both keyed on the class's ctor (without a
    // class definition site the declarations would never print and the
    // elided definitions would be LOST).
    let is_class_ctor = module.insts.iter().any(|inst| {
        matches!(
            &inst.op,
            Op::DefineClass { ctor: c, .. } | Op::DefineSendableClass { ctor: c, .. } if *c == ctor
        )
    });
    if !is_class_ctor {
        return None;
    }
    let ctor_fd = module.func(ctor)?;
    let ctor_this = this_param_index(module, ctor_fd)?;

    // 1. The ctor's callinit-shaped calls (callee = a lexenv load,
    // this = the ctor's this-role slot, no args, result unused).
    let mut calls: Vec<(InstId, u16, u16)> = Vec::new();
    for &b in &ctor_fd.blocks {
        let block = module.block(b)?;
        for &iid in &block.insts {
            let inst = module.inst(iid)?;
            let Op::Call {
                callee,
                this: Some(this),
                args,
                kind: abcd_ir::CallKind::Dynamic,
            } = &inst.op
            else {
                continue;
            };
            if !args.is_empty() {
                continue;
            }
            let ValueDef::Param(i) = module.value(*this)?.def else {
                continue;
            };
            if i as usize != ctor_this {
                continue;
            }
            let ValueDef::Inst(def_iid) = module.value(*callee)?.def else {
                continue;
            };
            let Op::GetLexVar { level, slot } = &module.inst(def_iid)?.op else {
                continue;
            };
            // The call result must be unused (elision drops it).
            if let Some(result) = inst.result {
                let mut used = false;
                for &bb in &ctor_fd.blocks {
                    for &other in &module.block(bb)?.insts {
                        if module.inst(other)?.op.operands().contains(&result) {
                            used = true;
                            break;
                        }
                    }
                }
                if used {
                    continue;
                }
            }
            calls.push((iid, *level, *slot));
        }
    }
    if calls.is_empty() {
        return None;
    }

    // 2. Exactly one initializer body behind the lexenv slots.
    let mut bodies: BTreeSet<FuncId> = BTreeSet::new();
    for &(_, level, slot) in &calls {
        for block in &module.blocks {
            for &iid in &block.insts {
                let inst = module.inst(iid)?;
                let Op::PutLexVar {
                    level: l,
                    slot: s,
                    value,
                } = &inst.op
                else {
                    continue;
                };
                if *l != level || *s != slot {
                    continue;
                }
                if let Some(body) = peel_closure_body(module, *value) {
                    bodies.insert(body);
                }
            }
        }
    }
    if bodies.len() != 1 {
        return None;
    }
    let init = *bodies.first()?;

    // 3. The initializer is a single block of constant private
    //    definitions on its own this-role slot (≥ 1), plus constant
    //    materializations and the return.
    let init_fd = module.func(init)?;
    if init_fd.blocks.len() != 1 {
        return None;
    }
    let init_this = this_param_index(module, init_fd)?;
    let scopes = NameScopes::build(module, init);
    let mut fields: Vec<(String, ConstId)> = Vec::new();
    for &iid in &module.block(init_fd.blocks[0])?.insts {
        let inst = module.inst(iid)?;
        match &inst.op {
            Op::LoadConst(_) => {}
            Op::DefinePrivate {
                level,
                slot,
                obj,
                value,
            } => {
                let ValueDef::Param(i) = module.value(*obj)?.def else {
                    return None;
                };
                if i as usize != init_this {
                    return None;
                }
                let cid = const_of(module, *value)?;
                let name = scopes
                    .name_of(iid)
                    .map(str::to_string)
                    .unwrap_or_else(|| format!("p{level}_{slot}"));
                fields.push((name, cid));
            }
            Op::Return { .. } => {}
            _ => return None,
        }
    }
    if fields.is_empty() {
        return None;
    }
    Some(ClassFieldFold {
        fields,
        call_insts: calls.into_iter().map(|(iid, _, _)| iid).collect(),
    })
}

/// Peel a `DefineMethod`/`AllocClosure`/`DefineFunc` chain to the
/// function body behind a value; `None` for any other shape.
fn peel_closure_body(module: &Module, mut v: abcd_ir::ValueId) -> Option<FuncId> {
    loop {
        let ValueDef::Inst(iid) = module.value(v)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::DefineMethod { func, .. } => v = *func,
            Op::AllocClosure { func } => v = *func,
            Op::DefineFunc { body, .. } => return Some(*body),
            _ => return None,
        }
    }
}

/// The constant behind a value (a pooled constant or a `LoadConst`).
fn const_of(module: &Module, v: abcd_ir::ValueId) -> Option<ConstId> {
    match module.value(v)?.def {
        ValueDef::Const(cid) => Some(cid),
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(cid) => Some(*cid),
            _ => None,
        },
        _ => None,
    }
}
