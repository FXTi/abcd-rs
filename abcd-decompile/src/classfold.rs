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

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::function::{Block, FunctionData, Inst, Value};
    use abcd_ir::module::{ClassData, FunctionKind, Modifiers, SourceLang};
    use abcd_ir::ty::Ty;
    use abcd_ir::{BlockId, CallKind, ClassId, Const, ValueId};

    // ── Hand-built module scaffolding (mirrors src/recover.rs's tests) ──

    fn mk_module() -> Module {
        let mut m = Module::new();
        let name = m.sym.intern("Ltest;");
        m.classes.push(ClassData {
            descriptor: name,
            name,
            modifiers: Modifiers::NONE,
            source_lang: SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
        m
    }

    /// A fresh function with the three vendored implicit frame slots
    /// (`[func][new.target][this]`, the annotation-absent default) and
    /// one empty entry block.
    fn add_fn(m: &mut Module, name: &str) -> FuncId {
        let sym = m.sym.intern(name);
        let id = FuncId::new(m.functions.len() as u32);
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            sym,
            FunctionKind::Function,
        ));
        let b = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(id).unwrap().blocks.push(b);
        for _ in 0..3 {
            let idx = m.func(id).unwrap().params.len() as u16;
            let val = ValueId::new(m.values.len() as u32);
            m.values.push(Value {
                def: ValueDef::Param(idx),
                ty: Ty::Any,
            });
            m.func_mut(id).unwrap().params.push(val);
        }
        id
    }

    fn entry_of(m: &Module, f: FuncId) -> BlockId {
        m.func(f).unwrap().blocks[0]
    }

    fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
        assert!(!op.has_result(), "{op:?} has a result");
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    }

    fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
        assert!(op.has_result(), "{op:?} has no result");
        let inst = push_inst_raw(m, b, op);
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(inst),
            ty: Ty::Any,
        });
        m.inst_mut(inst).unwrap().result = Some(val);
        val
    }

    fn push_inst_raw(m: &mut Module, b: BlockId, op: Op) -> InstId {
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    }

    /// A value defined directly by a pooled constant (no defining inst).
    fn const_value(m: &mut Module, c: Const) -> (ValueId, ConstId) {
        let cid = m.consts.push(c);
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Const(cid),
            ty: Ty::Any,
        });
        (val, cid)
    }

    // ── The exact es2abc class-field fold shape ─────────────────────

    /// The fixture roles the mutation closures reach for.
    struct Fixture {
        ctor: FuncId,
        init: FuncId,
        ctor_b: BlockId,
        init_b: BlockId,
        wire_b: BlockId,
        call_iid: InstId,
        class_iid: InstId,
        put_iid: InstId,
        field_iid: InstId,
        field_cid: ConstId,
        callee_v: ValueId,
        call_v: ValueId,
        df_v: ValueId,
    }

    /// The qualifying shape (module docs conditions 1-3): a DefineClass
    /// ctor whose body calls `GetLexVar(0,0)()` with the this-role slot
    /// and drops the result; the slot stores a DefineFunc chain to an
    /// initializer that is a single block of one constant private field
    /// definition on its own this-role slot. `edit` mutates the shape
    /// for the near-miss tests.
    fn fixture(edit: &mut dyn FnMut(&mut Module, &Fixture)) -> (Module, Fixture) {
        let mut m = mk_module();
        let ctor = add_fn(&mut m, "ctor");
        let init = add_fn(&mut m, "init");
        let wire = add_fn(&mut m, "wire");
        let ctor_b = entry_of(&m, ctor);
        let init_b = entry_of(&m, init);
        let wire_b = entry_of(&m, wire);
        let ctor_this = m.func(ctor).unwrap().params[2];
        let init_this = m.func(init).unwrap().params[2];

        // The class definition site (wire hosts the es2abc wiring).
        let members = m.consts.push(Const::ArrayLiteral(vec![]));
        let class_v = emit_val(
            &mut m,
            wire_b,
            Op::DefineClass {
                ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 0,
            },
        );
        let ValueDef::Inst(class_iid) = m.value(class_v).unwrap().def else {
            panic!("the class definition is instruction-defined");
        };
        // The initializer body behind lexenv slot (0, 0).
        let df_v = emit_val(
            &mut m,
            wire_b,
            Op::DefineFunc {
                body: init,
                captures: vec![],
                length: 0,
            },
        );
        let put_iid = push_inst(
            &mut m,
            wire_b,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: df_v,
            },
        );
        push_inst(&mut m, wire_b, Op::Return { value: None });

        // The ctor's callinit-shaped call (result dropped).
        let callee_v = emit_val(&mut m, ctor_b, Op::GetLexVar { level: 0, slot: 0 });
        let call_v = emit_val(
            &mut m,
            ctor_b,
            Op::Call {
                callee: callee_v,
                this: Some(ctor_this),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let ValueDef::Inst(call_iid) = m.value(call_v).unwrap().def else {
            panic!("the call result is instruction-defined");
        };
        push_inst(&mut m, ctor_b, Op::Return { value: None });

        // The initializer: `#x = 4;` on its own this-role slot.
        let field_cid = m.consts.push(Const::number(4.0));
        let field_v = emit_val(&mut m, init_b, Op::LoadConst(field_cid));
        let field_iid = push_inst(
            &mut m,
            init_b,
            Op::DefinePrivate {
                level: 0,
                slot: 1,
                obj: init_this,
                value: field_v,
            },
        );
        push_inst(&mut m, init_b, Op::Return { value: None });

        let fx = Fixture {
            ctor,
            init,
            ctor_b,
            init_b,
            wire_b,
            call_iid,
            class_iid,
            put_iid,
            field_iid,
            field_cid,
            callee_v,
            call_v,
            df_v,
        };
        edit(&mut m, &fx);
        (m, fx)
    }

    /// The exact shape folds: the field declaration plus the elided call.
    #[test]
    fn fold_mainline() {
        let (m, fx) = fixture(&mut |_, _| ());
        let fold = plan(&m, fx.ctor).expect("the exact shape folds");
        assert_eq!(fold.fields, vec![("p0_1".to_string(), fx.field_cid)]);
        assert!(fold.call_insts.contains(&fx.call_iid));
        assert_eq!(fold.call_insts.len(), 1);
    }

    /// A DefineSendableClass definition site qualifies the same way.
    #[test]
    fn fold_sendable_class_ctor() {
        let (m, fx) = fixture(&mut |m, fx| {
            let members = m.consts.push(Const::ArrayLiteral(vec![]));
            m.inst_mut(fx.class_iid).unwrap().op = Op::DefineSendableClass {
                ctor: fx.ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 0,
            };
        });
        assert!(plan(&m, fx.ctor).is_some());
    }

    /// Without a class definition site for the ctor there is no fold
    /// (the declarations would never print).
    #[test]
    fn bail_not_a_class_ctor() {
        let (m, fx) = fixture(&mut |m, fx| {
            let members = m.consts.push(Const::ArrayLiteral(vec![]));
            m.inst_mut(fx.class_iid).unwrap().op = Op::DefineClass {
                ctor: fx.init,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 0,
            };
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// The ctor carrying fewer slots than the implicit frame layout has
    /// no this-role slot to match against.
    #[test]
    fn bail_ctor_without_this_slot() {
        let (mut m, fx) = fixture(&mut |_, _| ());
        m.func_mut(fx.ctor).unwrap().params.clear();
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A call with arguments is not the callinit shape.
    #[test]
    fn bail_call_has_args() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.ctor).unwrap().params[0];
            let Op::Call { args, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *args = vec![p0];
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A call without an explicit receiver is not the callinit shape.
    #[test]
    fn bail_call_without_this() {
        let (m, fx) = fixture(&mut |m, fx| {
            let Op::Call { this, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *this = None;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A non-Dynamic call kind is not the callinit shape.
    #[test]
    fn bail_call_non_dynamic_kind() {
        let (m, fx) = fixture(&mut |m, fx| {
            let Op::Call { kind, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *kind = CallKind::Direct;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A receiver that is not a frame slot is not the callinit shape.
    #[test]
    fn bail_call_this_not_a_param() {
        let (m, fx) = fixture(&mut |m, fx| {
            let Op::Call { this, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *this = Some(fx.callee_v);
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A receiver on the wrong frame slot (not the this-role slot) is
    /// not the callinit shape.
    #[test]
    fn bail_call_wrong_this_slot() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.ctor).unwrap().params[0];
            let Op::Call { this, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *this = Some(p0);
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A callee that is not instruction-defined cannot be a lexenv load.
    #[test]
    fn bail_callee_not_inst_defined() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.ctor).unwrap().params[0];
            let Op::Call { callee, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *callee = p0;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A callee defined by anything but a GetLexVar is not the callinit
    /// shape.
    #[test]
    fn bail_callee_not_getlexvar() {
        let (m, fx) = fixture(&mut |m, fx| {
            let Op::Call { callee, .. } = &mut m.inst_mut(fx.call_iid).unwrap().op else {
                panic!("call fixture");
            };
            *callee = fx.df_v;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A used call result cannot be elided.
    #[test]
    fn bail_call_result_used() {
        let (m, fx) = fixture(&mut |m, fx| {
            let last = *m.block(fx.ctor_b).unwrap().insts.last().unwrap();
            m.inst_mut(last).unwrap().op = Op::Return {
                value: Some(fx.call_v),
            };
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// No initializer body stored into the called slot: nothing to fold.
    #[test]
    fn bail_no_initializer_store() {
        let (m, fx) = fixture(&mut |m, fx| {
            let Op::PutLexVar { slot, .. } = &mut m.inst_mut(fx.put_iid).unwrap().op else {
                panic!("put fixture");
            };
            *slot = 9;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// Two candidate bodies behind one slot is ambiguous: no fold.
    #[test]
    fn bail_two_initializer_bodies() {
        let (m, fx) = fixture(&mut |m, fx| {
            let init2 = add_fn(m, "init2");
            let b2 = entry_of(m, init2);
            let this2 = m.func(init2).unwrap().params[2];
            let cid = m.consts.push(Const::number(5.0));
            let v = emit_val(m, b2, Op::LoadConst(cid));
            push_inst(
                m,
                b2,
                Op::DefinePrivate {
                    level: 0,
                    slot: 2,
                    obj: this2,
                    value: v,
                },
            );
            push_inst(m, b2, Op::Return { value: None });
            let df2 = emit_val(
                m,
                fx.wire_b,
                Op::DefineFunc {
                    body: init2,
                    captures: vec![],
                    length: 0,
                },
            );
            push_inst(
                m,
                fx.wire_b,
                Op::PutLexVar {
                    level: 0,
                    slot: 0,
                    value: df2,
                },
            );
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A stored value that is not a closure chain is not an initializer.
    #[test]
    fn bail_store_not_a_closure() {
        let (m, fx) = fixture(&mut |m, fx| {
            let cid = m.consts.push(Const::number(9.0));
            let v = emit_val(m, fx.wire_b, Op::LoadConst(cid));
            let Op::PutLexVar { value, .. } = &mut m.inst_mut(fx.put_iid).unwrap().op else {
                panic!("put fixture");
            };
            *value = v;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A multi-block initializer has control flow the fold cannot
    /// account for.
    #[test]
    fn bail_init_two_blocks() {
        let (m, fx) = fixture(&mut |m, fx| {
            let b = BlockId::new(m.blocks.len() as u32);
            m.blocks.push(Block::default());
            m.func_mut(fx.init).unwrap().blocks.push(b);
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// An initializer with observable side effects beyond the field
    /// definitions must keep its call.
    #[test]
    fn bail_init_side_effect() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.init).unwrap().params[0];
            emit_val(
                m,
                fx.init_b,
                Op::Call {
                    callee: p0,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A field defined on a non-slot receiver is not the es2abc shape.
    #[test]
    fn bail_field_obj_not_a_param() {
        let (m, fx) = fixture(&mut |m, fx| {
            let cid = m.consts.push(Const::Null);
            let v = emit_val(m, fx.init_b, Op::LoadConst(cid));
            let Op::DefinePrivate { obj, .. } = &mut m.inst_mut(fx.field_iid).unwrap().op else {
                panic!("field fixture");
            };
            *obj = v;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A field defined on the wrong frame slot is not the es2abc shape.
    #[test]
    fn bail_field_wrong_this_slot() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.init).unwrap().params[0];
            let Op::DefinePrivate { obj, .. } = &mut m.inst_mut(fx.field_iid).unwrap().op else {
                panic!("field fixture");
            };
            *obj = p0;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A field defined with a non-constant value cannot become a class
    /// field declaration.
    #[test]
    fn bail_field_value_not_const() {
        let (m, fx) = fixture(&mut |m, fx| {
            let p0 = m.func(fx.init).unwrap().params[0];
            let Op::DefinePrivate { value, .. } = &mut m.inst_mut(fx.field_iid).unwrap().op else {
                panic!("field fixture");
            };
            *value = p0;
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// A field value pooled directly as a constant (no LoadConst) folds
    /// the same way.
    #[test]
    fn fold_field_value_direct_const() {
        let (mut m, fx) = fixture(&mut |_, _| ());
        let (v, cid) = const_value(&mut m, Const::number(7.0));
        let Op::DefinePrivate { value, .. } = &mut m.inst_mut(fx.field_iid).unwrap().op else {
            panic!("field fixture");
        };
        *value = v;
        let fold = plan(&m, fx.ctor).expect("a pooled constant folds");
        assert_eq!(fold.fields, vec![("p0_1".to_string(), cid)]);
    }

    /// An initializer defining no fields at all is not the es2abc shape.
    #[test]
    fn bail_init_without_fields() {
        let (m, fx) = fixture(&mut |m, fx| {
            m.block_mut(fx.init_b)
                .unwrap()
                .insts
                .retain(|&i| i != fx.field_iid);
        });
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// The initializer without a this-role slot cannot match the field
    /// receiver.
    #[test]
    fn bail_init_without_this_slot() {
        let (mut m, fx) = fixture(&mut |_, _| ());
        m.func_mut(fx.init).unwrap().params.clear();
        assert!(plan(&m, fx.ctor).is_none());
    }

    /// The DefineMethod → AllocClosure → DefineFunc wiring chain peels
    /// to the same initializer body.
    #[test]
    fn fold_peeled_method_chain() {
        let (m, fx) = fixture(&mut |m, fx| {
            let ac_v = emit_val(m, fx.wire_b, Op::AllocClosure { func: fx.df_v });
            let cid = m.consts.push(Const::Null);
            let obj_v = emit_val(m, fx.wire_b, Op::LoadConst(cid));
            let name = m.sym.intern("init");
            let dm_v = emit_val(
                m,
                fx.wire_b,
                Op::DefineMethod {
                    object: obj_v,
                    name,
                    func: ac_v,
                    length: 0,
                },
            );
            let Op::PutLexVar { value, .. } = &mut m.inst_mut(fx.put_iid).unwrap().op else {
                panic!("put fixture");
            };
            *value = dm_v;
        });
        assert!(plan(&m, fx.ctor).is_some());
    }

    /// `peel_closure_body` declines values outside the chain shape: a
    /// bare frame slot (not instruction-defined) and any other op.
    #[test]
    fn peel_closure_body_declines() {
        let (m, fx) = fixture(&mut |_, _| ());
        let p0 = m.func(fx.ctor).unwrap().params[0];
        assert_eq!(peel_closure_body(&m, p0), None);
        assert_eq!(peel_closure_body(&m, fx.callee_v), None);
    }

    /// `const_of`: a pooled constant and a LoadConst both resolve; frame
    /// slots and non-LoadConst instructions do not.
    #[test]
    fn const_of_forms() {
        let (mut m, fx) = fixture(&mut |_, _| ());
        let (direct, direct_cid) = const_value(&mut m, Const::number(1.0));
        assert_eq!(const_of(&m, direct), Some(direct_cid));
        let cid = m.consts.push(Const::number(2.0));
        let loaded = emit_val(&mut m, fx.ctor_b, Op::LoadConst(cid));
        assert_eq!(const_of(&m, loaded), Some(cid));
        let p0 = m.func(fx.ctor).unwrap().params[0];
        assert_eq!(const_of(&m, p0), None);
        assert_eq!(const_of(&m, fx.callee_v), None);
    }
}
