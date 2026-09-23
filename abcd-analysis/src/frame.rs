//! The vendored frame-slot model (N66): which leading `params` slots of a
//! callee are the implicit frame slots `[func][newTarget][this]` rather
//! than source formals.
//!
//! The ground truth is arkcompiler's `MethodLiteral::Initialize` — a slot
//! is present iff the corresponding `L_ESCallTypeAnnotation;` callType
//! bit: `HaveThis = 0x1`, `HaveNewTarget = 0x2`, `HaveFunc = 0x8`. When
//! the annotation is ABSENT on a `<static>` callee the vendored default
//! is `callType = 0xF` — all three implicit slots — which is exactly the
//! es2abc corpus shape (every corpus function declares
//! `num_args = 3 + formals` and reads its first formal from `a3`).
//!
//! This is the shared home of the model for the ANALYSIS side
//! (`abcd-taint`'s arg↔param binding and the rung-1 alias engine's
//! interprocedural hops). `abcd-opt/src/inline.rs` keeps its own copy
//! (`abcd-opt` cannot be imported here).
//!
//! **Orchestrator ruling (t-P2):** `abcd-ir` is the CANONICAL home for
//! this model (it is IR semantics — the meaning of `FunctionData.params`
//! slots); a public `abcd_ir::frame` module is being built there
//! concurrently. This module is an approved TEMPORARY stopgap: when
//! `abcd_ir::frame` lands, replace it with a deferral (re-export / thin
//! adapter) so the alias engine keeps its behavior contract pinned
//! locally. End state: `abcd-ir::frame` canonical; `abcd-opt`,
//! `abcd-taint`, and this stopgap all defer to it.

use abcd_ir::{AnnValue, Const, FuncId, Modifiers, Module};

/// The callee's call-type: which leading `params` slots are implicit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FrameSlots {
    /// The func slot (the closure itself) leads.
    pub func: bool,
    /// The new.target slot follows.
    pub new_target: bool,
    /// The this slot follows.
    pub this: bool,
}

impl FrameSlots {
    /// The vendored annotation-absent default (`UINT32_MAX & 0xF`).
    pub const DEFAULT: Self = Self {
        func: true,
        new_target: true,
        this: true,
    };

    /// Number of leading implicit slots (= the first formal's index).
    pub fn implicit_slots(self) -> usize {
        self.func as usize + self.new_target as usize + self.this as usize
    }

    /// The this-slot index (implicit slots are ordered func, newTarget,
    /// this), when the this slot is present.
    pub fn this_slot(self) -> Option<usize> {
        self.this
            .then(|| self.func as usize + self.new_target as usize)
    }

    /// Read the callee's `L_ESCallTypeAnnotation;` callType bits, when
    /// the annotation is present.
    pub fn from_annotation(module: &Module, callee: FuncId) -> Option<Self> {
        let func = module.func(callee)?;
        for ann in &func.annotations {
            let is_call_type = module
                .class(ann.class)
                .and_then(|c| module.sym.resolve(c.descriptor))
                == Some("L_ESCallTypeAnnotation;");
            if !is_call_type {
                continue;
            }
            for (name, value) in &ann.elements {
                if module.sym.resolve(*name) != Some("callType") {
                    continue;
                }
                let AnnValue::Const(cid) = value else {
                    continue;
                };
                let bits = module
                    .consts
                    .get(*cid)
                    .and_then(Const::as_f64)
                    .map(|x| x as u32)?;
                return Some(Self {
                    func: bits & 0b1000 != 0,
                    new_target: bits & 0b0010 != 0,
                    this: bits & 0b0001 != 0,
                });
            }
        }
        None
    }

    /// The callee's effective frame model: the annotation when present,
    /// the 0xF default for `<static>` callees, and `None` when no
    /// reliable model exists (non-static callee without the annotation
    /// — conservative consumers must over-approximate).
    pub fn of(module: &Module, callee: FuncId) -> Option<Self> {
        match Self::from_annotation(module, callee) {
            Some(ct) => Some(ct),
            None => {
                let fd = module.func(callee)?;
                if fd.modifiers.contains(Modifiers::STATIC) {
                    Some(Self::DEFAULT)
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;

    #[test]
    fn static_callee_without_annotation_gets_the_default() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        m.func_mut(f).unwrap().modifiers = Modifiers::STATIC;
        let slots = FrameSlots::of(&m, f).expect("static default");
        assert_eq!(slots, FrameSlots::DEFAULT);
        assert_eq!(slots.implicit_slots(), 3);
        assert_eq!(slots.this_slot(), Some(2));
    }

    #[test]
    fn non_static_without_annotation_has_no_model() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        assert_eq!(FrameSlots::of(&m, f), None);
    }
}
