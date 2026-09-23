//! The analysis-side adapter over the CANONICAL frame-slot model
//! ([`abcd_ir::frame`], N66/N67 — vendored ground truth:
//! `MethodLiteral::Initialize`, `L_ESCallTypeAnnotation;` callType bits
//! `HaveThis = 0x1`, `HaveNewTarget = 0x2`, `HaveFunc = 0x8`).
//!
//! Why an adapter and not a bare re-export: the canonical
//! [`abcd_ir::frame::FrameSlots::of`] applies the vendored
//! annotation-absent default (`0xF`) UNCONDITIONALLY, while the taint
//! engine's deliberate policy (N66, pinned by
//! `abcd-taint/tests/mechanisms.rs::call_binding_nonstatic_unannotated_overapprox`)
//! is that a NON-STATIC callee without the annotation has NO reliable
//! slot model and must over-approximate rather than bind precisely (the
//! one place taint chooses FP over FN). This module keeps that policy
//! local: annotation present → the canonical decode; absent + STATIC →
//! the canonical default; absent + non-static → `None`.
//!
//! History: landed as a stopgap duplicate in t-P2 with an orchestrator
//! ruling to defer to `abcd-ir::frame` once it landed (it did, d-P6).
//! `abcd-opt/src/inline.rs` keeps its own copy (`abcd-opt` cannot be
//! imported here); whether taint should adopt the canonical
//! unconditional-0xF reading (dropping the non-static policy) is flagged
//! to the orchestrator as a behavior-change decision, not folded in
//! silently.

use abcd_ir::{FuncId, Modifiers, Module};

pub use abcd_ir::frame::FrameSlots;

/// The callee's effective frame model under the TAINT policy: the
/// canonical decode when the annotation is present, the canonical
/// vendored default for `<static>` callees, and `None` when no reliable
/// model exists under the policy (non-static callee without the
/// annotation — conservative consumers must over-approximate).
pub fn frame_slots_of(module: &Module, callee: FuncId) -> Option<FrameSlots> {
    let fd = module.func(callee)?;
    if FrameSlots::from_annotation(module, callee).is_some() {
        return Some(FrameSlots::of(module, fd));
    }
    if fd.modifiers.contains(Modifiers::STATIC) {
        return Some(FrameSlots::DEFAULT);
    }
    None
}

/// Extension: the annotation-presence probe the canonical module does
/// not expose (it folds absence into the default).
trait FromAnnotation {
    fn from_annotation(module: &Module, callee: FuncId) -> Option<FrameSlots>;
}

impl FromAnnotation for FrameSlots {
    fn from_annotation(module: &Module, callee: FuncId) -> Option<FrameSlots> {
        let fd = module.func(callee)?;
        // The canonical decoder returns DEFAULT both for "absent" and
        // for an unreadable annotation; distinguishing requires the
        // annotation walk. Cheap and local: annotation present iff any
        // L_ESCallTypeAnnotation with a callType element exists.
        let present = fd.annotations.iter().any(|ann| {
            module
                .class(ann.class)
                .and_then(|c| module.sym.resolve(c.descriptor))
                == Some("L_ESCallTypeAnnotation;")
                && ann
                    .elements
                    .iter()
                    .any(|(name, _)| module.sym.resolve(*name) == Some("callType"))
        });
        present.then(|| FrameSlots::of(module, fd))
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
        let slots = frame_slots_of(&m, f).expect("static default");
        assert_eq!(slots, FrameSlots::DEFAULT);
        assert_eq!(slots.implicit_count(), 3);
        assert_eq!(slots.this_index(), Some(2));
    }

    #[test]
    fn non_static_without_annotation_has_no_model() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        assert_eq!(frame_slots_of(&m, f), None);
    }
}
