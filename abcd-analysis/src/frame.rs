//! The analysis-side adapter over the canonical frame-slot model
//! ([`abcd_ir::frame`], `D6`, N66/N67 — vendored ground truth:
//! `MethodLiteral::Initialize`, `L_ESCallTypeAnnotation;` `callType` bits
//! `HaveThis = 0x1`, `HaveNewTarget = 0x2`, `HaveFunc = 0x8`, and
//! `static_core` typed method frames).
//!
//! Why an adapter and not a bare re-export: [`abcd_ir::frame::FrameSlots::of`]
//! applies the `DynamicEcma` annotation-absent default (`0xF`) unconditionally,
//! while the taint engine's deliberate policy (N66, pinned by
//! `abcd-taint/tests/mechanisms.rs::call_binding_nonstatic_unannotated_overapprox`)
//! is that an unannotated non-static [`abcd_ir::Dialect::DynamicEcma`] callee
//! has no reliable slot model and must over-approximate rather than bind
//! precisely. Under [`abcd_ir::Dialect::StaticArkTS`], method frame layouts
//! (`H = 0` static, `H = 1` instance `this` at `params[0]`) are fixed by static
//! signature metadata without needing `L_ESCallTypeAnnotation;`.
//!
//! `abcd-opt/src/inline.rs` keeps its own local slot helper (`abcd-opt`
//! does not depend on `abcd-analysis`). See `design/decisions.md` (`D6`,
//! N66/N67) and `design/analysis.md` for the interprocedural frame-binding
//! contract.

use abcd_ir::{Dialect, FuncId, Modifiers, Module};

pub use abcd_ir::frame::FrameSlots;

/// Resolve `callee`'s effective frame model under the analysis/taint policy:
///
/// 1. Explicit `L_ESCallTypeAnnotation;` `callType` bits win when present.
/// 2. Under [`Dialect::StaticArkTS`], returns [`FrameSlots::of`] (`H = 0` for
///    `STATIC`, `H = 1` with `this` at `params[0]` for instance/constructor).
/// 3. Under [`Dialect::DynamicEcma`], returns [`FrameSlots::DEFAULT`] (`H = 3`)
///    for `Modifiers::STATIC` callees and `None` otherwise (`N66`).
#[must_use]
pub fn frame_slots_of(module: &Module, callee: FuncId) -> Option<FrameSlots> {
    let fd = module.func(callee)?;
    if FrameSlots::from_call_type_annotation(module, fd).is_some()
        || module.func_dialect(fd) == Dialect::StaticArkTS
    {
        return Some(FrameSlots::of(module, fd));
    }
    if fd.modifiers.contains(Modifiers::STATIC) {
        return Some(FrameSlots::DEFAULT);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::module::{ClassData, FunctionKind, SourceLang};
    use abcd_ir::{ClassId, FunctionData};

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

    #[test]
    fn static_arkts_methods_resolve_h0_and_h1_without_annotation() {
        let mut m = Module::with_dialect(Dialect::StaticArkTS);
        let sym = m.sym.intern("LArkPkg/Widget;");
        let mut cls = ClassData::new(sym, sym);
        cls.source_lang = SourceLang::ArkTS;
        let ark_cid = ClassId::new(m.classes.len() as u32);
        m.classes.push(cls);

        let s_name = m.sym.intern("staticFn");
        let s_fid = FuncId::new(m.functions.len() as u32);
        let mut s_fd = FunctionData::new(ark_cid, s_name, FunctionKind::Function);
        s_fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        m.functions.push(s_fd);

        let i_name = m.sym.intern("instFn");
        let i_fid = FuncId::new(m.functions.len() as u32);
        let mut i_fd = FunctionData::new(ark_cid, i_name, FunctionKind::Function);
        i_fd.modifiers = Modifiers::PUBLIC;
        m.functions.push(i_fd);

        let s_slots = frame_slots_of(&m, s_fid).expect("StaticArkTS static method");
        assert_eq!(s_slots, FrameSlots::NONE);
        assert_eq!(s_slots.implicit_count(), 0);
        assert_eq!(s_slots.this_index(), None);

        let i_slots = frame_slots_of(&m, i_fid).expect("StaticArkTS instance method");
        assert_eq!(i_slots, FrameSlots::STATIC_INSTANCE);
        assert_eq!(i_slots.implicit_count(), 1);
        assert_eq!(i_slots.this_index(), Some(0));

        // Dynamic container (`Dialect::DynamicEcma`) with `SourceLang::ArkTS` keeps N66 policy.
        let mut dyn_m = mk_module();
        let dyn_sym = dyn_m.sym.intern("LDynArk/Widget;");
        let mut dyn_cls = ClassData::new(dyn_sym, dyn_sym);
        dyn_cls.source_lang = SourceLang::ArkTS;
        let dyn_cid = ClassId::new(dyn_m.classes.len() as u32);
        dyn_m.classes.push(dyn_cls);
        let dyn_fid = FuncId::new(dyn_m.functions.len() as u32);
        let mut dyn_fd = FunctionData::new(dyn_cid, i_name, FunctionKind::Function);
        dyn_fd.modifiers = Modifiers::PUBLIC;
        dyn_m.functions.push(dyn_fd);
        assert_eq!(frame_slots_of(&dyn_m, dyn_fid), None);
    }
}
