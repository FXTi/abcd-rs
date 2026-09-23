//! The vendored frame-slot model (design/ir-v0.2.md T4/§5.3 — canonical;
//! N66/N67). This supersedes the earlier "`params[0]` = `this`"
//! convention.
//!
//! A callee's [`FunctionData::params`] are the code-header argument
//! slots. The LEADING slots are the vendored implicit frame slots
//! `[func][new.target][this]`, each present per the callee's
//! `L_ESCallTypeAnnotation;` `callType` bits (vendor
//! `method_literal.h:59-62`: `HaveThisBit` = bit 0, `HaveNewTargetBit` =
//! bit 1, `HaveExtraBit` = bit 2, `HaveFuncBit` = bit 3); annotation
//! ABSENT → the vendored `0xF` default (`CALL_TYPE_MASK`,
//! `method_literal.h:28` — all three leading slots present, the es2abc
//! shape). The source formals follow, left-aligned and
//! `undefined`-padded (`interpreter-inl.cpp:486-494`). `callType` bit 2
//! ("extra") carries NO leading slot — it appends the actual argument
//! count as a TRAILING slot at call entry
//! (`interpreter-inl.cpp:490-494`), so it never shifts the leading
//! layout.
//!
//! The runtime binds the frame's `thisObj` from the this-role slot, and
//! `ldthis` reads it back (`EcmaInterpreter::GetThis`,
//! `interpreter-inl.cpp:7907-7912`; `HANDLE_OPCODE(LDTHIS)`,
//! `interpreter-inl.cpp:6970-6973`) — so the IR's this value of a
//! `Bytecode::Ldthis` is the this-role [`ValueDef::Param`], never
//! `params[0]` (which is the FUNC slot under the `0xF` default).

use crate::function::FunctionData;
use crate::module::{AnnValue, Module};

/// The callee's leading implicit frame slots, decoded from its
/// `L_ESCallTypeAnnotation;` `callType` bits (or the vendored default).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameSlots {
    /// The closure object itself (bit 3).
    pub func: bool,
    /// `new.target` (bit 1).
    pub new_target: bool,
    /// The `this` binding (bit 0).
    pub this: bool,
}

impl FrameSlots {
    /// The vendored annotation-absent default (`0xF & CALL_TYPE_MASK`):
    /// func + new.target + this all present (the es2abc shape).
    pub const DEFAULT: Self = Self {
        func: true,
        new_target: true,
        this: true,
    };

    /// The number of leading implicit slots.
    pub fn implicit_count(self) -> usize {
        self.func as usize + self.new_target as usize + self.this as usize
    }

    /// The `params` index of the this-role slot; `None` when the
    /// callType carries no this bit.
    pub fn this_index(self) -> Option<usize> {
        if self.this {
            Some(self.func as usize + self.new_target as usize)
        } else {
            None
        }
    }

    /// Decode the callee's `L_ESCallTypeAnnotation;` `callType` element;
    /// the annotation absent (or unreadable) → [`FrameSlots::DEFAULT`]
    /// (the vendored `UINT32_MAX & 0xF` fallback, `method_literal.cpp:51`
    /// — `UINT32_MAX means not found`).
    pub fn of(module: &Module, func: &FunctionData) -> Self {
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
                let Some(bits) = module.consts.get(*cid).and_then(|c| c.as_f64()) else {
                    continue;
                };
                let bits = bits as u32;
                return Self {
                    func: bits & 0b1000 != 0,
                    new_target: bits & 0b0010 != 0,
                    this: bits & 0b0001 != 0,
                };
            }
        }
        Self::DEFAULT
    }
}

/// The `params` index of `func`'s this-role slot under the vendored
/// frame-slot model; `None` when the callType carries no this bit or the
/// params are fewer than the implicit slots (the vendor ASSERT's
/// malformed shape, `method_literal.cpp:96-97` — conservative fallback,
/// documented).
pub fn this_param_index(module: &Module, func: &FunctionData) -> Option<usize> {
    let slots = FrameSlots::of(module, func);
    let idx = slots.this_index()?;
    if func.params.len() < slots.implicit_count() {
        return None;
    }
    Some(idx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::{Annotation, ClassData, FunctionKind, Modifiers, SourceLang};
    use crate::{ClassId, Const, FuncId};

    fn bare_module() -> Module {
        Module::new()
    }

    fn bare_func(m: &mut Module, params: usize) -> FuncId {
        let id = FuncId::new(m.functions.len() as u32);
        let name = m.sym.intern("f");
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            name,
            FunctionKind::Function,
        ));
        for _ in 0..params {
            let val = crate::ValueId::new(m.values.len() as u32);
            m.values.push(crate::Value {
                def: crate::ValueDef::Param(m.functions[id.index()].params.len() as u16),
                ty: crate::ty::Ty::Any,
            });
            m.functions[id.index()].params.push(val);
        }
        id
    }

    fn add_call_type(m: &mut Module, f: FuncId, bits: u32) {
        let descriptor = m.sym.intern("L_ESCallTypeAnnotation;");
        m.classes.push(ClassData {
            descriptor,
            name: descriptor,
            modifiers: Modifiers::NONE,
            source_lang: SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
        let class = ClassId::new((m.classes.len() - 1) as u32);
        let elem = m.sym.intern("callType");
        let cid = m.consts.push(Const::number(f64::from(bits)));
        m.functions[f.index()].annotations.push(Annotation {
            class,
            elements: vec![(elem, AnnValue::Const(cid))],
        });
    }

    #[test]
    fn default_0xf_shape_this_is_params_2() {
        let mut m = bare_module();
        let f = bare_func(&mut m, 3);
        assert_eq!(
            this_param_index(&m, &m.functions[f.index()]),
            Some(2),
            "0xF default: [func][new.target][this] → this at params[2]"
        );
    }

    #[test]
    fn annotation_without_newtarget_shifts_this() {
        let mut m = bare_module();
        let f = bare_func(&mut m, 2);
        add_call_type(&mut m, f, 0b1001); // func + this, no new.target
        assert_eq!(this_param_index(&m, &m.functions[f.index()]), Some(1));
    }

    #[test]
    fn annotation_without_this_bit_has_no_this_slot() {
        let mut m = bare_module();
        let f = bare_func(&mut m, 2);
        add_call_type(&mut m, f, 0b1000); // func only
        assert_eq!(this_param_index(&m, &m.functions[f.index()]), None);
    }

    #[test]
    fn params_shorter_than_implicit_slots_is_malformed() {
        let mut m = bare_module();
        let f = bare_func(&mut m, 2); // 0xF default needs 3 leading slots
        assert_eq!(this_param_index(&m, &m.functions[f.index()]), None);
    }
}
