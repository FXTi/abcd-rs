//! Explicit calling-convention and frame-slot contract (`design/ir.md`,
//! `design/decisions.md` D6, N66/N67).
//!
//! A callee's [`FunctionData::params`] are the SSA entry parameter slots in
//! code-header argument order. `abcd-ir` supports two explicit execution and
//! calling-convention dialects ([`crate::Dialect`], determined by the owning
//! [`crate::ClassData::source_lang`]):
//!
//! ## 1. Dynamic ECMAScript / TypeScript ([`crate::Dialect::DynamicEcma`])
//!
//! In dynamic `.abc` modules (`es2abc`, [`crate::SourceLang::EcmaScript`] /
//! [`crate::SourceLang::TypeScript`]), the LEADING slots of
//! [`FunctionData::params`] are the vendored implicit frame slots
//! `[func][new.target][this]`, each present per the callee's
//! `L_ESCallTypeAnnotation;` `callType` bits (vendor `method_literal.h:59-62`:
//! `HaveThisBit` = bit 0, `HaveNewTargetBit` = bit 1, `HaveExtraBit` = bit 2,
//! `HaveFuncBit` = bit 3). When the annotation is absent, the vendored `0xF`
//! default (`CALL_TYPE_MASK`, `method_literal.h:28`) applies
//! ([`FrameSlots::DEFAULT`], `H = 3` — all three leading slots present).
//! Declared source formals follow at `params[H..]`, left-aligned and
//! `undefined`-padded (`interpreter-inl.cpp:486-494`). Bit 2 (`HaveExtraBit`)
//! appends actual argc as a TRAILING slot at call entry
//! (`interpreter-inl.cpp:490-494`) and never shifts leading indices.
//!
//! The dynamic runtime binds `thisObj` from the `this`-role slot and `ldthis`
//! reads it back (`EcmaInterpreter::GetThis`, `interpreter-inl.cpp:7907-7912`;
//! `HANDLE_OPCODE(LDTHIS)`, `interpreter-inl.cpp:6970-6973`), so `ldthis`
//! lifts to the `this`-role [`crate::ValueDef::Param`] (`params[2]` under the
//! `0xF` default, never `params[0]`, which holds `func`; N66/N67).
//!
//! ## 2. Static ArkTS ([`crate::Dialect::StaticArkTS`])
//!
//! In static ArkTS modules (`static_core` / `ets2panda`,
//! [`crate::SourceLang::ArkTS`], `#36`), functions carry **zero** hidden
//! ECMAScript closure (`func`) or `new.target` slots (`vendor`
//! `MethodDataAccessor::EnumerateTypes`, `method_data_accessor-inl.h:318-330`;
//! `DebugInfoExtractor`, `debug_info_extractor.cpp:206-208`):
//!
//! - **`static` methods / top-level functions**
//!   (`func.modifiers.contains(Modifiers::STATIC)`): `H = 0` implicit leading
//!   slots ([`FrameSlots::NONE`]); declared formals start directly at
//!   `params[0..]` and [`this_param_index`] is `None`.
//! - **Instance methods and constructors**
//!   (`!func.modifiers.contains(Modifiers::STATIC)`): [`FrameSlots::STATIC_INSTANCE`]
//!   (`H = 1`); `params[0]` is the explicit receiver `this` of the owning
//!   class ([`this_param_index`] = `Some(0)`) and declared formals follow at
//!   `params[1..]`.

use crate::function::FunctionData;
use crate::module::{AnnValue, Dialect, Modifiers, Module};

/// The callee's leading implicit parameter slots before declared source formals.
///
/// Resolved via [`FrameSlots::of`] from an explicit `L_ESCallTypeAnnotation;`
/// when present, or from the callee's [`Dialect`] default (`D6`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameSlots {
    /// Leading closure-object slot (`func`, dynamic `callType` bit 3).
    pub func: bool,
    /// Leading `new.target` slot (dynamic `callType` bit 1).
    pub new_target: bool,
    /// Leading `this` receiver slot (dynamic `callType` bit 0, or `params[0]`
    /// on non-static [`Dialect::StaticArkTS`] instance methods/constructors).
    pub this: bool,
}

impl FrameSlots {
    /// Dynamic ECMAScript annotation-absent default (`0xF & CALL_TYPE_MASK`):
    /// `func` + `new.target` + `this` all present (`H = 3`, the `es2abc` shape).
    pub const DEFAULT: Self = Self {
        func: true,
        new_target: true,
        this: true,
    };

    /// Zero implicit leading slots (`H = 0`): [`Dialect::StaticArkTS`] `static`
    /// methods (and dynamic callees with `callType = 0`). Declared formals
    /// start directly at `params[0]`.
    pub const NONE: Self = Self {
        func: false,
        new_target: false,
        this: false,
    };

    /// [`Dialect::StaticArkTS`] instance method / constructor frame (`H = 1`):
    /// no hidden `func` or `new.target` slots, with the receiver `this` at
    /// `params[0]` and declared formals at `params[1..]`.
    pub const STATIC_INSTANCE: Self = Self {
        func: false,
        new_target: false,
        this: true,
    };

    /// Default leading frame layout for [`Dialect::StaticArkTS`]
    /// (`SourceLang::ArkTS`): [`Self::NONE`] (`H = 0`) when `is_static_method`
    /// is `true`, [`Self::STATIC_INSTANCE`] (`params[0]` = `this`) otherwise.
    #[must_use]
    pub const fn for_static_arkts(is_static_method: bool) -> Self {
        if is_static_method {
            Self::NONE
        } else {
            Self::STATIC_INSTANCE
        }
    }

    /// Number of leading implicit slots (`H`) preceding declared formals.
    #[must_use]
    pub const fn implicit_count(self) -> usize {
        self.func as usize + self.new_target as usize + self.this as usize
    }

    /// Index in [`FunctionData::params`] where declared source formals begin
    /// (`params[H..]`, alias for [`Self::implicit_count`]).
    #[must_use]
    pub const fn formal_offset(self) -> usize {
        self.implicit_count()
    }

    /// The `params` index of the `this`-role slot; `None` when the frame
    /// carries no `this` slot.
    #[must_use]
    pub const fn this_index(self) -> Option<usize> {
        if self.this {
            Some(self.func as usize + self.new_target as usize)
        } else {
            None
        }
    }

    /// Decode an explicit `L_ESCallTypeAnnotation;` `callType` element on
    /// `func`, returning `None` when the annotation is absent or unreadable.
    #[must_use]
    pub fn from_call_type_annotation(module: &Module, func: &FunctionData) -> Option<Self> {
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
                return Some(Self {
                    func: bits & 0b1000 != 0,
                    new_target: bits & 0b0010 != 0,
                    this: bits & 0b0001 != 0,
                });
            }
        }
        None
    }

    /// Resolve `func`'s leading implicit frame slots (`D6`):
    ///
    /// 1. Explicit `L_ESCallTypeAnnotation;` `callType` bits win when present.
    /// 2. Under [`Dialect::StaticArkTS`] (`SourceLang::ArkTS`), `static`
    ///    methods return [`FrameSlots::NONE`] (`H = 0`) and non-static methods
    ///    return [`FrameSlots::STATIC_INSTANCE`] (`params[0]` = `this`).
    /// 3. Under [`Dialect::DynamicEcma`] (or bare synthetic modules without a
    ///    class entry), returns [`FrameSlots::DEFAULT`] (`0xF`, `H = 3` —
    ///    vendor `method_literal.cpp:51`).
    #[must_use]
    pub fn of(module: &Module, func: &FunctionData) -> Self {
        if let Some(annotated) = Self::from_call_type_annotation(module, func) {
            return annotated;
        }
        match module.func_dialect(func) {
            Dialect::DynamicEcma => Self::DEFAULT,
            Dialect::StaticArkTS => {
                Self::for_static_arkts(func.modifiers.contains(Modifiers::STATIC))
            }
        }
    }
}

/// The `params` index of `func`'s `this`-role slot under its [`Dialect`]
/// frame-slot contract; `None` when the frame carries no `this` slot (e.g.
/// `callType` without bit 0, or a `static` method in [`Dialect::StaticArkTS`])
/// or when `func.params` is shorter than the implicit slot prefix (vendor
/// `method_literal.cpp:96-97` malformed-header fallback).
#[must_use]
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
    use crate::module::{Annotation, ClassData, FunctionKind, SourceLang};
    use crate::{ClassId, Const, FuncId};

    fn bare_module() -> Module {
        Module::new()
    }

    fn bare_func(m: &mut Module, params: usize) -> FuncId {
        bare_func_in_class(m, ClassId::new(0), Modifiers::NONE, params)
    }

    fn bare_func_in_class(
        m: &mut Module,
        class_id: ClassId,
        modifiers: Modifiers,
        params: usize,
    ) -> FuncId {
        let id = FuncId::new(m.functions.len() as u32);
        let name = m.sym.intern("f");
        let mut fd = FunctionData::new(class_id, name, FunctionKind::Function);
        fd.modifiers = modifiers;
        m.functions.push(fd);
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

    fn add_class_with_lang(m: &mut Module, desc: &str, lang: SourceLang) -> ClassId {
        let sym = m.sym.intern(desc);
        let mut cls = ClassData::new(sym, sym);
        cls.source_lang = lang;
        let id = ClassId::new(m.classes.len() as u32);
        m.classes.push(cls);
        id
    }

    fn add_call_type(m: &mut Module, f: FuncId, bits: u32) {
        let descriptor = m.sym.intern("L_ESCallTypeAnnotation;");
        m.classes.push(ClassData::new(descriptor, descriptor));
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
        let fd = &m.functions[f.index()];
        assert_eq!(FrameSlots::from_call_type_annotation(&m, fd), None);
        assert_eq!(FrameSlots::of(&m, fd), FrameSlots::DEFAULT);
        assert_eq!(FrameSlots::DEFAULT.formal_offset(), 3);
        assert_eq!(
            this_param_index(&m, fd),
            Some(2),
            "0xF default: [func][new.target][this] → this at params[2]"
        );
    }

    #[test]
    fn annotation_without_newtarget_shifts_this() {
        let mut m = bare_module();
        let f = bare_func(&mut m, 2);
        add_call_type(&mut m, f, 0b1001); // func + this, no new.target
        let fd = &m.functions[f.index()];
        assert!(FrameSlots::from_call_type_annotation(&m, fd).is_some());
        assert_eq!(this_param_index(&m, fd), Some(1));
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

    #[test]
    fn static_arkts_static_method_has_zero_hidden_slots() {
        let mut m = bare_module();
        let ark_cls = add_class_with_lang(&mut m, "LArkPkg/ETSGLOBAL;", SourceLang::ArkTS);
        let f = bare_func_in_class(&mut m, ark_cls, Modifiers::STATIC, 2);
        let fd = &m.functions[f.index()];

        assert_eq!(m.func_dialect(fd), Dialect::StaticArkTS);
        let slots = FrameSlots::of(&m, fd);
        assert_eq!(slots, FrameSlots::NONE);
        assert_eq!(slots.implicit_count(), 0);
        assert_eq!(slots.formal_offset(), 0);
        assert_eq!(slots.this_index(), None);
        assert_eq!(this_param_index(&m, fd), None);
    }

    #[test]
    fn static_arkts_instance_method_binds_this_at_params_0() {
        let mut m = bare_module();
        let ark_cls = add_class_with_lang(&mut m, "LArkPkg/Widget;", SourceLang::ArkTS);
        let inst_fn = bare_func_in_class(&mut m, ark_cls, Modifiers::PUBLIC, 2);
        let fd = &m.functions[inst_fn.index()];

        let slots = FrameSlots::of(&m, fd);
        assert_eq!(slots, FrameSlots::STATIC_INSTANCE);
        assert!(!slots.func);
        assert!(!slots.new_target);
        assert!(slots.this);
        assert_eq!(slots.implicit_count(), 1);
        assert_eq!(slots.formal_offset(), 1);
        assert_eq!(this_param_index(&m, fd), Some(0));

        // Malformed 0-param instance method safely returns None instead of panicking.
        let bad = bare_func_in_class(&mut m, ark_cls, Modifiers::PUBLIC, 0);
        assert_eq!(this_param_index(&m, &m.functions[bad.index()]), None);
    }

    #[test]
    fn dynamic_ecmascript_and_typescript_keep_3_hidden_slots_even_when_static() {
        let mut m = bare_module();
        let es_cls = add_class_with_lang(&mut m, "L_GLOBAL;", SourceLang::EcmaScript);
        let ts_cls = add_class_with_lang(&mut m, "LTsMod;", SourceLang::TypeScript);
        let es_fn = bare_func_in_class(&mut m, es_cls, Modifiers::STATIC, 4);
        let ts_fn = bare_func_in_class(&mut m, ts_cls, Modifiers::STATIC, 3);

        for fid in [es_fn, ts_fn] {
            let fd = &m.functions[fid.index()];
            assert_eq!(m.func_dialect(fd), Dialect::DynamicEcma);
            assert_eq!(FrameSlots::of(&m, fd), FrameSlots::DEFAULT);
            assert_eq!(this_param_index(&m, fd), Some(2));
        }
    }
}
