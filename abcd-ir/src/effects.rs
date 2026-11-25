//! First-class per-op effects (`design/ir.md`, requirement T3;
//! `design/decisions.md` N48/N50, R2-D2).
//!
//! [`Op::effects`] provides the conservative mechanical baseline for untyped
//! dynamic JS/TS (modeling `ToNumeric`/`ToPrimitive`/`ToPropertyKey` coercion
//! and global accessor setters), while [`Op::effects_in`] refines compute ops
//! (`UnaryOp`, `BinaryOp`, `Compare`) to [`Effects::PURE`] whenever operands
//! are proven coercion-free and non-throwing via [`Ty`] or [`crate::ConstPool`].

use crate::consts::Const;
use crate::function::ValueDef;
use crate::id::{Sym, ValueId};
use crate::module::Module;
use crate::op::{BinOp, CmpOp, ModuleVarKind, Op, UnOp};
use crate::ty::{DynPrim, StaticTy, Ty};

/// A set of memory classes an op may read or write.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct MemClasses(u8);

impl MemClasses {
    /// No memory.
    pub const NONE: Self = Self(0);
    /// Object properties / elements (the JS heap).
    pub const HEAP: Self = Self(1 << 0);
    /// Lexical environments (scope slots).
    pub const LEX_ENV: Self = Self(1 << 1);
    /// Global bindings.
    pub const GLOBAL: Self = Self(1 << 2);
    /// Module-variable slots.
    pub const MODULE: Self = Self(1 << 3);
    /// Iterator/generator internal state.
    pub const ITERATOR: Self = Self(1 << 4);
    /// Prototype chains.
    pub const PROTOTYPE: Self = Self(1 << 5);
    /// Every class.
    pub const ALL: Self = Self(0x3F);

    /// Whether `other` is fully contained in this set.
    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Union of two sets.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Whether the set is empty.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl std::ops::BitOr for MemClasses {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

/// Whether (and what) an op may call.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CallEffect {
    /// Cannot call anything.
    #[default]
    None,
    /// May call an unknown callee (getters/setters, Proxy traps, coercion,
    /// protocol methods, or a genuine call).
    UnknownCallee,
    /// May call a callee that has a registered external summary (T6).
    KnownSummary(Sym),
    /// May call the containing function (direct recursion).
    SelfRecursive,
}

/// What an op may allocate (T7 — allocation sites are unique ops; the
/// [`InstId`](crate::id::InstId) of the instruction is the allocation-site identity).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum AllocKind {
    /// Allocates nothing.
    #[default]
    None,
    /// A plain object (also namespace/iterator-result wrapper objects).
    Object,
    /// An array.
    Array,
    /// A closure.
    Closure,
    /// A RegExp.
    RegExp,
    /// An iterator / property-name iterator record.
    Iterator,
    /// A generator object.
    GeneratorObj,
    /// May allocate arbitrary objects (calls, dynamic import).
    Unknown,
}

/// The effect record of one op (`design/ir.md`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Effects {
    /// Memory classes read.
    pub reads: MemClasses,
    /// Memory classes written.
    pub writes: MemClasses,
    /// Whether the op may throw (including conditional throws).
    pub may_throw: bool,
    /// Whether (and what) the op may call.
    pub may_call: CallEffect,
    /// What the op may allocate.
    pub allocs: AllocKind,
}

impl Effects {
    /// No effects at all.
    pub const PURE: Self = Self {
        reads: MemClasses::NONE,
        writes: MemClasses::NONE,
        may_throw: false,
        may_call: CallEffect::None,
        allocs: AllocKind::None,
    };

    /// Whether the op has zero memory reads/writes, cannot throw, cannot call,
    /// and allocates nothing (`*self == Self::PURE`). For DCE eligibility of
    /// unused reads or fresh allocations, see [`Self::is_removable_if_unused`].
    #[must_use]
    pub fn is_pure(&self) -> bool {
        *self == Self::PURE
    }

    /// Whether an instruction with these effects may be removed by DCE when its
    /// SSA result is unused (no writes, cannot throw, and cannot call).
    #[must_use]
    pub const fn is_removable_if_unused(&self) -> bool {
        self.writes.is_empty() && !self.may_throw && matches!(self.may_call, CallEffect::None)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrimKind {
    Dyn(DynPrim),
    Static(StaticTy),
}

fn proven_const(module: &Module, v: ValueId) -> Option<&Const> {
    let val = module.value(v)?;
    match val.def {
        ValueDef::Const(cid) => module.consts.get(cid),
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(cid) => module.consts.get(*cid),
            _ => None,
        },
        _ => None,
    }
}

fn proven_prim(module: &Module, v: ValueId) -> Option<PrimKind> {
    let val = module.value(v)?;
    match &val.ty {
        Ty::DynPrim(p) => return Some(PrimKind::Dyn(*p)),
        Ty::Static(s) => return Some(PrimKind::Static(*s)),
        _ => {}
    }
    match proven_const(module, v)? {
        Const::Undefined => Some(PrimKind::Dyn(DynPrim::Undefined)),
        Const::Null | Const::LitNull(_) => Some(PrimKind::Dyn(DynPrim::Null)),
        Const::Bool(_) => Some(PrimKind::Dyn(DynPrim::Bool)),
        Const::Number(_) => Some(PrimKind::Dyn(DynPrim::Number)),
        Const::Float32(_) => Some(PrimKind::Static(StaticTy::F32)),
        Const::Int8(_) => Some(PrimKind::Static(StaticTy::U8)),
        Const::Int32(_) => Some(PrimKind::Static(StaticTy::I32)),
        Const::String(_) => Some(PrimKind::Dyn(DynPrim::String)),
        Const::BigInt(_) => Some(PrimKind::Dyn(DynPrim::BigInt)),
        Const::Int64(_) => Some(PrimKind::Static(StaticTy::I64)),
        Const::UInt64(_) => Some(PrimKind::Static(StaticTy::U64)),
        Const::Hole
        | Const::Accessor(_)
        | Const::MethodAffiliate(_)
        | Const::BuiltinTypeIndex(_)
        | Const::EtsImplements(_)
        | Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::LiteralBufferRef(_)
        | Const::MethodRef { .. } => None,
    }
}

const fn is_js_num_like(p: DynPrim) -> bool {
    matches!(
        p,
        DynPrim::Number | DynPrim::Bool | DynPrim::Null | DynPrim::Undefined
    )
}

const fn is_static_int(s: StaticTy) -> bool {
    matches!(
        s,
        StaticTy::I8
            | StaticTy::U8
            | StaticTy::I16
            | StaticTy::U16
            | StaticTy::I32
            | StaticTy::U32
            | StaticTy::I64
            | StaticTy::U64
    )
}

const fn is_static_float_or_bool(s: StaticTy) -> bool {
    matches!(s, StaticTy::U1 | StaticTy::F32 | StaticTy::F64)
}

fn is_nonzero_const(module: &Module, v: ValueId) -> bool {
    match proven_const(module, v) {
        Some(Const::Int8(n)) => *n != 0,
        Some(Const::Int32(n)) => *n != 0,
        Some(Const::Int64(n)) => *n != 0,
        Some(Const::UInt64(n)) => *n != 0,
        Some(Const::Number(bits)) => {
            let f = f64::from_bits(*bits);
            f.is_finite() && f != 0.0 && (f as i64) != 0
        }
        _ => false,
    }
}

impl Op {
    /// Conservative baseline effects derived from the op alone (T3, `R2-D2`).
    /// Dynamic compute ops (`BinaryOp`, coercing `UnaryOp`, non-strict
    /// `Compare`) conservatively report heap coercion / `may_throw` /
    /// `UnknownCallee`; use [`Op::effects_in`] when [`Module`] value types or
    /// constants are available.
    #[must_use]
    pub fn effects(&self) -> Effects {
        use crate::op::Op::*;
        let reads = |reads: MemClasses| Effects {
            reads,
            ..Effects::PURE
        };
        let writes = |writes: MemClasses| Effects {
            writes,
            ..Effects::PURE
        };
        let coercion = Effects {
            reads: MemClasses::HEAP,
            writes: MemClasses::HEAP,
            may_throw: true,
            may_call: CallEffect::UnknownCallee,
            allocs: AllocKind::None,
        };
        match self {
            Mov { .. }
            | LoadConst(_)
            | Phi { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Unreachable
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction => Effects::PURE,

            UnaryOp { op, .. } => match op {
                UnOp::LogicalNot
                | UnOp::IsTrue
                | UnOp::IsFalse
                | UnOp::JumpEqz
                | UnOp::JumpNez
                | UnOp::TypeOf
                | UnOp::Void => Effects::PURE,
                UnOp::Minus
                | UnOp::BitNot
                | UnOp::Inc
                | UnOp::Dec
                | UnOp::ToNumber
                | UnOp::ToNumeric
                | UnOp::ToPropertyKey => coercion,
            },
            BinaryOp { .. } => coercion,
            Compare { op, .. } => match op {
                CmpOp::StrictEq | CmpOp::StrictNotEq => Effects::PURE,
                CmpOp::Eq
                | CmpOp::NotEq
                | CmpOp::Less
                | CmpOp::LessEq
                | CmpOp::Greater
                | CmpOp::GreaterEq => coercion,
                CmpOp::In | CmpOp::InstanceOf => Effects {
                    reads: MemClasses::HEAP.union(MemClasses::PROTOTYPE),
                    writes: MemClasses::HEAP,
                    may_throw: true,
                    may_call: CallEffect::UnknownCallee,
                    allocs: AllocKind::None,
                },
            },

            // Vendor `asyncfunctionenter`: allocates the async context/promise,
            // still removable when unused via `Effects::is_removable_if_unused`.
            AsyncFunctionEnter => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },

            // Allocation sites (T7).
            AllocObject { .. }
            | GetUnmappedArgs
            | CreateIterResultObj { .. }
            | CreateAsyncGenerator { .. } => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            AllocArray { .. } | CopyRestArgs { .. } => Effects {
                allocs: AllocKind::Array,
                ..Effects::PURE
            },
            AllocRegExp { .. } => Effects {
                allocs: AllocKind::RegExp,
                may_throw: true,
                ..Effects::PURE
            },
            AllocClosure { .. } => Effects {
                allocs: AllocKind::Closure,
                ..Effects::PURE
            },
            CreateGenerator { .. } => Effects {
                allocs: AllocKind::GeneratorObj,
                ..Effects::PURE
            },
            GetTemplateObject { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },

            // Property access (T2/T3).
            LoadProp { .. } | LoadPropDyn { .. } | LoadSuper { .. } | TestProp { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            LoadPropIdx { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            StoreProp { .. }
            | StorePropDyn { .. }
            | StoreSuper { .. }
            | StorePropIdx { .. }
            | DeleteProp { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            StoreOwnPropName { .. } | StoreOwnPropIdx { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                ..Effects::PURE
            },
            // Computed key triggers ToPropertyKey on object keys (`R2-M3`).
            StoreOwnPropDyn { .. } | DefineGetterSetterByValue { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            DefineMethod { .. } => Effects {
                reads: MemClasses::HEAP,
                writes: MemClasses::HEAP,
                may_throw: true,
                allocs: AllocKind::Closure,
                ..Effects::PURE
            },
            CopyDataProps { .. } => Effects {
                reads: MemClasses::HEAP,
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            SetObjectWithProto { .. } => Effects {
                writes: MemClasses::PROTOTYPE,
                may_throw: true,
                ..Effects::PURE
            },
            ArraySpread { .. } => Effects {
                reads: MemClasses::ITERATOR | MemClasses::HEAP,
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            CreateObjectWithExcludedKeys { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },

            // Iteration protocol (`R2-M1`).
            GetIterator { .. } | GetAsyncIterator { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            GetPropIterator { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE,
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // Proxy `ownKeys` trap
                allocs: AllocKind::Iterator,
            },
            IteratorNext { .. } | IteratorReturn { .. } | IteratorThrow { .. } => Effects {
                reads: MemClasses::ITERATOR | MemClasses::HEAP,
                writes: MemClasses::ITERATOR,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            NextPropName { .. } => Effects {
                reads: MemClasses::ITERATOR | MemClasses::HEAP,
                writes: MemClasses::ITERATOR,
                may_throw: true,
                ..Effects::PURE
            },

            // Lexical / global / module bindings (`R2-H3`, `R2-M4`).
            GetLexVar { .. } => reads(MemClasses::LEX_ENV),
            NewLexEnv { .. } | NewLexEnvWithName { .. } | PopLexEnv | PutLexVar { .. } => {
                writes(MemClasses::LEX_ENV)
            }
            TryGetGlobal { .. } => Effects {
                reads: MemClasses::GLOBAL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            // Both `stglobalvar` (`StoreGlobal`) and `trystglobalbyname`
            // (`TryStoreGlobal`) invoke global accessor setters; `trystglobalbyname`
            // additionally throws `ReferenceError` when the binding is absent (`R2-H3`).
            StoreGlobal { .. } | TryStoreGlobal { .. } => Effects {
                reads: MemClasses::GLOBAL,
                writes: MemClasses::GLOBAL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            StoreGlobalRecord { .. } => Effects {
                writes: MemClasses::GLOBAL,
                may_throw: true,
                ..Effects::PURE
            },
            LoadModuleVar { kind, .. } if kind.is_lazy() => Effects {
                reads: MemClasses::ALL,
                writes: MemClasses::ALL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Unknown,
            },
            LoadModuleVar {
                kind: ModuleVarKind::SendableClass,
                ..
            } => reads(MemClasses::MODULE.union(MemClasses::LEX_ENV)),
            LoadModuleVar { .. } => reads(MemClasses::MODULE),
            StoreModuleVar { .. } => writes(MemClasses::MODULE),
            GetModuleNamespace { .. } => Effects {
                reads: MemClasses::MODULE,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            DynamicImport { .. } => Effects {
                reads: MemClasses::MODULE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Unknown,
                ..Effects::PURE
            },

            // Calls / definitions (T4, `R2-M2`).
            Call { .. } => Effects {
                reads: MemClasses::ALL,
                writes: MemClasses::ALL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Unknown,
            },
            DefineFunc { .. } => reads(MemClasses::LEX_ENV),
            DefineClass(_) | DefineSendableClass(_) => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE | MemClasses::LEX_ENV,
                writes: MemClasses::HEAP | MemClasses::PROTOTYPE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object,
            },

            // Private properties (`R2-M2`).
            LoadPrivate { .. } | TestPrivate { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::LEX_ENV,
                may_throw: true,
                ..Effects::PURE
            },
            StorePrivate { .. } | DefinePrivate { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::LEX_ENV,
                writes: MemClasses::HEAP,
                may_throw: true,
                ..Effects::PURE
            },
            CreatePrivateNames { .. } => writes(MemClasses::LEX_ENV),

            // Exceptions.
            Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty => Effects {
                may_throw: true,
                ..Effects::PURE
            },

            Debugger => Effects {
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },

            // Generator / async suspension: while suspended (`SuspendGenerator`,
            // `Await`, `AwaitUncaught`), arbitrary host/caller JS may run before
            // resumption (`may_call: UnknownCallee` acts as the memory clobber
            // barrier for analyses; `ResumeGenerator` reads the saved resume
            // value from the generator object in `ecmascript`).
            SuspendGenerator { .. } | ResumeGenerator { .. } => Effects {
                reads: MemClasses::ITERATOR,
                writes: MemClasses::ITERATOR,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            GetResumeMode { .. } => reads(MemClasses::ITERATOR),
            SetGeneratorState { .. } => writes(MemClasses::HEAP),
            LoadSymbol => reads(MemClasses::GLOBAL),
            NotifyConcurrentResult { .. } => writes(MemClasses::GLOBAL),
            Await { .. } | AwaitUncaught { .. } => Effects {
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            AsyncGeneratorResolve { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::GLOBAL,
                writes: MemClasses::HEAP | MemClasses::GLOBAL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            AsyncResolve { .. } | AsyncReject { .. } | AsyncGeneratorReject { .. } => Effects {
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
        }
    }

    /// Context-sensitive effect query (`R2-D2`): refines [`Op::effects`] to
    /// [`Effects::PURE`] on `UnaryOp`, `BinaryOp`, and non-brand `Compare`
    /// whenever operand types or constant definitions in `module` rule out
    /// object coercion (`valueOf`/`toString`/`@@toPrimitive`) and runtime
    /// exceptions (such as `Symbol` numeric coercion or `BigInt` division by zero).
    #[must_use]
    pub fn effects_in(&self, module: &Module) -> Effects {
        match self {
            Op::UnaryOp { op, operand } => {
                let base = self.effects();
                if base.is_pure() {
                    return Effects::PURE;
                }
                match (op, proven_prim(module, *operand)) {
                    (
                        UnOp::ToPropertyKey,
                        Some(PrimKind::Dyn(
                            DynPrim::String | DynPrim::Symbol | DynPrim::Number | DynPrim::Bool,
                        )),
                    ) => Effects::PURE,
                    (UnOp::ToPropertyKey, Some(PrimKind::Static(s)))
                        if is_static_float_or_bool(s) || is_static_int(s) =>
                    {
                        Effects::PURE
                    }
                    (_, Some(PrimKind::Dyn(p)))
                        if *op != UnOp::ToPropertyKey
                            && (is_js_num_like(p) || p == DynPrim::String) =>
                    {
                        Effects::PURE
                    }
                    (_, Some(PrimKind::Static(s)))
                        if *op != UnOp::ToPropertyKey
                            && (is_static_float_or_bool(s) || is_static_int(s)) =>
                    {
                        Effects::PURE
                    }
                    _ => base,
                }
            }
            Op::BinaryOp { op, left, right } => {
                match (proven_prim(module, *left), proven_prim(module, *right)) {
                    (Some(PrimKind::Dyn(l)), Some(PrimKind::Dyn(r))) => {
                        let both_num_like = is_js_num_like(l) && is_js_num_like(r);
                        let safe_add = *op == BinOp::Add
                            && (is_js_num_like(l) || l == DynPrim::String)
                            && (is_js_num_like(r) || r == DynPrim::String);
                        if both_num_like || safe_add {
                            Effects::PURE
                        } else {
                            self.effects()
                        }
                    }
                    (Some(PrimKind::Static(l)), Some(PrimKind::Static(r))) => {
                        if is_static_float_or_bool(l) && is_static_float_or_bool(r) {
                            Effects::PURE
                        } else if is_static_int(l) && is_static_int(r) {
                            if matches!(op, BinOp::Div | BinOp::Mod)
                                && !is_nonzero_const(module, *right)
                            {
                                self.effects()
                            } else {
                                Effects::PURE
                            }
                        } else {
                            self.effects()
                        }
                    }
                    _ => self.effects(),
                }
            }
            Op::Compare { op, left, right } => {
                if matches!(op, CmpOp::StrictEq | CmpOp::StrictNotEq) {
                    return Effects::PURE;
                }
                if matches!(op, CmpOp::In | CmpOp::InstanceOf) {
                    return self.effects();
                }
                let is_cmp_safe = |k: PrimKind| match k {
                    PrimKind::Dyn(p) => {
                        is_js_num_like(p) || matches!(p, DynPrim::String | DynPrim::BigInt)
                    }
                    PrimKind::Static(s) => is_static_float_or_bool(s) || is_static_int(s),
                };
                match (proven_prim(module, *left), proven_prim(module, *right)) {
                    (Some(l), Some(r)) if is_cmp_safe(l) && is_cmp_safe(r) => Effects::PURE,
                    _ => self.effects(),
                }
            }
            _ => self.effects(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function::Value;
    use crate::id::{BlockId, ConstId, ValueId};
    use crate::op::CallKind;

    #[test]
    fn effects_spot_table_and_refinement() {
        let v = ValueId::new(0);
        let name = Sym::new(0);

        assert_eq!(Op::LoadConst(ConstId::new(0)).effects(), Effects::PURE);
        assert_eq!(
            Op::Branch {
                dest: BlockId::new(0)
            }
            .effects(),
            Effects::PURE
        );

        // Untyped BinaryOp is conservative; StrictEq and LogicalNot are pure.
        let add_untyped = Op::BinaryOp {
            op: BinOp::Add,
            left: v,
            right: v,
        }
        .effects();
        assert!(add_untyped.may_throw);
        assert_eq!(add_untyped.may_call, CallEffect::UnknownCallee);
        assert_eq!(
            Op::Compare {
                op: CmpOp::StrictEq,
                left: v,
                right: v,
            }
            .effects(),
            Effects::PURE
        );
        assert_eq!(
            Op::UnaryOp {
                op: UnOp::LogicalNot,
                operand: v,
            }
            .effects(),
            Effects::PURE
        );

        // AsyncFunctionEnter allocates Object, removable when unused.
        let afe = Op::AsyncFunctionEnter.effects();
        assert_eq!(afe.allocs, AllocKind::Object);
        assert!(!afe.is_pure());
        assert!(afe.is_removable_if_unused());

        // StoreGlobal & TryStoreGlobal both read/write GLOBAL, may_throw, may_call.
        for op in [
            Op::StoreGlobal { name, value: v },
            Op::TryStoreGlobal { name, value: v },
        ] {
            let e = op.effects();
            assert!(e.reads.contains(MemClasses::GLOBAL));
            assert!(e.writes.contains(MemClasses::GLOBAL));
            assert!(e.may_throw);
            assert_eq!(e.may_call, CallEffect::UnknownCallee);
        }

        // Typed/constant refinement via effects_in.
        let mut m = Module::new();
        let c1 = m.consts.push(Const::number(2.0));
        let v_num = ValueId::new(0);
        m.values.push(Value {
            def: ValueDef::Const(c1),
            ty: Ty::Any,
        });
        let v_sym = ValueId::new(1);
        m.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::DynPrim(DynPrim::Symbol),
        });
        assert_eq!(
            Op::BinaryOp {
                op: BinOp::Add,
                left: v_num,
                right: v_num,
            }
            .effects_in(&m),
            Effects::PURE
        );
        assert!(
            Op::BinaryOp {
                op: BinOp::Add,
                left: v_num,
                right: v_sym,
            }
            .effects_in(&m)
            .may_throw
        );

        // Call touches everything.
        let e = Op::Call {
            callee: v,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        }
        .effects();
        assert_eq!(e.reads, MemClasses::ALL);
        assert_eq!(e.writes, MemClasses::ALL);
        assert!(e.may_throw);
    }

    #[test]
    fn effects_cover_observable_loads() {
        let v = ValueId::new(0);
        let name = Sym::new(0);
        let cases = [
            Op::GetIterator { obj: v },
            Op::GetAsyncIterator { obj: v },
            Op::GetPropIterator { obj: v },
            Op::NextPropName { iterator: v },
            Op::LoadProp { object: v, name },
            Op::LoadPropDyn { object: v, key: v },
            Op::LoadPropIdx {
                object: v,
                index: v,
            },
            Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: v,
            },
            Op::TestPrivate {
                level: 0,
                slot: 0,
                obj: v,
            },
            Op::AllocRegExp {
                pattern: name,
                flags: 0,
            },
            // `ldglobalvar` (`default: None`) throws ReferenceError on missing binding
            // and calls getters; `tryldglobalbyname` (`default: Some`) tolerates
            // absence (`undefined`) yet still calls prototype getters (`N48`/`N50`).
            Op::TryGetGlobal {
                name,
                default: None,
            },
            Op::TryGetGlobal {
                name,
                default: Some(v),
            },
            Op::LoadSuper {
                key: crate::op::SuperKey::Name(name),
                this_value: v,
            },
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Lazy,
            },
        ];
        for op in cases {
            assert!(
                !op.effects().is_removable_if_unused(),
                "observable load must NOT be removable if unused: {op:?}"
            );
        }

        // Pure reads and non-throwing allocations stay removable when unused.
        for op in [
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: crate::op::LexEnvKind::Plain,
            },
            Op::LoadSymbol,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::SendableClass,
            },
            Op::GetResumeMode { genobj: v },
            Op::AllocObject {
                shape: ConstId::new(0),
            },
            Op::AllocArray { shape: None },
            Op::AllocClosure { func: v },
            Op::CreateAsyncGenerator { func: v },
            Op::AsyncFunctionEnter,
        ] {
            assert!(
                op.effects().is_removable_if_unused(),
                "pure read/alloc must stay removable if unused: {op:?}"
            );
        }
    }
}
