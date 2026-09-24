//! First-class per-op effects (design/ir-v0.2.md §4.2, requirement T3).
//!
//! [`Op::effects`] is computed mechanically from the op itself plus its
//! operand *shapes* — never hand-maintained per pass. This table is the
//! single source of truth that replaces v0.1's `is_essential` hand list
//! (N48/N50): DCE, reordering, and taint propagation all read effects
//! from here.
//!
//! Modelling notes (deliberate, documented):
//!
//! - JS coercion side effects of the dynamic compute ops (`BinaryOp`,
//!   `UnaryOp`, `Compare` can invoke `valueOf`/`toString` on object
//!   operands) are NOT modeled at the op level: the op alone cannot know
//!   its operands' types (`ty` lives on values, not ops — §4.1). A
//!   type-refined effect *refinement* (object-typed operand ⇒ may call)
//!   is an analysis-layer extension over this baseline, not more entries
//!   in this table.
//! - [`CallEffect::KnownSummary`] and [`CallEffect::SelfRecursive`] are
//!   produced by refinement (a callee-resolving analysis rewrites
//!   `UnknownCallee`); the mechanical derivation only ever emits
//!   `UnknownCallee` for call-capable ops.

use crate::id::Sym;
use crate::op::Op;

/// A set of memory classes an op may read or write.
///
/// Memory is classified by *what is being accessed*, not by monolithic
/// "the heap" (the Hermes `Unknown` collapse this design explicitly
/// avoids — §6.3): field-sensitive taint tracks [`MemClasses::HEAP`]
/// separately from lexical/global/module bindings.
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
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Union of two sets.
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Whether the set is empty.
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    const NAMES: [(MemClasses, &str); 6] = [
        (Self::HEAP, "heap"),
        (Self::LEX_ENV, "lexenv"),
        (Self::GLOBAL, "global"),
        (Self::MODULE, "module"),
        (Self::ITERATOR, "iterator"),
        (Self::PROTOTYPE, "prototype"),
    ];
}

impl std::ops::BitOr for MemClasses {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

impl std::ops::BitOrAssign for MemClasses {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.union(rhs);
    }
}

impl std::fmt::Display for MemClasses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (class, name) in Self::NAMES {
            if self.contains(class) {
                if !first {
                    write!(f, "|")?;
                }
                write!(f, "{name}")?;
                first = false;
            }
        }
        if first {
            write!(f, "none")?;
        }
        Ok(())
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
    /// May call a callee that has a registered external summary (T6);
    /// produced by refinement, keyed by the summary's symbol.
    KnownSummary(Sym),
    /// May call the containing function (direct recursion); produced by
    /// refinement.
    SelfRecursive,
}

/// What an op may allocate (T7 — allocation sites are unique ops; the
/// [`InstId`](crate::id::InstId) of the instruction is the
/// allocation-site identity).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum AllocKind {
    /// Allocates nothing.
    #[default]
    None,
    /// A plain object (also namespace/iterator wrapper objects).
    Object,
    /// An array.
    Array,
    /// A closure.
    Closure,
    /// A RegExp.
    RegExp,
    /// A generator object.
    GeneratorObj,
    /// May allocate arbitrary objects (calls, dynamic import) — the
    /// conservative over-approximation of "any of the above".
    Unknown,
}

/// The effect record of one op (§4.2).
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

    /// Whether the op has no observable effect (DCE-eligible when its
    /// result is unused).
    pub fn is_pure(&self) -> bool {
        *self == Self::PURE
    }
}

impl Op {
    /// The op's effects, mechanically derived from the taxonomy (T3).
    /// This is the single source of effect truth; passes must not
    /// hand-maintain their own lists.
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
        let rw = |mem: MemClasses| Effects {
            reads: mem,
            writes: mem,
            ..Effects::PURE
        };
        match self {
            // Pure compute / value flow / control. (Coercion effects of
            // dynamic operators are a type-refined extension — see module
            // docs.)
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | Phi { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Unreachable => Effects::PURE,

            // Frame-state loads: pure reads of the physical frame (vendor
            // `acc: out:top`, no memory interaction).
            LoadNewTarget | LoadGlobalObject | LoadFunction => Effects::PURE,

            // Vendor `asyncfunctionenter`: v0.1's proven DCE contract
            // treats it as non-essential (dead-deletable when the result
            // is unused) — modeled PURE to preserve that behavior.
            AsyncFunctionEnter => Effects::PURE,

            // Allocation sites (T7).
            AllocObject { .. } => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            AllocArray { .. } => Effects {
                allocs: AllocKind::Array,
                ..Effects::PURE
            },
            AllocRegExp { .. } => Effects {
                allocs: AllocKind::RegExp,
                may_throw: true, // invalid pattern/flags
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
            // The unmapped `arguments` exotic object.
            GetUnmappedArgs => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            // The rest-args array.
            CopyRestArgs { .. } => Effects {
                allocs: AllocKind::Array,
                ..Effects::PURE
            },
            // The iterator result object `{ value, done }`.
            CreateIterResultObj { .. } => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            // Vendor `gettemplateobject` (isa.yaml:1279-1283): reads the
            // template-object cache and allocates the (cached) template
            // object on first call; the vendored handler is
            // abrupt-checked (`INTERPRETER_RETURN_IF_ABRUPT`,
            // interpreter_assembly.cpp:2079-2082).
            GetTemplateObject { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },

            // Property access (T2/T3): getters/setters/Proxy traps may
            // run arbitrary code.
            LoadProp { .. } | LoadPropDyn { .. } => Effects {
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
            StoreProp { .. } | StorePropDyn { .. } | StoreSuper { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            StorePropIdx { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            // Own-property DEFINITION (vendor stownby*/definefieldby*/
            // definepropertybyname): CreateDataProperty semantics — no
            // setters and no prototype-chain walk, so NO may_call
            // (mirrors DefineMethod/DefineGetterSetterByValue); throws
            // like defineproperty (define-on-non-extensible /
            // non-configurable redefinition failure).
            StoreOwnPropName { .. } | StoreOwnPropDyn { .. } | StoreOwnPropIdx { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                ..Effects::PURE
            },
            LoadSuper { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            DefineMethod { .. } => writes(MemClasses::HEAP),
            DeleteProp { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,                     // strict-mode delete failures
                may_call: CallEffect::UnknownCallee, // Proxy deleteProperty trap
                ..Effects::PURE
            },
            TestProp { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // Proxy has trap
                ..Effects::PURE
            },
            CopyDataProps { .. } => Effects {
                reads: MemClasses::HEAP,
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // source getters
                ..Effects::PURE
            },
            // Prototype-link mutation (vendor `setobjectwithproto`,
            // isa.yaml:1333-1337): NOT a property copy — writes the
            // object's prototype link directly.
            SetObjectWithProto { .. } => Effects {
                writes: MemClasses::PROTOTYPE,
                may_throw: true, // cyclic prototype chain
                ..Effects::PURE
            },
            // Vendor `starrayspread` (isa.yaml:1329-1332): drives the
            // source's iterator protocol and mutates the destination
            // array; the new-index result is the acc write-back.
            ArraySpread { .. } => Effects {
                reads: MemClasses::ITERATOR | MemClasses::HEAP,
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // iterator protocol
                ..Effects::PURE
            },
            // Rest destructuring (`createobjectwithexcludedkeys`): copies
            // the source's own enumerable properties except the excluded
            // keys into a FRESH object — a heap read plus an allocation;
            // the copy invokes getters (CopyDataProperties semantics).
            CreateObjectWithExcludedKeys { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            // Accessor definition on an object
            // (`definegettersetterbyvalue`): defines the property — the
            // closures are installed, not invoked.
            DefineGetterSetterByValue { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true,
                ..Effects::PURE
            },

            // Iteration protocol.
            GetIterator { .. } => Effects {
                reads: MemClasses::HEAP, // @@iterator lookup
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object, // the iterator record
                ..Effects::PURE
            },
            GetAsyncIterator { .. } => Effects {
                reads: MemClasses::HEAP, // @@asyncIterator lookup
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Object, // the iterator record
                ..Effects::PURE
            },
            GetPropIterator { .. } => Effects {
                allocs: AllocKind::Object,
                ..Effects::PURE
            },
            IteratorNext { .. } | IteratorReturn { .. } | IteratorThrow { .. } => Effects {
                reads: MemClasses::ITERATOR | MemClasses::HEAP,
                writes: MemClasses::ITERATOR,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // next/return/throw methods
                ..Effects::PURE
            },
            NextPropName { .. } => rw(MemClasses::ITERATOR),

            // Lexical / global / module bindings.
            GetLexVar { .. } => reads(MemClasses::LEX_ENV),
            // Lexical-environment lifecycle: pushing/popping an
            // environment mutates the scope stack (v0.1 essential).
            NewLexEnv { .. } | NewLexEnvWithName { .. } | PopLexEnv => writes(MemClasses::LEX_ENV),
            PutLexVar { .. } => writes(MemClasses::LEX_ENV),
            TryGetGlobal { .. } => Effects {
                reads: MemClasses::GLOBAL,
                // N48/N50: BOTH source forms (v0.1 `LoadGlobalVar` =
                // `ldglobalvar`, `TryLoadGlobalByName` =
                // `tryldglobalbyname`) were ADCE-essential — a dead
                // result does not make the load dead. Vendor grounding:
                // both handlers' slow paths run
                // `JSTaggedValue::GetProperty` on the global's prototype
                // chain, CALLING global getters, and abrupt-check the
                // result (RuntimeStubs::RuntimeLdGlobalVarFromProto,
                // stubs/runtime_stubs-inl.h:1782-1793 via
                // SlowRuntimeStub::LdGlobalVarFromGlobalProto;
                // RuntimeStubs::RuntimeTryLdGlobalByName,
                // :1739-1748 via
                // SlowRuntimeStub::TryLdGlobalByNameFromGlobalProto,
                // interpreter/slow_runtime_stub.cpp; INTERPRETER_RETURN_
                // IF_ABRUPT in both handlers, interpreter_assembly.cpp
                // :2425/:2611). The try form additionally raises
                // ReferenceError " is not defined" on a miss.
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            StoreGlobal { .. } => Effects {
                writes: MemClasses::GLOBAL,
                may_throw: true, // unresolved reference in strict mode
                ..Effects::PURE
            },
            // Vendor `trystglobalbyname`: the TOLERANT store — no
            // ReferenceError when the global is absent (mirrors
            // TryGetGlobal's "never throws").
            TryStoreGlobal { .. } => writes(MemClasses::GLOBAL),
            LoadModuleVar { .. } => reads(MemClasses::MODULE),
            StoreModuleVar { .. } => writes(MemClasses::MODULE),
            GetModuleNamespace { .. } => Effects {
                reads: MemClasses::MODULE,
                allocs: AllocKind::Object, // the namespace exotic object
                ..Effects::PURE
            },
            DynamicImport { .. } => Effects {
                reads: MemClasses::MODULE,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // host hook
                allocs: AllocKind::Unknown,          // the promise
                ..Effects::PURE
            },

            // Calls / definitions (T4).
            Call { .. } => Effects {
                reads: MemClasses::ALL,
                writes: MemClasses::ALL,
                may_throw: true,
                may_call: CallEffect::UnknownCallee,
                allocs: AllocKind::Unknown,
            },
            DefineFunc { .. } => reads(MemClasses::LEX_ENV), // capture env
            DefineClass { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE, // heritage
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // heritage/proto machinery
                allocs: AllocKind::Object,
            },
            // N53: same effect shape as DefineClass — the difference is
            // the runtime stub (CreateSharedClass, shared/sendable
            // machinery vs CreateClassWithBuffer), not the effect
            // classes the IR tracks.
            DefineSendableClass { .. } => Effects {
                reads: MemClasses::HEAP | MemClasses::PROTOTYPE, // heritage
                writes: MemClasses::HEAP,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // heritage/proto machinery
                allocs: AllocKind::Object,
            },

            // Private properties.
            LoadPrivate { .. } | TestPrivate { .. } => Effects {
                reads: MemClasses::HEAP,
                may_throw: true, // brand check failure
                ..Effects::PURE
            },
            StorePrivate { .. } | DefinePrivate { .. } => Effects {
                writes: MemClasses::HEAP,
                may_throw: true, // brand check / redefinition failure
                ..Effects::PURE
            },
            CreatePrivateNames { .. } => writes(MemClasses::LEX_ENV),

            // Exceptions: conditional or unconditional throws.
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

            // Vendor `debugger`: a breakpoint can invoke the attached
            // debugger's hook — kept non-pure so DCE preserves it (v0.1's
            // is_essential parity).
            Debugger { .. } => Effects {
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },

            // Generator / async protocol.
            SuspendGenerator { .. } => Effects {
                reads: MemClasses::ITERATOR,
                writes: MemClasses::ITERATOR,
                may_throw: true, // resume can throw back in
                may_call: CallEffect::UnknownCallee,
                ..Effects::PURE
            },
            ResumeGenerator { .. } => Effects {
                reads: MemClasses::ITERATOR,
                writes: MemClasses::ITERATOR,
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // runs generator body
                ..Effects::PURE
            },
            GetResumeMode { .. } => reads(MemClasses::ITERATOR),
            Await { .. } | AwaitUncaught { .. } => Effects {
                may_throw: true,
                may_call: CallEffect::UnknownCallee, // thenables
                ..Effects::PURE
            },
            AsyncResolve { .. } | AsyncReject { .. } => Effects {
                may_call: CallEffect::UnknownCallee, // promise reactions
                ..Effects::PURE
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{ConstId, ValueId};
    use crate::op::{BinOp, CallKind};

    /// The §4.2 spot table: pinned effect derivations.
    #[test]
    fn effects_spot_table() {
        let v = ValueId::new(0);
        let name = Sym::new(0);

        // LoadConst is pure.
        assert_eq!(Op::LoadConst(ConstId::new(0)).effects(), Effects::PURE);
        // Compute ops and control flow are pure at the op level.
        assert_eq!(
            Op::BinaryOp {
                op: BinOp::Add,
                left: v,
                right: v
            }
            .effects(),
            Effects::PURE
        );
        assert_eq!(
            Op::Branch {
                dest: crate::id::BlockId::new(0)
            }
            .effects(),
            Effects::PURE
        );

        // LoadProp reads Heap + may call a getter.
        let e = Op::LoadProp { object: v, name }.effects();
        assert!(e.reads.contains(MemClasses::HEAP));
        assert_eq!(e.may_call, CallEffect::UnknownCallee);
        assert!(e.writes.is_empty());
        assert!(!e.is_pure());

        // StoreGlobal writes Global.
        let e = Op::StoreGlobal { name, value: v }.effects();
        assert!(e.writes.contains(MemClasses::GLOBAL));
        assert!(e.reads.is_empty());

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
        assert_eq!(e.may_call, CallEffect::UnknownCallee);
        assert_eq!(e.allocs, AllocKind::Unknown);

        // Allocation sites have distinct kinds (T7).
        assert_eq!(
            Op::AllocArray { shape: None }.effects().allocs,
            AllocKind::Array
        );
        assert_eq!(
            Op::AllocClosure { func: v }.effects().allocs,
            AllocKind::Closure
        );
    }

    /// Every op's effect record is constructible (the match is total —
    /// this test fails to compile if a variant is added without an
    /// effects entry, because `match` on `Op` is exhaustive).
    #[test]
    fn effects_total_over_taxonomy() {
        let e = Op::GetLexVar { level: 0, slot: 0 }.effects();
        assert!(e.reads.contains(MemClasses::LEX_ENV));
        let e = Op::PutLexVar {
            level: 0,
            slot: 0,
            value: ValueId::new(0),
        }
        .effects();
        assert!(e.writes.contains(MemClasses::LEX_ENV));
    }

    /// The v2-P0.5 taxonomy-growth pins: the new ISA-coverage ops carry
    /// the documented effect records.
    #[test]
    fn effects_taxonomy_growth_pins() {
        let v = ValueId::new(0);

        // Lexical-env lifecycle mutates the scope stack.
        for op in [
            Op::NewLexEnv { num_vars: 1 },
            Op::NewLexEnvWithName {
                num_vars: 1,
                scope_names: ConstId::new(0),
            },
            Op::PopLexEnv,
        ] {
            let e = op.effects();
            assert!(e.writes.contains(MemClasses::LEX_ENV), "{op:?}");
        }

        // SetObjectWithProto writes the prototype link, never the heap
        // property space.
        let e = Op::SetObjectWithProto { proto: v, obj: v }.effects();
        assert!(e.writes.contains(MemClasses::PROTOTYPE));
        assert!(!e.writes.contains(MemClasses::HEAP));
        assert!(e.may_throw);

        // ArraySpread: heap mutation + iterator protocol.
        let e = Op::ArraySpread {
            dst: v,
            index: v,
            src: v,
        }
        .effects();
        assert!(e.reads.contains(MemClasses::ITERATOR));
        assert!(e.writes.contains(MemClasses::HEAP));
        assert_eq!(e.may_call, CallEffect::UnknownCallee);

        // GetTemplateObject: cache read + first-call allocation + abrupt.
        let e = Op::GetTemplateObject { literal: v }.effects();
        assert!(e.reads.contains(MemClasses::HEAP));
        assert_eq!(e.allocs, AllocKind::Object);
        assert!(e.may_throw);

        // Frame-state loaders are pure.
        for op in [Op::LoadNewTarget, Op::LoadGlobalObject, Op::LoadFunction] {
            assert!(op.effects().is_pure(), "{op:?}");
        }

        // The exotic allocations.
        assert_eq!(Op::GetUnmappedArgs.effects().allocs, AllocKind::Object);
        assert_eq!(
            Op::CopyRestArgs { start_index: 0 }.effects().allocs,
            AllocKind::Array
        );
        assert_eq!(
            Op::CreateIterResultObj { value: v, done: v }
                .effects()
                .allocs,
            AllocKind::Object
        );

        // The async forms.
        let e = Op::AwaitUncaught {
            funcobj: v,
            value: v,
        }
        .effects();
        assert!(e.may_throw);
        assert_eq!(e.may_call, CallEffect::UnknownCallee);
        assert!(Op::AsyncFunctionEnter.effects().is_pure());

        // The dedicated throw ops throw.
        for op in [
            Op::ThrowUndefinedIfHoleWithName {
                name: Sym::new(0),
                value: v,
            },
            Op::ThrowNotExists,
            Op::ThrowPatternNonCoercible,
            Op::ThrowDeleteSuperProperty,
        ] {
            assert!(op.effects().may_throw, "{op:?}");
        }

        // Debugger stays essential (v0.1 parity) via the hook call effect.
        assert!(!Op::Debugger.effects().is_pure());
    }

    /// N48/N50: every entry of v0.1's ADCE essential OBSERVABLE-LOAD list
    /// must derive non-pure from this table (a write, a possible throw,
    /// or a possible call — the abcd-opt ADCE essentiality rule). The
    /// v0.1 list: GetIterator, GetAsyncIterator, LoadProperty,
    /// LoadPrivateProperty, TestPrivateProperty, CreateRegExp,
    /// LoadGlobalVar, TryLoadGlobalByName, LoadSuperProperty.
    #[test]
    fn effects_cover_v0_1_observable_loads() {
        let v = ValueId::new(0);
        let name = Sym::new(0);
        let essential = |op: Op| {
            let e = op.effects();
            !e.writes.is_empty() || e.may_throw || e.may_call != CallEffect::None
        };
        let cases = [
            Op::GetIterator { obj: v },
            Op::GetAsyncIterator { obj: v },
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
            // LoadGlobalVar (the throwing form) and TryLoadGlobalByName
            // (the tolerant form) BOTH fold to TryGetGlobal.
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
            },
        ];
        for op in cases {
            assert!(
                essential(op.clone()),
                "v0.1-essential observable load must derive non-pure (N48/N50): {op:?}"
            );
        }

        // Control: the pure reads / pure allocations stay dead-deletable
        // (v0.1 parity — they were NOT on the essential list).
        for op in [
            Op::GetLexVar { level: 0, slot: 0 },
            Op::LoadModuleVar { index: 0 },
            Op::GetResumeMode { genobj: v },
            Op::AllocObject {
                shape: ConstId::new(0),
            },
            Op::AllocArray { shape: None },
            Op::AllocClosure { func: v },
            Op::GetPropIterator { obj: v },
        ] {
            assert!(
                !essential(op.clone()),
                "pure read/alloc must stay dead-deletable (v0.1 parity): {op:?}"
            );
        }
    }
}
