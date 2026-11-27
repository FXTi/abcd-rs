//! The 88-variant semantic op taxonomy (`design/ir.md`): **no `Switch`**,
//! and a **single** `LoadPropIdx`/`StorePropIdx`.
//!
//! [`Op`] is a *closed* enum of semantic variants — zero opcode concepts:
//! width variants, typed/dynamic twins, and the call family all fold into
//! this set at lift; encoding selection is a lowering concern.
//!
//! Every consumer (passes, verifier, analyses) compiles against ONLY the
//! single-point interfaces [`Op::operands`], [`Op::for_each_operand`],
//! [`Op::has_operand`], [`Op::operands_mut`], [`Op::has_result`], and
//! [`Op::is_terminator`] — never against a hand-maintained variant list, so
//! variant lists cannot drift.

use crate::consts::Const;
use crate::function::{Edge, ValueDef};
use crate::id::{BlockId, ClassId, ConstId, FuncId, Sym, ValueId};
use crate::module::{FunctionKind, Module};
use crate::ty::{DynPrim, StaticTy, Ty};

/// Per-member attribute payloads of a class member buffer (B2 —
/// `defineclasswithbuffer`'s literal array), one entry per buffer member
/// in buffer order.
///
/// Vendor grounding (arkcompiler_ets_runtime-master):
///
/// - **Placement** (`is_static`): the buffer's collapsed runtime array is
///   `[name0, value0, …, nameK, valueK, i32 nonStaticNum]` — "non static
///   properties number is hidden in the last index of Literal buffer"
///   (`ecmascript/jspandafile/class_info_extractor.cpp:36-42`,
///   `ClassInfoExtractor::BuildClassInfoExtractorFromLiteral`). The first
///   `nonStaticNum` (name, value) pairs are INSTANCE members; the rest
///   install on the class object (static) —
///   `class_info_extractor.cpp:78`
///   (`staticNum = (valueLength) / 2 - nonStaticNum`) and the static
///   range's `extractBegin = nonStaticNum * 2`.
/// - **Callable kind** (`kind`): the buffer entry's method-kind literal
///   tag (`METHOD`/`GETTER`/`SETTER`/`GENERATORMETHOD`/
///   `ASYNCGENERATORMETHOD`, `libpandafile/literal_data_accessor.h:33-59`)
///   sets the materialized function's `FunctionKind` when the following
///   `METHODAFFILIATE` entry materializes it
///   (`ecmascript/jspandafile/literal_data_extractor.cpp:588-624`,
///   `LiteralDataExtractor::DefineFunctionTemplate`).
///
/// Derived at lift from the same literal array [`DefineClassData::members`]
/// pools — a semantic PROJECTION, never new content: lowering ignores it
/// and re-emits the raw buffer, so byte fidelity is unaffected.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MemberAttrs {
    /// `true` when the member installs on the class object (static
    /// placement — its pair index is at-or-past the buffer's trailing
    /// `nonStaticNum` count); `false` for prototype (instance) members.
    pub is_static: bool,
    /// The callable kind from the buffer entry's method-kind tag
    /// (`Function`, `Getter`, `Setter`, `Generator`, `AsyncGenerator`).
    pub kind: FunctionKind,
}

/// Shared payload for [`Op::DefineClass`] and [`Op::DefineSendableClass`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefineClassData {
    /// The constructor in the module's function table.
    pub ctor: FuncId,
    /// The heritage (`extends`) expression value, when present.
    pub heritage: Option<ValueId>,
    /// The member-buffer constant (`Const::ArrayLiteral` / `Const::ObjectLiteral`).
    pub members: ConstId,
    /// Per-member attribute payloads decoded from the buffer.
    pub member_attrs: Vec<MemberAttrs>,
    /// The class constructor's `.length` operand.
    pub count: u16,
}

/// Binary arithmetic/bitwise operator kind. Typed twins
/// (`add_i32` vs `add_f64`) are `BinaryOp::Add` plus the result value's
/// [`Ty`], not two ops.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Mod,
    /// `**`.
    Exp,
    /// `<<`.
    Shl,
    /// `>>>` (zero-fill).
    Shr,
    /// `>>` (sign-propagating).
    Ashr,
    /// `&`.
    BitAnd,
    /// `|`.
    BitOr,
    /// `^`.
    BitXor,
}

/// Unary operator kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// Numeric negation.
    Minus,
    /// `~`.
    BitNot,
    /// `!`.
    LogicalNot,
    /// `++`.
    Inc,
    /// `--`.
    Dec,
    /// `typeof`.
    TypeOf,
    /// ToNumber coercion.
    ToNumber,
    /// ToNumeric coercion.
    ToNumeric,
    /// `ToPropertyKey` coercion (`callruntime.topropertykey`, `#55`).
    ToPropertyKey,
    /// `void x`.
    Void,
    /// ToBoolean truth test.
    IsTrue,
    /// ToBoolean falsity test.
    IsFalse,
    /// ArkCompiler raw `jeqz` predicate (`interpreter-inl.cpp:1130-1131`):
    /// evaluates to `true` iff operand is `false` or numeric `±0`
    /// (`int == 0 || double == 0.0`); evaluates to `false` for `null`,
    /// `undefined`, `""`, `NaN`, strings, and objects (`#61` `R3-X1`).
    JumpEqz,
    /// ArkCompiler raw `jnez` predicate (`interpreter-inl.cpp:1178-1179`):
    /// evaluates to `true` iff operand is `true` or a non-zero number
    /// (`int != 0 || double != 0.0`, which is **`true` for `NaN`**); evaluates
    /// to `false` for `null`, `undefined`, strings, and objects (`#61` `R3-X1`).
    JumpNez,
}

impl UnOp {
    /// `true` when this unary operator always produces a boolean result.
    #[inline]
    #[must_use]
    pub const fn is_boolean_result(self) -> bool {
        matches!(
            self,
            Self::LogicalNot | Self::IsTrue | Self::IsFalse | Self::JumpEqz | Self::JumpNez
        )
    }
}

/// Comparison operator kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    /// `==`.
    Eq,
    /// `!=`.
    NotEq,
    /// `===`.
    StrictEq,
    /// `!==`.
    StrictNotEq,
    /// `<`.
    Less,
    /// `<=`.
    LessEq,
    /// `>`.
    Greater,
    /// `>=`.
    GreaterEq,
    /// `in`.
    In,
    /// `instanceof`.
    InstanceOf,
}

/// Kind of a module-variable load ([`Op::LoadModuleVar`]).
///
/// ArkCompiler separates local module export slots (`ldlocalmodulevar`),
/// eagerly-evaluated external import bindings (`ldexternalmodulevar`),
/// lazily-evaluated external import bindings (`callruntime.ldlazymodulevar`,
/// which triggers target-module evaluation on first read), and their sendable
/// counterparts into distinct index spaces and runtime paths.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ModuleVarKind {
    /// Local export slot of the current module (`ldlocalmodulevar` /
    /// `wide.ldlocalmodulevar`).
    #[default]
    Local,
    /// Imported binding from an eagerly-evaluated external module
    /// (`ldexternalmodulevar` / `wide.ldexternalmodulevar`).
    External,
    /// Imported binding from an `import lazy` module
    /// (`callruntime.ldlazymodulevar` / `callruntime.wideldlazymodulevar`);
    /// triggers lazy module evaluation on first read.
    Lazy,
    /// Sendable local module export slot
    /// (`callruntime.ldsendablelocalmodulevar` /
    /// `callruntime.wideldsendablelocalmodulevar`).
    SendableLocal,
    /// Sendable external module import binding
    /// (`callruntime.ldsendableexternalmodulevar` /
    /// `callruntime.wideldsendableexternalmodulevar`).
    SendableExternal,
    /// Sendable `import lazy` binding
    /// (`callruntime.ldlazysendablemodulevar` /
    /// `callruntime.wideldlazysendablemodulevar`).
    LazySendable,
    /// Sendable class lexical/module slot (`callruntime.ldsendableclass`).
    SendableClass,
}

impl ModuleVarKind {
    /// `true` when the slot belongs to the current module's own local export
    /// table (`Local`, `SendableLocal`, or `SendableClass`), i.e. the 0-based
    /// local export slot space written by [`Op::StoreModuleVar`] rather than
    /// `ImportDecl::Regular` (`#82`).
    #[must_use]
    pub const fn is_local(self) -> bool {
        matches!(
            self,
            Self::Local | Self::SendableLocal | Self::SendableClass
        )
    }

    /// `true` when reading the binding may trigger lazy module evaluation
    /// (`Lazy` or `LazySendable`).
    #[must_use]
    pub const fn is_lazy(self) -> bool {
        matches!(self, Self::Lazy | Self::LazySendable)
    }
}

/// Lexical environment flavor (`#55` `R3-D1`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum LexEnvKind {
    /// Ordinary ECMAScript lexical environment (`newlexenv`, `ldlexvar`, `stlexvar`).
    #[default]
    Plain,
    /// Sendable shared lexical environment (`callruntime.newsendableenv`,
    /// `callruntime.ldsendablevar`, `callruntime.stsendablevar`).
    Sendable,
    /// Hot-reload patch lexical slot (`ldpatchvar`, `stpatchvar`; `level == 0`).
    Patch,
}

/// Own-property / field definition flavor (`#55` `R3-D1`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum OwnStoreKind {
    /// Standard own-property store (`stownbyname` / `stownbyvalue` / `stownbyindex`).
    #[default]
    OwnProp,
    /// Own-property store setting anonymous function `.name`
    /// (`stownbynamewithnameset` / `stownbyvaluewithnameset`).
    OwnPropWithNameSet,
    /// Class public field definition (`definefieldbyname` /
    /// `callruntime.definefieldbyvalue` / `callruntime.definefieldbyindex`).
    ClassField,
    /// `Object.defineProperty`-style own-property definition (`definepropertybyname`).
    DefineProperty,
}

/// Call kind — the call-binding table (`design/ir.md`,
/// [`crate::frame::FrameSlots`], where `H = slots.implicit_count()` is the
/// callee's leading implicit slot count — `H = 3` under
/// [`crate::Dialect::DynamicEcma`] `0xF` default, `H = 0` on
/// [`crate::Dialect::StaticArkTS`] `static` methods, `H = 1` on
/// [`crate::Dialect::StaticArkTS`] instance methods/constructors; `D6`):
///
/// | kind | `this` slot | `new.target` slot | formals |
/// |------|-------------|-------------------|---------|
/// | `Direct` | `call.this` | `undefined` | `args → params[H..]` |
/// | `Dynamic` | `call.this` when `Some` (`callthis*`), else computed at callee entry (`callarg*`/`callrange`) | `undefined` | `args → params[H..]` |
/// | `Apply` | `call.this` (explicit receiver) | `undefined` | SPREAD of `args[0]` |
/// | `Super` | inherited from enclosing ctor | inherited | `args → params[H..]` |
/// | `SuperArrow` | inherited from enclosing ctor | inherited | `args → params[H..]` (`callee` explicit from `acc`) |
/// | `SuperSpread` | inherited from enclosing ctor | inherited | SPREAD of `args[0]` |
/// | `SuperForwardAllArgs` | inherited | inherited | ALL own args (forwarded) |
/// | `New` | fresh object from `callee.prototype` | callee itself | `args → params[H..]` |
/// | `NewSpread` | fresh object from `callee.prototype` | callee itself | SPREAD of `args[0]` |
/// | `ClassInit` | `call.this` (explicit receiver) | `undefined` | `[]` (0 args) |
///
/// The result is the callee's return value; a throw inside the callee
/// flows to the caller's exceptional edges.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallKind {
    /// A statically resolved callee with an explicit `this`.
    Direct,
    /// A dynamically computed callee: when `Call::this` is `Some(receiver)`
    /// (`callthis*`), that explicit receiver is passed in the `this` slot;
    /// when `Call::this` is `None` (`callarg*` / `callrange`), `this` is
    /// computed at callee entry (`undefined` in strict mode, global object in
    /// sloppy mode).
    Dynamic,
    /// `func.apply(this, argsArray)` — vendor `apply imm, v_this, v_args`
    /// (`isa.yaml:1104`, the func in the acc): the receiver is explicit and
    /// the single argument is an ARRAY spread over the formal parameters.
    Apply,
    /// A `super(...)` call in a constructor with EXPLICIT arguments and the
    /// enclosing constructor in `callee` (vendor `supercallthisrange`).
    Super,
    /// A `super(...)` call inside an arrow function in a constructor where
    /// `callee` is the explicit super constructor from `acc` and `Call::this`
    /// is `None` (vendor `supercallarrowrange`, `#55`).
    SuperArrow,
    /// A `super(...args)` call spreading an argument ARRAY into the super
    /// constructor — vendor `supercallspread imm, v_args` (`isa.yaml`).
    /// `Call::this` is `None` (inherited) and `Call::args` is `[array]`.
    SuperSpread,
    /// Vendor `callruntime.supercallforwardallargs v_this` (`isa.yaml`): a
    /// default derived constructor forwarding ALL of its own arguments to
    /// the super constructor (`Call::this` is `None` and `Call::args` is `[this]`).
    SuperForwardAllArgs,
    /// `new callee(args...)` (`newobjrange` / `wide.newobjrange`).
    New,
    /// `new callee(...argsArray)` (`newobjapply` / `wide.newobjapply`, `#55`):
    /// `Call::this` is `None` and `Call::args` is `[array]`.
    NewSpread,
    /// Class field-initializer invocation (`callruntime.callinit`, `#55`):
    /// `Call::this` is `Some(receiver)` and `Call::args` is `[]`.
    ClassInit,
}

/// Which `this`-binding check [`Op::ThrowIfSuperNotCalled`] performs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SuperCheck {
    /// TDZ guard: a derived constructor must call `super()` before using
    /// `this`.
    NotCalled,
    /// Re-bind guard: `super()` may not re-bind `this`.
    Rebind,
}

/// Property key for [`Op::TestProp`] (T2: named / index / dynamic access
/// are always distinguishable).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PropKey {
    /// A statically known property name.
    Name(Sym),
    /// An integer index operand (constant-index detection is a def-chain
    /// query for the analysis layer — `design/ir.md`).
    Index(ValueId),
    /// A computed key operand.
    Dynamic(ValueId),
}

/// Property key for super-property access.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SuperKey {
    /// A statically known property name.
    Name(Sym),
    /// A computed key operand.
    Dynamic(ValueId),
}

/// Declared operand arity of an op — the taxonomy's arity table, checked
/// by the verifier against [`Op::operands`] as a drift guard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    /// Exactly this many SSA operands.
    Exact(usize),
    /// Operand count varies with the payload (`Call` args, `Phi` entries,
    /// `DefineFunc` captures, optional operands, key enums).
    Variadic,
}

/// The closed op enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    // ── Compute ────────────────────────────────────────────────────────
    /// Binary arithmetic/bitwise op.
    BinaryOp {
        /// The operator.
        op: BinOp,
        /// Left operand.
        left: ValueId,
        /// Right operand.
        right: ValueId,
    },
    /// Unary op.
    UnaryOp {
        /// The operator.
        op: UnOp,
        /// The operand.
        operand: ValueId,
    },
    /// Comparison.
    Compare {
        /// The operator.
        op: CmpOp,
        /// Left operand.
        left: ValueId,
        /// Right operand.
        right: ValueId,
    },
    /// Pure value copy (sign extension is `Mov` + the result's `Ty`).
    Mov {
        /// The source value.
        src: ValueId,
    },
    /// Load a constant from the module pool.
    LoadConst(ConstId),

    // ── Objects / arrays ───────────────────────────────────────────────
    /// Allocate an object with a literal shape (T7; the
    /// [`InstId`](crate::id::InstId) of the instruction is the
    /// allocation-site identity).
    AllocObject {
        /// The object-literal shape constant.
        shape: ConstId,
    },
    /// Allocate an array (T7). `shape: None` is the empty array
    /// (`createemptyarray`); `Some(shape)` is an array with a literal
    /// shape (`createarraywithbuffer` — the literal array as a pooled
    /// shape). The object/array tag is OPCODE-carried (`design/decisions.md`
    /// N59): it is not recoverable from the flat literal-buffer content, so
    /// it must come from the op, mirroring [`Op::AllocObject`]'s treatment.
    AllocArray {
        /// The array-literal shape constant, when present.
        shape: Option<ConstId>,
    },
    /// Allocate a RegExp (T7).
    AllocRegExp {
        /// The pattern source.
        pattern: Sym,
        /// Flag bits.
        flags: u32,
    },
    /// Allocate a closure from a [`Op::DefineFunc`] result (T7).
    AllocClosure {
        /// The `DefineFunc` result value (carries body + capture flow).
        func: ValueId,
    },
    /// Named property load: `object.name` (T2).
    LoadProp {
        /// The receiver object.
        object: ValueId,
        /// The property name.
        name: Sym,
    },
    /// Named property store: `object.name = value`.
    StoreProp {
        /// The receiver object.
        object: ValueId,
        /// The property name.
        name: Sym,
        /// The stored value.
        value: ValueId,
    },
    /// Integer-indexed element access: `object[index]` (single op —
    /// `design/ir.md`).
    LoadPropIdx {
        /// The receiver object.
        object: ValueId,
        /// The index.
        index: ValueId,
    },
    /// Integer-indexed element store.
    StorePropIdx {
        /// The receiver object.
        object: ValueId,
        /// The index.
        index: ValueId,
        /// The stored value.
        value: ValueId,
    },
    /// Computed-key property access: `object[key]`.
    LoadPropDyn {
        /// The receiver object.
        object: ValueId,
        /// The computed key.
        key: ValueId,
    },
    /// Computed-key property store.
    StorePropDyn {
        /// The receiver object.
        object: ValueId,
        /// The computed key.
        key: ValueId,
        /// The stored value.
        value: ValueId,
    },
    /// Named OWN-property store: define `object.name = value` as an own
    /// property (vendor `stownbyname`(+withnameset)/`definefieldbyname`/
    /// `definepropertybyname`) — CreateDataProperty/DefineField
    /// semantics: NO setters, NO prototype-chain walk, unlike
    /// [`Op::StoreProp`] (`design/decisions.md` N60; lowers to the
    /// `stownby*` family).
    StoreOwnPropName {
        /// The receiver object.
        object: ValueId,
        /// The property name.
        name: Sym,
        /// The stored value.
        value: ValueId,
        /// Own-store opcode flavor (`stownbyname*`, `definefieldbyname`, `definepropertybyname`).
        kind: OwnStoreKind,
    },
    /// Computed-key own-property store (vendor
    /// `stownbyvalue`(+withnameset)/`callruntime.definefieldbyvalue`;
    /// `design/decisions.md` N60).
    StoreOwnPropDyn {
        /// The receiver object.
        object: ValueId,
        /// The computed key.
        key: ValueId,
        /// The stored value.
        value: ValueId,
        /// Own-store opcode flavor (`stownbyvalue*`, `callruntime.definefieldbyvalue`).
        kind: OwnStoreKind,
    },
    /// Integer-indexed own-property store (vendor
    /// `stownbyindex`/`wide.stownbyindex`/
    /// `callruntime.definefieldbyindex`; `design/decisions.md` N60).
    StoreOwnPropIdx {
        /// The receiver object.
        object: ValueId,
        /// The index.
        index: ValueId,
        /// The stored value.
        value: ValueId,
        /// Own-store opcode flavor (`stownbyindex`, `callruntime.definefieldbyindex`).
        kind: OwnStoreKind,
    },
    /// Define a method on an object (class/object-literal semantics).
    DefineMethod {
        /// The home object.
        object: ValueId,
        /// The method name.
        name: Sym,
        /// The function value (a closure).
        func: ValueId,
        /// The method's `.length` property value (vendor `definemethod
        /// imm1, method_id, imm2:u8`, isa.yaml).
        length: u16,
    },
    /// `delete object[key]`.
    DeleteProp {
        /// The receiver object.
        object: ValueId,
        /// The key.
        key: ValueId,
    },
    /// Property existence test (`in`-family).
    TestProp {
        /// The receiver object.
        object: ValueId,
        /// The key (named / index / dynamic).
        key: PropKey,
    },
    /// ECMAScript CopyDataProperties (object spread): copy all own
    /// enumerable properties of `src` into `dst`.
    CopyDataProps {
        /// The destination object.
        dst: ValueId,
        /// The source object.
        src: ValueId,
    },
    /// Vendor `setobjectwithproto imm:u16, v:in:top, acc: in:top`
    /// (isa.yaml:1333-1337): set `obj`'s prototype link to `proto`
    /// directly, WITHOUT running any `__proto__` setter machinery —
    /// never collapsible into a named-property store or a
    /// [`Op::CopyDataProps`].
    SetObjectWithProto {
        /// The new prototype.
        proto: ValueId,
        /// The object whose prototype link is set.
        obj: ValueId,
    },
    /// Vendor `starrayspread v1:in:top, v2:in:top, acc: inout:top`
    /// (isa.yaml:1329-1332): spread the `src` iterable's elements into
    /// the `dst` array starting at `index`; the runtime writes the NEW
    /// index back to the accumulator — the op's result is that new
    /// index (never a plain element store).
    ArraySpread {
        /// The destination array.
        dst: ValueId,
        /// The start index.
        index: ValueId,
        /// The source iterable.
        src: ValueId,
    },
    /// Vendor `createobjectwithexcludedkeys imm, v1, v2, acc: out:top`
    /// (isa.yaml:494-504, `range_1`): create a fresh object copying
    /// `obj`'s own enumerable properties EXCEPT the listed `keys`
    /// (rest-destructuring semantics).
    CreateObjectWithExcludedKeys {
        /// The source object.
        obj: ValueId,
        /// The excluded key values.
        keys: Vec<ValueId>,
    },
    /// Vendor `definegettersetterbyvalue v1, v2, v3, v4, acc: inout:top`
    /// (`isa.yaml:1220`): define an accessor property on `obj` under the
    /// computed `key` with the given `getter`/`setter` closures and `set_name`
    /// boolean flag (`acc` input).
    DefineGetterSetterByValue {
        /// The target object.
        obj: ValueId,
        /// The computed property key.
        key: ValueId,
        /// The getter closure.
        getter: ValueId,
        /// The setter closure.
        setter: ValueId,
        /// Boolean flag controlling whether runtime sets accessor `.name` (`acc` input).
        set_name: ValueId,
    },
    /// Vendor `gettemplateobject imm:u16, acc: inout:top`
    /// (isa.yaml:1279-1283): turn the template `literal` into its
    /// (cached) template object. The cache identity is the point —
    /// never an element read and never a `Mov`.
    GetTemplateObject {
        /// The template literal value.
        literal: ValueId,
    },
    /// Vendor `createiterresultobj v1, v2, acc: out:top`
    /// (isa.yaml:490-493): allocate the iterator result object
    /// `{ value, done }`.
    CreateIterResultObj {
        /// The iteration value.
        value: ValueId,
        /// The done flag.
        done: ValueId,
    },

    // ── Iteration ──────────────────────────────────────────────────────
    /// Get an iterator (`@@iterator` protocol).
    GetIterator {
        /// The iterable.
        obj: ValueId,
    },
    /// Get an async iterator (`@@asyncIterator` protocol) — a distinct
    /// protocol lookup from [`Op::GetIterator`], vendor `getasynciterator
    /// imm:u8, acc: inout:top` (isa.yaml:431-435).
    GetAsyncIterator {
        /// The iterable.
        obj: ValueId,
    },
    /// Advance an iterator; yields the next result object.
    IteratorNext {
        /// The iterator.
        iterator: ValueId,
    },
    /// `return()` an iterator (early exit).
    IteratorReturn {
        /// The iterator.
        iterator: ValueId,
    },
    /// `throw()` into an iterator.
    IteratorThrow {
        /// The iterator.
        iterator: ValueId,
    },
    /// Create a for-in property-name iterator.
    GetPropIterator {
        /// The object being enumerated.
        obj: ValueId,
    },
    /// Advance a for-in iterator; yields the next property name.
    NextPropName {
        /// The for-in iterator.
        iterator: ValueId,
    },

    // ── Lexical / global / module ──────────────────────────────────────
    /// Push a new lexical or sendable environment with `num_vars` slots,
    /// yielding it (`newlexenv` / `callruntime.newsendableenv`).
    NewLexEnv {
        /// Number of variables in the new environment.
        num_vars: u16,
        /// Environment flavor (`Plain` or `Sendable`; never `Patch`).
        kind: LexEnvKind,
    },
    /// Push a new NAMED lexical environment, yielding it (vendor
    /// `newlexenvwithname` / `wide.newlexenvwithname`, isa.yaml): the
    /// scope's variable names come from a literal-array constant.
    NewLexEnvWithName {
        /// Number of variables in the new environment.
        num_vars: u16,
        /// The scope-names constant (an [`Const::ArrayLiteral`] of
        /// [`Const::String`] names).
        scope_names: ConstId,
    },
    /// Pop the current lexical environment (vendor `poplexenv`,
    /// isa.yaml:367-370). Void, but observable: the lexical scope
    /// discipline is part of the program's semantics (round-tripping
    /// and the lexical model depend on it).
    PopLexEnv,
    /// Load a lexical, sendable, or patch variable by environment level and slot.
    GetLexVar {
        /// Scope-chain level (`0` for `LexEnvKind::Patch`).
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// Lexical environment flavor.
        kind: LexEnvKind,
    },
    /// Store a lexical, sendable, or patch variable by environment level and slot.
    PutLexVar {
        /// Scope-chain level (`0` for `LexEnvKind::Patch`).
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The stored value.
        value: ValueId,
        /// Lexical environment flavor.
        kind: LexEnvKind,
    },
    /// Load a global by name, tolerating absence (`default` when the
    /// global does not exist). Absence-tolerant does NOT mean
    /// side-effect-free: the vendored slow paths of both source forms
    /// (`ldglobalvar`, `tryldglobalbyname`) run `GetProperty` on the
    /// global's prototype chain — global getters are called and the
    /// calls are abrupt-checked (see [`Op::effects`],
    /// `design/decisions.md` N48/N50).
    TryGetGlobal {
        /// The global's name.
        name: Sym,
        /// Fallback value when the global is absent.
        default: Option<ValueId>,
    },
    /// Store a global by name.
    StoreGlobal {
        /// The global's name.
        name: Sym,
        /// The stored value.
        value: ValueId,
    },
    /// Store into the global LEXICAL record (vendor `sttoglobalrecord` /
    /// `stconsttoglobalrecord`, isa.yaml:1585/:1574): declares a global
    /// lexical binding in the GlobalDictionary (`RuntimeStGlobalRecord`,
    /// arkcompiler_ets_runtime-master/ecmascript/stubs/
    /// runtime_stubs-inl.h:780 — `PutIfAbsent`, SyntaxError "Duplicate
    /// identifier" on collision) — NOT a property store on the global
    /// OBJECT (that is [`Op::StoreGlobal`] / `RuntimeStGlobalVar`,
    /// runtime_stubs-inl.h:1793). The deprecated trio
    /// (stlet-/stclass-/stconstto-globalrecord, interpreter-inl.cpp
    /// :6260-6345, all `SlowRuntimeStub::StGlobalRecord`) lifts here too:
    /// stconst→`is_const: true`, stlet/stclass→`false`
    /// (`design/decisions.md` N72: folding this into `StoreGlobal` would
    /// turn a top-level `let Array` into `globalThis.Array = undefined`,
    /// clobbering the builtin).
    StoreGlobalRecord {
        /// The binding's name.
        name: Sym,
        /// The stored value.
        value: ValueId,
        /// `stconsttoglobalrecord` when true, `sttoglobalrecord` when
        /// false.
        is_const: bool,
    },
    /// Store a global by name, TOLERANT of absence (vendor
    /// `trystglobalbyname`): no ReferenceError when the global does not
    /// exist — unlike the throwing [`Op::StoreGlobal`]
    /// (`design/decisions.md` N61).
    TryStoreGlobal {
        /// The global's name.
        name: Sym,
        /// The stored value.
        value: ValueId,
    },
    /// Load a module variable by its module slot and namespace kind.
    LoadModuleVar {
        /// The module-variable slot (index within `kind`'s table, not a file
        /// pool index).
        index: u32,
        /// Whether this load reads a local export slot, an external import
        /// binding, a lazy import binding, or a sendable variant.
        kind: ModuleVarKind,
    },
    /// Store a module-local variable.
    StoreModuleVar {
        /// The module-variable slot.
        index: u32,
        /// The stored value.
        value: ValueId,
    },
    /// Get the namespace object of an imported module.
    GetModuleNamespace {
        /// The module slot of the imported module.
        index: u32,
    },
    /// `import(specifier)`.
    DynamicImport {
        /// The module specifier expression.
        specifier: ValueId,
    },

    // ── Calls / definitions ────────────────────────────────────────────
    /// A call (`T4`; one semantic op for the whole `callthis`/`callshort`/
    /// `callrange` family). Binding per [`CallKind`] (`design/ir.md`).
    Call {
        /// The callee.
        callee: ValueId,
        /// The `this` binding; `None` when the kind computes it
        /// (`Dynamic`) or inherits it (`Super`).
        this: Option<ValueId>,
        /// Arguments, in order.
        args: Vec<ValueId>,
        /// The call kind.
        kind: CallKind,
    },
    /// Define a function: body + explicit capture list (T4 — capture flow
    /// is data for taint). Feeds [`Op::AllocClosure`].
    DefineFunc {
        /// The function body in the module's function table.
        body: FuncId,
        /// `(name, value)` captured bindings, explicit.
        captures: Vec<(Sym, ValueId)>,
        /// The function's `.length` property value (vendor `definefunc
        /// imm1, method_id, imm2:u8`, isa.yaml — the declared formal
        /// parameter count the runtime installs).
        length: u16,
    },
    /// Define a class with a member buffer (boxed via [`DefineClassData`] so
    /// [`Op`] stays compact).
    DefineClass(Box<DefineClassData>),
    /// Define a SENDABLE (shared) class with a member buffer — vendor
    /// `callruntime.definesendableclass imm1:u16, method_id,
    /// literalarray_id, imm2:u16, v:in:top` (`isa.yaml:861-866`).
    ///
    /// Distinct from [`Op::DefineClass`] (`design/decisions.md` N53): the
    /// vendor runtime builds the class through
    /// `SlowRuntimeStub::CreateSharedClass`, NOT `CreateClassWithBuffer`,
    /// so lowering must preserve the sendable opcode identity.
    DefineSendableClass(Box<DefineClassData>),

    // ── Private properties ─────────────────────────────────────────────
    /// Load a private field by environment level and slot.
    LoadPrivate {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The receiver object.
        obj: ValueId,
    },
    /// Store a private field.
    StorePrivate {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The receiver object.
        obj: ValueId,
        /// The stored value.
        value: ValueId,
    },
    /// Define a private field (definition, not assignment semantics).
    DefinePrivate {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The receiver object.
        obj: ValueId,
        /// The defined value.
        value: ValueId,
    },
    /// Private-brand test (`#x in obj`).
    TestPrivate {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The receiver object.
        obj: ValueId,
    },
    /// Register `count` private names in the current environment.
    CreatePrivateNames {
        /// How many private names to register.
        count: u16,
        /// The private-name strings (an [`Const::ArrayLiteral`] of
        /// [`Const::String`]) — vendor
        /// `callruntime.createprivateproperty imm:u16, literalarray_id`
        /// (isa.yaml:843-848).
        names: ConstId,
    },

    // ── Exceptions ─────────────────────────────────────────────────────
    /// `throw value`.
    Throw {
        /// The thrown value.
        value: ValueId,
    },
    /// Derived-constructor `this` guard.
    ThrowIfSuperNotCalled {
        /// The `this` value being checked.
        value: ValueId,
        /// Which check.
        kind: SuperCheck,
    },
    /// TDZ guard: throw a ReferenceError if `value` is the hole; `name`
    /// is the runtime variable-name value.
    ThrowUndefinedIfHole {
        /// The variable name (a runtime value).
        name: ValueId,
        /// The value being hole-checked.
        value: ValueId,
    },
    /// TDZ guard with a COMPILE-TIME name — a different vendor
    /// instruction from [`Op::ThrowUndefinedIfHole`]:
    /// `throw.undefinedifholewithname string_id, acc: in:top`
    /// (isa.yaml:1010-1015). The name is a constant string; the checked
    /// value is the operand.
    ThrowUndefinedIfHoleWithName {
        /// The variable name (a compile-time string).
        name: Sym,
        /// The value being hole-checked.
        value: ValueId,
    },
    /// Throw a ReferenceError for a nonexistent binding (vendor
    /// `throw.notexists`, isa.yaml).
    ThrowNotExists,
    /// Throw on a pattern applied to a non-coercible value (vendor
    /// `throw.patternnoncoercible`, isa.yaml).
    ThrowPatternNonCoercible,
    /// Throw on `delete super.x` (vendor `throw.deletesuperproperty`,
    /// isa.yaml).
    ThrowDeleteSuperProperty,
    /// Throw on assignment to a `const` binding.
    ThrowConstAssignment {
        /// The variable name (a runtime value).
        name: ValueId,
    },
    /// Throw if the value is not coercible to an object.
    ThrowIfNotObject {
        /// The value being checked.
        value: ValueId,
    },

    // ── Generator / async ──────────────────────────────────────────────
    /// Create a generator object from a closure (T7).
    CreateGenerator {
        /// The closure value.
        func: ValueId,
    },
    /// Create an async generator object from a closure (`createasyncgeneratorobj`, `#55`).
    CreateAsyncGenerator {
        /// The closure value.
        func: ValueId,
    },
    /// Set a generator or async-generator object's internal state (`setgeneratorstate imm`, `#55`).
    SetGeneratorState {
        /// The generator object (`acc` input).
        genobj: ValueId,
        /// Target generator state code (`imm:u8`).
        state: u8,
    },
    /// `yield`: suspend `genobj`, producing `value`; the result is the
    /// resume value.
    SuspendGenerator {
        /// The generator object.
        genobj: ValueId,
        /// The yielded value.
        value: ValueId,
    },
    /// Resume a generator; yields the resume result.
    ResumeGenerator {
        /// The generator object.
        genobj: ValueId,
    },
    /// Read a generator's resume mode.
    GetResumeMode {
        /// The generator object.
        genobj: ValueId,
    },
    /// `await value`.
    Await {
        /// The awaited value.
        value: ValueId,
    },
    /// Vendor `asyncfunctionawaituncaught v:in:top, acc: inout:top`
    /// (isa.yaml:1311-1314; runtime interpreter-inl.cpp
    /// `HANDLE_OPCODE(ASYNCFUNCTIONAWAITUNCAUGHT_V8)` :5357-5366) — the
    /// es2abc await form: await `value` without the caught-completion
    /// wrapper. The REGISTER operand is the async function object; the
    /// ACCUMULATOR carries the awaited value in and receives the result.
    /// Distinct from [`Op::Await`]; lift emits this op for the
    /// (deprecated.)asyncfunctionawaituncaught bytecodes.
    AwaitUncaught {
        /// The async function object (the v0 register operand).
        funcobj: ValueId,
        /// The awaited value (the accumulator input).
        value: ValueId,
    },
    /// Vendor `asyncfunctionenter` (isa.yaml, `acc: out:top`): enter an
    /// async function, yielding the async context/promise value.
    AsyncFunctionEnter,
    /// Vendor `asyncfunctionresolve v:in:top, acc: inout:top`
    /// (isa.yaml:1413-1416; interpreter-inl.cpp
    /// `HANDLE_OPCODE(ASYNCFUNCTIONRESOLVE_V8)` :6577-6589) — resolve the
    /// async function's promise. The register operand is the async
    /// function object; the accumulator carries the resolution value in
    /// and receives the result.
    AsyncResolve {
        /// The async function object (the v0 register operand).
        funcobj: ValueId,
        /// The resolution value (the accumulator input).
        value: ValueId,
    },
    /// Vendor `asyncfunctionreject v:in:top, acc: inout:top`
    /// (isa.yaml:1422-1425; interpreter-inl.cpp
    /// `HANDLE_OPCODE(ASYNCFUNCTIONREJECT_V8)` :6605-6617) — reject the
    /// async function's promise. The register operand is the async
    /// function object; the accumulator carries the rejection reason in
    /// and receives the result.
    AsyncReject {
        /// The async function object (the v0 register operand).
        funcobj: ValueId,
        /// The rejection reason (the accumulator input).
        value: ValueId,
    },
    /// Resolve an async generator step (`asyncgeneratorresolve v1, v2, v3`, `#55`).
    AsyncGeneratorResolve {
        /// The async generator object (`v1`).
        genobj: ValueId,
        /// The yielded/returned value (`v2`).
        value: ValueId,
        /// Boolean `done` flag (`v3`).
        done: ValueId,
    },
    /// Reject an async generator step (`asyncgeneratorreject v`, `#55`).
    AsyncGeneratorReject {
        /// The async generator object (`v`).
        genobj: ValueId,
        /// The rejection reason (`acc` input).
        value: ValueId,
    },
    /// Notify the concurrent task runtime of `value` (`callruntime.notifyconcurrentresult`, `#55`).
    NotifyConcurrentResult {
        /// Result value (`acc` input).
        value: ValueId,
    },

    // ── Frame / special value loaders ──────────────────────────────────
    /// Load the global `Symbol` constructor (`ldsymbol`, `#55`).
    LoadSymbol,
    /// Load `new.target` (vendor `ldnewtarget`, isa.yaml — `acc:
    /// out:top`): a real frame-state value (the construct receiver in a
    /// constructor, `undefined` otherwise), never a constant.
    LoadNewTarget,
    /// Load the global object (vendor `ldglobal`, isa.yaml).
    LoadGlobalObject,
    /// Load the currently executing function object (vendor
    /// `ldfunction`, isa.yaml).
    LoadFunction,
    /// Create the unmapped `arguments` object (vendor `getunmappedargs`,
    /// isa.yaml): an exotic-object allocation site.
    GetUnmappedArgs,
    /// Copy the rest arguments from `start_index` into a fresh array
    /// (vendor `copyrestargs` / `wide.copyrestargs`, isa.yaml).
    CopyRestArgs {
        /// Index of the first rest argument.
        start_index: u16,
    },

    // ── Super ──────────────────────────────────────────────────────────
    /// Super-property load.
    LoadSuper {
        /// The property key.
        key: SuperKey,
        /// The `thisValue` of the super reference (`design/decisions.md` N74:
        /// `ldsuperbyvalue imm, v` carries it in `v` while the key is in `acc`,
        /// and `ldsuperbyname imm, string_id` also supplies an explicit
        /// `this_value` from `acc` per `isa.yaml` `acc: inout:top`).
        this_value: ValueId,
    },
    /// Super-property store.
    StoreSuper {
        /// The property key.
        key: SuperKey,
        /// The `thisValue` of the super reference (vendor
        /// `stsuperbyvalue imm, v1, v2`: `v1 = this`, `v2 = key`, `acc =
        /// value` — `design/decisions.md` N74).
        this_value: ValueId,
        /// The stored value.
        value: ValueId,
    },

    // ── Control ────────────────────────────────────────────────────────
    /// Unconditional branch.
    Branch {
        /// Target block.
        dest: BlockId,
    },
    /// Conditional branch.
    CondBranch {
        /// The condition value.
        cond: ValueId,
        /// Taken when the condition is truthy.
        true_dest: BlockId,
        /// Taken otherwise.
        false_dest: BlockId,
    },
    /// Return from the function (`None` = `return undefined`).
    Return {
        /// The return value.
        value: Option<ValueId>,
    },
    /// SSA phi: one entry per incoming edge (`design/ir.md` — entries
    /// reference `(Edge, ValueId)`; the value flows from the edge's source
    /// block).
    Phi {
        /// `(incoming edge, value)` pairs.
        entries: Vec<(Edge, ValueId)>,
    },
    /// Dead control point.
    Unreachable,

    // ── Debug ──────────────────────────────────────────────────────────
    /// Vendor `debugger` (`isa.yaml`): a debugger breakpoint — observable
    /// when a debugger is attached (modeled via the potential debugger-hook
    /// call effect in [`Op::effects`]).
    Debugger,
}

impl Op {
    /// Internal short-circuiting visitor over all SSA operands (uses) in
    /// canonical [`Op::operands`] order. Single source of operand truth for
    /// [`Op::for_each_operand`], [`Op::has_operand`], and [`Op::operands`].
    #[inline]
    fn try_for_each_operand<F>(&self, mut f: F) -> std::ops::ControlFlow<()>
    where
        F: FnMut(ValueId) -> std::ops::ControlFlow<()>,
    {
        use Op::*;
        use std::ops::ControlFlow::Continue;
        match self {
            BinaryOp { left, right, .. } | Compare { left, right, .. } => {
                f(*left)?;
                f(*right)?;
            }
            UnaryOp { operand, .. } => f(*operand)?,
            Mov { src } => f(*src)?,
            LoadConst(_) | AllocObject { .. } | AllocArray { .. } | AllocRegExp { .. } => {}
            AllocClosure { func } => f(*func)?,
            LoadProp { object, .. } => f(*object)?,
            StoreProp { object, value, .. } | StoreOwnPropName { object, value, .. } => {
                f(*object)?;
                f(*value)?;
            }
            LoadPropIdx { object, index } | LoadPropDyn { object, key: index } => {
                f(*object)?;
                f(*index)?;
            }
            StorePropIdx {
                object,
                index,
                value,
            }
            | StorePropDyn {
                object,
                key: index,
                value,
            }
            | StoreOwnPropDyn {
                object,
                key: index,
                value,
                ..
            }
            | StoreOwnPropIdx {
                object,
                index,
                value,
                ..
            } => {
                f(*object)?;
                f(*index)?;
                f(*value)?;
            }
            DefineMethod { object, func, .. } => {
                f(*object)?;
                f(*func)?;
            }
            DeleteProp { object, key } => {
                f(*object)?;
                f(*key)?;
            }
            TestProp { object, key } => {
                f(*object)?;
                match key {
                    PropKey::Name(_) => {}
                    PropKey::Index(k) | PropKey::Dynamic(k) => f(*k)?,
                }
            }
            CopyDataProps { dst, src } => {
                f(*dst)?;
                f(*src)?;
            }
            SetObjectWithProto { proto, obj } => {
                f(*proto)?;
                f(*obj)?;
            }
            ArraySpread { dst, index, src } => {
                f(*dst)?;
                f(*index)?;
                f(*src)?;
            }
            CreateObjectWithExcludedKeys { obj, keys } => {
                f(*obj)?;
                for &k in keys {
                    f(k)?;
                }
            }
            DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                set_name,
            } => {
                f(*obj)?;
                f(*key)?;
                f(*getter)?;
                f(*setter)?;
                f(*set_name)?;
            }
            GetTemplateObject { literal } => f(*literal)?,
            CreateIterResultObj { value, done } => {
                f(*value)?;
                f(*done)?;
            }
            GetIterator { obj } | GetPropIterator { obj } | GetAsyncIterator { obj } => f(*obj)?,
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator }
            | NextPropName { iterator } => f(*iterator)?,
            NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | CreatePrivateNames { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | AsyncFunctionEnter
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | Debugger => {}
            PutLexVar { value, .. } => f(*value)?,
            TryGetGlobal { default, .. } => {
                if let Some(v) = default {
                    f(*v)?;
                }
            }
            StoreGlobal { value, .. }
            | StoreGlobalRecord { value, .. }
            | TryStoreGlobal { value, .. }
            | StoreModuleVar { value, .. } => f(*value)?,
            LoadModuleVar { .. } | GetModuleNamespace { .. } => {}
            DynamicImport { specifier } => f(*specifier)?,
            Call {
                callee, this, args, ..
            } => {
                f(*callee)?;
                if let Some(t) = this {
                    f(*t)?;
                }
                for &arg in args {
                    f(arg)?;
                }
            }
            DefineFunc { captures, .. } => {
                for &(_, v) in captures {
                    f(v)?;
                }
            }
            DefineClass(d) | DefineSendableClass(d) => {
                if let Some(h) = &d.heritage {
                    f(*h)?;
                }
            }
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => f(*obj)?,
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                f(*obj)?;
                f(*value)?;
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | ThrowUndefinedIfHoleWithName { value, .. }
            | Await { value }
            | NotifyConcurrentResult { value } => f(*value)?,
            AwaitUncaught { funcobj, value }
            | AsyncResolve { funcobj, value }
            | AsyncReject { funcobj, value }
            | AsyncGeneratorReject {
                genobj: funcobj,
                value,
            } => {
                f(*funcobj)?;
                f(*value)?;
            }
            AsyncGeneratorResolve {
                genobj,
                value,
                done,
            } => {
                f(*genobj)?;
                f(*value)?;
                f(*done)?;
            }
            ThrowUndefinedIfHole { name, value } => {
                f(*name)?;
                f(*value)?;
            }
            CreateGenerator { func } | CreateAsyncGenerator { func } => f(*func)?,
            SuspendGenerator { genobj, value } => {
                f(*genobj)?;
                f(*value)?;
            }
            ResumeGenerator { genobj }
            | GetResumeMode { genobj }
            | SetGeneratorState { genobj, .. } => f(*genobj)?,
            LoadSuper { key, this_value } => match key {
                SuperKey::Name(_) => f(*this_value)?,
                SuperKey::Dynamic(k) => {
                    f(*k)?;
                    f(*this_value)?;
                }
            },
            StoreSuper {
                key,
                this_value,
                value,
            } => {
                f(*value)?;
                f(*this_value)?;
                if let SuperKey::Dynamic(k) = key {
                    f(*k)?;
                }
            }
            Branch { .. } | Unreachable => {}
            CondBranch { cond, .. } => f(*cond)?,
            Return { value } => {
                if let Some(v) = value {
                    f(*v)?;
                }
            }
            Phi { entries } => {
                for &(_, v) in entries {
                    f(v)?;
                }
            }
        }
        Continue(())
    }

    /// Visit each SSA operand (use) of this op in exact [`Op::operands`]
    /// order without allocating. Block/const/symbol/func payloads are not SSA
    /// operands and are not visited.
    #[inline]
    pub fn for_each_operand<F: FnMut(ValueId)>(&self, mut f: F) {
        let _ = self.try_for_each_operand(|v| {
            f(v);
            std::ops::ControlFlow::Continue(())
        });
    }

    /// Return `true` iff `target` appears among this op's SSA operands,
    /// short-circuiting on the first match without allocating.
    #[inline]
    pub fn has_operand(&self, target: ValueId) -> bool {
        self.try_for_each_operand(|v| {
            if v == target {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
    }

    /// All SSA operands (uses) of this op. Block/const/symbol/func
    /// payloads are not SSA operands and are not returned.
    ///
    /// Prefer [`Op::for_each_operand`] or [`Op::has_operand`] in hot loops
    /// when a heap-allocated `Vec` is not needed.
    pub fn operands(&self) -> Vec<ValueId> {
        let mut out = match self.arity() {
            Arity::Exact(n) => Vec::with_capacity(n),
            Arity::Variadic => Vec::new(),
        };
        self.for_each_operand(|v| out.push(v));
        out
    }

    /// Visit each mutable SSA operand (use) of this op in exact
    /// [`Op::operands`] order without allocating.
    pub fn for_each_operand_mut<'a, F: FnMut(&'a mut ValueId)>(&'a mut self, mut f: F) {
        use Op::*;
        match self {
            BinaryOp { left, right, .. } | Compare { left, right, .. } => {
                f(left);
                f(right);
            }
            UnaryOp { operand, .. } => f(operand),
            Mov { src } => f(src),
            LoadConst(_) | AllocObject { .. } | AllocArray { .. } | AllocRegExp { .. } => {}
            AllocClosure { func } => f(func),
            LoadProp { object, .. } => f(object),
            StoreProp { object, value, .. } | StoreOwnPropName { object, value, .. } => {
                f(object);
                f(value);
            }
            LoadPropIdx { object, index } | LoadPropDyn { object, key: index } => {
                f(object);
                f(index);
            }
            StorePropIdx {
                object,
                index,
                value,
            }
            | StorePropDyn {
                object,
                key: index,
                value,
            }
            | StoreOwnPropDyn {
                object,
                key: index,
                value,
                ..
            }
            | StoreOwnPropIdx {
                object,
                index,
                value,
                ..
            } => {
                f(object);
                f(index);
                f(value);
            }
            DefineMethod { object, func, .. } => {
                f(object);
                f(func);
            }
            DeleteProp { object, key } => {
                f(object);
                f(key);
            }
            TestProp { object, key } => {
                f(object);
                match key {
                    PropKey::Name(_) => {}
                    PropKey::Index(k) | PropKey::Dynamic(k) => f(k),
                }
            }
            CopyDataProps { dst, src } => {
                f(dst);
                f(src);
            }
            SetObjectWithProto { proto, obj } => {
                f(proto);
                f(obj);
            }
            ArraySpread { dst, index, src } => {
                f(dst);
                f(index);
                f(src);
            }
            CreateObjectWithExcludedKeys { obj, keys } => {
                f(obj);
                for k in keys {
                    f(k);
                }
            }
            DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                set_name,
            } => {
                f(obj);
                f(key);
                f(getter);
                f(setter);
                f(set_name);
            }
            GetTemplateObject { literal } => f(literal),
            CreateIterResultObj { value, done } => {
                f(value);
                f(done);
            }
            GetIterator { obj } | GetPropIterator { obj } | GetAsyncIterator { obj } => f(obj),
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator }
            | NextPropName { iterator } => f(iterator),
            NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | CreatePrivateNames { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | AsyncFunctionEnter
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | Debugger => {}
            PutLexVar { value, .. } => f(value),
            TryGetGlobal { default, .. } => {
                if let Some(v) = default {
                    f(v);
                }
            }
            StoreGlobal { value, .. }
            | StoreGlobalRecord { value, .. }
            | TryStoreGlobal { value, .. }
            | StoreModuleVar { value, .. } => f(value),
            LoadModuleVar { .. } | GetModuleNamespace { .. } => {}
            DynamicImport { specifier } => f(specifier),
            Call {
                callee, this, args, ..
            } => {
                f(callee);
                if let Some(t) = this {
                    f(t);
                }
                for arg in args {
                    f(arg);
                }
            }
            DefineFunc { captures, .. } => {
                for (_, v) in captures {
                    f(v);
                }
            }
            DefineClass(d) | DefineSendableClass(d) => {
                if let Some(h) = &mut d.heritage {
                    f(h);
                }
            }
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => f(obj),
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                f(obj);
                f(value);
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | ThrowUndefinedIfHoleWithName { value, .. }
            | Await { value }
            | NotifyConcurrentResult { value } => f(value),
            AwaitUncaught { funcobj, value }
            | AsyncResolve { funcobj, value }
            | AsyncReject { funcobj, value }
            | AsyncGeneratorReject {
                genobj: funcobj,
                value,
            } => {
                f(funcobj);
                f(value);
            }
            AsyncGeneratorResolve {
                genobj,
                value,
                done,
            } => {
                f(genobj);
                f(value);
                f(done);
            }
            ThrowUndefinedIfHole { name, value } => {
                f(name);
                f(value);
            }
            CreateGenerator { func } | CreateAsyncGenerator { func } => f(func),
            SuspendGenerator { genobj, value } => {
                f(genobj);
                f(value);
            }
            ResumeGenerator { genobj }
            | GetResumeMode { genobj }
            | SetGeneratorState { genobj, .. } => f(genobj),
            LoadSuper { key, this_value } => match key {
                SuperKey::Name(_) => f(this_value),
                SuperKey::Dynamic(k) => {
                    f(k);
                    f(this_value);
                }
            },
            StoreSuper {
                key,
                this_value,
                value,
            } => {
                f(value);
                f(this_value);
                if let SuperKey::Dynamic(k) = key {
                    f(k);
                }
            }
            Branch { .. } | Unreachable => {}
            CondBranch { cond, .. } => f(cond),
            Return { value } => {
                if let Some(v) = value {
                    f(v);
                }
            }
            Phi { entries } => {
                for (_, v) in entries {
                    f(v);
                }
            }
        }
    }

    /// Mutable views of all SSA operands, in the same order as
    /// [`Op::operands`]. Single-sourced wrapper over [`Op::for_each_operand_mut`].
    pub fn operands_mut(&mut self) -> Vec<&mut ValueId> {
        let mut out = match self.arity() {
            Arity::Exact(n) => Vec::with_capacity(n),
            Arity::Variadic => Vec::new(),
        };
        self.for_each_operand_mut(|v| out.push(v));
        out
    }

    /// Whether this op produces an SSA result.
    pub fn has_result(&self) -> bool {
        use Op::*;
        !matches!(
            self,
            StoreProp { .. }
                | StorePropIdx { .. }
                | StorePropDyn { .. }
                | StoreOwnPropName { .. }
                | StoreOwnPropDyn { .. }
                | StoreOwnPropIdx { .. }
                | StoreSuper { .. }
                | CopyDataProps { .. }
                | SetObjectWithProto { .. }
                | StorePrivate { .. }
                | DefinePrivate { .. }
                | CreatePrivateNames { .. }
                | PutLexVar { .. }
                | PopLexEnv
                | StoreGlobal { .. }
                | StoreGlobalRecord { .. }
                | TryStoreGlobal { .. }
                | StoreModuleVar { .. }
                | SetGeneratorState { .. }
                | NotifyConcurrentResult { .. }
                | Throw { .. }
                | ThrowIfSuperNotCalled { .. }
                | ThrowUndefinedIfHole { .. }
                | ThrowUndefinedIfHoleWithName { .. }
                | ThrowConstAssignment { .. }
                | ThrowIfNotObject { .. }
                | ThrowNotExists
                | ThrowPatternNonCoercible
                | ThrowDeleteSuperProperty
                | Debugger
                | Branch { .. }
                | CondBranch { .. }
                | Return { .. }
                | Unreachable
        )
    }

    /// Whether this op is a block terminator.
    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            Op::Branch { .. } | Op::CondBranch { .. } | Op::Return { .. } | Op::Unreachable
        )
    }

    /// Whether this op is a phi node.
    pub fn is_phi(&self) -> bool {
        matches!(self, Op::Phi { .. })
    }

    /// The op's declared operand arity (taxonomy table; verifier-checked
    /// against [`Op::operands`] as a drift guard). Variadic ops (`Call`,
    /// `Phi`, `DefineFunc`, optional operands, key enums) are constrained
    /// by their own rules — e.g. a phi's entry count must equal the
    /// block's predecessor count.
    pub fn arity(&self) -> Arity {
        use Op::*;
        match self {
            BinaryOp { .. } | Compare { .. } => Arity::Exact(2),
            UnaryOp { .. }
            | Mov { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | GetIterator { .. }
            | GetPropIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | NextPropName { .. }
            | PutLexVar { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | StoreModuleVar { .. }
            | DynamicImport { .. }
            | LoadPrivate { .. }
            | TestPrivate { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | NotifyConcurrentResult { .. }
            | GetAsyncIterator { .. }
            | GetTemplateObject { .. }
            | ThrowUndefinedIfHoleWithName { .. } => Arity::Exact(1),
            LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | LoadModuleVar { .. }
            | GetModuleNamespace { .. }
            | CreatePrivateNames { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | AsyncFunctionEnter
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | Debugger
            | Branch { .. }
            | Unreachable => Arity::Exact(0),
            StoreProp { .. }
            | StoreOwnPropName { .. }
            | DefineMethod { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | CreateIterResultObj { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | DeleteProp { .. }
            | LoadPropIdx { .. }
            | LoadPropDyn { .. }
            | ThrowUndefinedIfHole { .. }
            | SuspendGenerator { .. }
            | AwaitUncaught { .. }
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorReject { .. } => Arity::Exact(2),
            StorePropIdx { .. } | StorePropDyn { .. } => Arity::Exact(3),
            StoreOwnPropDyn { .. } | StoreOwnPropIdx { .. } => Arity::Exact(3),
            ArraySpread { .. } | AsyncGeneratorResolve { .. } => Arity::Exact(3),
            DefineGetterSetterByValue { .. } => Arity::Exact(5),
            CondBranch { .. } => Arity::Exact(1),
            TestProp { .. }
            | TryGetGlobal { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | CreateObjectWithExcludedKeys { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Return { .. }
            | Phi { .. } => Arity::Variadic,
        }
    }

    /// Visit every [`ConstId`] referenced directly by this op.
    pub fn for_each_const_id<F: FnMut(ConstId)>(&self, mut f: F) {
        use Op::*;
        match self {
            LoadConst(c) => f(*c),
            AllocObject { shape } => f(*shape),
            AllocArray { shape } => {
                if let Some(c) = shape {
                    f(*c);
                }
            }
            NewLexEnvWithName { scope_names, .. } => f(*scope_names),
            DefineClass(d) | DefineSendableClass(d) => f(d.members),
            CreatePrivateNames { names, .. } => f(*names),
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit every [`FuncId`] referenced directly by this op.
    pub fn for_each_func_id<F: FnMut(FuncId)>(&self, mut f: F) {
        use Op::*;
        match self {
            DefineFunc { body, .. } => f(*body),
            DefineClass(d) | DefineSendableClass(d) => f(d.ctor),
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit every [`Sym`] referenced directly by this op (including capture
    /// names in [`Op::DefineFunc`]).
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        use Op::*;
        match self {
            AllocRegExp { pattern, .. } => f(*pattern),
            LoadProp { name, .. }
            | StoreProp { name, .. }
            | StoreOwnPropName { name, .. }
            | DefineMethod { name, .. }
            | TryGetGlobal { name, .. }
            | StoreGlobal { name, .. }
            | StoreGlobalRecord { name, .. }
            | TryStoreGlobal { name, .. }
            | ThrowUndefinedIfHoleWithName { name, .. } => f(*name),
            TestProp { key, .. } => {
                if let PropKey::Name(s) = key {
                    f(*s);
                }
            }
            DefineFunc { captures, .. } => {
                for &(s, _) in captures {
                    f(s);
                }
            }
            LoadSuper { key, .. } | StoreSuper { key, .. } => {
                if let SuperKey::Name(s) = key {
                    f(*s);
                }
            }
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocClosure { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DeleteProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit every [`BlockId`] referenced directly by this op (terminator
    /// targets and [`Op::Phi`] incoming edge sources).
    pub fn for_each_block_id<F: FnMut(BlockId)>(&self, mut f: F) {
        use Op::*;
        match self {
            Branch { dest } => f(*dest),
            CondBranch {
                true_dest,
                false_dest,
                ..
            } => {
                f(*true_dest);
                f(*false_dest);
            }
            Phi { entries } => {
                for (edge, _) in entries {
                    f(edge.from);
                }
            }
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Return { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit each mutable [`BlockId`] referenced directly by this op in exact
    /// [`Op::for_each_block_id`] order.
    pub fn for_each_block_id_mut<'a, F: FnMut(&'a mut BlockId)>(&'a mut self, mut f: F) {
        use Op::*;
        match self {
            Branch { dest } => f(dest),
            CondBranch {
                true_dest,
                false_dest,
                ..
            } => {
                f(true_dest);
                f(false_dest);
            }
            Phi { entries } => {
                for (edge, _) in entries {
                    f(&mut edge.from);
                }
            }
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Return { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit each mutable [`ConstId`] referenced directly by this op in exact
    /// [`Op::for_each_const_id`] order.
    pub fn for_each_const_id_mut<'a, F: FnMut(&'a mut ConstId)>(&'a mut self, mut f: F) {
        use Op::*;
        match self {
            LoadConst(c) => f(c),
            AllocObject { shape } => f(shape),
            AllocArray { shape } => {
                if let Some(c) = shape {
                    f(c);
                }
            }
            NewLexEnvWithName { scope_names, .. } => f(scope_names),
            DefineClass(d) | DefineSendableClass(d) => f(&mut d.members),
            CreatePrivateNames { names, .. } => f(names),
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit each mutable [`FuncId`] referenced directly by this op in exact
    /// [`Op::for_each_func_id`] order.
    pub fn for_each_func_id_mut<'a, F: FnMut(&'a mut FuncId)>(&'a mut self, mut f: F) {
        use Op::*;
        match self {
            DefineFunc { body, .. } => f(body),
            DefineClass(d) | DefineSendableClass(d) => f(&mut d.ctor),
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit each mutable [`Sym`] referenced directly by this op in exact
    /// [`Op::for_each_sym`] order.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        use Op::*;
        match self {
            AllocRegExp { pattern, .. } => f(pattern),
            LoadProp { name, .. }
            | StoreProp { name, .. }
            | StoreOwnPropName { name, .. }
            | DefineMethod { name, .. }
            | TryGetGlobal { name, .. }
            | StoreGlobal { name, .. }
            | StoreGlobalRecord { name, .. }
            | TryStoreGlobal { name, .. }
            | ThrowUndefinedIfHoleWithName { name, .. } => f(name),
            TestProp { key, .. } => {
                if let PropKey::Name(s) = key {
                    f(s);
                }
            }
            DefineFunc { captures, .. } => {
                for (s, _) in captures {
                    f(s);
                }
            }
            LoadSuper { key, .. } | StoreSuper { key, .. } => {
                if let SuperKey::Name(s) = key {
                    f(s);
                }
            }
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocClosure { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DeleteProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit every [`ClassId`] referenced directly by this op.
    ///
    /// Exhaustive over all 94 [`Op`] variants so adding any class-referencing
    /// payload in the future is enforced at compile time.
    pub fn for_each_class_id<F: FnMut(ClassId)>(&self, mut _f: F) {
        use Op::*;
        match self {
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Visit each mutable [`ClassId`] referenced directly by this op in exact
    /// [`Op::for_each_class_id`] order.
    pub fn for_each_class_id_mut<'a, F: FnMut(&'a mut ClassId)>(&'a mut self, mut _f: F) {
        use Op::*;
        match self {
            BinaryOp { .. }
            | UnaryOp { .. }
            | Compare { .. }
            | Mov { .. }
            | LoadConst(_)
            | AllocObject { .. }
            | AllocArray { .. }
            | AllocRegExp { .. }
            | AllocClosure { .. }
            | LoadProp { .. }
            | StoreProp { .. }
            | LoadPropIdx { .. }
            | StorePropIdx { .. }
            | LoadPropDyn { .. }
            | StorePropDyn { .. }
            | StoreOwnPropName { .. }
            | StoreOwnPropDyn { .. }
            | StoreOwnPropIdx { .. }
            | DefineMethod { .. }
            | DeleteProp { .. }
            | TestProp { .. }
            | CopyDataProps { .. }
            | SetObjectWithProto { .. }
            | ArraySpread { .. }
            | CreateObjectWithExcludedKeys { .. }
            | DefineGetterSetterByValue { .. }
            | GetTemplateObject { .. }
            | CreateIterResultObj { .. }
            | GetIterator { .. }
            | GetAsyncIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | GetPropIterator { .. }
            | NextPropName { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | GetLexVar { .. }
            | PutLexVar { .. }
            | TryGetGlobal { .. }
            | StoreGlobal { .. }
            | StoreGlobalRecord { .. }
            | TryStoreGlobal { .. }
            | LoadModuleVar { .. }
            | StoreModuleVar { .. }
            | GetModuleNamespace { .. }
            | DynamicImport { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass(_)
            | DefineSendableClass(_)
            | LoadPrivate { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | TestPrivate { .. }
            | CreatePrivateNames { .. }
            | Throw { .. }
            | ThrowIfSuperNotCalled { .. }
            | ThrowUndefinedIfHole { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | ThrowIfNotObject { .. }
            | CreateGenerator { .. }
            | CreateAsyncGenerator { .. }
            | SetGeneratorState { .. }
            | SuspendGenerator { .. }
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | AsyncFunctionEnter
            | AsyncResolve { .. }
            | AsyncReject { .. }
            | AsyncGeneratorResolve { .. }
            | AsyncGeneratorReject { .. }
            | NotifyConcurrentResult { .. }
            | LoadSymbol
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Branch { .. }
            | CondBranch { .. }
            | Return { .. }
            | Phi { .. }
            | Unreachable
            | Debugger => {}
        }
    }

    /// Whether this op unconditionally produces an ECMAScript boolean result
    /// from its opcode semantics alone (`Compare`, boolean `UnaryOp`,
    /// `TestProp`, `TestPrivate`, `DeleteProp`).
    #[must_use]
    pub const fn produces_bool(&self) -> bool {
        match self {
            Op::Compare { .. }
            | Op::TestProp { .. }
            | Op::TestPrivate { .. }
            | Op::DeleteProp { .. } => true,
            Op::UnaryOp { op, .. } => op.is_boolean_result(),
            _ => false,
        }
    }

    /// Context-sensitive boolean-result query inspecting `module` constants,
    /// `Mov` chains, and `Phi` inputs when [`Op::produces_bool`] is `false`.
    #[must_use]
    pub fn produces_bool_in(&self, module: &Module) -> bool {
        let is_val_bool = |start: ValueId| -> bool {
            let mut cur = start;
            let limit = module.values.len();
            for _ in 0..=limit {
                let Some(val) = module.value(cur) else {
                    return false;
                };
                if matches!(
                    val.ty,
                    Ty::DynPrim(DynPrim::Bool) | Ty::Static(StaticTy::U1)
                ) {
                    return true;
                }
                match val.def {
                    ValueDef::Const(cid) => {
                        return matches!(module.consts.get(cid), Some(Const::Bool(_)));
                    }
                    ValueDef::Inst(iid) => {
                        let Some(inst) = module.inst(iid) else {
                            return false;
                        };
                        if inst.op.produces_bool() {
                            return true;
                        }
                        match &inst.op {
                            Op::LoadConst(cid) => {
                                return matches!(module.consts.get(*cid), Some(Const::Bool(_)));
                            }
                            Op::Mov { src } => {
                                if *src == cur {
                                    return false;
                                }
                                cur = *src;
                            }
                            _ => return false,
                        }
                    }
                    ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
                }
            }
            false
        };

        if self.produces_bool() {
            return true;
        }
        match self {
            Op::LoadConst(cid) => matches!(module.consts.get(*cid), Some(Const::Bool(_))),
            Op::Mov { src } => is_val_bool(*src),
            Op::Phi { entries } => {
                !entries.is_empty() && entries.iter().all(|(_, v)| is_val_bool(*v))
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests;
