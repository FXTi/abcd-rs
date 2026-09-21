//! The op taxonomy (design/ir-v0.2.md §4.1, with §9's resolutions: **no
//! `Switch`**, a **single** `LoadPropIdx`/`StorePropIdx`).
//!
//! [`Op`] is a *closed* enum of semantic variants — zero opcode concepts:
//! width variants, typed/dynamic twins, and the call family all fold into
//! this set at lift; encoding selection is a lowering concern.
//!
//! Every consumer (passes, verifier, analyses) compiles against ONLY the
//! single-point interfaces [`Op::operands`], [`Op::operands_mut`],
//! [`Op::has_result`], and [`Op::is_terminator`] — never against a
//! hand-maintained variant list, so variant lists cannot drift.

use crate::function::Edge;
use crate::id::{BlockId, ConstId, FuncId, Sym, ValueId};

/// Binary arithmetic/bitwise operator kind. Typed twins
/// (`add_i32` vs `add_f64`) are `BinaryOp::Add` plus the result value's
/// [`Ty`](crate::ty::Ty), not two ops.
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
    /// `void x`.
    Void,
    /// ToBoolean truth test.
    IsTrue,
    /// ToBoolean falsity test.
    IsFalse,
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

/// Call kind — the §5.3 binding table:
///
/// | kind      | this binding                        | new.target    | args         |
/// |-----------|-------------------------------------|---------------|--------------|
/// | `Direct`  | `call.this`                         | undefined     | args→params[1..] |
/// | `Dynamic` | computed at callee entry            | undefined     | args→params[1..] |
/// | `Apply`   | `call.this` (explicit receiver)     | undefined     | SPREAD of args[0] |
/// | `Super`   | inherited from enclosing ctor       | inherited     | args→params[1..] |
/// | `SuperSpread` | inherited from enclosing ctor   | inherited     | SPREAD of args[0] |
/// | `SuperForwardAllArgs` | inherited               | inherited     | ALL own args (forwarded) |
/// | `New`     | fresh object from callee.prototype  | callee itself | args→params[1..] |
///
/// The result is the callee's return value; a throw inside the callee
/// flows to the caller's exceptional edges.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallKind {
    /// A statically resolved callee with an explicit `this`.
    Direct,
    /// A dynamically computed callee; `this` is computed at callee entry
    /// (non-strict = global, strict = undefined), so `Call::this` is
    /// `None`.
    Dynamic,
    /// `func.apply(this, argsArray)` — vendor `apply imm, v_this, v_args`
    /// (isa.yaml:1104, the func in the acc): the receiver is explicit and
    /// the single argument is an ARRAY spread over the formal parameters.
    /// Never an arity overload of [`CallKind::Dynamic`]: `Call::this` is
    /// `Some(receiver)` and `Call::args` is exactly `[array]` (N16/N57;
    /// v0.1 `CallKind::Apply`, isel emits the `apply` opcode).
    Apply,
    /// A `super(...)` call in a constructor with EXPLICIT arguments
    /// (vendor `supercallthisrange`/`supercallarrowrange`).
    Super,
    /// A `super(...args)` call spreading an argument ARRAY into the super
    /// constructor — vendor `supercallspread imm, v_args` (isa.yaml).
    /// `Call::this` is `None` (inherited) and `Call::args` is exactly
    /// `[array]` (N58; v0.1 `CallKind::SuperCallSpread`, isel emits the
    /// `supercallspread` opcode). Never a 1-argument [`CallKind::Super`].
    SuperSpread,
    /// Vendor `callruntime.supercallforwardallargs v_this` (isa.yaml): a
    /// default derived constructor forwarding ALL of its own arguments to
    /// the super constructor. v0.1's representation is kept verbatim
    /// (`CallKind::SuperCall`, args = `[this]` — the enclosing `this`
    /// models the forwarded argument list, lowering to
    /// `supercallthisrange` argc=1), but the KIND stays distinct from
    /// [`CallKind::Super`] so the lower never confuses the forward-all
    /// form with an explicit-arguments super call (N58).
    SuperForwardAllArgs,
    /// `new callee(args...)`.
    New,
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
    /// query for the analysis layer — §9 resolution 3).
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
#[derive(Clone, Debug)]
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
    /// shape). The object/array tag is OPCODE-carried (N59): it is not
    /// recoverable from the flat literal-buffer content, so it must
    /// come from the op, mirroring [`Op::AllocObject`]'s treatment.
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
    /// Integer-indexed element access: `object[index]` (single op — §9
    /// resolution 3).
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
    /// [`Op::StoreProp`] (N60; v0.1 `InstData::StoreOwnProperty` with
    /// `PropKind::ByName`, isel emits the `stownby*` family).
    StoreOwnPropName {
        /// The receiver object.
        object: ValueId,
        /// The property name.
        name: Sym,
        /// The stored value.
        value: ValueId,
    },
    /// Computed-key own-property store (vendor
    /// `stownbyvalue`(+withnameset)/`callruntime.definefieldbyvalue` —
    /// v0.1 `PropKind::ByValue`).
    StoreOwnPropDyn {
        /// The receiver object.
        object: ValueId,
        /// The computed key.
        key: ValueId,
        /// The stored value.
        value: ValueId,
    },
    /// Integer-indexed own-property store (vendor
    /// `stownbyindex`/`wide.stownbyindex`/
    /// `callruntime.definefieldbyindex` — v0.1 `PropKind::ByIndex`).
    StoreOwnPropIdx {
        /// The receiver object.
        object: ValueId,
        /// The index.
        index: ValueId,
        /// The stored value.
        value: ValueId,
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
    /// (isa.yaml:1220): define an accessor property on `obj` under the
    /// computed `key` with the given `getter`/`setter` closures.
    DefineGetterSetterByValue {
        /// The target object.
        obj: ValueId,
        /// The computed property key.
        key: ValueId,
        /// The getter closure.
        getter: ValueId,
        /// The setter closure.
        setter: ValueId,
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
    /// Push a new lexical environment with `num_vars` slots, yielding it
    /// (vendor `newlexenv` / `wide.newlexenv`, isa.yaml; v0.2's original
    /// `GetLexEnv` renamed to the ISA-honest name and given its payload).
    NewLexEnv {
        /// Number of variables in the new environment.
        num_vars: u16,
    },
    /// Push a new NAMED lexical environment, yielding it (vendor
    /// `newlexenvwithname` / `wide.newlexenvwithname`, isa.yaml): the
    /// scope's variable names come from a literal-array constant.
    NewLexEnvWithName {
        /// Number of variables in the new environment.
        num_vars: u16,
        /// The scope-names constant (an
        /// [`Const::ArrayLiteral`](crate::consts::Const::ArrayLiteral) of
        /// [`Const::String`](crate::consts::Const::String) names).
        scope_names: ConstId,
    },
    /// Pop the current lexical environment (vendor `poplexenv`,
    /// isa.yaml:367-370). Void, but observable: the lexical scope
    /// discipline is part of the program's semantics (round-tripping
    /// and the lexical model depend on it).
    PopLexEnv,
    /// Load a lexical variable by environment level and slot.
    GetLexVar {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
    },
    /// Store a lexical variable by environment level and slot.
    PutLexVar {
        /// Scope-chain level.
        level: u16,
        /// Slot within the environment.
        slot: u16,
        /// The stored value.
        value: ValueId,
    },
    /// Load a global by name, tolerating absence (`default` when the
    /// global does not exist). Absence-tolerant does NOT mean
    /// side-effect-free: the vendored slow paths of both source forms
    /// (`ldglobalvar`, `tryldglobalbyname`) run `GetProperty` on the
    /// global's prototype chain — global getters are called and the
    /// calls are abrupt-checked (see [`Op::effects`], N48/N50).
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
    /// Store a global by name, TOLERANT of absence (vendor
    /// `trystglobalbyname`): no ReferenceError when the global does not
    /// exist — unlike the throwing [`Op::StoreGlobal`] (N61; v0.1
    /// `InstData::TryStoreGlobalByName`).
    TryStoreGlobal {
        /// The global's name.
        name: Sym,
        /// The stored value.
        value: ValueId,
    },
    /// Load a module-local variable by its module slot.
    LoadModuleVar {
        /// The module-variable slot (module semantics, not a file pool
        /// index).
        index: u32,
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
    /// A call (T4; one semantic op for the whole callthis/callshort/
    /// callrange family). Binding per [`CallKind`] (§5.3 table above).
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
    /// Define a class with a member buffer.
    DefineClass {
        /// The constructor in the module's function table.
        ctor: FuncId,
        /// The heritage (`extends`) expression value, when present.
        heritage: Option<ValueId>,
        /// The member-buffer constant (an
        /// [`Const::ObjectLiteral`](crate::consts::Const::ObjectLiteral)/
        /// [`Const::ArrayLiteral`](crate::consts::Const::ArrayLiteral)
        /// shape with [`Const::MethodRef`](crate::consts::Const::MethodRef)
        /// entries).
        members: ConstId,
        /// The class constructor's `.length` (vendor
        /// `defineclasswithbuffer imm2`, isa.yaml) — the runtime consumes
        /// it via RuntimeSetClassConstructorLength (N15); modeled for
        /// byte fidelity and semantics.
        count: u16,
    },
    /// Define a SENDABLE (shared) class with a member buffer — vendor
    /// `callruntime.definesendableclass imm1:u16, method_id,
    /// literalarray_id, imm2:u16, v:in:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:861-866).
    ///
    /// Distinct from [`Op::DefineClass`] (N53): the vendor runtime
    /// builds the class through `SlowRuntimeStub::CreateSharedClass`
    /// (arkcompiler_ets_runtime-master/ecmascript/interpreter/
    /// interpreter_assembly.cpp:6157-6180,
    /// `HandleCallRuntimeDefineSendableClassPrefImm16Id16Id16Imm16V8` —
    /// `ASSERT(res.IsJSSharedFunction())`), NOT the contemporary
    /// `defineclasswithbuffer`'s `SlowRuntimeStub::CreateClassWithBuffer`
    /// (interpreter_assembly.cpp:6007/6033). v0.1 collapsed this opcode
    /// into `InstData::DefineClassWithBuffer` and its isel re-emitted
    /// the CONTEMPORARY `defineclasswithbuffer` — opcode-identity
    /// corruption. The 24.0.0.0 sendable fixtures are runtime-N/A
    /// (structural only, not in the 1149-fixture VM set), so no VM
    /// evidence is possible; the distinction is anchored to the vendor
    /// sources above.
    DefineSendableClass {
        /// The constructor in the module's function table.
        ctor: FuncId,
        /// The heritage (`extends`) expression value, when present
        /// (vendor `v:in:top` — `base` in the handler).
        heritage: Option<ValueId>,
        /// The member-buffer constant (same shape as
        /// [`Op::DefineClass::members`]).
        members: ConstId,
        /// The class constructor's `.length` (vendor imm2, isa.yaml) —
        /// `CreateSharedClass` consumes it the way
        /// `CreateClassWithBuffer` consumes the contemporary form's
        /// (N15).
        count: u16,
    },

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
        /// The private-name strings (an
        /// [`Const::ArrayLiteral`](crate::consts::Const::ArrayLiteral) of
        /// [`Const::String`](crate::consts::Const::String)) — vendor
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
    /// Vendor `asyncfunctionawaituncaught v:in:top, acc: out:top`
    /// (isa.yaml) — the es2abc await form: await `value` without the
    /// caught-completion wrapper. Distinct from [`Op::Await`]; lift
    /// emits this op for the (deprecated.)asyncfunctionawaituncaught
    /// bytecodes.
    AwaitUncaught {
        /// The awaited value.
        value: ValueId,
    },
    /// Vendor `asyncfunctionenter` (isa.yaml, `acc: out:top`): enter an
    /// async function, yielding the async context/promise value.
    AsyncFunctionEnter,
    /// Resolve the async function's promise.
    AsyncResolve {
        /// The resolution value.
        value: ValueId,
    },
    /// Reject the async function's promise.
    AsyncReject {
        /// The rejection reason.
        value: ValueId,
    },

    // ── Frame / special value loaders ──────────────────────────────────
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
    },
    /// Super-property store.
    StoreSuper {
        /// The property key.
        key: SuperKey,
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
    /// SSA phi: one entry per incoming edge (§5.1 — entries reference
    /// `(Edge, ValueId)`; the value flows from the edge's source block).
    Phi {
        /// `(incoming edge, value)` pairs.
        entries: Vec<(Edge, ValueId)>,
    },
    /// Dead control point.
    Unreachable,

    // ── Debug ──────────────────────────────────────────────────────────
    /// Vendor `debugger` (isa.yaml): a debugger breakpoint — observable
    /// when a debugger is attached (v0.1 kept it essential; the effect
    /// record models the potential debugger hook).
    Debugger,
}

impl Op {
    /// All SSA operands (uses) of this op. Block/const/symbol/func
    /// payloads are not SSA operands and are not returned.
    pub fn operands(&self) -> Vec<ValueId> {
        use Op::*;
        match self {
            BinaryOp { left, right, .. } | Compare { left, right, .. } => vec![*left, *right],
            UnaryOp { operand, .. } => vec![*operand],
            Mov { src } => vec![*src],
            LoadConst(_) | AllocObject { .. } | AllocArray { .. } | AllocRegExp { .. } => vec![],
            AllocClosure { func } => vec![*func],
            LoadProp { object, .. } => vec![*object],
            StoreProp { object, value, .. } => vec![*object, *value],
            StoreOwnPropName { object, value, .. } => vec![*object, *value],
            LoadPropIdx { object, index } | LoadPropDyn { object, key: index } => {
                vec![*object, *index]
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
            } => vec![*object, *index, *value],
            StoreOwnPropDyn {
                object,
                key: index,
                value,
            }
            | StoreOwnPropIdx {
                object,
                index,
                value,
            } => vec![*object, *index, *value],
            DefineMethod { object, func, .. } => vec![*object, *func],
            DeleteProp { object, key } => vec![*object, *key],
            TestProp { object, key } => {
                let mut v = vec![*object];
                match key {
                    PropKey::Name(_) => {}
                    PropKey::Index(k) | PropKey::Dynamic(k) => v.push(*k),
                }
                v
            }
            CopyDataProps { dst, src } => vec![*dst, *src],
            SetObjectWithProto { proto, obj } => vec![*proto, *obj],
            ArraySpread { dst, index, src } => vec![*dst, *index, *src],
            CreateObjectWithExcludedKeys { obj, keys } => {
                let mut v = vec![*obj];
                v.extend(keys.iter());
                v
            }
            DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
            } => vec![*obj, *key, *getter, *setter],
            GetTemplateObject { literal } => vec![*literal],
            CreateIterResultObj { value, done } => vec![*value, *done],
            GetIterator { obj } | GetPropIterator { obj } | GetAsyncIterator { obj } => vec![*obj],
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator } => {
                vec![*iterator]
            }
            NextPropName { iterator } => vec![*iterator],
            NewLexEnv { .. } | NewLexEnvWithName { .. } | PopLexEnv | GetLexVar { .. } => vec![],
            CreatePrivateNames { .. } => vec![],
            LoadNewTarget | LoadGlobalObject | LoadFunction => vec![],
            GetUnmappedArgs | CopyRestArgs { .. } | AsyncFunctionEnter => vec![],
            ThrowNotExists | ThrowPatternNonCoercible | ThrowDeleteSuperProperty | Debugger => {
                vec![]
            }
            PutLexVar { value, .. } => vec![*value],
            TryGetGlobal { default, .. } => default.iter().copied().collect(),
            StoreGlobal { value, .. }
            | TryStoreGlobal { value, .. }
            | StoreModuleVar { value, .. } => {
                vec![*value]
            }
            LoadModuleVar { .. } | GetModuleNamespace { .. } => vec![],
            DynamicImport { specifier } => vec![*specifier],
            Call {
                callee, this, args, ..
            } => {
                let mut v = vec![*callee];
                v.extend(this.iter());
                v.extend(args.iter());
                v
            }
            DefineFunc { captures, .. } => captures.iter().map(|(_, v)| *v).collect(),
            DefineClass { heritage, .. } | DefineSendableClass { heritage, .. } => {
                heritage.iter().copied().collect()
            }
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => vec![*obj],
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                vec![*obj, *value]
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | ThrowUndefinedIfHoleWithName { value, .. }
            | Await { value }
            | AwaitUncaught { value }
            | AsyncResolve { value }
            | AsyncReject { value } => vec![*value],
            ThrowUndefinedIfHole { name, value } => vec![*name, *value],
            CreateGenerator { func } => vec![*func],
            SuspendGenerator { genobj, value } => vec![*genobj, *value],
            ResumeGenerator { genobj } | GetResumeMode { genobj } => vec![*genobj],
            LoadSuper { key } => match key {
                SuperKey::Name(_) => vec![],
                SuperKey::Dynamic(k) => vec![*k],
            },
            StoreSuper { key, value } => {
                let mut v = vec![*value];
                if let SuperKey::Dynamic(k) = key {
                    v.push(*k);
                }
                v
            }
            Branch { .. } | Unreachable => vec![],
            CondBranch { cond, .. } => vec![*cond],
            Return { value } => value.iter().copied().collect(),
            Phi { entries } => entries.iter().map(|(_, v)| *v).collect(),
        }
    }

    /// Mutable views of all SSA operands, in the same order as
    /// [`Op::operands`]. The single mutation point for passes that rewrite
    /// uses.
    pub fn operands_mut(&mut self) -> Vec<&mut ValueId> {
        use Op::*;
        match self {
            BinaryOp { left, right, .. } | Compare { left, right, .. } => vec![left, right],
            UnaryOp { operand, .. } => vec![operand],
            Mov { src } => vec![src],
            LoadConst(_) | AllocObject { .. } | AllocArray { .. } | AllocRegExp { .. } => vec![],
            AllocClosure { func } => vec![func],
            LoadProp { object, .. } => vec![object],
            StoreProp { object, value, .. } => vec![object, value],
            StoreOwnPropName { object, value, .. } => vec![object, value],
            LoadPropIdx { object, index } | LoadPropDyn { object, key: index } => {
                vec![object, index]
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
            } => vec![object, index, value],
            StoreOwnPropDyn {
                object,
                key: index,
                value,
            }
            | StoreOwnPropIdx {
                object,
                index,
                value,
            } => vec![object, index, value],
            DefineMethod { object, func, .. } => vec![object, func],
            DeleteProp { object, key } => vec![object, key],
            TestProp { object, key } => {
                let mut v = vec![object];
                match key {
                    PropKey::Name(_) => {}
                    PropKey::Index(k) | PropKey::Dynamic(k) => v.push(k),
                }
                v
            }
            CopyDataProps { dst, src } => vec![dst, src],
            SetObjectWithProto { proto, obj } => vec![proto, obj],
            ArraySpread { dst, index, src } => vec![dst, index, src],
            CreateObjectWithExcludedKeys { obj, keys } => {
                let mut v = vec![obj];
                v.extend(keys.iter_mut());
                v
            }
            DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
            } => vec![obj, key, getter, setter],
            GetTemplateObject { literal } => vec![literal],
            CreateIterResultObj { value, done } => vec![value, done],
            GetIterator { obj } | GetPropIterator { obj } | GetAsyncIterator { obj } => vec![obj],
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator } => {
                vec![iterator]
            }
            NextPropName { iterator } => vec![iterator],
            NewLexEnv { .. } | NewLexEnvWithName { .. } | PopLexEnv | GetLexVar { .. } => vec![],
            CreatePrivateNames { .. } => vec![],
            LoadNewTarget | LoadGlobalObject | LoadFunction => vec![],
            GetUnmappedArgs | CopyRestArgs { .. } | AsyncFunctionEnter => vec![],
            ThrowNotExists | ThrowPatternNonCoercible | ThrowDeleteSuperProperty | Debugger => {
                vec![]
            }
            PutLexVar { value, .. } => vec![value],
            TryGetGlobal { default, .. } => default.iter_mut().collect(),
            StoreGlobal { value, .. }
            | TryStoreGlobal { value, .. }
            | StoreModuleVar { value, .. } => {
                vec![value]
            }
            LoadModuleVar { .. } | GetModuleNamespace { .. } => vec![],
            DynamicImport { specifier } => vec![specifier],
            Call {
                callee, this, args, ..
            } => {
                let mut v: Vec<&mut ValueId> = vec![callee];
                v.extend(this.iter_mut());
                v.extend(args.iter_mut());
                v
            }
            DefineFunc { captures, .. } => captures.iter_mut().map(|(_, v)| v).collect(),
            DefineClass { heritage, .. } | DefineSendableClass { heritage, .. } => {
                heritage.iter_mut().collect()
            }
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => vec![obj],
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                vec![obj, value]
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | ThrowUndefinedIfHoleWithName { value, .. }
            | Await { value }
            | AwaitUncaught { value }
            | AsyncResolve { value }
            | AsyncReject { value } => vec![value],
            ThrowUndefinedIfHole { name, value } => vec![name, value],
            CreateGenerator { func } => vec![func],
            SuspendGenerator { genobj, value } => vec![genobj, value],
            ResumeGenerator { genobj } | GetResumeMode { genobj } => vec![genobj],
            LoadSuper { key } => match key {
                SuperKey::Name(_) => vec![],
                SuperKey::Dynamic(k) => vec![k],
            },
            StoreSuper { key, value } => {
                let mut v = vec![value];
                if let SuperKey::Dynamic(k) = key {
                    v.push(k);
                }
                v
            }
            Branch { .. } | Unreachable => vec![],
            CondBranch { cond, .. } => vec![cond],
            Return { value } => value.iter_mut().collect(),
            Phi { entries } => entries.iter_mut().map(|(_, v)| v).collect(),
        }
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
                | TryStoreGlobal { .. }
                | StoreModuleVar { .. }
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
            | ResumeGenerator { .. }
            | GetResumeMode { .. }
            | Await { .. }
            | AwaitUncaught { .. }
            | GetAsyncIterator { .. }
            | GetTemplateObject { .. }
            | ThrowUndefinedIfHoleWithName { .. }
            | AsyncResolve { .. }
            | AsyncReject { .. } => Arity::Exact(1),
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
            | SuspendGenerator { .. } => Arity::Exact(2),
            StorePropIdx { .. } | StorePropDyn { .. } => Arity::Exact(3),
            StoreOwnPropDyn { .. } | StoreOwnPropIdx { .. } => Arity::Exact(3),
            ArraySpread { .. } => Arity::Exact(3),
            DefineGetterSetterByValue { .. } => Arity::Exact(4),
            CondBranch { .. } => Arity::Exact(1),
            TestProp { .. }
            | TryGetGlobal { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass { .. }
            | DefineSendableClass { .. }
            | CreateObjectWithExcludedKeys { .. }
            | LoadSuper { .. }
            | StoreSuper { .. }
            | Return { .. }
            | Phi { .. } => Arity::Variadic,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two single-point operand accessors must agree (drift guard
    /// behind the verifier's arity check).
    #[test]
    fn operands_and_operands_mut_agree() {
        let v = || ValueId::new(1);
        let s = Sym::new(0);
        let mut ops = vec![
            Op::BinaryOp {
                op: BinOp::Add,
                left: v(),
                right: v(),
            },
            Op::UnaryOp {
                op: UnOp::Minus,
                operand: v(),
            },
            Op::Mov { src: v() },
            Op::LoadConst(ConstId::new(0)),
            Op::AllocObject {
                shape: ConstId::new(0),
            },
            Op::LoadProp {
                object: v(),
                name: s,
            },
            Op::StorePropIdx {
                object: v(),
                index: v(),
                value: v(),
            },
            Op::DeleteProp {
                object: v(),
                key: v(),
            },
            Op::LoadPropIdx {
                object: v(),
                index: v(),
            },
            Op::LoadPropDyn {
                object: v(),
                key: v(),
            },
            Op::TestProp {
                object: v(),
                key: PropKey::Dynamic(v()),
            },
            Op::Call {
                callee: v(),
                this: Some(v()),
                args: vec![v(), v()],
                kind: CallKind::Direct,
            },
            Op::DefineFunc {
                body: FuncId::new(0),
                captures: vec![(s, v())],
                length: 2,
            },
            Op::Phi { entries: vec![] },
            Op::Branch {
                dest: BlockId::new(0),
            },
            Op::Return { value: Some(v()) },
            Op::Unreachable,
            // ── v2-P0.5 taxonomy growth: full ISA coverage ──
            Op::NewLexEnv { num_vars: 3 },
            Op::NewLexEnvWithName {
                num_vars: 3,
                scope_names: ConstId::new(0),
            },
            Op::PopLexEnv,
            Op::SetObjectWithProto {
                proto: v(),
                obj: v(),
            },
            Op::ArraySpread {
                dst: v(),
                index: v(),
                src: v(),
            },
            Op::CreateObjectWithExcludedKeys {
                obj: v(),
                keys: vec![v(), v()],
            },
            Op::DefineGetterSetterByValue {
                obj: v(),
                key: v(),
                getter: v(),
                setter: v(),
            },
            Op::GetTemplateObject { literal: v() },
            Op::CreateIterResultObj {
                value: v(),
                done: v(),
            },
            Op::GetAsyncIterator { obj: v() },
            Op::CopyRestArgs { start_index: 1 },
            Op::GetUnmappedArgs,
            Op::LoadNewTarget,
            Op::LoadGlobalObject,
            Op::LoadFunction,
            Op::AsyncFunctionEnter,
            Op::AwaitUncaught { value: v() },
            Op::ThrowUndefinedIfHoleWithName {
                name: s,
                value: v(),
            },
            Op::ThrowNotExists,
            Op::ThrowPatternNonCoercible,
            Op::ThrowDeleteSuperProperty,
            Op::Debugger,
            Op::DefineMethod {
                object: v(),
                name: s,
                func: v(),
                length: 1,
            },
            Op::DefineClass {
                ctor: FuncId::new(0),
                heritage: Some(v()),
                members: ConstId::new(0),
                count: 2,
            },
            Op::DefineSendableClass {
                ctor: FuncId::new(0),
                heritage: Some(v()),
                members: ConstId::new(0),
                count: 2,
            },
            Op::CreatePrivateNames {
                count: 2,
                names: ConstId::new(0),
            },
        ];
        for op in &mut ops {
            assert_eq!(op.operands().len(), op.operands_mut().len(), "{op:?}");
            if let Arity::Exact(n) = op.arity() {
                assert_eq!(op.operands().len(), n, "{op:?}");
            }
        }
    }
}
