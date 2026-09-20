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
/// | `Super`   | inherited from enclosing ctor       | inherited     | args→params[1..] |
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
    /// A `super(...)` call in a constructor.
    Super,
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
    /// Allocate an array (T7).
    AllocArray,
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
    /// Define a method on an object (class/object-literal semantics).
    DefineMethod {
        /// The home object.
        object: ValueId,
        /// The method name.
        name: Sym,
        /// The function value (a closure).
        func: ValueId,
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

    // ── Iteration ──────────────────────────────────────────────────────
    /// Get an iterator (`@@iterator` protocol).
    GetIterator {
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
    /// Push a new lexical environment, yielding it.
    GetLexEnv,
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
    /// global does not exist); never throws.
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
            LoadConst(_) | AllocObject { .. } | AllocArray | AllocRegExp { .. } => vec![],
            AllocClosure { func } => vec![*func],
            LoadProp { object, .. } => vec![*object],
            StoreProp { object, value, .. } => vec![*object, *value],
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
            GetIterator { obj } | GetPropIterator { obj } => vec![*obj],
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator } => {
                vec![*iterator]
            }
            NextPropName { iterator } => vec![*iterator],
            GetLexEnv | GetLexVar { .. } | CreatePrivateNames { .. } => vec![],
            PutLexVar { value, .. } => vec![*value],
            TryGetGlobal { default, .. } => default.iter().copied().collect(),
            StoreGlobal { value, .. } | StoreModuleVar { value, .. } => vec![*value],
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
            DefineClass { heritage, .. } => heritage.iter().copied().collect(),
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => vec![*obj],
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                vec![*obj, *value]
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | Await { value }
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
            LoadConst(_) | AllocObject { .. } | AllocArray | AllocRegExp { .. } => vec![],
            AllocClosure { func } => vec![func],
            LoadProp { object, .. } => vec![object],
            StoreProp { object, value, .. } => vec![object, value],
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
            GetIterator { obj } | GetPropIterator { obj } => vec![obj],
            IteratorNext { iterator }
            | IteratorReturn { iterator }
            | IteratorThrow { iterator } => {
                vec![iterator]
            }
            NextPropName { iterator } => vec![iterator],
            GetLexEnv | GetLexVar { .. } | CreatePrivateNames { .. } => vec![],
            PutLexVar { value, .. } => vec![value],
            TryGetGlobal { default, .. } => default.iter_mut().collect(),
            StoreGlobal { value, .. } | StoreModuleVar { value, .. } => vec![value],
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
            DefineClass { heritage, .. } => heritage.iter_mut().collect(),
            LoadPrivate { obj, .. } | TestPrivate { obj, .. } => vec![obj],
            StorePrivate { obj, value, .. } | DefinePrivate { obj, value, .. } => {
                vec![obj, value]
            }
            Throw { value }
            | ThrowIfSuperNotCalled { value, .. }
            | ThrowConstAssignment { name: value }
            | ThrowIfNotObject { value }
            | Await { value }
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
                | StoreSuper { .. }
                | CopyDataProps { .. }
                | StorePrivate { .. }
                | DefinePrivate { .. }
                | CreatePrivateNames { .. }
                | PutLexVar { .. }
                | StoreGlobal { .. }
                | StoreModuleVar { .. }
                | Throw { .. }
                | ThrowIfSuperNotCalled { .. }
                | ThrowUndefinedIfHole { .. }
                | ThrowConstAssignment { .. }
                | ThrowIfNotObject { .. }
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
            | LoadPropIdx { .. }
            | LoadPropDyn { .. }
            | DeleteProp { .. }
            | GetIterator { .. }
            | GetPropIterator { .. }
            | IteratorNext { .. }
            | IteratorReturn { .. }
            | IteratorThrow { .. }
            | NextPropName { .. }
            | PutLexVar { .. }
            | StoreGlobal { .. }
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
            | AsyncResolve { .. }
            | AsyncReject { .. } => Arity::Exact(1),
            LoadConst(_)
            | AllocObject { .. }
            | AllocArray
            | AllocRegExp { .. }
            | GetLexEnv
            | GetLexVar { .. }
            | LoadModuleVar { .. }
            | GetModuleNamespace { .. }
            | CreatePrivateNames { .. }
            | Branch { .. }
            | Unreachable => Arity::Exact(0),
            StoreProp { .. }
            | DefineMethod { .. }
            | CopyDataProps { .. }
            | StorePrivate { .. }
            | DefinePrivate { .. }
            | ThrowUndefinedIfHole { .. }
            | SuspendGenerator { .. } => Arity::Exact(2),
            StorePropIdx { .. } | StorePropDyn { .. } => Arity::Exact(3),
            CondBranch { .. } => Arity::Exact(1),
            TestProp { .. }
            | TryGetGlobal { .. }
            | Call { .. }
            | DefineFunc { .. }
            | DefineClass { .. }
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
            },
            Op::Phi { entries: vec![] },
            Op::Branch {
                dest: BlockId::new(0),
            },
            Op::Return { value: Some(v()) },
            Op::Unreachable,
        ];
        for op in &mut ops {
            assert_eq!(op.operands().len(), op.operands_mut().len(), "{op:?}");
            if let Arity::Exact(n) = op.arity() {
                assert_eq!(op.operands().len(), n, "{op:?}");
            }
        }
    }
}
