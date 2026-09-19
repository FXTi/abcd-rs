//! IR instruction definitions.

use crate::entity::{Block, StringId, Value};

/// Binary operator kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
    Eq,
    NotEq,
    StrictEq,
    StrictNotEq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    Shl,
    Shr,
    Ashr,
    BitAnd,
    BitOr,
    BitXor,
    In,
    InstanceOf,
}

/// Unary operator kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Minus,
    BitNot,
    LogicalNot,
    Inc,
    Dec,
    TypeOf,
    ToNumber,
    ToNumeric,
    Void,
}

/// Property access key kind.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropKind {
    ByName(StringId),
    ByValue(Value),
    ByIndex(u32),
}

/// Call kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallKind {
    Call,
    CallThis,
    SuperCall,
    SuperCallArrow,
    SuperCallSpread,
    Apply,
    /// `new callee(args...)` — the callee is the constructor and the VM
    /// receives it as BOTH func and newTarget (vendor
    /// `SlowRuntimeStub::NewObjRange(thread, ctor, ctor, ...)`,
    /// arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:4205).
    /// Lowers to the newobjrange family: the reserved call window is filled
    /// [callee, args...] in order and the encoded argc is args.len() + 1
    /// (the constructor counts).
    Construct,
}

/// IR instruction data.
///
/// Operands are [`Value`] references; instructions that produce a result
/// are themselves usable as values.  Bytecode-level details (accumulator,
/// IC slots, register widths) are abstracted away.
#[derive(Clone, Debug)]
pub enum InstData {
    // ── Literals ──────────────────────────────────────────────────────
    LiteralUndefined,
    LiteralNull,
    LiteralBool(bool),
    LiteralNumber(f64),
    LiteralString(StringId),
    /// BigInt literal — vendor `ldbigint string_id`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1622-1626, `acc: out:top`): the
    /// runtime builds a BigInt from the constant-pool entry
    /// (`SlowRuntimeStub::LdBigInt`, arkcompiler_ets_runtime-master/
    /// ecmascript/interpreter/interpreter_assembly.cpp:2915-2930), NOT a
    /// string — this must never collapse into [`InstData::LiteralString`].
    /// Opaque to the optimizers (SCCP treats it as a non-foldable
    /// constant); dead-code-eliminable when unused, like every literal.
    LiteralBigInt(StringId),
    LiteralNaN,
    LiteralInfinity,
    LiteralHole,

    // ── Binary / Unary ───────────────────────────────────────────────
    BinaryOp {
        op: BinOp,
        left: Value,
        right: Value,
    },
    UnaryOp {
        op: UnOp,
        operand: Value,
    },
    IsTrue {
        operand: Value,
    },
    IsFalse {
        operand: Value,
    },

    // ── Object creation ──────────────────────────────────────────────
    CreateEmptyObject,
    CreateEmptyArray,
    CreateObjectWithBuffer {
        literal_array: u32,
    },
    CreateArrayWithBuffer {
        literal_array: u32,
    },
    CreateRegExp {
        pattern: StringId,
        flags: StringId,
    },
    CreateObjectWithExcludedKeys {
        obj: Value,
        keys: Vec<Value>,
    },

    // ── Property access ──────────────────────────────────────────────
    LoadProperty {
        object: Value,
        key: PropKind,
    },
    StoreProperty {
        object: Value,
        key: PropKind,
        value: Value,
    },
    StoreOwnProperty {
        object: Value,
        key: PropKind,
        value: Value,
    },
    DeleteProperty {
        object: Value,
        key: Value,
    },
    LoadSuperProperty {
        key: PropKind,
    },
    StoreSuperProperty {
        key: PropKind,
        value: Value,
    },
    /// ECMAScript CopyDataProperties (object spread): copy all own
    /// enumerable properties of `src` into `dst`. Side-effecting,
    /// store-like, no IR result — the runtime result is the mutated `dst`
    /// object itself, which lift re-binds to the accumulator.
    ///
    /// Both vendor forms map here (the codebase folds deprecated opcodes
    /// into the modern IR variant, cf. `DeprecatedDelobjprop` →
    /// `DeleteProperty`):
    /// - `copydataproperties v:in:top, acc: inout:top` — `dst` from the
    ///   register operand, `src` from the accumulator;
    /// - `deprecated.copydataproperties v1:in:top, v2:in:top, acc: out:top`
    ///   — `dst` from v1, `src` from v2.
    CopyDataProperties {
        dst: Value,
        src: Value,
    },
    /// Vendor `starrayspread v1:in:top, v2:in:top, acc: inout:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1329-1332): `dst` (v1) is the
    /// destination array, `index` (v2) the start index, `src` the
    /// accumulator iterable; the runtime appends the spread elements
    /// and writes the NEW INDEX back to the accumulator
    /// (`SlowRuntimeStub::StArraySpread(thread, dst, index, src)` +
    /// `SET_ACC`, arkcompiler_ets_runtime-master/ecmascript/
    /// interpreter/interpreter_assembly.cpp:2876-2894). Side-effecting
    /// (mutates `dst`) AND result-producing (the new index) — never a
    /// single [`InstData::StoreProperty`].
    ArraySpread {
        dst: Value,
        index: Value,
        src: Value,
    },

    // ── Global variables ─────────────────────────────────────────────
    LoadGlobalVar {
        name: StringId,
    },
    StoreGlobalVar {
        name: StringId,
        value: Value,
    },
    TryLoadGlobalByName {
        name: StringId,
    },
    TryStoreGlobalByName {
        name: StringId,
        value: Value,
    },

    // ── Lexical variables (scope/frame) ──────────────────────────────
    LoadLexVar {
        level: u16,
        slot: u16,
    },
    StoreLexVar {
        level: u16,
        slot: u16,
        value: Value,
    },

    // ── Module variables ─────────────────────────────────────────────
    LoadLocalModuleVar {
        index: u32,
    },
    LoadExternalModuleVar {
        index: u32,
    },
    StoreModuleVar {
        index: u32,
        value: Value,
    },
    GetModuleNamespace {
        index: u32,
    },
    DynamicImport {
        specifier: Value,
    },

    // ── Scope management ─────────────────────────────────────────────
    NewLexEnv {
        num_vars: u32,
    },
    NewLexEnvWithName {
        num_vars: u32,
        scope_literal_array: u32,
    },
    PopLexEnv,

    // ── Function operations ──────────────────────────────────────────
    DefineFunc {
        /// Method name (display/debugging only — NOT the entity identity:
        /// distinct methods can share a name, and a name can collide with a
        /// string entity).
        method_id: StringId,
        /// Source-file offset of the referenced method. This is the entity
        /// identity: encode resolves MethodId operands by offset
        /// (`methods_by_offset`), so lowering keys on this, never the name.
        method_offset: u32,
        length: u16,
    },
    DefineMethod {
        /// Display name only; see `DefineFunc::method_id`.
        method_id: StringId,
        /// Source-file offset of the referenced method (the identity).
        method_offset: u32,
        length: u16,
        home_object: Value,
    },
    DefineClassWithBuffer {
        /// Display name only; see `DefineFunc::method_id`.
        method_id: StringId,
        /// Source-file offset of the constructor method (the identity).
        method_offset: u32,
        literal_array: u32,
        base: Value,
    },
    DefineGetterSetterByValue {
        obj: Value,
        key: Value,
        getter: Value,
        setter: Value,
    },

    // ── Calls ────────────────────────────────────────────────────────
    Call {
        kind: CallKind,
        callee: Value,
        args: Vec<Value>,
    },

    // ── Special value loaders ────────────────────────────────────────
    LoadThis,
    LoadNewTarget,
    LoadGlobalObject,
    LoadFunction,
    GetUnmappedArgs,
    CopyRestArgs {
        start_index: u32,
    },

    // ── Iterators ────────────────────────────────────────────────────
    GetIterator {
        obj: Value,
    },
    GetAsyncIterator {
        obj: Value,
    },
    GetPropIterator {
        obj: Value,
    },
    /// Vendor `getnextpropname v:in:top, acc: out:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1289-1292): the register
    /// operand is the for-in ITERATOR; the next property name is written
    /// to the accumulator. The handler ADVANCES the iterator
    /// (`SlowRuntimeStub::GetNextPropName(thread, iter)` + `SET_ACC`,
    /// arkcompiler_ets_runtime-master/ecmascript/interpreter/
    /// interpreter_assembly.cpp:2085-2099) — a side effect on the
    /// iterator object, so DCE keeps the instruction essential even when
    /// the result name is unused. Never collapsible into
    /// [`InstData::GetPropIterator`] (which CREATES an iterator from the
    /// accumulator instead).
    GetNextPropName {
        iterator: Value,
    },
    CloseIterator {
        iterator: Value,
    },

    // ── Generator / Async ────────────────────────────────────────────
    CreateGeneratorObj {
        func: Value,
    },
    /// Vendor `suspendgenerator v:in:top, acc: inout:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1302-1305): the register operand
    /// is the generator object, the accumulator carries the YIELD VALUE;
    /// the result (the resume result after a later resume) goes back to
    /// the accumulator.
    SuspendGenerator {
        genobj: Value,
        value: Value,
    },
    /// Vendor `resumegenerator` (isa.yaml:1261-1264): `acc: inout:top`,
    /// NO register operand — the generator object is read from acc, the
    /// resume result is written back to acc.
    ResumeGenerator {
        genobj: Value,
    },
    /// Vendor `getresumemode` (isa.yaml:1270-1273): `acc: inout:top`,
    /// NO register operand — the generator object is read from acc, the
    /// resume mode (a number) is written back to acc.
    GetResumeMode {
        genobj: Value,
    },
    AsyncFunctionEnter,
    AsyncFunctionAwaitUncaught {
        value: Value,
    },
    AsyncFunctionResolve {
        value: Value,
    },
    AsyncFunctionReject {
        value: Value,
    },
    CreateIterResultObj {
        value: Value,
        done: Value,
    },
    /// Vendor `gettemplateobject imm:u16, acc: inout:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1279-1283; properties
    /// `[ic_slot, one_slot, eight_sixteen_bit_ic]` — ONE IC slot): the
    /// accumulator carries the template literal, the (cached) template
    /// object is written back to the accumulator
    /// (`SlowRuntimeStub::GetTemplateObject(thread, literal)` +
    /// `SET_ACC`, arkcompiler_ets_runtime-master/ecmascript/
    /// interpreter/interpreter_assembly.cpp:2071-2083). The deprecated
    /// form (`deprecated.gettemplateobject v:in:top, acc: inout:top`,
    /// isa.yaml:1284-1288) takes the literal from the register operand;
    /// both map here (the codebase folds deprecated opcodes into the
    /// modern IR variant, cf. `DeprecatedDelobjprop` →
    /// `DeleteProperty`). NOT an element read — never collapsible into
    /// [`InstData::LoadProperty`].
    GetTemplateObject {
        literal: Value,
    },

    // ── Exception handling ───────────────────────────────────────────
    Throw {
        value: Value,
    },
    ThrowIfNotObject {
        value: Value,
    },
    ThrowConstAssignment {
        name: StringId,
    },
    ThrowUndefinedIfHole {
        name: StringId,
        value: Value,
    },
    ThrowIfSuperNotCorrectCall {
        /// The `this` value being checked, read from the accumulator —
        /// vendor `throw.ifsupernotcorrectcall imm:u16, acc: in:top`
        /// (abcd-isa-sys/vendor/isa/isa.yaml:1003-1008).
        value: Value,
        /// The bytecode imm operand selecting the CHECK KIND: 0 = TDZ
        /// guard ("sub-class must call super before use 'this'"),
        /// 1 = re-bind guard ("super() forbidden re-bind 'this'") —
        /// `RuntimeThrowIfSuperNotCorrectCall` (arkcompiler_ets_runtime
        /// ecmascript/stubs/runtime_stubs-inl.h:2520-2532).
        kind: u16,
    },
    ThrowNotExists,
    ThrowPatternNonCoercible,
    ThrowDeleteSuperProperty,

    // ── Phi ──────────────────────────────────────────────────────────
    /// SSA phi node.  Must appear at the beginning of a basic block.
    /// Each entry maps a predecessor block to the value flowing from it.
    Phi {
        entries: Vec<(Block, Value)>,
    },

    // ── Terminators ──────────────────────────────────────────────────
    Branch {
        dest: Block,
    },
    CondBranch {
        cond: Value,
        true_dest: Block,
        false_dest: Block,
    },
    Return {
        value: Option<Value>,
    },
    Unreachable,

    // ── Debug ────────────────────────────────────────────────────────
    Debugger,
}

impl InstData {
    /// Returns mutable references to all Value operands.
    pub fn operands_mut(&mut self) -> Vec<&mut Value> {
        use InstData::*;
        match self {
            LiteralUndefined
            | LiteralNull
            | LiteralBool(_)
            | LiteralNumber(_)
            | LiteralString(_)
            | LiteralBigInt(_)
            | LiteralNaN
            | LiteralInfinity
            | LiteralHole
            | CreateEmptyObject
            | CreateEmptyArray
            | CreateObjectWithBuffer { .. }
            | CreateArrayWithBuffer { .. }
            | CreateRegExp { .. }
            | LoadGlobalVar { .. }
            | TryLoadGlobalByName { .. }
            | LoadLexVar { .. }
            | LoadLocalModuleVar { .. }
            | LoadExternalModuleVar { .. }
            | GetModuleNamespace { .. }
            | NewLexEnv { .. }
            | NewLexEnvWithName { .. }
            | PopLexEnv
            | DefineFunc { .. }
            | LoadThis
            | LoadNewTarget
            | LoadGlobalObject
            | LoadFunction
            | GetUnmappedArgs
            | CopyRestArgs { .. }
            | AsyncFunctionEnter
            | ThrowNotExists
            | ThrowPatternNonCoercible
            | ThrowDeleteSuperProperty
            | ThrowConstAssignment { .. }
            | Branch { .. }
            | Unreachable
            | Debugger => vec![],

            BinaryOp { left, right, .. } => vec![left, right],
            UnaryOp { operand, .. } | IsTrue { operand } | IsFalse { operand } => vec![operand],

            CreateObjectWithExcludedKeys { obj, keys } => {
                let mut v: Vec<&mut Value> = vec![obj];
                v.extend(keys.iter_mut());
                v
            }

            LoadProperty { object, key } => {
                let mut v: Vec<&mut Value> = vec![object];
                if let PropKind::ByValue(k) = key {
                    v.push(k);
                }
                v
            }
            StoreProperty { object, key, value } | StoreOwnProperty { object, key, value } => {
                let mut v: Vec<&mut Value> = vec![object, value];
                if let PropKind::ByValue(k) = key {
                    v.push(k);
                }
                v
            }
            DeleteProperty { object, key } => vec![object, key],
            CopyDataProperties { dst, src } => vec![dst, src],
            ArraySpread { dst, index, src } => vec![dst, index, src],
            LoadSuperProperty { key } => {
                if let PropKind::ByValue(k) = key {
                    vec![k]
                } else {
                    vec![]
                }
            }
            StoreSuperProperty { key, value } => {
                let mut v: Vec<&mut Value> = vec![value];
                if let PropKind::ByValue(k) = key {
                    v.push(k);
                }
                v
            }

            StoreGlobalVar { value, .. }
            | TryStoreGlobalByName { value, .. }
            | StoreLexVar { value, .. }
            | StoreModuleVar { value, .. }
            | DynamicImport { specifier: value }
            | Throw { value }
            | ThrowIfNotObject { value }
            | ThrowIfSuperNotCorrectCall { value, .. }
            | GetIterator { obj: value }
            | GetAsyncIterator { obj: value }
            | GetPropIterator { obj: value }
            | GetNextPropName { iterator: value }
            | CloseIterator { iterator: value }
            | CreateGeneratorObj { func: value }
            | ResumeGenerator { genobj: value }
            | GetResumeMode { genobj: value }
            | AsyncFunctionAwaitUncaught { value }
            | AsyncFunctionResolve { value }
            | AsyncFunctionReject { value }
            | GetTemplateObject { literal: value } => vec![value],

            ThrowUndefinedIfHole { value, .. } => vec![value],
            SuspendGenerator { genobj, value } => vec![genobj, value],
            CreateIterResultObj { value, done } => vec![value, done],

            DefineMethod { home_object, .. } => vec![home_object],
            DefineClassWithBuffer { base, .. } => vec![base],
            DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
            } => {
                vec![obj, key, getter, setter]
            }

            Call { callee, args, .. } => {
                let mut v: Vec<&mut Value> = vec![callee];
                v.extend(args.iter_mut());
                v
            }

            Phi { entries } => entries.iter_mut().map(|(_, v)| v).collect(),
            CondBranch { cond, .. } => vec![cond],
            Return { value } => value.iter_mut().collect(),
        }
    }

    /// Returns `true` if this instruction is a block terminator.
    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            InstData::Branch { .. }
                | InstData::CondBranch { .. }
                | InstData::Return { .. }
                | InstData::Unreachable
        )
    }

    /// Returns `true` if this instruction is a phi node.
    pub fn is_phi(&self) -> bool {
        matches!(self, InstData::Phi { .. })
    }

    /// Returns `true` if this instruction produces a value.
    pub fn has_result(&self) -> bool {
        !matches!(
            self,
            InstData::StoreProperty { .. }
                | InstData::StoreOwnProperty { .. }
                | InstData::StoreSuperProperty { .. }
                | InstData::CopyDataProperties { .. }
                | InstData::StoreGlobalVar { .. }
                | InstData::TryStoreGlobalByName { .. }
                | InstData::StoreLexVar { .. }
                | InstData::StoreModuleVar { .. }
                | InstData::PopLexEnv
                | InstData::Branch { .. }
                | InstData::CondBranch { .. }
                | InstData::Return { .. }
                | InstData::Unreachable
                | InstData::Throw { .. }
                | InstData::ThrowIfNotObject { .. }
                | InstData::ThrowConstAssignment { .. }
                | InstData::ThrowUndefinedIfHole { .. }
                | InstData::ThrowIfSuperNotCorrectCall { .. }
                | InstData::ThrowNotExists
                | InstData::ThrowPatternNonCoercible
                | InstData::ThrowDeleteSuperProperty
                | InstData::Debugger
        )
    }
}
