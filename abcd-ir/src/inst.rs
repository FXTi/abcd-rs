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
        scope_name: StringId,
    },
    PopLexEnv,

    // ── Function operations ──────────────────────────────────────────
    DefineFunc {
        method_id: StringId,
        length: u16,
    },
    DefineMethod {
        method_id: StringId,
        length: u16,
        home_object: Value,
    },
    DefineClassWithBuffer {
        method_id: StringId,
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
    CloseIterator {
        iterator: Value,
    },

    // ── Generator / Async ────────────────────────────────────────────
    CreateGeneratorObj {
        func: Value,
    },
    SuspendGenerator {
        value: Value,
    },
    ResumeGenerator,
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
        value: Value,
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
            | ResumeGenerator
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
            | ThrowIfSuperNotCorrectCall { value }
            | GetIterator { obj: value }
            | GetAsyncIterator { obj: value }
            | GetPropIterator { obj: value }
            | CloseIterator { iterator: value }
            | CreateGeneratorObj { func: value }
            | SuspendGenerator { value }
            | AsyncFunctionAwaitUncaught { value }
            | AsyncFunctionResolve { value }
            | AsyncFunctionReject { value } => vec![value],

            ThrowUndefinedIfHole { value, .. } => vec![value],
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
