//! The §5 fitness audit as executable data: per-op class (Trivial /
//! NeedsWork / Hard), the Stage-A mapping, and — for the elided `Throw*`
//! guard family — the documented elision reason.
//!
//! The corpus gate's coverage histogram is keyed by this table, so the
//! table is the single source of truth for "expressed vs fallback per
//! the §5 fitness table".

use abcd_ir::op::Op;

/// Fitness class (design/decompile.md §5).
///
/// Count note: §5's summary line claims T=31/N=49, but the §5 per-row
/// table itself marks **32** rows T (row 87 `Debugger` included) and
/// therefore 48 N — the per-row markings are the source of truth here
/// (the same doc-drift resolution as IR gap G5; reported by d-P2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fitness {
    /// Trivially expressible (direct syntactic mapping). 32 ops per the
    /// row-level table (the §5 summary's "31" is doc drift — see above).
    Trivial,
    /// Needs work (fold rule / reconstruction / naming dependency). 48 ops.
    NeedsWork,
    /// Hard (driver-plumbing or no direct surface syntax). 7 ops.
    Hard,
}

/// The stable op name used in dumps and the coverage histogram.
pub fn op_name(op: &Op) -> &'static str {
    use Op::*;
    match op {
        BinaryOp { .. } => "BinaryOp",
        UnaryOp { .. } => "UnaryOp",
        Compare { .. } => "Compare",
        Mov { .. } => "Mov",
        LoadConst(_) => "LoadConst",
        AllocObject { .. } => "AllocObject",
        AllocArray { .. } => "AllocArray",
        AllocRegExp { .. } => "AllocRegExp",
        AllocClosure { .. } => "AllocClosure",
        LoadProp { .. } => "LoadProp",
        StoreProp { .. } => "StoreProp",
        LoadPropIdx { .. } => "LoadPropIdx",
        StorePropIdx { .. } => "StorePropIdx",
        LoadPropDyn { .. } => "LoadPropDyn",
        StorePropDyn { .. } => "StorePropDyn",
        StoreOwnPropName { .. } => "StoreOwnPropName",
        StoreOwnPropDyn { .. } => "StoreOwnPropDyn",
        StoreOwnPropIdx { .. } => "StoreOwnPropIdx",
        DefineMethod { .. } => "DefineMethod",
        DeleteProp { .. } => "DeleteProp",
        TestProp { .. } => "TestProp",
        CopyDataProps { .. } => "CopyDataProps",
        SetObjectWithProto { .. } => "SetObjectWithProto",
        ArraySpread { .. } => "ArraySpread",
        CreateObjectWithExcludedKeys { .. } => "CreateObjectWithExcludedKeys",
        DefineGetterSetterByValue { .. } => "DefineGetterSetterByValue",
        GetTemplateObject { .. } => "GetTemplateObject",
        CreateIterResultObj { .. } => "CreateIterResultObj",
        GetIterator { .. } => "GetIterator",
        GetAsyncIterator { .. } => "GetAsyncIterator",
        IteratorNext { .. } => "IteratorNext",
        IteratorReturn { .. } => "IteratorReturn",
        IteratorThrow { .. } => "IteratorThrow",
        GetPropIterator { .. } => "GetPropIterator",
        NextPropName { .. } => "NextPropName",
        NewLexEnv { .. } => "NewLexEnv",
        NewLexEnvWithName { .. } => "NewLexEnvWithName",
        PopLexEnv => "PopLexEnv",
        GetLexVar { .. } => "GetLexVar",
        PutLexVar { .. } => "PutLexVar",
        TryGetGlobal { .. } => "TryGetGlobal",
        StoreGlobal { .. } => "StoreGlobal",
        TryStoreGlobal { .. } => "TryStoreGlobal",
        LoadModuleVar { .. } => "LoadModuleVar",
        StoreModuleVar { .. } => "StoreModuleVar",
        GetModuleNamespace { .. } => "GetModuleNamespace",
        DynamicImport { .. } => "DynamicImport",
        Call { .. } => "Call",
        DefineFunc { .. } => "DefineFunc",
        DefineClass { .. } => "DefineClass",
        DefineSendableClass { .. } => "DefineSendableClass",
        LoadPrivate { .. } => "LoadPrivate",
        StorePrivate { .. } => "StorePrivate",
        DefinePrivate { .. } => "DefinePrivate",
        TestPrivate { .. } => "TestPrivate",
        CreatePrivateNames { .. } => "CreatePrivateNames",
        Throw { .. } => "Throw",
        ThrowIfSuperNotCalled { .. } => "ThrowIfSuperNotCalled",
        ThrowUndefinedIfHole { .. } => "ThrowUndefinedIfHole",
        ThrowUndefinedIfHoleWithName { .. } => "ThrowUndefinedIfHoleWithName",
        ThrowNotExists => "ThrowNotExists",
        ThrowPatternNonCoercible => "ThrowPatternNonCoercible",
        ThrowDeleteSuperProperty => "ThrowDeleteSuperProperty",
        ThrowConstAssignment { .. } => "ThrowConstAssignment",
        ThrowIfNotObject { .. } => "ThrowIfNotObject",
        CreateGenerator { .. } => "CreateGenerator",
        SuspendGenerator { .. } => "SuspendGenerator",
        ResumeGenerator { .. } => "ResumeGenerator",
        GetResumeMode { .. } => "GetResumeMode",
        Await { .. } => "Await",
        AwaitUncaught { .. } => "AwaitUncaught",
        AsyncFunctionEnter => "AsyncFunctionEnter",
        AsyncResolve { .. } => "AsyncResolve",
        AsyncReject { .. } => "AsyncReject",
        LoadNewTarget => "LoadNewTarget",
        LoadGlobalObject => "LoadGlobalObject",
        LoadFunction => "LoadFunction",
        GetUnmappedArgs => "GetUnmappedArgs",
        CopyRestArgs { .. } => "CopyRestArgs",
        LoadSuper { .. } => "LoadSuper",
        StoreSuper { .. } => "StoreSuper",
        Branch { .. } => "Branch",
        CondBranch { .. } => "CondBranch",
        Return { .. } => "Return",
        Phi { .. } => "Phi",
        Unreachable => "Unreachable",
        Debugger => "Debugger",
    }
}

/// The fitness class of an op (the §5 table verbatim).
pub fn fitness_of(op: &Op) -> Fitness {
    use Op::*;
    match op {
        // ── T = 32 (trivially expressible; per-row table) ──
        BinaryOp { .. }
        | Compare { .. }
        | Mov { .. }
        | LoadConst(_)
        | AllocRegExp { .. }
        | LoadProp { .. }
        | StoreProp { .. }
        | LoadPropIdx { .. }
        | StorePropIdx { .. }
        | LoadPropDyn { .. }
        | StorePropDyn { .. }
        | DeleteProp { .. }
        | TestProp { .. }
        | TryGetGlobal { .. }
        | StoreGlobal { .. }
        | TryStoreGlobal { .. }
        | GetModuleNamespace { .. }
        | DynamicImport { .. }
        | Throw { .. }
        | Await { .. }
        | AwaitUncaught { .. }
        | LoadNewTarget
        | LoadGlobalObject
        | LoadFunction
        | GetUnmappedArgs
        | LoadSuper { .. }
        | StoreSuper { .. }
        | Branch { .. }
        | CondBranch { .. }
        | Return { .. }
        | Unreachable
        | Debugger => Fitness::Trivial,
        // ── H = 7 (driver plumbing / no surface syntax) ──
        IteratorReturn { .. }
        | IteratorThrow { .. }
        | DefineSendableClass { .. }
        | ResumeGenerator { .. }
        | GetResumeMode { .. }
        | AsyncResolve { .. }
        | AsyncReject { .. } => Fitness::Hard,
        // ── N = 48 (everything else) ──
        _ => Fitness::NeedsWork,
    }
}

/// The documented elision reason for the `Throw*` guard family (and the
/// async-machinery entry) — `Some` iff Stage A elides the op on purpose
/// (design/decompile.md §4.2.6 "the `Throw*` guard family → elided",
/// §5 rows 58–65/72, R6: a future `--keep-guards` flag re-enables them).
pub fn elision_reason(op: &Op) -> Option<&'static str> {
    use Op::*;
    Some(match op {
        ThrowIfSuperNotCalled { .. } => {
            "derived-ctor `this` guard; emitted source proves the condition can't fire (§5 row 58)"
        }
        ThrowUndefinedIfHole { .. } => {
            "TDZ guard; emitted source has no TDZ-hole reads (§5 row 59)"
        }
        ThrowUndefinedIfHoleWithName { .. } => {
            "TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60)"
        }
        ThrowNotExists => "ReferenceError guard; elided in normal-flow reconstruction (§5 row 61)",
        ThrowPatternNonCoercible => {
            "destructuring coercion guard; elided in destructuring reconstruction (§5 row 62)"
        }
        ThrowConstAssignment { .. } => {
            "const-violation guard; elided — the const binding is reconstructed (§5 row 64)"
        }
        ThrowIfNotObject { .. } => {
            "for-in/for-of coercion guard; elided in loop reconstruction (§5 row 65)"
        }
        AsyncFunctionEnter => {
            "async-machinery entry; recognized and elided inside `async function` emission (§5 row 72)"
        }
        _ => return None,
    })
}

/// The note attached to the hard-7 / Stage-A fallback nodes.
pub fn fallback_note(op: &Op) -> &'static str {
    use Op::*;
    match op {
        IteratorReturn { .. } | IteratorThrow { .. } => {
            "iterator-cleanup protocol (H); folding into for-of's implicit cleanup is d-P3 pattern work (§5 rows 32-33)"
        }
        DefineSendableClass { .. } => {
            "ArkTS sendable/shared class (H); no JS surface syntax — emitted as `class` + `/* sendable */` at best (§5 row 51)"
        }
        ResumeGenerator { .. } | GetResumeMode { .. } => {
            "generator-driver plumbing (H); folds with SuspendGenerator into plain `yield` at Stage B (folds::generator_machine_fold, d-P11; §5 rows 68-69, R4)"
        }
        AsyncResolve { .. } | AsyncReject { .. } => {
            "async promise plumbing (H); folding the resolve/reject wrapper back to plain `return` needs the lift's dropped acc-input (IR gap G6; §5 rows 73-74, R4)"
        }
        ThrowDeleteSuperProperty => {
            "`delete super.x` reconstruction (N); the throw IS the delete's semantics, but the op carries no object operand — the member expression is unrecoverable at Stage A (§5 row 63)"
        }
        _ => "unhandled at Stage A",
    }
}
