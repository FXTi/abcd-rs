//! Structural and SSA dominance verifier (`design/ir.md`,
//! `design/decisions.md` N27/N38/N45/N64: the verifier is a first-class
//! contract, not a debug-build afterthought).
//!
//! Checks, per function:
//!
//! - **SSA dominance (`N45`, `N64`)**: every use is dominated by its def over
//!   **Normal** edges. Entry-defined values (params, entry-block
//!   instruction results, constants) dominate everything.
//!   `ExceptionParam` values are valid in their handler and its
//!   exceptional-reachable downstream. Phi entries are uses on the
//!   incoming edge, checked against the predecessor. Blocks unreachable
//!   over the full edge graph (dead code) are exempt — they legitimately
//!   carry junk and CFG simplification removes them; so are blocks with
//!   no Normal-edge path from entry (catch handlers: exception dispatch
//!   is not Normal-edge dominance).
//! - **`N27`**: a phi on a *reachable* block with no predecessors is an
//!   error (no incoming edge can carry it a value).
//! - **Terminators**: exactly one per block, in last position.
//! - **Arity**: fixed-arity ops match the taxonomy table
//!   ([`Op::arity`]); a phi's entry count equals the block's predecessor
//!   count.
//! - **`N38` (warning, not error)**: a handler phi joining distinct values
//!   across exceptional edges is an imprecise join — passes must not
//!   constant-fold it.
//!
//! All findings are collected, never panicked on (library rule): errors
//! in [`VerifyError`], warnings in [`VerifyWarning`], both bundled in
//! [`VerifyReport`].

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::cfg::{ExceptionHandlerMap, SplitValueDom, normal_succs_inline};
use crate::consts::Const;
use crate::function::{Edge, EdgeKind, ValueDef};
use crate::id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
use crate::module::{AnnValue, ExportDecl, ImportDecl, Module};
use crate::op::{CallKind, LexEnvKind, Op, OwnStoreKind};
use crate::ty::{StaticTy, Ty};

/// The error taxonomy. All variants derive their messages via thiserror
/// (library rule: errors via thiserror, no panics on data).
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum VerifyErrorKind {
    /// A non-external function must have a body.
    #[error("function has no blocks but is not external")]
    MissingBody,
    /// A block id listed twice in one function.
    #[error("block list contains duplicate {0}")]
    DuplicateBlock(BlockId),
    /// A block id outside the module's block arena.
    #[error("{0} is outside the block arena")]
    BlockOutOfArena(BlockId),
    /// An instruction id outside the module's inst arena.
    #[error("{0} is outside the inst arena")]
    InstOutOfArena(InstId),
    /// `Inst.block` disagrees with the block listing the instruction.
    #[error("instruction is listed in {expected} but records its block as {actual}")]
    InstBlockMismatch {
        /// The block listing the instruction.
        expected: BlockId,
        /// The block the instruction records.
        actual: BlockId,
    },
    /// A block must contain at least its terminator.
    #[error("block has no instructions (missing terminator)")]
    EmptyBlock,
    /// The last instruction is not a terminator.
    #[error("block does not end with a terminator")]
    MissingTerminator,
    /// A terminator appears before the last instruction (so the block
    /// would have two).
    #[error("terminator in the middle of a block")]
    MidBlockTerminator,
    /// Phis must lead the block.
    #[error("phi node after a non-phi instruction")]
    PhiAfterNonPhi,
    /// [`Op::operands`] disagrees with [`Op::arity`] (taxonomy drift).
    #[error("op arity mismatch: taxonomy declares {expected} operands, operands() yields {actual}")]
    ArityMismatch {
        /// The taxonomy-declared operand count.
        expected: usize,
        /// The operand count `operands()` yields.
        actual: usize,
    },
    /// Phi entry count must equal the predecessor count.
    #[error("phi has {entries} entries but block has {preds} predecessors")]
    PhiArity {
        /// The phi's entry count.
        entries: usize,
        /// The block's predecessor count.
        preds: usize,
    },
    /// A phi entry must key on one of the block's predecessor edges.
    #[error("phi entry edge {edge:?} is not a predecessor edge of the block")]
    PhiForeignEdge {
        /// The offending entry edge.
        edge: Edge,
    },
    /// Duplicate phi entry edge.
    #[error("phi contains duplicate entry edge {edge:?}")]
    PhiDuplicateEdge {
        /// The duplicated entry edge.
        edge: Edge,
    },
    /// N27: a phi on a reachable zero-predecessor block can never receive
    /// a value.
    #[error("phi on a reachable block with no predecessors (N27)")]
    ZeroPredPhi,
    /// The entry block may only be its own predecessor (loop back-edge).
    #[error("entry block has a predecessor from another block")]
    EntryHasPred,
    /// Predecessor edge lists are sets.
    #[error("duplicate predecessor edge {0:?}")]
    DuplicatePred(Edge),
    /// Predecessor edges must originate inside the function.
    #[error("predecessor {0} is not in this function")]
    ForeignPred(BlockId),
    /// A Normal predecessor's terminator must actually target the block.
    #[error("normal predecessor {0}'s terminator does not target this block")]
    PredDoesNotTarget(BlockId),
    /// An Exceptional predecessor must have a try region dispatching to
    /// this handler.
    #[error("exceptional predecessor {0} has no try region dispatching to this handler")]
    ExceptionalPredWithoutRegion(BlockId),
    /// Terminator targets must be inside the function.
    #[error("successor {0} is not in this function")]
    ForeignSuccessor(BlockId),
    /// CFG edge symmetry: the successor must list the edge.
    #[error("successor {0} is missing this block from its predecessors")]
    SuccessorMissingPred(BlockId),
    /// Exceptional edges are first-class (T5): the handler must list
    /// every protected block as an Exceptional predecessor.
    #[error(
        "handler {handler} is missing the exceptional predecessor edge from protected block {protected}"
    )]
    MissingExceptionalPred {
        /// The catch handler.
        handler: BlockId,
        /// The protected block whose exceptional edge is missing.
        protected: BlockId,
    },
    /// Try regions reference only the function's own blocks.
    #[error("try region references foreign block {0}")]
    ForeignTryBlock(BlockId),
    /// Catch handlers must be blocks of this function.
    #[error("try region references foreign handler {0}")]
    ForeignHandler(BlockId),
    /// A try region protects a block at most once.
    #[error("try region contains duplicate protected block {0}")]
    DuplicateTryBlock(BlockId),
    /// The catch's exception value must be defined by the dispatch at
    /// that handler.
    #[error("catch exception value {value} is not defined by ExceptionParam({handler})")]
    BadExceptionParam {
        /// The catch's exception value.
        value: ValueId,
        /// The handler block.
        handler: BlockId,
    },
    /// A result value id outside the value arena.
    #[error("result value {0} is outside the value arena")]
    ValueOutOfArena(ValueId),
    /// A result's `ValueDef` must point back at its instruction.
    #[error("result {value} has mismatched definition {actual:?}")]
    ResultDefMismatch {
        /// The result value.
        value: ValueId,
        /// The definition it actually carries.
        actual: ValueDef,
    },
    /// A parameter's `ValueDef` must be `Param` of its index.
    #[error("parameter value {value} has mismatched definition {actual:?}")]
    ParamDefMismatch {
        /// The parameter value.
        value: ValueId,
        /// The definition it actually carries.
        actual: ValueDef,
    },
    /// A use of a value id outside the value arena.
    #[error("uses undefined value {0}")]
    UndefinedValue(ValueId),
    /// A use of a value owned by another function (or by nothing).
    #[error("value {0} is not owned by this function")]
    ForeignValue(ValueId),
    /// Within one block the def must precede the use.
    #[error("uses {value} before its definition in the same block")]
    UseBeforeDef {
        /// The misused value.
        value: ValueId,
    },
    /// N45: cross-block uses need Normal-edge dominance.
    #[error(
        "uses {value} whose definition in {def_block} does not dominate this block (over Normal edges)"
    )]
    UseNotDominated {
        /// The misused value.
        value: ValueId,
        /// The block its definition lives in.
        def_block: BlockId,
    },
    /// N45 for phi edge uses.
    #[error(
        "phi entry from {pred} uses {value} whose definition in {def_block} does not dominate the predecessor (over Normal edges)"
    )]
    PhiUseNotDominated {
        /// The phi entry's source block.
        pred: BlockId,
        /// The misused value.
        value: ValueId,
        /// The block its definition lives in.
        def_block: BlockId,
    },
    /// Exception params live in their handler and its downstream.
    #[error(
        "uses exception value {value} delivered at handler {handler} — not available here (N45)"
    )]
    ExceptionParamOutOfScope {
        /// The exception value.
        value: ValueId,
        /// The handler it was delivered at.
        handler: BlockId,
    },
    /// Exception params on phi edges: the edge must leave the handler's
    /// downstream.
    #[error(
        "phi entry from {pred} uses exception value {value} delivered at handler {handler} (N45)"
    )]
    ExceptionParamPhiOutOfScope {
        /// The phi entry's source block.
        pred: BlockId,
        /// The exception value.
        value: ValueId,
        /// The handler it was delivered at.
        handler: BlockId,
    },
    /// A class reference outside the class table (module level).
    #[error("class {0} is outside the class table")]
    ClassOutOfRange(ClassId),
    /// A function reference outside the function table (module level).
    #[error("function {0} is outside the function table")]
    FuncOutOfRange(FuncId),
    /// A constant reference outside the const pool (module level).
    #[error("constant {0} is outside the const pool")]
    ConstOutOfRange(ConstId),
    /// `Inst.result` presence disagrees with [`Op::has_result`].
    #[error(
        "instruction result presence ({has_result}) disagrees with op.has_result() ({op_expects_result})"
    )]
    ResultPresenceMismatch {
        /// Whether `inst.result` is `Some`.
        has_result: bool,
        /// Whether `inst.op.has_result()` is `true`.
        op_expects_result: bool,
    },
    /// An `InstId` listed more than once across blocks or functions.
    #[error("duplicate instruction listing {0}")]
    DuplicateInst(InstId),
    /// A `ValueId` defined more than once (duplicate param, catch exception, or cross-function claim).
    #[error("duplicate value definition {0}")]
    DuplicateValueDef(ValueId),
    /// `Op::Call` receiver/argument shape violates [`CallKind`] invariants.
    #[error("invalid call operand shape for {kind:?}")]
    InvalidCallShape {
        /// The call kind whose structural contract was violated.
        kind: CallKind,
    },
    /// `LexEnvKind` or `OwnStoreKind` violates its opcode invariant (`#55`).
    #[error("invalid op modifier on {inst}: {detail}")]
    InvalidOpModifier {
        /// The offending instruction id.
        inst: InstId,
        /// Description of the violated modifier rule.
        detail: &'static str,
    },
    /// A symbol reference outside `module.sym`.
    #[error("symbol {0} is outside the symbol table")]
    SymOutOfRange(Sym),
    /// A cycle in `ConstPool` literal references (`ArrayLiteral` / `ObjectLiteral`).
    #[error("constant {0} participates in a literal-shape cycle")]
    ConstCycle(ConstId),
    /// `Const::ObjectLiteral` `keys.len() != values.len()`.
    #[error("object literal {const_id} has {keys} keys but {values} values")]
    ObjectLiteralArityMismatch {
        /// The malformed constant id.
        const_id: ConstId,
        /// Key count.
        keys: usize,
        /// Value count.
        values: usize,
    },
    /// An external function carries body blocks (`T6`).
    #[error("external function must not have body blocks")]
    ExternalFunctionHasBody,
    /// A field reference outside the owning class's field table.
    #[error("field {field} is outside class {class}'s field table")]
    FieldOutOfRange {
        /// The referenced class.
        class: ClassId,
        /// The out-of-range field id.
        field: FieldId,
    },
    /// A function id is listed more than once across `ClassData::methods`.
    #[error("function {0} is listed multiple times across class method tables")]
    DuplicateClassMethod(FuncId),
    /// `ClassData::methods` lists a function whose `class_id` names another class.
    #[error("class {class} lists method {func}, whose class_id is {actual_class}")]
    ClassMethodOwnerMismatch {
        /// The class listing `func` in `methods`.
        class: ClassId,
        /// The mismatched function id.
        func: FuncId,
        /// The `class_id` recorded on `func`.
        actual_class: ClassId,
    },
    /// A function in `module.functions` is missing from `module.classes[func.class_id].methods`.
    #[error("function {func} declares class_id {class} but is missing from its methods list")]
    UnlistedClassMethod {
        /// The expected owning class.
        class: ClassId,
        /// The unlisted function id.
        func: FuncId,
    },
    /// `DebugData` references an in-arena `InstId` that does not belong to this function.
    #[error("debug info references instruction {0} not in this function")]
    DebugInstNotInFunc(InstId),
    /// A [`Const`] entry or constant-referencing site has an incompatible payload shape.
    #[error("constant {const_id} has invalid payload shape: {detail}")]
    InvalidConstShape {
        /// The offending constant id.
        const_id: ConstId,
        /// Description of the violated shape invariant.
        detail: &'static str,
    },
}

/// The warning taxonomy (non-fatal findings).
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum VerifyWarningKind {
    /// N38: a handler phi joining distinct values across exceptional
    /// edges reads an imprecise join — passes must not fold it to a
    /// constant.
    #[error(
        "handler phi joins {count} distinct values across exceptional edges — imprecise join; passes must NOT constant-fold it (N38)"
    )]
    HandlerPhiImpreciseJoin {
        /// The handler block carrying the phi.
        handler: BlockId,
        /// How many distinct values join across exceptional edges.
        count: usize,
    },
}

/// A verification error with location context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyError {
    /// The function being verified (`None` for module-level findings).
    pub func: Option<FuncId>,
    /// The block, when applicable.
    pub block: Option<BlockId>,
    /// The instruction, when applicable.
    pub inst: Option<InstId>,
    /// What is wrong.
    pub kind: VerifyErrorKind,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "verify error")?;
        if let Some(func) = self.func {
            write!(f, " in {func}")?;
        }
        if let Some(bb) = self.block {
            write!(f, " {bb}")?;
        }
        if let Some(i) = self.inst {
            write!(f, " {i}")?;
        }
        write!(f, ": {}", self.kind)
    }
}

impl std::error::Error for VerifyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.kind)
    }
}

/// A verification warning with location context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyWarning {
    /// The function being verified.
    pub func: Option<FuncId>,
    /// The block, when applicable.
    pub block: Option<BlockId>,
    /// The instruction, when applicable.
    pub inst: Option<InstId>,
    /// What is suspicious.
    pub kind: VerifyWarningKind,
}

impl fmt::Display for VerifyWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "verify warning")?;
        if let Some(func) = self.func {
            write!(f, " in {func}")?;
        }
        if let Some(bb) = self.block {
            write!(f, " {bb}")?;
        }
        if let Some(i) = self.inst {
            write!(f, " {i}")?;
        }
        write!(f, ": {}", self.kind)
    }
}

impl std::error::Error for VerifyWarning {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.kind)
    }
}

/// The outcome of verifying a module or function: errors (hard
/// violations) and warnings (N38 channel).
#[must_use]
#[derive(Clone, Debug, Default)]
pub struct VerifyReport {
    /// Hard violations.
    pub errors: Vec<VerifyError>,
    /// Non-fatal findings.
    pub warnings: Vec<VerifyWarning>,
}

impl VerifyReport {
    /// Whether no errors were found (warnings do not affect this).
    #[must_use]
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Stack-allocated Normal-edge successors of `bb` (`0..=2` targets).
#[inline]
fn block_normal_succs(module: &Module, bb: BlockId) -> ([BlockId; 2], usize) {
    let Some(block) = module.block(bb) else {
        return ([BlockId::new(0); 2], 0);
    };
    let Some(&last) = block.insts.last() else {
        return ([BlockId::new(0); 2], 0);
    };
    let Some(inst) = module.inst(last) else {
        return ([BlockId::new(0); 2], 0);
    };
    normal_succs_inline(&inst.op)
}

#[inline]
const fn is_literal_shape_const(c: &Const) -> bool {
    matches!(
        c,
        Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_)
    )
}

#[inline]
const fn is_loadable_scalar_const(c: &Const) -> bool {
    !matches!(
        c,
        Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_)
            | Const::MethodRef { .. }
    )
}

fn check_debug_insts(
    module: &Module,
    func_id: FuncId,
    seen_insts: &HashSet<InstId>,
    report: &mut VerifyReport,
) {
    let Some(dbg) = module.func(func_id).and_then(|f| f.debug.as_ref()) else {
        return;
    };
    let mut check_iid = |iid: InstId| {
        let kind = if module.inst(iid).is_none() {
            Some(VerifyErrorKind::InstOutOfArena(iid))
        } else if !seen_insts.contains(&iid) {
            Some(VerifyErrorKind::DebugInstNotInFunc(iid))
        } else {
            None
        };
        if let Some(kind) = kind {
            report.errors.push(VerifyError {
                func: Some(func_id),
                block: None,
                inst: Some(iid),
                kind,
            });
        }
    };
    for entry in &dbg.line_table {
        check_iid(entry.inst);
    }
    for entry in &dbg.column_table {
        check_iid(entry.inst);
    }
    for ln in &dbg.local_names {
        if let Some(scope) = ln.scope {
            check_iid(scope.start);
            check_iid(scope.end);
        }
    }
}

/// Verify one function.
#[must_use = "verification findings must be checked via VerifyReport::is_ok()"]
pub fn verify_func(module: &Module, func_id: FuncId) -> VerifyReport {
    let mut report = VerifyReport::default();
    let Some(func) = module.func(func_id) else {
        report.errors.push(VerifyError {
            func: None,
            block: None,
            inst: None,
            kind: VerifyErrorKind::FuncOutOfRange(func_id),
        });
        return report;
    };
    let err = |block: Option<BlockId>, inst: Option<InstId>, kind: VerifyErrorKind| VerifyError {
        func: Some(func_id),
        block,
        inst,
        kind,
    };

    if func.is_external && !func.blocks.is_empty() {
        report
            .errors
            .push(err(None, None, VerifyErrorKind::ExternalFunctionHasBody));
    }

    let mut defined: HashSet<ValueId> = HashSet::new();
    for (i, &val) in func.params.iter().enumerate() {
        let expected_idx = u16::try_from(i).ok();
        match module.value(val).map(|v| v.def) {
            None => report
                .errors
                .push(err(None, None, VerifyErrorKind::ValueOutOfArena(val))),
            Some(def) if expected_idx.is_none_or(|idx| def != ValueDef::Param(idx)) => {
                report.errors.push(err(
                    None,
                    None,
                    VerifyErrorKind::ParamDefMismatch {
                        value: val,
                        actual: def,
                    },
                ));
            }
            _ => {
                if !defined.insert(val) {
                    report
                        .errors
                        .push(err(None, None, VerifyErrorKind::DuplicateValueDef(val)));
                }
            }
        }
    }
    for &val in &func.frame_init_consts {
        match module.value(val).map(|v| v.def) {
            None => report
                .errors
                .push(err(None, None, VerifyErrorKind::ValueOutOfArena(val))),
            Some(ValueDef::Const(c)) => {
                if module.consts.get(c).is_some() {
                    defined.insert(val);
                } else {
                    report
                        .errors
                        .push(err(None, None, VerifyErrorKind::ConstOutOfRange(c)));
                    report
                        .errors
                        .push(err(None, None, VerifyErrorKind::ForeignValue(val)));
                }
            }
            Some(_) => report
                .errors
                .push(err(None, None, VerifyErrorKind::ForeignValue(val))),
        }
    }

    // External functions carry no body (T6).
    if func.blocks.is_empty() {
        if !func.is_external {
            report
                .errors
                .push(err(None, None, VerifyErrorKind::MissingBody));
        }
        for region in &func.try_regions {
            for &p in &region.protected {
                report
                    .errors
                    .push(err(None, None, VerifyErrorKind::ForeignTryBlock(p)));
            }
            for catch in &region.catches {
                report.errors.push(err(
                    None,
                    None,
                    VerifyErrorKind::ForeignHandler(catch.handler),
                ));
            }
        }
        check_debug_insts(module, func_id, &HashSet::new(), &mut report);
        return report;
    }

    let func_blocks: HashSet<BlockId> = func.blocks.iter().copied().collect();
    if func_blocks.len() != func.blocks.len() {
        let mut seen = HashSet::new();
        for &bb in &func.blocks {
            if !seen.insert(bb) {
                report
                    .errors
                    .push(err(None, None, VerifyErrorKind::DuplicateBlock(bb)));
            }
        }
    }
    let mut block_pred_sets: HashMap<BlockId, HashSet<Edge>> =
        HashMap::with_capacity(func.blocks.len());
    for &bb in &func.blocks {
        match module.block(bb) {
            Some(b) => {
                block_pred_sets
                    .entry(bb)
                    .or_insert_with(|| b.preds.iter().copied().collect());
            }
            None => {
                report
                    .errors
                    .push(err(None, None, VerifyErrorKind::BlockOutOfArena(bb)));
            }
        }
    }
    let entry = func.blocks[0];

    // ── Try-region structure (checked first; edge checks rely on it) ──
    for region in &func.try_regions {
        let mut seen = HashSet::new();
        for &p in &region.protected {
            if !func_blocks.contains(&p) {
                report
                    .errors
                    .push(err(None, None, VerifyErrorKind::ForeignTryBlock(p)));
            }
            if !seen.insert(p) {
                report
                    .errors
                    .push(err(Some(p), None, VerifyErrorKind::DuplicateTryBlock(p)));
            }
        }
        for catch in &region.catches {
            if !func_blocks.contains(&catch.handler) {
                report.errors.push(err(
                    None,
                    None,
                    VerifyErrorKind::ForeignHandler(catch.handler),
                ));
            }
            if let Some(tc) = catch.type_class
                && module.class(tc).is_none()
            {
                report.errors.push(err(
                    Some(catch.handler),
                    None,
                    VerifyErrorKind::ClassOutOfRange(tc),
                ));
            }
            // The exception value must be the dispatch-defined value of
            // this handler.
            let ok = matches!(
                module.value(catch.exception).map(|v| v.def),
                Some(ValueDef::ExceptionParam(h)) if h == catch.handler
            );
            if !ok {
                report.errors.push(err(
                    Some(catch.handler),
                    None,
                    VerifyErrorKind::BadExceptionParam {
                        value: catch.exception,
                        handler: catch.handler,
                    },
                ));
            } else if func_blocks.contains(&catch.handler) {
                defined.insert(catch.exception);
            }
            // Exceptional edges are first-class (T5): the handler lists
            // every protected block as an Exceptional predecessor (using hoisted
            // `block_pred_sets` rather than rebuilding `h_preds` per catch).
            if let Some(handler) = module.block(catch.handler) {
                let h_preds = block_pred_sets
                    .entry(catch.handler)
                    .or_insert_with(|| handler.preds.iter().copied().collect());
                for &p in &region.protected {
                    let edge = Edge {
                        from: p,
                        kind: EdgeKind::Exceptional,
                    };
                    if func_blocks.contains(&p) && !h_preds.contains(&edge) {
                        report.errors.push(err(
                            Some(catch.handler),
                            None,
                            VerifyErrorKind::MissingExceptionalPred {
                                handler: catch.handler,
                                protected: p,
                            },
                        ));
                    }
                }
            }
        }
    }

    let Some(exc_map) = ExceptionHandlerMap::build(module, func_id) else {
        return report;
    };

    // ── Instruction ownership scan ───────────────────────────────────
    let mut seen_insts: HashSet<InstId> = HashSet::new();
    let mut inst_pos: HashMap<InstId, usize> = HashMap::new();
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for (pos, &inst_id) in block.insts.iter().enumerate() {
            if !seen_insts.insert(inst_id) {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::DuplicateInst(inst_id),
                ));
            } else {
                inst_pos.insert(inst_id, pos);
            }
            let Some(inst) = module.inst(inst_id) else {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::InstOutOfArena(inst_id),
                ));
                continue;
            };
            if inst.block != bb {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::InstBlockMismatch {
                        expected: bb,
                        actual: inst.block,
                    },
                ));
            }
            let has_res = inst.result.is_some();
            let expects_res = inst.op.has_result();
            if has_res != expects_res {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::ResultPresenceMismatch {
                        has_result: has_res,
                        op_expects_result: expects_res,
                    },
                ));
            }
            if let Some(val) = inst.result {
                match module.value(val).map(|v| v.def) {
                    None => report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::ValueOutOfArena(val),
                    )),
                    Some(ValueDef::Inst(def)) if def == inst_id => {
                        if !defined.insert(val) {
                            report.errors.push(err(
                                Some(bb),
                                Some(inst_id),
                                VerifyErrorKind::DuplicateValueDef(val),
                            ));
                        }
                    }
                    Some(actual) => report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::ResultDefMismatch { value: val, actual },
                    )),
                }
            }
        }
    }

    check_debug_insts(module, func_id, &seen_insts, &mut report);

    // Entry predecessors: only a Normal self-loop back-edge is legal.
    if let Some(entry_block) = module.block(entry)
        && entry_block
            .preds
            .iter()
            .any(|e| e.from != entry || e.kind != EdgeKind::Normal)
    {
        report
            .errors
            .push(err(Some(entry), None, VerifyErrorKind::EntryHasPred));
    }

    // ── Per-block structural checks ──────────────────────────────────
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };

        // Predecessor edge consistency.
        let mut seen_edges = HashSet::with_capacity(block.preds.len());
        for edge in &block.preds {
            if !seen_edges.insert(*edge) {
                report
                    .errors
                    .push(err(Some(bb), None, VerifyErrorKind::DuplicatePred(*edge)));
                continue;
            }
            if !func_blocks.contains(&edge.from) {
                report
                    .errors
                    .push(err(Some(bb), None, VerifyErrorKind::ForeignPred(edge.from)));
                continue;
            }
            match edge.kind {
                EdgeKind::Normal => {
                    let (targets, count) = block_normal_succs(module, edge.from);
                    if !targets[..count].contains(&bb) {
                        report.errors.push(err(
                            Some(bb),
                            None,
                            VerifyErrorKind::PredDoesNotTarget(edge.from),
                        ));
                    }
                }
                EdgeKind::Exceptional => {
                    if !exc_map.dispatches_to(edge.from, bb) {
                        report.errors.push(err(
                            Some(bb),
                            None,
                            VerifyErrorKind::ExceptionalPredWithoutRegion(edge.from),
                        ));
                    }
                }
            }
        }

        if block.insts.is_empty() {
            report
                .errors
                .push(err(Some(bb), None, VerifyErrorKind::EmptyBlock));
            continue;
        }

        // Exactly one terminator, in last position; phis lead the block.
        let mut seen_non_phi = false;
        for (pos, &inst_id) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            let last = pos == block.insts.len() - 1;
            if inst.op.is_terminator() && !last {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::MidBlockTerminator,
                ));
            }
            if inst.op.is_phi() && seen_non_phi {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::PhiAfterNonPhi,
                ));
            }
            if !inst.op.is_phi() {
                seen_non_phi = true;
            }
            if let crate::op::Arity::Exact(n) = inst.op.arity() {
                let mut actual = 0usize;
                inst.op.for_each_operand(|_| actual += 1);
                if actual != n {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::ArityMismatch {
                            expected: n,
                            actual,
                        },
                    ));
                }
            }
            if let Op::Call {
                this, args, kind, ..
            } = &inst.op
            {
                let valid_shape = match kind {
                    CallKind::Apply => this.is_some() && args.len() == 1,
                    CallKind::SuperSpread | CallKind::SuperForwardAllArgs | CallKind::NewSpread => {
                        this.is_none() && args.len() == 1
                    }
                    CallKind::SuperArrow => this.is_none(),
                    CallKind::ClassInit => this.is_some() && args.is_empty(),
                    CallKind::Dynamic | CallKind::Direct | CallKind::Super | CallKind::New => true,
                };
                if !valid_shape {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::InvalidCallShape { kind: *kind },
                    ));
                }
            }
            let invalid_mod = match &inst.op {
                Op::NewLexEnv {
                    kind: LexEnvKind::Patch,
                    ..
                } => Some("NewLexEnv cannot use LexEnvKind::Patch"),
                Op::GetLexVar {
                    level,
                    kind: LexEnvKind::Patch,
                    ..
                }
                | Op::PutLexVar {
                    level,
                    kind: LexEnvKind::Patch,
                    ..
                } if *level != 0 => Some("LexEnvKind::Patch requires level == 0"),
                Op::StoreOwnPropDyn {
                    kind: OwnStoreKind::DefineProperty,
                    ..
                } => Some("StoreOwnPropDyn cannot use OwnStoreKind::DefineProperty"),
                Op::StoreOwnPropIdx { kind, .. }
                    if !matches!(kind, OwnStoreKind::OwnProp | OwnStoreKind::ClassField) =>
                {
                    Some("StoreOwnPropIdx only allows OwnProp or ClassField")
                }
                _ => None,
            };
            if let Some(detail) = invalid_mod {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::InvalidOpModifier {
                        inst: inst_id,
                        detail,
                    },
                ));
            }
            inst.op.for_each_const_id(|cid| {
                if module.consts.get(cid).is_none() {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::ConstOutOfRange(cid),
                    ));
                }
            });
            match &inst.op {
                Op::LoadConst(cid) => {
                    if let Some(c) = module.consts.get(*cid)
                        && !is_loadable_scalar_const(c)
                    {
                        report.errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            VerifyErrorKind::InvalidConstShape {
                                const_id: *cid,
                                detail: "LoadConst requires a scalar constant, not a literal shape or method tag",
                            },
                        ));
                    }
                }
                Op::AllocObject { shape: cid }
                | Op::AllocArray { shape: Some(cid) }
                | Op::NewLexEnvWithName {
                    scope_names: cid, ..
                }
                | Op::CreatePrivateNames { names: cid, .. } => {
                    if let Some(c) = module.consts.get(*cid)
                        && !is_literal_shape_const(c)
                    {
                        report.errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            VerifyErrorKind::InvalidConstShape {
                                const_id: *cid,
                                detail: "op requires a literal-shape constant",
                            },
                        ));
                    }
                }
                Op::DefineClass(d) | Op::DefineSendableClass(d) => {
                    if let Some(c) = module.consts.get(d.members)
                        && !is_literal_shape_const(c)
                    {
                        report.errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            VerifyErrorKind::InvalidConstShape {
                                const_id: d.members,
                                detail: "DefineClass members requires a literal-shape constant",
                            },
                        ));
                    }
                }
                _ => {}
            }
            inst.op.for_each_func_id(|fid| {
                if module.func(fid).is_none() {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::FuncOutOfRange(fid),
                    ));
                }
            });
            inst.op.for_each_sym(|sym| {
                if module.sym.resolve(sym).is_none() {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::SymOutOfRange(sym),
                    ));
                }
            });
        }
        let last_id = block.insts[block.insts.len() - 1];
        if let Some(last) = module.inst(last_id) {
            if !last.op.is_terminator() {
                report.errors.push(err(
                    Some(bb),
                    Some(last_id),
                    VerifyErrorKind::MissingTerminator,
                ));
            }
            let (targets, count) = normal_succs_inline(&last.op);
            for &succ in &targets[..count] {
                if !func_blocks.contains(&succ) {
                    report.errors.push(err(
                        Some(bb),
                        Some(last_id),
                        VerifyErrorKind::ForeignSuccessor(succ),
                    ));
                } else if block_pred_sets.get(&succ).is_some_and(|pset| {
                    !pset.contains(&Edge {
                        from: bb,
                        kind: EdgeKind::Normal,
                    })
                }) {
                    report.errors.push(err(
                        Some(bb),
                        Some(last_id),
                        VerifyErrorKind::SuccessorMissingPred(succ),
                    ));
                }
            }
        }

        // Phi arity and edge keys (`O(1)` edge lookup via `seen_edges`).
        for &inst_id in &block.insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            let Op::Phi { entries } = &inst.op else {
                continue;
            };
            if entries.len() != block.preds.len() {
                report.errors.push(err(
                    Some(bb),
                    Some(inst_id),
                    VerifyErrorKind::PhiArity {
                        entries: entries.len(),
                        preds: block.preds.len(),
                    },
                ));
            }
            let mut seen = HashSet::with_capacity(entries.len());
            for (edge, _) in entries {
                if !seen_edges.contains(edge) {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::PhiForeignEdge { edge: *edge },
                    ));
                }
                if !seen.insert(*edge) {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::PhiDuplicateEdge { edge: *edge },
                    ));
                }
            }
        }
    }

    // ── Pre-indexed catch exception ownership & split dominance ──────
    let mut catch_pairs: HashSet<(BlockId, ValueId)> = HashSet::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            catch_pairs.insert((catch.handler, catch.exception));
        }
    }
    let ownership = |val: ValueId| -> Option<VerifyErrorKind> {
        let v = module.value(val)?;
        let owned = match v.def {
            ValueDef::Const(c) => module.consts.get(c).is_some(),
            ValueDef::Param(i) => {
                defined.contains(&val) && func.params.get(i as usize) == Some(&val)
            }
            ValueDef::Inst(def) => {
                defined.contains(&val)
                    && seen_insts.contains(&def)
                    && module.inst(def).is_some_and(|inst| {
                        inst.result == Some(val) && func_blocks.contains(&inst.block)
                    })
            }
            ValueDef::ExceptionParam(h) => {
                defined.contains(&val) && catch_pairs.contains(&(h, val))
            }
        };
        if owned {
            None
        } else {
            Some(VerifyErrorKind::ForeignValue(val))
        }
    };

    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            inst.op.for_each_operand(|val| {
                if module.value(val).is_none() {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::UndefinedValue(val),
                    ));
                } else {
                    if let Some(ValueDef::Const(c)) = module.value(val).map(|v| v.def)
                        && module.consts.get(c).is_none()
                    {
                        report.errors.push(err(
                            Some(bb),
                            Some(inst_id),
                            VerifyErrorKind::ConstOutOfRange(c),
                        ));
                    }
                    if let Some(kind) = ownership(val) {
                        report.errors.push(err(Some(bb), Some(inst_id), kind));
                    }
                }
            });
        }
    }

    let mut block_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(func.blocks.len());
    for (idx, &bb) in func.blocks.iter().enumerate() {
        block_to_idx.entry(bb).or_insert(idx);
    }
    let vdom = SplitValueDom::compute(module, &func.blocks, &block_to_idx, &exc_map);

    // ── N27: reachable zero-pred phi ─────────────────────────────────
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let Some(&bi) = block_to_idx.get(&bb) else {
            continue;
        };
        if !vdom.is_pt_reachable(vdom.entry_pt(bi)) || !block.preds.is_empty() {
            continue;
        }
        for &inst_id in &block.insts {
            if module.inst(inst_id).is_some_and(|i| i.op.is_phi()) {
                report
                    .errors
                    .push(err(Some(bb), Some(inst_id), VerifyErrorKind::ZeroPredPhi));
            }
        }
    }

    // ── N45 / R2-D1 split dominance over Normal + Exceptional edges ──
    verify_dominance(
        module,
        func_id,
        &defined,
        &block_to_idx,
        &inst_pos,
        &vdom,
        &mut report,
    );

    // ── N38: handler-phi imprecise-join warnings (deduped per handler)
    let mut warned_handlers: HashSet<BlockId> = HashSet::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            if !warned_handlers.insert(catch.handler) {
                continue;
            }
            let Some(handler) = module.block(catch.handler) else {
                continue;
            };
            for &inst_id in &handler.insts {
                let Some(inst) = module.inst(inst_id) else {
                    continue;
                };
                let Op::Phi { entries } = &inst.op else {
                    continue;
                };
                let distinct: HashSet<ValueId> = entries
                    .iter()
                    .filter(|(edge, _)| edge.kind == EdgeKind::Exceptional)
                    .map(|(_, v)| *v)
                    .collect();
                if distinct.len() > 1 {
                    report.warnings.push(VerifyWarning {
                        func: Some(func_id),
                        block: Some(catch.handler),
                        inst: Some(inst_id),
                        kind: VerifyWarningKind::HandlerPhiImpreciseJoin {
                            handler: catch.handler,
                            count: distinct.len(),
                        },
                    });
                }
            }
        }
    }

    report
}

/// `N45` / `R2-D1` SSA use-def dominance over the pre-throw (`entry_pt`) and
/// post-normal-exit (`norm_pt`) split CFG (`O(1)` Euler-interval queries per operand).
fn verify_dominance(
    module: &Module,
    func_id: FuncId,
    defined: &HashSet<ValueId>,
    index: &HashMap<BlockId, usize>,
    inst_pos: &HashMap<InstId, usize>,
    vdom: &SplitValueDom,
    report: &mut VerifyReport,
) {
    let Some(func) = module.func(func_id) else {
        return;
    };
    let err = |block: Option<BlockId>, inst: Option<InstId>, kind: VerifyErrorKind| VerifyError {
        func: Some(func_id),
        block,
        inst,
        kind,
    };

    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let Some(&bi) = index.get(&bb) else { continue };
        let bb_entry_pt = vdom.entry_pt(bi);
        let bb_reachable = vdom.is_pt_reachable(bb_entry_pt);

        for (pos, &inst_id) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };

            if let Op::Phi { entries } = &inst.op {
                for (edge, val) in entries {
                    let Some(v) = module.value(*val) else {
                        continue;
                    };
                    let Some(&pi) = index.get(&edge.from) else {
                        continue;
                    };
                    let use_pt = vdom.edge_use_pt(pi, edge.kind);
                    match v.def {
                        ValueDef::Param(_) | ValueDef::Const(_) => {}
                        ValueDef::ExceptionParam(h) => {
                            if !defined.contains(val) {
                                continue;
                            }
                            let Some(&hi) = index.get(&h) else {
                                continue;
                            };
                            let h_pt = vdom.entry_pt(hi);
                            if vdom.is_pt_reachable(use_pt) && !vdom.dominates_pt(h_pt, use_pt) {
                                report.errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    VerifyErrorKind::ExceptionParamPhiOutOfScope {
                                        pred: edge.from,
                                        value: *val,
                                        handler: h,
                                    },
                                ));
                            }
                        }
                        ValueDef::Inst(def_inst) => {
                            if !defined.contains(val) {
                                continue;
                            }
                            let Some(def) = module.inst(def_inst) else {
                                continue;
                            };
                            let Some(&di) = index.get(&def.block) else {
                                continue;
                            };
                            if !vdom.is_pt_reachable(use_pt) {
                                continue;
                            }
                            let def_p = inst_pos.get(&def_inst).copied().unwrap_or(usize::MAX);
                            let def_pt = vdom.def_pt(di, def_p);
                            if !vdom.dominates_pt(def_pt, use_pt) {
                                report.errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    VerifyErrorKind::PhiUseNotDominated {
                                        pred: edge.from,
                                        value: *val,
                                        def_block: def.block,
                                    },
                                ));
                            }
                        }
                    }
                }
                continue;
            }

            inst.op.for_each_operand(|val| {
                let Some(v) = module.value(val) else { return };
                match v.def {
                    ValueDef::Param(_) | ValueDef::Const(_) => {}
                    ValueDef::ExceptionParam(h) => {
                        if !defined.contains(&val) {
                            return;
                        }
                        let Some(&hi) = index.get(&h) else { return };
                        let h_pt = vdom.entry_pt(hi);
                        if bb_reachable && !vdom.dominates_pt(h_pt, bb_entry_pt) {
                            report.errors.push(err(
                                Some(bb),
                                Some(inst_id),
                                VerifyErrorKind::ExceptionParamOutOfScope {
                                    value: val,
                                    handler: h,
                                },
                            ));
                        }
                    }
                    ValueDef::Inst(def_inst) => {
                        if !defined.contains(&val) {
                            return;
                        }
                        let Some(def) = module.inst(def_inst) else {
                            return;
                        };
                        if def.block == bb {
                            let def_p = inst_pos.get(&def_inst).copied().unwrap_or(usize::MAX);
                            if def_p >= pos {
                                report.errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    VerifyErrorKind::UseBeforeDef { value: val },
                                ));
                            }
                            return;
                        }
                        let Some(&di) = index.get(&def.block) else {
                            return;
                        };
                        if !bb_reachable {
                            return;
                        }
                        let def_p = inst_pos.get(&def_inst).copied().unwrap_or(usize::MAX);
                        let def_pt = vdom.def_pt(di, def_p);
                        if !vdom.dominates_pt(def_pt, bb_entry_pt) {
                            report.errors.push(err(
                                Some(bb),
                                Some(inst_id),
                                VerifyErrorKind::UseNotDominated {
                                    value: val,
                                    def_block: def.block,
                                },
                            ));
                        }
                    }
                }
            });
        }
    }
}

fn check_ty_classes(module: &Module, ty: &Ty, out: &mut Vec<VerifyError>, func: Option<FuncId>) {
    match ty {
        Ty::Static(StaticTy::Reference(c)) => {
            if module.class(*c).is_none() {
                out.push(VerifyError {
                    func,
                    block: None,
                    inst: None,
                    kind: VerifyErrorKind::ClassOutOfRange(*c),
                });
            }
        }
        Ty::Union(xs) => {
            let mut stack: Vec<&[Ty]> = vec![xs];
            while let Some(slice) = stack.pop() {
                for item in slice {
                    match item {
                        Ty::Static(StaticTy::Reference(c)) if module.class(*c).is_none() => {
                            out.push(VerifyError {
                                func,
                                block: None,
                                inst: None,
                                kind: VerifyErrorKind::ClassOutOfRange(*c),
                            });
                        }
                        Ty::Union(sub) if !sub.is_empty() => stack.push(sub),
                        _ => {}
                    }
                }
            }
        }
        _ => {}
    }
}

fn check_annotations(
    module: &Module,
    anns: &[crate::module::Annotation],
    func: Option<FuncId>,
    out: &mut Vec<VerifyError>,
) {
    for ann in anns {
        if module.class(ann.class).is_none() {
            out.push(VerifyError {
                func,
                block: None,
                inst: None,
                kind: VerifyErrorKind::ClassOutOfRange(ann.class),
            });
        }
        for (name, val) in &ann.elements {
            if module.sym.resolve(*name).is_none() {
                out.push(VerifyError {
                    func,
                    block: None,
                    inst: None,
                    kind: VerifyErrorKind::SymOutOfRange(*name),
                });
            }
            match val {
                AnnValue::Const(c) if module.consts.get(*c).is_none() => out.push(VerifyError {
                    func,
                    block: None,
                    inst: None,
                    kind: VerifyErrorKind::ConstOutOfRange(*c),
                }),
                AnnValue::Class(c) if module.class(*c).is_none() => {
                    out.push(VerifyError {
                        func,
                        block: None,
                        inst: None,
                        kind: VerifyErrorKind::ClassOutOfRange(*c),
                    });
                }
                AnnValue::Field(c, f) => match module.class(*c) {
                    None => out.push(VerifyError {
                        func,
                        block: None,
                        inst: None,
                        kind: VerifyErrorKind::ClassOutOfRange(*c),
                    }),
                    Some(cls) if f.index() >= cls.fields.len() => out.push(VerifyError {
                        func,
                        block: None,
                        inst: None,
                        kind: VerifyErrorKind::FieldOutOfRange {
                            class: *c,
                            field: *f,
                        },
                    }),
                    Some(_) => {}
                },
                AnnValue::Name(s) if module.sym.resolve(*s).is_none() => out.push(VerifyError {
                    func,
                    block: None,
                    inst: None,
                    kind: VerifyErrorKind::SymOutOfRange(*s),
                }),
                _ => {}
            }
        }
    }
}

/// Verify the whole module: every function, cross-function arena disjointness,
/// and module-level reference & cycle integrity (`R2-H5`, `R2-D5`).
#[must_use = "verification findings must be checked via VerifyReport::is_ok()"]
pub fn verify_module(module: &Module) -> VerifyReport {
    let mut report = VerifyReport::default();
    let module_err = |kind: VerifyErrorKind| VerifyError {
        func: None,
        block: None,
        inst: None,
        kind,
    };
    let check_sym = |s: Sym, func: Option<FuncId>, out: &mut Vec<VerifyError>| {
        if module.sym.resolve(s).is_none() {
            out.push(VerifyError {
                func,
                block: None,
                inst: None,
                kind: VerifyErrorKind::SymOutOfRange(s),
            });
        }
    };

    let mut method_claimed_by: Vec<Option<ClassId>> = vec![None; module.functions.len()];

    for (ci, class) in module.classes.iter().enumerate() {
        let cid = ClassId::new(ci as u32);
        check_sym(class.descriptor, None, &mut report.errors);
        check_sym(class.name, None, &mut report.errors);
        if let Some(sf) = class.source_file {
            check_sym(sf, None, &mut report.errors);
        }
        if let Some(s) = class.super_class
            && module.class(s).is_none()
        {
            report
                .errors
                .push(module_err(VerifyErrorKind::ClassOutOfRange(s)));
        }
        for &i in &class.interfaces {
            if module.class(i).is_none() {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::ClassOutOfRange(i)));
            }
        }
        for &m in &class.methods {
            let Some(f_data) = module.func(m) else {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::FuncOutOfRange(m)));
                continue;
            };
            if method_claimed_by[m.index()].is_some() {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::DuplicateClassMethod(m)));
            } else {
                method_claimed_by[m.index()] = Some(cid);
            }
            if f_data.class_id != cid {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::ClassMethodOwnerMismatch {
                        class: cid,
                        func: m,
                        actual_class: f_data.class_id,
                    }));
            }
        }
        for field in &class.fields {
            check_sym(field.name, None, &mut report.errors);
            check_ty_classes(module, &field.ty, &mut report.errors, None);
            if let Some(iv) = field.initial_value
                && module.consts.get(iv).is_none()
            {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::ConstOutOfRange(iv)));
            }
            check_annotations(module, &field.annotations, None, &mut report.errors);
        }
        check_annotations(module, &class.annotations, None, &mut report.errors);
        if let Some(sn) = class.scope_names {
            match module.consts.get(sn) {
                None => report
                    .errors
                    .push(module_err(VerifyErrorKind::ConstOutOfRange(sn))),
                Some(c) if !is_literal_shape_const(c) => {
                    report
                        .errors
                        .push(module_err(VerifyErrorKind::InvalidConstShape {
                            const_id: sn,
                            detail: "scope_names requires a literal-shape constant",
                        }));
                }
                Some(_) => {}
            }
        }
        if let Some(esm) = &class.es_module {
            for imp in &esm.imports {
                match imp {
                    ImportDecl::Regular {
                        local_name,
                        import_name,
                        module_request,
                    } => {
                        check_sym(*local_name, None, &mut report.errors);
                        check_sym(*import_name, None, &mut report.errors);
                        check_sym(*module_request, None, &mut report.errors);
                    }
                    ImportDecl::Namespace {
                        local_name,
                        module_request,
                    } => {
                        check_sym(*local_name, None, &mut report.errors);
                        check_sym(*module_request, None, &mut report.errors);
                    }
                }
            }
            for exp in &esm.exports {
                match exp {
                    ExportDecl::Local {
                        local_name,
                        export_name,
                    } => {
                        check_sym(*local_name, None, &mut report.errors);
                        check_sym(*export_name, None, &mut report.errors);
                    }
                    ExportDecl::Indirect {
                        export_name,
                        import_name,
                        module_request,
                    } => {
                        check_sym(*export_name, None, &mut report.errors);
                        check_sym(*import_name, None, &mut report.errors);
                        check_sym(*module_request, None, &mut report.errors);
                    }
                    ExportDecl::Star { module_request } => {
                        check_sym(*module_request, None, &mut report.errors);
                    }
                }
            }
            for req in &esm.module_requests {
                check_sym(req.specifier, None, &mut report.errors);
            }
        }
    }

    for imp in &module.imports {
        match imp {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                check_sym(*local_name, None, &mut report.errors);
                check_sym(*import_name, None, &mut report.errors);
                check_sym(*module_request, None, &mut report.errors);
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                check_sym(*local_name, None, &mut report.errors);
                check_sym(*module_request, None, &mut report.errors);
            }
        }
    }
    for exp in &module.exports {
        match exp {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                check_sym(*local_name, None, &mut report.errors);
                check_sym(*export_name, None, &mut report.errors);
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                check_sym(*export_name, None, &mut report.errors);
                check_sym(*import_name, None, &mut report.errors);
                check_sym(*module_request, None, &mut report.errors);
            }
            ExportDecl::Star { module_request } => {
                check_sym(*module_request, None, &mut report.errors);
            }
        }
    }
    for req in &module.module_requests {
        check_sym(req.specifier, None, &mut report.errors);
    }

    let mut global_blocks: HashSet<BlockId> = HashSet::with_capacity(module.blocks.len());
    let mut global_insts: HashSet<InstId> = HashSet::with_capacity(module.insts.len());
    let mut global_values: HashSet<ValueId> = HashSet::with_capacity(module.values.len());

    for (fi, func) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        if module.class(func.class_id).is_none() {
            report
                .errors
                .push(module_err(VerifyErrorKind::ClassOutOfRange(func.class_id)));
        } else if method_claimed_by[fi].is_none() {
            report
                .errors
                .push(module_err(VerifyErrorKind::UnlistedClassMethod {
                    class: func.class_id,
                    func: fid,
                }));
        }
        check_sym(func.name, Some(fid), &mut report.errors);
        if let Some(sig) = &func.sig {
            if let Some(ret) = &sig.return_ty {
                check_ty_classes(module, ret, &mut report.errors, Some(fid));
            }
            for pty in &sig.param_tys {
                check_ty_classes(module, pty, &mut report.errors, Some(fid));
            }
        }
        check_annotations(module, &func.annotations, Some(fid), &mut report.errors);
        if let Some(dbg) = &func.debug {
            if let Some(sf) = dbg.source_file {
                check_sym(sf, Some(fid), &mut report.errors);
            }
            for &pn in &dbg.param_names {
                check_sym(pn, Some(fid), &mut report.errors);
            }
            for ln in &dbg.local_names {
                check_sym(ln.name, Some(fid), &mut report.errors);
                if let Some(ty) = &ln.ty {
                    check_ty_classes(module, ty, &mut report.errors, Some(fid));
                }
            }
            if let Some(sn) = dbg.scope_names {
                match module.consts.get(sn) {
                    None => report.errors.push(VerifyError {
                        func: Some(fid),
                        block: None,
                        inst: None,
                        kind: VerifyErrorKind::ConstOutOfRange(sn),
                    }),
                    Some(c) if !is_literal_shape_const(c) => {
                        report.errors.push(VerifyError {
                            func: Some(fid),
                            block: None,
                            inst: None,
                            kind: VerifyErrorKind::InvalidConstShape {
                                const_id: sn,
                                detail: "scope_names requires a literal-shape constant",
                            },
                        });
                    }
                    Some(_) => {}
                }
            }
        }

        let mut func_unique_blocks: HashSet<BlockId> = HashSet::with_capacity(func.blocks.len());
        for &bb in &func.blocks {
            if func_unique_blocks.insert(bb) && !global_blocks.insert(bb) {
                report.errors.push(VerifyError {
                    func: Some(fid),
                    block: Some(bb),
                    inst: None,
                    kind: VerifyErrorKind::DuplicateBlock(bb),
                });
            }
        }
        let mut func_unique_vals: HashSet<ValueId> = HashSet::new();
        for &v in func.params.iter().chain(func.frame_init_consts.iter()) {
            if func_unique_vals.insert(v) && !global_values.insert(v) {
                report.errors.push(VerifyError {
                    func: Some(fid),
                    block: None,
                    inst: None,
                    kind: VerifyErrorKind::DuplicateValueDef(v),
                });
            }
        }
        for region in &func.try_regions {
            for catch in &region.catches {
                if func_unique_vals.insert(catch.exception)
                    && !global_values.insert(catch.exception)
                {
                    report.errors.push(VerifyError {
                        func: Some(fid),
                        block: Some(catch.handler),
                        inst: None,
                        kind: VerifyErrorKind::DuplicateValueDef(catch.exception),
                    });
                }
            }
        }
        let mut func_unique_insts: HashSet<InstId> = HashSet::new();
        let mut seen_func_blocks: HashSet<BlockId> = HashSet::with_capacity(func.blocks.len());
        for &bb in &func.blocks {
            if !seen_func_blocks.insert(bb) {
                continue;
            }
            if let Some(block) = module.block(bb) {
                for &iid in &block.insts {
                    if func_unique_insts.insert(iid) && !global_insts.insert(iid) {
                        report.errors.push(VerifyError {
                            func: Some(fid),
                            block: Some(bb),
                            inst: Some(iid),
                            kind: VerifyErrorKind::DuplicateInst(iid),
                        });
                    }
                    if let Some(inst) = module.inst(iid)
                        && let Some(res) = inst.result
                        && func_unique_vals.insert(res)
                        && !global_values.insert(res)
                    {
                        report.errors.push(VerifyError {
                            func: Some(fid),
                            block: Some(bb),
                            inst: Some(iid),
                            kind: VerifyErrorKind::DuplicateValueDef(res),
                        });
                    }
                }
            }
        }

        let fr = verify_func(module, fid);
        report.errors.extend(fr.errors);
        report.warnings.extend(fr.warnings);
    }

    for val in &module.values {
        check_ty_classes(module, &val.ty, &mut report.errors, None);
    }

    // Iterative ConstPool bounds + 3-color cycle detection (`0=unvisited, 1=visiting, 2=done`).
    let pool_len = module.consts.len();
    for ci in 0..pool_len {
        let cid = ConstId::new(ci as u32);
        let Some(c) = module.consts.get(cid) else {
            continue;
        };
        match c {
            Const::MethodRef { func, .. } if module.func(*func).is_none() => {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::FuncOutOfRange(*func)));
            }
            Const::String(s) | Const::BigInt(s) | Const::EtsImplements(s) => {
                check_sym(*s, None, &mut report.errors);
            }
            Const::LiteralBufferRef(child) => match module.consts.get(*child) {
                None => report
                    .errors
                    .push(module_err(VerifyErrorKind::ConstOutOfRange(*child))),
                Some(inner) if !is_literal_shape_const(inner) => {
                    report
                        .errors
                        .push(module_err(VerifyErrorKind::InvalidConstShape {
                            const_id: cid,
                            detail: "LiteralBufferRef target must be a literal-shape constant",
                        }));
                }
                Some(_) => {}
            },
            Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
                for &child in items {
                    if module.consts.get(child).is_none() {
                        report
                            .errors
                            .push(module_err(VerifyErrorKind::ConstOutOfRange(child)));
                    }
                }
            }
            Const::ObjectLiteral { keys, values } => {
                if keys.len() != values.len() {
                    report
                        .errors
                        .push(module_err(VerifyErrorKind::ObjectLiteralArityMismatch {
                            const_id: cid,
                            keys: keys.len(),
                            values: values.len(),
                        }));
                }
                for &child in keys.iter().chain(values.iter()) {
                    if module.consts.get(child).is_none() {
                        report
                            .errors
                            .push(module_err(VerifyErrorKind::ConstOutOfRange(child)));
                    }
                }
            }
            _ => {}
        }
    }

    let mut color = vec![0u8; pool_len];
    let mut dfs_stack: Vec<(usize, usize)> = Vec::new();
    for root in 0..pool_len {
        if color[root] != 0 {
            continue;
        }
        color[root] = 1;
        dfs_stack.push((root, 0));
        while let Some((ci, child_pos)) = dfs_stack.last_mut() {
            let cur = *ci;
            let next_child = match module.consts.get(ConstId::new(cur as u32)) {
                Some(Const::LiteralBufferRef(child)) => (*child_pos == 0).then_some(*child),
                Some(Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. }) => {
                    items.get(*child_pos).copied()
                }
                Some(Const::ObjectLiteral { keys, values }) => {
                    let pos = *child_pos;
                    if pos < keys.len() {
                        Some(keys[pos])
                    } else {
                        values.get(pos - keys.len()).copied()
                    }
                }
                _ => None,
            };
            if let Some(child_id) = next_child {
                *child_pos += 1;
                let ch_idx = child_id.index();
                if ch_idx < pool_len {
                    match color[ch_idx] {
                        0 => {
                            color[ch_idx] = 1;
                            dfs_stack.push((ch_idx, 0));
                        }
                        1 => {
                            report
                                .errors
                                .push(module_err(VerifyErrorKind::ConstCycle(child_id)));
                        }
                        _ => {}
                    }
                }
            } else {
                color[cur] = 2;
                dfs_stack.pop();
            }
        }
    }

    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::Const;
    use crate::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
    use crate::module::{ClassData, FunctionKind};
    use crate::op::BinOp;
    use crate::ty::Ty;

    // ── Test scaffolding (hand-built modules) ────────────────────────

    fn mk_module() -> Module {
        let mut m = Module::new();
        let name = m.sym.intern("Ltest;");
        m.classes.push(ClassData::new(name, name));
        m
    }

    fn add_func(m: &mut Module) -> FuncId {
        let name = m.sym.intern("f");
        let id = FuncId::new(m.functions.len() as u32);
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            name,
            FunctionKind::Function,
        ));
        m.classes[0].methods.push(id);
        add_block(m, id); // entry
        id
    }

    fn add_block(m: &mut Module, f: FuncId) -> BlockId {
        let id = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f).unwrap().blocks.push(id);
        id
    }

    fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    }

    fn emit(m: &mut Module, b: BlockId, op: Op) -> ValueId {
        assert!(op.has_result());
        let inst = push_inst(m, b, op);
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(inst),
            ty: Ty::Any,
        });
        m.inst_mut(inst).unwrap().result = Some(val);
        val
    }

    fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
        assert!(!op.has_result());
        push_inst(m, b, op)
    }

    fn add_param(m: &mut Module, f: FuncId, idx: u16) -> ValueId {
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        m.func_mut(f).unwrap().params.push(val);
        val
    }

    fn add_exception_param(m: &mut Module, handler: BlockId) -> ValueId {
        let val = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(handler),
            ty: Ty::Any,
        });
        val
    }

    fn link(m: &mut Module, from: BlockId, to: BlockId) {
        m.block_mut(to).unwrap().preds.push(Edge {
            from,
            kind: EdgeKind::Normal,
        });
    }

    fn link_exc(m: &mut Module, from: BlockId, to: BlockId) {
        m.block_mut(to).unwrap().preds.push(Edge {
            from,
            kind: EdgeKind::Exceptional,
        });
    }

    fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId, exc: ValueId) {
        for &p in &protected {
            link_exc(m, p, handler);
        }
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected,
            catches: vec![Catch {
                handler,
                exception: exc,
                type_class: None,
            }],
        });
    }

    fn entry_of(m: &Module, f: FuncId) -> BlockId {
        m.func(f).unwrap().blocks[0]
    }

    fn add(m: &mut Module, b: BlockId, l: ValueId, r: ValueId) -> ValueId {
        emit(
            m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: l,
                right: r,
            },
        )
    }

    fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
        let c = m.consts.push(Const::number(x));
        emit(m, b, Op::LoadConst(c))
    }

    fn has_error(r: &VerifyReport, f: impl Fn(&VerifyErrorKind) -> bool) -> bool {
        r.errors.iter().any(|e| f(&e.kind))
    }

    // ── Tests ────────────────────────────────────────────────────────

    #[test]
    fn valid_simple_function_passes() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0); // this
        let p1 = add_param(&mut m, f, 1);
        let sum = add(&mut m, entry, p0, p1);
        emit_void(&mut m, entry, Op::Return { value: Some(sum) });

        let r = verify_func(&m, f);
        assert!(r.is_ok(), "expected no errors, got: {:?}", r.errors);
        assert!(r.warnings.is_empty());
    }

    /// N45 red pin: diamond where b1's def cannot dominate b2's use.
    #[test]
    fn non_dominated_use_in_diamond_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        let v = load_number(&mut m, b1, 1.0);
        emit_void(&mut m, b1, Op::Return { value: None });
        emit_void(&mut m, b2, Op::Return { value: Some(v) });

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(k, VerifyErrorKind::UseNotDominated { .. })),
            "expected dominance error, got: {:?}",
            r.errors
        );
    }

    /// N64 red pin: an unreachable Normal predecessor must NOT exempt a
    /// reachable block's uses from dominance checks. Same diamond as
    /// `non_dominated_use_in_diamond_is_error` (b2's use of v is
    /// non-dominated), plus an unreachable block u with a Normal edge
    /// into b2 — pre-fix u's degenerate dominator set polluted b2's
    /// intersection, entry was lost, and b2's uses were exempted.
    #[test]
    fn unreachable_normal_pred_does_not_exempt_dominance() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        let v = load_number(&mut m, b1, 1.0);
        emit_void(&mut m, b1, Op::Return { value: None });
        emit_void(&mut m, b2, Op::Return { value: Some(v) });
        // The N64 polluter: unreachable from the entry, but its
        // terminator really targets b2 (a Normal pred edge into b2).
        let u = add_block(&mut m, f);
        emit_void(&mut m, u, Op::Branch { dest: b2 });
        link(&mut m, u, b2);

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(k, VerifyErrorKind::UseNotDominated { .. })),
            "unreachable Normal pred must not exempt b2's non-dominated use, got: {:?}",
            r.errors
        );
    }

    /// N27: a phi on a reachable zero-pred block (here: the entry) is an
    /// error.
    #[test]
    fn reachable_zero_pred_phi_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        emit(&mut m, entry, Op::Phi { entries: vec![] });
        emit_void(&mut m, entry, Op::Return { value: None });

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(k, VerifyErrorKind::ZeroPredPhi)),
            "expected N27 error, got: {:?}",
            r.errors
        );
    }

    /// Exactly one terminator per block: a terminator mid-block means
    /// two.
    #[test]
    fn dual_terminators_are_an_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let target = add_block(&mut m, f);
        emit_void(&mut m, entry, Op::Branch { dest: target }); // terminator 1
        emit_void(&mut m, entry, Op::Return { value: None }); // terminator 2
        emit_void(&mut m, target, Op::Return { value: None });

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(k, VerifyErrorKind::MidBlockTerminator)),
            "expected mid-block terminator error, got: {:?}",
            r.errors
        );
    }

    #[test]
    fn missing_terminator_is_an_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        load_number(&mut m, entry, 1.0);

        let r = verify_func(&m, f);
        assert!(has_error(&r, |k| matches!(
            k,
            VerifyErrorKind::MissingTerminator
        )));
    }

    /// Wrong arity: a phi whose entry count disagrees with the block's
    /// predecessor count.
    #[test]
    fn phi_arity_mismatch_is_an_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, join);
        emit_void(&mut m, entry, Op::Branch { dest: join });
        let v = load_number(&mut m, join, 1.0);
        // Two entries, but only one predecessor edge.
        emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: entry,
                            kind: EdgeKind::Normal,
                        },
                        v,
                    ),
                    (
                        Edge {
                            from: join,
                            kind: EdgeKind::Normal,
                        },
                        v,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: None });

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(
                k,
                VerifyErrorKind::PhiArity {
                    entries: 2,
                    preds: 1
                }
            )),
            "expected phi arity error, got: {:?}",
            r.errors
        );
        assert!(has_error(&r, |k| matches!(
            k,
            VerifyErrorKind::PhiForeignEdge { .. }
        )));
    }

    /// N45 exemptions, positive form: a handler using an entry-defined
    /// value and a value defined in its protected block is fine.
    #[test]
    fn entry_defined_use_in_handler_is_exempt() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, t);
        link(&mut m, t, join);
        link(&mut m, h, join);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);

        let e0 = load_number(&mut m, entry, 0.0); // entry-defined
        emit_void(&mut m, entry, Op::Branch { dest: t });
        let v = load_number(&mut m, t, 1.0); // defined in protected block
        emit_void(&mut m, t, Op::Branch { dest: join });
        // Handler uses an entry-defined value AND a protected-block def.
        let w = add(&mut m, h, v, e0);
        emit_void(&mut m, h, Op::Branch { dest: join });
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: t,
                            kind: EdgeKind::Normal,
                        },
                        v,
                    ),
                    (
                        Edge {
                            from: h,
                            kind: EdgeKind::Normal,
                        },
                        w,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });

        let r = verify_func(&m, f);
        assert!(
            r.is_ok(),
            "exception-dispatch value flow must be exempt: {:?}",
            r.errors
        );
    }

    /// ExceptionParam is valid inside its own handler.
    #[test]
    fn exception_param_in_own_handler_is_valid() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        link(&mut m, entry, t);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);

        emit_void(&mut m, entry, Op::Branch { dest: t });
        emit_void(&mut m, t, Op::Return { value: None });
        let one = load_number(&mut m, h, 1.0);
        let w = add(&mut m, h, exc, one); // uses the exception param
        emit_void(&mut m, h, Op::Return { value: Some(w) });

        let r = verify_func(&m, f);
        assert!(
            r.is_ok(),
            "exception param in its handler must be valid: {:?}",
            r.errors
        );
    }

    /// ...but NOT outside the handler's downstream.
    #[test]
    fn exception_param_outside_handler_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        link(&mut m, entry, t);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);

        emit_void(&mut m, entry, Op::Branch { dest: t });
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Return { value: None });
        // Entry (Normal-reachable, NOT in h's downstream) uses exc.
        // Rebuild entry: branch first is already emitted... use a fresh
        // normal block instead.
        let n2 = add_block(&mut m, f);
        // entry currently ends with Branch(t) — add a second branch target
        // via a diamond: replace with CondBranch.
        let p0 = add_param(&mut m, f, 0);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: t,
                false_dest: n2,
            },
        );
        link(&mut m, entry, n2);
        emit_void(&mut m, n2, Op::Return { value: Some(exc) });

        let r = verify_func(&m, f);
        assert!(
            has_error(&r, |k| matches!(
                k,
                VerifyErrorKind::ExceptionParamOutOfScope { .. }
            )),
            "expected exception-param scope error, got: {:?}",
            r.errors
        );
    }

    /// Dead blocks legitimately carry junk: no N27, no dominance errors.
    #[test]
    fn dead_block_junk_is_exempt() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        emit_void(&mut m, entry, Op::Return { value: None });

        // Unreachable chain with a cross-block use and a zero-pred phi.
        let d1 = add_block(&mut m, f);
        let d2 = add_block(&mut m, f);
        let d3 = add_block(&mut m, f);
        link(&mut m, d1, d2);
        let v = load_number(&mut m, d1, 1.0);
        emit_void(&mut m, d1, Op::Branch { dest: d2 });
        emit_void(&mut m, d2, Op::Return { value: Some(v) }); // non-dominated, but dead
        emit(&mut m, d3, Op::Phi { entries: vec![] }); // zero-pred phi, but dead
        emit_void(&mut m, d3, Op::Return { value: None });

        let r = verify_func(&m, f);
        assert!(r.is_ok(), "dead-block junk must be exempt: {:?}", r.errors);
    }

    /// A well-formed phi over normal edges verifies clean.
    #[test]
    fn valid_phi_on_edges_passes() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        link(&mut m, b1, join);
        link(&mut m, b2, join);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        let v1 = load_number(&mut m, b1, 1.0);
        emit_void(&mut m, b1, Op::Branch { dest: join });
        let v2 = load_number(&mut m, b2, 2.0);
        emit_void(&mut m, b2, Op::Branch { dest: join });
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b1,
                            kind: EdgeKind::Normal,
                        },
                        v1,
                    ),
                    (
                        Edge {
                            from: b2,
                            kind: EdgeKind::Normal,
                        },
                        v2,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });

        let r = verify_func(&m, f);
        assert!(r.is_ok(), "valid phi must pass: {:?}", r.errors);
        assert!(r.warnings.is_empty());
    }

    /// N38: a handler phi joining distinct values across exceptional
    /// edges warns — and does not error.
    #[test]
    fn handler_phi_with_distinct_exceptional_values_warns() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let t1 = add_block(&mut m, f);
        let t2 = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        link(&mut m, entry, t1);
        link(&mut m, entry, t2);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: t1,
                false_dest: t2,
            },
        );
        let v1 = load_number(&mut m, t1, 1.0);
        emit_void(&mut m, t1, Op::Return { value: Some(v1) });
        let v2 = load_number(&mut m, t2, 2.0);
        emit_void(&mut m, t2, Op::Return { value: Some(v2) });
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t1, t2], h, exc);
        let phi = emit(
            &mut m,
            h,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: t1,
                            kind: EdgeKind::Exceptional,
                        },
                        v1,
                    ),
                    (
                        Edge {
                            from: t2,
                            kind: EdgeKind::Exceptional,
                        },
                        v2,
                    ),
                ],
            },
        );
        emit_void(&mut m, h, Op::Return { value: Some(phi) });

        let r = verify_func(&m, f);
        assert!(r.is_ok(), "N38 is a warning, not an error: {:?}", r.errors);
        assert!(
            r.warnings
                .iter()
                .any(|w| matches!(w.kind, VerifyWarningKind::HandlerPhiImpreciseJoin { .. })),
            "expected N38 warning, got: {:?}",
            r.warnings
        );
    }

    #[test]
    fn verify_module_covers_all_funcs() {
        let mut m = mk_module();
        let f1 = add_func(&mut m);
        let e1 = entry_of(&m, f1);
        emit_void(&mut m, e1, Op::Return { value: None });
        let f2 = add_func(&mut m);
        let e2 = entry_of(&m, f2);
        emit_void(&mut m, e2, Op::Return { value: None });

        let r = verify_module(&m);
        assert!(r.is_ok(), "got: {:?}", r.errors);
    }

    #[test]
    fn external_function_needs_no_body() {
        let mut m = mk_module();
        let name = m.sym.intern("print");
        m.functions.push(FunctionData {
            is_external: true,
            ..FunctionData::new(ClassId::new(0), name, FunctionKind::Function)
        });
        let f = FuncId::new(m.functions.len() as u32 - 1);
        let r = verify_func(&m, f);
        assert!(r.is_ok(), "got: {:?}", r.errors);
    }

    // ── Negative coverage per error arm ──────────────────────────────
    //
    // Each test builds the minimal invalid shape from the arm→shape table
    // and asserts the exact VerifyErrorKind plus its Display message (the
    // message asserts also cover the VerifyError/VerifyWarning Display and
    // source() impls).
    //
    // Deliberately absent (UNREACHABLE-INVARIANT, documented):
    // - ArityMismatch: Op::arity() and Op::operands() both derive from the
    //   same op value; a mismatch needs taxonomy drift in op.rs, not an
    //   input property (the op.rs drift-guard test pins consistency).
    // - verify_dominance's func-None early return: its only caller already
    //   resolved `func`.
    // - the empty-npreds dominator arm: after the N64 retain every
    //   Normal-reachable non-entry block has a reachable Normal pred by
    //   construction, and the entry is skipped.

    /// Extract the single error matching `pred`.
    fn expect_error<'a>(
        r: &'a VerifyReport,
        pred: impl Fn(&VerifyErrorKind) -> bool,
        what: &str,
    ) -> &'a VerifyError {
        let matches: Vec<_> = r.errors.iter().filter(|e| pred(&e.kind)).collect();
        assert_eq!(
            matches.len(),
            1,
            "expected exactly one {what}, got: {:?}",
            r.errors
        );
        matches[0]
    }

    /// A module with one function whose entry just returns.
    fn minimal_func_module() -> (Module, FuncId) {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        emit_void(&mut m, entry, Op::Return { value: None });
        (m, f)
    }

    #[test]
    fn func_out_of_range_is_module_level_error() {
        let (m, _) = minimal_func_module();
        let bogus = FuncId::new(999);
        let r = verify_func(&m, bogus);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus),
            "FuncOutOfRange",
        );
        assert_eq!(e.func, None, "a missing function has no location");
        assert_eq!(
            format!("{e}"),
            "verify error: function FuncId(999) is outside the function table"
        );
        assert!(std::error::Error::source(e).is_some());
    }

    #[test]
    fn missing_body_is_error() {
        let mut m = mk_module();
        let name = m.sym.intern("bodiless");
        m.functions.push(FunctionData::new(
            ClassId::new(0),
            name,
            FunctionKind::Function,
        ));
        let f = FuncId::new(m.functions.len() as u32 - 1);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::MissingBody),
            "MissingBody",
        );
        assert_eq!(e.func, Some(f));
        assert_eq!(e.block, None);
        assert_eq!(
            format!("{e}"),
            format!("verify error in {f}: function has no blocks but is not external")
        );
    }

    #[test]
    fn duplicate_block_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        m.func_mut(f).unwrap().blocks.push(entry); // entry listed twice
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::DuplicateBlock(b) if *b == entry),
            "DuplicateBlock",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error in FuncId(0): block list contains duplicate {entry}")
        );
    }

    #[test]
    fn block_out_of_arena_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b2 = add_block(&mut m, f);
        emit_void(&mut m, b2, Op::Return { value: None });
        // Rewire: entry -> b2, and a bogus arena id listed as a block with
        // a Normal pred edge from it (rides the defensive normal_succs
        // empty arms: out-of-arena block lookup).
        let bogus = BlockId::new(999);
        m.func_mut(f).unwrap().blocks.push(bogus);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b2 });
        link(&mut m, entry, b2);
        link(&mut m, bogus, b2); // pred from an out-of-arena block
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::BlockOutOfArena(b) if *b == bogus),
            "BlockOutOfArena",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error in FuncId(0): {bogus} is outside the block arena")
        );
    }

    #[test]
    fn foreign_try_block_is_error() {
        let (mut m, f) = minimal_func_module();
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        emit_void(&mut m, gx, Op::Return { value: None });
        // f's try region protects a block of g.
        let h = add_block(&mut m, f);
        emit_void(&mut m, h, Op::Return { value: None });
        let exc = add_exception_param(&mut m, h);
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![gx],
            catches: vec![Catch {
                handler: h,
                exception: exc,
                type_class: None,
            }],
        });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignTryBlock(b) if *b == gx),
            "ForeignTryBlock",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error in FuncId(0): try region references foreign block {gx}")
        );
    }

    #[test]
    fn duplicate_try_block_is_error() {
        let (mut m, f) = minimal_func_module();
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Return { value: None });
        let exc = add_exception_param(&mut m, h);
        link_exc(&mut m, t, h);
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![t, t],
            catches: vec![Catch {
                handler: h,
                exception: exc,
                type_class: None,
            }],
        });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::DuplicateTryBlock(b) if *b == t),
            "DuplicateTryBlock",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {t}: try region contains duplicate protected block {t}"
            )
        );
    }

    /// A foreign handler is an error; an in-arena foreign handler that
    /// never received the exceptional edge also trips the
    /// MissingExceptionalPred check. A handler outside the ARENA rides the
    /// N38 scan's defensive skip.
    #[test]
    fn foreign_handler_and_missing_exceptional_pred_are_errors() {
        let (mut m, f) = minimal_func_module();
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        emit_void(&mut m, gx, Op::Return { value: None });
        let t = add_block(&mut m, f);
        emit_void(&mut m, t, Op::Return { value: None });
        // Case 1: handler is another function's block, no exceptional edge.
        let exc = add_exception_param(&mut m, gx);
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![t],
            catches: vec![Catch {
                handler: gx,
                exception: exc,
                type_class: None,
            }],
        });
        // Case 2: handler outside the block arena entirely.
        let arena_bug = BlockId::new(999);
        let exc2 = add_exception_param(&mut m, arena_bug);
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![t],
            catches: vec![Catch {
                handler: arena_bug,
                exception: exc2,
                type_class: None,
            }],
        });
        let r = verify_func(&m, f);
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignHandler(b) if *b == gx),
            "ForeignHandler(gx)",
        );
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignHandler(b) if *b == arena_bug),
            "ForeignHandler(arena)",
        );
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::MissingExceptionalPred {
                        handler,
                        protected,
                    } if *handler == gx && *protected == t
                )
            },
            "MissingExceptionalPred",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {gx}: handler {gx} is missing the exceptional predecessor edge from protected block {t}"
            )
        );
    }

    #[test]
    fn bad_exception_param_is_error() {
        let (mut m, f) = minimal_func_module();
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Return { value: None });
        // The catch's exception value is a plain PARAM, not the dispatch's
        // ExceptionParam.
        let not_exc = add_param(&mut m, f, 0);
        link_exc(&mut m, t, h);
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![t],
            catches: vec![Catch {
                handler: h,
                exception: not_exc,
                type_class: None,
            }],
        });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::BadExceptionParam { value, handler }
                        if *value == not_exc && *handler == h
                )
            },
            "BadExceptionParam",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {h}: catch exception value {not_exc} is not defined by ExceptionParam({h})"
            )
        );
    }

    #[test]
    fn param_out_of_arena_is_error() {
        let (mut m, f) = minimal_func_module();
        let bogus = ValueId::new(999);
        m.func_mut(f).unwrap().params.push(bogus);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ValueOutOfArena(v) if *v == bogus),
            "ValueOutOfArena(param)",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error in FuncId(0): result value {bogus} is outside the value arena")
        );
    }

    #[test]
    fn param_def_mismatch_is_error() {
        let (mut m, f) = minimal_func_module();
        let p0 = add_param(&mut m, f, 0); // params[0], def Param(0): fine
        let _ = p0;
        // params[1] whose def says Param(7).
        let bad = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(7),
            ty: Ty::Any,
        });
        m.func_mut(f).unwrap().params.push(bad);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::ParamDefMismatch { value, actual }
                        if *value == bad && *actual == ValueDef::Param(7)
                )
            },
            "ParamDefMismatch",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0): parameter value {bad} has mismatched definition {:?}",
                ValueDef::Param(7)
            )
        );
    }

    /// An out-of-arena InstId in a block's list, in the middle (rides the
    /// structural-scan skips) and as the last entry of a predecessor block
    /// (rides normal_succs' out-of-arena last-inst arm).
    #[test]
    fn inst_out_of_arena_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let bogus = InstId::new(999);
        // Middle of the entry block: [bogus, return].
        m.block_mut(entry).unwrap().insts.insert(0, bogus);
        // A second block whose ONLY entry is bogus, listed as a Normal pred
        // of entry... would trip EntryHasPred; use a mid block instead.
        let b2 = add_block(&mut m, f);
        m.block_mut(b2).unwrap().insts.push(bogus);
        // entry currently ends with Return; give the CFG entry -> b2 via a
        // branch and reterminate b2 through the bogus slot (stays bogus).
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        insts.push(bogus);
        emit_void(&mut m, entry, Op::Branch { dest: b2 });
        link(&mut m, entry, b2);
        link(&mut m, b2, entry);
        let r = verify_func(&m, f);
        let matches: Vec<_> = r
            .errors
            .iter()
            .filter(|e| matches!(e.kind, VerifyErrorKind::InstOutOfArena(id) if id == bogus))
            .collect();
        assert_eq!(
            matches.len(),
            2,
            "both block listings must report the dangling inst: {:?}",
            r.errors
        );
        assert_eq!(
            format!("{}", matches[0]),
            format!("verify error in FuncId(0) {entry} {bogus}: {bogus} is outside the inst arena")
        );
    }

    #[test]
    fn inst_block_mismatch_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b2 = add_block(&mut m, f);
        let c = m.consts.push(Const::number(1.0));
        // The inst records `entry` as its home but is ALSO listed in b2.
        let i = push_inst(&mut m, entry, Op::LoadConst(c));
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b2 });
        link(&mut m, entry, b2);
        m.block_mut(b2).unwrap().insts.push(i);
        emit_void(&mut m, b2, Op::Return { value: None });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::InstBlockMismatch { expected, actual }
                        if *expected == b2 && *actual == entry
                )
            },
            "InstBlockMismatch",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {b2} {i}: instruction is listed in {b2} but records its block as {entry}"
            )
        );
    }

    #[test]
    fn result_out_of_arena_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let c = m.consts.push(Const::number(1.0));
        let i = push_inst(&mut m, entry, Op::LoadConst(c));
        let bogus = ValueId::new(999);
        m.inst_mut(i).unwrap().result = Some(bogus);
        // Keep the block well-terminated: [load, return].
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ValueOutOfArena(v) if *v == bogus),
            "ValueOutOfArena(result)",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {i}: result value {bogus} is outside the value arena"
            )
        );
    }

    #[test]
    fn result_def_mismatch_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let c = m.consts.push(Const::number(1.0));
        let i = push_inst(&mut m, entry, Op::LoadConst(c));
        // The result value's def points at a Param, not at its inst.
        let v = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        m.inst_mut(i).unwrap().result = Some(v);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::ResultDefMismatch { value, actual }
                        if *value == v && *actual == ValueDef::Param(0)
                )
            },
            "ResultDefMismatch",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {i}: result {v} has mismatched definition {:?}",
                ValueDef::Param(0)
            )
        );
    }

    #[test]
    fn entry_has_pred_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b1 });
        emit_void(&mut m, b1, Op::Branch { dest: entry }); // back-edge
        link(&mut m, entry, b1);
        link(&mut m, b1, entry);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::EntryHasPred),
            "EntryHasPred",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry}: entry block has a predecessor from another block"
            )
        );
    }

    #[test]
    fn duplicate_pred_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b1 });
        link(&mut m, entry, b1);
        link(&mut m, entry, b1); // the same edge twice
        emit_void(&mut m, b1, Op::Return { value: None });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::DuplicatePred(edge) if edge.from == entry),
            "DuplicatePred",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {b1}: duplicate predecessor edge {:?}",
                Edge {
                    from: entry,
                    kind: EdgeKind::Normal,
                }
            )
        );
    }

    #[test]
    fn foreign_pred_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b1 });
        link(&mut m, entry, b1);
        emit_void(&mut m, b1, Op::Return { value: None });
        // A pred edge from another function's block (in-arena, foreign).
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        emit_void(&mut m, gx, Op::Return { value: None });
        link(&mut m, gx, b1);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignPred(b) if *b == gx),
            "ForeignPred",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error in FuncId(0) {b1}: predecessor {gx} is not in this function")
        );
    }

    /// An empty block errors; its use as a Normal predecessor also rides
    /// normal_succs' empty-insts arm (and PredDoesNotTarget).
    #[test]
    fn empty_block_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let empty = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b2 });
        link(&mut m, entry, b2);
        emit_void(&mut m, b2, Op::Return { value: None });
        link(&mut m, empty, b2); // the empty block as a predecessor
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::EmptyBlock),
            "EmptyBlock",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {empty}: block has no instructions (missing terminator)"
            )
        );
        assert!(
            has_error(
                &r,
                |k| matches!(k, VerifyErrorKind::PredDoesNotTarget(b) if *b == empty)
            ),
            "the empty predecessor's terminator cannot target anything: {:?}",
            r.errors
        );
    }

    #[test]
    fn foreign_successor_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        emit_void(&mut m, gx, Op::Return { value: None });
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: gx });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignSuccessor(b) if *b == gx),
            "ForeignSuccessor",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: successor {gx} is not in this function",
                e.inst.unwrap()
            )
        );
    }

    #[test]
    fn phi_duplicate_edge_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        link(&mut m, b1, join);
        link(&mut m, b2, join);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        let v1 = load_number(&mut m, b1, 1.0);
        emit_void(&mut m, b1, Op::Branch { dest: join });
        emit_void(&mut m, b2, Op::Branch { dest: join });
        let e1 = Edge {
            from: b1,
            kind: EdgeKind::Normal,
        };
        // Two entries keyed on the SAME edge (count still equals preds).
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![(e1, v1), (e1, v1)],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::PhiDuplicateEdge { edge } if *edge == e1),
            "PhiDuplicateEdge",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {join} {:?}: phi contains duplicate entry edge {:?}",
                e.inst.unwrap(),
                e1
            )
        );
    }

    #[test]
    fn undefined_value_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let bogus = ValueId::new(999);
        let v = add(&mut m, entry, bogus, p0);
        emit_void(&mut m, entry, Op::Return { value: Some(v) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::UndefinedValue(val) if *val == bogus),
            "UndefinedValue",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: uses undefined value {bogus}",
                e.inst.unwrap()
            )
        );
    }

    /// A phi entry whose value is outside the value arena: UndefinedValue
    /// from the use scan, and the dominance phi-entry walk skips it.
    #[test]
    fn undefined_phi_entry_value_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, b1, join);
        emit_void(&mut m, entry, Op::Branch { dest: b1 });
        emit_void(&mut m, b1, Op::Branch { dest: join });
        let bogus = ValueId::new(999);
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![(
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    bogus,
                )],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::UndefinedValue(v) if *v == bogus),
            "UndefinedValue(phi entry)",
        );
    }

    /// A used value whose def is an out-of-arena inst is not owned
    /// (ForeignValue); the dominance walk skips the dangling def.
    #[test]
    fn foreign_value_out_of_arena_def_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let dangling = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
        });
        let v = add(&mut m, entry, dangling, p0);
        emit_void(&mut m, entry, Op::Return { value: Some(v) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == dangling),
            "ForeignValue",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: value {dangling} is not owned by this function",
                e.inst.unwrap()
            )
        );
    }

    /// A used value whose def inst lives in ANOTHER function's block is
    /// foreign; both the operand and phi-entry dominance walks skip it.
    #[test]
    fn foreign_value_foreign_block_def_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        // The defining inst lives in g's entry block.
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        let foreign_def = {
            let c = m.consts.push(Const::number(7.0));
            emit(&mut m, gx, Op::LoadConst(c))
        };
        emit_void(
            &mut m,
            gx,
            Op::Return {
                value: Some(foreign_def),
            },
        );
        // Use g's value in f: as a plain operand…
        let v = add(&mut m, entry, foreign_def, p0);
        emit_void(&mut m, entry, Op::Return { value: Some(v) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == foreign_def),
            "ForeignValue(foreign block)",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: value {foreign_def} is not owned by this function",
                e.inst.unwrap()
            )
        );
    }

    /// Phi-entry variants of the dangling/foreign def walks.
    #[test]
    fn phi_entry_with_dangling_or_foreign_def_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        link(&mut m, b1, join);
        link(&mut m, b2, join);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        emit_void(&mut m, b1, Op::Branch { dest: join });
        emit_void(&mut m, b2, Op::Branch { dest: join });
        // b1's phi entry value: def is an out-of-arena inst.
        let dangling = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
        });
        // b2's phi entry value: def is an inst of another function.
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        let foreign = {
            let c = m.consts.push(Const::number(7.0));
            emit(&mut m, gx, Op::LoadConst(c))
        };
        emit_void(
            &mut m,
            gx,
            Op::Return {
                value: Some(foreign),
            },
        );
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b1,
                            kind: EdgeKind::Normal,
                        },
                        dangling,
                    ),
                    (
                        Edge {
                            from: b2,
                            kind: EdgeKind::Normal,
                        },
                        foreign,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == dangling),
            "ForeignValue(dangling def)",
        );
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == foreign),
            "ForeignValue(foreign def)",
        );
    }

    /// A phi entry keyed on an edge from another function's block: the
    /// structural PhiForeignEdge error fires and the dominance walk skips
    /// the foreign source. The entry's value is defined INSIDE the
    /// function, so the dominance walk reaches the foreign-source skip.
    #[test]
    fn phi_entry_from_foreign_block_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, b1, join);
        emit_void(&mut m, entry, Op::Branch { dest: b1 });
        let v1 = load_number(&mut m, b1, 1.0); // defined in-function
        emit_void(&mut m, b1, Op::Branch { dest: join });
        let g = add_func(&mut m);
        let gx = entry_of(&m, g);
        emit_void(&mut m, gx, Op::Return { value: None });
        let foreign_edge = Edge {
            from: gx,
            kind: EdgeKind::Normal,
        };
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![(foreign_edge, v1)],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::PhiForeignEdge { edge } if *edge == foreign_edge),
            "PhiForeignEdge",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {join} {:?}: phi entry edge {:?} is not a predecessor edge of the block",
                e.inst.unwrap(),
                foreign_edge
            )
        );
    }

    /// A phi entry carrying the exception param on an edge whose source is
    /// reachable but OUTSIDE the handler's exceptional downstream.
    #[test]
    fn exception_param_phi_out_of_scope_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        let n2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, t);
        link(&mut m, entry, n2);
        link(&mut m, n2, join);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: t,
                false_dest: n2,
            },
        );
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Return { value: None });
        emit_void(&mut m, n2, Op::Branch { dest: join });
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![(
                    Edge {
                        from: n2,
                        kind: EdgeKind::Normal,
                    },
                    exc,
                )],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::ExceptionParamPhiOutOfScope { pred, value, handler }
                        if *pred == n2 && *value == exc && *handler == h
                )
            },
            "ExceptionParamPhiOutOfScope",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {join} {:?}: phi entry from {n2} uses exception value {exc} delivered at handler {h} (N45)",
                e.inst.unwrap()
            )
        );
    }

    #[test]
    fn use_before_def_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let v = add(&mut m, entry, p0, p0); // pos 0: defines v
        let w = add(&mut m, entry, v, p0); // pos 1: uses v (once)
        emit_void(&mut m, entry, Op::Return { value: Some(w) });
        // Swap the two adds: the use now precedes its def within the block.
        m.block_mut(entry).unwrap().insts.swap(0, 1);
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::UseBeforeDef { value } if *value == v),
            "UseBeforeDef",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: uses {v} before its definition in the same block",
                e.inst.unwrap()
            )
        );
    }

    /// An Exceptional pred edge whose source has no try region dispatching
    /// to the block is an error.
    #[test]
    fn exceptional_pred_without_region_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: t });
        link(&mut m, entry, t);
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Return { value: None });
        link_exc(&mut m, t, h); // exceptional edge with NO try region
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ExceptionalPredWithoutRegion(b) if *b == t),
            "ExceptionalPredWithoutRegion",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {h}: exceptional predecessor {t} has no try region dispatching to this handler"
            )
        );
    }

    /// A terminator targeting an in-function block that does not list the
    /// edge in its predecessors: CFG edge symmetry error.
    #[test]
    fn successor_missing_pred_is_error() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let b2 = add_block(&mut m, f);
        let insts = &mut m.block_mut(entry).unwrap().insts;
        insts.clear();
        emit_void(&mut m, entry, Op::Branch { dest: b2 });
        // No link(entry, b2): b2.preds misses the edge.
        emit_void(&mut m, b2, Op::Return { value: None });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::SuccessorMissingPred(b) if *b == b2),
            "SuccessorMissingPred",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: successor {b2} is missing this block from its predecessors",
                e.inst.unwrap()
            )
        );
    }

    /// Ownership of const-defined values: in-pool is owned (no error), an
    /// out-of-pool ConstId is foreign.
    #[test]
    fn const_defined_value_ownership_is_checked() {
        let (mut m, f) = minimal_func_module();
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let c = m.consts.push(Const::number(1.0));
        // A value defined as Const(in-pool): owned — no error.
        let owned = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Const(c),
            ty: Ty::Any,
        });
        // A value defined as Const(out-of-pool): foreign.
        let bogus = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Const(ConstId::new(999)),
            ty: Ty::Any,
        });
        let v = add(&mut m, entry, owned, p0);
        let w = add(&mut m, entry, bogus, v);
        emit_void(&mut m, entry, Op::Return { value: Some(w) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == bogus),
            "ForeignValue(const)",
        );
        assert!(
            !r.errors
                .iter()
                .any(|e| matches!(e.kind, VerifyErrorKind::ForeignValue(v) if v == owned)),
            "the in-pool const-defined value must be owned: {:?}",
            r.errors
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {entry} {:?}: value {bogus} is not owned by this function",
                e.inst.unwrap()
            )
        );
    }

    /// The N38 handler scan skips a handler instruction that is out of the
    /// inst arena (the structural scan reports it instead).
    #[test]
    fn handler_with_out_of_arena_inst_skips_n38_scan() {
        let (mut m, f) = minimal_func_module();
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        emit_void(&mut m, t, Op::Return { value: None });
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);
        // The handler's instruction list dangles.
        let bogus = InstId::new(999);
        m.block_mut(h).unwrap().insts.push(bogus);
        emit_void(&mut m, h, Op::Return { value: None });
        let r = verify_func(&m, f);
        assert!(
            has_error(
                &r,
                |k| matches!(k, VerifyErrorKind::InstOutOfArena(id) if *id == bogus)
            ),
            "expected InstOutOfArena, got: {:?}",
            r.errors
        );
        assert!(
            r.warnings.is_empty(),
            "the dangling handler inst must not reach the N38 scan: {:?}",
            r.warnings
        );
    }

    /// Two uses of the same handler's exception param hit the region cache
    /// (the second `exc_region` call returns the cached set).
    #[test]
    fn exception_param_used_twice_caches_region() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        link(&mut m, entry, t);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);
        emit_void(&mut m, entry, Op::Branch { dest: t });
        emit_void(&mut m, t, Op::Return { value: None });
        let one = load_number(&mut m, h, 1.0);
        let w1 = add(&mut m, h, exc, one); // first use of exc
        let w2 = add(&mut m, h, exc, w1); // second use — region cache hit
        emit_void(&mut m, h, Op::Return { value: Some(w2) });
        let r = verify_func(&m, f);
        assert!(r.is_ok(), "two in-scope uses must pass: {:?}", r.errors);
    }

    /// The exception param is valid in the handler's exceptional-reachable
    /// DOWNSTREAM (the region BFS walks successors).
    #[test]
    fn exception_param_in_handler_downstream_is_valid() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        let down = add_block(&mut m, f);
        link(&mut m, entry, t);
        link(&mut m, h, down);
        let exc = add_exception_param(&mut m, h);
        add_try(&mut m, f, vec![t], h, exc);
        emit_void(&mut m, entry, Op::Branch { dest: t });
        emit_void(&mut m, t, Op::Return { value: None });
        emit_void(&mut m, h, Op::Branch { dest: down });
        let one = load_number(&mut m, down, 1.0);
        let w = add(&mut m, down, exc, one); // used in the handler's downstream
        emit_void(&mut m, down, Op::Return { value: Some(w) });
        let r = verify_func(&m, f);
        assert!(
            r.is_ok(),
            "downstream-of-handler use must be in scope: {:?}",
            r.errors
        );
    }

    /// Phi entries carrying entry-defined values (params, constants) are
    /// exempt from dominance by construction.
    #[test]
    fn phi_with_param_entries_passes() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        link(&mut m, b1, join);
        link(&mut m, b2, join);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        emit_void(&mut m, b1, Op::Branch { dest: join });
        emit_void(&mut m, b2, Op::Branch { dest: join });
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b1,
                            kind: EdgeKind::Normal,
                        },
                        p0, // entry-defined: exempt
                    ),
                    (
                        Edge {
                            from: b2,
                            kind: EdgeKind::Normal,
                        },
                        p0,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        assert!(r.is_ok(), "param phi entries must pass: {:?}", r.errors);
    }

    /// A phi entry whose value is defined in a block that does NOT dominate
    /// the entry's source edge is an N45 error.
    #[test]
    fn phi_use_not_dominated_is_error() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p0 = add_param(&mut m, f, 0);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        link(&mut m, entry, b1);
        link(&mut m, entry, b2);
        link(&mut m, b1, join);
        link(&mut m, b2, join);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond: p0,
                true_dest: b1,
                false_dest: b2,
            },
        );
        let v1 = load_number(&mut m, b1, 1.0); // defined in b1
        emit_void(&mut m, b1, Op::Branch { dest: join });
        emit_void(&mut m, b2, Op::Branch { dest: join });
        // The b2 edge entry uses b1's value — b1 does not dominate b2.
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: b1,
                            kind: EdgeKind::Normal,
                        },
                        v1,
                    ),
                    (
                        Edge {
                            from: b2,
                            kind: EdgeKind::Normal,
                        },
                        v1,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });
        let r = verify_func(&m, f);
        let e = expect_error(
            &r,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::PhiUseNotDominated { pred, value, def_block }
                        if *pred == b2 && *value == v1 && *def_block == b1
                )
            },
            "PhiUseNotDominated",
        );
        assert_eq!(
            format!("{e}"),
            format!(
                "verify error in FuncId(0) {join} {:?}: phi entry from {b2} uses {v1} whose definition in {b1} does not dominate the predecessor (over Normal edges)",
                e.inst.unwrap()
            )
        );
    }

    // ── Module-level reference integrity ─────────────────────────────

    #[test]
    fn class_super_and_interface_out_of_range_are_errors() {
        let (mut m, _f) = minimal_func_module();
        let bogus_super = ClassId::new(99);
        let bogus_iface = ClassId::new(98);
        m.classes[0].super_class = Some(bogus_super);
        m.classes[0].interfaces.push(bogus_iface);
        let r = verify_module(&m);
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_super),
            "ClassOutOfRange(super)",
        );
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_iface),
            "ClassOutOfRange(interface)",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error: class {bogus_iface} is outside the class table")
        );
    }

    #[test]
    fn class_method_out_of_range_is_error() {
        let (mut m, _f) = minimal_func_module();
        let bogus = FuncId::new(99);
        m.classes[0].methods.push(bogus);
        let r = verify_module(&m);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus),
            "FuncOutOfRange(class method)",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error: function {bogus} is outside the function table")
        );
    }

    #[test]
    fn func_class_out_of_range_is_error() {
        let (mut m, _f) = minimal_func_module();
        let name = m.sym.intern("orphan");
        let bogus_class = ClassId::new(99);
        m.functions.push(FunctionData {
            class_id: bogus_class,
            is_external: true, // isolate from MissingBody
            ..FunctionData::new(ClassId::new(0), name, FunctionKind::Function)
        });
        let r = verify_module(&m);
        let e = expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::ClassOutOfRange(c) if *c == bogus_class),
            "ClassOutOfRange(func.class_id)",
        );
        assert_eq!(
            format!("{e}"),
            format!("verify error: class {bogus_class} is outside the class table")
        );
    }

    /// Const-pool MethodRef payloads are checked, including nested inside
    /// ObjectLiteral and ArrayLiteral trees (which also exercises the two
    /// walks the corpus never lifts).
    #[test]
    fn const_method_ref_out_of_range_is_error() {
        let (mut m, _f) = minimal_func_module();
        let bogus_direct = FuncId::new(77);
        let bogus_nested = FuncId::new(78);
        let bogus_in_array = FuncId::new(79);
        m.consts.push(Const::method_ref(bogus_direct));
        let key = m.sym.intern("k");
        let k_cid = m.consts.push(Const::String(key));
        let nested_cid = m.consts.push(Const::method_ref(bogus_nested));
        m.consts.push(Const::ObjectLiteral {
            keys: vec![k_cid],
            values: vec![nested_cid],
        });
        let null_cid = m.consts.push(Const::Null);
        let arr_m_cid = m.consts.push(Const::method_ref(bogus_in_array));
        m.consts
            .push(Const::ArrayLiteral(vec![null_cid, arr_m_cid]));
        let r = verify_module(&m);
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_direct),
            "FuncOutOfRange(direct const)",
        );
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_nested),
            "FuncOutOfRange(nested const)",
        );
        expect_error(
            &r,
            |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus_in_array),
            "FuncOutOfRange(array const)",
        );
    }

    /// Valid shapes the corpus never lifts: a class with a super class and
    /// interfaces verifies clean.
    #[test]
    fn valid_super_class_and_interfaces_pass() {
        let (mut m, _f) = minimal_func_module();
        m.classes[0].super_class = Some(ClassId::new(0)); // self
        m.classes[0].interfaces.push(ClassId::new(0));
        let r = verify_module(&m);
        assert!(
            r.is_ok(),
            "valid super/interfaces must pass: {:?}",
            r.errors
        );
    }

    // ── Display + source() across all location combinations ─────────

    #[test]
    fn error_and_warning_display_cover_all_location_combos() {
        let kind = || VerifyErrorKind::MissingTerminator;
        let combos = [
            (
                None,
                None,
                None,
                "verify error: block does not end with a terminator",
            ),
            (
                Some(FuncId::new(1)),
                None,
                None,
                "verify error in FuncId(1): block does not end with a terminator",
            ),
            (
                Some(FuncId::new(1)),
                Some(BlockId::new(2)),
                None,
                "verify error in FuncId(1) BlockId(2): block does not end with a terminator",
            ),
            (
                Some(FuncId::new(1)),
                Some(BlockId::new(2)),
                Some(InstId::new(3)),
                "verify error in FuncId(1) BlockId(2) InstId(3): block does not end with a terminator",
            ),
        ];
        for (func, block, inst, want) in combos {
            let e = VerifyError {
                func,
                block,
                inst,
                kind: kind(),
            };
            assert_eq!(format!("{e}"), want);
            assert_eq!(
                format!("{}", std::error::Error::source(&e).unwrap()),
                "block does not end with a terminator"
            );
        }

        let w_combos = [
            (
                None,
                None,
                None,
                "verify warning: handler phi joins 2 distinct values across exceptional edges — imprecise join; passes must NOT constant-fold it (N38)",
            ),
            (
                Some(FuncId::new(1)),
                Some(BlockId::new(4)),
                Some(InstId::new(5)),
                "verify warning in FuncId(1) BlockId(4) InstId(5): handler phi joins 2 distinct values across exceptional edges — imprecise join; passes must NOT constant-fold it (N38)",
            ),
        ];
        for (func, block, inst, want) in w_combos {
            let w = VerifyWarning {
                func,
                block,
                inst,
                kind: VerifyWarningKind::HandlerPhiImpreciseJoin {
                    handler: BlockId::new(4),
                    count: 2,
                },
            };
            assert_eq!(format!("{w}"), want);
            assert!(std::error::Error::source(&w).is_some());
        }
    }

    #[test]
    fn readme_quick_start_module_verifies_clean() {
        let mut module = Module::new();
        let desc = module.sym.intern("L_GLOBAL;");
        module.classes.push(ClassData::new(desc, desc));

        let fname = module.sym.intern("add");
        let entry = BlockId::new(0);
        module.blocks.push(Block::default());

        let mut func = FunctionData::new(ClassId::new(0), fname, FunctionKind::Function);
        func.blocks.push(entry);
        for idx in 0..5u16 {
            let vid = ValueId::new(module.values.len() as u32);
            module.values.push(Value {
                def: ValueDef::Param(idx),
                ty: Ty::Any,
            });
            func.params.push(vid);
        }
        let (a, b) = (func.params[3], func.params[4]);
        module.functions.push(func);
        module.classes[0].methods.push(FuncId::new(0));

        let sum_inst = InstId::new(0);
        let sum_val = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(sum_inst),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::BinaryOp {
                op: BinOp::Add,
                left: a,
                right: b,
            },
            result: Some(sum_val),
            block: entry,
            loc: None,
        });
        let ret_inst = InstId::new(1);
        module.insts.push(Inst {
            op: Op::Return {
                value: Some(sum_val),
            },
            result: None,
            block: entry,
            loc: None,
        });
        module.blocks[entry.index()]
            .insts
            .extend([sum_inst, ret_inst]);

        assert!(verify_module(&module).is_ok());
    }

    #[test]
    fn detached_inst_value_class_methods_bijection_debug_and_const_shapes_are_checked() {
        use crate::function::{ColumnEntry, DebugData, LineEntry, LocalName, LocalScope};
        use crate::module::Annotation;

        // 1. Detached `ValueDef::Inst` (instruction in arena with `block = entry`,
        //    but unlinked from `entry.insts`) MUST be rejected!
        let (mut m1, f1) = minimal_func_module();
        let e1 = entry_of(&m1, f1);
        let c1 = m1.consts.push(Const::number(42.0));
        let detached_iid = InstId::new(m1.insts.len() as u32);
        let detached_val = ValueId::new(m1.values.len() as u32);
        m1.values.push(Value {
            def: ValueDef::Inst(detached_iid),
            ty: Ty::Any,
        });
        m1.insts.push(Inst {
            op: Op::LoadConst(c1),
            result: Some(detached_val),
            block: e1,
            loc: None,
        });
        m1.block_mut(e1).unwrap().insts.clear();
        emit_void(
            &mut m1,
            e1,
            Op::Return {
                value: Some(detached_val),
            },
        );
        let r1 = verify_func(&m1, f1);
        expect_error(
            &r1,
            |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == detached_val),
            "ForeignValue(detached inst)",
        );

        // 2. ClassData::methods <-> FunctionData::class_id bijection, AnnValue::Field,
        //    ExternalFunctionHasBody, DebugData InstIds, and Const payload shapes.
        let (mut m2, f2) = minimal_func_module();
        let e2 = entry_of(&m2, f2);
        let sym = m2.sym.intern("x");
        m2.classes.push(ClassData::new(sym, sym)); // ClassId(1)

        // Duplicate method + owner mismatch (`f2` has `class_id == ClassId(0)`, also listed in `ClassId(1)`).
        m2.classes[1].methods.push(f2);

        // Unlisted method (`f_unlisted` has `class_id == ClassId(1)`, not in `classes[1].methods`)
        // AND is external with non-empty blocks (`ExternalFunctionHasBody`).
        let f_unlisted = FuncId::new(m2.functions.len() as u32);
        let b_ext = BlockId::new(m2.blocks.len() as u32);
        m2.blocks.push(Block::default());
        emit_void(&mut m2, b_ext, Op::Return { value: None });
        let mut ext_fd = FunctionData::new(ClassId::new(1), sym, FunctionKind::Function);
        ext_fd.is_external = true;
        ext_fd.blocks.push(b_ext);
        m2.functions.push(ext_fd);

        // AnnValue::Field out of range on `ClassId(0)` (`0` fields).
        m2.classes[0].annotations.push(Annotation {
            class: ClassId::new(0),
            elements: vec![(sym, AnnValue::Field(ClassId::new(0), FieldId::new(3)))],
        });

        // DebugData referencing an instruction of `f_unlisted` (foreign to `f2`) + out-of-arena InstId.
        let foreign_iid = m2.block(b_ext).unwrap().insts[0];
        m2.func_mut(f2).unwrap().debug = Some(DebugData {
            line_table: vec![LineEntry {
                inst: foreign_iid,
                line: 1,
            }],
            column_table: vec![ColumnEntry {
                inst: InstId::new(9999),
                column: 1,
            }],
            local_names: vec![LocalName {
                name: sym,
                ty: None,
                scope: Some(LocalScope {
                    start: foreign_iid,
                    end: foreign_iid,
                }),
            }],
            ..DebugData::default()
        });

        // InvalidConstShape: LiteralBufferRef pointing to scalar + AllocObject pointing to scalar + LoadConst of ArrayLiteral.
        let c_scalar = m2.consts.push(Const::Null);
        let c_bad_bref = m2.consts.push(Const::LiteralBufferRef(c_scalar));
        let c_arr = m2.consts.push_array(vec![c_scalar]);
        m2.block_mut(e2).unwrap().insts.clear();
        let _ = emit(&mut m2, e2, Op::AllocObject { shape: c_scalar });
        let _ = emit(&mut m2, e2, Op::LoadConst(c_arr));
        emit_void(&mut m2, e2, Op::Return { value: None });

        let r2 = verify_module(&m2);
        expect_error(
            &r2,
            |k| matches!(k, VerifyErrorKind::DuplicateClassMethod(id) if *id == f2),
            "DuplicateClassMethod",
        );
        expect_error(
            &r2,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::ClassMethodOwnerMismatch {
                        class,
                        func,
                        actual_class,
                    } if *class == ClassId::new(1) && *func == f2 && *actual_class == ClassId::new(0)
                )
            },
            "ClassMethodOwnerMismatch",
        );
        expect_error(
            &r2,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::UnlistedClassMethod { class, func }
                        if *class == ClassId::new(1) && *func == f_unlisted
                )
            },
            "UnlistedClassMethod",
        );
        expect_error(
            &r2,
            |k| matches!(k, VerifyErrorKind::ExternalFunctionHasBody),
            "ExternalFunctionHasBody",
        );
        expect_error(
            &r2,
            |k| {
                matches!(
                    k,
                    VerifyErrorKind::FieldOutOfRange { class, field }
                        if *class == ClassId::new(0) && *field == FieldId::new(3)
                )
            },
            "FieldOutOfRange",
        );
        assert!(has_error(&r2, |k| {
            matches!(k, VerifyErrorKind::DebugInstNotInFunc(id) if *id == foreign_iid)
        }));
        assert!(has_error(&r2, |k| {
            matches!(k, VerifyErrorKind::InstOutOfArena(id) if *id == InstId::new(9999))
        }));
        expect_error(
            &r2,
            |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_bad_bref),
            "InvalidConstShape(LiteralBufferRef)",
        );
        expect_error(
            &r2,
            |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_scalar),
            "InvalidConstShape(AllocObject)",
        );
        expect_error(
            &r2,
            |k| matches!(k, VerifyErrorKind::InvalidConstShape { const_id, .. } if *const_id == c_arr),
            "InvalidConstShape(LoadConst)",
        );
    }
}
