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
mod tests;
