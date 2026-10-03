//! Verifier skeleton (design/ir-v0.2.md §6.3: the verifier is a
//! first-class contract, not a debug-build afterthought).
//!
//! Checks, per function:
//!
//! - **SSA dominance (N45 port)**: every use is dominated by its def over
//!   **Normal** edges. Entry-defined values (params, entry-block
//!   instruction results, constants) dominate everything.
//!   `ExceptionParam` values are valid in their handler and its
//!   exceptional-reachable downstream. Phi entries are uses on the
//!   incoming edge, checked against the predecessor. Blocks unreachable
//!   over the full edge graph (dead code) are exempt — they legitimately
//!   carry junk and CFG simplification removes them; so are blocks with
//!   no Normal-edge path from entry (catch handlers: exception dispatch
//!   is not Normal-edge dominance, exactly as in v0.1's N45 model).
//! - **N27**: a phi on a *reachable* block with no predecessors is an
//!   error (no incoming edge can carry it a value).
//! - **Terminators**: exactly one per block, in last position.
//! - **Arity**: fixed-arity ops match the taxonomy table
//!   ([`Op::arity`]); a phi's entry count equals the block's predecessor
//!   count.
//! - **N38 (warning, not error)**: a handler phi joining distinct values
//!   across exceptional edges is an imprecise join — passes must not
//!   constant-fold it.
//!
//! All findings are collected, never panicked on (library rule): errors
//! in [`VerifyError`], warnings in [`VerifyWarning`], both bundled in
//! [`VerifyReport`].

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::function::{Edge, EdgeKind, ValueDef};
use crate::id::{BlockId, ClassId, ConstId, FuncId, InstId, ValueId};
use crate::module::Module;
use crate::op::Op;

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
#[derive(Clone, Debug, Default)]
pub struct VerifyReport {
    /// Hard violations.
    pub errors: Vec<VerifyError>,
    /// Non-fatal findings.
    pub warnings: Vec<VerifyWarning>,
}

impl VerifyReport {
    /// Whether no errors were found (warnings do not affect this).
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Normal-edge successors of a block (terminator targets), restricted to
/// in-function blocks by the caller.
fn normal_succs(module: &Module, bb: BlockId) -> Vec<BlockId> {
    let Some(block) = module.block(bb) else {
        return Vec::new();
    };
    let Some(&last) = block.insts.last() else {
        return Vec::new();
    };
    let Some(inst) = module.inst(last) else {
        return Vec::new();
    };
    match &inst.op {
        Op::Branch { dest } => vec![*dest],
        Op::CondBranch {
            true_dest,
            false_dest,
            ..
        } => vec![*true_dest, *false_dest],
        _ => Vec::new(),
    }
}

/// Verify one function.
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

    // External functions carry no body (T6).
    if func.blocks.is_empty() {
        if !func.is_external {
            report
                .errors
                .push(err(None, None, VerifyErrorKind::MissingBody));
        }
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
    for &bb in &func.blocks {
        if module.block(bb).is_none() {
            report
                .errors
                .push(err(None, None, VerifyErrorKind::BlockOutOfArena(bb)));
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
            }
            // Exceptional edges are first-class (T5): the handler lists
            // every protected block as an Exceptional predecessor.
            if let Some(handler) = module.block(catch.handler) {
                for &p in &region.protected {
                    let edge = Edge {
                        from: p,
                        kind: EdgeKind::Exceptional,
                    };
                    if func_blocks.contains(&p) && !handler.preds.contains(&edge) {
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

    let dispatches_to = |from: BlockId, handler: BlockId| {
        func.try_regions.iter().any(|region| {
            region.protected.contains(&from) && region.catches.iter().any(|c| c.handler == handler)
        })
    };

    // ── Defined-value ownership scan ─────────────────────────────────
    let mut defined: HashMap<ValueId, ()> = HashMap::new();
    for (i, &val) in func.params.iter().enumerate() {
        match module.value(val).map(|v| v.def) {
            None => report
                .errors
                .push(err(None, None, VerifyErrorKind::ValueOutOfArena(val))),
            Some(def) if def != ValueDef::Param(i as u16) => report.errors.push(err(
                None,
                None,
                VerifyErrorKind::ParamDefMismatch {
                    value: val,
                    actual: def,
                },
            )),
            _ => {
                defined.insert(val, ());
            }
        }
    }
    for region in &func.try_regions {
        for catch in &region.catches {
            if module.value(catch.exception).is_some() {
                defined.insert(catch.exception, ());
            }
        }
    }
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
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
            if let Some(val) = inst.result {
                match module.value(val).map(|v| v.def) {
                    None => report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::ValueOutOfArena(val),
                    )),
                    Some(ValueDef::Inst(def)) if def == inst_id => {
                        defined.insert(val, ());
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

    // Entry predecessors: only a self-loop back-edge is legal.
    if let Some(entry_block) = module.block(entry)
        && entry_block.preds.iter().any(|e| e.from != entry)
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
        let mut seen_edges = HashSet::new();
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
                    if !normal_succs(module, edge.from).contains(&bb) {
                        report.errors.push(err(
                            Some(bb),
                            None,
                            VerifyErrorKind::PredDoesNotTarget(edge.from),
                        ));
                    }
                }
                EdgeKind::Exceptional => {
                    if !dispatches_to(edge.from, bb) {
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
            // Taxonomy arity drift guard (fixed-arity ops only; variadic
            // ops are constrained by their own rules, e.g. phi/preds).
            if let crate::op::Arity::Exact(n) = inst.op.arity() {
                let actual = inst.op.operands().len();
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
            // Successor edge symmetry.
            for succ in normal_succs(module, bb) {
                if !func_blocks.contains(&succ) {
                    report.errors.push(err(
                        Some(bb),
                        Some(last_id),
                        VerifyErrorKind::ForeignSuccessor(succ),
                    ));
                } else if module.block(succ).is_some_and(|s| {
                    !s.preds.contains(&Edge {
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

        // Phi arity and edge keys.
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
            let mut seen = HashSet::new();
            for (edge, _) in entries {
                if !block.preds.contains(edge) {
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

    // ── Use existence / ownership ────────────────────────────────────
    // (Dominance below reports its own errors; this pass reports only
    // arena-bounds and cross-function ownership.)
    let ownership = |val: ValueId| -> Option<VerifyErrorKind> {
        let v = module.value(val)?;
        let owned = match v.def {
            ValueDef::Param(i) => func.params.get(i as usize) == Some(&val),
            ValueDef::Inst(def) => match module.inst(def) {
                Some(inst) => inst.result == Some(val) && func_blocks.contains(&inst.block),
                None => false,
            },
            ValueDef::Const(c) => module.consts.get(c).is_some(),
            ValueDef::ExceptionParam(h) => func
                .try_regions
                .iter()
                .flat_map(|r| &r.catches)
                .any(|c| c.handler == h && c.exception == val),
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
            let uses: Vec<ValueId> = match &inst.op {
                Op::Phi { entries } => entries.iter().map(|(_, v)| *v).collect(),
                _ => inst.op.operands(),
            };
            for val in uses {
                if module.value(val).is_none() {
                    report.errors.push(err(
                        Some(bb),
                        Some(inst_id),
                        VerifyErrorKind::UndefinedValue(val),
                    ));
                } else if let Some(kind) = ownership(val) {
                    report.errors.push(err(Some(bb), Some(inst_id), kind));
                }
            }
        }
    }

    // ── Reachability (over ALL edges: Normal + first-class Exceptional)
    let all_succs = |bb: BlockId| -> Vec<BlockId> {
        let mut out = normal_succs(module, bb);
        for region in &func.try_regions {
            if region.protected.contains(&bb) {
                out.extend(region.catches.iter().map(|c| c.handler));
            }
        }
        out.retain(|s| func_blocks.contains(s));
        out
    };
    let reachable_all: HashSet<BlockId> = {
        let mut seen = HashSet::from([entry]);
        let mut queue = VecDeque::from([entry]);
        while let Some(bb) = queue.pop_front() {
            for succ in all_succs(bb) {
                if seen.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
        seen
    };

    // ── N27: reachable zero-pred phi ─────────────────────────────────
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        if !reachable_all.contains(&bb) || !block.preds.is_empty() {
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

    // ── N45 dominance over Normal edges ──────────────────────────────
    verify_dominance(module, func_id, &reachable_all, &all_succs, &mut report);

    // ── N38: handler-phi imprecise-join warnings ─────────────────────
    for region in &func.try_regions {
        for catch in &region.catches {
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

/// N45 use-def dominance over **Normal** edges, with the documented
/// exception-model exemptions (ported from v0.1 `verify.rs`):
///
/// 1. Uses in blocks unreachable over the full edge graph are exempt
///    (dead code carries junk; same standing as the N27 exemption).
/// 2. Uses in blocks with no Normal-edge path from the entry (catch
///    handlers and their Normal-only downstream) are exempt — exception
///    dispatch is not Normal-edge dominance.
/// 3. Phi entries are uses on the incoming edge: the value must be
///    available at the END of the edge's source block.
/// 4. Entry-defined values (params, constants, entry-block results)
///    dominate everything, handlers included.
/// 5. `ExceptionParam(h)` values are valid in `h` and its
///    exceptional-reachable downstream, and on phi edges leaving it.
fn verify_dominance(
    module: &Module,
    func_id: FuncId,
    reachable_all: &HashSet<BlockId>,
    all_succs: &dyn Fn(BlockId) -> Vec<BlockId>,
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

    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    let n = func.blocks.len();
    let entry_i = 0usize;

    // Normal-edge predecessors per block (in-function only).
    let mut npreds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let i = index[&bb];
        for edge in &block.preds {
            if edge.kind == EdgeKind::Normal
                && let Some(&p) = index.get(&edge.from)
            {
                npreds[i].push(p);
            }
        }
    }

    // N64: Normal-edge reachability from the entry, then drop unreachable
    // Normal predecessors. Without this, a REACHABLE block with any
    // unreachable Normal pred loses `entry` from its dominator set
    // (dom[unreachable] degenerates to a self-singleton that drags the
    // intersection down) and is wrongly treated as Normal-unreachable —
    // exempting its uses from the N45 checks below (weakening only, but
    // wrong). Unreachable blocks themselves stay exempt via the
    // `dom[i].contains(entry_i)` test either way.
    let mut nsuccs: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, preds) in npreds.iter().enumerate() {
        for &p in preds {
            nsuccs[p].push(i);
        }
    }
    let mut normal_reach = vec![false; n];
    normal_reach[entry_i] = true;
    let mut queue = VecDeque::from([entry_i]);
    while let Some(b) = queue.pop_front() {
        for &s in &nsuccs[b] {
            if !normal_reach[s] {
                normal_reach[s] = true;
                queue.push_back(s);
            }
        }
    }
    for preds in npreds.iter_mut() {
        preds.retain(|&p| normal_reach[p]);
    }

    // Iterative dominator sets over the Normal-edge CFG.
    let all: HashSet<usize> = (0..n).collect();
    let mut dom: Vec<HashSet<usize>> = vec![all; n];
    dom[entry_i] = HashSet::from([entry_i]);
    loop {
        let mut changed = false;
        for i in 0..n {
            if i == entry_i || !normal_reach[i] {
                continue;
            }
            let mut new: HashSet<usize> = if npreds[i].is_empty() {
                HashSet::new()
            } else {
                let mut acc = dom[npreds[i][0]].clone();
                for &p in &npreds[i][1..] {
                    acc = acc.intersection(&dom[p]).copied().collect();
                }
                acc
            };
            new.insert(i);
            if new != dom[i] {
                dom[i] = new;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // A block is Normal-reachable iff the entry dominates it.
    let normal_reachable = |i: usize| dom[i].contains(&entry_i);
    let dominates = |a: usize, b: usize| dom[b].contains(&a);

    // Exceptional-reachable downstream per handler (over ALL edges).
    let mut exc_region_cache: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();
    let mut exc_region = |handler: BlockId| -> HashSet<BlockId> {
        if let Some(r) = exc_region_cache.get(&handler) {
            return r.clone();
        }
        let mut seen = HashSet::from([handler]);
        let mut queue = VecDeque::from([handler]);
        while let Some(bb) = queue.pop_front() {
            for succ in all_succs(bb) {
                if seen.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
        exc_region_cache.insert(handler, seen.clone());
        seen
    };

    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let Some(&bi) = index.get(&bb) else { continue };

        // Instruction positions for the same-block def-before-use check.
        let position: HashMap<InstId, usize> = block
            .insts
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, i))
            .collect();

        for (pos, &inst_id) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };

            if let Op::Phi { entries } = &inst.op {
                // Exemption 3: phi entries are uses at the END of the
                // edge's source block.
                for (edge, val) in entries {
                    let Some(v) = module.value(*val) else {
                        continue;
                    };
                    match v.def {
                        // Exemption 4: entry-defined values dominate all.
                        ValueDef::Param(_) | ValueDef::Const(_) => {}
                        ValueDef::ExceptionParam(h) => {
                            let region = exc_region(h);
                            if !region.contains(&edge.from) && reachable_all.contains(&edge.from) {
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
                            let Some(def) = module.inst(def_inst) else {
                                continue;
                            };
                            let Some(&di) = index.get(&def.block) else {
                                continue;
                            };
                            let Some(&pi) = index.get(&edge.from) else {
                                continue;
                            };
                            // Def in the pred itself, entry-defined, or a
                            // dead/unreachable pred: OK/exempt.
                            if di == pi || di == entry_i || !normal_reachable(pi) {
                                continue;
                            }
                            if !dominates(di, pi) {
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

            for val in inst.op.operands() {
                let Some(v) = module.value(val) else { continue };
                match v.def {
                    ValueDef::Param(_) | ValueDef::Const(_) => {}
                    ValueDef::ExceptionParam(h) => {
                        if !exc_region(h).contains(&bb) && reachable_all.contains(&bb) {
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
                        let Some(def) = module.inst(def_inst) else {
                            continue;
                        };
                        if def.block == bb {
                            // Same block: the definition must precede the
                            // use (dominance is not just block-granular).
                            let def_pos = position.get(&def_inst).copied().unwrap_or(usize::MAX);
                            if def_pos >= pos {
                                report.errors.push(err(
                                    Some(bb),
                                    Some(inst_id),
                                    VerifyErrorKind::UseBeforeDef { value: val },
                                ));
                            }
                            continue;
                        }
                        let Some(&di) = index.get(&def.block) else {
                            continue;
                        };
                        // Exemption 4 (entry-defined) and exemptions 1-2
                        // (dead blocks; blocks with no Normal-edge path
                        // from entry — handlers).
                        if di == entry_i || !normal_reachable(bi) {
                            continue;
                        }
                        if !dominates(di, bi) {
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
            }
        }
    }
}

/// Verify the whole module: every function, plus module-level reference
/// integrity (class table, function table, const pool).
pub fn verify_module(module: &Module) -> VerifyReport {
    let mut report = VerifyReport::default();
    let module_err = |kind: VerifyErrorKind| VerifyError {
        func: None,
        block: None,
        inst: None,
        kind,
    };

    for class in &module.classes {
        let mut check_class = |c: ClassId| {
            if module.class(c).is_none() {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::ClassOutOfRange(c)));
            }
        };
        if let Some(s) = class.super_class {
            check_class(s);
        }
        for &i in &class.interfaces {
            check_class(i);
        }
        for &m in &class.methods {
            if module.func(m).is_none() {
                report
                    .errors
                    .push(module_err(VerifyErrorKind::FuncOutOfRange(m)));
            }
        }
    }

    for (fi, func) in module.functions.iter().enumerate() {
        if module.class(func.class_id).is_none() {
            report
                .errors
                .push(module_err(VerifyErrorKind::ClassOutOfRange(func.class_id)));
        }
        let fr = verify_func(module, FuncId::new(fi as u32));
        report.errors.extend(fr.errors);
        report.warnings.extend(fr.warnings);
    }

    // Const::MethodRef payloads reference the function table (nested
    // literal shapes are inline trees — walk them).
    fn check_const(module: &Module, c: &crate::consts::Const, out: &mut Vec<VerifyError>) {
        match c {
            crate::consts::Const::MethodRef(f) => {
                if module.func(*f).is_none() {
                    out.push(VerifyError {
                        func: None,
                        block: None,
                        inst: None,
                        kind: VerifyErrorKind::FuncOutOfRange(*f),
                    });
                }
            }
            crate::consts::Const::ArrayLiteral(items) => {
                for item in items {
                    check_const(module, item, out);
                }
            }
            crate::consts::Const::ObjectLiteral { keys, values } => {
                for item in keys.iter().chain(values.iter()) {
                    check_const(module, item, out);
                }
            }
            _ => {}
        }
    }
    for ci in 0..module.consts.len() {
        if let Some(c) = module.consts.get(ConstId::new(ci as u32)) {
            check_const(module, c, &mut report.errors);
        }
    }

    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::Const;
    use crate::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
    use crate::module::{ClassData, FunctionKind, Modifiers, SourceLang};
    use crate::op::BinOp;
    use crate::ty::Ty;

    // ── Test scaffolding (hand-built modules; no builder in P0) ──────

    fn mk_module() -> Module {
        let mut m = Module::new();
        let name = m.sym.intern("Ltest;");
        m.classes.push(ClassData {
            descriptor: name,
            name,
            modifiers: Modifiers::NONE,
            source_lang: SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
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
                type_idx: None,
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

    // ── W12: one negative per remaining dark error arm ───────────────
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
                type_idx: None,
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
                type_idx: None,
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
                type_idx: None,
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
                type_idx: None,
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
                type_idx: None,
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
        m.consts.push(Const::MethodRef(bogus_direct));
        let key = m.sym.intern("k");
        m.consts.push(Const::ObjectLiteral {
            keys: vec![Const::String(key)],
            values: vec![Const::MethodRef(bogus_nested)],
        });
        m.consts.push(Const::ArrayLiteral(vec![
            Const::Null,
            Const::MethodRef(bogus_in_array),
        ]));
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
}
