//! Stage B — control-flow structuring (design/decompile.md §4.2):
//! d-P1's region tree ([`self::regions::structure_regions`]) + Stage A's
//! per-block statements ([`crate::recover::RecoveredFunc`]) → a structured
//! JavaScript statement tree ([`SNode`]).
//!
//! ## Region → statement mapping
//!
//! - `Block` → the block's Stage-A statements (terminator consumed per
//!   the rules below).
//! - `Seq` → concatenation (with [`RegionNode::Alternates`] handling —
//!   see "Labeled alternates" below).
//! - `If` → `if (cond) { … } [else { … }]`; the head block's
//!   `CondBranch` supplies the condition; the head's trailing
//!   [`Stmt::PhiAssign`]s are partitioned onto the two out-edges.
//! - `Loop` → `while (cond)` when the header test is a clean two-way
//!   split (one edge stays in the body, the other is an unlabeled
//!   `Break` to the loop's structural continuation), `do { … } while
//!   (cond)` when a unique latch carries that test and is the body's
//!   last-emitted block, and `while (true)` + explicit
//!   `if (!c) break;` leaf rules otherwise (always correct; the clean
//!   forms are a presentation refinement).
//! - `Alternates`/`Labeled` → the JS labeled-statement model: nested
//!   `L$entry: { … }` blocks such that `break L$entry` from the
//!   preceding siblings lands at the arm's start, plus a `A$k: { … }`
//!   wrapper so mid-arm exits become `break A$k` (see
//!   `Ctx::emit_alternates_wrapped`).
//! - `Irreducible` → the state-variable dispatch escape hatch of
//!   design §4.2.4, with an honesty comment (expected count on the
//!   es2abc corpus: zero — the d-P1 gate proved it — but the path
//!   exists and is tested by crafted input).
//!
//! ## Phi placement rule (out-of-SSA, design §4.1)
//!
//! Stage A appends each phi's incoming-value assignment at the END of
//! the predecessor block's statement list. Structuring places them by
//! the edge they belong to:
//!
//! - **Straight-line / unconditional-branch blocks**: the assignments
//!   stay at the block end, before any `break`/`continue` trailer —
//!   correct because the block has exactly one out-edge.
//! - **Conditional heads (If, leaf `if (c) break/continue`)**: the
//!   assignments are partitioned by their `to` block onto the matching
//!   arm, emitted BEFORE the arm's content (and before the arm's
//!   `break`/`continue`).
//! - **Loop back edges**: a latch's assignments to the header's phis
//!   stay at the latch end — inside the loop body, before the
//!   `continue`/loop-back (and before the `do…while` condition, which
//!   is where es2abc's own evaluation order puts them).
//! - **Loop exit edges** (a clean `while (cond)` header's assignments
//!   to the exit target's phis): emitted immediately AFTER the loop —
//!   exactly-once on normal termination. If the loop body contains
//!   other `break` exits that bypass them, an honesty comment is added
//!   ([`StructStats::exit_phi_after_loop`] counts the placements).
//!
//! ## try/catch projection (design §4.2.5 + d-P1's [`self::regions::TryPlan`])
//!
//! Protected sets are laminar (d-P1 asserts it). Each block maps to its
//! innermost plan; each region node is `Uniform(plan)` or `Mixed`:
//!
//! - A node fully inside plan P (and not already emitting inside P) is
//!   wrapped in `try { … } catch (e) { … }`.
//! - A `Mixed` `Seq`/`If`/`Labeled` descends — children wrap
//!   themselves. Re-wrapping the same plan duplicates the catch body
//!   (counted in [`StructStats::try_splits`]; semantically sound — the
//!   same duplication es2abc itself uses for finally bodies).
//! - A `Mixed` `Loop` is the d-P1 `cuts_structured_region` case: the
//!   loop is emitted whole and the `try` lands INSIDE the loop body at
//!   the cut boundary, with an honesty comment on the plan
//!   ([`self::regions::TryPlan::cuts_structured_region`]).
//! - A `Mixed` node whose HEAD block is protected wraps whole (the
//!   condition evaluation is protected; arms may be over-protected —
//!   documented approximation, counted).
//!
//! Handlers are NOT in the region tree (d-P1's N45 design): each
//! handler body is structured as its own sub-CFG through a zero-copy
//! [`CfgSubgraph`] view ([`structure_subgraph`]), projecting out-of-set
//! Normal terminator edges without cloning or mutating [`Module`] (#29).
//! Nested try-in-handler regions recurse through their own subgraphs. The
//! `ExceptionParam` binding comes from Stage A's [`Stmt::CatchBind`]
//! marker at the handler head.

use std::collections::{BTreeSet, HashMap, HashSet};

use abcd_analysis::control::block_succs;
use abcd_ir::BlockId;
use abcd_ir::module::Module;
use abcd_ir::op::{CmpOp, UnOp};

use crate::expr::Expr;
use crate::recover::{RecoveredFunc, Stmt};

mod ast;
mod control;
mod frame;
pub mod regions;
mod try_cut;
mod try_project;
mod xarm;

pub use ast::{
    CatchClause, Leaf, SNode, StructStats, Structured, SwitchCase, is_terminal_node, negate,
};
pub(in crate::structure) use ast::{cond_avoids_main_decls, num_lit, subst_expr};
pub(in crate::structure) use frame::*;

use self::regions::{
    CfgSubgraph, EdgeClass, EscapeHatch, LoopKind, RegionId, RegionNode, RegionTree,
    structure_regions, structure_subgraph,
};

/// Structure one function (region tree + Stage-A statements → [`SNode`]s).
pub fn structure_func(module: &Module, rf: &RecoveredFunc) -> Structured {
    Ctx::new(module, rf).build()
}

/// A block's content split for emission: main statements (terminator
/// and trailing phi-assignments removed), the trailing
/// [`Stmt::PhiAssign`] run, and the terminator. Owned (cloned) so the
/// emitter can mutate its context afterwards.
pub(in crate::structure) struct BlockParts {
    pub(in crate::structure) main: Vec<Stmt>,
    pub(in crate::structure) phi: Vec<Stmt>,
    pub(in crate::structure) term: Term,
}

/// A block terminator relevant to structuring.
#[derive(Clone)]
pub(in crate::structure) enum Term {
    /// No control terminator (return/throw/end).
    None,
    /// Unconditional branch.
    Branch(BlockId),
    /// Conditional branch.
    Cond(Expr, BlockId, BlockId),
}

pub(in crate::structure) struct Ctx<'m> {
    pub(in crate::structure) module: &'m Module,
    pub(in crate::structure) rf: &'m RecoveredFunc,
    /// block → index into `rf.blocks`.
    pub(in crate::structure) bmap: HashMap<BlockId, usize>,
    pub(in crate::structure) stats: StructStats,
    pub(in crate::structure) frames: Vec<Frame>,
    /// handler entry → its own region tree (zero-copy subgraph view).
    pub(in crate::structure) shim_trees: HashMap<BlockId, RegionTree>,
    /// handler entry → the plans nested inside its sub-CFG.
    pub(in crate::structure) shim_plans: HashMap<BlockId, Vec<Plan>>,
    /// handler entry → its sub-CFG block set (d-P5: the handler's
    /// out-of-set Normal edges are its continuation targets — the
    /// join-hoist correctness condition).
    pub(in crate::structure) shim_sets: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Counter for `A$k` alternates-wrapper labels (deterministic).
    pub(in crate::structure) alt_counter: usize,
    /// Counter for `s$k` state-machine temporaries (deterministic).
    pub(in crate::structure) state_counter: usize,
    /// Cross-arm edges the tail-duplication fold repaired (the build()
    /// summary lists only the residual, unfolded ones).
    pub(in crate::structure) folded_xarms: BTreeSet<(BlockId, BlockId)>,
    /// Protected sets of the outer-finally wrappers currently being
    /// assembled ABOVE the emission point (the wrap_try_run chain,
    /// threads through `emit_handler` frames). Nested emissions must
    /// not re-wrap these plans: the wrappers physically enclose
    /// everything emitted while they are pending.
    pub(in crate::structure) pending_wraps: Vec<BTreeSet<BlockId>>,
    /// Rejoin entries of in-flight join hoists (`emit_cut_try`): while
    /// a hoisted try/catch's catch clauses are being emitted, the
    /// hoisted tail's entry block IS physically emitted right after the
    /// try/catch, so handler cut edges to it are safe fall-outs and the
    /// shim-tail duplication must stand down (N76 follow-up: golden
    /// s28/s29's join tail was duplicated into the catch body).
    pub(in crate::structure) hoist_rejoins: Vec<BlockId>,
    /// Verified fall-out targets (N76): while a `try/catch` whose
    /// physical continuation is KNOWN (the caller's `follow` resolves
    /// to a concrete next block) is being emitted, handler cut edges to
    /// that block are sound as plain catch-clause fall-outs — the
    /// run-fold may use them (`if/else` with the skip arm falling
    /// through) and the shim-tail duplication must stand down.
    pub(in crate::structure) verified_fallout: Vec<BlockId>,
    /// N77 de-absorption: blocks Normal-reachable from >= 2 handler
    /// entries (shared joins — see [`Ctx::build_deabsorb`]).
    pub(in crate::structure) shared_join: BTreeSet<BlockId>,
    /// Handler entry -> its UNIQUE prefix (reachable set minus the
    /// shared joins).
    pub(in crate::structure) uniq_sets: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Handler entry -> region tree over its unique prefix.
    pub(in crate::structure) uniq_trees: HashMap<BlockId, RegionTree>,
    /// Handler entry -> plans nested inside its unique prefix.
    pub(in crate::structure) uniq_plans: HashMap<BlockId, Vec<Plan>>,
    /// Whether de-absorption analysis populated unique handler subgraphs.
    pub(in crate::structure) has_deabsorb: bool,
    /// Join block set -> its structured tree (None = failed; memoized).
    pub(in crate::structure) join_memo: HashMap<BTreeSet<BlockId>, Option<(RegionTree, Vec<Plan>)>>,
    /// Join sets currently being emitted by enclosing de-absorbed
    /// towers (nested towers must not re-emit them).
    pub(in crate::structure) pending_joins: Vec<BTreeSet<BlockId>>,
    /// Protected sets whose try wrapper PHYSICALLY encloses the current
    /// emission point with no intervening catch (a de-absorbed tower's
    /// clause/join contexts): wraps of these plans are suppressed —
    /// the wrapper already exists above.
    pub(in crate::structure) suppress_wraps: Vec<BTreeSet<BlockId>>,
    /// Every handler entry of the function (region order, deduped).
    pub(in crate::structure) all_handlers: Vec<BlockId>,
    /// Handler entry -> its raw Normal-reachable set (pre-trim), for
    /// the de-absorption foreign-reach check.
    pub(in crate::structure) handler_approx: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Handler entry -> the root-frame plan indices it catches.
    pub(in crate::structure) handler_root_plans: HashMap<BlockId, Vec<usize>>,
    /// Shared-join blocks already emitted by a de-absorbed tower (a
    /// re-wrapped plan's tower must not emit them twice).
    pub(in crate::structure) emitted_joins: BTreeSet<BlockId>,
    /// Local parameters, catch bindings, and hoisted phi variables that
    /// cannot throw `ReferenceError` / TDZ on bare `Expr::Ident` read (`D1`/`D2`).
    pub(in crate::structure) safe_idents: HashSet<String>,
    /// Lazily-built SSA use-def chains for `clean_while_main_ok` (`D2`).
    pub(in crate::structure) chains: Option<abcd_analysis::dataflow::UseDefChains>,
    /// Monotonic token counter for deferred cross-arm/irreducible catch resolution.
    pub(in crate::structure) deferred_try_counter: usize,
    /// Pending `(tok, region, handlers, wraps)` jobs scheduled onto `run_emit_tasks`
    /// without synchronous `emit_handler` recursion.
    pub(in crate::structure) deferred_try_catches: Vec<(usize, usize, Vec<BlockId>, usize)>,
}

impl<'m> Ctx<'m> {
    pub(in crate::structure) fn new(module: &'m Module, rf: &'m RecoveredFunc) -> Self {
        let bmap = rf
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.block, i))
            .collect();
        let mut safe_idents: HashSet<String> = rf.params.iter().cloned().collect();
        safe_idents.insert("this".to_string());
        for blk in &rf.blocks {
            for stmt in &blk.stmts {
                match stmt {
                    Stmt::CatchBind { name } | Stmt::PhiDecl { name, .. } => {
                        safe_idents.insert(name.clone());
                    }
                    _ => {}
                }
            }
        }
        Ctx {
            module,
            rf,
            bmap,
            stats: StructStats::default(),
            frames: Vec::new(),
            shim_trees: HashMap::new(),
            shim_plans: HashMap::new(),
            shim_sets: HashMap::new(),
            alt_counter: 0,
            state_counter: 0,
            folded_xarms: BTreeSet::new(),
            pending_wraps: Vec::new(),
            hoist_rejoins: Vec::new(),
            verified_fallout: Vec::new(),
            shared_join: BTreeSet::new(),
            uniq_sets: HashMap::new(),
            uniq_trees: HashMap::new(),
            uniq_plans: HashMap::new(),
            has_deabsorb: false,
            join_memo: HashMap::new(),
            pending_joins: Vec::new(),
            suppress_wraps: Vec::new(),
            all_handlers: Vec::new(),
            handler_approx: HashMap::new(),
            handler_root_plans: HashMap::new(),
            emitted_joins: BTreeSet::new(),
            safe_idents,
            chains: None,
            deferred_try_counter: 0,
            deferred_try_catches: Vec::new(),
        }
    }

    pub(in crate::structure) fn f(&self) -> &Frame {
        self.frames.last().expect("a frame is always active")
    }

    pub(in crate::structure) fn f_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame is always active")
    }

    /// The active frame's handler-shim block set (the legacy absorbed
    /// set or the N77 unique prefix, per the frame kind).
    pub(in crate::structure) fn frame_shim_set(&self) -> Option<&BTreeSet<BlockId>> {
        let h = self.f().shim_of?;
        if self.f().shim_uniq {
            self.uniq_sets.get(&h)
        } else {
            self.shim_sets.get(&h)
        }
    }

    /// Whether plan `p`'s wrapper is being suppressed at the current
    /// emission point (its physical wrapper encloses the point with no
    /// intervening catch — [`Ctx::suppress_wraps`]).
    pub(in crate::structure) fn is_suppressed(&mut self, p: usize) -> bool {
        let protected = self.f().plans[p].protected.clone();
        self.suppress_wraps.contains(&protected)
    }

    pub(in crate::structure) fn build(mut self) -> Structured {
        let tree = structure_regions(self.module, self.rf.func);
        self.build_shims(&tree);
        let plans = tree
            .try_plans
            .iter()
            .map(|p| Plan {
                region: p.region,
                protected: p.protected.iter().copied().collect(),
                handlers: p.handlers.clone(),
                cuts: p.cuts_structured_region,
            })
            .collect();
        let mut body = Vec::new();
        self.frames.push(Frame::new(tree, plans));
        // Whole-function irreducibility: d-P1 detects irreducible cores
        // (cycles minus dominance back edges) and records the
        // unclaimable backward edges as CrossEdge escape hatches, but
        // the region tree still threads those blocks acyclically — the
        // back-flow is NOT representable as loops. Fall back to a
        // state-machine dispatch over the whole reachable function
        // (design §4.2.4; expected count on the es2abc corpus: zero —
        // the d-P1 gate proved it; the path exists for crafted input).
        let has_cross_edge = self
            .f()
            .tree
            .escape_hatches
            .iter()
            .any(|e| matches!(e, EscapeHatch::CrossEdge { .. }));
        if !self.f().tree.irreducible.is_empty() || has_cross_edge {
            self.emit_whole_function_state_machine(&mut body);
            if !self.deferred_try_catches.is_empty() {
                self.run_emit_tasks(StructTask::Noop, &mut body);
            }
        } else if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, &mut body);
        }
        // d-P1's cross-arm hint, d-P4's tail-duplication fold: edges
        // the fold repaired are gone from the output entirely (the
        // shared tail is duplicated inline at the drop site); only the
        // residual — edges whose tail the fold refused (budget, loop
        // header, mid-tail conditional, try-boundary crossing) — keeps
        // the summary honesty comment.
        let cross: Vec<String> = self
            .f()
            .tree
            .cross_arm_edges
            .iter()
            .filter(|e| !self.folded_xarms.contains(e))
            .map(|(a, b)| format!("B{}→B{}", a.index(), b.index()))
            .collect();
        if !cross.is_empty() {
            self.stats.cross_arm_notes += cross.len();
            body.insert(
                0,
                SNode::Honest(format!(
                    "cross-arm edges unfolded ({}); the tail-duplication fold bailed (budget/complexity) — the shared tail is NOT duplicated and the conditions are NOT merged; affected flow may read oddly",
                    cross.join(", ")
                )),
            );
        }
        self.frames.pop();
        Structured {
            body,
            stats: self.stats,
        }
    }
}

impl<'m> Ctx<'m> {
    // ── Block parts ──────────────────────────────────────────────────

    pub(in crate::structure) fn block_parts(&self, b: BlockId) -> BlockParts {
        let Some(&bi) = self.bmap.get(&b) else {
            return BlockParts {
                main: Vec::new(),
                phi: Vec::new(),
                term: Term::None,
            };
        };
        let stmts = self.rf.blocks[bi].stmts.as_slice();
        let mut end = stmts.len();
        while end > 0 && matches!(stmts[end - 1], Stmt::PhiAssign { .. }) {
            end -= 1;
        }
        let phi = stmts[end..].to_vec();
        let mut term = Term::None;
        let mut main_end = end;
        let mut extra_cond_expr: Option<Expr> = None;
        if end > 0 {
            match &stmts[end - 1] {
                Stmt::Branch { dest } => {
                    term = Term::Branch(*dest);
                    main_end = end - 1;
                }
                Stmt::CondBranch {
                    cond,
                    true_dest,
                    false_dest,
                } => {
                    if true_dest == false_dest {
                        if !expr_is_pure(cond, &self.safe_idents) {
                            extra_cond_expr = Some(cond.clone());
                        }
                        term = Term::Branch(*true_dest);
                    } else {
                        term = Term::Cond(cond.clone(), *true_dest, *false_dest);
                    }
                    main_end = end - 1;
                }
                _ => {}
            }
        }
        let mut main = stmts[..main_end].to_vec();
        if let Some(cond_e) = extra_cond_expr {
            main.push(Stmt::Expr(cond_e));
        }
        BlockParts { main, phi, term }
    }

    /// Partition a trailing phi-assign run by NORMAL edge destination.
    /// Exceptional-edge assigns ALWAYS go to `rest` so `push_main_phi`
    /// hoists them before any throwing statement in the block (`D1`).
    pub(in crate::structure) fn partition_phi(
        phi: &[Stmt],
        t: BlockId,
        f: BlockId,
    ) -> (Vec<Stmt>, Vec<Stmt>, Vec<Stmt>) {
        let mut pt = Vec::new();
        let mut pf = Vec::new();
        let mut rest = Vec::new();
        for s in phi {
            match s {
                Stmt::PhiAssign {
                    to,
                    exceptional: false,
                    ..
                } if *to == t => pt.push(s.clone()),
                Stmt::PhiAssign {
                    to,
                    exceptional: false,
                    ..
                } if *to == f => pf.push(s.clone()),
                _ => rest.push(s.clone()),
            }
        }
        (pt, pf, rest)
    }

    pub(in crate::structure) fn stmts_leaves(stmts: &[Stmt]) -> Vec<Leaf> {
        stmts
            .iter()
            .filter(|s| !matches!(s, Stmt::CatchBind { .. }))
            .map(|s| Leaf::Raw(s.clone()))
            .collect()
    }

    /// Push a block's main statements and trailing phi assigns, honoring the
    /// exception-dispatch rule (`D1` / `N38`): whenever `phi` carries any
    /// `PhiAssign { exceptional: true, .. }`, place those exceptional-edge
    /// flushes immediately after any `Declare` whose `name` they read and
    /// BEFORE the first statement in `main` that may throw at runtime (or at
    /// `main.len()`, before a conditional terminator, if `main` cannot throw).
    pub(in crate::structure) fn push_main_phi(
        &self,
        out: &mut Vec<SNode>,
        main: &[Stmt],
        phi: &[Stmt],
    ) {
        if phi.iter().any(|s| {
            matches!(
                s,
                Stmt::PhiAssign {
                    exceptional: true,
                    ..
                }
            )
        }) {
            let (xphi, rest): (Vec<Stmt>, Vec<Stmt>) = phi.iter().cloned().partition(|s| {
                matches!(
                    s,
                    Stmt::PhiAssign {
                        exceptional: true,
                        ..
                    }
                )
            });
            if let Some(first_throw) = main
                .iter()
                .position(|s| stmt_may_throw(s, &self.safe_idents))
            {
                let mut xphi_reads: HashSet<&str> = HashSet::new();
                for s in &xphi {
                    if let Stmt::PhiAssign { value, .. } = s {
                        collect_expr_ident_refs(value, &mut xphi_reads);
                    }
                }
                let dep_after = main
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, s)| match s {
                        Stmt::Declare { name, .. } if xphi_reads.contains(name.as_str()) => {
                            Some(idx + 1)
                        }
                        Stmt::PhiAssign { target, .. } if xphi_reads.contains(target.as_str()) => {
                            Some(idx + 1)
                        }
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                let insert_at = if dep_after == 0 {
                    first_throw
                } else if dep_after <= first_throw {
                    dep_after
                } else {
                    main[dep_after..]
                        .iter()
                        .position(|s| stmt_may_throw(s, &self.safe_idents))
                        .map_or(main.len(), |off| dep_after + off)
                };
                let mut combined = Self::stmts_leaves(&main[..insert_at]);
                combined.extend(Self::stmts_leaves(&xphi));
                combined.extend(Self::stmts_leaves(&main[insert_at..]));
                Self::push_stmts(out, combined);
                Self::push_stmts(out, Self::stmts_leaves(&rest));
                return;
            }
            Self::push_stmts(out, Self::stmts_leaves(main));
            Self::push_stmts(out, Self::stmts_leaves(&xphi));
            Self::push_stmts(out, Self::stmts_leaves(&rest));
            return;
        }
        Self::push_stmts(out, Self::stmts_leaves(main));
        Self::push_stmts(out, Self::stmts_leaves(phi));
    }

    pub(in crate::structure) fn push_stmts(out: &mut Vec<SNode>, leaves: Vec<Leaf>) {
        if !leaves.is_empty() {
            out.push(SNode::Stmts(leaves));
        }
    }

    // ── Edge actions ─────────────────────────────────────────────────

    /// The statement an out-edge `from → to` forces at a leaf
    /// terminator: a (labeled) break/continue, or nothing when the tree
    /// already encodes the flow.
    pub(in crate::structure) fn edge_action(
        &mut self,
        from: BlockId,
        to: BlockId,
    ) -> Option<SNode> {
        self.edge_action_with_follow(from, to, Follow::Unknown)
    }

    pub(in crate::structure) fn edge_action_with_follow(
        &mut self,
        from: BlockId,
        to: BlockId,
        follow: Follow,
    ) -> Option<SNode> {
        // 1. An arm entry of a pending Alternates or Ramsey forward merge:
        //    `break L$entry` unless natural fallthrough directly enters `to`.
        let matched_scope = self
            .f()
            .arm_scopes
            .iter()
            .rev()
            .find(|scope| scope.entry == to)
            .cloned();
        if let Some(scope) = matched_scope {
            if self.f().cross_arm.contains(&(from, to)) {
                self.folded_xarms.insert((from, to));
            }
            if scope.fallthrough_ok
                && follow == Follow::Entry(to)
                && self
                    .f()
                    .arm_bodies
                    .last()
                    .is_none_or(|ab| ab.slice.contains(&to))
            {
                return None;
            }
            return Some(SNode::Break {
                label: Some(scope.label),
            });
        }
        // 2. Inside an arm body, any edge leaving the slice exits to
        //    the alternates continuation: `break A$k`.
        if let Some(ab) = self.f().arm_bodies.last()
            && !ab.slice.contains(&to)
        {
            return Some(SNode::Break {
                label: Some(ab.done.clone()),
            });
        }
        // 3. The structural classification.
        match self.f().eclass.get(&(from, to)).copied() {
            Some(EdgeClass::Break { header, labeled }) => {
                let label = if labeled {
                    self.stats.labeled_exits += 1;
                    Some(format!("L${}", header.index()))
                } else {
                    None
                };
                Some(SNode::Break { label })
            }
            Some(EdgeClass::Continue { header, labeled }) => {
                let label = if labeled {
                    self.stats.labeled_exits += 1;
                    Some(format!("L${}", header.index()))
                } else {
                    None
                };
                Some(SNode::Continue { label })
            }
            _ => None,
        }
    }

    /// Whether an unlabeled `break` from `from → to` lands at the
    /// loop's structural continuation (the clean-loop-form
    /// precondition; also the defensive body-break audit).
    pub(in crate::structure) fn plain_break_ok(&self, to: BlockId, follow: Follow) -> bool {
        if self
            .f()
            .arm_scopes
            .iter()
            .any(|s| s.entry == to && !(s.fallthrough_ok && follow == Follow::Entry(to)))
        {
            return false;
        }
        if let Some(ab) = self.f().arm_bodies.last()
            && !ab.slice.contains(&to)
        {
            return false;
        }
        match follow {
            Follow::Tail => true,
            Follow::Entry(e) => e == to,
            Follow::Unknown => false,
        }
    }

    // ── Emission (iterative heap workstack) ─────────────────────────

    pub(in crate::structure) fn emit_node(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        self.run_emit_tasks(StructTask::EmitNode { id, active, follow }, out);
    }
}

pub(in crate::structure) struct TaskState {
    pub(in crate::structure) sinks: Vec<Vec<SNode>>,
    pub(in crate::structure) catch_lists: Vec<Vec<CatchClause>>,
    pub(in crate::structure) tasks: Vec<StructTask>,
}

pub(in crate::structure) enum CutTryInput {
    Node(RegionId),
    Slice(Vec<RegionId>),
}

pub(in crate::structure) enum LoopCutFallback {
    WrapWhole {
        id: RegionId,
        p: usize,
        follow: Follow,
    },
    PlainLoop {
        id: RegionId,
        header: BlockId,
        kind: LoopKind,
        body: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
}

pub(in crate::structure) enum StructTask {
    Noop,
    ResolveDeferredCrossArmTry {
        tok: usize,
        p_region: usize,
        wraps: usize,
    },
    FinishRamseyScope {
        label: String,
    },
    RamseyIfAfterSrc {
        head: BlockId,
        if_cond: Expr,
        src_dest: BlockId,
        src_r_is_none: bool,
        tgt_label: String,
        tgt_phi: Vec<Stmt>,
        tgt_r: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    RamseyIfAfterTgt {
        done_label: Option<String>,
    },
    EmitNode {
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    EmitContent {
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    EmitMixed {
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    SeqStep {
        children: Vec<RegionId>,
        idx: usize,
        active: Option<usize>,
        follow: Follow,
    },
    SeqAltPrefixStep {
        children: Vec<RegionId>,
        idx: usize,
        alt_idx: usize,
        popped: usize,
        active: Option<usize>,
        follow: Follow,
    },
    SeqAfterAlt {
        children: Vec<RegionId>,
        next_idx: usize,
        popped: usize,
        active: Option<usize>,
        follow: Follow,
    },
    FinishLabeled {
        label: String,
    },
    AlternatesStart {
        id: RegionId,
        prefix: Vec<SNode>,
        active: Option<usize>,
    },
    AlternatesStep {
        done: String,
        prefix: Vec<SNode>,
        active: Option<usize>,
        arms: Vec<(BlockId, RegionId)>,
        idx: usize,
        bodies: Vec<(String, Vec<SNode>)>,
    },
    EmitIf {
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    IfAfterThen {
        head: BlockId,
        cond: Expr,
        t: BlockId,
        f: BlockId,
        phi_f: Vec<Stmt>,
        act_t: Option<SNode>,
        no_act_t: bool,
        then_r_is_none: bool,
        duped_t: bool,
        else_r: Option<RegionId>,
        active: Option<usize>,
        follow: Follow,
    },
    IfAfterElse {
        cond: Expr,
        then: Vec<SNode>,
        f: BlockId,
        act_f: Option<SNode>,
        no_act_f: bool,
        else_r_is_none: bool,
        duped_f: bool,
    },
    EmitLoop {
        id: RegionId,
        header: BlockId,
        kind: LoopKind,
        body_r: RegionId,
        active: Option<usize>,
        follow: Follow,
    },
    FinishCleanWhile {
        label: Option<String>,
        while_cond: Expr,
        phi_exit: Vec<Stmt>,
    },
    FinishDoWhile {
        label: Option<String>,
        lp_main: Vec<Stmt>,
        latch_phi: Vec<Stmt>,
        while_cond: Expr,
        phi_exit: Vec<Leaf>,
    },
    FinishWhileTrue {
        label: Option<String>,
    },
    EmitHandler {
        h: BlockId,
        uniq: bool,
        extra_continue: bool,
    },
    FinishHandler {
        binding: Option<String>,
        extra_continue: bool,
    },
    EmitJoinLevel {
        head: BlockId,
        set: BTreeSet<BlockId>,
    },
    PopFrame,
    PushNodeToSink(SNode),
    TruncateSuppress(usize),
    WrapTryRun {
        ids: Vec<RegionId>,
        p: usize,
        prologues: Vec<try_project::TryPrologue>,
        follow: Follow,
    },
    DeabsorbAfterBody(Box<try_project::DeabsorbState>),
    DeabsorbStep {
        st: Box<try_project::DeabsorbState>,
        k: usize,
        prev_body: Vec<SNode>,
        prev_region: usize,
        suppress_mark: usize,
        vf_pop: usize,
    },
    DeabsorbChainAfterInner {
        st: Box<try_project::DeabsorbState>,
        k: usize,
        qregion: usize,
        qhandlers: Vec<BlockId>,
    },
    DeabsorbFinish {
        joins_mark: usize,
        follow_chain_len: usize,
        join_union: BTreeSet<BlockId>,
    },
    LegacyWrapAfterBody(Box<try_project::LegacyWrapState>),
    LegacyWrapAfterPCatches {
        st: Box<try_project::LegacyWrapState>,
        body: Vec<SNode>,
        suppress_mark: usize,
    },
    LegacyWrapAfterQCatches {
        st: Box<try_project::LegacyWrapState>,
        k: usize,
        node: SNode,
        qregion: usize,
        wraps: usize,
        qsuppress_mark: usize,
    },
    LegacyWrapFinishStep {
        st: Box<try_project::LegacyWrapState>,
        k: usize,
        qregion: usize,
        wraps: usize,
        qcatches: Vec<CatchClause>,
    },
    CutTryAfterSkel {
        region: usize,
        hoisted: Vec<RegionId>,
        handlers: Vec<BlockId>,
        active: Option<usize>,
        follow: Follow,
    },
    CutTryAfterCatches {
        region: usize,
        body: Vec<SNode>,
        rejoin_pushed: bool,
        hoisted: Vec<RegionId>,
        active: Option<usize>,
        follow: Follow,
    },
    LoopCutAfterSkel(Box<try_project::LoopCutState>),
    LoopCutAfterCatches0 {
        st: Box<try_project::LoopCutState>,
        skel: Vec<SNode>,
        pending_mark: usize,
        suppress_mark: usize,
    },
    LoopCutAfterPreTry {
        st: Box<try_project::LoopCutState>,
        node0: SNode,
        pending_mark: usize,
    },
    LoopCutAfterPrefix {
        st: Box<try_project::LoopCutState>,
        q1: usize,
        region1: usize,
        pending_mark: usize,
    },
    LoopCutAfterCatches1 {
        st: Box<try_project::LoopCutState>,
        region1: usize,
        p1_body: Vec<SNode>,
        pending_mark: usize,
    },
    LoopCutFinish {
        kept_main: Vec<Stmt>,
        while_cond: Expr,
    },
}

impl<'m> Ctx<'m> {
    pub(in crate::structure) fn run_emit_tasks(
        &mut self,
        initial: StructTask,
        out: &mut Vec<SNode>,
    ) {
        let mut ts = TaskState {
            sinks: vec![std::mem::take(out)],
            catch_lists: Vec::new(),
            tasks: vec![initial],
        };
        loop {
            if let Some((tok, p_region, handlers, wraps)) = self.deferred_try_catches.pop() {
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::ResolveDeferredCrossArmTry {
                    tok,
                    p_region,
                    wraps,
                });
                try_project::schedule_dedup_handlers(&handlers, false, false, &mut ts.tasks);
                continue;
            }
            let Some(task) = ts.tasks.pop() else {
                break;
            };
            match task {
                StructTask::Noop => {}
                StructTask::ResolveDeferredCrossArmTry {
                    tok,
                    p_region,
                    wraps,
                } => {
                    let catches = ts.catch_lists.pop().unwrap_or_default();
                    if catches.len() > 1 {
                        self.stats.multi_catch += 1;
                    }
                    let note = if wraps == 0 {
                        None
                    } else {
                        Some(format!(
                            "cross-arm tail duplication re-wraps try region {p_region} (wrapper #{wraps}; protectedness is an instruction property, so the duplicated code keeps its own try/catch)"
                        ))
                    };
                    let marker = deferred_try_marker(tok);
                    resolve_deferred_try_in_task_state(&mut ts, &marker, catches, note);
                }
                StructTask::FinishRamseyScope { label } => {
                    self.f_mut().arm_scopes.pop();
                    let inner = ts.sinks.pop().unwrap_or_default();
                    if let Some(sink) = ts.sinks.last_mut() {
                        if nodes_use_label(&inner, &label) {
                            self.stats.alternates += 1;
                            sink.push(SNode::Labeled { label, body: inner });
                        } else {
                            sink.extend(inner);
                        }
                    }
                }
                StructTask::RamseyIfAfterSrc {
                    head,
                    if_cond,
                    src_dest,
                    src_r_is_none,
                    tgt_label,
                    tgt_phi,
                    tgt_r,
                    active,
                    follow,
                } => {
                    let mut src_body = ts.sinks.pop().unwrap_or_default();
                    if src_r_is_none {
                        if let Some(act) =
                            self.edge_action_with_follow(head, src_dest, Follow::Unknown)
                        {
                            src_body.push(act);
                        } else if let Some((tail, _)) = self.shim_tail_dup(src_dest) {
                            src_body.extend(tail);
                        }
                    }
                    self.f_mut().arm_scopes.pop();
                    let src_falls_through = !src_body.last().is_some_and(is_terminal_node);
                    let done_label = if src_falls_through {
                        let d = format!("A${}", self.alt_counter);
                        self.alt_counter += 1;
                        src_body.push(SNode::Break {
                            label: Some(d.clone()),
                        });
                        Some(d)
                    } else {
                        None
                    };
                    let mut other_body = Vec::new();
                    Self::push_stmts(&mut other_body, Self::stmts_leaves(&tgt_phi));
                    self.stats.ifs += 1;
                    let if_node = SNode::If {
                        cond: if_cond,
                        then: src_body,
                        otherwise: other_body,
                    };
                    let first_item = if nodes_use_label(std::slice::from_ref(&if_node), &tgt_label)
                    {
                        self.stats.alternates += 1;
                        SNode::Labeled {
                            label: tgt_label,
                            body: vec![if_node],
                        }
                    } else {
                        if_node
                    };
                    ts.sinks.push(vec![first_item]);
                    ts.tasks.push(StructTask::RamseyIfAfterTgt { done_label });
                    ts.tasks.push(StructTask::EmitNode {
                        id: tgt_r,
                        active,
                        follow,
                    });
                }
                StructTask::RamseyIfAfterTgt { done_label } => {
                    let combined = ts.sinks.pop().unwrap_or_default();
                    if let Some(sink) = ts.sinks.last_mut() {
                        if let Some(done) = done_label {
                            sink.push(SNode::Labeled {
                                label: done,
                                body: combined,
                            });
                        } else {
                            sink.extend(combined);
                        }
                    }
                }
                StructTask::EmitNode { id, active, follow } => {
                    if let Some(cd) = self.f_mut().cut_defer.as_mut()
                        && cd.ids.remove(&id)
                    {
                        continue;
                    }
                    let cov = self.f_mut().cov(id);
                    match cov {
                        Cov::Uniform(p) if p == active => {
                            ts.tasks
                                .push(StructTask::EmitContent { id, active, follow });
                        }
                        Cov::Uniform(Some(p)) if self.is_suppressed(p) => {
                            ts.tasks.push(StructTask::EmitContent {
                                id,
                                active: Some(p),
                                follow,
                            });
                        }
                        Cov::Uniform(Some(p)) => {
                            ts.tasks.push(StructTask::WrapTryRun {
                                ids: vec![id],
                                p,
                                prologues: Vec::new(),
                                follow,
                            });
                        }
                        Cov::Uniform(None) => {
                            self.stats.try_splits += 1;
                            let region = active
                                .map(|a| self.f().plans[a].region)
                                .unwrap_or(usize::MAX);
                            if let Some(sink) = ts.sinks.last_mut() {
                                sink.push(SNode::Honest(format!(
                                    "try region {region}: statements inside the protected span are NOT protected (non-contiguous range) — emitted inside the try body regardless"
                                )));
                            }
                            ts.tasks
                                .push(StructTask::EmitContent { id, active, follow });
                        }
                        Cov::Mixed => {
                            ts.tasks.push(StructTask::EmitMixed { id, active, follow });
                        }
                    }
                }
                StructTask::EmitContent { id, active, follow } => {
                    let node = self.f().node(id).clone();
                    match node {
                        RegionNode::Block(b) => {
                            if !self.f_mut().skip_blocks.remove(&b)
                                && let Some(mut sink) = ts.sinks.pop()
                            {
                                self.emit_leaf(b, follow, &mut sink);
                                ts.sinks.push(sink);
                            }
                        }
                        RegionNode::Seq(children) => {
                            ts.tasks.push(StructTask::SeqStep {
                                children,
                                idx: 0,
                                active,
                                follow,
                            });
                        }
                        RegionNode::Alternates(_) => {
                            ts.tasks.push(StructTask::AlternatesStart {
                                id,
                                prefix: Vec::new(),
                                active,
                            });
                        }
                        RegionNode::Labeled { label, body } => {
                            ts.sinks.push(Vec::new());
                            ts.tasks.push(StructTask::FinishLabeled {
                                label: format!("L${}", label.index()),
                            });
                            ts.tasks.push(StructTask::EmitNode {
                                id: body,
                                active,
                                follow,
                            });
                        }
                        RegionNode::If { .. } => {
                            ts.tasks.push(StructTask::EmitIf { id, active, follow });
                        }
                        RegionNode::Loop { header, kind, body } => {
                            ts.tasks.push(StructTask::EmitLoop {
                                id,
                                header,
                                kind,
                                body_r: body,
                                active,
                                follow,
                            });
                        }
                        RegionNode::Irreducible { .. } => {
                            if let Some(mut sink) = ts.sinks.pop() {
                                self.emit_irreducible(id, active, &mut sink);
                                ts.sinks.push(sink);
                            }
                        }
                    }
                }
                StructTask::EmitMixed { id, active, follow } => {
                    self.step_emit_mixed(id, active, follow, &mut ts);
                }
                StructTask::SeqStep {
                    children,
                    mut idx,
                    active,
                    follow,
                } => {
                    self.step_seq(children, &mut idx, active, follow, &mut ts);
                }
                StructTask::SeqAltPrefixStep {
                    children,
                    mut idx,
                    alt_idx,
                    popped,
                    active,
                    follow,
                } => {
                    while idx < alt_idx {
                        let consumed = if let Some(mut sink) = ts.sinks.pop() {
                            let c = self.try_run_fold(&children, idx, active, follow, &mut sink);
                            ts.sinks.push(sink);
                            c
                        } else {
                            0
                        };
                        if consumed > 0 {
                            idx += consumed;
                        } else {
                            break;
                        }
                    }
                    if idx < alt_idx {
                        if let Some((off, m)) = self.find_ramsey_forward_merge(
                            &children[idx..alt_idx],
                            active,
                            Follow::Unknown,
                        ) {
                            let d_max = idx + off;
                            let label = format!("L${}", m.index());
                            self.f_mut().arm_scopes.push(ArmScope {
                                entry: m,
                                label: label.clone(),
                                fallthrough_ok: true,
                                ramsey: true,
                            });
                            ts.sinks.push(Vec::new());
                            ts.tasks.push(StructTask::SeqAltPrefixStep {
                                children: children.clone(),
                                idx: d_max,
                                alt_idx,
                                popped,
                                active,
                                follow,
                            });
                            ts.tasks.push(StructTask::FinishRamseyScope { label });
                            ts.tasks.push(StructTask::SeqStep {
                                children: children[idx..d_max].to_vec(),
                                idx: 0,
                                active,
                                follow: Follow::Entry(m),
                            });
                            continue;
                        }
                        let fl = if idx + 1 < alt_idx {
                            self.entry_of(children[idx + 1])
                        } else {
                            Follow::Unknown
                        };
                        let child = children[idx];
                        ts.tasks.push(StructTask::SeqAltPrefixStep {
                            children,
                            idx: idx + 1,
                            alt_idx,
                            popped,
                            active,
                            follow,
                        });
                        ts.tasks.push(StructTask::EmitNode {
                            id: child,
                            active,
                            follow: fl,
                        });
                    } else {
                        let prefix = ts.sinks.last_mut().map(std::mem::take).unwrap_or_default();
                        let alt_id = children[alt_idx];
                        ts.tasks.push(StructTask::SeqAfterAlt {
                            children,
                            next_idx: alt_idx + 1,
                            popped,
                            active,
                            follow,
                        });
                        ts.tasks.push(StructTask::AlternatesStart {
                            id: alt_id,
                            prefix,
                            active,
                        });
                    }
                }
                StructTask::SeqAfterAlt {
                    children,
                    next_idx,
                    popped,
                    active,
                    follow,
                } => {
                    for _ in 0..popped {
                        self.f_mut().arm_scopes.pop();
                    }
                    if next_idx < children.len() {
                        ts.tasks.push(StructTask::SeqStep {
                            children,
                            idx: next_idx,
                            active,
                            follow,
                        });
                    }
                }
                StructTask::FinishLabeled { label } => {
                    let inner = ts.sinks.pop().unwrap_or_default();
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(SNode::Labeled { label, body: inner });
                    }
                }
                StructTask::AlternatesStart { id, prefix, active } => {
                    let arms: Vec<(BlockId, RegionId)> = match self.f().node(id) {
                        RegionNode::Alternates(arms) => arms
                            .iter()
                            .filter_map(|&a| match self.f().node(a) {
                                RegionNode::Labeled { label, body } => Some((*label, *body)),
                                _ => None,
                            })
                            .collect(),
                        _ => Vec::new(),
                    };
                    if arms.is_empty() {
                        if let Some(sink) = ts.sinks.last_mut() {
                            sink.extend(prefix);
                            sink.push(SNode::Honest(
                                "malformed alternates node (no labeled arms) — content dropped"
                                    .to_string(),
                            ));
                        }
                        continue;
                    }
                    self.stats.alternates += 1;
                    let done = format!("A${}", self.alt_counter);
                    self.alt_counter += 1;
                    let body_r = arms[0].1;
                    let slice = self.f_mut().node_blocks(body_r);
                    self.f_mut().arm_bodies.push(ArmBody {
                        done: done.clone(),
                        slice,
                    });
                    ts.sinks.push(Vec::new());
                    ts.tasks.push(StructTask::AlternatesStep {
                        done,
                        prefix,
                        active,
                        arms,
                        idx: 1,
                        bodies: Vec::new(),
                    });
                    ts.tasks.push(StructTask::EmitNode {
                        id: body_r,
                        active,
                        follow: Follow::Tail,
                    });
                }
                StructTask::AlternatesStep {
                    done,
                    prefix,
                    active,
                    arms,
                    idx,
                    mut bodies,
                } => {
                    let finished = ts.sinks.pop().unwrap_or_default();
                    self.f_mut().arm_bodies.pop();
                    let prev_entry = arms[idx - 1].0;
                    bodies.push((format!("L${}", prev_entry.index()), finished));
                    if idx < arms.len() {
                        let body_r = arms[idx].1;
                        let slice = self.f_mut().node_blocks(body_r);
                        self.f_mut().arm_bodies.push(ArmBody {
                            done: done.clone(),
                            slice,
                        });
                        ts.sinks.push(Vec::new());
                        ts.tasks.push(StructTask::AlternatesStep {
                            done,
                            prefix,
                            active,
                            arms,
                            idx: idx + 1,
                            bodies,
                        });
                        ts.tasks.push(StructTask::EmitNode {
                            id: body_r,
                            active,
                            follow: Follow::Tail,
                        });
                    } else {
                        let mut iter = bodies.into_iter();
                        let Some((first_label, first_body)) = iter.next() else {
                            continue;
                        };
                        let rest: Vec<(String, Vec<SNode>)> = iter.collect();
                        let mut nodes = prefix;
                        for (label, body) in rest.into_iter().rev() {
                            let terminal = body.last().is_some_and(is_terminal_node);
                            let mut inner = vec![SNode::Labeled { label, body: nodes }];
                            inner.extend(body);
                            if !terminal {
                                inner.push(SNode::Break {
                                    label: Some(done.clone()),
                                });
                            }
                            nodes = inner;
                        }
                        let mut wrapper = vec![SNode::Labeled {
                            label: first_label,
                            body: nodes,
                        }];
                        wrapper.extend(first_body);
                        if let Some(sink) = ts.sinks.last_mut() {
                            sink.push(SNode::Labeled {
                                label: done,
                                body: wrapper,
                            });
                        }
                    }
                }
                StructTask::EmitIf { id, active, follow } => {
                    self.step_emit_if(id, active, follow, &mut ts);
                }
                StructTask::IfAfterThen {
                    head,
                    cond,
                    t,
                    f,
                    phi_f,
                    act_t,
                    no_act_t,
                    then_r_is_none,
                    duped_t,
                    else_r,
                    active,
                    follow,
                } => {
                    let mut then = ts.sinks.pop().unwrap_or_default();
                    if !then.last().is_some_and(is_terminal_node) {
                        then.extend(act_t);
                    }
                    if no_act_t
                        && then_r_is_none
                        && !duped_t
                        && let Some((tail, _)) = self.shim_tail_dup(t)
                    {
                        then.extend(tail);
                    }
                    let act_f = if else_r.is_none() {
                        self.edge_action_with_follow(head, f, follow)
                    } else {
                        self.edge_action(head, f)
                    };
                    let no_act_f = act_f.is_none();
                    let mut otherwise: Vec<SNode> = Vec::new();
                    Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                    let mut duped_f = false;
                    if act_f.is_none()
                        && self.f().cross_arm.contains(&(head, f))
                        && let Some(dup) = self.try_cross_arm_fold(head, f, follow)
                    {
                        otherwise.extend(dup);
                        duped_f = true;
                    }
                    ts.sinks.push(otherwise);
                    ts.tasks.push(StructTask::IfAfterElse {
                        cond,
                        then,
                        f,
                        act_f,
                        no_act_f,
                        else_r_is_none: else_r.is_none(),
                        duped_f,
                    });
                    if let Some(r) = else_r {
                        ts.tasks.push(StructTask::EmitNode {
                            id: r,
                            active,
                            follow,
                        });
                    }
                }
                StructTask::IfAfterElse {
                    cond,
                    then,
                    f,
                    act_f,
                    no_act_f,
                    else_r_is_none,
                    duped_f,
                } => {
                    let mut otherwise = ts.sinks.pop().unwrap_or_default();
                    if !otherwise.last().is_some_and(is_terminal_node) {
                        otherwise.extend(act_f);
                    }
                    if no_act_f
                        && else_r_is_none
                        && !duped_f
                        && let Some((tail, _)) = self.shim_tail_dup(f)
                    {
                        otherwise.extend(tail);
                    }
                    self.stats.ifs += 1;
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(SNode::If {
                            cond,
                            then,
                            otherwise,
                        });
                    }
                }
                StructTask::EmitLoop {
                    id,
                    header,
                    kind,
                    body_r,
                    active,
                    follow,
                } => {
                    self.step_emit_loop(id, header, kind, body_r, active, follow, &mut ts);
                }
                StructTask::FinishCleanWhile {
                    label,
                    while_cond,
                    phi_exit,
                } => {
                    let body = ts.sinks.pop().unwrap_or_default();
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(SNode::While {
                            label,
                            cond: Some(while_cond),
                            body,
                        });
                        if !phi_exit.is_empty() {
                            self.stats.exit_phi_after_loop += 1;
                            Self::push_stmts(sink, Self::stmts_leaves(&phi_exit));
                        }
                    }
                }
                StructTask::FinishDoWhile {
                    label,
                    lp_main,
                    latch_phi,
                    while_cond,
                    phi_exit,
                } => {
                    let mut body = ts.sinks.pop().unwrap_or_default();
                    self.push_main_phi(&mut body, &lp_main, &latch_phi);
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(SNode::DoWhile {
                            label,
                            body,
                            cond: while_cond,
                        });
                        if !phi_exit.is_empty() {
                            self.stats.exit_phi_after_loop += 1;
                            Self::push_stmts(sink, phi_exit);
                        }
                    }
                }
                StructTask::FinishWhileTrue { label } => {
                    let body = ts.sinks.pop().unwrap_or_default();
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(SNode::While {
                            label,
                            cond: None,
                            body,
                        });
                    }
                }
                StructTask::EmitHandler {
                    h,
                    uniq,
                    extra_continue,
                } => {
                    let binding = self
                        .bmap
                        .get(&h)
                        .and_then(|&bi| self.rf.blocks[bi].stmts.first())
                        .and_then(|s| match s {
                            Stmt::CatchBind { name } => Some(name.clone()),
                            _ => None,
                        });
                    let tree_opt = if uniq {
                        self.uniq_trees.get(&h).cloned()
                    } else {
                        self.shim_trees.get(&h).cloned()
                    };
                    let Some(tree) = tree_opt else {
                        let msg = if uniq {
                            format!(
                                "handler B{}: unique-prefix body unavailable (no shim)",
                                h.index()
                            )
                        } else {
                            format!(
                                "handler B{}: body unavailable (no shim — exotic entry shape)",
                                h.index()
                            )
                        };
                        let mut body = vec![SNode::Honest(msg)];
                        if extra_continue {
                            body.push(SNode::Continue { label: None });
                        }
                        if let Some(cl) = ts.catch_lists.last_mut() {
                            cl.push(CatchClause { binding, body });
                        }
                        continue;
                    };
                    let plans = if uniq {
                        self.uniq_plans.get(&h).cloned().unwrap_or_default()
                    } else {
                        self.shim_plans.get(&h).cloned().unwrap_or_default()
                    };
                    let mut frame = Frame::new(tree, plans);
                    frame.shim_of = Some(h);
                    frame.shim_uniq = uniq;
                    self.frames.push(frame);
                    ts.sinks.push(Vec::new());
                    ts.tasks.push(StructTask::FinishHandler {
                        binding,
                        extra_continue,
                    });
                    if let Some(root) = self.f().tree.root {
                        ts.tasks.push(StructTask::EmitNode {
                            id: root,
                            active: None,
                            follow: Follow::Tail,
                        });
                    }
                }
                StructTask::FinishHandler {
                    binding,
                    extra_continue,
                } => {
                    self.frames.pop();
                    let mut body = ts.sinks.pop().unwrap_or_default();
                    if extra_continue {
                        body.push(SNode::Continue { label: None });
                    }
                    if let Some(cl) = ts.catch_lists.last_mut() {
                        cl.push(CatchClause { binding, body });
                    }
                }
                StructTask::EmitJoinLevel { head, set } => {
                    let Some((tree, plans)) = self.join_tree(head, &set) else {
                        if let Some(sink) = ts.sinks.last_mut() {
                            sink.push(SNode::Honest(
                                "N77: tower-join tree vanished between analysis and emission (defensive)"
                                    .into(),
                            ));
                        }
                        continue;
                    };
                    let mut frame = Frame::new(tree, plans);
                    frame.join_shim = true;
                    self.frames.push(frame);
                    ts.tasks.push(StructTask::PopFrame);
                    if let Some(root) = self.f().tree.root {
                        ts.tasks.push(StructTask::EmitNode {
                            id: root,
                            active: None,
                            follow: Follow::Tail,
                        });
                    }
                }
                StructTask::PopFrame => {
                    self.frames.pop();
                }
                StructTask::PushNodeToSink(node) => {
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(node);
                    }
                }
                StructTask::TruncateSuppress(mark) => {
                    self.suppress_wraps.truncate(mark);
                }
                other => self.step_try_task(other, &mut ts),
            }
        }
        *out = ts.sinks.pop().unwrap_or_default();
    }
}

/// Collect every `Expr::Ident` / `Expr::Temp` name referenced inside `e`
/// iteratively (zero recursion).
pub(in crate::structure) fn collect_expr_ident_refs<'a>(e: &'a Expr, out: &mut HashSet<&'a str>) {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Ident(name) | Expr::Temp { name, .. } => {
                out.insert(name.as_str());
            }
            _ => stack.extend(crate::folds::expr_children(cur)),
        }
    }
}

pub(in crate::structure) fn stmt_reads_any_name(stmt: &Stmt, names: &HashSet<&str>) -> bool {
    let mut refs: HashSet<&str> = HashSet::new();
    match stmt {
        Stmt::Declare { value, .. }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value))
        | Stmt::Throw(value)
        | Stmt::CondBranch { cond: value, .. }
        | Stmt::PhiAssign { value, .. }
        | Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => collect_expr_ident_refs(value, &mut refs),
        Stmt::StoreProp { object, value, .. } | Stmt::StorePrivate { object, value, .. } => {
            collect_expr_ident_refs(object, &mut refs);
            collect_expr_ident_refs(value, &mut refs);
        }
        Stmt::StoreIndex {
            object,
            index: key,
            value,
            ..
        }
        | Stmt::StoreDyn {
            object, key, value, ..
        } => {
            collect_expr_ident_refs(object, &mut refs);
            collect_expr_ident_refs(key, &mut refs);
            collect_expr_ident_refs(value, &mut refs);
        }
        Stmt::StoreSuper { key, value, .. } => {
            if let Some(k) = key {
                collect_expr_ident_refs(k, &mut refs);
            }
            collect_expr_ident_refs(value, &mut refs);
        }
        Stmt::DefineMethod { object, func, .. } => {
            collect_expr_ident_refs(object, &mut refs);
            collect_expr_ident_refs(func, &mut refs);
        }
        Stmt::CatchBind { .. }
        | Stmt::PhiDecl { .. }
        | Stmt::Elided { .. }
        | Stmt::ScopePush { .. }
        | Stmt::ScopePop
        | Stmt::PrivateNames { .. }
        | Stmt::Return(None)
        | Stmt::Branch { .. }
        | Stmt::Unreachable
        | Stmt::Debugger
        | Stmt::Fallback { .. } => return false,
    }
    refs.iter().any(|r| names.contains(r))
}

/// Whether evaluating `e` may throw at runtime (`D1`).
pub(in crate::structure) fn expr_may_throw(e: &Expr, safe_idents: &HashSet<String>) -> bool {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Lit(_)
            | Expr::Temp { .. }
            | Expr::Arguments
            | Expr::NewTarget
            | Expr::GlobalThis
            | Expr::SelfFunction(_)
            | Expr::Closure { .. }
            | Expr::RegExp { .. }
            | Expr::ObjectLit { .. }
            | Expr::ArrayLit { .. }
            | Expr::SuperMarker
            | Expr::ModuleNamespace { .. } => {}
            Expr::Fallback { .. } => return true,
            Expr::Ident(name) => {
                if !safe_idents.contains(name) {
                    return true;
                }
            }
            Expr::Unary {
                op:
                    UnOp::LogicalNot
                    | UnOp::IsTrue
                    | UnOp::IsFalse
                    | UnOp::TypeOf
                    | UnOp::Void
                    | UnOp::JumpEqz
                    | UnOp::JumpNez,
                operand,
            } => stack.push(operand),
            Expr::Compare {
                op: CmpOp::StrictEq | CmpOp::StrictNotEq,
                left,
                right,
            } => {
                stack.push(left);
                stack.push(right);
            }
            _ => return true,
        }
    }
    false
}

/// Whether `e` is completely free of side effects, property accesses,
/// coercions, throws, yields, and awaits (`D2`).
pub(in crate::structure) fn expr_is_pure(e: &Expr, safe_idents: &HashSet<String>) -> bool {
    !expr_may_throw(e, safe_idents)
}

pub(in crate::structure) fn stmt_may_throw(s: &Stmt, safe_idents: &HashSet<String>) -> bool {
    match s {
        Stmt::CatchBind { .. }
        | Stmt::PhiDecl { .. }
        | Stmt::Elided { .. }
        | Stmt::ScopePush { .. }
        | Stmt::ScopePop
        | Stmt::PrivateNames { .. }
        | Stmt::Return(None)
        | Stmt::Branch { .. }
        | Stmt::Unreachable
        | Stmt::Debugger
        | Stmt::Fallback { .. } => false,
        Stmt::Throw(_)
        | Stmt::StoreProp { .. }
        | Stmt::StoreIndex { .. }
        | Stmt::StoreDyn { .. }
        | Stmt::StorePrivate { .. }
        | Stmt::DefineMethod { .. }
        | Stmt::StoreSuper { .. }
        | Stmt::GlobalStore { .. } => true,
        Stmt::Declare { value, .. }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value))
        | Stmt::CondBranch { cond: value, .. }
        | Stmt::PhiAssign { value, .. }
        | Stmt::LexStore { value, .. }
        | Stmt::ModuleStore { value, .. } => expr_may_throw(value, safe_idents),
    }
}

/// Every block of a raw region tree (N77 join-shim verification; iterative).
pub(in crate::structure) fn tree_blocks(tree: &RegionTree) -> BTreeSet<BlockId> {
    let mut out = BTreeSet::new();
    let Some(root) = tree.root else {
        return out;
    };
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        match tree.node(id) {
            RegionNode::Block(b) => {
                out.insert(*b);
            }
            RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                stack.extend(children.iter().copied());
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                stack.push(*body);
            }
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => {
                out.insert(*head);
                stack.extend([then, otherwise].into_iter().flatten().copied());
            }
        }
    }
    out
}

/// The first-executed block of a raw region tree (N77 join-shim
/// verification; iterative over `Seq`).
pub(in crate::structure) fn tree_entry(tree: &RegionTree, mut id: RegionId) -> Option<BlockId> {
    loop {
        match tree.node(id) {
            RegionNode::Block(b) => return Some(*b),
            RegionNode::If { head, .. } => return Some(*head),
            RegionNode::Loop { header, .. } => return Some(*header),
            RegionNode::Labeled { label, .. } => return Some(*label),
            RegionNode::Seq(children) => {
                id = *children.first()?;
            }
            RegionNode::Alternates(_) | RegionNode::Irreducible { .. } => return None,
        }
    }
}

/// The ENTRY blocks of a tree's top-level emission positions
/// (reachable from the root through `Seq` nesting only; iterative).
pub(in crate::structure) fn tree_top_blocks(tree: &RegionTree) -> BTreeSet<BlockId> {
    let mut out = BTreeSet::new();
    let Some(root) = tree.root else {
        return out;
    };
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        match tree.node(id) {
            RegionNode::Seq(children) => {
                stack.extend(children.iter().copied());
            }
            _ => {
                if let Some(e) = tree_entry(tree, id) {
                    out.insert(e);
                }
            }
        }
    }
    out
}

pub(in crate::structure) fn deferred_try_marker(tok: usize) -> String {
    format!("__DEFERRED_TRY_CATCH_{tok}__")
}

pub(in crate::structure) fn resolve_deferred_try_in_task_state(
    ts: &mut TaskState,
    marker: &str,
    catches: Vec<CatchClause>,
    real_note: Option<String>,
) {
    let mut pending = Some((catches, real_note));
    let mut stack: Vec<&mut [SNode]> = Vec::new();
    for sink in &mut ts.sinks {
        stack.push(sink.as_mut_slice());
    }
    for clist in &mut ts.catch_lists {
        for c in clist {
            stack.push(c.body.as_mut_slice());
        }
    }
    while let Some(slice) = stack.pop() {
        for n in slice {
            match n {
                SNode::Try {
                    body,
                    catches: dst_catches,
                    note,
                    finally,
                } => {
                    if note.as_deref() == Some(marker)
                        && let Some((resolved_catches, resolved_note)) = pending.take()
                    {
                        *dst_catches = resolved_catches;
                        *note = resolved_note;
                        return;
                    }
                    stack.push(body);
                    for c in dst_catches {
                        stack.push(&mut c.body);
                    }
                    if let Some(fin) = finally {
                        stack.push(fin);
                    }
                }
                SNode::Block(body)
                | SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => stack.push(body),
                SNode::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        stack.push(&mut c.body);
                    }
                }
                SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
        }
    }
}

pub(in crate::structure) fn nodes_use_label(nodes: &[SNode], target: &str) -> bool {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(slice) = stack.pop() {
        for n in slice {
            match n {
                SNode::Break { label: Some(l) } | SNode::Continue { label: Some(l) }
                    if l == target =>
                {
                    return true;
                }
                SNode::Block(body)
                | SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => stack.push(body),
                SNode::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    stack.push(body);
                    for c in catches {
                        stack.push(&c.body);
                    }
                    if let Some(fin) = finally {
                        stack.push(fin);
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        stack.push(&c.body);
                    }
                }
                SNode::Stmts(_)
                | SNode::Break { label: None }
                | SNode::Continue { label: None }
                | SNode::Honest(_) => {}
                SNode::Break { label: Some(_) } | SNode::Continue { label: Some(_) } => {}
            }
        }
    }
    false
}

/// An out-of-set edge inside the irreducible fallback: emit a labeled
/// `break <dispatch_label>` to exit the dispatch loop when no enclosing
/// structural action applies, plus an honesty note.
pub(in crate::structure) fn out_exits(
    ctx: &mut Ctx,
    body: &mut Vec<SNode>,
    from: BlockId,
    to: BlockId,
    dispatch_label: &str,
) {
    if let Some(act) = ctx.edge_action(from, to) {
        body.push(act);
    } else {
        body.push(SNode::Honest(format!(
            "state-machine exit B{}→B{}: target outside the irreducible core — break {dispatch_label} assumes the structured continuation follows",
            from.index(),
            to.index()
        )));
        body.push(SNode::Break {
            label: Some(dispatch_label.to_string()),
        });
    }
}
