//! Region structuring over the Normal-edge CFG (`design/decompile.md` §4.2):
//! iterative region reduction producing a region tree per function.
//!
//! The algorithm is pattern-independent in the sense of Yakdan et al.
//! (NDSS'15) and Ramsey (2022): no block-shape matching drives the
//! reduction. Every decision is derived from dominance, post-dominance,
//! and reachability over the **Normal-edge** CFG (the N45 model: exception
//! edges are dispatch, not dominance — `TryRegion`s are projected onto the
//! finished tree, never structured through).
//!
//! ## Reduction order
//!
//! [`structure_regions`] computes the Normal-reachable block universe, then
//! recurses over block-set partitions with a single entry:
//!
//! 1. **Loop peel**: if the region entry has a predecessor inside the set
//!    (a latch — in a single-entry set every such edge is a back edge, and
//!    single-entry regions imply the entry dominates the set, so subgraph
//!    loops coincide with the global natural loops), the natural loop
//!    (entry plus everything reaching a latch without passing the entry)
//!    becomes a [`RegionNode::Loop`]; the remainder becomes a continuation.
//!    Loop kind is decided by header-test position: a header with an exit
//!    edge is `While`; otherwise a latch with an exit edge is `DoWhile`.
//! 2. **Straight-line run**: blocks with one in-set successor are peeled
//!    iteratively (no recursion depth per chain block).
//! 3. **Conditional**: a two-successor head splits the set into arm sets —
//!    blocks reachable from each arm entry without passing the head's
//!    immediate post-dominator (the merge, when it lies inside the set).
//!    Blocks reachable from both arms (no separating merge) are demoted to
//!    the continuation, never duplicated.
//! 4. **Multi-entry continuation**: a remainder with several handoff
//!    entries becomes [`RegionNode::Alternates`] of [`RegionNode::Labeled`]
//!    arms when the per-entry reachability slices are disjoint and cover
//!    the remainder (the labeled-break target model: exactly one arm
//!    executes). Overlapping or uncovered remainders are irreducible-ish:
//!    they collapse to [`RegionNode::Irreducible`] plus an
//!    [`EscapeHatch::MultiEntry`] record.
//!
//! Recursion always strictly shrinks the block set (loop bodies recurse
//! with their header *disabled* so the peel cannot repeat), so structuring
//! terminates on any graph.
//!
//! ## Exit edges
//!
//! After the tree is built, every Normal edge within the universe is
//! classified ([`ClassifiedEdge`]): back edges become
//! [`EdgeClass::Continue`], edges leaving one or more enclosing loops
//! become [`EdgeClass::Break`], everything else is
//! [`EdgeClass::Internal`] (fall-through/merge flow the tree already
//! encodes). A break/continue is *labeled* when it crosses more loop
//! boundaries than the innermost enclosing loop — the JS labeled
//! break/continue escape hatch (the CFR trick). Backward edges that are
//! not continues indicate an unstructured cycle and are recorded as
//! [`EscapeHatch::CrossEdge`].
//!
//! ## Irreducible detection
//!
//! A CFG is reducible iff removing its dominance back edges yields a DAG,
//! so irreducible cores are found as *cycles in the graph minus its back
//! edges* (this catches jump-into-loop shapes, whose extra entry destroys
//! the header's dominance and therefore the back edge itself). Each cycle
//! is reported as an [`IrreducibleCore`] (blocks + cycle edges); detection
//! never aborts structuring — the affected region collapses to
//! [`RegionNode::Irreducible`] through the multi-entry escape path.
//!
//! ## TryRegion containment
//!
//! `TryRegion`s are projected onto the finished tree ([`TryPlan`]).
//! Hard errors (recorded in [`RegionTree::errors`], never panicked — the
//! corpus gate asserts the list is empty, since the lift guarantees
//! containment):
//!
//! - **Pairwise laminarity**: two protected sets are disjoint or nested;
//!   intersecting-but-not-nesting is interleaving.
//! - **Single entry per Normal component**: each Normal-connected
//!   component of a protected set has at most one Normal entry (a block
//!   entered from outside the set, or the function entry). Components
//!   with zero Normal entries are dispatch-entered handler-side sub-CFGs
//!   (an outer try legitimately protects inner catch-handler blocks,
//!   whose predecessors are exceptional) or dead cycles — not violations.
//! - **No self-protection**: a catch handler is never in its own
//!   region's protected set.
//!
//! Note what is deliberately NOT an error: es2abc try ranges are
//! bytecode-contiguous, not structure-aligned, so a protected boundary
//! may cut a `Loop`/`Seq`/`If` node (e.g. cover a loop's header but not
//! its latch). That is reported as the [`TryPlan::cuts_structured_region`]
//! observation for the emitter, which places `try`/`catch` markers inside
//! the cut region.
//!
//! ## Determinism
//!
//! All iteration is over `BTreeSet`/`BTreeMap` (ordered by [`BlockId`]) or
//! the CHK dominator tree's RPO; two runs over the same module produce
//! identical trees (`PartialEq` on [`RegionTree`] is the corpus gate's
//! determinism check).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

use abcd_ir::{BlockId, EdgeKind, FuncId, Module, TryRegion};

use abcd_analysis::control::{
    Dominators, PostDominators, back_edges_in_blocks, block_succs, reachable_from,
};

mod analysis;
use analysis::*;

#[cfg(test)]
mod tests;

/// Index of a region node in [`RegionTree::nodes`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionId(pub u32);

impl RegionId {
    /// Arena index of this node.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Loop classification by header-test position (design §4.2.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopKind {
    /// The header carries an exit test (`while (c) { … }` / `for (…)`).
    While,
    /// The header falls through unconditionally and a latch carries the
    /// exit test (`do { … } while (c)`).
    DoWhile,
}

/// One node of the region tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegionNode {
    /// A single basic block.
    Block(BlockId),
    /// Sequential composition, in emission order.
    Seq(Vec<RegionId>),
    /// A multi-entry continuation: exactly one arm executes, reached via a
    /// labeled exit from a sibling region (the Relooper "multiple" shape /
    /// JS labeled-block targets). Arms are keyed by their entry block.
    Alternates(Vec<RegionId>),
    /// A labeled group: inner [`EdgeClass::Break`] edges targeting `label`
    /// land here. `label` is the arm/region entry block.
    Labeled {
        /// The label (this group's entry block).
        label: BlockId,
        /// The labeled body region.
        body: RegionId,
    },
    /// `if (head-cond) { then } [else { otherwise }]`, reconverging at
    /// `merge` when one exists inside the region. `head` doubles as the
    /// block emission (its terminator is the branch).
    If {
        /// The branch head block.
        head: BlockId,
        /// The true-arm region (`None` = empty arm).
        then: Option<RegionId>,
        /// The false-arm region (`None` = no else).
        otherwise: Option<RegionId>,
        /// The merge block (the head's immediate post-dominator), when it
        /// lies inside the parent region.
        merge: Option<BlockId>,
    },
    /// A cyclic region; `body` contains `header` (emitted in place).
    Loop {
        /// The loop header (unique entry of the body).
        header: BlockId,
        /// Header-test position.
        kind: LoopKind,
        /// The loop body region.
        body: RegionId,
    },
    /// Escape hatch: a subgraph that resisted structuring (irreducible or
    /// multi-entry). Kept as raw blocks + internal edges for the
    /// state-variable-dispatch fallback of design §4.2.4.
    Irreducible {
        /// Member blocks, sorted.
        blocks: Vec<BlockId>,
        /// Internal Normal edges `(from, to)`, sorted by source order.
        edges: Vec<(BlockId, BlockId)>,
    },
}

/// Classification of one Normal CFG edge after structuring.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeClass {
    /// Fall-through/merge flow already encoded by the tree shape.
    Internal,
    /// Back edge to an enclosing loop header (`continue`). `labeled` when
    /// the target loop is not the innermost loop enclosing the source —
    /// emission needs `continue <label>`.
    Continue {
        /// The target loop's header (the continue label).
        header: BlockId,
        /// Whether emission needs the labeled form.
        labeled: bool,
    },
    /// Edge leaving one or more enclosing loops (`break`). `header` is the
    /// outermost loop exited; `labeled` when more than the innermost loop
    /// is crossed — emission needs `break <label>`.
    Break {
        /// The outermost exited loop's header (the break label).
        header: BlockId,
        /// Whether emission needs the labeled form.
        labeled: bool,
    },
}

/// A classified Normal edge of the function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassifiedEdge {
    /// Source block.
    pub from: BlockId,
    /// Target block.
    pub to: BlockId,
    /// The edge's structural role.
    pub class: EdgeClass,
}

/// An irreducible CFG core: a cycle in the Normal-edge graph after
/// removing dominance back edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrreducibleCore {
    /// Member blocks, sorted.
    pub blocks: Vec<BlockId>,
    /// The cycle's edges, in cycle order.
    pub cycle_edges: Vec<(BlockId, BlockId)>,
}

/// A shape that structuring could not fold into the tree; every such
/// shape is also materialized as a [`RegionNode::Irreducible`] (or a
/// classified cross-edge) so the tree remains total.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EscapeHatch {
    /// A region subset with more than one Normal entry (blocks + the
    /// entry blocks). Irreducible jump-into-loop shapes surface here.
    MultiEntry {
        /// Member blocks, sorted.
        blocks: Vec<BlockId>,
        /// Entry blocks (blocks with a Normal predecessor outside the
        /// subset), sorted.
        entries: Vec<BlockId>,
    },
    /// Blocks with no handoff from the already-structured part of the
    /// region (defensive; unreachable in single-entry partitions).
    Stranded {
        /// Member blocks, sorted.
        blocks: Vec<BlockId>,
    },
    /// A backward edge (in RPO) that is not a loop continue — the marker
    /// of a cycle the loop forest did not claim.
    CrossEdge {
        /// Source block.
        from: BlockId,
        /// Target block.
        to: BlockId,
    },
}

/// A hard structuring error. Recorded, never panicked — the corpus gate
/// asserts none occur.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegionError {
    /// Two `TryRegion`s' protected sets intersect without nesting.
    InterleavedTryRegions {
        /// Earlier region index (`func.try_regions` position).
        a: usize,
        /// Later region index.
        b: usize,
    },
    /// A catch handler is protected by its own region.
    HandlerInsideProtected {
        /// Region index.
        region: usize,
        /// The handler block.
        handler: BlockId,
    },
    /// A protected set has a Normal-connected component with several
    /// entries (a structured try body is a single-entry sub-CFG per
    /// component).
    TryMultipleEntries {
        /// Region index.
        region: usize,
        /// The entry blocks found, sorted.
        entries: Vec<BlockId>,
    },
}

/// A natural loop of the function (back edges merged by header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopInfo {
    /// The loop header (back-edge target; dominates the body).
    pub header: BlockId,
    /// Header-test position.
    pub kind: LoopKind,
    /// Member blocks, sorted.
    pub blocks: Vec<BlockId>,
    /// Index of the smallest strictly-containing loop, if any.
    pub parent: Option<usize>,
}

/// Projection of one `TryRegion` onto the region tree (design §4.2.5:
/// the try is one region with multiple exits; the protected blocks are
/// structured as a sub-CFG).
pub struct TryPlan {
    /// Index into `func.try_regions`.
    pub region: usize,
    /// The unique Normal entry of the protected set (`None` when the
    /// entry check failed — see [`RegionError::TryMultipleEntries`]).
    pub entry: Option<BlockId>,
    /// Protected blocks, sorted (as recorded in the IR, dead included).
    pub protected: Vec<BlockId>,
    /// Catch handler entry blocks, in dispatch order.
    pub handlers: Vec<BlockId>,
    /// The smallest tree node containing all reachable protected blocks
    /// (`None` when no protected block is Normal-reachable).
    pub span: Option<RegionId>,
    /// Observation hook for decompiler emission: the protected boundary
    /// partially overlaps a Loop or Irreducible tree node. es2abc try ranges
    /// are bytecode-contiguous, not structure-aligned (a range may cover a
    /// loop's header but not its latch), so this is NOT an error — but
    /// emission must place the `try {`/`catch` markers inside the cut
    /// region.
    pub cuts_structured_region: bool,
    /// Nested laminar child `TryPlan`s when organized into a nesting forest
    /// (see [`RegionTree::try_plan_forest`]).
    pub children: Vec<TryPlan>,
}

impl Drop for TryPlan {
    fn drop(&mut self) {
        if self.children.is_empty() {
            return;
        }
        let mut stack: Vec<TryPlan> = std::mem::take(&mut self.children);
        while let Some(mut cur) = stack.pop() {
            if !cur.children.is_empty() {
                stack.extend(std::mem::take(&mut cur.children));
            }
        }
    }
}

impl Clone for TryPlan {
    fn clone(&self) -> Self {
        if self.children.is_empty() {
            return Self {
                region: self.region,
                entry: self.entry,
                protected: self.protected.clone(),
                handlers: self.handlers.clone(),
                span: self.span,
                cuts_structured_region: self.cuts_structured_region,
                children: Vec::new(),
            };
        }
        enum Step<'a> {
            Visit(&'a TryPlan),
            Build(&'a TryPlan, usize),
        }
        let mut steps = vec![Step::Visit(self)];
        let mut vals: Vec<TryPlan> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(p) => {
                    if p.children.is_empty() {
                        vals.push(TryPlan {
                            region: p.region,
                            entry: p.entry,
                            protected: p.protected.clone(),
                            handlers: p.handlers.clone(),
                            span: p.span,
                            cuts_structured_region: p.cuts_structured_region,
                            children: Vec::new(),
                        });
                    } else {
                        steps.push(Step::Build(p, p.children.len()));
                        for ch in p.children.iter().rev() {
                            steps.push(Step::Visit(ch));
                        }
                    }
                }
                Step::Build(p, count) => {
                    let start = vals.len().saturating_sub(count);
                    let children = vals.split_off(start);
                    vals.push(TryPlan {
                        region: p.region,
                        entry: p.entry,
                        protected: p.protected.clone(),
                        handlers: p.handlers.clone(),
                        span: p.span,
                        cuts_structured_region: p.cuts_structured_region,
                        children,
                    });
                }
            }
        }
        vals.pop().unwrap_or(Self {
            region: self.region,
            entry: self.entry,
            protected: Vec::new(),
            handlers: Vec::new(),
            span: None,
            cuts_structured_region: false,
            children: Vec::new(),
        })
    }
}

impl PartialEq for TryPlan {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            if a.region != b.region
                || a.entry != b.entry
                || a.protected != b.protected
                || a.handlers != b.handlers
                || a.span != b.span
                || a.cuts_structured_region != b.cuts_structured_region
                || a.children.len() != b.children.len()
            {
                return false;
            }
            for (ca, cb) in a.children.iter().zip(b.children.iter()).rev() {
                stack.push((ca, cb));
            }
        }
        true
    }
}

impl Eq for TryPlan {}

impl std::fmt::Debug for TryPlan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Plan(&'a TryPlan),
            Raw(&'static str),
        }
        let mut tasks = vec![Task::Plan(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Raw(s) => f.write_str(s)?,
                Task::Plan(p) => {
                    write!(
                        f,
                        "TryPlan {{ region: {:?}, entry: {:?}, protected: {:?}, handlers: {:?}, span: {:?}, cuts_structured_region: {:?}, children: [",
                        p.region,
                        p.entry,
                        p.protected,
                        p.handlers,
                        p.span,
                        p.cuts_structured_region
                    )?;
                    tasks.push(Task::Raw("] }"));
                    for (idx, ch) in p.children.iter().enumerate().rev() {
                        tasks.push(Task::Plan(ch));
                        if idx > 0 {
                            tasks.push(Task::Raw(", "));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// The structured region tree of one function, plus all side reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionTree {
    /// The analyzed function.
    pub func: FuncId,
    nodes: Vec<RegionNode>,
    /// The root region; `None` for functions without blocks.
    pub root: Option<RegionId>,
    /// Every Normal edge within the reachable universe, classified, in
    /// RPO-then-successor order.
    pub edges: Vec<ClassifiedEdge>,
    /// The natural-loop forest (back edges merged by header).
    pub loops: Vec<LoopInfo>,
    /// Irreducible cores (cycles minus dominance back edges).
    pub irreducible: Vec<IrreducibleCore>,
    /// Shapes that fell to the escape hatch during structuring.
    pub escape_hatches: Vec<EscapeHatch>,
    /// Forward edges from one conditional arm into its sibling arm (the
    /// es2abc `if (c) goto shared; …` / short-circuit idiom). NOT a
    /// structuring failure — the tree is truthful — but emission must
    /// duplicate the shared tail or merge the conditions during folding,
    /// so the shape is enumerable here.
    pub cross_arm_edges: Vec<(BlockId, BlockId)>,
    /// `TryRegion` projections.
    pub try_plans: Vec<TryPlan>,
    /// Hard errors (must be empty on well-formed input; the corpus gate
    /// asserts this).
    pub errors: Vec<RegionError>,
    /// Blocks of the function not Normal-reachable from the entry (dead
    /// code and catch handlers — handlers appear in [`TryPlan::handlers`],
    /// never in the tree).
    pub dead_blocks: Vec<BlockId>,
}

impl RegionTree {
    /// All region nodes (arena; [`RegionId`] indexes this slice).
    pub fn nodes(&self) -> &[RegionNode] {
        &self.nodes
    }

    /// Look up one node by id, returning `None` when `id` is out of bounds.
    #[must_use]
    pub fn get(&self, id: RegionId) -> Option<&RegionNode> {
        self.nodes.get(id.index())
    }

    /// One node by id (panic-free: returns a shared empty [`RegionNode::Seq`]
    /// if `id` is out of bounds).
    pub fn node(&self, id: RegionId) -> &RegionNode {
        static EMPTY_SEQ: RegionNode = RegionNode::Seq(Vec::new());
        self.nodes.get(id.index()).unwrap_or(&EMPTY_SEQ)
    }

    /// The root node, when the function has blocks.
    pub fn root_node(&self) -> Option<&RegionNode> {
        self.root.and_then(|r| self.get(r))
    }

    /// Organize [`Self::try_plans`] into a laminar nesting forest via
    /// [`TryPlan::children`] (outermost plans as roots, nested sub-plans
    /// attached in declaration order).
    #[must_use]
    pub fn try_plan_forest(&self) -> Vec<TryPlan> {
        if self.try_plans.is_empty() {
            return Vec::new();
        }
        let n = self.try_plans.len();
        let sets: Vec<BTreeSet<BlockId>> = self
            .try_plans
            .iter()
            .map(|p| p.protected.iter().copied().collect())
            .collect();
        // Order indices by `(protected.len(), region)` ascending so children
        // are finalized before their enclosing parents without recursion.
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by_key(|&i| (sets[i].len(), self.try_plans[i].region));

        let mut parent_of = vec![None; n];
        for (pos, &i) in order.iter().enumerate() {
            if sets[i].is_empty() {
                continue;
            }
            for &j in &order[pos + 1..] {
                let strict_or_earlier_tie =
                    sets[j].len() > sets[i].len() || (sets[j].len() == sets[i].len() && j < i);
                if strict_or_earlier_tie && sets[i].is_subset(&sets[j]) {
                    parent_of[i] = Some(j);
                    break;
                }
            }
        }

        let mut nodes: Vec<Option<TryPlan>> = self.try_plans.iter().cloned().map(Some).collect();
        let mut children_buckets: Vec<Vec<TryPlan>> = (0..n).map(|_| Vec::new()).collect();
        for &i in &order {
            let Some(mut plan) = nodes[i].take() else {
                continue;
            };
            let mut ch = std::mem::take(&mut children_buckets[i]);
            ch.sort_by_key(|p| p.region);
            plan.children = ch;
            if let Some(p) = parent_of[i] {
                children_buckets[p].push(plan);
            } else {
                nodes[i] = Some(plan);
            }
        }
        let mut roots: Vec<TryPlan> = nodes.into_iter().flatten().collect();
        roots.sort_by_key(|p| p.region);
        roots
    }
}

/// Zero-copy view of a single-entry CFG subgraph within a [`Module`] (#29).
///
/// Used by `abcd-decompile` to structure catch/finally handler sub-CFGs and
/// shared continuation join slices directly against `&Module`, without
/// cloning or mutating `Module`.
pub struct CfgSubgraph<'a> {
    /// Function identity recorded on [`RegionTree::func`].
    pub func: FuncId,
    /// Subgraph entry block (`None` yields an empty [`RegionTree`]).
    pub entry: Option<BlockId>,
    /// Ordered member blocks (`entry` first, matching `FunctionData::blocks`).
    pub blocks: &'a [BlockId],
    /// Projected Normal-edge successor relation (consistent with
    /// [`Dominators::over`] and [`PostDominators::over`]).
    pub succ: &'a dyn Fn(BlockId) -> Vec<BlockId>,
    /// Scoped `TryRegion`s belonging to this subgraph.
    pub try_regions: &'a [TryRegion],
}

/// Structure one function's Normal-edge CFG into a region tree. Total:
/// every reachable block lands in the tree, and any shape that resists
/// structuring is recorded in [`RegionTree::escape_hatches`] /
/// [`RegionTree::irreducible`] instead of aborting.
pub fn structure_regions(module: &Module, func: FuncId) -> RegionTree {
    let succ = |b: BlockId| block_succs(module, b);
    let Some(f) = module.func(func) else {
        return structure_subgraph(
            module,
            &CfgSubgraph {
                func,
                entry: None,
                blocks: &[],
                succ: &succ,
                try_regions: &[],
            },
        );
    };
    structure_subgraph(
        module,
        &CfgSubgraph {
            func,
            entry: f.entry(),
            blocks: &f.blocks,
            succ: &succ,
            try_regions: &f.try_regions,
        },
    )
}

/// Structure an explicit [`CfgSubgraph`] over `module` with zero `Module`
/// clones and `O(|subgraph|)` working memory (#29).
pub fn structure_subgraph(module: &Module, subgraph: &CfgSubgraph<'_>) -> RegionTree {
    let func = subgraph.func;
    let Some(entry) = subgraph.entry else {
        return RegionTree {
            func,
            nodes: Vec::new(),
            root: None,
            edges: Vec::new(),
            loops: Vec::new(),
            irreducible: Vec::new(),
            escape_hatches: Vec::new(),
            cross_arm_edges: Vec::new(),
            try_plans: Vec::new(),
            errors: Vec::new(),
            dead_blocks: subgraph.blocks.to_vec(),
        };
    };

    let normal_succs = subgraph.succ;

    // The universe: blocks Normal-reachable from the entry, sorted by `BlockId`.
    let universe: BTreeSet<BlockId> = reachable_from(entry, normal_succs).into_iter().collect();
    let u_blocks: Vec<BlockId> = universe.iter().copied().collect();
    let u_len = u_blocks.len();
    let word_len = u_len.div_ceil(64);
    let mut u_idx: HashMap<BlockId, u32> = HashMap::with_capacity(u_len);
    for (i, &b) in u_blocks.iter().enumerate() {
        u_idx.insert(b, i as u32);
    }

    let dead_blocks: Vec<BlockId> = subgraph
        .blocks
        .iter()
        .copied()
        .filter(|b| !u_idx.contains_key(b))
        .collect();

    let dom = Dominators::from_entry(func, Some(entry), normal_succs);
    // Post-dominance over the full Normal graph. Note the two merge
    // computations consume it differently: conditional merges take the
    // head's immediate post-dominator verbatim (a join may itself be a
    // function-exit block — short-circuit conditionals reconverge on a
    // return), while loop merges use the exit TARGETS' common
    // post-dominator (a `return`/`throw` from inside the loop is a loop
    // exit but not a continuation, and must not poison the merge).
    let postdom = PostDominators::over_blocks(func, subgraph.blocks, normal_succs);

    // Universe-filtered successor/predecessor tables over dense `0..u_len`
    // indices (successors in terminator order, deduped; predecessors sorted,
    // deduped).
    let mut succs: Vec<Vec<u32>> = vec![Vec::new(); u_len];
    let mut preds: Vec<Vec<u32>> = vec![Vec::new(); u_len];
    // Blocks with a Normal predecessor OUTSIDE the universe (the N45
    // model: handler sub-CFGs are structured separately, so their
    // Normal out-edges into the shared continuation are invisible in
    // the filtered tables). Such a block is a handler-path rejoin
    // target: the handler side can only reach it by falling out of a
    // catch clause onto it, so it must never be buried inside a
    // conditional arm (N76).
    let mut external_preds = BitSet::empty(word_len);
    for (bi, &b) in u_blocks.iter().enumerate() {
        let mut seen: Vec<u32> = Vec::new();
        for s in normal_succs(b) {
            if let Some(&si) = u_idx.get(&s)
                && !seen.contains(&si)
            {
                seen.push(si);
            }
        }
        succs[bi] = seen;
        if let Some(bb) = module.block(b) {
            let mut p_vec: Vec<u32> = Vec::new();
            for e in &bb.preds {
                if e.kind == EdgeKind::Normal {
                    if let Some(&pi) = u_idx.get(&e.from) {
                        p_vec.push(pi);
                    } else {
                        external_preds.insert(bi as u32);
                    }
                }
            }
            p_vec.sort_unstable();
            p_vec.dedup();
            preds[bi] = p_vec;
        }
    }

    // The natural-loop forest: dominance back edges merged by header.
    let be = back_edges_in_blocks(subgraph.blocks, &dom, normal_succs);
    let mut by_header_u: BTreeMap<u32, BitSet> = BTreeMap::new();
    let mut dead_loop_headers: BTreeSet<BlockId> = BTreeSet::new();
    let mut nl_stack: Vec<u32> = Vec::new();
    for &(latch, header) in &be {
        if let (Some(&hi), Some(&li)) = (u_idx.get(&header), u_idx.get(&latch)) {
            let members = by_header_u.entry(hi).or_insert_with(|| {
                let mut bs = BitSet::empty(word_len);
                bs.insert(hi);
                bs
            });
            nl_stack.clear();
            nl_stack.push(li);
            while let Some(m) = nl_stack.pop() {
                if m == hi || !members.insert(m) {
                    continue;
                }
                for &p in &preds[m as usize] {
                    if !members.contains(p) {
                        nl_stack.push(p);
                    }
                }
            }
        } else {
            dead_loop_headers.insert(header);
        }
    }

    let mut paired_loops: Vec<(LoopInfo, BitSet)> =
        Vec::with_capacity(by_header_u.len() + dead_loop_headers.len());
    for (&hi, block_bits) in &by_header_u {
        let header = u_blocks[hi as usize];
        let blocks_vec = block_bits.to_blocks(&u_blocks);
        let header_exits = succs[hi as usize].iter().any(|&s| !block_bits.contains(s));
        let latch_exits = preds[hi as usize]
            .iter()
            .copied()
            .filter(|&p| block_bits.contains(p))
            .any(|l| succs[l as usize].iter().any(|&s| !block_bits.contains(s)));
        let kind = if header_exits {
            LoopKind::While
        } else if latch_exits {
            LoopKind::DoWhile
        } else {
            // No exit on header or latch (infinite or mid-body exits only).
            LoopKind::While
        };
        paired_loops.push((
            LoopInfo {
                header,
                kind,
                blocks: blocks_vec,
                parent: None,
            },
            block_bits.clone(),
        ));
    }
    if !dead_loop_headers.is_empty() {
        for dh in dead_loop_headers {
            paired_loops.push((
                LoopInfo {
                    header: dh,
                    kind: LoopKind::While,
                    blocks: vec![dh],
                    parent: None,
                },
                BitSet::empty(word_len),
            ));
        }
        paired_loops.sort_by_key(|(info, _)| info.header);
    }
    let mut loops: Vec<LoopInfo> = Vec::with_capacity(paired_loops.len());
    let mut loop_bits: Vec<BitSet> = Vec::with_capacity(paired_loops.len());
    for (info, bits) in paired_loops {
        loops.push(info);
        loop_bits.push(bits);
    }

    // Parent links: two reducible natural loops with distinct headers are
    // laminar (`L_i ⊂ L_j` iff `header(L_i) ∈ L_j`), so indexing headers in
    // `header_to_loop` discovers every loop's smallest strictly-containing
    // parent in `O(|U| + ∑|L_j|)` without an `O(L^2)` pair scan.
    let mut header_to_loop: Vec<Option<usize>> = vec![None; u_len];
    for (i, lp) in loops.iter().enumerate() {
        if !loop_bits[i].is_empty()
            && let Some(&hi) = u_idx.get(&lp.header)
        {
            header_to_loop[hi as usize] = Some(i);
        }
    }
    for j in 0..loops.len() {
        if loop_bits[j].is_empty() {
            continue;
        }
        let j_len = loops[j].blocks.len();
        for bi in loop_bits[j].iter() {
            if let Some(i) = header_to_loop[bi as usize]
                && i != j
                && j_len > loops[i].blocks.len()
                && loops[i]
                    .parent
                    .is_none_or(|p| j_len < loops[p].blocks.len())
                && loop_bits[i].is_subset(&loop_bits[j])
            {
                loops[i].parent = Some(j);
            }
        }
    }

    // Irreducible cores: single-pass iterative Tarjan SCC over `G \ back_edges`
    // (`O(|U| + |E|)` worst-case time, zero DFS restarts).
    let mut back_edges_u: HashSet<(u32, u32)> = HashSet::with_capacity(be.len() * 2);
    for &(u, v) in &be {
        if let (Some(&ui), Some(&vi)) = (u_idx.get(&u), u_idx.get(&v)) {
            back_edges_u.insert((ui, vi));
        }
    }
    let irreducible = irreducible_cores_tarjan(u_len, &u_blocks, &succs, &back_edges_u);

    // Innermost natural loop per block (the tail-arm decomposition's
    // fold-compatibility bail — see `Builder::shared_tail_plan`).
    let mut block_loop: Vec<Option<usize>> = vec![None; u_len];
    for (i, bits) in loop_bits.iter().enumerate() {
        let set_len = loops[i].blocks.len();
        for bi in bits.iter() {
            let slot = &mut block_loop[bi as usize];
            *slot = match *slot {
                Some(j) if loops[j].blocks.len() <= set_len => Some(j),
                _ => Some(i),
            };
        }
    }

    // Build the tree.
    let mut builder = Builder {
        u_blocks,
        u_idx,
        word_len,
        succs,
        preds,
        dom,
        postdom,
        nodes: Vec::new(),
        escape_hatches: Vec::new(),
        cross_arms: Vec::new(),
        external_preds,
        block_loop,
        loop_bits,
        scratch_unvisited: vec![0u64; word_len],
        scratch_queue: Vec::with_capacity(u_len),
    };
    let root = if u_len == 0 {
        None
    } else {
        let entry_idx = builder.u_idx[&entry];
        let full = BitSet::full(u_len, word_len);
        let empty_disabled = BitSet::empty(word_len);
        Some(builder.structure_set(full, entry_idx, &empty_disabled))
    };

    // Classify every Normal edge in the universe (RPO order, then
    // successor order — fully deterministic).
    let mut rpo_pos: Vec<Option<usize>> = vec![None; u_len];
    for (pos, &b) in builder.dom.rpo().iter().enumerate() {
        if let Some(&bi) = builder.u_idx.get(&b) {
            rpo_pos[bi as usize] = Some(pos);
        }
    }
    let mut header_loop: Vec<Option<usize>> = vec![None; u_len];
    for (li, l) in loops.iter().enumerate() {
        if !builder.loop_bits[li].is_empty()
            && let Some(&hi) = builder.u_idx.get(&l.header)
        {
            header_loop[hi as usize] = Some(li);
        }
    }
    let loop_key = |i: usize| (loops[i].blocks.len(), loops[i].header);
    let mut innermost_loop: Vec<Option<usize>> = vec![None; u_len];
    for (li, bits) in builder.loop_bits.iter().enumerate() {
        for bi in bits.iter() {
            let slot = &mut innermost_loop[bi as usize];
            match *slot {
                None => *slot = Some(li),
                Some(prev) if loop_key(li) < loop_key(prev) => *slot = Some(li),
                Some(_) => {}
            }
        }
    }
    let mut loops_desc: Vec<usize> = (0..loops.len())
        .filter(|&i| !builder.loop_bits[i].is_empty())
        .collect();
    loops_desc.sort_by_key(|&a| std::cmp::Reverse((loop_key(a), a)));

    let mut edges = Vec::new();
    let rpo_blocks: Vec<BlockId> = builder.dom.rpo().to_vec();
    for u in rpo_blocks {
        let Some(&ui) = builder.u_idx.get(&u) else {
            continue;
        };
        let u_succ_len = builder.succs[ui as usize].len();
        for si in 0..u_succ_len {
            let vi = builder.succs[ui as usize][si];
            let v = builder.u_blocks[vi as usize];
            let class = classify_edge(
                u,
                ui,
                v,
                vi,
                &loops,
                &builder.loop_bits,
                &header_loop,
                &innermost_loop,
                &loops_desc,
                &rpo_pos,
                &mut builder.escape_hatches,
            );
            edges.push(ClassifiedEdge {
                from: u,
                to: v,
                class,
            });
        }
    }

    // TryRegion projection + containment assertions.
    let (try_plans, errors) = project_try_regions(
        module,
        subgraph,
        entry,
        &builder.u_idx,
        word_len,
        root.map(|_| &builder.nodes[..]),
        root,
    );

    RegionTree {
        func,
        nodes: builder.nodes,
        root,
        edges,
        loops,
        irreducible,
        escape_hatches: builder.escape_hatches,
        cross_arm_edges: builder.cross_arms,
        try_plans,
        errors,
        dead_blocks,
    }
}

/// The iterative structurer's working state.
struct Builder {
    u_blocks: Vec<BlockId>,
    u_idx: HashMap<BlockId, u32>,
    word_len: usize,
    succs: Vec<Vec<u32>>,
    preds: Vec<Vec<u32>>,
    dom: Dominators,
    postdom: PostDominators,
    nodes: Vec<RegionNode>,
    escape_hatches: Vec<EscapeHatch>,
    cross_arms: Vec<(BlockId, BlockId)>,
    /// Universe blocks with a Normal predecessor outside the universe
    /// (handler-side rejoin targets — see `structure_regions`).
    external_preds: BitSet,
    /// Innermost natural loop per universe block (index into `loop_bits`).
    block_loop: Vec<Option<usize>>,
    /// Natural-loop block sets, indexed by `block_loop`.
    loop_bits: Vec<BitSet>,
    /// Reusable bitmask buffer for `reach` / `rev_reach`.
    scratch_unvisited: Vec<u64>,
    /// Reusable BFS queue for `reach` / `rev_reach` / exit-tail absorption.
    scratch_queue: Vec<u32>,
}

impl Builder {
    fn push_node(&mut self, node: RegionNode) -> RegionId {
        let id = RegionId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    fn wrap_seq(&mut self, mut items: Vec<RegionId>) -> RegionId {
        match items.len() {
            1 => items.pop().expect("one item"),
            _ => self.push_node(RegionNode::Seq(items)),
        }
    }

    /// True when `s` is a Return/Throw leaf or a single-predecessor linear
    /// chain ending in one (e.g. a straight-line return/throw tail split at
    /// `may_throw` register-write boundaries under `R2-C1`), with no external
    /// handler-rejoin predecessors along the chain.
    fn is_leaf_tail(&self, mut s: u32) -> bool {
        if self.succs[s as usize].is_empty() {
            return true;
        }
        if self.preds[s as usize].len() != 1 || self.external_preds.contains(s) {
            return false;
        }
        for _ in 0..=self.succs.len() {
            match self.succs[s as usize].as_slice() {
                [] => return true,
                &[next]
                    if next != s
                        && self.preds[next as usize].len() == 1
                        && !self.external_preds.contains(next) =>
                {
                    s = next;
                }
                _ => return false,
            }
        }
        false
    }

    /// Deepest common post-dominator (LCA in `self.postdom`) across a
    /// non-empty target set (`#82` `R4-P4`).
    fn intersect_postdom(&self, targets: &BitSet) -> Option<BlockId> {
        let mut iter = targets.iter();
        let mut cur = self.u_blocks[iter.next()? as usize];
        for ti in iter {
            let t = self.u_blocks[ti as usize];
            while !self.postdom.post_dominates(cur, t) {
                cur = self.postdom.ipostdom(cur)?;
            }
        }
        Some(cur)
    }

    /// The merge of the loop with (natural) body `body`: the nearest
    /// common post-dominator of the loop's exit targets, excluding targets
    /// that leave the function (Return/Throw leaves — they are loop exits
    /// but not continuations). `None` for infinite loops and for loops
    /// whose exit tails never reconverge (those structure as
    /// [`RegionNode::Alternates`] continuations).
    fn loop_merge(&self, body: &BitSet) -> Option<BlockId> {
        let mut raw_targets = BitSet::empty(self.word_len);
        let mut raw_count = 0usize;
        for b in body.iter() {
            for &s in &self.succs[b as usize] {
                if !body.contains(s)
                    && !self.succs[s as usize].is_empty()
                    && !raw_targets.contains(s)
                {
                    raw_targets.insert(s);
                    raw_count += 1;
                }
            }
        }
        if let Some(m) = self.intersect_postdom(&raw_targets) {
            return Some(m);
        }
        if raw_count < 2 {
            return None;
        }
        let mut filtered = BitSet::empty(self.word_len);
        for s in raw_targets.iter() {
            if !self.is_leaf_tail(s) {
                filtered.insert(s);
            }
        }
        self.intersect_postdom(&filtered)
    }

    /// Forward reachability from `from` over `succs`, restricted to
    /// `within`, never entering `avoid_a` or `avoid_b`.
    fn reach(
        &mut self,
        from: u32,
        within: &BitSet,
        avoid_a: Option<u32>,
        avoid_b: Option<u32>,
    ) -> BitSet {
        self.scratch_unvisited.copy_from_slice(&within.words);
        if let Some(a) = avoid_a {
            self.scratch_unvisited[(a >> 6) as usize] &= !(1u64 << (a & 63));
        }
        if let Some(b) = avoid_b {
            self.scratch_unvisited[(b >> 6) as usize] &= !(1u64 << (b & 63));
        }
        let from_mask = 1u64 << (from & 63);
        let from_slot = &mut self.scratch_unvisited[(from >> 6) as usize];
        if (*from_slot & from_mask) == 0 {
            return BitSet::empty(self.word_len);
        }
        *from_slot &= !from_mask;
        self.scratch_queue.clear();
        self.scratch_queue.push(from);
        let mut head = 0usize;
        while head < self.scratch_queue.len() {
            let b = self.scratch_queue[head];
            head += 1;
            for &s in &self.succs[b as usize] {
                let mask = 1u64 << (s & 63);
                let slot = &mut self.scratch_unvisited[(s >> 6) as usize];
                if (*slot & mask) != 0 {
                    *slot &= !mask;
                    self.scratch_queue.push(s);
                }
            }
        }
        let mut words = within.words.clone();
        if let Some(a) = avoid_a {
            words[(a >> 6) as usize] &= !(1u64 << (a & 63));
        }
        if let Some(b) = avoid_b {
            words[(b >> 6) as usize] &= !(1u64 << (b & 63));
        }
        for (w, &u) in words.iter_mut().zip(self.scratch_unvisited.iter()) {
            *w ^= u;
        }
        BitSet {
            words,
            len: self.scratch_queue.len(),
        }
    }

    /// Reverse reachability from `sources` over `preds`, restricted to
    /// `within`, never entering `avoid`.
    fn rev_reach(&mut self, sources: &[u32], within: &BitSet, avoid: u32) -> BitSet {
        self.scratch_unvisited.copy_from_slice(&within.words);
        self.scratch_unvisited[(avoid >> 6) as usize] &= !(1u64 << (avoid & 63));
        self.scratch_queue.clear();
        for &s in sources {
            let mask = 1u64 << (s & 63);
            let slot = &mut self.scratch_unvisited[(s >> 6) as usize];
            if (*slot & mask) != 0 {
                *slot &= !mask;
                self.scratch_queue.push(s);
            }
        }
        if self.scratch_queue.is_empty() {
            return BitSet::empty(self.word_len);
        }
        let mut head = 0usize;
        while head < self.scratch_queue.len() {
            let b = self.scratch_queue[head];
            head += 1;
            for &p in &self.preds[b as usize] {
                let mask = 1u64 << (p & 63);
                let slot = &mut self.scratch_unvisited[(p >> 6) as usize];
                if (*slot & mask) != 0 {
                    *slot &= !mask;
                    self.scratch_queue.push(p);
                }
            }
        }
        let mut words = within.words.clone();
        words[(avoid >> 6) as usize] &= !(1u64 << (avoid & 63));
        for (w, &u) in words.iter_mut().zip(self.scratch_unvisited.iter()) {
            *w ^= u;
        }
        BitSet {
            words,
            len: self.scratch_queue.len(),
        }
    }

    /// A collapsed escape-hatch node for a set that resisted structuring.
    fn irreducible_node(&mut self, set: &BitSet) -> RegionId {
        let mut edges = Vec::new();
        for b in set.iter() {
            let b_id = self.u_blocks[b as usize];
            for &s in &self.succs[b as usize] {
                if set.contains(s) {
                    edges.push((b_id, self.u_blocks[s as usize]));
                }
            }
        }
        self.push_node(RegionNode::Irreducible {
            blocks: set.to_blocks(&self.u_blocks),
            edges,
        })
    }
}

/// Pending labeled arms of an alternates decomposition: per-entry block
/// sets in entry order.
type ArmSets = VecDeque<(u32, BitSet)>;

/// The shared-tail decomposition plan: tail entry, tail set, pending
/// prefix arms.
type SharedTailPlan = (u32, BitSet, ArmSets);

/// One work item of the iterative structuring driver.
///
/// Region structuring used to be a mutual recursion (`structure_set` ⇄
/// `peel_loop` ⇄ `structure_continuation` ⇄ `structure_acyclic`) whose
/// depth tracked the input CFG's nesting — an ASan corpus run overflowed
/// an 8 MiB native stack on a deeply nested fixture. The driver keeps the
/// exact same node-push, escape-hatch and child-call order (the corpus
/// determinism gate pins it) on this explicit heap stack instead.
///
/// Protocol: every task leaves exactly one result in the driver's `child`
/// slot — the [`RegionId`] it produced, or `None` for an empty
/// conditional arm (a child that was never scheduled). Resume frames read
/// `child` when popped; because a resume frame is always pushed before
/// the child task it waits for, the value it reads is its own child's.
enum Task {
    /// `structure_set(set, entry, disabled)`.
    Set {
        set: BitSet,
        entry: u32,
        disabled: Rc<BitSet>,
    },
    /// `structure_continuation(set, disabled)`.
    Cont { set: BitSet, disabled: Rc<BitSet> },
    /// `peel_loop` resume after the body is structured; `child` is the
    /// body region.
    LoopBody {
        entry: u32,
        kind: LoopKind,
        remainder: BitSet,
        disabled: Rc<BitSet>,
    },
    /// `peel_loop` resume after the continuation is structured; `child`
    /// is the continuation region.
    LoopCont { loop_r: RegionId },
    /// Shared-tail resume after the tail is structured; `child` is the
    /// tail body. `pending` holds the per-entry non-empty exclusive
    /// prefixes, in entry order.
    TailBody {
        t0: u32,
        pending: ArmSets,
        disabled: Rc<BitSet>,
    },
    /// Labeled-arm accumulation (disjoint alternates arms and shared-tail
    /// prefix arms alike): on entry `child` is the body of the arm
    /// entered by `last` (`None` before the first arm).
    Arms {
        pending: ArmSets,
        arms: Vec<RegionId>,
        last: Option<u32>,
        disabled: Rc<BitSet>,
    },
    /// `structure_acyclic` resume after a child region that simply gets
    /// appended to `items`: the loop-header handoff and the continuation
    /// share this shape.
    AcycAppend { items: Vec<RegionId> },
    /// `structure_acyclic` resume after the then arm; `child` is the then
    /// region (`None` for an empty arm).
    AcycThen {
        items: Vec<RegionId>,
        head: BlockId,
        merge: Option<BlockId>,
        rest: BitSet,
        else_set: BitSet,
        else_entry: u32,
        disabled: Rc<BitSet>,
    },
    /// `structure_acyclic` resume after the else arm; `child` is the else
    /// region (`None` for an empty arm).
    AcycElse {
        items: Vec<RegionId>,
        head: BlockId,
        merge: Option<BlockId>,
        rest: BitSet,
        then_r: Option<RegionId>,
        disabled: Rc<BitSet>,
    },
    /// `structure_acyclic` handler-rejoin demotion resume; `child` is the
    /// single conditional arm (`None` when empty).
    AcycDemote {
        items: Vec<RegionId>,
        head: BlockId,
        cond_arm_is_then: bool,
        rest: BitSet,
        disabled: Rc<BitSet>,
    },
}

impl Builder {
    /// Structure `set` (a single-entry subset of the universe) with `entry`
    /// as its unique handoff. `disabled` holds loop headers already peeled
    /// by an ancestor (their incoming edges are continues, not loops).
    ///
    /// Iterative driver over the explicit [`Task`] stack — see the enum
    /// docs for why this is not recursion.
    fn structure_set(&mut self, set: BitSet, entry: u32, disabled: &BitSet) -> RegionId {
        let mut stack: Vec<Task> = vec![Task::Set {
            set,
            entry,
            disabled: Rc::new(disabled.clone()),
        }];
        let mut child: Option<RegionId> = None;
        while let Some(task) = stack.pop() {
            match task {
                Task::Set {
                    set,
                    entry,
                    disabled,
                } => self.start_set(&mut stack, &mut child, set, entry, disabled),
                Task::Cont { set, disabled } => {
                    self.start_continuation(&mut stack, &mut child, set, disabled)
                }
                Task::LoopBody {
                    entry,
                    kind,
                    remainder,
                    disabled,
                } => {
                    let body_r = child.expect("loop body region");
                    let loop_r = self.push_node(RegionNode::Loop {
                        header: self.u_blocks[entry as usize],
                        kind,
                        body: body_r,
                    });
                    if remainder.is_empty() {
                        child = Some(loop_r);
                    } else {
                        stack.push(Task::LoopCont { loop_r });
                        stack.push(Task::Cont {
                            set: remainder,
                            disabled,
                        });
                    }
                }
                Task::LoopCont { loop_r } => {
                    let cont = child.expect("loop continuation region");
                    child = Some(self.push_node(RegionNode::Seq(vec![loop_r, cont])));
                }
                Task::TailBody {
                    t0,
                    pending,
                    disabled,
                } => {
                    let tail_body = child.expect("shared-tail body region");
                    let arms = vec![self.push_node(RegionNode::Labeled {
                        label: self.u_blocks[t0 as usize],
                        body: tail_body,
                    })];
                    stack.push(Task::Arms {
                        pending,
                        arms,
                        last: None,
                        disabled,
                    });
                }
                Task::Arms {
                    mut pending,
                    mut arms,
                    last,
                    disabled,
                } => {
                    if let Some(e) = last {
                        let body = child.expect("alternates arm region");
                        arms.push(self.push_node(RegionNode::Labeled {
                            label: self.u_blocks[e as usize],
                            body,
                        }));
                    }
                    match pending.pop_front() {
                        Some((e, set)) => {
                            stack.push(Task::Arms {
                                pending,
                                arms,
                                last: Some(e),
                                disabled: disabled.clone(),
                            });
                            stack.push(Task::Set {
                                set,
                                entry: e,
                                disabled,
                            });
                        }
                        None => {
                            child = Some(self.push_node(RegionNode::Alternates(arms)));
                        }
                    }
                }
                Task::AcycAppend { mut items } => {
                    let r = child.expect("acyclic child region");
                    items.push(r);
                    child = Some(self.wrap_seq(items));
                }
                Task::AcycThen {
                    items,
                    head,
                    merge,
                    rest,
                    else_set,
                    else_entry,
                    disabled,
                } => {
                    let then_r = child;
                    stack.push(Task::AcycElse {
                        items,
                        head,
                        merge,
                        rest,
                        then_r,
                        disabled: disabled.clone(),
                    });
                    if else_set.is_empty() {
                        child = None;
                    } else {
                        stack.push(Task::Set {
                            set: else_set,
                            entry: else_entry,
                            disabled,
                        });
                    }
                }
                Task::AcycElse {
                    mut items,
                    head,
                    merge,
                    rest,
                    then_r,
                    disabled,
                } => {
                    let else_r = child;
                    items.push(self.push_node(RegionNode::If {
                        head,
                        then: then_r,
                        otherwise: else_r,
                        merge,
                    }));
                    if rest.is_empty() {
                        child = Some(self.wrap_seq(items));
                    } else {
                        stack.push(Task::AcycAppend { items });
                        stack.push(Task::Cont {
                            set: rest,
                            disabled,
                        });
                    }
                }
                Task::AcycDemote {
                    mut items,
                    head,
                    cond_arm_is_then,
                    rest,
                    disabled,
                } => {
                    let arm_r = child;
                    let (then_r, else_r) = if cond_arm_is_then {
                        (arm_r, None)
                    } else {
                        (None, arm_r)
                    };
                    items.push(self.push_node(RegionNode::If {
                        head,
                        then: then_r,
                        otherwise: else_r,
                        merge: None,
                    }));
                    if rest.is_empty() {
                        child = Some(self.wrap_seq(items));
                    } else {
                        stack.push(Task::AcycAppend { items });
                        stack.push(Task::Cont {
                            set: rest,
                            disabled,
                        });
                    }
                }
            }
        }
        child.expect("the root task always produces a region")
    }

    /// The `structure_set` prologue: multi-entry escape, loop-peel
    /// dispatch, else acyclic structuring.
    fn start_set(
        &mut self,
        stack: &mut Vec<Task>,
        child: &mut Option<RegionId>,
        set: BitSet,
        entry: u32,
        disabled: Rc<BitSet>,
    ) {
        debug_assert!(set.contains(entry));
        // Single-entry invariant: only `entry` may have predecessors
        // outside the set. Violations are irreducible/multi-entry shapes.
        let mut extra: Vec<BlockId> = Vec::new();
        let set_words = &set.words;
        for (wi, &word_val) in set_words.iter().enumerate() {
            let mut w = word_val;
            while w != 0 {
                let tz = w.trailing_zeros();
                w &= w - 1;
                let b = ((wi as u32) << 6) | tz;
                if b == entry {
                    continue;
                }
                for &p in &self.preds[b as usize] {
                    if (set_words[(p >> 6) as usize] & (1u64 << (p & 63))) == 0 {
                        extra.push(self.u_blocks[b as usize]);
                        break;
                    }
                }
            }
        }
        if !extra.is_empty() {
            self.escape_hatches.push(EscapeHatch::MultiEntry {
                blocks: set.to_blocks(&self.u_blocks),
                entries: extra,
            });
            *child = Some(self.irreducible_node(&set));
            return;
        }
        // Loop peel: any in-set predecessor of the entry is a latch.
        if !disabled.contains(entry) && self.preds[entry as usize].iter().any(|&p| set.contains(p))
        {
            self.start_loop(stack, set, entry, disabled);
            return;
        }
        self.start_acyclic(stack, child, set, entry, disabled);
    }

    /// Peel the loop headed by `entry` out of `set`: schedule the body
    /// and continuation, resuming at [`Task::LoopBody`].
    ///
    /// The body starts as the natural loop (entry plus everything reaching
    /// a latch without passing entry) and is then grown by **exit-tail
    /// absorption**: blocks whose in-set predecessors are all in the body
    /// are loop-exit paths (`if (c) {…} else {…; break/continue/return}`
    /// tails) and belong to the body. Targets of the header's or a latch's
    /// own exit edges are excluded — they are the loop's normal
    /// termination/after-point (reconverging with break tails there), not
    /// exit paths. Absorption is what keeps break/continue tails from
    /// surfacing as bogus multi-entry continuations.
    fn start_loop(&mut self, stack: &mut Vec<Task>, set: BitSet, entry: u32, disabled: Rc<BitSet>) {
        let latches: Vec<u32> = self.preds[entry as usize]
            .iter()
            .copied()
            .filter(|&p| set.contains(p))
            .collect();
        let mut body = self.rev_reach(&latches, &set, entry);
        body.insert(entry);

        // Exit-tail absorption to the unique monotone least fixed point:
        //
        // - If the loop has a merge (the common post-dominator of its
        //   non-leaf exit targets) inside `set`, the merge is the loop's
        //   after-point: absorb everything whose predecessors are all in
        //   the body, stopping at the merge. This pulls in the normal
        //   exit tail too (e.g. the header-test-true path reconverging
        //   with a break tail at the outer latch).
        // - Otherwise (infinite loops, exits straight out of the
        //   function), exclude the header's and latches' own exit targets
        //   from absorption — they are the loop's normal
        //   termination/after-point, not exit paths.
        let merge_bi = self
            .loop_merge(&body)
            .and_then(|mb| self.u_idx.get(&mb).copied())
            .filter(|&m| set.contains(m));
        let mut excluded = BitSet::empty(self.word_len);
        match merge_bi {
            Some(m) => {
                excluded.insert(m);
            }
            None => {
                for &b in std::iter::once(&entry).chain(latches.iter()) {
                    for &s in &self.succs[b as usize] {
                        if !body.contains(s) {
                            excluded.insert(s);
                        }
                    }
                }
            }
        }
        // Worklist propagation over out-edges of `body` (`O(|body| + |edges(body)|)`):
        // a candidate `x` can satisfy `∅ ≠ (preds(x) ∩ set) ⊆ body` only
        // after one of its predecessors joins `body`.
        self.scratch_queue.clear();
        for b in body.iter() {
            for &s in &self.succs[b as usize] {
                if set.contains(s) && !body.contains(s) && !excluded.contains(s) {
                    self.scratch_queue.push(s);
                }
            }
        }
        let mut head = 0usize;
        while head < self.scratch_queue.len() {
            let x = self.scratch_queue[head];
            head += 1;
            if body.contains(x) {
                continue;
            }
            let mut has_in_set_pred = false;
            let mut all_in_body = true;
            for &p in &self.preds[x as usize] {
                if set.contains(p) {
                    has_in_set_pred = true;
                    if !body.contains(p) {
                        all_in_body = false;
                        break;
                    }
                }
            }
            if has_in_set_pred && all_in_body {
                body.insert(x);
                for &s in &self.succs[x as usize] {
                    if set.contains(s) && !body.contains(s) && !excluded.contains(s) {
                        self.scratch_queue.push(s);
                    }
                }
            }
        }

        // Loop kind by header-test position (local to this body).
        let header_exits = self.succs[entry as usize]
            .iter()
            .any(|&s| !body.contains(s));
        let latch_exits = latches
            .iter()
            .any(|&l| self.succs[l as usize].iter().any(|&s| !body.contains(s)));
        let kind = if header_exits {
            LoopKind::While
        } else if latch_exits {
            LoopKind::DoWhile
        } else {
            LoopKind::While
        };

        let mut disabled2 = (*disabled).clone();
        disabled2.insert(entry);
        let disabled2 = Rc::new(disabled2);
        let mut remainder = set;
        remainder.remove_all(&body);
        stack.push(Task::LoopBody {
            entry,
            kind,
            remainder,
            disabled: disabled2.clone(),
        });
        stack.push(Task::Set {
            set: body,
            entry,
            disabled: disabled2,
        });
    }

    /// Structure a remainder set entered by handoff from already-structured
    /// siblings. Single entry: plain dispatch. Multiple entries: disjoint
    /// per-entry slices become labeled alternates; overlapping slices with
    /// a shared fall-through tail become a tail-arm alternates (see
    /// [`Builder::shared_tail_plan`]); anything else escapes.
    fn start_continuation(
        &mut self,
        stack: &mut Vec<Task>,
        child: &mut Option<RegionId>,
        set: BitSet,
        disabled: Rc<BitSet>,
    ) {
        let mut entries: Vec<u32> = Vec::new();
        for b in set.iter() {
            if self.preds[b as usize].iter().any(|&p| !set.contains(p)) {
                entries.push(b);
            }
        }
        match entries.len() {
            0 => {
                self.escape_hatches.push(EscapeHatch::Stranded {
                    blocks: set.to_blocks(&self.u_blocks),
                });
                *child = Some(self.irreducible_node(&set));
            }
            1 => stack.push(Task::Set {
                set,
                entry: entries[0],
                disabled,
            }),
            _ => {
                let slices: Vec<BitSet> = entries
                    .iter()
                    .map(|&e| self.reach(e, &set, None, None))
                    .collect();
                let mut covered = BitSet::empty(self.word_len);
                let mut disjoint = true;
                for slice in &slices {
                    for b in slice.iter() {
                        if !covered.insert(b) {
                            disjoint = false;
                        }
                    }
                }
                if !disjoint || covered != set {
                    // Overlapping slices: the es2abc switch fall-through
                    // shape — several entries converge on a SHARED TAIL
                    // (case bodies falling into each other). Try the
                    // tail-arm decomposition before escaping.
                    match self.shared_tail_plan(&set, &entries, &slices) {
                        Some((t0, tail, pending)) => {
                            stack.push(Task::TailBody {
                                t0,
                                pending,
                                disabled: disabled.clone(),
                            });
                            stack.push(Task::Set {
                                set: tail,
                                entry: t0,
                                disabled,
                            });
                        }
                        None => {
                            self.escape_hatches.push(EscapeHatch::MultiEntry {
                                blocks: set.to_blocks(&self.u_blocks),
                                entries: entries
                                    .iter()
                                    .map(|&e| self.u_blocks[e as usize])
                                    .collect(),
                            });
                            *child = Some(self.irreducible_node(&set));
                        }
                    }
                } else {
                    let pending: ArmSets = entries.into_iter().zip(slices).collect();
                    stack.push(Task::Arms {
                        pending,
                        arms: Vec::new(),
                        last: None,
                        disabled,
                    });
                }
            }
        }
    }

    /// Shared-tail decomposition of a multi-entry set whose per-entry
    /// slices OVERLAP (the switch fall-through shape: `case A: …` falls
    /// into `case B: …`, and `B` is also a direct dispatch target).
    fn shared_tail_plan(
        &self,
        set: &BitSet,
        entries: &[u32],
        slices: &[BitSet],
    ) -> Option<SharedTailPlan> {
        // The tail: reachable from every entry.
        let mut tail = slices.first()?.clone();
        for slice in &slices[1..] {
            tail.intersect_with(slice);
        }
        if tail.is_empty() {
            return None;
        }
        // Suffix-closed: no edge from the tail back into an exclusive
        // prefix (that would be a cycle crossing the split — genuinely
        // irreducible).
        for b in tail.iter() {
            for &s in &self.succs[b as usize] {
                if set.contains(s) && !tail.contains(s) {
                    return None;
                }
            }
        }
        // Exclusive prefixes: pairwise disjoint, and with the tail they
        // cover the set exactly.
        let prefixes: Vec<BitSet> = slices.iter().map(|s| s.difference(&tail)).collect();
        let mut seen = BitSet::empty(self.word_len);
        for prefix in &prefixes {
            for b in prefix.iter() {
                if !seen.insert(b) {
                    return None;
                }
            }
        }
        if seen.len + tail.len != set.len {
            return None;
        }
        // Single tail entry `t0`: every edge into the tail — from a
        // prefix or from outside the set — targets it.
        let mut t0: Option<u32> = None;
        for b in tail.iter() {
            for &p in &self.preds[b as usize] {
                if tail.contains(p) {
                    continue;
                }
                match t0 {
                    None => t0 = Some(b),
                    Some(t) if t == b => {}
                    Some(_) => return None,
                }
            }
        }
        let t0 = t0?;
        // Fold-compatibility bail: an arm entry targeted by an edge
        // from a loop that is not wholly inside this set would force a
        // LABELED break/continue at that loop's exit.
        let arm_entry_has_loop_pred = std::iter::once(&t0).chain(entries.iter()).any(|&e| {
            self.preds[e as usize]
                .iter()
                .any(|&p| match self.block_loop[p as usize] {
                    Some(l) => !self.loop_bits[l].is_subset(set),
                    None => false,
                })
        });
        if arm_entry_has_loop_pred {
            return None;
        }
        let pending: ArmSets = entries
            .iter()
            .copied()
            .zip(prefixes)
            .filter(|(_, prefix)| !prefix.is_empty())
            .collect();
        Some((t0, tail, pending))
    }

    /// Acyclic structuring: iterative straight-line runs, conditional
    /// splits at two-successor heads, loop headers handed back to
    /// [`Task::Set`]. Child structurings suspend the run through resume
    /// frames on `stack`.
    fn start_acyclic(
        &mut self,
        stack: &mut Vec<Task>,
        child: &mut Option<RegionId>,
        set: BitSet,
        entry: u32,
        disabled: Rc<BitSet>,
    ) {
        let mut items: Vec<RegionId> = Vec::new();
        let mut rest = set;
        let mut cur = entry;
        loop {
            // A loop header reached mid-run: hand the whole remainder over
            // (the peel structures it and its continuation).
            if !disabled.contains(cur) && self.preds[cur as usize].iter().any(|&p| rest.contains(p))
            {
                stack.push(Task::AcycAppend { items });
                stack.push(Task::Set {
                    set: rest,
                    entry: cur,
                    disabled,
                });
                return;
            }
            rest.remove(cur);
            let cur_block = self.u_blocks[cur as usize];
            let mut s0: Option<u32> = None;
            let mut s1: Option<u32> = None;
            let mut in_len = 0usize;
            for &s in &self.succs[cur as usize] {
                if rest.contains(s) {
                    match in_len {
                        0 => s0 = Some(s),
                        1 => s1 = Some(s),
                        _ => {}
                    }
                    in_len += 1;
                }
            }
            match in_len {
                0 => {
                    items.push(self.push_node(RegionNode::Block(cur_block)));
                    break;
                }
                1 => {
                    items.push(self.push_node(RegionNode::Block(cur_block)));
                    cur = s0.expect("in_len == 1");
                }
                _ => {
                    let (t, f) = (s0.expect("in_len >= 2"), s1.expect("in_len >= 2"));
                    // Two-arm conditional. The merge is the head's
                    // immediate post-dominator (when inside the region);
                    // arms are what each entry reaches without passing the
                    // merge AND without entering the other arm's entry.
                    let merge_bi = self
                        .postdom
                        .ipostdom(cur_block)
                        .and_then(|mb| self.u_idx.get(&mb).copied())
                        .filter(|&m| rest.contains(m));
                    let merge = merge_bi.map(|m| self.u_blocks[m as usize]);
                    let mut then_set = self.reach(t, &rest, merge_bi, Some(f));
                    let mut else_set = self.reach(f, &rest, merge_bi, Some(t));
                    // Blocks reachable from both arms without passing the
                    // merge are shared: demote them to the continuation,
                    // never duplicate.
                    if !then_set.is_empty() && !else_set.is_empty() {
                        let mut removed = 0usize;
                        for (tw, ew) in then_set.words.iter_mut().zip(else_set.words.iter_mut()) {
                            let ov = *tw & *ew;
                            if ov != 0 {
                                *tw &= !ov;
                                *ew &= !ov;
                                removed += ov.count_ones() as usize;
                            }
                        }
                        then_set.len -= removed;
                        else_set.len -= removed;
                    }
                    // Edges from one arm into the sibling arm (the
                    // goto-shared idiom) are recorded as cross-arm hints.
                    let mut cross: Vec<(BlockId, BlockId)> = Vec::new();
                    if !then_set.is_empty() && !else_set.is_empty() {
                        for (arm, sibling) in [(&then_set, &else_set), (&else_set, &then_set)] {
                            for b in arm.iter() {
                                let b_id = self.u_blocks[b as usize];
                                for &s in &self.succs[b as usize] {
                                    if sibling.contains(s) {
                                        cross.push((b_id, self.u_blocks[s as usize]));
                                    }
                                }
                            }
                        }
                    }
                    // Handler-rejoin demotion (N76).
                    let mut demote: Option<bool> = None;
                    if merge.is_none()
                        && self.external_preds.contains(t) != self.external_preds.contains(f)
                    {
                        demote = Some(self.external_preds.contains(f));
                    }
                    let demote = demote.filter(|&cond_arm_is_then| {
                        let (arm_set, demoted_set, demoted_entry) = if cond_arm_is_then {
                            (&then_set, &else_set, f)
                        } else {
                            (&else_set, &then_set, t)
                        };
                        let exits_ok = arm_set.iter().all(|b| {
                            self.succs[b as usize].iter().all(|&s| {
                                arm_set.contains(s) || s == demoted_entry || !rest.contains(s)
                            })
                        });
                        let no_reentry = demoted_set
                            .iter()
                            .all(|b| self.succs[b as usize].iter().all(|&s| !arm_set.contains(s)));
                        exits_ok && no_reentry
                    });
                    if let Some(cond_arm_is_then) = demote {
                        let (arm_set, arm_entry) = if cond_arm_is_then {
                            (then_set, t)
                        } else {
                            (else_set, f)
                        };
                        rest.remove_all(&arm_set);
                        stack.push(Task::AcycDemote {
                            items,
                            head: cur_block,
                            cond_arm_is_then,
                            rest,
                            disabled: disabled.clone(),
                        });
                        if arm_set.is_empty() {
                            *child = None;
                        } else {
                            stack.push(Task::Set {
                                set: arm_set,
                                entry: arm_entry,
                                disabled,
                            });
                        }
                        return;
                    }
                    self.cross_arms.extend(cross);
                    rest.remove_all(&then_set);
                    rest.remove_all(&else_set);
                    stack.push(Task::AcycThen {
                        items,
                        head: cur_block,
                        merge,
                        rest,
                        else_set,
                        else_entry: f,
                        disabled: disabled.clone(),
                    });
                    if then_set.is_empty() {
                        *child = None;
                    } else {
                        stack.push(Task::Set {
                            set: then_set,
                            entry: t,
                            disabled,
                        });
                    }
                    return;
                }
            }
        }
        // Defensive: with the single-entry invariant every block is
        // consumed; record and collapse anything left over.
        if !rest.is_empty() {
            self.escape_hatches.push(EscapeHatch::Stranded {
                blocks: rest.to_blocks(&self.u_blocks),
            });
            let r = self.irreducible_node(&rest);
            items.push(r);
        }
        *child = Some(self.wrap_seq(items));
    }
}
