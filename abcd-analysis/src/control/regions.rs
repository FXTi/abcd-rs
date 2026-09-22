//! Region structuring over the Normal-edge CFG (design/decompile.md §4.2,
//! d-P1 infra phase): recursive region reduction producing a region tree
//! per function.
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

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use abcd_ir::{BlockId, EdgeKind, FuncId, Module};

use super::dom::{Dominators, PostDominators};
use super::loops::{back_edges, natural_loop};
use super::succs::block_succs;

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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    /// Observation hook for d-P3: the protected boundary partially
    /// overlaps a Loop or Irreducible tree node. es2abc try ranges are
    /// bytecode-contiguous, not structure-aligned (a range may cover a
    /// loop's header but not its latch), so this is NOT an error — but
    /// emission must place the `try {`/`catch` markers inside the cut
    /// region.
    pub cuts_structured_region: bool,
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
    /// duplicate the shared tail or merge the conditions (a d-P3 fold),
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

    /// One node by id.
    pub fn node(&self, id: RegionId) -> &RegionNode {
        &self.nodes[id.index()]
    }

    /// The root node, when the function has blocks.
    pub fn root_node(&self) -> Option<&RegionNode> {
        self.root.map(|r| self.node(r))
    }
}

/// Structure one function's Normal-edge CFG into a region tree. Total:
/// every reachable block lands in the tree, and any shape that resists
/// structuring is recorded in [`RegionTree::escape_hatches`] /
/// [`RegionTree::irreducible`] instead of aborting.
pub fn structure_regions(module: &Module, func: FuncId) -> RegionTree {
    let empty = |module: &Module| RegionTree {
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
        dead_blocks: module
            .func(func)
            .map(|f| f.blocks.clone())
            .unwrap_or_default(),
    };
    let Some(f) = module.func(func) else {
        return empty(module);
    };
    let Some(entry) = f.entry() else {
        return empty(module);
    };

    // The universe: blocks Normal-reachable from the entry.
    let normal_succs = |b: BlockId| block_succs(module, b);
    let universe: BTreeSet<BlockId> = super::reach::reachable_blocks(module, func, &normal_succs)
        .into_iter()
        .collect();
    let dead_blocks: Vec<BlockId> = f
        .blocks
        .iter()
        .copied()
        .filter(|b| !universe.contains(b))
        .collect();

    let dom = Dominators::normal(module, func);
    // Post-dominance over the full Normal graph. Note the two merge
    // computations consume it differently: conditional merges take the
    // head's immediate post-dominator verbatim (a join may itself be a
    // function-exit block — short-circuit conditionals reconverge on a
    // return), while loop merges use the exit TARGETS' common
    // post-dominator (a `return`/`throw` from inside the loop is a loop
    // exit but not a continuation, and must not poison the merge).
    let postdom = PostDominators::normal(module, func);

    // Universe-filtered successor/predecessor tables (successors in
    // terminator order, deduped; predecessors sorted, deduped).
    let mut succs: Vec<Vec<BlockId>> = vec![Vec::new(); module.blocks.len()];
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); module.blocks.len()];
    for &b in &universe {
        let mut seen = BTreeSet::new();
        succs[b.index()] = block_succs(module, b)
            .into_iter()
            .filter(|s| universe.contains(s) && seen.insert(*s))
            .collect();
        if let Some(bb) = module.block(b) {
            preds[b.index()] = bb
                .preds
                .iter()
                .filter(|e| e.kind == EdgeKind::Normal && universe.contains(&e.from))
                .map(|e| e.from)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
        }
    }

    // The natural-loop forest: dominance back edges merged by header.
    let be = back_edges(module, func, &dom, &normal_succs);
    let loop_preds = |b: BlockId| preds[b.index()].clone();
    let mut by_header: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for &(latch, header) in &be {
        by_header
            .entry(header)
            .or_default()
            .extend(natural_loop(header, latch, &loop_preds));
    }
    let mut loops: Vec<LoopInfo> = Vec::new();
    for (header, blocks) in &by_header {
        let blocks_vec: Vec<BlockId> = blocks.iter().copied().collect();
        let block_set = blocks;
        let header_exits = succs[header.index()].iter().any(|s| !block_set.contains(s));
        let latches: Vec<BlockId> = preds[header.index()]
            .iter()
            .copied()
            .filter(|p| block_set.contains(p))
            .collect();
        let latch_exits = latches
            .iter()
            .any(|&l| succs[l.index()].iter().any(|s| !block_set.contains(s)));
        let kind = if header_exits {
            LoopKind::While
        } else if latch_exits {
            LoopKind::DoWhile
        } else {
            // No exit on header or latch (infinite or mid-body exits only).
            LoopKind::While
        };
        loops.push(LoopInfo {
            header: *header,
            kind,
            blocks: blocks_vec,
            parent: None,
        });
    }
    // Parent links: the smallest strict superset loop.
    for i in 0..loops.len() {
        let sub: BTreeSet<BlockId> = loops[i].blocks.iter().copied().collect();
        let mut parent: Option<usize> = None;
        for (j, other) in loops.iter().enumerate() {
            if i == j || other.blocks.len() <= loops[i].blocks.len() {
                continue;
            }
            let sup: BTreeSet<BlockId> = other.blocks.iter().copied().collect();
            let smaller = match parent {
                None => true,
                Some(p) => loops[p].blocks.len() > other.blocks.len(),
            };
            if sub.is_subset(&sup) && smaller {
                parent = Some(j);
            }
        }
        loops[i].parent = parent;
    }

    // Irreducible cores: cycles in the graph minus dominance back edges.
    let back: BTreeSet<(BlockId, BlockId)> = be.iter().copied().collect();
    let mut removed = back.clone();
    let mut irreducible = Vec::new();
    while let Some((blocks, cycle_edges)) = find_cycle(&universe, &succs, &removed) {
        removed.extend(cycle_edges.iter().copied());
        irreducible.push(IrreducibleCore {
            blocks,
            cycle_edges,
        });
    }

    // Build the tree.
    let mut builder = Builder {
        succs,
        preds,
        dom,
        postdom,
        nodes: Vec::new(),
        escape_hatches: Vec::new(),
        cross_arms: Vec::new(),
    };
    let root = if universe.is_empty() {
        None
    } else {
        Some(builder.structure_set(universe.clone(), entry, &BTreeSet::new()))
    };

    // Classify every Normal edge in the universe (RPO order, then
    // successor order — fully deterministic).
    let rpo_index: BTreeMap<BlockId, usize> = builder
        .dom
        .rpo()
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    let mut edges = Vec::new();
    for &u in builder.dom.rpo() {
        for &v in &builder.succs[u.index()] {
            let class = classify_edge(u, v, &loops, &rpo_index, &mut builder.escape_hatches);
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
        f,
        entry,
        &universe,
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

/// The recursive structurer's working state.
struct Builder {
    succs: Vec<Vec<BlockId>>,
    preds: Vec<Vec<BlockId>>,
    dom: Dominators,
    postdom: PostDominators,
    nodes: Vec<RegionNode>,
    escape_hatches: Vec<EscapeHatch>,
    cross_arms: Vec<(BlockId, BlockId)>,
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

    /// The merge of the loop with (natural) body `body`: the nearest
    /// common post-dominator of the loop's exit targets, excluding targets
    /// that leave the function (Return/Throw leaves — they are loop exits
    /// but not continuations). `None` for infinite loops and for loops
    /// whose exit tails never reconverge (those structure as
    /// [`RegionNode::Alternates`] continuations).
    fn loop_merge(&self, body: &BTreeSet<BlockId>) -> Option<BlockId> {
        let mut targets = BTreeSet::new();
        for &b in body {
            for &s in &self.succs[b.index()] {
                if !body.contains(&s) && !self.succs[s.index()].is_empty() {
                    targets.insert(s);
                }
            }
        }
        let mut iter = targets.iter();
        let first = *iter.next()?;
        let mut chain = self.postdom.post_dominator_chain(first);
        for &t in iter {
            let other = self.postdom.post_dominator_chain(t);
            // The chains are ordered from the block upward; the first
            // common element is the deepest common post-dominator.
            let mut found = None;
            'outer: for &a in &chain {
                for &b in &other {
                    if a == b {
                        found = Some(a);
                        break 'outer;
                    }
                }
            }
            chain = vec![found?];
        }
        chain.first().copied()
    }

    /// Forward reachability from `from` over `succs`, restricted to
    /// `within`, never entering `avoid`.
    fn reach(
        &self,
        from: BlockId,
        within: &BTreeSet<BlockId>,
        avoid: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut seen = BTreeSet::new();
        if !within.contains(&from) || avoid.contains(&from) {
            return seen;
        }
        seen.insert(from);
        let mut queue = VecDeque::from([from]);
        while let Some(b) = queue.pop_front() {
            for &s in &self.succs[b.index()] {
                if within.contains(&s) && !avoid.contains(&s) && seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        seen
    }

    /// Reverse reachability from `sources` over `preds`, restricted to
    /// `within`, never entering `avoid`.
    fn rev_reach(
        &self,
        sources: &[BlockId],
        within: &BTreeSet<BlockId>,
        avoid: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut seen = BTreeSet::new();
        let mut queue = VecDeque::new();
        for &s in sources {
            if within.contains(&s) && !avoid.contains(&s) && seen.insert(s) {
                queue.push_back(s);
            }
        }
        while let Some(b) = queue.pop_front() {
            for &p in &self.preds[b.index()] {
                if within.contains(&p) && !avoid.contains(&p) && seen.insert(p) {
                    queue.push_back(p);
                }
            }
        }
        seen
    }

    /// A collapsed escape-hatch node for a set that resisted structuring.
    fn irreducible_node(&mut self, set: &BTreeSet<BlockId>) -> RegionId {
        let mut edges = Vec::new();
        for &b in set {
            for &s in &self.succs[b.index()] {
                if set.contains(&s) {
                    edges.push((b, s));
                }
            }
        }
        self.push_node(RegionNode::Irreducible {
            blocks: set.iter().copied().collect(),
            edges,
        })
    }

    /// Structure `set` (a single-entry subset of the universe) with `entry`
    /// as its unique handoff. `disabled` holds loop headers already peeled
    /// by an ancestor (their incoming edges are continues, not loops).
    fn structure_set(
        &mut self,
        set: BTreeSet<BlockId>,
        entry: BlockId,
        disabled: &BTreeSet<BlockId>,
    ) -> RegionId {
        debug_assert!(set.contains(&entry));
        // Single-entry invariant: only `entry` may have predecessors
        // outside the set. Violations are irreducible/multi-entry shapes.
        let extra: Vec<BlockId> = set
            .iter()
            .copied()
            .filter(|&b| b != entry && self.preds[b.index()].iter().any(|p| !set.contains(p)))
            .collect();
        if !extra.is_empty() {
            self.escape_hatches.push(EscapeHatch::MultiEntry {
                blocks: set.iter().copied().collect(),
                entries: extra,
            });
            return self.irreducible_node(&set);
        }
        // Loop peel: any in-set predecessor of the entry is a latch.
        if !disabled.contains(&entry) && self.preds[entry.index()].iter().any(|p| set.contains(p)) {
            return self.peel_loop(set, entry, disabled);
        }
        self.structure_acyclic(set, entry, disabled)
    }

    /// Peel the loop headed by `entry` out of `set`.
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
    fn peel_loop(
        &mut self,
        set: BTreeSet<BlockId>,
        entry: BlockId,
        disabled: &BTreeSet<BlockId>,
    ) -> RegionId {
        let latches: Vec<BlockId> = self.preds[entry.index()]
            .iter()
            .copied()
            .filter(|p| set.contains(p))
            .collect();
        let avoid = BTreeSet::from([entry]);
        let mut body = self.rev_reach(&latches, &set, &avoid);
        body.insert(entry);

        // Exit-tail absorption to a fixpoint (sorted iteration keeps it
        // deterministic regardless of growth order). Two modes:
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
        let merge = self.loop_merge(&body).filter(|m| set.contains(m));
        let excluded: BTreeSet<BlockId> = match merge {
            Some(m) => BTreeSet::from([m]),
            None => {
                let mut ex = BTreeSet::new();
                for b in std::iter::once(&entry).chain(latches.iter()) {
                    ex.extend(
                        self.succs[b.index()]
                            .iter()
                            .copied()
                            .filter(|s| !body.contains(s)),
                    );
                }
                ex
            }
        };
        loop {
            let mut grew = false;
            for &x in &set {
                if body.contains(&x) || excluded.contains(&x) {
                    continue;
                }
                let ps: Vec<BlockId> = self.preds[x.index()]
                    .iter()
                    .copied()
                    .filter(|p| set.contains(p))
                    .collect();
                if !ps.is_empty() && ps.iter().all(|p| body.contains(p)) {
                    body.insert(x);
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }

        // Loop kind by header-test position (local to this body).
        let header_exits = self.succs[entry.index()].iter().any(|s| !body.contains(s));
        let latch_exits = latches
            .iter()
            .any(|&l| self.succs[l.index()].iter().any(|s| !body.contains(s)));
        let kind = if header_exits {
            LoopKind::While
        } else if latch_exits {
            LoopKind::DoWhile
        } else {
            LoopKind::While
        };

        let mut disabled2 = disabled.clone();
        disabled2.insert(entry);
        let mut remainder = set;
        for b in &body {
            remainder.remove(b);
        }
        let body_r = self.structure_set(body, entry, &disabled2);
        let loop_r = self.push_node(RegionNode::Loop {
            header: entry,
            kind,
            body: body_r,
        });
        if remainder.is_empty() {
            return loop_r;
        }
        let cont = self.structure_continuation(remainder, &disabled2);
        self.push_node(RegionNode::Seq(vec![loop_r, cont]))
    }

    /// Structure a remainder set entered by handoff from already-structured
    /// siblings. Single entry: plain recursion. Multiple entries: disjoint
    /// per-entry slices become labeled alternates; anything else escapes.
    fn structure_continuation(
        &mut self,
        set: BTreeSet<BlockId>,
        disabled: &BTreeSet<BlockId>,
    ) -> RegionId {
        let entries: Vec<BlockId> = set
            .iter()
            .copied()
            .filter(|&b| self.preds[b.index()].iter().any(|p| !set.contains(p)))
            .collect();
        match entries.len() {
            0 => {
                self.escape_hatches.push(EscapeHatch::Stranded {
                    blocks: set.iter().copied().collect(),
                });
                self.irreducible_node(&set)
            }
            1 => self.structure_set(set, entries[0], disabled),
            _ => {
                let avoid = BTreeSet::new();
                let slices: Vec<BTreeSet<BlockId>> = entries
                    .iter()
                    .map(|&e| self.reach(e, &set, &avoid))
                    .collect();
                let mut covered: BTreeSet<BlockId> = BTreeSet::new();
                let mut disjoint = true;
                for slice in &slices {
                    for &b in slice {
                        if !covered.insert(b) {
                            disjoint = false;
                        }
                    }
                }
                if !disjoint || covered != set {
                    self.escape_hatches.push(EscapeHatch::MultiEntry {
                        blocks: set.iter().copied().collect(),
                        entries,
                    });
                    self.irreducible_node(&set)
                } else {
                    let arms: Vec<RegionId> = entries
                        .iter()
                        .zip(slices)
                        .map(|(&e, slice)| {
                            let body = self.structure_set(slice, e, disabled);
                            self.push_node(RegionNode::Labeled { label: e, body })
                        })
                        .collect();
                    self.push_node(RegionNode::Alternates(arms))
                }
            }
        }
    }

    /// Acyclic structuring: iterative straight-line runs, conditional
    /// splits at two-successor heads, loop headers handed back to
    /// [`Builder::structure_set`].
    fn structure_acyclic(
        &mut self,
        set: BTreeSet<BlockId>,
        entry: BlockId,
        disabled: &BTreeSet<BlockId>,
    ) -> RegionId {
        let mut items: Vec<RegionId> = Vec::new();
        let mut rest = set;
        let mut cur = entry;
        loop {
            // A loop header reached mid-run: hand the whole remainder over
            // (the peel structures it and its continuation).
            if !disabled.contains(&cur) && self.preds[cur.index()].iter().any(|p| rest.contains(p))
            {
                let r = self.structure_set(rest, cur, disabled);
                items.push(r);
                return self.wrap_seq(items);
            }
            rest.remove(&cur);
            let succs_in: Vec<BlockId> = self.succs[cur.index()]
                .iter()
                .copied()
                .filter(|s| rest.contains(s))
                .collect();
            match succs_in.len() {
                0 => {
                    items.push(self.push_node(RegionNode::Block(cur)));
                    break;
                }
                1 => {
                    items.push(self.push_node(RegionNode::Block(cur)));
                    cur = succs_in[0];
                }
                _ => {
                    let (t, f) = (succs_in[0], succs_in[1]);
                    // Two-arm conditional. The merge is the head's
                    // immediate post-dominator (when inside the region);
                    // arms are what each entry reaches without passing the
                    // merge AND without entering the other arm's entry —
                    // the es2abc idiom `if (c0) goto shared; else {…}`
                    // makes one arm entry reachable from the other arm,
                    // and letting reachability flow through it would
                    // swallow the sibling arm (and, via bypass edges, the
                    // whole downstream).
                    let merge = self.postdom.ipostdom(cur).filter(|m| rest.contains(m));
                    let mut then_avoid: BTreeSet<BlockId> = merge.into_iter().collect();
                    then_avoid.insert(f);
                    let mut else_avoid: BTreeSet<BlockId> = merge.into_iter().collect();
                    else_avoid.insert(t);
                    let mut then_set = self.reach(t, &rest, &then_avoid);
                    let mut else_set = self.reach(f, &rest, &else_avoid);
                    // Blocks reachable from both arms without passing the
                    // merge are shared: demote them to the continuation,
                    // never duplicate.
                    let overlap: Vec<BlockId> = then_set.intersection(&else_set).copied().collect();
                    for b in overlap {
                        then_set.remove(&b);
                        else_set.remove(&b);
                    }
                    // Edges from one arm into the sibling arm (the
                    // goto-shared idiom) are recorded as cross-arm hints:
                    // the tree is truthful, and emission duplicates the
                    // shared block or merges the conditions (d-P3).
                    for (arm, sibling) in [(&then_set, &else_set), (&else_set, &then_set)] {
                        for &b in arm {
                            for &s in &self.succs[b.index()] {
                                if sibling.contains(&s) {
                                    self.cross_arms.push((b, s));
                                }
                            }
                        }
                    }
                    for b in &then_set {
                        rest.remove(b);
                    }
                    for b in &else_set {
                        rest.remove(b);
                    }
                    let then_r =
                        (!then_set.is_empty()).then(|| self.structure_set(then_set, t, disabled));
                    let else_r =
                        (!else_set.is_empty()).then(|| self.structure_set(else_set, f, disabled));
                    items.push(self.push_node(RegionNode::If {
                        head: cur,
                        then: then_r,
                        otherwise: else_r,
                        merge,
                    }));
                    if rest.is_empty() {
                        break;
                    }
                    let cont = self.structure_continuation(rest, disabled);
                    items.push(cont);
                    return self.wrap_seq(items);
                }
            }
        }
        // Defensive: with the single-entry invariant every block is
        // consumed; record and collapse anything left over.
        if !rest.is_empty() {
            self.escape_hatches.push(EscapeHatch::Stranded {
                blocks: rest.iter().copied().collect(),
            });
            let r = self.irreducible_node(&rest);
            items.push(r);
        }
        self.wrap_seq(items)
    }
}

/// Classify one Normal edge against the loop forest.
fn classify_edge(
    u: BlockId,
    v: BlockId,
    loops: &[LoopInfo],
    rpo_index: &BTreeMap<BlockId, usize>,
    escapes: &mut Vec<EscapeHatch>,
) -> EdgeClass {
    let containing: Vec<usize> = loops
        .iter()
        .enumerate()
        .filter(|(_, l)| l.blocks.contains(&u))
        .map(|(i, _)| i)
        .collect();
    let key = |i: usize| (loops[i].blocks.len(), loops[i].header);
    let innermost = containing.iter().copied().min_by_key(|&i| key(i));
    if let Some(&target) = containing.iter().find(|&&i| loops[i].header == v) {
        return EdgeClass::Continue {
            header: v,
            labeled: innermost != Some(target),
        };
    }
    let outermost_exited = containing
        .iter()
        .copied()
        .filter(|&i| !loops[i].blocks.contains(&v))
        .max_by_key(|&i| key(i));
    if let Some(outer) = outermost_exited {
        return EdgeClass::Break {
            header: loops[outer].header,
            labeled: innermost != Some(outer),
        };
    }
    // Not a loop edge. A backward edge here means a cycle the forest did
    // not claim (irreducible) — record it.
    if rpo_index.get(&v) < rpo_index.get(&u) {
        escapes.push(EscapeHatch::CrossEdge { from: u, to: v });
    }
    EdgeClass::Internal
}

/// Find one cycle in the graph minus `removed` edges, deterministically
/// (start nodes in sorted order, successors in terminator order). Returns
/// the cycle's blocks (sorted) and edges (cycle order).
fn find_cycle(
    universe: &BTreeSet<BlockId>,
    succs: &[Vec<BlockId>],
    removed: &BTreeSet<(BlockId, BlockId)>,
) -> Option<(Vec<BlockId>, Vec<(BlockId, BlockId)>)> {
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        Gray,
        Black,
    }
    let mut state: BTreeMap<BlockId, Color> = BTreeMap::new();
    for &start in universe {
        if state.contains_key(&start) {
            continue;
        }
        // Iterative DFS with an explicit path stack.
        let mut path: Vec<BlockId> = Vec::new();
        let mut stack: Vec<(BlockId, usize)> = vec![(start, 0)];
        state.insert(start, Color::Gray);
        path.push(start);
        while let Some((node, next)) = stack.last_mut() {
            let node = *node;
            let mut advanced = false;
            while *next < succs[node.index()].len() {
                let s = succs[node.index()][*next];
                *next += 1;
                if removed.contains(&(node, s)) || !universe.contains(&s) {
                    continue;
                }
                match state.get(&s) {
                    None => {
                        state.insert(s, Color::Gray);
                        stack.push((s, 0));
                        path.push(s);
                        advanced = true;
                        break;
                    }
                    Some(Color::Gray) => {
                        // Cycle: the path segment from s to node, closed by
                        // (node → s).
                        let pos = path.iter().position(|&b| b == s).expect("gray on path");
                        let mut blocks: Vec<BlockId> = path[pos..].to_vec();
                        let mut edges: Vec<(BlockId, BlockId)> =
                            blocks.windows(2).map(|w| (w[0], w[1])).collect();
                        edges.push((node, s));
                        blocks.sort();
                        return Some((blocks, edges));
                    }
                    Some(Color::Black) => {}
                }
            }
            if !advanced {
                state.insert(node, Color::Black);
                stack.pop();
                path.pop();
            }
        }
    }
    None
}

/// Project `TryRegion`s onto the finished tree and run the containment
/// assertions (module docs, "TryRegion containment").
fn project_try_regions(
    module: &Module,
    f: &abcd_ir::function::FunctionData,
    func_entry: BlockId,
    universe: &BTreeSet<BlockId>,
    nodes: Option<&[RegionNode]>,
    root: Option<RegionId>,
) -> (Vec<TryPlan>, Vec<RegionError>) {
    // Unfiltered in-function Normal predecessors: the entry assertion must
    // see handler-side sub-CFGs, whose blocks are unreachable from the
    // function entry over Normal edges (the N45 model) and therefore not
    // in the structuring universe.
    let normal_preds = |b: BlockId| -> Vec<BlockId> {
        module
            .block(b)
            .map(|bb| {
                bb.preds
                    .iter()
                    .filter(|e| e.kind == EdgeKind::Normal && f.blocks.contains(&e.from))
                    .map(|e| e.from)
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut plans = Vec::new();
    let mut errors = Vec::new();
    let mut earlier: Vec<BTreeSet<BlockId>> = Vec::new();
    for (i, tr) in f.try_regions.iter().enumerate() {
        let protected: BTreeSet<BlockId> = tr.protected.iter().copied().collect();
        let handlers: Vec<BlockId> = tr.catches.iter().map(|c| c.handler).collect();
        for &h in &handlers {
            if protected.contains(&h) {
                errors.push(RegionError::HandlerInsideProtected {
                    region: i,
                    handler: h,
                });
            }
        }
        for (j, prev) in earlier.iter().enumerate() {
            let inter: BTreeSet<_> = protected.intersection(prev).collect();
            if !inter.is_empty() && !protected.is_subset(prev) && !prev.is_subset(&protected) {
                errors.push(RegionError::InterleavedTryRegions { a: j, b: i });
            }
        }
        earlier.push(protected.clone());

        // Single-entry assertion, per Normal-connected component of the
        // protected sub-CFG: each component must have at most one NORMAL
        // entry — a block that is the function entry or has a Normal
        // predecessor outside the protected set. Components with zero
        // Normal entries are dispatch-entered handler-side sub-CFGs (an
        // outer try legitimately protects inner catch-handler blocks,
        // whose predecessors are exceptional) or dead cycles — not a
        // containment violation.
        let mut surface_entry: Option<BlockId> = None;
        let mut unseen: BTreeSet<BlockId> = protected.clone();
        while let Some(&start) = unseen.iter().next() {
            // One undirected Normal-connected component within protected.
            let mut component = vec![start];
            let mut queue = VecDeque::from([start]);
            unseen.remove(&start);
            while let Some(b) = queue.pop_front() {
                for nb in normal_preds(b).into_iter().chain(block_succs(module, b)) {
                    if protected.contains(&nb) && unseen.remove(&nb) {
                        component.push(nb);
                        queue.push_back(nb);
                    }
                }
            }
            let entries: Vec<BlockId> = component
                .iter()
                .copied()
                .filter(|&b| {
                    b == func_entry || normal_preds(b).iter().any(|p| !protected.contains(p))
                })
                .collect();
            if entries.len() > 1 {
                errors.push(RegionError::TryMultipleEntries {
                    region: i,
                    entries: entries.clone(),
                });
            }
            // The plan entry is the Normal entry of the component
            // containing the region's first protected block (or its first
            // block, for dispatch-entered components).
            if component.contains(&tr.protected[0]) {
                surface_entry = match entries.len() {
                    1 => Some(entries[0]),
                    0 => Some(component[0]),
                    _ => None,
                };
            }
        }

        // Tree projection walk over the reachable protected blocks:
        // records the span (the smallest node containing the protected
        // set) and whether the boundary cuts a Loop/Irreducible node
        // (an emission observation, not an error — see
        // [`TryPlan::cuts_structured_region`]).
        let p_eff: BTreeSet<BlockId> = protected.intersection(universe).copied().collect();
        let mut span = None;
        let mut cuts = false;
        if let (Some(nodes), Some(root_id), false) = (nodes, root, p_eff.is_empty()) {
            walk_region(nodes, root_id, &p_eff, &mut span, &mut cuts);
        }

        plans.push(TryPlan {
            region: i,
            entry: surface_entry,
            protected: protected.into_iter().collect(),
            handlers,
            span,
            cuts_structured_region: cuts,
        });
    }
    (plans, errors)
}

/// Recursive containment walk: returns `(protected blocks inside, total
/// blocks inside)` for the subtree, records the smallest node containing
/// the whole protected set in `span`, and sets `cuts` when a Loop or
/// Irreducible node is partially protected (see
/// [`TryPlan::cuts_structured_region`]).
fn walk_region(
    nodes: &[RegionNode],
    id: RegionId,
    p: &BTreeSet<BlockId>,
    span: &mut Option<RegionId>,
    cuts: &mut bool,
) -> (usize, usize) {
    let node = &nodes[id.index()];
    let (in_p, total) = match node {
        RegionNode::Block(b) => (usize::from(p.contains(b)), 1),
        RegionNode::Irreducible { blocks, .. } => (
            blocks.iter().filter(|b| p.contains(b)).count(),
            blocks.len(),
        ),
        RegionNode::Seq(children) | RegionNode::Alternates(children) => {
            walk_children(nodes, children, p, span, cuts)
        }
        RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
            walk_region(nodes, *body, p, span, cuts)
        }
        RegionNode::If {
            head,
            then,
            otherwise,
            ..
        } => {
            let mut total = (usize::from(p.contains(head)), 1);
            for child in [then, otherwise].into_iter().flatten() {
                let c = walk_region(nodes, *child, p, span, cuts);
                total.0 += c.0;
                total.1 += c.1;
            }
            total
        }
    };
    if matches!(
        node,
        RegionNode::Loop { .. } | RegionNode::Irreducible { .. }
    ) && in_p > 0
        && in_p < total
    {
        *cuts = true;
    }
    // Deepest node containing the whole protected set wins.
    if in_p == p.len() && span.is_none() {
        *span = Some(id);
    }
    (in_p, total)
}

fn walk_children(
    nodes: &[RegionNode],
    children: &[RegionId],
    p: &BTreeSet<BlockId>,
    span: &mut Option<RegionId>,
    cuts: &mut bool,
) -> (usize, usize) {
    let mut total = (0, 0);
    for &c in children {
        let r = walk_region(nodes, c, p, span, cuts);
        total.0 += r.0;
        total.1 += r.1;
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::Op;

    /// `cond`-terminated block helper.
    fn cond_branch(m: &mut abcd_ir::Module, b: BlockId, t: BlockId, f: BlockId) {
        let c = load_number(m, b, 1.0);
        emit_void(
            m,
            b,
            Op::CondBranch {
                cond: c,
                true_dest: t,
                false_dest: f,
            },
        );
    }

    fn branch(m: &mut abcd_ir::Module, b: BlockId, to: BlockId) {
        emit_void(m, b, Op::Branch { dest: to });
    }

    fn ret(m: &mut abcd_ir::Module, b: BlockId) {
        emit_void(m, b, Op::Return { value: None });
    }

    /// Find a classified edge.
    fn edge(tree: &RegionTree, from: BlockId, to: BlockId) -> EdgeClass {
        tree.edges
            .iter()
            .find(|e| e.from == from && e.to == to)
            .unwrap_or_else(|| panic!("edge {from:?} -> {to:?} not classified"))
            .class
    }

    /// The single Loop node of the tree, if exactly one.
    fn loops_in(tree: &RegionTree) -> Vec<&RegionNode> {
        tree.nodes()
            .iter()
            .filter(|n| matches!(n, RegionNode::Loop { .. }))
            .collect()
    }

    /// Diamond: entry → {a, b} → join → exit.
    #[test]
    fn diamond_conditional() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let a = add_block(&mut m, f);
        let b = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        cond_branch(&mut m, entry, a, b);
        branch(&mut m, a, join);
        branch(&mut m, b, join);
        branch(&mut m, join, exit);
        ret(&mut m, exit);
        link(&mut m, entry, a);
        link(&mut m, entry, b);
        link(&mut m, a, join);
        link(&mut m, b, join);
        link(&mut m, join, exit);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
        assert!(tree.loops.is_empty());
        let RegionNode::Seq(items) = tree.root_node().unwrap() else {
            panic!("root must be Seq: {:?}", tree.root_node());
        };
        let RegionNode::If {
            head,
            then,
            otherwise,
            merge,
        } = tree.node(items[0])
        else {
            panic!("first item must be If: {:?}", tree.node(items[0]));
        };
        assert_eq!(*head, entry);
        assert_eq!(*merge, Some(join));
        assert_eq!(then.map(|r| tree.node(r)), Some(&RegionNode::Block(a)));
        assert_eq!(otherwise.map(|r| tree.node(r)), Some(&RegionNode::Block(b)));
        // Continuation: join → exit.
        let RegionNode::Seq(cont) = tree.node(items[1]) else {
            panic!("continuation must be Seq: {:?}", tree.node(items[1]));
        };
        assert_eq!(tree.node(cont[0]), &RegionNode::Block(join));
        assert_eq!(tree.node(cont[1]), &RegionNode::Block(exit));
        // All five edges are internal flow.
        for e in &tree.edges {
            assert_eq!(e.class, EdgeClass::Internal, "{e:?}");
        }
    }

    /// Nested loops: entry → outer-header → {inner-header, exit};
    /// inner-header → {inner-body, outer-latch}; inner-body → inner-header;
    /// outer-latch → outer-header.
    #[test]
    fn nested_loops() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let oh = add_block(&mut m, f);
        let ih = add_block(&mut m, f);
        let ib = add_block(&mut m, f);
        let ol = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        branch(&mut m, entry, oh);
        cond_branch(&mut m, oh, ih, exit);
        cond_branch(&mut m, ih, ib, ol);
        branch(&mut m, ib, ih);
        branch(&mut m, ol, oh);
        ret(&mut m, exit);
        link(&mut m, entry, oh);
        link(&mut m, oh, ih);
        link(&mut m, oh, exit);
        link(&mut m, ih, ib);
        link(&mut m, ih, ol);
        link(&mut m, ib, ih);
        link(&mut m, ol, oh);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
        assert!(tree.irreducible.is_empty());
        assert_eq!(tree.loops.len(), 2);
        // Both headers carry the exit test.
        assert!(tree.loops.iter().all(|l| l.kind == LoopKind::While));
        // Nesting: inner ⊆ outer, parent link set.
        let inner = tree.loops.iter().find(|l| l.header == ih).unwrap();
        let outer = tree.loops.iter().find(|l| l.header == oh).unwrap();
        assert_eq!(inner.blocks, vec![ih, ib]);
        assert_eq!(outer.blocks.len(), 4);
        let outer_idx = tree.loops.iter().position(|l| l.header == oh).unwrap();
        assert_eq!(inner.parent, Some(outer_idx));
        assert_eq!(outer.parent, None);
        // Two Loop nodes, the inner nested under the outer's body.
        assert_eq!(loops_in(&tree).len(), 2);
        // Edge classes: plain continues.
        assert_eq!(
            edge(&tree, ib, ih),
            EdgeClass::Continue {
                header: ih,
                labeled: false
            }
        );
        assert_eq!(
            edge(&tree, ol, oh),
            EdgeClass::Continue {
                header: oh,
                labeled: false
            }
        );
        assert_eq!(
            edge(&tree, oh, exit),
            EdgeClass::Break {
                header: oh,
                labeled: false
            }
        );
        // ih → ol leaves the inner loop (ol is the outer latch): unlabeled
        // break from the inner loop.
        assert_eq!(
            edge(&tree, ih, ol),
            EdgeClass::Break {
                header: ih,
                labeled: false
            }
        );
    }

    /// Labeled multi-exit: an inner-loop block breaks out of the OUTER loop
    /// (labeled break) and another continues the outer loop (labeled
    /// continue).
    ///
    /// entry → oh → {ih, after}; ih → {ib, ol}; ib → {after, ib2};
    /// ib2 → {oh, ih}; ol → oh; after returns.
    #[test]
    fn labeled_break_and_continue() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let oh = add_block(&mut m, f);
        let ih = add_block(&mut m, f);
        let ib = add_block(&mut m, f);
        let ib2 = add_block(&mut m, f);
        let ol = add_block(&mut m, f);
        let after = add_block(&mut m, f);
        branch(&mut m, entry, oh);
        cond_branch(&mut m, oh, ih, after);
        cond_branch(&mut m, ih, ib, ol);
        cond_branch(&mut m, ib, after, ib2);
        cond_branch(&mut m, ib2, oh, ih);
        branch(&mut m, ol, oh);
        ret(&mut m, after);
        for (u, v) in [
            (entry, oh),
            (oh, ih),
            (oh, after),
            (ih, ib),
            (ih, ol),
            (ib, after),
            (ib, ib2),
            (ib2, oh),
            (ib2, ih),
            (ol, oh),
        ] {
            link(&mut m, u, v);
        }

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert!(tree.irreducible.is_empty(), "{:?}", tree.irreducible);
        assert_eq!(tree.loops.len(), 2);
        // ib → after breaks out of BOTH loops: labeled by the outer header.
        assert_eq!(
            edge(&tree, ib, after),
            EdgeClass::Break {
                header: oh,
                labeled: true
            }
        );
        // ib2 → oh continues the OUTER loop across the inner: labeled.
        assert_eq!(
            edge(&tree, ib2, oh),
            EdgeClass::Continue {
                header: oh,
                labeled: true
            }
        );
        // ib2 → ih is the inner loop's plain continue.
        assert_eq!(
            edge(&tree, ib2, ih),
            EdgeClass::Continue {
                header: ih,
                labeled: false
            }
        );
        // oh → after exits only the outer loop: unlabeled break.
        assert_eq!(
            edge(&tree, oh, after),
            EdgeClass::Break {
                header: oh,
                labeled: false
            }
        );
        // Determinism: a second run produces an identical tree.
        let again = structure_regions(&m, f);
        assert_eq!(tree, again);
    }

    /// Switch-like multi-way: a cascade of two-way conditionals reconverging
    /// at a common join.
    #[test]
    fn switch_like_cascade() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let c1 = add_block(&mut m, f);
        let d2 = add_block(&mut m, f);
        let c2 = add_block(&mut m, f);
        let c3 = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        cond_branch(&mut m, entry, c1, d2);
        cond_branch(&mut m, d2, c2, c3);
        branch(&mut m, c1, join);
        branch(&mut m, c2, join);
        branch(&mut m, c3, join);
        ret(&mut m, join);
        link(&mut m, entry, c1);
        link(&mut m, entry, d2);
        link(&mut m, d2, c2);
        link(&mut m, d2, c3);
        link(&mut m, c1, join);
        link(&mut m, c2, join);
        link(&mut m, c3, join);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
        let RegionNode::Seq(items) = tree.root_node().unwrap() else {
            panic!("root must be Seq");
        };
        let RegionNode::If {
            head,
            then,
            otherwise,
            merge,
        } = tree.node(items[0])
        else {
            panic!("first item must be If");
        };
        assert_eq!(*head, entry);
        assert_eq!(*merge, Some(join));
        assert_eq!(then.map(|r| tree.node(r)), Some(&RegionNode::Block(c1)));
        // The else arm is the nested dispatch conditional.
        let RegionNode::If {
            head: h2,
            then: t2,
            otherwise: o2,
            merge: m2,
        } = tree.node(otherwise.unwrap())
        else {
            panic!("else arm must be If");
        };
        assert_eq!(*h2, d2);
        assert_eq!(*m2, None); // the join lives outside the arm set
        assert_eq!(t2.map(|r| tree.node(r)), Some(&RegionNode::Block(c2)));
        assert_eq!(o2.map(|r| tree.node(r)), Some(&RegionNode::Block(c3)));
    }

    /// Try/handler: protected blocks structure normally; the handler is
    /// Normal-unreachable (dead for structuring) and appears in the TryPlan.
    #[test]
    fn try_handler_projection() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t2 = add_block(&mut m, f);
        let handler = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        branch(&mut m, entry, t2);
        branch(&mut m, t2, exit);
        ret(&mut m, exit);
        let exc = add_exception_param(&mut m, handler);
        emit_void(&mut m, handler, Op::Return { value: Some(exc) });
        link(&mut m, entry, t2);
        link(&mut m, t2, exit);
        add_try(&mut m, f, vec![entry, t2], handler, exc);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert_eq!(tree.dead_blocks, vec![handler]);
        assert_eq!(tree.try_plans.len(), 1);
        let plan = &tree.try_plans[0];
        assert_eq!(plan.region, 0);
        assert_eq!(plan.entry, Some(entry));
        assert_eq!(plan.protected, vec![entry, t2]);
        assert_eq!(plan.handlers, vec![handler]);
        assert_eq!(plan.span, tree.root);
    }

    /// Interleaved try regions are a hard error (reported, never panicked).
    #[test]
    fn interleaved_try_regions_are_hard_errors() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let b = add_block(&mut m, f);
        let c = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        let h1 = add_block(&mut m, f);
        let h2 = add_block(&mut m, f);
        branch(&mut m, entry, b);
        branch(&mut m, b, c);
        branch(&mut m, c, exit);
        ret(&mut m, exit);
        let e1 = add_exception_param(&mut m, h1);
        ret(&mut m, h1);
        let e2 = add_exception_param(&mut m, h2);
        ret(&mut m, h2);
        link(&mut m, entry, b);
        link(&mut m, b, c);
        link(&mut m, c, exit);
        // {entry, b} and {b, c} intersect without nesting.
        add_try(&mut m, f, vec![entry, b], h1, e1);
        add_try(&mut m, f, vec![b, c], h2, e2);

        let tree = structure_regions(&m, f);
        assert!(
            tree.errors
                .iter()
                .any(|e| matches!(e, RegionError::InterleavedTryRegions { a: 0, b: 1 })),
            "{:?}",
            tree.errors
        );
    }

    /// Irreducible jump-into-loop: entry → {h, b}; h → b; b → {h, exit}.
    /// The cycle {h, b} has no dominating header (entry → b bypasses h), so
    /// there is no dominance back edge at all. Detected and reported, and
    /// structuring still produces a total tree.
    #[test]
    fn irreducible_jump_into_loop() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let h = add_block(&mut m, f);
        let b = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        cond_branch(&mut m, entry, h, b);
        branch(&mut m, h, b);
        cond_branch(&mut m, b, h, exit);
        ret(&mut m, exit);
        link(&mut m, entry, h);
        link(&mut m, entry, b);
        link(&mut m, h, b);
        link(&mut m, b, h);
        link(&mut m, b, exit);

        let tree = structure_regions(&m, f);
        assert!(tree.root.is_some());
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        // One irreducible core over exactly the cycle blocks.
        assert_eq!(tree.irreducible.len(), 1);
        assert_eq!(tree.irreducible[0].blocks, {
            let mut v = vec![h, b];
            v.sort();
            v
        });
        // No natural loops exist (no dominance back edge).
        assert!(tree.loops.is_empty());
        // The backward edge b → h is flagged as a cross edge, not a
        // continue.
        assert!(
            tree.escape_hatches.iter().any(
                |e| matches!(e, EscapeHatch::CrossEdge { from, to } if *from == b && *to == h)
            ),
            "{:?}",
            tree.escape_hatches
        );
        assert_eq!(edge(&tree, b, h), EdgeClass::Internal);
        // Determinism on the irreducible shape too.
        assert_eq!(tree, structure_regions(&m, f));
    }

    /// Self-loop on the entry block: `while (c) { … }` at the function
    /// entry.
    #[test]
    fn self_loop_entry() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let exit = add_block(&mut m, f);
        cond_branch(&mut m, entry, entry, exit);
        ret(&mut m, exit);
        link(&mut m, entry, entry);
        link(&mut m, entry, exit);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert_eq!(tree.loops.len(), 1);
        assert_eq!(tree.loops[0].kind, LoopKind::While);
        let RegionNode::Seq(items) = tree.root_node().unwrap() else {
            panic!("root must be Seq");
        };
        let RegionNode::Loop { header, kind, body } = tree.node(items[0]) else {
            panic!("first item must be Loop: {:?}", tree.node(items[0]));
        };
        assert_eq!(*header, entry);
        assert_eq!(*kind, LoopKind::While);
        assert_eq!(tree.node(*body), &RegionNode::Block(entry));
        assert_eq!(tree.node(items[1]), &RegionNode::Block(exit));
        assert_eq!(
            edge(&tree, entry, entry),
            EdgeClass::Continue {
                header: entry,
                labeled: false
            }
        );
        assert_eq!(
            edge(&tree, entry, exit),
            EdgeClass::Break {
                header: entry,
                labeled: false
            }
        );
    }

    /// do-while: header falls through unconditionally, the latch carries
    /// the exit test.
    #[test]
    fn do_while_kind() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let h = add_block(&mut m, f);
        let b = add_block(&mut m, f);
        let exit = add_block(&mut m, f);
        branch(&mut m, entry, h);
        branch(&mut m, h, b);
        cond_branch(&mut m, b, h, exit);
        ret(&mut m, exit);
        link(&mut m, entry, h);
        link(&mut m, h, b);
        link(&mut m, b, h);
        link(&mut m, b, exit);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert_eq!(tree.loops.len(), 1);
        assert_eq!(tree.loops[0].kind, LoopKind::DoWhile);
        let loops = loops_in(&tree);
        assert_eq!(loops.len(), 1);
        assert!(matches!(
            loops[0],
            RegionNode::Loop {
                kind: LoopKind::DoWhile,
                header,
                ..
            } if *header == h
        ));
    }

    /// Multi-entry continuation: a loop whose two exit edges target
    /// disjoint tails. The remainder becomes labeled alternates.
    #[test]
    fn multi_exit_alternates() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let h = add_block(&mut m, f);
        let body = add_block(&mut m, f);
        let tail_a = add_block(&mut m, f);
        let tail_b = add_block(&mut m, f);
        branch(&mut m, entry, h);
        cond_branch(&mut m, h, body, tail_a);
        cond_branch(&mut m, body, h, tail_b);
        ret(&mut m, tail_a);
        ret(&mut m, tail_b);
        link(&mut m, entry, h);
        link(&mut m, h, body);
        link(&mut m, h, tail_a);
        link(&mut m, body, h);
        link(&mut m, body, tail_b);

        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty(), "{:?}", tree.errors);
        assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
        let RegionNode::Seq(items) = tree.root_node().unwrap() else {
            panic!("root must be Seq");
        };
        // [Block(entry), Seq[Loop, Alternates]] — the straight-line entry
        // peel precedes the loop.
        assert_eq!(tree.node(items[0]), &RegionNode::Block(entry));
        let RegionNode::Seq(inner) = tree.node(items[1]) else {
            panic!("second item must be Seq: {:?}", tree.node(items[1]));
        };
        assert!(matches!(tree.node(inner[0]), RegionNode::Loop { .. }));
        let RegionNode::Alternates(arms) = tree.node(inner[1]) else {
            panic!("continuation must be Alternates: {:?}", tree.node(inner[1]));
        };
        assert_eq!(arms.len(), 2);
        let labels: Vec<BlockId> = arms
            .iter()
            .map(|&a| match tree.node(a) {
                RegionNode::Labeled { label, .. } => *label,
                n => panic!("arm must be Labeled: {n:?}"),
            })
            .collect();
        assert_eq!(labels, {
            let mut v = vec![tail_a, tail_b];
            v.sort();
            v
        });
        assert_eq!(
            edge(&tree, h, tail_a),
            EdgeClass::Break {
                header: h,
                labeled: false
            }
        );
        assert_eq!(
            edge(&tree, body, tail_b),
            EdgeClass::Break {
                header: h,
                labeled: false
            }
        );
        assert_eq!(
            edge(&tree, body, h),
            EdgeClass::Continue {
                header: h,
                labeled: false
            }
        );
    }

    /// Degenerate shape: a bare-return function structures to one Block.
    #[test]
    fn bare_return_is_single_block() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        ret(&mut m, entry);
        let tree = structure_regions(&m, f);
        assert!(tree.errors.is_empty());
        assert_eq!(tree.root_node(), Some(&RegionNode::Block(entry)));
        assert!(tree.edges.is_empty());
        assert!(tree.loops.is_empty());
    }
}
