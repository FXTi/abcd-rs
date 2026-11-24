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

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

use abcd_ir::{BlockId, EdgeKind, FuncId, Module, TryRegion};

use super::dom::{Dominators, PostDominators};
use super::loops::back_edges_in_blocks;
use super::reach::reachable_from;
use super::succs::block_succs;

/// Fixed-width dense bitset over `0..u_len` universe block indices.
///
/// Because `u_blocks` is sorted by [`BlockId`], iterating set bits in
/// ascending word/bit order yields elements in exact `BTreeSet<BlockId>`
/// order while replacing heap-allocated B-tree operations with `O(|U|/64)`
/// word bitwise operations.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BitSet {
    words: Vec<u64>,
    len: usize,
}

impl BitSet {
    #[inline]
    fn empty(word_len: usize) -> Self {
        Self {
            words: vec![0u64; word_len],
            len: 0,
        }
    }

    #[inline]
    fn full(u_len: usize, word_len: usize) -> Self {
        let mut words = vec![!0u64; word_len];
        let rem = u_len & 63;
        if rem != 0
            && let Some(last) = words.last_mut()
        {
            *last = (1u64 << rem) - 1;
        }
        Self { words, len: u_len }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    fn contains(&self, idx: u32) -> bool {
        (self.words[(idx >> 6) as usize] & (1u64 << (idx & 63))) != 0
    }

    #[inline]
    fn insert(&mut self, idx: u32) -> bool {
        let w = &mut self.words[(idx >> 6) as usize];
        let mask = 1u64 << (idx & 63);
        if (*w & mask) == 0 {
            *w |= mask;
            self.len += 1;
            true
        } else {
            false
        }
    }

    #[inline]
    fn remove(&mut self, idx: u32) -> bool {
        let w = &mut self.words[(idx >> 6) as usize];
        let mask = 1u64 << (idx & 63);
        if (*w & mask) != 0 {
            *w &= !mask;
            self.len -= 1;
            true
        } else {
            false
        }
    }

    fn remove_all(&mut self, other: &BitSet) {
        if other.len == 0 || self.len == 0 {
            return;
        }
        let mut removed = 0usize;
        for (w, &ow) in self.words.iter_mut().zip(other.words.iter()) {
            let ov = *w & ow;
            if ov != 0 {
                *w &= !ow;
                removed += ov.count_ones() as usize;
            }
        }
        self.len -= removed;
    }

    fn intersect_with(&mut self, other: &BitSet) {
        let mut new_len = 0usize;
        for (w, &ow) in self.words.iter_mut().zip(other.words.iter()) {
            *w &= ow;
            new_len += w.count_ones() as usize;
        }
        self.len = new_len;
    }

    fn difference(&self, other: &BitSet) -> BitSet {
        let mut words = Vec::with_capacity(self.words.len());
        let mut len = 0usize;
        for (&w, &ow) in self.words.iter().zip(other.words.iter()) {
            let d = w & !ow;
            len += d.count_ones() as usize;
            words.push(d);
        }
        BitSet { words, len }
    }

    fn is_subset(&self, sup: &BitSet) -> bool {
        if self.len > sup.len {
            return false;
        }
        for (&w, &sw) in self.words.iter().zip(sup.words.iter()) {
            if (w & !sw) != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    fn iter(&self) -> BitSetIter<'_> {
        BitSetIter {
            words: &self.words,
            wi: 0,
            cur: 0,
        }
    }

    fn to_blocks(&self, u_blocks: &[BlockId]) -> Vec<BlockId> {
        let mut out = Vec::with_capacity(self.len);
        for bi in self.iter() {
            out.push(u_blocks[bi as usize]);
        }
        out
    }
}

struct BitSetIter<'a> {
    words: &'a [u64],
    wi: usize,
    cur: u64,
}

impl Iterator for BitSetIter<'_> {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<u32> {
        while self.cur == 0 {
            if self.wi >= self.words.len() {
                return None;
            }
            self.cur = self.words[self.wi];
            self.wi += 1;
        }
        let tz = self.cur.trailing_zeros();
        self.cur &= self.cur - 1;
        Some(((self.wi - 1) as u32) * 64 + tz)
    }
}

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

    // Parent links: the smallest strict superset loop (`O(|U|/64)` word subset test).
    for i in 0..loops.len() {
        let i_len = loops[i].blocks.len();
        if loop_bits[i].is_empty() {
            continue;
        }
        let mut parent: Option<usize> = None;
        for j in 0..loops.len() {
            let j_len = loops[j].blocks.len();
            if i == j || j_len <= i_len || loop_bits[j].is_empty() {
                continue;
            }
            if let Some(p) = parent
                && loops[p].blocks.len() <= j_len
            {
                continue;
            }
            if loop_bits[i].is_subset(&loop_bits[j]) {
                parent = Some(j);
            }
        }
        loops[i].parent = parent;
    }

    // Irreducible cores: cycles in the graph minus dominance back edges.
    let mut removed: HashSet<(u32, u32)> = HashSet::with_capacity(be.len() * 2);
    for &(u, v) in &be {
        if let (Some(&ui), Some(&vi)) = (u_idx.get(&u), u_idx.get(&v)) {
            removed.insert((ui, vi));
        }
    }
    let mut irreducible = Vec::new();
    while let Some((blocks, cycle_edges_idx)) = find_cycle(u_len, &u_blocks, &succs, &removed) {
        let mut cycle_edges = Vec::with_capacity(cycle_edges_idx.len());
        for (ui, vi) in cycle_edges_idx {
            removed.insert((ui, vi));
            cycle_edges.push((u_blocks[ui as usize], u_blocks[vi as usize]));
        }
        irreducible.push(IrreducibleCore {
            blocks,
            cycle_edges,
        });
    }

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

    /// The merge of the loop with (natural) body `body`: the nearest
    /// common post-dominator of the loop's exit targets, excluding targets
    /// that leave the function (Return/Throw leaves — they are loop exits
    /// but not continuations). `None` for infinite loops and for loops
    /// whose exit tails never reconverge (those structure as
    /// [`RegionNode::Alternates`] continuations).
    fn loop_merge(&self, body: &BitSet) -> Option<BlockId> {
        let mut targets = BitSet::empty(self.word_len);
        for b in body.iter() {
            for &s in &self.succs[b as usize] {
                if !body.contains(s) && !self.succs[s as usize].is_empty() {
                    targets.insert(s);
                }
            }
        }
        let mut iter = targets.iter();
        let first = self.u_blocks[iter.next()? as usize];
        let mut chain = self.postdom.post_dominator_chain(first);
        for ti in iter {
            let t = self.u_blocks[ti as usize];
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

/// Classify one Normal edge against the loop forest using `O(1)` bitset
/// membership queries.
#[allow(clippy::too_many_arguments)]
fn classify_edge(
    u: BlockId,
    ui: u32,
    v: BlockId,
    vi: u32,
    loops: &[LoopInfo],
    loop_bits: &[BitSet],
    header_loop: &[Option<usize>],
    innermost_loop: &[Option<usize>],
    loops_desc: &[usize],
    rpo_pos: &[Option<usize>],
    escapes: &mut Vec<EscapeHatch>,
) -> EdgeClass {
    if let Some(inner) = innermost_loop[ui as usize] {
        if let Some(target) = header_loop[vi as usize]
            && loop_bits[target].contains(ui)
        {
            return EdgeClass::Continue {
                header: v,
                labeled: inner != target,
            };
        }
        if let Some(outer) = loops_desc
            .iter()
            .copied()
            .find(|&li| loop_bits[li].contains(ui) && !loop_bits[li].contains(vi))
        {
            return EdgeClass::Break {
                header: loops[outer].header,
                labeled: inner != outer,
            };
        }
    }
    // Not a loop edge. A backward edge here means a cycle the forest did
    // not claim (irreducible) — record it.
    if rpo_pos[vi as usize] < rpo_pos[ui as usize] {
        escapes.push(EscapeHatch::CrossEdge { from: u, to: v });
    }
    EdgeClass::Internal
}

/// A cycle witness: the cycle's blocks (sorted) and dense edges (cycle order).
type CycleWitness = (Vec<BlockId>, Vec<(u32, u32)>);

/// Find one cycle in the graph minus `removed` edges, deterministically
/// (start nodes in sorted order, successors in terminator order). Returns
/// the cycle's blocks (sorted) and dense edges (cycle order).
fn find_cycle(
    u_len: usize,
    u_blocks: &[BlockId],
    succs: &[Vec<u32>],
    removed: &HashSet<(u32, u32)>,
) -> Option<CycleWitness> {
    let mut state: Vec<u8> = vec![0u8; u_len]; // 0 = Unvisited, 1 = Gray, 2 = Black
    let mut path: Vec<u32> = Vec::new();
    let mut stack: Vec<(u32, usize)> = Vec::new();
    for start in 0..u_len as u32 {
        if state[start as usize] != 0 {
            continue;
        }
        path.clear();
        stack.clear();
        stack.push((start, 0));
        state[start as usize] = 1;
        path.push(start);
        while let Some((node, next)) = stack.last_mut() {
            let node = *node;
            let node_succs = &succs[node as usize];
            let mut advanced = false;
            while *next < node_succs.len() {
                let s = node_succs[*next];
                *next += 1;
                if removed.contains(&(node, s)) {
                    continue;
                }
                match state[s as usize] {
                    0 => {
                        state[s as usize] = 1;
                        stack.push((s, 0));
                        path.push(s);
                        advanced = true;
                        break;
                    }
                    1 => {
                        // Cycle: the path segment from s to node, closed by (node → s).
                        let pos = path.iter().position(|&b| b == s).expect("gray on path");
                        let seg = &path[pos..];
                        let mut blocks: Vec<BlockId> =
                            seg.iter().map(|&bi| u_blocks[bi as usize]).collect();
                        let mut edges: Vec<(u32, u32)> =
                            seg.windows(2).map(|w| (w[0], w[1])).collect();
                        edges.push((node, s));
                        blocks.sort();
                        return Some((blocks, edges));
                    }
                    _ => {}
                }
            }
            if !advanced {
                state[node as usize] = 2;
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
    subgraph: &CfgSubgraph<'_>,
    func_entry: BlockId,
    u_idx: &HashMap<BlockId, u32>,
    word_len: usize,
    nodes: Option<&[RegionNode]>,
    root: Option<RegionId>,
) -> (Vec<TryPlan>, Vec<RegionError>) {
    let blocks = subgraph.blocks;
    let try_regions = subgraph.try_regions;
    let normal_succs = subgraph.succ;
    let block_set: HashSet<BlockId> = blocks.iter().copied().collect();
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
                    .filter(|e| e.kind == EdgeKind::Normal && block_set.contains(&e.from))
                    .map(|e| e.from)
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut plans = Vec::new();
    let mut errors = Vec::new();
    let mut earlier: Vec<BTreeSet<BlockId>> = Vec::new();
    for (i, tr) in try_regions.iter().enumerate() {
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
            let has_inter = protected.intersection(prev).next().is_some();
            if has_inter && !protected.is_subset(prev) && !prev.is_subset(&protected) {
                errors.push(RegionError::InterleavedTryRegions { a: j, b: i });
            }
        }
        earlier.push(protected.clone());

        // Single-entry assertion, per Normal-connected component of the
        // protected sub-CFG.
        let mut surface_entry: Option<BlockId> = None;
        let mut unseen: BTreeSet<BlockId> = protected.clone();
        let first_prot = tr.protected.first().copied();
        while let Some(&start) = unseen.iter().next() {
            // One undirected Normal-connected component within protected.
            let mut component = vec![start];
            let mut queue = VecDeque::from([start]);
            unseen.remove(&start);
            while let Some(b) = queue.pop_front() {
                for nb in normal_preds(b).into_iter().chain(normal_succs(b)) {
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
            if let Some(fp) = first_prot
                && component.contains(&fp)
            {
                surface_entry = match entries.len() {
                    1 => Some(entries[0]),
                    0 => Some(component[0]),
                    _ => None,
                };
            }
        }

        // Tree projection walk over the reachable protected blocks.
        let mut p_eff = BitSet::empty(word_len);
        for &b in &protected {
            if let Some(&bi) = u_idx.get(&b) {
                p_eff.insert(bi);
            }
        }
        let mut span = None;
        let mut cuts = false;
        if let (Some(nodes), Some(root_id), false) = (nodes, root, p_eff.is_empty()) {
            walk_region(nodes, root_id, u_idx, &p_eff, &mut span, &mut cuts);
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

/// Iterative containment walk (post-order over an explicit stack — the
/// tree depth is input-driven, so this must not recurse): returns
/// `(protected blocks inside, total blocks inside)` for the subtree,
/// records the smallest node containing the whole protected set in `span`,
/// and sets `cuts` when a Loop or Irreducible node is partially protected
/// (see [`TryPlan::cuts_structured_region`]).
fn walk_region(
    nodes: &[RegionNode],
    root: RegionId,
    u_idx: &HashMap<BlockId, u32>,
    p: &BitSet,
    span: &mut Option<RegionId>,
    cuts: &mut bool,
) -> (usize, usize) {
    /// Post-order scheduling: `Enter` pushes the node's `Exit` marker
    /// followed by its children (in reverse, so they run in order);
    /// `Exit` folds the children's results from `results` and applies the
    /// node-local bookkeeping, exactly the recursive post-order.
    enum W {
        Enter(RegionId),
        Exit(RegionId),
    }
    let in_prot = |b: BlockId| -> bool { u_idx.get(&b).is_some_and(|&bi| p.contains(bi)) };
    let mut stack = vec![W::Enter(root)];
    let mut results: Vec<(usize, usize)> = Vec::new();
    while let Some(w) = stack.pop() {
        match w {
            W::Enter(id) => {
                stack.push(W::Exit(id));
                match &nodes[id.index()] {
                    RegionNode::Block(_) | RegionNode::Irreducible { .. } => {}
                    RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                        for &c in children.iter().rev() {
                            stack.push(W::Enter(c));
                        }
                    }
                    RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                        stack.push(W::Enter(*body));
                    }
                    RegionNode::If {
                        then, otherwise, ..
                    } => {
                        // Child order: then, then otherwise.
                        if let Some(o) = otherwise {
                            stack.push(W::Enter(*o));
                        }
                        if let Some(t) = then {
                            stack.push(W::Enter(*t));
                        }
                    }
                }
            }
            W::Exit(id) => {
                let node = &nodes[id.index()];
                let (in_p, total) = match node {
                    RegionNode::Block(b) => (usize::from(in_prot(*b)), 1),
                    RegionNode::Irreducible { blocks, .. } => {
                        (blocks.iter().filter(|&&b| in_prot(b)).count(), blocks.len())
                    }
                    RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                        let mut total = (0, 0);
                        for r in results.drain(results.len() - children.len()..) {
                            total.0 += r.0;
                            total.1 += r.1;
                        }
                        total
                    }
                    RegionNode::Labeled { .. } | RegionNode::Loop { .. } => {
                        results.pop().expect("child result")
                    }
                    RegionNode::If {
                        head,
                        then,
                        otherwise,
                        ..
                    } => {
                        let n = usize::from(then.is_some()) + usize::from(otherwise.is_some());
                        let mut total = (usize::from(in_prot(*head)), 1);
                        for r in results.drain(results.len() - n..) {
                            total.0 += r.0;
                            total.1 += r.1;
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
                if in_p == p.len && span.is_none() {
                    *span = Some(id);
                }
                results.push((in_p, total));
            }
        }
    }
    results.pop().expect("root result")
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

    /// Stack-depth regression guard for the ASan corpus stack-overflow
    /// (lift-analysis gate, rayon worker thread): region structuring must
    /// be driven by an explicit heap stack, never by native recursion with
    /// input-driven depth. Deeply nested shapes must structure on a
    /// 256 KiB stack.
    ///
    /// `if (c1) { if (c2) { … } }` nesting, N levels deep: every level is
    /// a two-successor head whose then-arm contains the whole inner nest
    /// (an empty else, the merge chained to the outer merge).
    #[test]
    fn deep_nested_ifs_structure_on_small_stack() {
        const N: usize = 1000;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut m = mk_module();
                let f = add_func(&mut m);
                let h: Vec<BlockId> = (0..N)
                    .map(|i| {
                        if i == 0 {
                            entry_of(&m, f)
                        } else {
                            add_block(&mut m, f)
                        }
                    })
                    .collect();
                let leaf = add_block(&mut m, f);
                let merges: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
                let exit = add_block(&mut m, f);
                for i in 0..N - 1 {
                    cond_branch(&mut m, h[i], h[i + 1], merges[i]);
                    link(&mut m, h[i], h[i + 1]);
                    link(&mut m, h[i], merges[i]);
                }
                cond_branch(&mut m, h[N - 1], leaf, merges[N - 1]);
                link(&mut m, h[N - 1], leaf);
                link(&mut m, h[N - 1], merges[N - 1]);
                branch(&mut m, leaf, merges[N - 1]);
                link(&mut m, leaf, merges[N - 1]);
                for i in (1..N).rev() {
                    branch(&mut m, merges[i], merges[i - 1]);
                    link(&mut m, merges[i], merges[i - 1]);
                }
                branch(&mut m, merges[0], exit);
                link(&mut m, merges[0], exit);
                ret(&mut m, exit);

                let tree = structure_regions(&m, f);
                assert!(tree.errors.is_empty(), "{:?}", tree.errors);
                assert!(tree.root.is_some());
                assert!(tree.loops.is_empty());
                // Every block structured: 2N+2 block-carrying nodes.
                let covered = tree
                    .nodes()
                    .iter()
                    .filter(|n| matches!(n, RegionNode::Block(_) | RegionNode::If { .. }))
                    .count();
                assert_eq!(covered, 2 * N + 2);
            })
            .expect("spawn");
        handle
            .join()
            .expect("structuring must not overflow the stack");
    }

    /// Same guard through the loop-peel path: N nested `while` loops, each
    /// level's body being the next inner loop, exits chaining to the outer
    /// latch.
    #[test]
    fn deep_nested_loops_structure_on_small_stack() {
        const N: usize = 400;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut m = mk_module();
                let f = add_func(&mut m);
                let entry = entry_of(&m, f);
                let h: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
                let body = add_block(&mut m, f);
                let latches: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
                let exits: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
                let exit = add_block(&mut m, f);
                branch(&mut m, entry, h[0]);
                link(&mut m, entry, h[0]);
                for i in 0..N - 1 {
                    cond_branch(&mut m, h[i], h[i + 1], exits[i]);
                    link(&mut m, h[i], h[i + 1]);
                    link(&mut m, h[i], exits[i]);
                }
                cond_branch(&mut m, h[N - 1], body, exits[N - 1]);
                link(&mut m, h[N - 1], body);
                link(&mut m, h[N - 1], exits[N - 1]);
                branch(&mut m, body, latches[N - 1]);
                link(&mut m, body, latches[N - 1]);
                for i in 0..N {
                    branch(&mut m, latches[i], h[i]);
                    link(&mut m, latches[i], h[i]);
                }
                // An exit out of loop i lands on the outer latch (still
                // inside loop i-1's body); the outermost exit returns.
                for i in 1..N {
                    branch(&mut m, exits[i], latches[i - 1]);
                    link(&mut m, exits[i], latches[i - 1]);
                }
                branch(&mut m, exits[0], exit);
                link(&mut m, exits[0], exit);
                ret(&mut m, exit);

                let tree = structure_regions(&m, f);
                assert!(tree.errors.is_empty(), "{:?}", tree.errors);
                assert!(tree.root.is_some());
                assert_eq!(tree.loops.len(), N);
                // Determinism on the deep shape too.
                assert_eq!(tree, structure_regions(&m, f));
            })
            .expect("spawn");
        handle
            .join()
            .expect("structuring must not overflow the stack");
    }

    /// Same guard through the TryRegion projection walk: a protected set
    /// covering a deeply nested tree makes `walk_region` descend the full
    /// tree depth.
    #[test]
    fn deep_nested_tree_try_projection_on_small_stack() {
        const N: usize = 1000;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut m = mk_module();
                let f = add_func(&mut m);
                let h: Vec<BlockId> = (0..N)
                    .map(|i| {
                        if i == 0 {
                            entry_of(&m, f)
                        } else {
                            add_block(&mut m, f)
                        }
                    })
                    .collect();
                let leaf = add_block(&mut m, f);
                let merges: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
                let exit = add_block(&mut m, f);
                for i in 0..N - 1 {
                    cond_branch(&mut m, h[i], h[i + 1], merges[i]);
                    link(&mut m, h[i], h[i + 1]);
                    link(&mut m, h[i], merges[i]);
                }
                cond_branch(&mut m, h[N - 1], leaf, merges[N - 1]);
                link(&mut m, h[N - 1], leaf);
                link(&mut m, h[N - 1], merges[N - 1]);
                branch(&mut m, leaf, merges[N - 1]);
                link(&mut m, leaf, merges[N - 1]);
                for i in (1..N).rev() {
                    branch(&mut m, merges[i], merges[i - 1]);
                    link(&mut m, merges[i], merges[i - 1]);
                }
                branch(&mut m, merges[0], exit);
                link(&mut m, merges[0], exit);
                ret(&mut m, exit);
                // One try region protecting every structured block.
                let handler = add_block(&mut m, f);
                let exc = add_exception_param(&mut m, handler);
                ret(&mut m, handler);
                let protected: Vec<BlockId> = h
                    .iter()
                    .chain(std::iter::once(&leaf))
                    .chain(merges.iter())
                    .chain(std::iter::once(&exit))
                    .copied()
                    .collect();
                add_try(&mut m, f, protected, handler, exc);

                let tree = structure_regions(&m, f);
                assert!(tree.errors.is_empty(), "{:?}", tree.errors);
                assert_eq!(tree.try_plans.len(), 1);
                assert_eq!(tree.try_plans[0].span, tree.root);
            })
            .expect("spawn");
        handle
            .join()
            .expect("projection must not overflow the stack");
    }
}
