//! Structurer emission frames, `TryPlan` coverage memoization, and cut-split trees.

use super::*;

/// What follows a region in emission order (for the clean-loop-form
/// "exit target == structural continuation" check).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::structure) enum Follow {
    /// The region is last in its ancestor chain: plain `break` is
    /// correct wherever the ancestors route.
    Tail,
    /// The next region's first-executed block.
    Entry(BlockId),
    /// Unknown (an [`RegionNode::Alternates`] or irreducible node
    /// follows) — clean loop forms disabled.
    Unknown,
}

/// Where a duplicated cross-arm tail ends ([`Ctx::cross_arm_dup`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::structure) enum DupStop {
    /// The tail ends in a terminal (return/throw) — never falls through.
    Terminal,
    /// The tail rejoins the structural flow at this block.
    Rejoin(BlockId),
}

/// A try plan within one frame (main tree or a handler shim).
#[derive(Clone, Debug)]
pub(in crate::structure) struct Plan {
    /// Display index (`try_regions` position in the owning function).
    pub(in crate::structure) region: usize,
    /// Protected blocks.
    pub(in crate::structure) protected: BTreeSet<BlockId>,
    /// Catch handler entries.
    pub(in crate::structure) handlers: Vec<BlockId>,
    /// d-P1's cut observation.
    pub(in crate::structure) cuts: bool,
}

/// Try-coverage of a region node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::structure) enum Cov {
    /// Every block of the node has the same innermost plan (`None` =
    /// no plan).
    Uniform(Option<usize>),
    /// Mixed coverage — descend.
    Mixed,
}

/// An active arm-entry label (from a not-yet-emitted
/// [`RegionNode::Alternates`] or Ramsey forward merge in the current sequence).
#[derive(Clone, Debug)]
pub(in crate::structure) struct ArmScope {
    /// The arm entry block.
    pub(in crate::structure) entry: BlockId,
    /// Its label (`break L$x` lands at the arm start).
    pub(in crate::structure) label: String,
    /// Whether natural fall-through to `Follow::Entry(entry)` lands directly
    /// at `entry` without needing an explicit `break L$x`.
    pub(in crate::structure) fallthrough_ok: bool,
    /// Whether this scope was opened speculatively for a Ramsey sequence merge
    /// (`try_run_fold` may still inline-fold small plain runs reaching `entry`).
    pub(in crate::structure) ramsey: bool,
}

/// The arm body currently being emitted (mid-arm exits become
/// `break <done>`).
#[derive(Clone, Debug)]
pub(in crate::structure) struct ArmBody {
    /// The alternates wrapper label.
    pub(in crate::structure) done: String,
    /// The arm's blocks.
    pub(in crate::structure) slice: BTreeSet<BlockId>,
}

/// An in-flight join hoist (d-P5, RC1): unprotected tail region nodes
/// of a cut mixed-coverage `If`. While set, [`Ctx::emit_node`]
/// suppresses their inline emission; the driver emits them after the
/// try/catch (where the handlers rejoin).
#[derive(Clone, Debug)]
pub(in crate::structure) struct CutDefer {
    /// The deferred region nodes (removed as intercepted).
    pub(in crate::structure) ids: HashSet<RegionId>,
}

/// The phase-1 split classification of a mixed-coverage node for the
/// join hoist (d-P5, RC1): how the node partitions into a protected
/// skeleton (stays inside the try) and an unprotected deferred tail
/// (emitted after the try/catch).
pub(in crate::structure) enum CutSplit {
    /// Fully protected by the cut plan.
    Prot,
    /// Fully unprotected — deferred whole.
    Defer,
    /// `Seq`: `children[..split_at]` protected, `children[split_at]`
    /// (when `inner`) splits recursively, the rest deferred.
    Seq {
        /// Protected prefix length (the `inner` child's index when
        /// present).
        split_at: usize,
        /// The recursively-splitting middle child.
        inner: Option<Box<CutSplit>>,
    },
    /// `If` with a protected head: exactly one arm splits, the other
    /// is verified terminal-only.
    If {
        /// The then-arm classification.
        then: Option<ArmCut>,
        /// The else-arm classification.
        otherwise: Option<ArmCut>,
    },
}

fn take_arm_cut_inner(arm: &mut ArmCut) -> Option<CutSplit> {
    match arm {
        ArmCut::Terminal => None,
        ArmCut::Splits(b) => match std::mem::replace(b.as_mut(), CutSplit::Prot) {
            CutSplit::Prot | CutSplit::Defer => None,
            compound => Some(compound),
        },
    }
}

fn drain_cut_split_children(cs: &mut CutSplit, stack: &mut Vec<CutSplit>) {
    match cs {
        CutSplit::Prot | CutSplit::Defer => {}
        CutSplit::Seq { inner, .. } => {
            if let Some(child) = inner.take() {
                stack.push(*child);
            }
        }
        CutSplit::If { then, otherwise } => {
            if let Some(mut arm) = then.take()
                && let Some(child) = take_arm_cut_inner(&mut arm)
            {
                stack.push(child);
            }
            if let Some(mut arm) = otherwise.take()
                && let Some(child) = take_arm_cut_inner(&mut arm)
            {
                stack.push(child);
            }
        }
    }
}

impl Drop for CutSplit {
    fn drop(&mut self) {
        let mut stack: Vec<CutSplit> = Vec::new();
        drain_cut_split_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_cut_split_children(&mut cur, &mut stack);
        }
    }
}

/// One arm of a cut `If`.
pub(in crate::structure) enum ArmCut {
    /// Fully protected AND every exit path terminal (throw/return or
    /// an edge with a structural action) — falling out would
    /// incorrectly route through the hoisted tail.
    Terminal,
    /// The arm splits into a protected prefix and a deferred tail.
    Splits(Box<CutSplit>),
}

impl Drop for ArmCut {
    fn drop(&mut self) {
        if let Some(mut first) = take_arm_cut_inner(self) {
            let mut stack: Vec<CutSplit> = Vec::new();
            drain_cut_split_children(&mut first, &mut stack);
            while let Some(mut cur) = stack.pop() {
                drain_cut_split_children(&mut cur, &mut stack);
            }
        }
    }
}

impl std::fmt::Debug for CutSplit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Split(&'a CutSplit),
            ArmOpt(&'a Option<ArmCut>),
            Raw(&'static str),
        }
        let mut tasks = vec![Task::Split(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Raw(s) => f.write_str(s)?,
                Task::ArmOpt(opt) => match opt {
                    None => f.write_str("None")?,
                    Some(ArmCut::Terminal) => f.write_str("Some(Terminal)")?,
                    Some(ArmCut::Splits(inner)) => {
                        f.write_str("Some(Splits(")?;
                        tasks.push(Task::Raw("))"));
                        tasks.push(Task::Split(inner));
                    }
                },
                Task::Split(cs) => match cs {
                    CutSplit::Prot => f.write_str("Prot")?,
                    CutSplit::Defer => f.write_str("Defer")?,
                    CutSplit::Seq { split_at, inner } => {
                        write!(f, "Seq {{ split_at: {split_at}, inner: ")?;
                        match inner {
                            None => f.write_str("None }")?,
                            Some(child) => {
                                f.write_str("Some(")?;
                                tasks.push(Task::Raw(") }"));
                                tasks.push(Task::Split(child));
                            }
                        }
                    }
                    CutSplit::If { then, otherwise } => {
                        f.write_str("If { then: ")?;
                        tasks.push(Task::Raw(" }"));
                        tasks.push(Task::ArmOpt(otherwise));
                        tasks.push(Task::Raw(", otherwise: "));
                        tasks.push(Task::ArmOpt(then));
                    }
                },
            }
        }
        Ok(())
    }
}

impl std::fmt::Debug for ArmCut {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArmCut::Terminal => f.write_str("Terminal"),
            ArmCut::Splits(inner) => write!(f, "Splits({inner:?})"),
        }
    }
}

/// One emission frame: a region tree (the main tree or one handler
/// shim) plus everything derived from it.
pub(in crate::structure) struct Frame {
    pub(in crate::structure) tree: RegionTree,
    pub(in crate::structure) plans: Vec<Plan>,
    /// Sorted ascending by protected-set size: the first plan
    /// containing a block is its innermost (laminarity).
    pub(in crate::structure) plan_order: Vec<usize>,
    pub(in crate::structure) eclass: HashMap<(BlockId, BlockId), EdgeClass>,
    /// Loop headers that need an emitted label (targeted by a labeled
    /// break/continue).
    pub(in crate::structure) loop_labels: HashMap<BlockId, String>,
    pub(in crate::structure) cov_memo: HashMap<RegionId, Cov>,
    pub(in crate::structure) blocks_memo: HashMap<RegionId, BTreeSet<BlockId>>,
    pub(in crate::structure) plan_of_memo: HashMap<BlockId, Option<usize>>,
    pub(in crate::structure) arm_scopes: Vec<ArmScope>,
    pub(in crate::structure) arm_bodies: Vec<ArmBody>,
    /// Blocks whose terminator a consumer (loop header/latch) took.
    pub(in crate::structure) skip_blocks: HashSet<BlockId>,
    /// How many times each plan was wrapped (>1 = split).
    pub(in crate::structure) wrap_counts: HashMap<usize, usize>,
    /// d-P1's cross-arm edges (arm block → sibling-arm block): the
    /// edges the acyclic structurer could not honor — the tail-
    /// duplication fold's work list.
    pub(in crate::structure) cross_arm: HashSet<(BlockId, BlockId)>,
    /// Loop headers (the tail fold never duplicates into a loop).
    pub(in crate::structure) loop_headers: BTreeSet<BlockId>,
    /// The in-flight join hoist (d-P5, RC1), when a cut `If` skeleton
    /// is being emitted.
    pub(in crate::structure) cut_defer: Option<CutDefer>,
    /// When this frame is a HANDLER SHIM: the handler entry (its
    /// sub-CFG block set is `Ctx::shim_sets[handler]`). Drives the
    /// handler-tail duplication at cut (out-of-set) terminator edges.
    pub(in crate::structure) shim_of: Option<BlockId>,
    /// N77: this frame is a UNIQUE-prefix handler shim (its block set
    /// is `Ctx::uniq_sets[handler]`, not `Ctx::shim_sets[handler]`).
    pub(in crate::structure) shim_uniq: bool,
    /// N77: this frame is a tower-JOIN shim (its out-of-set edges are
    /// verified inter-level fall-outs; `shim_of` stays `None`).
    pub(in crate::structure) join_shim: bool,
}

impl Frame {
    pub(in crate::structure) fn new(tree: RegionTree, plans: Vec<Plan>) -> Self {
        let mut eclass = HashMap::new();
        let mut labeled_headers = BTreeSet::new();
        for ce in &tree.edges {
            eclass.insert((ce.from, ce.to), ce.class);
            match ce.class {
                EdgeClass::Break { header, labeled } | EdgeClass::Continue { header, labeled }
                    if labeled =>
                {
                    labeled_headers.insert(header);
                }
                _ => {}
            }
        }
        let loop_labels = labeled_headers
            .into_iter()
            .map(|h| (h, format!("L${}", h.index())))
            .collect();
        let cross_arm: HashSet<(BlockId, BlockId)> = tree.cross_arm_edges.iter().copied().collect();
        let mut loop_headers = BTreeSet::new();
        for node in tree.nodes() {
            if let RegionNode::Loop { header, .. } = node {
                loop_headers.insert(*header);
            }
        }
        let mut plan_order: Vec<usize> = (0..plans.len()).collect();
        plan_order.sort_by_key(|&i| plans[i].protected.len());
        Frame {
            tree,
            plans,
            plan_order,
            eclass,
            loop_labels,
            cov_memo: HashMap::new(),
            blocks_memo: HashMap::new(),
            plan_of_memo: HashMap::new(),
            arm_scopes: Vec::new(),
            arm_bodies: Vec::new(),
            skip_blocks: HashSet::new(),
            wrap_counts: HashMap::new(),
            cross_arm,
            loop_headers,
            cut_defer: None,
            shim_of: None,
            shim_uniq: false,
            join_shim: false,
        }
    }

    pub(in crate::structure) fn node(&self, id: RegionId) -> &RegionNode {
        self.tree.node(id)
    }

    /// The innermost plan containing `b` (laminar ⇒ well-defined).
    pub(in crate::structure) fn plan_of(&mut self, b: BlockId) -> Option<usize> {
        if let Some(p) = self.plan_of_memo.get(&b) {
            return *p;
        }
        let p = self
            .plan_order
            .iter()
            .copied()
            .find(|&i| self.plans[i].protected.contains(&b));
        self.plan_of_memo.insert(b, p);
        p
    }

    /// Every block of a region node (iterative post-order memoization).
    pub(in crate::structure) fn node_blocks(&mut self, id: RegionId) -> BTreeSet<BlockId> {
        if let Some(s) = self.blocks_memo.get(&id) {
            return s.clone();
        }
        let mut stack: Vec<(RegionId, bool)> = vec![(id, false)];
        while let Some((cur, expanded)) = stack.pop() {
            if self.blocks_memo.contains_key(&cur) {
                continue;
            }
            if !expanded {
                stack.push((cur, true));
                match self.node(cur) {
                    RegionNode::Block(_) | RegionNode::Irreducible { .. } => {}
                    RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                        for &c in children.iter().rev() {
                            if !self.blocks_memo.contains_key(&c) {
                                stack.push((c, false));
                            }
                        }
                    }
                    RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                        let body = *body;
                        if !self.blocks_memo.contains_key(&body) {
                            stack.push((body, false));
                        }
                    }
                    RegionNode::If {
                        then, otherwise, ..
                    } => {
                        for c in [otherwise, then].into_iter().flatten() {
                            if !self.blocks_memo.contains_key(c) {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
                continue;
            }
            let mut out = BTreeSet::new();
            match self.node(cur) {
                RegionNode::Block(b) => {
                    out.insert(*b);
                }
                RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
                RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                    let children = children.clone();
                    for c in children {
                        if let Some(cb) = self.blocks_memo.get(&c) {
                            out.extend(cb.iter().copied());
                        }
                    }
                }
                RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                    let body = *body;
                    if let Some(cb) = self.blocks_memo.get(&body) {
                        out.extend(cb.iter().copied());
                    }
                }
                RegionNode::If {
                    head,
                    then,
                    otherwise,
                    ..
                } => {
                    out.insert(*head);
                    let children: [Option<RegionId>; 2] = [*then, *otherwise];
                    for c in children.into_iter().flatten() {
                        if let Some(cb) = self.blocks_memo.get(&c) {
                            out.extend(cb.iter().copied());
                        }
                    }
                }
            }
            self.blocks_memo.insert(cur, out);
        }
        self.blocks_memo.get(&id).cloned().unwrap_or_default()
    }

    /// The node's try coverage (iterative post-order memoized fold).
    pub(in crate::structure) fn cov(&mut self, id: RegionId) -> Cov {
        if let Some(c) = self.cov_memo.get(&id) {
            return *c;
        }
        let mut stack: Vec<(RegionId, bool)> = vec![(id, false)];
        while let Some((cur, expanded)) = stack.pop() {
            if self.cov_memo.contains_key(&cur) {
                continue;
            }
            if !expanded {
                stack.push((cur, true));
                match self.node(cur) {
                    RegionNode::Block(_) | RegionNode::Irreducible { .. } => {}
                    RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                        for &c in children.iter().rev() {
                            if !self.cov_memo.contains_key(&c) {
                                stack.push((c, false));
                            }
                        }
                    }
                    RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                        let body = *body;
                        if !self.cov_memo.contains_key(&body) {
                            stack.push((body, false));
                        }
                    }
                    RegionNode::If {
                        then, otherwise, ..
                    } => {
                        for c in [otherwise, then].into_iter().flatten() {
                            if !self.cov_memo.contains_key(c) {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
                continue;
            }
            let node = self.node(cur).clone();
            let cov = match node {
                RegionNode::Block(b) => Cov::Uniform(self.plan_of(b)),
                RegionNode::Irreducible { blocks, .. } => {
                    let mut it = blocks.iter();
                    let first = it.next().map(|&b| self.plan_of(b));
                    let mut acc = Cov::Uniform(first.unwrap_or(None));
                    for &b in it {
                        if acc != Cov::Uniform(self.plan_of(b)) {
                            acc = Cov::Mixed;
                            break;
                        }
                    }
                    acc
                }
                RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                    let mut acc: Option<Cov> = None;
                    for c in children {
                        let cc = self.cov_memo.get(&c).copied().unwrap_or(Cov::Uniform(None));
                        acc = Some(match acc {
                            None => cc,
                            Some(a) if a == cc => a,
                            _ => Cov::Mixed,
                        });
                    }
                    acc.unwrap_or(Cov::Uniform(None))
                }
                RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => self
                    .cov_memo
                    .get(&body)
                    .copied()
                    .unwrap_or(Cov::Uniform(None)),
                RegionNode::If {
                    head,
                    then,
                    otherwise,
                    ..
                } => {
                    let hc = Cov::Uniform(self.plan_of(head));
                    let mut acc = hc;
                    for c in [then, otherwise].into_iter().flatten() {
                        let cc = self.cov_memo.get(&c).copied().unwrap_or(Cov::Uniform(None));
                        if acc != cc {
                            acc = Cov::Mixed;
                        }
                    }
                    acc
                }
            };
            self.cov_memo.insert(cur, cov);
        }
        self.cov_memo
            .get(&id)
            .copied()
            .unwrap_or(Cov::Uniform(None))
    }
}
