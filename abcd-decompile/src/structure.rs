//! Stage B — control-flow structuring (design/decompile.md §4.2):
//! d-P1's region tree ([`abcd_analysis::control::regions`]) + Stage A's
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
//!   [`Ctx::emit_alternates`]).
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
//! ## try/catch projection (design §4.2.5 + d-P1's [`TryPlan`])
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
//!   ([`TryPlan::cuts_structured_region`]).
//! - A `Mixed` node whose HEAD block is protected wraps whole (the
//!   condition evaluation is protected; arms may be over-protected —
//!   documented approximation, counted).
//!
//! Handlers are NOT in the region tree (d-P1's N45 design): each
//! handler body is structured as its own sub-CFG. Since
//! [`structure_regions`] only structures from a function entry, the
//! structurer builds a per-function SHIM module (a clone whose handler
//! sub-CFGs are exposed as extra functions with the out-of-set
//! terminator edges cut to `Return`) and structures each handler
//! through the same [`structure_regions`] entry point. Nested
//! try-in-handler regions recurse through their own shims. The
//! `ExceptionParam` binding comes from Stage A's [`Stmt::CatchBind`]
//! marker at the handler head.

use std::collections::{BTreeSet, HashMap, HashSet};

use abcd_analysis::control::{
    EdgeClass, LoopKind, RegionId, RegionNode, RegionTree, block_succs, structure_regions,
};
use abcd_ir::function::FunctionData;
use abcd_ir::module::Module;
use abcd_ir::op::{CmpOp, UnOp};
use abcd_ir::{BlockId, ClassId, FuncId, Op, Sym};

use crate::expr::{Expr, Lit};
use crate::recover::{RecoveredFunc, Stmt};

/// A leaf statement: Stage-A statements plus Stage-B synthetic forms
/// (the desugar folds in [`crate::folds`] add [`Leaf::Destructure`];
/// the irreducible fallback uses [`Leaf::Decl`]/[`Leaf::Assign`]).
#[derive(Clone, Debug, PartialEq)]
pub enum Leaf {
    /// A Stage-A recovered statement.
    Raw(Stmt),
    /// `const {k0: t0, …, ...rest} = obj` — rest-destructuring fold
    /// output (design §4.2.6).
    Destructure {
        /// The source object.
        obj: Expr,
        /// `(key, target binding)` pairs for the excluded keys.
        keys: Vec<(String, String)>,
        /// The rest binding.
        rest: String,
    },
    /// A synthetic `let`/`const` declaration (no SSA provenance).
    Decl {
        /// Binding name (legalized).
        name: String,
        /// `let` vs `const`.
        mutable: bool,
        /// The initializer (`let x;` when `None`).
        value: Option<Expr>,
    },
    /// A synthetic assignment `target = value`.
    Assign {
        /// The target identifier.
        target: String,
        /// The assigned value.
        value: Expr,
    },
}

/// A structured statement node (Stage B output; [`crate::emit`] prints).
#[derive(Clone, Debug, PartialEq)]
pub enum SNode {
    /// A run of leaf statements (one block's content or a phi partition).
    Stmts(Vec<Leaf>),
    /// `if (cond) { then } [else { otherwise }]`.
    If {
        /// The condition.
        cond: Expr,
        /// The true arm.
        then: Vec<SNode>,
        /// The false arm (empty = no else).
        otherwise: Vec<SNode>,
    },
    /// `while (cond) { body }`; `cond: None` → `while (true)`.
    While {
        /// The loop label (emitted `L: while …` — required by labeled
        /// break/continue targeting this loop).
        label: Option<String>,
        /// The header condition (`None` = `while (true)`).
        cond: Option<Expr>,
        /// The body.
        body: Vec<SNode>,
    },
    /// `do { body } while (cond)`.
    DoWhile {
        /// The loop label.
        label: Option<String>,
        /// The body.
        body: Vec<SNode>,
        /// The latch condition.
        cond: Expr,
    },
    /// `break [label]`.
    Break {
        /// The label, when the exit crosses more than the innermost
        /// enclosing loop (or targets a labeled alternate).
        label: Option<String>,
    },
    /// `continue [label]`.
    Continue {
        /// The label, when the edge targets a non-innermost loop.
        label: Option<String>,
    },
    /// A labeled block: `label: { body }` (the JS labeled-statement
    /// escape hatch for multi-entry continuations).
    Labeled {
        /// The label.
        label: String,
        /// The body.
        body: Vec<SNode>,
    },
    /// `try { body } catch (binding) { … }`. Multiple IR catch handlers
    /// (typed catches — no JS surface syntax) are merged into the first
    /// clause with an honesty comment ([`StructStats::multi_catch`]).
    Try {
        /// The try body.
        body: Vec<SNode>,
        /// The catch clauses (emitted: the first; the rest are merged
        /// with a note).
        catches: Vec<CatchClause>,
        /// An optional honesty note (cut-boundary placement, …).
        note: Option<String>,
    },
    /// `for (const binding of iter) { body }` / `for await (…)` — the
    /// iterator-loop desugar fold output ([`crate::folds`]).
    ForOf {
        /// `for await…of` when set.
        is_await: bool,
        /// The iteration binding.
        binding: String,
        /// The iterated expression.
        iter: Expr,
        /// The body.
        body: Vec<SNode>,
    },
    /// `for (const binding in obj) { body }` — the for-in fold output.
    ForIn {
        /// The key binding.
        binding: String,
        /// The enumerated object.
        obj: Expr,
        /// The body.
        body: Vec<SNode>,
    },
    /// `switch (disc) { case … }` — the cosmetic compare/branch-chain
    /// re-detection fold output ([`crate::folds`]; the IR has no
    /// `Switch` op by design — ir-v0.2 §9 resolution 2).
    Switch {
        /// The discriminant.
        disc: Expr,
        /// The cases.
        cases: Vec<SwitchCase>,
    },
    /// An honesty comment line (fallbacks, cut placements, pending
    /// folds). Never silent, never elided.
    Honest(String),
}

/// One `catch` clause of [`SNode::Try`].
#[derive(Clone, Debug, PartialEq)]
pub struct CatchClause {
    /// The `catch (e)` binding (`None` = unavailable — honesty path).
    pub binding: Option<String>,
    /// The handler body.
    pub body: Vec<SNode>,
}

/// One case of [`SNode::Switch`]; `tests` empty = `default:`.
#[derive(Clone, Debug, PartialEq)]
pub struct SwitchCase {
    /// The case test expressions.
    pub tests: Vec<Expr>,
    /// The case body.
    pub body: Vec<SNode>,
}

/// Structuring counters (the corpus gate prints them verbatim).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StructStats {
    /// `if`/`if…else` nodes emitted.
    pub ifs: usize,
    /// Clean `while (cond)` loops.
    pub loops_while: usize,
    /// `do…while` loops.
    pub loops_do_while: usize,
    /// `while (true)` loops (the always-correct general form).
    pub loops_while_true: usize,
    /// Labeled `break`/`continue` to non-innermost loops.
    pub labeled_exits: usize,
    /// Multi-entry continuations emitted as labeled alternates.
    pub alternates: usize,
    /// Irreducible subgraphs emitted as state-machine dispatch.
    pub irreducible_fallbacks: usize,
    /// Blocks inside state-machine fallbacks.
    pub state_machine_blocks: usize,
    /// `try`/`catch` wrappers emitted.
    pub try_catches: usize,
    /// Try plans whose protected range cuts a structured region (d-P1's
    /// `cuts_structured_region` observation — try placed at the cut).
    pub try_cuts: usize,
    /// Non-contiguous protected emission (a plan wrapped more than
    /// once, or unprotected statements inside a try span).
    pub try_splits: usize,
    /// Regions with more than one catch handler (merged, noted).
    pub multi_catch: usize,
    /// Handler sub-CFGs structured through the shim module.
    pub handler_shims: usize,
    /// Loop-exit phi assignments placed after the loop.
    pub exit_phi_after_loop: usize,
    /// Dropped no-op conditional branches whose cross-arm edge could
    /// NOT be repaired by the tail-duplication fold (residual).
    pub cross_arm_notes: usize,
    /// Cross-arm drop sites repaired by the shared-tail duplication
    /// fold (d-P4; d-P1's `cross_arm_edges` hint): the dropped edge's
    /// target tail is emitted inline at the site.
    pub cross_arm_folds: usize,
    /// Blocks duplicated by the cross-arm fold.
    pub cross_arm_dup_blocks: usize,
    /// Unverifiable break targets (defensive; expected 0).
    pub break_target_notes: usize,
}

/// The Stage-B result for one function.
#[derive(Clone, Debug)]
pub struct Structured {
    /// The structured body.
    pub body: Vec<SNode>,
    /// Structuring counters.
    pub stats: StructStats,
}

/// Structure one function (region tree + Stage-A statements → [`SNode`]s).
pub fn structure_func(module: &Module, rf: &RecoveredFunc) -> Structured {
    Ctx::new(module, rf).build()
}

/// What follows a region in emission order (for the clean-loop-form
/// "exit target == structural continuation" check).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Follow {
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
enum DupStop {
    /// The tail ends in a terminal (return/throw) — never falls through.
    Terminal,
    /// The tail rejoins the structural flow at this block.
    Rejoin(BlockId),
}

/// A try plan within one frame (main tree or a handler shim).
#[derive(Clone, Debug)]
struct Plan {
    /// Display index (`try_regions` position in the owning function).
    region: usize,
    /// Protected blocks.
    protected: BTreeSet<BlockId>,
    /// Catch handler entries.
    handlers: Vec<BlockId>,
    /// d-P1's cut observation.
    cuts: bool,
}

/// Try-coverage of a region node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cov {
    /// Every block of the node has the same innermost plan (`None` =
    /// no plan).
    Uniform(Option<usize>),
    /// Mixed coverage — descend.
    Mixed,
}

/// An active arm-entry label (from a not-yet-emitted
/// [`RegionNode::Alternates`] in the current sequence).
#[derive(Clone, Debug)]
struct ArmScope {
    /// The arm entry block.
    entry: BlockId,
    /// Its label (`break L$x` lands at the arm start).
    label: String,
}

/// The arm body currently being emitted (mid-arm exits become
/// `break <done>`).
#[derive(Clone, Debug)]
struct ArmBody {
    /// The alternates wrapper label.
    done: String,
    /// The arm's blocks.
    slice: BTreeSet<BlockId>,
}

/// One emission frame: a region tree (the main tree or one handler
/// shim) plus everything derived from it.
struct Frame {
    tree: RegionTree,
    plans: Vec<Plan>,
    /// Sorted ascending by protected-set size: the first plan
    /// containing a block is its innermost (laminarity).
    plan_order: Vec<usize>,
    eclass: HashMap<(BlockId, BlockId), EdgeClass>,
    /// Loop headers that need an emitted label (targeted by a labeled
    /// break/continue).
    loop_labels: HashMap<BlockId, String>,
    cov_memo: HashMap<RegionId, Cov>,
    blocks_memo: HashMap<RegionId, BTreeSet<BlockId>>,
    plan_of_memo: HashMap<BlockId, Option<usize>>,
    arm_scopes: Vec<ArmScope>,
    arm_bodies: Vec<ArmBody>,
    /// Blocks whose terminator a consumer (loop header/latch) took.
    skip_blocks: HashSet<BlockId>,
    /// How many times each plan was wrapped (>1 = split).
    wrap_counts: HashMap<usize, usize>,
    /// d-P1's cross-arm edges (arm block → sibling-arm block): the
    /// edges the acyclic structurer could not honor — the tail-
    /// duplication fold's work list.
    cross_arm: HashSet<(BlockId, BlockId)>,
    /// Loop headers (the tail fold never duplicates into a loop).
    loop_headers: BTreeSet<BlockId>,
}

impl Frame {
    fn new(tree: RegionTree, plans: Vec<Plan>) -> Self {
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
        }
    }

    fn node(&self, id: RegionId) -> &RegionNode {
        self.tree.node(id)
    }

    /// The innermost plan containing `b` (laminar ⇒ well-defined).
    fn plan_of(&mut self, b: BlockId) -> Option<usize> {
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

    /// Every block of a region node.
    fn node_blocks(&mut self, id: RegionId) -> BTreeSet<BlockId> {
        if let Some(s) = self.blocks_memo.get(&id) {
            return s.clone();
        }
        let mut out = BTreeSet::new();
        match self.node(id) {
            RegionNode::Block(b) => {
                out.insert(*b);
            }
            RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                let children = children.clone();
                for c in children {
                    out.extend(self.node_blocks(c));
                }
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                let body = *body;
                out.extend(self.node_blocks(body));
            }
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => {
                out.insert(*head);
                let children: Vec<RegionId> =
                    [then, otherwise].into_iter().flatten().copied().collect();
                for child in children {
                    out.extend(self.node_blocks(child));
                }
            }
        }
        self.blocks_memo.insert(id, out.clone());
        out
    }

    /// The node's try coverage (memoized fold).
    fn cov(&mut self, id: RegionId) -> Cov {
        if let Some(c) = self.cov_memo.get(&id) {
            return *c;
        }
        let node = self.node(id).clone();
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
                    let cc = self.cov(c);
                    acc = Some(match acc {
                        None => cc,
                        Some(a) if a == cc => a,
                        _ => Cov::Mixed,
                    });
                }
                acc.unwrap_or(Cov::Uniform(None))
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => self.cov(body),
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => {
                let hc = Cov::Uniform(self.plan_of(head));
                let mut acc = hc;
                for c in [then, otherwise].into_iter().flatten() {
                    let cc = self.cov(c);
                    if acc != cc {
                        acc = Cov::Mixed;
                    }
                }
                acc
            }
        };
        self.cov_memo.insert(id, cov);
        cov
    }
}

/// A block's content split for emission: main statements (terminator
/// and trailing phi-assignments removed), the trailing
/// [`Stmt::PhiAssign`] run, and the terminator. Owned (cloned) so the
/// emitter can mutate its context afterwards.
struct BlockParts {
    main: Vec<Stmt>,
    phi: Vec<Stmt>,
    term: Term,
}

/// A block terminator relevant to structuring.
#[derive(Clone)]
enum Term {
    /// No control terminator (return/throw/end).
    None,
    /// Unconditional branch.
    Branch(BlockId),
    /// Conditional branch.
    Cond(Expr, BlockId, BlockId),
}

struct Ctx<'m> {
    module: &'m Module,
    rf: &'m RecoveredFunc,
    /// block → index into `rf.blocks`.
    bmap: HashMap<BlockId, usize>,
    stats: StructStats,
    frames: Vec<Frame>,
    /// Shim module (a clone exposing handler sub-CFGs as functions);
    /// built lazily when the function has try regions with handlers.
    shim_module: Option<Module>,
    /// handler entry → its own region tree (over the shim module).
    shim_trees: HashMap<BlockId, RegionTree>,
    /// handler entry → the plans nested inside its sub-CFG.
    shim_plans: HashMap<BlockId, Vec<Plan>>,
    /// Counter for `A$k` alternates-wrapper labels (deterministic).
    alt_counter: usize,
    /// Counter for `s$k` state-machine temporaries (deterministic).
    state_counter: usize,
    /// Cross-arm edges the tail-duplication fold repaired (the build()
    /// summary lists only the residual, unfolded ones).
    folded_xarms: BTreeSet<(BlockId, BlockId)>,
}

impl<'m> Ctx<'m> {
    fn new(module: &'m Module, rf: &'m RecoveredFunc) -> Self {
        let bmap = rf
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.block, i))
            .collect();
        Ctx {
            module,
            rf,
            bmap,
            stats: StructStats::default(),
            frames: Vec::new(),
            shim_module: None,
            shim_trees: HashMap::new(),
            shim_plans: HashMap::new(),
            alt_counter: 0,
            state_counter: 0,
            folded_xarms: BTreeSet::new(),
        }
    }

    fn f(&self) -> &Frame {
        self.frames.last().expect("a frame is always active")
    }

    fn f_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame is always active")
    }

    fn build(mut self) -> Structured {
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
            .any(|e| matches!(e, abcd_analysis::control::EscapeHatch::CrossEdge { .. }));
        if !self.f().tree.irreducible.is_empty() || has_cross_edge {
            self.emit_whole_function_state_machine(&mut body);
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

    // ── Handler shims ────────────────────────────────────────────────

    /// Build shim region trees for every catch handler of the function
    /// (handlers are not Normal-reachable from the entry — the N45
    /// model — so each handler body is structured as its own sub-CFG
    /// through a cloned module with the out-of-set edges cut).
    fn build_shims(&mut self, _main_tree: &RegionTree) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        if f.try_regions.is_empty() {
            return;
        }
        let main_universe: BTreeSet<BlockId> = self
            .module
            .func(self.rf.func)
            .map(|f| {
                let entry = f.blocks.first().copied();
                let mut set = BTreeSet::new();
                if let Some(e) = entry {
                    let mut queue = std::collections::VecDeque::from([e]);
                    set.insert(e);
                    while let Some(b) = queue.pop_front() {
                        for s in block_succs(self.module, b) {
                            if set.insert(s) {
                                queue.push_back(s);
                            }
                        }
                    }
                }
                set
            })
            .unwrap_or_default();

        // Every handler entry, in region order (deduped).
        let mut handlers: Vec<BlockId> = Vec::new();
        for tr in &f.try_regions {
            for c in &tr.catches {
                if !handlers.contains(&c.handler) {
                    handlers.push(c.handler);
                }
            }
        }
        // Approximate per-handler sub-CFG: Normal-reachable from the
        // handler, stopping at the main universe.
        let approx = |h: BlockId| -> BTreeSet<BlockId> {
            let mut set = BTreeSet::new();
            let mut queue = std::collections::VecDeque::from([h]);
            set.insert(h);
            while let Some(b) = queue.pop_front() {
                for s in block_succs(self.module, b) {
                    if !main_universe.contains(&s) && set.insert(s) {
                        queue.push_back(s);
                    }
                }
            }
            set
        };
        let approx_sets: HashMap<BlockId, BTreeSet<BlockId>> =
            handlers.iter().map(|&h| (h, approx(h))).collect();
        // Ancestor relation: handler `a` is an ancestor of `h` when h's
        // region's protected blocks live inside a's sub-CFG (a nested
        // try inside a catch body). The nested handler's set stops at
        // its ancestors' sets (the continuation belongs to the ancestor).
        let mut sets: HashMap<BlockId, BTreeSet<BlockId>> = HashMap::new();
        for (ri, tr) in f.try_regions.iter().enumerate() {
            let _ = ri;
            for c in &tr.catches {
                let h = c.handler;
                if sets.contains_key(&h) {
                    continue;
                }
                let protected: BTreeSet<BlockId> = tr.protected.iter().copied().collect();
                let mut set = approx_sets[&h].clone();
                for (&a, aset) in &approx_sets {
                    if a == h {
                        continue;
                    }
                    // a is an ancestor of this handler when the region's
                    // protected set is inside a's reach.
                    let region_of_a_protects_h = f.try_regions.iter().any(|tr2| {
                        tr2.catches.iter().any(|c2| c2.handler == a)
                            && protected.iter().all(|b| aset.contains(b))
                    });
                    if region_of_a_protects_h && protected.iter().all(|b| aset.contains(b)) {
                        for b in aset {
                            set.remove(b);
                        }
                    }
                }
                sets.insert(h, set);
            }
        }

        // Build the shim module: clone, patch out-of-set terminators,
        // add one shim function per handler.
        let mut shim = self.module.clone();
        for (&h, set) in &sets {
            if !set.contains(&h) {
                continue; // entry swallowed (exotic) — honesty at emission
            }
            for &b in set {
                let Some(block) = shim.block(b).cloned() else {
                    continue;
                };
                let Some(&last) = block.insts.last() else {
                    continue;
                };
                let new_op = match &shim.inst(last).expect("inst").op {
                    Op::Branch { dest } if !set.contains(dest) => Some(Op::Return { value: None }),
                    Op::CondBranch {
                        true_dest,
                        false_dest,
                        ..
                    } => {
                        let t_in = set.contains(true_dest);
                        let f_in = set.contains(false_dest);
                        match (t_in, f_in) {
                            (true, true) => None,
                            (true, false) => Some(Op::Branch { dest: *true_dest }),
                            (false, true) => Some(Op::Branch { dest: *false_dest }),
                            (false, false) => Some(Op::Return { value: None }),
                        }
                    }
                    _ => None,
                };
                if let Some(op) = new_op {
                    shim.inst_mut(last).expect("inst").op = op;
                }
            }
        }
        for (&h, set) in &sets {
            if !set.contains(&h) {
                continue;
            }
            let mut blocks: Vec<BlockId> = vec![h];
            blocks.extend(set.iter().copied().filter(|b| *b != h));
            let name: Sym = shim.sym.intern(&format!("$handler${}", h.index()));
            let fid = FuncId::new(shim.functions.len() as u32);
            let mut fd = FunctionData::new(ClassId::new(0), name, self.rf.kind);
            fd.blocks = blocks;
            // Nested try regions fully inside this handler's set ride
            // along (their handlers get their own shims).
            let block_set: BTreeSet<BlockId> = fd.blocks.iter().copied().collect();
            fd.try_regions = f
                .try_regions
                .iter()
                .filter(|tr| tr.protected.iter().all(|b| block_set.contains(b)))
                .cloned()
                .collect();
            shim.functions.push(fd);
            let tree = structure_regions(&shim, fid);
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
            self.shim_trees.insert(h, tree);
            self.shim_plans.insert(h, plans);
            self.stats.handler_shims += 1;
        }
        self.shim_module = Some(shim);
    }

    // ── Block parts ──────────────────────────────────────────────────

    fn block_parts(&self, b: BlockId) -> BlockParts {
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
                        term = Term::Branch(*true_dest);
                    } else {
                        term = Term::Cond(cond.clone(), *true_dest, *false_dest);
                    }
                    main_end = end - 1;
                }
                _ => {}
            }
        }
        BlockParts {
            main: stmts[..main_end].to_vec(),
            phi,
            term,
        }
    }

    /// Partition a trailing phi-assign run by edge destination.
    /// Returns `(to_t, to_f, rest)`.
    fn partition_phi(phi: &[Stmt], t: BlockId, f: BlockId) -> (Vec<Stmt>, Vec<Stmt>, Vec<Stmt>) {
        let mut pt = Vec::new();
        let mut pf = Vec::new();
        let mut rest = Vec::new();
        for s in phi {
            match s {
                Stmt::PhiAssign { to, .. } if *to == t => pt.push(s.clone()),
                Stmt::PhiAssign { to, .. } if *to == f => pf.push(s.clone()),
                _ => rest.push(s.clone()),
            }
        }
        (pt, pf, rest)
    }

    fn stmts_leaves(stmts: &[Stmt]) -> Vec<Leaf> {
        stmts
            .iter()
            .filter(|s| !matches!(s, Stmt::CatchBind { .. }))
            .map(|s| Leaf::Raw(s.clone()))
            .collect()
    }

    fn push_stmts(out: &mut Vec<SNode>, leaves: Vec<Leaf>) {
        if !leaves.is_empty() {
            out.push(SNode::Stmts(leaves));
        }
    }

    // ── Edge actions ─────────────────────────────────────────────────

    /// The statement an out-edge `from → to` forces at a leaf
    /// terminator: a (labeled) break/continue, or nothing when the tree
    /// already encodes the flow.
    fn edge_action(&mut self, from: BlockId, to: BlockId) -> Option<SNode> {
        // 1. An arm entry of a pending Alternates: `break L$entry`
        //    (overrides the edge classification — a plain break would
        //    land at the WRONG arm).
        for scope in self.f().arm_scopes.iter().rev() {
            if scope.entry == to {
                return Some(SNode::Break {
                    label: Some(scope.label.clone()),
                });
            }
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
    fn plain_break_ok(&self, to: BlockId, follow: Follow) -> bool {
        if self.f().arm_scopes.iter().any(|s| s.entry == to) {
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

    // ── Cross-arm tail-duplication fold (d-P4) ─────────────────────

    /// The es2abc `if (c) goto shared; else {…}` / short-circuit idiom
    /// leaves a forward edge from one conditional arm into its sibling
    /// (d-P1's `cross_arm_edges`). Such an edge has no structural
    /// action, so emission v1 dropped it (loudly). The fold duplicates
    /// the SHARED TAIL inline at the drop site: the target block's
    /// statements, then any further blocks chained through *recorded
    /// cross-arm edges only*, stopping at a terminal (return/throw) or
    /// at the first non-cross-arm edge, whose destination is reported
    /// to the caller as the rejoin point ([`DupStop::Rejoin`]) — the
    /// caller decides whether its emission context actually falls
    /// through to that block.
    ///
    /// Bounded: ≤ 8 blocks, ≤ 128 statements, never into a loop header,
    /// no conditional terminators mid-tail, and never across a try-plan
    /// boundary (duplicating protected code into an unprotected context
    /// would change throw behavior). Returns `None` — the caller keeps
    /// the honest drop — when any bound trips. On success returns the
    /// duplicated nodes, the stop mode, and the block count.
    fn cross_arm_dup(
        &mut self,
        site: BlockId,
        target: BlockId,
    ) -> Option<(Vec<SNode>, DupStop, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 128;
        let site_plan = self.f_mut().plan_of(site);
        let mut segs: Vec<(Option<usize>, Vec<SNode>)> = Vec::new();
        let mut cur = target;
        let mut visited = BTreeSet::new();
        let mut stmts = 0usize;
        let mut stop = None;
        loop {
            if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                return None;
            }
            if self.f().loop_headers.contains(&cur) {
                return None;
            }
            let cur_plan = self.f_mut().plan_of(cur);
            // Try-plan crossing: protectedness is a property of the
            // executed instruction (the PC range), not of the path — a
            // segment whose plan differs from the site's must be
            // wrapped in its own try/catch (below), which is only
            // possible when the segment IS protected (unprotecting is
            // impossible) and, when the site is itself protected, the
            // segment's plan is nested inside the site's (laminar
            // subset) so the physical nesting matches reality.
            if cur_plan != site_plan {
                let ok = match (site_plan, cur_plan) {
                    (None, Some(_)) => true,
                    (Some(q), Some(p)) => {
                        let (pp, qq) = (&self.f().plans[p].protected, &self.f().plans[q].protected);
                        pp.is_subset(qq)
                    }
                    _ => false,
                };
                if !ok {
                    return None;
                }
            }
            let parts = self.block_parts(cur);
            stmts += parts.main.len() + parts.phi.len();
            if stmts > MAX_STMTS {
                return None;
            }
            let mut blk: Vec<SNode> = Vec::new();
            let term = match parts.term {
                Term::None => {
                    // Terminal (return/throw) or no out-edge.
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.main));
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.phi));
                    stop = Some(DupStop::Terminal);
                    None
                }
                Term::Branch(dest) => {
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.main));
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.phi));
                    if self.f().cross_arm.contains(&(cur, dest)) {
                        // The shared tail continues through another
                        // dropped edge — keep walking.
                        Some(Some(dest))
                    } else {
                        // The tail rejoins the structural flow at
                        // `dest`; the caller checks its context falls
                        // through there.
                        stop = Some(DupStop::Rejoin(dest));
                        None
                    }
                }
                // A conditional mid-tail is beyond the v1 fold.
                Term::Cond(..) => {
                    return None;
                }
            };
            // Append the block's nodes to the current plan segment.
            match segs.last_mut() {
                Some((p, nodes)) if *p == cur_plan => nodes.append(&mut blk),
                _ => segs.push((cur_plan, blk)),
            }
            match term {
                Some(Some(dest)) => {
                    cur = dest;
                }
                Some(None) => unreachable!(),
                None => break,
            }
        }
        let Some(stop) = stop else {
            unreachable!("the dup walk only breaks after setting `stop`")
        };
        // Assemble: segments whose plan differs from the site's get
        // their own try/catch wrapper (the catch body duplicates — the
        // same finally-style duplication es2abc itself uses).
        let mut out: Vec<SNode> = Vec::new();
        for (plan, nodes) in segs {
            if plan != site_plan
                && let Some(p) = plan
            {
                let handlers = self.f().plans[p].handlers.clone();
                let mut catches = Vec::new();
                let mut seen = HashSet::new();
                for h in handlers {
                    if seen.insert(h) {
                        catches.push(self.emit_handler(h));
                    }
                }
                let wraps = {
                    let w = self.f_mut().wrap_counts.entry(p).or_insert(0);
                    *w += 1;
                    *w
                };
                if wraps > 1 {
                    self.stats.try_splits += 1;
                }
                self.stats.try_catches += 1;
                out.push(SNode::Try {
                    body: nodes,
                    catches,
                    note: Some(format!(
                        "cross-arm tail duplication re-wraps try region {p} (wrapper #{wraps}; protectedness is an instruction property, so the duplicated code keeps its own try/catch)"
                    )),
                });
            } else {
                out.extend(nodes);
            }
        }
        Some((out, stop, visited.len()))
    }

    /// Whether a duplicated tail stopping at `stop` is correct in an
    /// emission context whose structural continuation is `follow`:
    /// terminal tails are always safe (they never fall through);
    /// rejoining tails must land exactly on the continuation (or the
    /// ancestor tail, where fall-through is definitionally correct).
    fn dup_ok_for_follow(stop: DupStop, follow: Follow) -> bool {
        match stop {
            DupStop::Terminal => follow != Follow::Unknown,
            DupStop::Rejoin(dest) => match follow {
                Follow::Entry(e) => e == dest,
                Follow::Tail => true,
                Follow::Unknown => false,
            },
        }
    }

    /// Fold attempt at one dropped edge `site → target` for a context
    /// whose continuation is `follow`: duplicate the shared tail when
    /// the walk succeeds AND its rejoin matches the continuation.
    fn try_cross_arm_fold(
        &mut self,
        site: BlockId,
        target: BlockId,
        follow: Follow,
    ) -> Option<Vec<SNode>> {
        let (nodes, stop, nblocks) = self.cross_arm_dup(site, target)?;
        if !Self::dup_ok_for_follow(stop, follow) {
            if std::env::var_os("ABCD_XARM_DEBUG").is_some() {
                eprintln!(
                    "XARM-BAIL site=B{} target=B{} reason=follow-mismatch({follow:?}, stop={stop:?})",
                    site.index(),
                    target.index()
                );
            }
            return None;
        }
        self.stats.cross_arm_folds += 1;
        self.stats.cross_arm_dup_blocks += nblocks;
        self.folded_xarms.insert((site, target));
        Some(nodes)
    }

    /// Whether the edge `from → to` forces a terminator action (a
    /// labeled/unlabeled break/continue or an alternates-arm jump) —
    /// the pure counterpart of [`Ctx::edge_action`] (no stats).
    fn edge_has_action(&self, from: BlockId, to: BlockId) -> bool {
        self.f().arm_scopes.iter().any(|s| s.entry == to)
            || self
                .f()
                .arm_bodies
                .last()
                .is_some_and(|ab| !ab.slice.contains(&to))
            || matches!(
                self.f().eclass.get(&(from, to)),
                Some(EdgeClass::Break { .. } | EdgeClass::Continue { .. })
            )
    }

    // ── Emission ───────────────────────────────────────────────────

    fn emit_node(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let cov = self.f_mut().cov(id);
        match cov {
            Cov::Uniform(p) if p == active => self.emit_content(id, active, follow, out),
            Cov::Uniform(Some(p)) => self.wrap_try(id, p, follow, out),
            Cov::Uniform(None) => {
                // Unprotected node inside plan `active`'s span
                // (non-contiguous protected range).
                self.stats.try_splits += 1;
                let region = active
                    .map(|a| self.f().plans[a].region)
                    .unwrap_or(usize::MAX);
                out.push(SNode::Honest(format!(
                    "try region {region}: statements inside the protected span are NOT protected (non-contiguous range) — emitted inside the try body regardless"
                )));
                self.emit_content(id, active, follow, out);
            }
            Cov::Mixed => self.emit_mixed(id, active, follow, out),
        }
    }

    /// Wrap a node in `try { … } catch …` for plan `p`.
    fn wrap_try(&mut self, id: RegionId, p: usize, follow: Follow, out: &mut Vec<SNode>) {
        self.wrap_try_run(&[id], p, follow, out);
    }

    /// Wrap a run of region nodes in ONE `try { … } catch …` (the
    /// coalesced form — see `emit_seq_children`).
    fn wrap_try_run(&mut self, ids: &[RegionId], p: usize, follow: Follow, out: &mut Vec<SNode>) {
        let (region, cuts, handlers) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts, plan.handlers.clone())
        };
        let wraps = {
            let f = self.f_mut();
            let n = f.wrap_counts.entry(p).or_insert(0);
            *n += 1;
            *n
        };
        if wraps > 1 {
            self.stats.try_splits += 1;
        }
        if cuts {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        let mut body = Vec::new();
        if cuts {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        if wraps > 1 {
            body.push(SNode::Honest(format!(
                "try region {region}: protected statements are not contiguous in the structured output — this is wrapper #{wraps} for the same region (catch body duplicated, finally-style)"
            )));
        }
        for &id in ids {
            self.emit_content(id, Some(p), follow, &mut body);
        }
        let mut catches = Vec::new();
        let mut seen = HashSet::new();
        for h in &handlers {
            if seen.insert(*h) {
                catches.push(self.emit_handler(*h));
            }
        }
        let note = if catches.len() > 1 {
            self.stats.multi_catch += 1;
            Some(format!(
                "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                catches.len()
            ))
        } else {
            None
        };
        let mut node = SNode::Try {
            body,
            catches,
            note,
        };
        // Handlers protected by an OUTER plan (nested try regions whose
        // protected range includes the inner handler — the es2abc
        // finally idiom: the inner catch body can itself throw, and the
        // outer handler runs the finally + rethrow): the whole
        // try/catch must be wrapped in the outer plan's try, or
        // exceptions from the inner handler escape unhandled and the
        // outer handler's body (and its phi temporaries) is silently
        // dropped (dream gate: local/exception-finally). Laminar plans
        // form a chain; walk it outward.
        let mut protected_handlers = handlers.clone();
        let mut current = p;
        let mut depth = 0usize;
        loop {
            depth += 1;
            if depth > self.f().plans.len() + 1 {
                break; // defensive: the laminar chain is finite
            }
            // The innermost outer plan protecting any handler. A plan
            // whose protected set lies INSIDE the handler's own sub-CFG
            // is already wrapped by the handler shim (nested try in the
            // catch body) — wrapping it again outside would duplicate
            // the catch (correct but redundant); skip those.
            let mut outer: Option<usize> = None;
            for h in &protected_handlers {
                if let Some(q) = self.f_mut().plan_of(*h)
                    && q != current
                {
                    let handled_inside = self.shim_plans.get(h).is_some_and(|plans| {
                        plans
                            .iter()
                            .any(|pl| pl.protected == self.f().plans[q].protected)
                    });
                    if handled_inside {
                        continue;
                    }
                    if outer.is_none_or(|o| {
                        self.f().plans[q].protected.len() < self.f().plans[o].protected.len()
                    }) {
                        outer = Some(q);
                    }
                }
            }
            let Some(q) = outer else {
                break;
            };
            current = q;
            let (qregion, qhandlers) = {
                let plan = &self.f().plans[q];
                (plan.region, plan.handlers.clone())
            };
            let wraps = {
                let f = self.f_mut();
                let n = f.wrap_counts.entry(q).or_insert(0);
                *n += 1;
                *n
            };
            if wraps > 1 {
                self.stats.try_splits += 1;
            }
            self.stats.try_catches += 1;
            let mut qcatches = Vec::new();
            let mut seen = HashSet::new();
            for h in &qhandlers {
                if seen.insert(*h) {
                    qcatches.push(self.emit_handler(*h));
                }
            }
            node = SNode::Try {
                body: vec![node],
                catches: qcatches,
                note: Some(format!(
                    "try region {qregion}: handler-protecting outer try (finally idiom) — wrapped around region {region}'s try/catch (wrapper #{wraps})"
                )),
            };
            protected_handlers = qhandlers;
        }
        out.push(node);
    }

    /// A mixed-coverage node: descend (or wrap whole when the head is
    /// protected — the documented cut approximation).
    fn emit_mixed(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let node = self.f().node(id).clone();
        match node {
            RegionNode::Seq(children) => self.emit_seq_children(&children, active, follow, out),
            RegionNode::If { head, .. } => {
                let hp = self.f_mut().plan_of(head);
                if hp.is_some() && hp != active {
                    self.wrap_try(id, hp.expect("checked"), follow, out);
                } else {
                    self.emit_if(id, active, follow, out);
                }
            }
            RegionNode::Loop { header, kind, body } => {
                let hp = self.f_mut().plan_of(header);
                if hp.is_some() && hp != active {
                    self.wrap_try(id, hp.expect("checked"), follow, out);
                } else {
                    self.emit_loop(id, header, kind, body, active, follow, out);
                }
            }
            RegionNode::Labeled { label, body } => {
                let mut inner = Vec::new();
                self.emit_node(body, active, follow, &mut inner);
                out.push(SNode::Labeled {
                    label: format!("L${}", label.index()),
                    body: inner,
                });
            }
            RegionNode::Irreducible { .. } => self.emit_irreducible(id, active, out),
            RegionNode::Block(b) => self.emit_leaf(b, follow, out),
            RegionNode::Alternates(_) => {
                // Reached only through the sequence handler; defensive.
                self.emit_alternates_wrapped(id, Vec::new(), active, out);
            }
        }
    }

    fn emit_content(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let node = self.f().node(id).clone();
        match node {
            RegionNode::Block(b) => {
                if self.f_mut().skip_blocks.remove(&b) {
                    return; // consumed by a loop header/latch
                }
                self.emit_leaf(b, follow, out);
            }
            RegionNode::Seq(children) => self.emit_seq_children(&children, active, follow, out),
            RegionNode::Alternates(_) => self.emit_alternates_wrapped(id, Vec::new(), active, out),
            RegionNode::Labeled { label, body } => {
                let mut inner = Vec::new();
                self.emit_node(body, active, follow, &mut inner);
                out.push(SNode::Labeled {
                    label: format!("L${}", label.index()),
                    body: inner,
                });
            }
            RegionNode::If { .. } => self.emit_if(id, active, follow, out),
            RegionNode::Loop { header, kind, body } => {
                self.emit_loop(id, header, kind, body, active, follow, out)
            }
            RegionNode::Irreducible { .. } => self.emit_irreducible(id, active, out),
        }
    }

    /// Sequence-run fold (d-P4): a leaf conditional `b` whose one edge
    /// falls structurally into the NEXT sequence item while the other
    /// edge either (a) is a cross-arm edge into the sibling arm — the
    /// `c14 ? X : (c15 ? Y : X)` / `if (c14 || !c15) {X} else {Y}`
    /// shared-arm diamond — or (b) skips ahead to a later point of the
    /// run — the ordinary `if (c) { … }` shape the acyclic structurer
    /// degrades to a plain run when the merge is outside the arm set
    /// (and the optional-chain `if (x == null) goto shared` family,
    /// where the shared arm rejoins several blocks later). Dropping
    /// such a conditional (emission v1) runs the skipped blocks on
    /// BOTH paths — wrong. The fold emits a real `if (c) { run } else
    /// { … }`, consuming the skipped run of plain blocks; the else arm
    /// is the cross-arm tail duplication (a), or just the skip edge's
    /// phi assigns (b). Returns the number of sequence items consumed
    /// (0 = no fold, emit normally).
    fn try_run_fold(
        &mut self,
        children: &[RegionId],
        i: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> usize {
        const MAX_ARM: usize = 8;
        if i + 1 >= children.len() {
            return 0;
        }
        let RegionNode::Block(b) = self.f().node(children[i]).clone() else {
            return 0;
        };
        if self.f_mut().cov(children[i]) != Cov::Uniform(active) {
            return 0;
        }
        let parts = self.block_parts(b);
        let Term::Cond(cond, t, f) = parts.term else {
            return 0;
        };
        // Orientation: exactly one edge structural (targets the next
        // item's first-executed block, no terminator action), the other
        // the "skip" edge (no action either — breaks/continues emit
        // normally).
        let Follow::Entry(next_entry) = self.entry_of(children[i + 1]) else {
            return 0;
        };
        let (skip, swapped) = if t == next_entry && !self.edge_has_action(b, t) {
            (f, false)
        } else if f == next_entry && !self.edge_has_action(b, f) {
            (t, true)
        } else {
            return 0;
        };
        if skip == next_entry || self.edge_has_action(b, skip) {
            return 0;
        }
        // The skip arm's content: the cross-arm tail duplication when
        // the edge jumps into a sibling arm, otherwise empty (the plain
        // skip-ahead guard).
        let is_dup = self.f().cross_arm.contains(&(b, skip));
        let (dup, stop, nblocks) = if is_dup {
            let Some((nodes, stop, nb)) = self.cross_arm_dup(b, skip) else {
                return 0;
            };
            (nodes, stop, nb)
        } else {
            (Vec::new(), DupStop::Rejoin(skip), 0)
        };
        // Terminal skip arms need no run consumption: the leaf-level
        // fold already handles them.
        let DupStop::Rejoin(rejoin) = stop else {
            return 0;
        };
        // Find the arm length: the run of plain blocks after `i` whose
        // end rejoins at `rejoin` exactly where the sequence continues.
        let after = |k: usize, ctx: &Self| {
            if k < children.len() {
                ctx.entry_of(children[k])
            } else {
                follow
            }
        };
        let mut k = i + 1;
        let mut arm: Vec<BlockId> = Vec::new();
        let ok = loop {
            if k >= children.len() || arm.len() >= MAX_ARM {
                break false;
            }
            let RegionNode::Block(sb) = self.f().node(children[k]).clone() else {
                break false;
            };
            if self.f_mut().cov(children[k]) != Cov::Uniform(active) {
                break false;
            }
            let sparts = self.block_parts(sb);
            arm.push(sb);
            k += 1;
            match sparts.term {
                // The arm's last block rejoins the sequence exactly at
                // the dup tail's rejoin point.
                Term::Branch(d)
                    if !self.edge_has_action(sb, d)
                        && d == rejoin
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
                    break true;
                }
                // The arm's last block is terminal: only the skip arm
                // falls through, to the continuation after the run.
                Term::None if Self::dup_ok_for_follow(stop, after(k, self)) => {
                    break true;
                }
                // Mid-arm block: must fall structurally into the next
                // sequence item.
                Term::Branch(d)
                    if !self.edge_has_action(sb, d)
                        && k < children.len()
                        && Follow::Entry(d) == self.entry_of(children[k]) => {}
                _ => break false,
            }
        };
        if !ok {
            return 0;
        }
        // Commit: head statements, phi partition, arms.
        Self::push_stmts(out, Self::stmts_leaves(&parts.main));
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        Self::push_stmts(out, Self::stmts_leaves(&rest));
        let (phi_struct, phi_skip) = if swapped {
            (phi_f, phi_t)
        } else {
            (phi_t, phi_f)
        };
        let mut then: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut then, Self::stmts_leaves(&phi_struct));
        for (n, &sb) in arm.iter().enumerate() {
            let fl = if n + 1 < arm.len() {
                Follow::Entry(arm[n + 1])
            } else {
                after(k, self)
            };
            self.emit_leaf(sb, fl, &mut then);
        }
        let mut otherwise: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_skip));
        otherwise.extend(dup);
        if is_dup {
            self.stats.cross_arm_folds += 1;
            self.stats.cross_arm_dup_blocks += nblocks;
            self.folded_xarms.insert((b, skip));
        }
        self.stats.ifs += 1;
        out.push(SNode::If {
            cond: if swapped { negate(&cond) } else { cond },
            then,
            otherwise,
        });
        1 + arm.len()
    }

    /// Sequence emission with [`RegionNode::Alternates`] pre-registration:
    /// arm-entry labels are in scope for everything emitted BEFORE the
    /// alternates node in the same sequence.
    fn emit_seq_children(
        &mut self,
        children: &[RegionId],
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let mut i = 0;
        while i < children.len() {
            // Try-run coalescing: a maximal run of consecutive children
            // uniformly inside the same plan wraps in ONE try/catch
            // (es2abc protected ranges are contiguous; without
            // coalescing every block would get its own wrapper).
            if let Cov::Uniform(Some(p)) = self.f_mut().cov(children[i])
                && Some(p) != active
            {
                let mut j = i + 1;
                while j < children.len() && self.f_mut().cov(children[j]) == Cov::Uniform(Some(p)) {
                    j += 1;
                }
                let fl = if j < children.len() {
                    self.entry_of(children[j])
                } else {
                    follow
                };
                self.wrap_try_run(&children[i..j], p, fl, out);
                i = j;
                continue;
            }
            let next_alt = (i..children.len()).find(|&j| {
                matches!(self.f().node(children[j]), RegionNode::Alternates(_))
                    && self.f_mut().cov(children[j]) == Cov::Uniform(active)
            });
            let Some(j) = next_alt else {
                let consumed = self.try_run_fold(children, i, active, follow, out);
                if consumed > 0 {
                    i += consumed;
                    continue;
                }
                let fl = if i + 1 < children.len() {
                    self.entry_of(children[i + 1])
                } else {
                    follow
                };
                self.emit_node(children[i], active, fl, out);
                i += 1;
                continue;
            };
            // Register the arm-entry labels, then emit the prefix.
            let scopes: Vec<ArmScope> = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms
                    .iter()
                    .filter_map(|&a| match self.f().node(a) {
                        RegionNode::Labeled { label, .. } => Some(ArmScope {
                            entry: *label,
                            label: format!("L${}", label.index()),
                        }),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            for s in scopes {
                self.f_mut().arm_scopes.push(s);
            }
            while i < j {
                let consumed = self.try_run_fold(children, i, active, follow, out);
                if consumed > 0 {
                    i += consumed;
                    continue;
                }
                let fl = if i + 1 < j {
                    self.entry_of(children[i + 1])
                } else {
                    Follow::Unknown // the alternates follow: clean forms off
                };
                self.emit_node(children[i], active, fl, out);
                i += 1;
            }
            let prefix = std::mem::take(out);
            self.emit_alternates_wrapped(children[j], prefix, active, out);
            let popped = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms.len(),
                _ => 0,
            };
            for _ in 0..popped {
                self.f_mut().arm_scopes.pop();
            }
            i = j + 1;
        }
    }

    /// The first-executed block of a region (for the clean-loop-form
    /// continuation check).
    fn entry_of(&self, id: RegionId) -> Follow {
        match self.f().node(id) {
            RegionNode::Block(b) => Follow::Entry(*b),
            RegionNode::If { head, .. } => Follow::Entry(*head),
            RegionNode::Loop { header, .. } => Follow::Entry(*header),
            RegionNode::Labeled { label, .. } => Follow::Entry(*label),
            RegionNode::Seq(children) => children
                .first()
                .map(|&c| self.entry_of(c))
                .unwrap_or(Follow::Tail),
            RegionNode::Alternates(_) | RegionNode::Irreducible { .. } => Follow::Unknown,
        }
    }

    /// Emit a leaf block: statements, phi placement, terminator actions.
    /// `follow` is the block's structural continuation (the cross-arm
    /// tail-duplication fold needs it to know where a duplicated tail
    /// may fall through).
    fn emit_leaf(&mut self, b: BlockId, follow: Follow, out: &mut Vec<SNode>) {
        let parts = self.block_parts(b);
        Self::push_stmts(out, Self::stmts_leaves(&parts.main));
        match parts.term {
            Term::None => {
                // Defensive: phi assigns without an out-edge.
                Self::push_stmts(out, Self::stmts_leaves(&parts.phi));
            }
            Term::Branch(dest) => {
                Self::push_stmts(out, Self::stmts_leaves(&parts.phi));
                if let Some(act) = self.edge_action(b, dest) {
                    out.push(act);
                } else if self.f().cross_arm.contains(&(b, dest))
                    && let Some(dup) = self.try_cross_arm_fold(b, dest, follow)
                {
                    // The edge jumps into a sibling arm (the es2abc
                    // `goto shared` idiom): duplicate the shared tail.
                    out.extend(dup);
                }
            }
            Term::Cond(cond, t, f) => {
                let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                if !rest.is_empty() {
                    Self::push_stmts(out, Self::stmts_leaves(&rest));
                }
                let act_t = self.edge_action(b, t);
                let act_f = self.edge_action(b, f);
                // Cross-arm edges (the `goto shared` idiom): duplicate
                // the sibling arm's shared tail into this arm (after
                // the edge's phi assigns).
                let dup_t = if act_t.is_none() && self.f().cross_arm.contains(&(b, t)) {
                    self.try_cross_arm_fold(b, t, follow)
                } else {
                    None
                };
                let dup_f = if act_f.is_none() && self.f().cross_arm.contains(&(b, f)) {
                    self.try_cross_arm_fold(b, f, follow)
                } else {
                    None
                };
                let mut then: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
                then.extend(act_t);
                if let Some(dup) = dup_t {
                    then.extend(dup);
                }
                let mut otherwise: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                otherwise.extend(act_f);
                if let Some(dup) = dup_f {
                    otherwise.extend(dup);
                }
                match (then.is_empty(), otherwise.is_empty()) {
                    (true, true) => {
                        // Both edges are structural and neither is a
                        // foldable cross-arm edge. The condition has no
                        // remaining effect; drop it loudly.
                        self.stats.cross_arm_notes += 1;
                        out.push(SNode::Honest(format!(
                            "conditional at B{} dropped: both targets are structural (cross-arm tail-duplication fold bailed)",
                            b.index()
                        )));
                    }
                    (true, false) => {
                        self.stats.ifs += 1;
                        out.push(SNode::If {
                            cond: negate(&cond),
                            then: otherwise,
                            otherwise: Vec::new(),
                        });
                    }
                    _ => {
                        self.stats.ifs += 1;
                        out.push(SNode::If {
                            cond: cond.clone(),
                            then,
                            otherwise,
                        });
                    }
                }
            }
        }
    }

    /// Emit an `If` node: head statements, partitioned phi assigns, arms.
    fn emit_if(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let (head, then_r, else_r) = match self.f().node(id) {
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => (*head, *then, *otherwise),
            _ => unreachable!("emit_if on non-If"),
        };
        let parts = self.block_parts(head);
        Self::push_stmts(out, Self::stmts_leaves(&parts.main));
        let Term::Cond(cond, t, f) = parts.term else {
            // Defensive: an If head always ends in a conditional.
            out.push(SNode::Honest(format!(
                "region If head B{} has no conditional terminator (data shape) — arms emitted sequentially",
                head.index()
            )));
            if let Some(r) = then_r {
                self.emit_node(r, active, follow, out);
            }
            if let Some(r) = else_r {
                self.emit_node(r, active, follow, out);
            }
            return;
        };
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        Self::push_stmts(out, Self::stmts_leaves(&rest));
        let mut then: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
        if let Some(act) = self.edge_action(head, t) {
            then.push(act);
        } else if self.f().cross_arm.contains(&(head, t))
            && let Some(dup) = self.try_cross_arm_fold(head, t, follow)
        {
            then.extend(dup);
        }
        if let Some(r) = then_r {
            self.emit_node(r, active, follow, &mut then);
        }
        let mut otherwise: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
        if let Some(act) = self.edge_action(head, f) {
            otherwise.push(act);
        } else if self.f().cross_arm.contains(&(head, f))
            && let Some(dup) = self.try_cross_arm_fold(head, f, follow)
        {
            otherwise.extend(dup);
        }
        if let Some(r) = else_r {
            self.emit_node(r, active, follow, &mut otherwise);
        }
        self.stats.ifs += 1;
        out.push(SNode::If {
            cond: cond.clone(),
            then,
            otherwise,
        });
    }

    /// Emit a `Loop` node: clean `while`/`do…while` forms when the
    /// header/latch test is a clean split to the structural
    /// continuation; `while (true)` + leaf rules otherwise.
    fn emit_loop(
        &mut self,
        id: RegionId,
        header: BlockId,
        kind: LoopKind,
        body_r: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let _ = id;
        let label = self.f().loop_labels.get(&header).cloned();
        let body_blocks = self.f_mut().node_blocks(body_r);
        let parts = self.block_parts(header);

        // Clean `while (cond)`: the header ends in a conditional whose
        // one edge stays in the body and whose other is a plain break
        // to the continuation, AND the header is the body's
        // first-emitted block. The header must carry NO main statements
        // of its own: they run on every condition evaluation, so they
        // can neither hoist (the condition would read stale
        // temporaries) nor land at the body top (the condition reads
        // them before they run — the d-P4 dream gate caught this as
        // `ReferenceError`/stale-value failures, e.g. local/decrement);
        // the `while (true)` general form stays correct for them.
        if kind == LoopKind::While
            && self.first_block(body_r) == Some(header)
            && let Term::Cond(cond, t, f) = parts.term.clone()
            && clean_while_main_ok(&parts.main, &cond)
        {
            let t_in = body_blocks.contains(&t);
            let f_in = body_blocks.contains(&f);
            if t_in != f_in {
                let (stay, exit) = if t_in { (t, f) } else { (f, t) };
                let exit_is_break = matches!(
                    self.f().eclass.get(&(header, exit)),
                    Some(EdgeClass::Break { labeled: false, .. })
                );
                if exit_is_break
                    && self.plain_break_ok(exit, follow)
                    && self.body_breaks_ok(body_r, &body_blocks, exit, follow)
                {
                    self.stats.loops_while += 1;
                    self.emit_clean_while(
                        label, header, &cond, t_in, stay, exit, &parts, body_r, active, out,
                    );
                    return;
                }
            }
        }

        // Clean `do…while`: a unique latch carrying the test, emitted
        // last in the body.
        if kind == LoopKind::DoWhile
            && let Some(latch) = self.find_do_while_latch(header, &body_blocks)
        {
            let lp = self.block_parts(latch);
            if self.last_block(body_r) == Some(latch)
                && let Term::Cond(cond, t, f) = lp.term
            {
                let (cond_true_continues, cont_dest, exit) = if t == header {
                    (true, t, f)
                } else {
                    (false, f, t)
                };
                let exit_is_break = matches!(
                    self.f().eclass.get(&(latch, exit)),
                    Some(EdgeClass::Break { labeled: false, .. })
                );
                if exit_is_break && self.plain_break_ok(exit, follow) {
                    self.stats.loops_do_while += 1;
                    self.emit_do_while(
                        label,
                        latch,
                        &cond,
                        cond_true_continues,
                        cont_dest,
                        exit,
                        body_r,
                        active,
                        out,
                    );
                    return;
                }
            }
        }

        // General form: `while (true)` + leaf rules (always correct).
        self.stats.loops_while_true += 1;
        let mut body = Vec::new();
        self.emit_node(body_r, active, Follow::Tail, &mut body);
        out.push(SNode::While {
            label,
            cond: None,
            body,
        });
    }

    /// The clean `while (cond)` form (preconditions checked by the caller).
    fn emit_clean_while(
        &mut self,
        label: Option<String>,
        header: BlockId,
        cond: &Expr,
        cond_true_stays: bool,
        stay: BlockId,
        exit: BlockId,
        parts: &BlockParts,
        body_r: RegionId,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
        let (phi_stay, phi_exit, rest) = Self::partition_phi(&parts.phi, stay, exit);
        let mut body: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut body, Self::stmts_leaves(&parts.main));
        Self::push_stmts(&mut body, Self::stmts_leaves(&phi_stay));
        Self::push_stmts(&mut body, Self::stmts_leaves(&rest));
        // The header block is consumed; the body region emits without it.
        self.f_mut().skip_blocks.insert(header);
        self.emit_node(body_r, active, Follow::Tail, &mut body);
        let while_cond = if cond_true_stays {
            cond.clone()
        } else {
            negate(cond)
        };
        out.push(SNode::While {
            label,
            cond: Some(while_cond),
            body,
        });
        if !phi_exit.is_empty() {
            self.stats.exit_phi_after_loop += 1;
            Self::push_stmts(out, Self::stmts_leaves(&phi_exit));
        }
    }

    /// The clean `do { … } while (cond)` form (preconditions checked).
    fn emit_do_while(
        &mut self,
        label: Option<String>,
        latch: BlockId,
        cond: &Expr,
        cond_true_continues: bool,
        cont_dest: BlockId,
        exit: BlockId,
        body_r: RegionId,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
        let lp = self.block_parts(latch);
        let (phi_cont, phi_exit, rest) = Self::partition_phi(&lp.phi, cont_dest, exit);
        let lp_main: Vec<Leaf> = Self::stmts_leaves(&lp.main);
        let phi_cont = Self::stmts_leaves(&phi_cont);
        let rest = Self::stmts_leaves(&rest);
        let phi_exit = Self::stmts_leaves(&phi_exit);
        self.f_mut().skip_blocks.insert(latch);
        let mut body = Vec::new();
        self.emit_node(body_r, active, Follow::Tail, &mut body);
        Self::push_stmts(&mut body, lp_main);
        Self::push_stmts(&mut body, phi_cont);
        Self::push_stmts(&mut body, rest);
        let while_cond = if cond_true_continues {
            cond.clone()
        } else {
            negate(cond)
        };
        out.push(SNode::DoWhile {
            label,
            body,
            cond: while_cond,
        });
        if !phi_exit.is_empty() {
            self.stats.exit_phi_after_loop += 1;
            Self::push_stmts(out, phi_exit);
        }
    }

    /// The first block a region emits (only the trivially-known cases).
    fn first_block(&self, id: RegionId) -> Option<BlockId> {
        match self.f().node(id) {
            RegionNode::Block(b) => Some(*b),
            RegionNode::Seq(children) => children.first().and_then(|&c| self.first_block(c)),
            _ => None,
        }
    }

    /// The last block a region emits (only the trivially-known cases).
    fn last_block(&self, id: RegionId) -> Option<BlockId> {
        match self.f().node(id) {
            RegionNode::Block(b) => Some(*b),
            RegionNode::Seq(children) => children.last().and_then(|&c| self.last_block(c)),
            RegionNode::Labeled { body, .. } => self.last_block(*body),
            _ => None,
        }
    }

    /// Find the unique do-while latch: a body block with an unlabeled
    /// continue to the header and a conditional terminator.
    fn find_do_while_latch(
        &self,
        header: BlockId,
        body_blocks: &BTreeSet<BlockId>,
    ) -> Option<BlockId> {
        let mut found = None;
        for ((from, to), class) in &self.f().eclass {
            if *to == header
                && body_blocks.contains(from)
                && matches!(class, EdgeClass::Continue { labeled: false, .. })
                && matches!(self.block_parts(*from).term, Term::Cond(..))
            {
                if found.is_some() {
                    return None; // not unique
                }
                found = Some(*from);
            }
        }
        found
    }

    /// Defensive audit for the clean-while form: every unlabeled break
    /// from inside the body must target the continuation (or the
    /// header exit). Violations disable the clean form.
    fn body_breaks_ok(
        &self,
        body_r: RegionId,
        body_blocks: &BTreeSet<BlockId>,
        exit: BlockId,
        follow: Follow,
    ) -> bool {
        let _ = body_r;
        for ((from, to), class) in &self.f().eclass {
            if !body_blocks.contains(from) || body_blocks.contains(to) {
                continue;
            }
            if let EdgeClass::Break { labeled: false, .. } = class
                && *to != exit
                && !self.plain_break_ok(*to, follow)
            {
                return false;
            }
        }
        true
    }

    /// Emit an `Alternates` node with its preceding-sibling prefix:
    /// nested labeled blocks such that `break L$arm` from the prefix
    /// lands at the arm's start, and mid-arm exits use the wrapper
    /// label `A$k`:
    ///
    /// ```text
    /// A$0: {
    ///   L$a0: {
    ///     L$a1: { …prefix… }
    ///     …arm a1…
    ///     break A$0;
    ///   }
    ///   …arm a0…   // falls through to the continuation
    /// }
    /// ```
    fn emit_alternates_wrapped(
        &mut self,
        id: RegionId,
        prefix: Vec<SNode>,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
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
            out.extend(prefix);
            out.push(SNode::Honest(
                "malformed alternates node (no labeled arms) — content dropped".to_string(),
            ));
            return;
        }
        self.stats.alternates += 1;
        let done = format!("A${}", self.alt_counter);
        self.alt_counter += 1;
        // Emit arm bodies (mid-arm exits become `break <done>`).
        let mut bodies: Vec<(String, Vec<SNode>)> = Vec::new();
        for (entry, body_r) in &arms {
            let slice = self.f_mut().node_blocks(*body_r);
            self.f_mut().arm_bodies.push(ArmBody {
                done: done.clone(),
                slice,
            });
            let mut b = Vec::new();
            self.emit_node(*body_r, active, Follow::Tail, &mut b);
            self.f_mut().arm_bodies.pop();
            bodies.push((format!("L${}", entry.index()), b));
        }
        // Assemble inside-out: arms[1..] nest, arms[0] falls through to
        // the wrapper end (the continuation).
        let mut iter = bodies.into_iter();
        let (first_label, first_body) = iter.next().expect("non-empty arms");
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
        out.push(SNode::Labeled {
            label: done,
            body: wrapper,
        });
    }

    /// Emit an `Irreducible` node as the state-variable dispatch escape
    /// hatch of design §4.2.4 (with the honesty comment).
    fn emit_irreducible(&mut self, id: RegionId, active: Option<usize>, out: &mut Vec<SNode>) {
        let (blocks, edges) = match self.f().node(id) {
            RegionNode::Irreducible { blocks, edges } => (blocks.clone(), edges.clone()),
            _ => unreachable!("emit_irreducible on non-Irreducible"),
        };
        let _ = active;
        self.stats.irreducible_fallbacks += 1;
        self.stats.state_machine_blocks += blocks.len();
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
        let state = format!("s${}", self.state_counter);
        self.state_counter += 1;
        // The entry: a block with an in-edge from outside the set, else
        // the smallest block (deterministic).
        let entry = blocks
            .iter()
            .copied()
            .find(|&b| {
                self.f()
                    .eclass
                    .keys()
                    .any(|&(from, t)| t == b && !set.contains(&from))
            })
            .unwrap_or(blocks[0]);
        out.push(SNode::Honest(format!(
            "IRREDUCIBLE CFG escape hatch (design §4.2.4): blocks [{}] resisted structuring — emitted as a state-variable dispatch loop; readable but NOT source-shaped",
            blocks
                .iter()
                .map(|b| format!("B{}", b.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )));
        // let s$k = <entry>;
        out.push(SNode::Stmts(vec![Leaf::Decl {
            name: state.clone(),
            mutable: true,
            value: Some(num_lit(entry.index() as f64)),
        }]));
        let _ = edges;
        // Dispatch arms: entry first, then sorted (deterministic).
        let mut order: Vec<BlockId> = vec![entry];
        order.extend(blocks.iter().copied().filter(|&b| b != entry));
        let mut arms: Vec<(BlockId, Vec<SNode>)> = Vec::new();
        for b in order {
            let parts = self.block_parts(b);
            let mut body = Vec::new();
            Self::push_stmts(&mut body, Self::stmts_leaves(&parts.main));
            Self::push_stmts(&mut body, Self::stmts_leaves(&parts.phi));
            match parts.term {
                Term::None => {}
                Term::Branch(dest) => {
                    if set.contains(&dest) {
                        body.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(dest.index() as f64),
                        }]));
                        body.push(SNode::Continue { label: None });
                    } else {
                        out_exits(self, &mut body, b, dest);
                    }
                }
                Term::Cond(cond, t, f) => {
                    let mut then = Vec::new();
                    let mut otherwise = Vec::new();
                    if set.contains(&t) {
                        then.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(t.index() as f64),
                        }]));
                        then.push(SNode::Continue { label: None });
                    } else {
                        out_exits(self, &mut then, b, t);
                    }
                    if set.contains(&f) {
                        otherwise.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(f.index() as f64),
                        }]));
                        otherwise.push(SNode::Continue { label: None });
                    } else {
                        out_exits(self, &mut otherwise, b, f);
                    }
                    body.push(SNode::If {
                        cond: cond.clone(),
                        then,
                        otherwise,
                    });
                }
            }
            arms.push((b, body));
        }
        // Build the nested if-chain.
        let mut chain: Vec<SNode> = vec![SNode::Honest(
            "dispatch fallthrough (unreachable)".to_string(),
        )];
        for (b, body) in arms.into_iter().rev() {
            chain = vec![SNode::If {
                cond: Expr::Compare {
                    op: CmpOp::StrictEq,
                    left: Box::new(Expr::Ident(state.clone())),
                    right: Box::new(num_lit(b.index() as f64)),
                },
                then: body,
                otherwise: chain,
            }];
        }
        out.push(SNode::While {
            label: None,
            cond: None,
            body: chain,
        });
    }

    /// The whole-function state-machine fallback (see `build`): d-P1
    /// detects irreducible cores and CrossEdge escape hatches, but the
    /// region tree still threads those blocks acyclically — the
    /// back-flow is not representable as loops, so the whole reachable
    /// function falls back to state-variable dispatch.
    fn emit_whole_function_state_machine(&mut self, out: &mut Vec<SNode>) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        let Some(entry) = f.blocks.first().copied() else {
            return;
        };
        let mut set = BTreeSet::new();
        let mut queue = std::collections::VecDeque::from([entry]);
        set.insert(entry);
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if set.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        let blocks: Vec<BlockId> = set.iter().copied().collect();
        self.stats.irreducible_fallbacks += 1;
        let cores: Vec<String> = self
            .f()
            .tree
            .irreducible
            .iter()
            .map(|c| {
                format!(
                    "[{}]",
                    c.blocks
                        .iter()
                        .map(|b| format!("B{}", b.index()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect();
        let crosses: Vec<String> = self
            .f()
            .tree
            .escape_hatches
            .iter()
            .filter_map(|e| match e {
                abcd_analysis::control::EscapeHatch::CrossEdge { from, to } => {
                    Some(format!("B{}→B{}", from.index(), to.index()))
                }
                _ => None,
            })
            .collect();
        out.push(SNode::Honest(format!(
            "IRREDUCIBLE CFG escape hatch (design §4.2.4): cores [{}], cross edges [{}] — the WHOLE function is emitted as a state-variable dispatch loop (coarse but honest; expected 0 on the es2abc corpus)",
            cores.join(", "),
            crosses.join(", ")
        )));
        self.emit_state_machine(&blocks, entry, out);
    }

    /// State-variable dispatch over `blocks` (entry first, then
    /// sorted): `let s$k = <entry>; while (true) { if (s$k === …) … }`.
    fn emit_state_machine(&mut self, blocks: &[BlockId], entry: BlockId, out: &mut Vec<SNode>) {
        self.stats.state_machine_blocks += blocks.len();
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
        let state = format!("s${}", self.state_counter);
        self.state_counter += 1;
        out.push(SNode::Stmts(vec![Leaf::Decl {
            name: state.clone(),
            mutable: true,
            value: Some(num_lit(entry.index() as f64)),
        }]));
        let mut order: Vec<BlockId> = vec![entry];
        order.extend(blocks.iter().copied().filter(|b| *b != entry));
        let mut arms: Vec<(BlockId, Vec<SNode>)> = Vec::new();
        for b in order {
            let parts = self.block_parts(b);
            let mut body = Vec::new();
            Self::push_stmts(&mut body, Self::stmts_leaves(&parts.main));
            Self::push_stmts(&mut body, Self::stmts_leaves(&parts.phi));
            match parts.term {
                Term::None => {}
                Term::Branch(dest) => {
                    if set.contains(&dest) {
                        body.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(dest.index() as f64),
                        }]));
                        body.push(SNode::Continue { label: None });
                    } else {
                        out_exits(self, &mut body, b, dest);
                    }
                }
                Term::Cond(cond, t, f) => {
                    let mut then = Vec::new();
                    let mut otherwise = Vec::new();
                    for (dest, arm) in [(t, &mut then), (f, &mut otherwise)] {
                        if set.contains(&dest) {
                            arm.push(SNode::Stmts(vec![Leaf::Assign {
                                target: state.clone(),
                                value: num_lit(dest.index() as f64),
                            }]));
                            arm.push(SNode::Continue { label: None });
                        } else {
                            out_exits(self, arm, b, dest);
                        }
                    }
                    body.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                }
            }
            arms.push((b, body));
        }
        // Build the nested if-chain.
        let mut chain: Vec<SNode> = vec![SNode::Honest(
            "dispatch fallthrough (unreachable)".to_string(),
        )];
        for (b, body) in arms.into_iter().rev() {
            chain = vec![SNode::If {
                cond: Expr::Compare {
                    op: CmpOp::StrictEq,
                    left: Box::new(Expr::Ident(state.clone())),
                    right: Box::new(num_lit(b.index() as f64)),
                },
                then: body,
                otherwise: chain,
            }];
        }
        out.push(SNode::While {
            label: None,
            cond: None,
            body: chain,
        });
    }

    /// Emit one catch handler body through its shim region tree.
    fn emit_handler(&mut self, h: BlockId) -> CatchClause {
        // The binding: Stage A's CatchBind marker at the handler head.
        let binding = self
            .bmap
            .get(&h)
            .and_then(|&bi| self.rf.blocks[bi].stmts.first())
            .and_then(|s| match s {
                Stmt::CatchBind { name } => Some(name.clone()),
                _ => None,
            });
        let Some(tree) = self.shim_trees.get(&h).cloned() else {
            return CatchClause {
                binding,
                body: vec![SNode::Honest(format!(
                    "handler B{}: body unavailable (no shim — exotic entry shape)",
                    h.index()
                ))],
            };
        };
        let plans = self.shim_plans.get(&h).cloned().unwrap_or_default();
        let mut body = Vec::new();
        self.frames.push(Frame::new(tree, plans));
        if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, &mut body);
        }
        self.frames.pop();
        CatchClause { binding, body }
    }
}

/// An out-of-set edge inside the irreducible fallback: emit a plain
/// `break` (the dispatch loop is innermost) plus an honesty note when
/// the target is not unique.
fn out_exits(ctx: &mut Ctx, body: &mut Vec<SNode>, from: BlockId, to: BlockId) {
    if let Some(act) = ctx.edge_action(from, to) {
        body.push(act);
    } else {
        body.push(SNode::Honest(format!(
            "state-machine exit B{}→B{}: target outside the irreducible core — plain break assumes the structured continuation follows",
            from.index(),
            to.index()
        )));
        body.push(SNode::Break { label: None });
    }
}

/// A number literal expression.
fn num_lit(v: f64) -> Expr {
    Expr::Lit(Lit::Number(v.to_bits()))
}

/// Whether a node is a control-flow terminal (break/continue/return/
/// throw) — used to avoid appending dead `break`s after alternates arms
/// and switch cases.
pub fn is_terminal_node(n: &SNode) -> bool {
    match n {
        SNode::Break { .. } | SNode::Continue { .. } => true,
        SNode::Stmts(s) => matches!(
            s.last(),
            Some(Leaf::Raw(
                Stmt::Return(_) | Stmt::Throw(_) | Stmt::Unreachable
            ))
        ),
        _ => false,
    }
}

/// Clean-`while` precondition (d-P4): the header's main statements run
/// on EVERY condition evaluation, so the clean form (which emits them
/// at the body top, AFTER the condition) is only sound when the
/// condition does not reference any block-scoped temporary they declare
/// (the dream gate caught the violation as `i$1 is not defined` /
/// stale-value failures, e.g. local/decrement). Phi wiring (`var`
/// decls + per-edge assigns) is hoisted and correctly valued at the
/// condition point, so it is always allowed. The for-of/for-in header
/// plumbing passes this rule (its condition reads the done-flag phi,
/// not the body-top temporaries) — the desugar folds keep firing.
fn clean_while_main_ok(main: &[Stmt], cond: &Expr) -> bool {
    let mut refs: BTreeSet<&str> = BTreeSet::new();
    let mut stack = vec![cond];
    while let Some(e) = stack.pop() {
        match e {
            Expr::Ident(name) => {
                refs.insert(name.as_str());
            }
            Expr::Temp { name, .. } => {
                refs.insert(name.as_str());
            }
            _ => stack.extend(crate::folds::expr_children(e)),
        }
    }
    main.iter().all(|s| match s {
        Stmt::PhiAssign { .. } | Stmt::PhiDecl { .. } | Stmt::Elided { .. } => true,
        Stmt::Declare { name, .. } => !refs.contains(name.as_str()),
        _ => false,
    })
}

/// Negate a condition, simplifying the wrapper forms es2abc produces
/// (`istrue`/`isfalse`/logical-not and reversible comparisons).
pub fn negate(e: &Expr) -> Expr {
    match e {
        Expr::Unary {
            op: UnOp::IsTrue,
            operand,
        } => Expr::Unary {
            op: UnOp::IsFalse,
            operand: operand.clone(),
        },
        Expr::Unary {
            op: UnOp::IsFalse,
            operand,
        } => Expr::Unary {
            op: UnOp::IsTrue,
            operand: operand.clone(),
        },
        Expr::Unary {
            op: UnOp::LogicalNot,
            operand,
        } => *operand.clone(),
        Expr::Compare { op, left, right } => {
            let flipped = match op {
                CmpOp::Eq => Some(CmpOp::NotEq),
                CmpOp::NotEq => Some(CmpOp::Eq),
                CmpOp::StrictEq => Some(CmpOp::StrictNotEq),
                CmpOp::StrictNotEq => Some(CmpOp::StrictEq),
                CmpOp::Less => Some(CmpOp::GreaterEq),
                CmpOp::GreaterEq => Some(CmpOp::Less),
                CmpOp::Greater => Some(CmpOp::LessEq),
                CmpOp::LessEq => Some(CmpOp::Greater),
                CmpOp::In | CmpOp::InstanceOf => None,
            };
            match flipped {
                Some(op) => Expr::Compare {
                    op,
                    left: left.clone(),
                    right: right.clone(),
                },
                None => Expr::Unary {
                    op: UnOp::LogicalNot,
                    operand: Box::new(e.clone()),
                },
            }
        }
        _ => Expr::Unary {
            op: UnOp::LogicalNot,
            operand: Box::new(e.clone()),
        },
    }
}
