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
        /// The `finally { … }` body — set only by the d-P8 finally
        /// fold ([`crate::folds`]) after it proves the es2abc
        /// duplicate-finally idiom; `None` everywhere else.
        finally: Option<Vec<SNode>>,
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
    /// Handler continuations (try joins) hoisted out of a wrapped
    /// mixed-coverage conditional to after the try/catch (d-P5).
    pub try_join_hoists: usize,
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
    /// Handler-shim cut edges repaired by duplicating the small
    /// terminal main-universe tail inline (N76).
    pub handler_tail_dups: usize,
    /// Blocks duplicated by the handler-tail fold.
    pub handler_tail_dup_blocks: usize,
    /// Try/catch towers emitted with de-absorbed continuations (N77):
    /// handler bodies stopped at the shared joins; the joins were
    /// emitted once per tower level.
    pub tower_deabsorbs: usize,
    /// Towers that bailed back to the legacy absorbed emission (N77
    /// verification failure — the honest fallback).
    pub deabsorb_bails: usize,
    /// Shared-join blocks emitted once per tower (they would have been
    /// duplicated into every absorbing catch clause).
    pub deabsorb_join_blocks: usize,
    /// Loops re-emitted as do-while with a cut try/catch INSIDE the
    /// body (the catch's `continue` targets the in-loop test — N78,
    /// test262 try/S12.14_A9_T5).
    pub loop_cut_rewrites: usize,
    /// Loop-cut candidates that failed a guard and kept the legacy
    /// whole-loop wrap (the honest fallback).
    pub loop_cut_bails: usize,
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

/// An in-flight join hoist (d-P5, RC1): unprotected tail region nodes
/// of a cut mixed-coverage `If`. While set, [`Ctx::emit_node`]
/// suppresses their inline emission; the driver emits them after the
/// try/catch (where the handlers rejoin).
#[derive(Clone, Debug)]
struct CutDefer {
    /// The deferred region nodes (removed as intercepted).
    ids: HashSet<RegionId>,
}

/// The phase-1 split classification of a mixed-coverage node for the
/// join hoist (d-P5, RC1): how the node partitions into a protected
/// skeleton (stays inside the try) and an unprotected deferred tail
/// (emitted after the try/catch).
#[derive(Clone, Debug)]
enum CutSplit {
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

/// One arm of a cut `If`.
#[derive(Clone, Debug)]
enum ArmCut {
    /// Fully protected AND every exit path terminal (throw/return or
    /// an edge with a structural action) — falling out would
    /// incorrectly route through the hoisted tail.
    Terminal,
    /// The arm splits into a protected prefix and a deferred tail.
    Splits(Box<CutSplit>),
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
    /// The in-flight join hoist (d-P5, RC1), when a cut `If` skeleton
    /// is being emitted.
    cut_defer: Option<CutDefer>,
    /// When this frame is a HANDLER SHIM: the handler entry (its
    /// sub-CFG block set is `Ctx::shim_sets[handler]`). Drives the
    /// handler-tail duplication at cut (out-of-set) terminator edges.
    shim_of: Option<BlockId>,
    /// N77: this frame is a UNIQUE-prefix handler shim (its block set
    /// is `Ctx::uniq_sets[handler]`, not `Ctx::shim_sets[handler]`).
    shim_uniq: bool,
    /// N77: this frame is a tower-JOIN shim (its out-of-set edges are
    /// verified inter-level fall-outs; `shim_of` stays `None`).
    join_shim: bool,
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
            cut_defer: None,
            shim_of: None,
            shim_uniq: false,
            join_shim: false,
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
    /// handler entry → its sub-CFG block set (d-P5: the handler's
    /// out-of-set Normal edges are its continuation targets — the
    /// join-hoist correctness condition).
    shim_sets: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Counter for `A$k` alternates-wrapper labels (deterministic).
    alt_counter: usize,
    /// Counter for `s$k` state-machine temporaries (deterministic).
    state_counter: usize,
    /// Cross-arm edges the tail-duplication fold repaired (the build()
    /// summary lists only the residual, unfolded ones).
    folded_xarms: BTreeSet<(BlockId, BlockId)>,
    /// Protected sets of the outer-finally wrappers currently being
    /// assembled ABOVE the emission point (the wrap_try_run chain,
    /// threads through `emit_handler` frames). Nested emissions must
    /// not re-wrap these plans: the wrappers physically enclose
    /// everything emitted while they are pending.
    pending_wraps: Vec<BTreeSet<BlockId>>,
    /// Rejoin entries of in-flight join hoists (`emit_cut_try`): while
    /// a hoisted try/catch's catch clauses are being emitted, the
    /// hoisted tail's entry block IS physically emitted right after the
    /// try/catch, so handler cut edges to it are safe fall-outs and the
    /// shim-tail duplication must stand down (N76 follow-up: golden
    /// s28/s29's join tail was duplicated into the catch body).
    hoist_rejoins: Vec<BlockId>,
    /// Verified fall-out targets (N76): while a `try/catch` whose
    /// physical continuation is KNOWN (the caller's `follow` resolves
    /// to a concrete next block) is being emitted, handler cut edges to
    /// that block are sound as plain catch-clause fall-outs — the
    /// run-fold may use them (`if/else` with the skip arm falling
    /// through) and the shim-tail duplication must stand down.
    verified_fallout: Vec<BlockId>,
    /// N77 de-absorption: blocks Normal-reachable from >= 2 handler
    /// entries (shared joins — see [`Ctx::build_deabsorb`]).
    shared_join: BTreeSet<BlockId>,
    /// Handler entry -> its UNIQUE prefix (reachable set minus the
    /// shared joins).
    uniq_sets: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Handler entry -> region tree over its unique prefix.
    uniq_trees: HashMap<BlockId, RegionTree>,
    /// Handler entry -> plans nested inside its unique prefix.
    uniq_plans: HashMap<BlockId, Vec<Plan>>,
    /// De-absorption shim module (unique-set boundary edges cut; join
    /// sets patched on demand in [`Ctx::join_tree`]).
    deabsorb_module: Option<Module>,
    /// Join block set -> its structured tree (None = failed; memoized).
    join_memo: HashMap<BTreeSet<BlockId>, Option<(RegionTree, Vec<Plan>)>>,
    /// Join sets currently being emitted by enclosing de-absorbed
    /// towers (nested towers must not re-emit them).
    pending_joins: Vec<BTreeSet<BlockId>>,
    /// Protected sets whose try wrapper PHYSICALLY encloses the current
    /// emission point with no intervening catch (a de-absorbed tower's
    /// clause/join contexts): wraps of these plans are suppressed —
    /// the wrapper already exists above.
    suppress_wraps: Vec<BTreeSet<BlockId>>,
    /// Every handler entry of the function (region order, deduped).
    all_handlers: Vec<BlockId>,
    /// Handler entry -> its raw Normal-reachable set (pre-trim), for
    /// the de-absorption foreign-reach check.
    handler_approx: HashMap<BlockId, BTreeSet<BlockId>>,
    /// Handler entry -> the root-frame plan indices it catches.
    handler_root_plans: HashMap<BlockId, Vec<usize>>,
    /// Shared-join blocks already emitted by a de-absorbed tower (a
    /// re-wrapped plan's tower must not emit them twice).
    emitted_joins: BTreeSet<BlockId>,
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
            deabsorb_module: None,
            join_memo: HashMap::new(),
            pending_joins: Vec::new(),
            suppress_wraps: Vec::new(),
            all_handlers: Vec::new(),
            handler_approx: HashMap::new(),
            handler_root_plans: HashMap::new(),
            emitted_joins: BTreeSet::new(),
        }
    }

    fn f(&self) -> &Frame {
        self.frames.last().expect("a frame is always active")
    }

    fn f_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame is always active")
    }

    /// The active frame's handler-shim block set (the legacy absorbed
    /// set or the N77 unique prefix, per the frame kind).
    fn frame_shim_set(&self) -> Option<&BTreeSet<BlockId>> {
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
    fn is_suppressed(&mut self, p: usize) -> bool {
        let protected = self.f().plans[p].protected.clone();
        self.suppress_wraps.contains(&protected)
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
            // along (their handlers get their own shims). A region
            // whose protected set ALSO covers an inner handler block
            // rides along too — transitively, once the inner handler's
            // own region is included: that is exactly the es2abc
            // finally idiom (the outer try protects the inner catch
            // body, whose blocks are dispatch-entered and therefore
            // never Normal-reachable members of this set), and
            // excluding it silently drops the outer finally's whole
            // try/catch — its handler body and its phi temporaries
            // (dream gate: opt-try-catch-func/test-nested-try-catch
            // `ReferenceError: v101 is not defined`, d-P5).
            let block_set: BTreeSet<BlockId> = fd.blocks.iter().copied().collect();
            let mut chosen: Vec<usize> = Vec::new();
            loop {
                let mut changed = false;
                for (i, tr) in f.try_regions.iter().enumerate() {
                    if chosen.contains(&i) {
                        continue;
                    }
                    let ok = tr.protected.iter().all(|b| {
                        block_set.contains(b)
                            || chosen.iter().any(|&j| {
                                f.try_regions[j].catches.iter().any(|cc| cc.handler == *b)
                            })
                    });
                    if ok {
                        chosen.push(i);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            chosen.sort_unstable();
            if std::env::var_os("ABCD_SHIM_DEBUG").is_some() {
                eprintln!(
                    "SHIM B{} (fn {}): set={:?} chosen={:?}",
                    h.index(),
                    fid.index(),
                    fd.blocks.iter().map(|b| b.index()).collect::<Vec<_>>(),
                    chosen
                );
            }
            fd.try_regions = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
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
            self.shim_sets.insert(h, set.clone());
            self.stats.handler_shims += 1;
        }
        self.shim_module = Some(shim);
        self.build_deabsorb(&approx_sets);
    }

    /// N77: the continuation de-absorption analysis. The legacy handler
    /// sets (above) ABSORB every Normal-reachable block up to the main
    /// universe, so a continuation Normal-reachable from several
    /// handler entries (a shared join — the es2abc finally idiom's
    /// dispatcher/rethrow tails and, transitively, everything
    /// downstream of them) is emitted inside every one of those
    /// handlers' catch clauses, and the outer-wrap chain re-emits the
    /// enclosing towers at every nested site: the emission is
    /// multiplicative in the finally nesting depth (test262
    /// try/S12.14_A7_T2 emitted ~12 MB from a 3,152-byte source).
    ///
    /// The de-absorption computes the shared joins J (blocks
    /// Normal-reachable from >= 2 handler entries) and each handler's
    /// UNIQUE prefix (its reachable set minus J). A try/catch tower
    /// (a plan plus its outer-wrap chain) then emits each handler's
    /// unique prefix in its catch clause and the shared joins ONCE:
    /// the blocks protected by a chain level inside that level's try
    /// body, the unprotected continuation after the outermost
    /// try/catch — exactly where the handlers' cut edges fall out
    /// (see [`Ctx::wrap_try_run`]).
    fn build_deabsorb(&mut self, approx_sets: &HashMap<BlockId, BTreeSet<BlockId>>) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        // J: blocks reachable from >= 2 handler entries.
        let mut reach_count: HashMap<BlockId, usize> = HashMap::new();
        for set in approx_sets.values() {
            for &b in set {
                *reach_count.entry(b).or_default() += 1;
            }
        }
        let shared: BTreeSet<BlockId> = reach_count
            .iter()
            .filter(|&(_, &n)| n >= 2)
            .map(|(&b, _)| b)
            .collect();
        if shared.is_empty() {
            return;
        }
        self.shared_join = shared;
        self.all_handlers = approx_sets.keys().copied().collect();
        self.handler_approx = approx_sets.clone();
        for (i, tr) in f.try_regions.iter().enumerate() {
            for c in &tr.catches {
                self.handler_root_plans
                    .entry(c.handler)
                    .or_default()
                    .push(i);
            }
        }
        // Unique prefixes. Handler entries are dispatch-only (no
        // Normal preds), so an entry is never shared and every unique
        // set contains its handler. Unique sets are pairwise disjoint:
        // a block in two of them would be shared.
        let mut uniq: HashMap<BlockId, BTreeSet<BlockId>> = HashMap::new();
        for (&h, set) in approx_sets {
            uniq.insert(h, set.difference(&self.shared_join).copied().collect());
        }
        // The de-absorption shim module: unique-set boundary edges cut
        // (join-set boundaries are patched on demand in `join_tree`).
        let mut dmod = self.module.clone();
        for set in uniq.values() {
            for &b in set {
                let Some(block) = dmod.block(b).cloned() else {
                    continue;
                };
                let Some(&last) = block.insts.last() else {
                    continue;
                };
                let new_op = match &dmod.inst(last).expect("inst").op {
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
                    dmod.inst_mut(last).expect("inst").op = op;
                }
            }
        }
        // Unique-handler shim functions + trees (the same ride-along
        // rule as the legacy shims).
        for (&h, set) in &uniq {
            if !set.contains(&h) {
                continue;
            }
            let mut blocks: Vec<BlockId> = vec![h];
            blocks.extend(set.iter().copied().filter(|b| *b != h));
            let name: Sym = dmod.sym.intern(&format!("$uhandler${}", h.index()));
            let fid = FuncId::new(dmod.functions.len() as u32);
            let mut fd = FunctionData::new(ClassId::new(0), name, self.rf.kind);
            fd.blocks = blocks;
            let block_set: BTreeSet<BlockId> = fd.blocks.iter().copied().collect();
            let mut chosen: Vec<usize> = Vec::new();
            loop {
                let mut changed = false;
                for (i, tr) in f.try_regions.iter().enumerate() {
                    if chosen.contains(&i) {
                        continue;
                    }
                    let ok = tr.protected.iter().all(|b| {
                        block_set.contains(b)
                            || chosen.iter().any(|&j| {
                                f.try_regions[j].catches.iter().any(|cc| cc.handler == *b)
                            })
                    });
                    if ok {
                        chosen.push(i);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            chosen.sort_unstable();
            fd.try_regions = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
            dmod.functions.push(fd);
            let tree = structure_regions(&dmod, fid);
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
            self.uniq_trees.insert(h, tree);
            self.uniq_plans.insert(h, plans);
            self.uniq_sets.insert(h, set.clone());
        }
        self.deabsorb_module = Some(dmod);
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

    /// Push a block's main statements and trailing phi assigns,
    /// honoring the exception-dispatch rule: for a block whose terminal
    /// statement is `throw`, the exceptional-edge phi assigns (the
    /// register flush the dispatching handler observes — N38) must
    /// execute BEFORE the `throw`; emitted after it they are dead code
    /// and the handler reads `undefined` temporaries (dream gate:
    /// upstream/optimizer try families, d-P5). Normal-edge assigns are
    /// unaffected (a `throw` block has no Normal successors; any found
    /// are kept in place defensively).
    fn push_main_phi(out: &mut Vec<SNode>, main: &[Stmt], phi: &[Stmt]) {
        let last_meaningful = main.iter().rposition(|s| !matches!(s, Stmt::Unreachable));
        let throw_at = last_meaningful.filter(|&i| matches!(main[i], Stmt::Throw(_)));
        if let Some(i) = throw_at
            && phi.iter().any(|s| {
                matches!(
                    s,
                    Stmt::PhiAssign {
                        exceptional: true,
                        ..
                    }
                )
            })
        {
            let (xphi, rest): (Vec<Stmt>, Vec<Stmt>) = phi.iter().cloned().partition(|s| {
                matches!(
                    s,
                    Stmt::PhiAssign {
                        exceptional: true,
                        ..
                    }
                )
            });
            Self::push_stmts(out, Self::stmts_leaves(&main[..i]));
            Self::push_stmts(out, Self::stmts_leaves(&xphi));
            Self::push_stmts(out, Self::stmts_leaves(&main[i..]));
            Self::push_stmts(out, Self::stmts_leaves(&rest));
            return;
        }
        Self::push_stmts(out, Self::stmts_leaves(main));
        Self::push_stmts(out, Self::stmts_leaves(phi));
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
    /// and never across a try-plan boundary (duplicating protected code
    /// into an unprotected context would change throw behavior).
    /// Conditional mid-tail blocks hand off to the tree form
    /// ([`Ctx::dup_tree`], N76). Returns `None` — the caller keeps the
    /// honest drop — when any bound trips. On success returns the
    /// duplicated nodes, the stop mode, and the block count.
    fn cross_arm_dup(
        &mut self,
        site: BlockId,
        target: BlockId,
    ) -> Option<(Vec<SNode>, DupStop, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 128;
        let xdebug = std::env::var_os("ABCD_XARM_DEBUG").is_some();
        let site_plan = self.f_mut().plan_of(site);
        // The walk's universe: when the target enters a sibling ARM
        // region, the whole arm region is the tail (its blocks run
        // exactly on the path being repaired) — the walk follows any
        // in-region edge and stops at the region's exit (N76: the
        // cross-edge-only chain stopped mid-arm at try/S12.14_A15's
        // nested dispatch, whose continuation sat in a sibling arm and
        // was NOT fall-through-reachable). A recorded cross-arm edge
        // OUT of the current region chains into the NEXT arm, whose
        // blocks join the boundary (N76 follow-up: the corpus's
        // unused-ldhole IteratorClose dispatch chains two arms —
        // stopping at the first arm's exit trusted a fall-through that
        // does not exist there). Without an arm region (the
        // short-circuit chains of the d-P4 corpus), the legacy
        // discipline holds: recorded cross-arm edges only.
        let mut boundary = self.arm_region_blocks(target);
        let mut segs: Vec<(Option<usize>, Vec<SNode>)> = Vec::new();
        let mut cur = target;
        let mut visited = BTreeSet::new();
        let mut stmts = 0usize;
        let mut stop = None;
        loop {
            if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                return None;
            }
            if boundary.as_ref().is_some_and(|b| !b.contains(&cur)) {
                return None; // defensive: the walk stays in the arm
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
                    Self::push_main_phi(&mut blk, &parts.main, &parts.phi);
                    stop = Some(DupStop::Terminal);
                    None
                }
                Term::Branch(dest) => {
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.main));
                    Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.phi));
                    let in_boundary = boundary.as_ref().is_some_and(|b| b.contains(&dest));
                    let is_cross = self.f().cross_arm.contains(&(cur, dest));
                    if in_boundary || is_cross {
                        if !in_boundary {
                            // Chaining into the NEXT arm through a
                            // recorded cross edge: its region joins the
                            // boundary (a bare target at least).
                            let extra = self
                                .arm_region_blocks(dest)
                                .unwrap_or_else(|| BTreeSet::from([dest]));
                            boundary = match boundary {
                                Some(mut b) => {
                                    b.extend(extra);
                                    Some(b)
                                }
                                None => Some(extra),
                            };
                        }
                        // The arm region's content continues — keep
                        // walking (its blocks run on this path).
                        Some(Some(dest))
                    } else {
                        // The tail rejoins the structural flow at
                        // `dest`; the caller checks its context falls
                        // through there.
                        stop = Some(DupStop::Rejoin(dest));
                        None
                    }
                }
                // A conditional mid-tail: switch to the tree form —
                // the nested dispatch duplicates as a nested `if/else`
                // (N76, try/S12.14_A15's finally-dispatch epilogue).
                // Only with a trivial plan prefix: the tree form keeps
                // the site's plan uniform (no segment wrapping).
                Term::Cond(cond, t, f) => {
                    if segs.len() > 1 || cur_plan != site_plan {
                        return None;
                    }
                    let Some(boundary) = boundary.clone() else {
                        // No arm region: the legacy walk never enters a
                        // conditional (it stops at the first ordinary
                        // edge), so this is unreachable — bail anyway.
                        return None;
                    };
                    // `cur`'s prologue was already accounted by the
                    // linear walk above; the tree walk owns the rest.
                    let (cond, t, f) = (cond.clone(), t, f);
                    let mut tree_nodes: Vec<SNode> = Vec::new();
                    Self::push_stmts(&mut tree_nodes, Self::stmts_leaves(&parts.main));
                    let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                    Self::push_stmts(&mut tree_nodes, Self::stmts_leaves(&rest));
                    let local_stop = self.tail_merge(t, f, &boundary, None);
                    let mut walk_arm = |entry: BlockId,
                                        phi: Vec<Stmt>,
                                        visited: &mut BTreeSet<BlockId>,
                                        stmts: &mut usize|
                     -> Option<(Vec<SNode>, DupStop)> {
                        let mut head: Vec<SNode> = Vec::new();
                        Self::push_stmts(&mut head, Self::stmts_leaves(&phi));
                        if Some(entry) == local_stop {
                            return Some((head, DupStop::Rejoin(entry)));
                        }
                        let (mut nodes, stop) =
                            self.dup_tree(entry, &boundary, local_stop, visited, stmts, 1)?;
                        head.append(&mut nodes);
                        Some((head, stop))
                    };
                    let (then, then_stop) = walk_arm(t, phi_t, &mut visited, &mut stmts)?;
                    let (otherwise, else_stop) = walk_arm(f, phi_f, &mut visited, &mut stmts)?;
                    let cont = match (then_stop, else_stop) {
                        (DupStop::Terminal, DupStop::Terminal) => None,
                        (DupStop::Rejoin(a), DupStop::Rejoin(b)) if a == b => Some(a),
                        (DupStop::Terminal, DupStop::Rejoin(b)) => Some(b),
                        (DupStop::Rejoin(a), DupStop::Terminal) => Some(a),
                        _ => return None,
                    };
                    tree_nodes.push(SNode::If {
                        cond: cond.clone(),
                        then,
                        otherwise,
                    });
                    let tree_stop = match cont {
                        None => DupStop::Terminal,
                        Some(m) => {
                            let (mut tail, stop) =
                                self.dup_tree(m, &boundary, None, &mut visited, &mut stmts, 0)?;
                            tree_nodes.append(&mut tail);
                            stop
                        }
                    };
                    match segs.last_mut() {
                        Some((_, nodes)) => nodes.append(&mut tree_nodes),
                        _ => segs.push((site_plan, tree_nodes)),
                    }
                    stop = Some(tree_stop);
                    break;
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
        if xdebug {
            eprintln!(
                "XARM-DUP site=B{} target=B{} stop={:?} blocks={}",
                site.index(),
                target.index(),
                stop,
                visited.len()
            );
        }
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
                    finally: None,
                });
            } else {
                out.extend(nodes);
            }
        }
        Some((out, stop, visited.len()))
    }

    /// The block set of the tightest conditional ARM whose
    /// first-executed block is `entry` — the sibling-arm content a
    /// cross-arm edge jumps into. The tree-form tail duplication stays
    /// inside this boundary: it is exactly the content the sibling arm
    /// would have run. (Leaf `Block` nodes with the same entry are NOT
    /// arms; without one the edge's tail is not region-bounded and the
    /// caller keeps the legacy cross-edge-chain walk.)
    fn arm_region_blocks(&mut self, entry: BlockId) -> Option<BTreeSet<BlockId>> {
        let mut best: Option<BTreeSet<BlockId>> = None;
        for id in 0..self.f().tree.nodes().len() {
            let id = RegionId(id as u32);
            let children: [Option<RegionId>; 2] = match self.f().node(id) {
                RegionNode::If {
                    then, otherwise, ..
                } => [*then, *otherwise],
                _ => [None, None],
            };
            for child in children.into_iter().flatten() {
                if self.entry_of(child) != Follow::Entry(entry) {
                    continue;
                }
                let blocks = self.f_mut().node_blocks(child);
                if best.as_ref().is_none_or(|b| blocks.len() < b.len()) {
                    best = Some(blocks);
                }
            }
        }
        best
    }

    /// The merge of a conditional tail's arms within `boundary`: the
    /// earliest block reachable from both — an intersection member not
    /// reachable from any OTHER intersection member. `None` when the
    /// arms never reconverge inside the boundary (both must then be
    /// terminal). `stop_at` (an enclosing merge) is excluded: arms stop
    /// there, they do not merge there.
    fn tail_merge(
        &self,
        t: BlockId,
        f: BlockId,
        boundary: &BTreeSet<BlockId>,
        stop_at: Option<BlockId>,
    ) -> Option<BlockId> {
        let reach = |from: BlockId| {
            let mut seen = BTreeSet::from([from]);
            let mut queue = std::collections::VecDeque::from([from]);
            while let Some(b) = queue.pop_front() {
                if Some(b) == stop_at {
                    continue; // do not expand past the enclosing merge
                }
                for s in block_succs(self.module, b) {
                    if boundary.contains(&s) && Some(s) != stop_at && seen.insert(s) {
                        queue.push_back(s);
                    }
                }
                if seen.len() > 32 {
                    break; // bounded: the tree dup's own budget guards
                }
            }
            seen
        };
        let rt = reach(t);
        let rf = reach(f);
        let inter: Vec<BlockId> = rt.intersection(&rf).copied().collect();
        inter
            .iter()
            .copied()
            .find(|&m| inter.iter().all(|&x| x == m || !reach(x).contains(&m)))
    }

    /// The tree form of the tail duplication (N76): a shared tail whose
    /// head is CONDITIONAL (the es2abc nested dispatch — test262
    /// try/S12.14_A15's finally-dispatch epilogue) duplicates as a
    /// nested `if/else`. Each arm is walked until it terminates
    /// (throw/return — no fall-through) or reaches its merge block (the
    /// walk then continues once after the `if`); `stop_at` is an
    /// ENCLOSING merge whose content belongs to the caller — reaching
    /// it stops the walk with [`DupStop::Rejoin`] without emitting it.
    /// Every block must stay inside the sibling arm's region
    /// (`boundary`) and share the site's plan; budgets are shared
    /// across the whole tree via `visited`/`stmts`.
    fn dup_tree(
        &mut self,
        cur: BlockId,
        boundary: &BTreeSet<BlockId>,
        stop_at: Option<BlockId>,
        visited: &mut BTreeSet<BlockId>,
        stmts: &mut usize,
        depth: usize,
    ) -> Option<(Vec<SNode>, DupStop)> {
        const MAX_BLOCKS: usize = 12;
        const MAX_STMTS: usize = 128;
        const MAX_DEPTH: usize = 3;
        if depth > MAX_DEPTH {
            return None;
        }
        if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
            return None;
        }
        if self.f().loop_headers.contains(&cur) {
            return None;
        }
        if !boundary.contains(&cur) {
            return None;
        }
        let parts = self.block_parts(cur);
        *stmts += parts.main.len() + parts.phi.len();
        if *stmts > MAX_STMTS {
            return None;
        }
        match &parts.term {
            Term::None => {
                // Terminal only on a real return/throw (a plain
                // fall-off end would silently truncate the path).
                let last = parts
                    .main
                    .iter()
                    .rposition(|s| !matches!(s, Stmt::Unreachable));
                match last {
                    Some(i) if matches!(parts.main[i], Stmt::Return(_) | Stmt::Throw(_)) => {}
                    _ => return None,
                }
                let mut blk = Vec::new();
                Self::push_main_phi(&mut blk, &parts.main, &parts.phi);
                Some((blk, DupStop::Terminal))
            }
            Term::Branch(d) => {
                let mut blk: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.main));
                Self::push_stmts(&mut blk, Self::stmts_leaves(&parts.phi));
                if Some(*d) == stop_at {
                    // The enclosing merge: the caller's walk resumes it.
                    return Some((blk, DupStop::Rejoin(*d)));
                }
                if !boundary.contains(d) {
                    // The arm region's own exit edge: the tail rejoins
                    // the structural flow here; the caller checks its
                    // context falls through.
                    return Some((blk, DupStop::Rejoin(*d)));
                }
                let (mut tail, stop) =
                    self.dup_tree(*d, boundary, stop_at, visited, stmts, depth)?;
                blk.append(&mut tail);
                Some((blk, stop))
            }
            Term::Cond(cond, t, f) => {
                let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, *t, *f);
                let merge = self.tail_merge(*t, *f, boundary, stop_at);
                let local_stop = merge.or(stop_at);
                let mut walk_arm = |entry: BlockId,
                                    phi: Vec<Stmt>,
                                    visited: &mut BTreeSet<BlockId>,
                                    stmts: &mut usize|
                 -> Option<(Vec<SNode>, DupStop)> {
                    let mut head: Vec<SNode> = Vec::new();
                    Self::push_stmts(&mut head, Self::stmts_leaves(&phi));
                    if Some(entry) == local_stop {
                        return Some((head, DupStop::Rejoin(entry)));
                    }
                    let (mut nodes, stop) =
                        self.dup_tree(entry, boundary, local_stop, visited, stmts, depth + 1)?;
                    head.append(&mut nodes);
                    Some((head, stop))
                };
                let (then, then_stop) = walk_arm(*t, phi_t, visited, stmts)?;
                let (otherwise, else_stop) = walk_arm(*f, phi_f, visited, stmts)?;
                // Combine: a terminal arm does not fall through; a
                // rejoining arm routes the continuation after the `if`.
                // Both arms rejoining must agree on the merge.
                let cont = match (then_stop, else_stop) {
                    (DupStop::Terminal, DupStop::Terminal) => None,
                    (DupStop::Rejoin(a), DupStop::Rejoin(b)) if a == b => Some(a),
                    (DupStop::Terminal, DupStop::Rejoin(b)) => Some(b),
                    (DupStop::Rejoin(a), DupStop::Terminal) => Some(a),
                    _ => return None,
                };
                let mut nodes: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut nodes, Self::stmts_leaves(&parts.main));
                Self::push_stmts(&mut nodes, Self::stmts_leaves(&rest));
                nodes.push(SNode::If {
                    cond: cond.clone(),
                    then,
                    otherwise,
                });
                match cont {
                    None => Some((nodes, DupStop::Terminal)),
                    // The enclosing merge: hand back to the caller.
                    Some(r) if Some(r) == stop_at => Some((nodes, DupStop::Rejoin(r))),
                    // The local merge: continue the walk past the `if`.
                    Some(m) => {
                        let (mut tail, stop) =
                            self.dup_tree(m, boundary, stop_at, visited, stmts, depth)?;
                        nodes.append(&mut tail);
                        Some((nodes, stop))
                    }
                }
            }
        }
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

    /// Handler-shim cut-edge tail duplication (N76). A handler
    /// sub-CFG's Normal edge leaving the shim's block set targets the
    /// try's continuation in the MAIN universe. Falling out of the
    /// catch clause reaches it only when the enclosing emission placed
    /// the continuation right after the try/catch (the d-P5 join
    /// hoist); when the region tree buried the continuation in a
    /// sibling conditional arm (a terminal sibling poisons the
    /// post-dominator merge), the fall-out lands at the end of the
    /// enclosing construct instead and the path silently returns
    /// `undefined` (test262 try/S12.14_A15's `SwitchTest3` — the
    /// finally's `break` path must still reach `return result`).
    ///
    /// Duplicate the target's tail inline when it is small, acyclic,
    /// try-plan-clean in the main frame, and ends in a terminal
    /// (return/throw) — the same finally-style duplication es2abc
    /// itself uses. Returns `None` (keep the structural fall-out) when
    /// any bound trips or the tail rejoins live control flow (then the
    /// enclosing emission may still route to it).
    fn shim_tail_dup(&mut self, target: BlockId) -> Option<(Vec<SNode>, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 64;
        let debug = std::env::var_os("ABCD_TAIL_DEBUG").is_some();
        macro_rules! bail {
            ($why:expr) => {{
                if debug {
                    eprintln!("TAIL-BAIL target=B{}: {}", target.index(), $why);
                }
                return None;
            }};
        }
        let h = self.f().shim_of?;
        let shim_uniq = self.f().shim_uniq;
        let set = if shim_uniq {
            self.uniq_sets.get(&h).cloned()
        } else {
            self.shim_sets.get(&h).cloned()
        }?;
        if debug {
            eprintln!("TAIL-TRY handler=B{} target=B{}", h.index(), target.index());
        }
        if set.contains(&target) {
            bail!("target in set");
        }
        // A cut edge to an in-flight join hoist's rejoin entry is a
        // SAFE fall-out (the hoisted tail is emitted right after the
        // try/catch being built) — duplicating it would emit the tail
        // twice. The same holds when the enclosing try/catch's physical
        // continuation is verified to be the target.
        if self.hoist_rejoins.contains(&target) || self.verified_fallout.contains(&target) {
            return None;
        }
        let mut out: Vec<SNode> = Vec::new();
        let mut cur = target;
        let mut visited = BTreeSet::new();
        let mut stmts = 0usize;
        loop {
            if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                bail!("cycle/budget");
            }
            // Never duplicate into a loop (either frame's view)…
            if self.f().loop_headers.contains(&cur) || self.frames[0].loop_headers.contains(&cur) {
                bail!("loop header");
            }
            // …and never duplicate a block protected by a main-frame
            // try plan: its throw routing is a PC-range property the
            // duplication cannot reproduce.
            if self
                .frames
                .first_mut()
                .expect("root frame")
                .plan_of(cur)
                .is_some()
            {
                bail!("protected in main frame");
            }
            let parts = self.block_parts(cur);
            stmts += parts.main.len() + parts.phi.len();
            if stmts > MAX_STMTS {
                bail!("stmt budget");
            }
            match &parts.term {
                Term::None => {
                    // Terminal only when the block really returns or
                    // throws (a plain fall-off end would silently
                    // truncate the path).
                    let last = parts
                        .main
                        .iter()
                        .rposition(|s| !matches!(s, Stmt::Unreachable));
                    match last {
                        Some(i) if matches!(parts.main[i], Stmt::Return(_) | Stmt::Throw(_)) => {}
                        _ => bail!("not terminal"),
                    }
                    Self::push_main_phi(&mut out, &parts.main, &parts.phi);
                    self.stats.handler_tail_dups += 1;
                    self.stats.handler_tail_dup_blocks += visited.len();
                    return Some((out, visited.len()));
                }
                Term::Branch(d) => {
                    if set.contains(d) {
                        bail!("re-enters handler set");
                    }
                    Self::push_main_phi(&mut out, &parts.main, &parts.phi);
                    cur = *d;
                }
                // A conditional mid-tail is beyond this fold (the same
                // bound as the cross-arm fold).
                Term::Cond(..) => bail!("conditional mid-tail"),
            }
        }
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
        // The d-P5 join hoist: this node is part of the deferred tail
        // of a cut region — suppressed here; the driver emits it after
        // the try/catch (the handlers' rejoin point). The interception
        // is coverage-agnostic (the N78 loop-cut driver defers MIXED
        // tails — e.g. the unprotected continuation below a cut
        // do-while body may contain chain-plan blocks).
        if let Some(cd) = self.f_mut().cut_defer.as_mut()
            && cd.ids.remove(&id)
        {
            return;
        }
        let cov = self.f_mut().cov(id);
        match cov {
            Cov::Uniform(p) if p == active => self.emit_content(id, active, follow, out),
            Cov::Uniform(Some(p)) if self.is_suppressed(p) => {
                // N77: p's try wrapper physically encloses this
                // emission point (a de-absorbed tower's clause/join
                // context) with no intervening catch — emit plain.
                self.emit_content(id, Some(p), follow, out)
            }
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
        // N77: the de-absorbed tower path (handler unique prefixes +
        // joins emitted once per level). Falls through to the legacy
        // absorbed emission whenever a guard fails.
        if self.emit_deabsorb_tower(ids, p, follow, out) {
            return;
        }
        let (region, cuts, handlers) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts, plan.handlers.clone())
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
        //
        // Two phases: SELECT the whole outward chain first (pure
        // analysis — the pending state is unchanged by the body
        // emission), then EMIT the handler bodies with the entire chain
        // on `self.pending_wraps`/`self.suppress_wraps`. Every
        // construct emitted while the chain is pending lands
        // physically inside these wrappers, so nested emissions must
        // NOT re-wrap the same plans — otherwise each handler body
        // re-wraps the chain around its own inner trys and the output
        // grows exponentially (N76 try/S12.14_A7_T2). N77 extends the
        // coverage to `p`'s OWN handlers (their clauses sit inside
        // every chain try body — without it, an absorbed handler body
        // re-wraps a chain plan around its chain-protected blocks and
        // re-emits the chain's handlers, the second-cascade wart).
        let chain = self.select_wrap_chain(p, &handlers);
        let chain_prots: Vec<BTreeSet<BlockId>> = chain
            .iter()
            .map(|&(fq, q)| self.frames[fq].plans[q].protected.clone())
            .collect();
        // When the physical continuation after this try/catch is a
        // known block, handler cut edges to it are sound plain
        // fall-outs (the catch clause ends exactly where the
        // continuation begins) — record it for the run-fold /
        // shim-tail-duplication decisions inside the handler bodies.
        // Pure trampolines are transparent to a fall-out: an empty
        // block that only branches runs nothing, so the whole chain is
        // the continuation (test262 if/S12.5_A3: the handler's cut edge
        // targets B75 past the empty B72 jump block).
        let mut verified_chain: Vec<BlockId> = Vec::new();
        if let Follow::Entry(fb) = follow {
            let mut cur = fb;
            loop {
                if !verified_chain.contains(&cur) {
                    verified_chain.push(cur);
                }
                let parts = self.block_parts(cur);
                if !parts.main.is_empty() || !parts.phi.is_empty() {
                    break;
                }
                match parts.term {
                    Term::Branch(d) if !verified_chain.contains(&d) => cur = d,
                    _ => break,
                }
                if verified_chain.len() > 16 {
                    break; // defensive bound
                }
            }
            for &b in &verified_chain {
                self.verified_fallout.push(b);
            }
        }
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
        // `p`'s handlers: emitted with the whole chain pending (their
        // clauses land inside every chain try body — chain-protected
        // blocks in the handler body need no re-wrap; N77).
        let pending_mark = self.pending_wraps.len();
        let suppress_mark = self.suppress_wraps.len();
        for cp in &chain_prots {
            self.pending_wraps.push(cp.clone());
            self.suppress_wraps.push(cp.clone());
        }
        let mut catches = Vec::new();
        let mut seen = HashSet::new();
        for h in &handlers {
            if seen.insert(*h) {
                catches.push(self.emit_handler(*h));
            }
        }
        self.suppress_wraps.truncate(suppress_mark);
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
            finally: None,
        };
        for (k, (fq, q)) in chain.iter().enumerate() {
            let (fq, q) = (*fq, *q);
            let (qregion, qhandlers) = {
                let plan = &self.frames[fq].plans[q];
                (plan.region, plan.handlers.clone())
            };
            let wraps = {
                let f = &mut self.frames[fq];
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
            // Chain step k's handlers: their clauses land inside the
            // try bodies of the steps ABOVE k only — suppress those
            // (and only those) primary re-wraps (N77).
            let qsuppress_mark = self.suppress_wraps.len();
            for cp in &chain_prots[k + 1..] {
                self.suppress_wraps.push(cp.clone());
            }
            for h in &qhandlers {
                if seen.insert(*h) {
                    qcatches.push(self.emit_handler(*h));
                }
            }
            self.suppress_wraps.truncate(qsuppress_mark);
            node = SNode::Try {
                body: vec![node],
                catches: qcatches,
                note: Some(format!(
                    "try region {qregion}: handler-protecting outer try (finally idiom) — wrapped around region {region}'s try/catch (wrapper #{wraps})"
                )),
                finally: None,
            };
        }
        self.pending_wraps.truncate(pending_mark);
        for _ in &verified_chain {
            self.verified_fallout.pop();
        }
        out.push(node);
    }

    /// The next outer plan whose try must wrap a construct whose
    /// handlers are `protected_handlers` (the es2abc finally idiom):
    /// the smallest plan — not already wrapped in this chain
    /// (`visited`, by protected-set identity) and not already emitted
    /// inside the handler's own shim — whose protected set contains a
    /// handler. This deliberately keeps scanning PAST shim-handled
    /// plans: the innermost plan containing a handler is often that
    /// handler's own nested try (already emitted by the shim), while a
    /// LARGER plan (the outer finally) still protects the handler and
    /// must wrap here, or its handler body is silently dropped (dream
    /// gate: opt-try-catch-func/test-nested-try-catch, d-P5).
    ///
    /// Frames searched: the current (innermost) frame first, then the
    /// ROOT frame (the function's full plan list). The shim ride-along
    /// list (`build_shims`) only admits a region when every protected
    /// block is in the shim's own set or is a chosen handler HEAD, so
    /// an outer finally region whose range also covers inner-handler
    /// BODY blocks is absent from the shim's plan list — but the shim
    /// still emits the inner try/catch the region must wrap
    /// (test262 try/S12.14_A7_T1's `ReferenceError: v384 is not
    /// defined` and A7_T2's escaping `ex3`, N76). Physical soundness
    /// is preserved: the wrapper encloses exactly the inner try body
    /// (laminar-nested in the outer range) plus the catch clause whose
    /// blocks the outer range covers.
    ///
    /// Returns `(frame index, plan index)`.
    fn outer_wrap_plan(
        &self,
        visited: &HashSet<BTreeSet<BlockId>>,
        protected_handlers: &[BlockId],
    ) -> Option<(usize, usize)> {
        let debug = std::env::var_os("ABCD_WRAP_DEBUG").is_some();
        let cur = self.frames.len() - 1;
        // Current frame first, then the root frame (skip when equal).
        let frame_ids = if cur == 0 { &[0][..] } else { &[cur, 0][..] };
        let mut outer: Option<(usize, usize)> = None;
        for h in protected_handlers {
            // plan_order is ascending by protected-set size: the first
            // eligible hit for this handler is its smallest outer plan.
            let mut cand: Option<(usize, usize)> = None;
            'frames: for &fi in frame_ids {
                let f = &self.frames[fi];
                for &q in &f.plan_order {
                    let plan = &f.plans[q];
                    if visited.contains(&plan.protected) || !plan.protected.contains(h) {
                        continue;
                    }
                    // A plan whose wrapper is already being assembled
                    // above this emission point (the outer-finally
                    // chain of an enclosing wrap_try_run) physically
                    // encloses this construct — re-wrapping it here
                    // duplicates its handler body at every nested site
                    // (exponential blowup, N76).
                    if self.pending_wraps.contains(&plan.protected) {
                        continue;
                    }
                    // A plan whose protected set lies INSIDE the
                    // handler's own sub-CFG is already wrapped by the
                    // handler shim (nested try in the catch body) —
                    // wrapping it again outside would duplicate the
                    // catch (correct but redundant); skip those, but
                    // keep scanning outward.
                    let handled_inside = self
                        .shim_plans
                        .get(h)
                        .is_some_and(|plans| plans.iter().any(|pl| pl.protected == plan.protected));
                    if handled_inside {
                        continue;
                    }
                    cand = Some((fi, q));
                    break 'frames;
                }
            }
            if let Some((fi, q)) = cand
                && outer.is_none_or(|(fo, o)| {
                    self.frames[fi].plans[q].protected.len()
                        < self.frames[fo].plans[o].protected.len()
                })
            {
                outer = Some((fi, q));
            }
            if debug {
                eprintln!(
                    "WRAP fn={} handler=B{} cand={:?}",
                    self.frames[cur].tree.func.index(),
                    h.index(),
                    cand.map(|(fi, q)| (fi, self.frames[fi].plans[q].region)),
                );
            }
        }
        outer
    }

    /// The outward handler-protecting chain for plan `p` (the es2abc
    /// finally idiom — see `wrap_try_run`). Extracted so the N77
    /// de-absorbed tower path shares the selection. Pure analysis: no
    /// emission, no mutation.
    fn select_wrap_chain(&mut self, p: usize, handlers: &[BlockId]) -> Vec<(usize, usize)> {
        let mut protected_handlers = handlers.to_vec();
        // `visited` tracks protected-SET identity: the laminar chain may
        // step from a shim frame's plans to the root frame's (the shim
        // ride-along list is only an approximation — see
        // `outer_wrap_plan`), so plan indices are not comparable across
        // frames.
        let mut visited: HashSet<BTreeSet<BlockId>> =
            [self.f().plans[p].protected.clone()].into_iter().collect();
        let mut chain: Vec<(usize, usize)> = Vec::new(); // (frame, plan)
        let mut depth = 0usize;
        loop {
            depth += 1;
            if depth > self.frames[0].plans.len() + self.f().plans.len() + 1 {
                break; // defensive: the laminar chain is finite
            }
            let Some((fq, q)) = self.outer_wrap_plan(&visited, &protected_handlers) else {
                break;
            };
            let plan = &self.frames[fq].plans[q];
            visited.insert(plan.protected.clone());
            protected_handlers = plan.handlers.clone();
            chain.push((fq, q));
        }
        chain
    }

    // ── The d-P5 join hoist (RC1) ──────────────────────────────────

    /// Root-frame innermost plan of `b` (None = unprotected).
    fn root_plan_of(&mut self, b: BlockId) -> Option<usize> {
        self.frames.first_mut().expect("root frame").plan_of(b)
    }

    /// Pure trampoline: no statements, one unconditional branch.
    fn is_trampoline(&self, b: BlockId) -> bool {
        let parts = self.block_parts(b);
        parts.main.is_empty() && parts.phi.is_empty() && matches!(parts.term, Term::Branch(_))
    }

    /// `t` is reachable from `head` within the shared join, and every
    /// block on every such path (endpoints excluded) is a pure
    /// trampoline — falling out at `head` is then equivalent to falling
    /// out at `t`.
    fn trampoline_only_path(&self, head: BlockId, t: BlockId) -> bool {
        let mut seen = BTreeSet::from([head]);
        let mut queue = std::collections::VecDeque::from([head]);
        let mut reaches = false;
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if s == t {
                    reaches = true;
                    continue;
                }
                if self.shared_join.contains(&s) && seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        reaches && seen.iter().all(|&x| x == head || self.is_trampoline(x))
    }

    /// Whether a foreign (nested-tower) handler `hp`'s cut to join
    /// block `j` routes soundly through this tower's emission: `hp`'s
    /// plan's protected set has a wrap site inside a tower handler's
    /// unique body or a join set, and only trampolines lie between the
    /// site and the fall-out target. For a unique-body site, `j` must
    /// be the body's fall-out head; for a join-set site, `j` must sit
    /// at that join tree's top level (the caller checks the latter).
    fn foreign_cut_ok(
        &mut self,
        hp: BlockId,
        j: BlockId,
        tower: &[BlockId],
        clause: &[usize],
        joins: &[Option<(BlockId, BTreeSet<BlockId>)>],
        m: usize,
    ) -> bool {
        let Some(qs) = self.handler_root_plans.get(&hp).cloned() else {
            return false;
        };
        qs.iter().any(|&q| {
            let prot = self.frames[0].plans[q].protected.clone();
            // Site inside a tower handler's unique body: the fall-out
            // unwinds to the body end — the body's own fall-out head.
            for (hi, &h) in tower.iter().enumerate() {
                let Some(uset) = self.uniq_sets.get(&h) else {
                    continue;
                };
                let site: BTreeSet<BlockId> = prot.intersection(uset).copied().collect();
                if site.is_empty() || !self.trampoline_tail(&site, j, uset, &prot) {
                    continue;
                }
                let c = clause[hi];
                let Some(first) = (c..=m).find(|&lvl_x| joins[lvl_x].is_some()) else {
                    return false;
                };
                let Some((head, set)) = &joins[first] else {
                    return false;
                };
                if set.contains(&j) && (*head == j || self.trampoline_only_path(*head, j)) {
                    return true;
                }
            }
            // Site inside a join set: the fall-out lands mid-tree; the
            // top-level check (the caller's tree walk) owns the rest.
            for jl in joins.iter().flatten() {
                let site: BTreeSet<BlockId> = prot.intersection(&jl.1).copied().collect();
                if !site.is_empty()
                    && jl.1.contains(&j)
                    && self.trampoline_tail(&site, j, &jl.1, &prot)
                {
                    return true;
                }
            }
            false
        })
    }

    /// Every block reachable from `site` within `within` without
    /// passing `j` is a pure trampoline or part of the nested tower's
    /// own protected set — the fall-out from the nested tower runs
    /// nothing the bytecode path wouldn't.
    fn trampoline_tail(
        &self,
        site: &BTreeSet<BlockId>,
        j: BlockId,
        within: &BTreeSet<BlockId>,
        prot: &BTreeSet<BlockId>,
    ) -> bool {
        let mut seen: BTreeSet<BlockId> = site.iter().copied().collect();
        let mut queue: std::collections::VecDeque<BlockId> = site.iter().copied().collect();
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if s == j || !within.contains(&s) {
                    continue;
                }
                if seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        seen.iter()
            .all(|&x| prot.contains(&x) || self.is_trampoline(x))
    }

    /// Structure a tower-join block set: a shim function over the set
    /// in the de-absorption module (out-of-set edges cut), with the
    /// usual ride-along plans. The set must be exactly the tree's
    /// universe and `head` its entry. Memoized per set (None = failed).
    fn join_tree(
        &mut self,
        head: BlockId,
        set: &BTreeSet<BlockId>,
    ) -> Option<(RegionTree, Vec<Plan>)> {
        if let Some(r) = self.join_memo.get(set) {
            return r.clone();
        }
        let r = self.build_join_tree(head, set);
        self.join_memo.insert(set.clone(), r.clone());
        r
    }

    fn build_join_tree(
        &mut self,
        head: BlockId,
        set: &BTreeSet<BlockId>,
    ) -> Option<(RegionTree, Vec<Plan>)> {
        // A FRESH clone per join set (only the set's own boundary is
        // cut — join blocks never branch into unique handler prefixes,
        // so the uniq patching is irrelevant here). A tower that bails
        // after its sets were patched therefore cannot poison a later
        // tower's join trees.
        let mut dmod = self.module.clone();
        for &b in set {
            let Some(block) = dmod.block(b).cloned() else {
                continue;
            };
            let Some(&last) = block.insts.last() else {
                continue;
            };
            let new_op = match &dmod.inst(last).expect("inst").op {
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
                dmod.inst_mut(last).expect("inst").op = op;
            }
        }
        let f = self.module.func(self.rf.func)?;
        let mut blocks: Vec<BlockId> = vec![head];
        blocks.extend(set.iter().copied().filter(|b| *b != head));
        let name: Sym = dmod.sym.intern(&format!("$join${}", head.index()));
        let fid = FuncId::new(dmod.functions.len() as u32);
        let mut fd = FunctionData::new(ClassId::new(0), name, self.rf.kind);
        fd.blocks = blocks;
        let block_set = set.clone();
        let mut chosen: Vec<usize> = Vec::new();
        loop {
            let mut changed = false;
            for (i, tr) in f.try_regions.iter().enumerate() {
                if chosen.contains(&i) {
                    continue;
                }
                let ok = tr.protected.iter().all(|b| {
                    block_set.contains(b)
                        || chosen
                            .iter()
                            .any(|&j| f.try_regions[j].catches.iter().any(|cc| cc.handler == *b))
                });
                if ok {
                    chosen.push(i);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        chosen.sort_unstable();
        fd.try_regions = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
        dmod.functions.push(fd);
        let tree = structure_regions(&dmod, fid);
        // The set must be exactly the tree's universe (no strays).
        if tree_blocks(&tree) != *set {
            return None;
        }
        // The head must be the tree's entry.
        let root = tree.root?;
        if tree_entry(&tree, root) != Some(head) {
            return None;
        }
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
        Some((tree, plans))
    }

    /// Emit one verified tower-join level through its join shim tree.
    fn emit_join_level(&mut self, head: BlockId, set: &BTreeSet<BlockId>, out: &mut Vec<SNode>) {
        if std::env::var_os("ABCD_DEAB_DEBUG").is_some() {
            eprintln!(
                "DEAB-JOIN fn={} head=B{} set={:?}",
                self.rf.func.index(),
                head.index(),
                set.iter().map(|b| b.index()).collect::<Vec<_>>()
            );
        }
        let Some((tree, plans)) = self.join_tree(head, set) else {
            out.push(SNode::Honest(
                "N77: tower-join tree vanished between analysis and emission (defensive)".into(),
            ));
            return;
        };
        let mut frame = Frame::new(tree, plans);
        frame.join_shim = true;
        self.frames.push(frame);
        if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, out);
        }
        self.frames.pop();
    }

    /// The de-absorbed tower fast path. Returns false (the caller takes
    /// the legacy absorbed path) unless every guard holds.
    fn emit_deabsorb_tower(
        &mut self,
        ids: &[RegionId],
        p: usize,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_DEAB_DEBUG").is_some();
        macro_rules! bail {
            ($($arg:tt)*) => {{
                if debug {
                    eprintln!(
                        "DEAB-BAIL fn={} region={}: {}",
                        self.rf.func.index(),
                        self.f().plans[p].region,
                        format!($($arg)*)
                    );
                }
                self.stats.deabsorb_bails += 1;
                return false;
            }};
        }
        if self.deabsorb_module.is_none() {
            return false;
        }
        let handlers = self.f().plans[p].handlers.clone();
        let chain = self.select_wrap_chain(p, &handlers);
        if chain.is_empty() {
            return false; // v1: towers (handler-protecting chains) only
        }
        if debug {
            eprintln!(
                "DEAB-TRY fn={} region={} chain={} shim={:?} join={}",
                self.rf.func.index(),
                self.f().plans[p].region,
                chain.len(),
                self.f().shim_of.map(|h| h.index()),
                self.f().join_shim
            );
        }
        let m = chain.len();
        let chain_prots: Vec<BTreeSet<BlockId>> = chain
            .iter()
            .map(|&(fq, q)| self.frames[fq].plans[q].protected.clone())
            .collect();
        // Tower handlers in clause order with their clause levels:
        // p's handlers sit in chain[0]'s try body (level 0); chain[k]'s
        // handlers sit in chain[k+1]'s try body (level k+1; the last
        // step's handlers sit at the AFTER level m).
        let mut tower: Vec<BlockId> = Vec::new();
        let mut clause: Vec<usize> = Vec::new();
        for h in &handlers {
            if !tower.contains(h) {
                tower.push(*h);
                clause.push(0);
            }
        }
        for (k, &(fq, q)) in chain.iter().enumerate() {
            for h in self.frames[fq].plans[q].handlers.clone() {
                if !tower.contains(&h) {
                    tower.push(h);
                    clause.push(if k + 1 < m { k + 1 } else { m });
                }
            }
        }
        // Cut edges from the handlers' unique prefixes into the shared
        // join (block_succs reads the ORIGINAL module — the patched
        // modules only shaped trees).
        let mut cuts: Vec<(BlockId, BlockId)> = Vec::new(); // (handler, target)
        for &h in &tower {
            let Some(set) = self.uniq_sets.get(&h) else {
                return false; // exotic entry shape — legacy
            };
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) && self.shared_join.contains(&s) {
                        cuts.push((h, s));
                    }
                }
            }
        }
        if cuts.is_empty() {
            return false; // no shared continuation — legacy is identical
        }
        if tower.iter().any(|h| !self.uniq_trees.contains_key(h)) {
            return false;
        }
        // The join level of a shared-join block: the smallest chain
        // level whose protected set contains its innermost plan's
        // protected set (the block runs inside that level's try body);
        // `m` (AFTER) when unprotected or outside the outermost plan.
        let level_of = |ctx: &mut Self, j: BlockId| -> usize {
            let Some(pi) = ctx.root_plan_of(j) else {
                return m;
            };
            let prot = ctx.frames[0].plans[pi].protected.clone();
            for (k, cp) in chain_prots.iter().enumerate() {
                if prot.is_subset(cp) {
                    return k;
                }
            }
            m
        };
        // Partition the cuts: targets already covered by an enclosing
        // tower's join emission (`pending_joins`) are verified against
        // that emission instead of producing joins here.
        let mut pools: Vec<BTreeSet<BlockId>> = vec![BTreeSet::new(); m + 1];
        let mut enclosed: Vec<(BlockId, BlockId)> = Vec::new(); // (handler, target)
        let mut local: Vec<(BlockId, BlockId, usize)> = Vec::new(); // (handler, target, level)
        for &(h, s) in &cuts {
            if self.pending_joins.iter().any(|js| js.contains(&s)) {
                enclosed.push((h, s));
                continue;
            }
            if self.emitted_joins.contains(&s) {
                bail!(
                    "cut target B{} already emitted by an earlier tower (plan re-wrap)",
                    s.index()
                );
            }
            let c = clause[tower.iter().position(|&x| x == h).expect("tower handler")];
            let lvl = level_of(self, s);
            if lvl < c {
                bail!("cut flows inward (target level {lvl} < clause level {c})");
            }
            pools[lvl].insert(s);
            local.push((h, s, lvl));
        }
        // A handler mixing local and enclosed cuts has two fall-out
        // positions — beyond v1.
        for &h in &tower {
            let has_local = local.iter().any(|&(x, _, _)| x == h);
            let has_encl = enclosed.iter().any(|&(x, _)| x == h);
            if has_local && has_encl {
                bail!("handler mixes local and enclosed cut targets");
            }
        }
        // Per level (ascending): pick the head (reaches every pool
        // target through trampoline-only paths), close over the level's
        // blocks, and feed boundary targets to outer levels' pools.
        let mut joins: Vec<Option<(BlockId, BTreeSet<BlockId>)>> = (0..=m).map(|_| None).collect();
        for lvl in 0..=m {
            if pools[lvl].is_empty() {
                continue;
            }
            let targets = pools[lvl].clone();
            let mut head: Option<BlockId> = None;
            for &cand in &targets {
                if targets
                    .iter()
                    .all(|&t| t == cand || self.trampoline_only_path(cand, t))
                {
                    head = Some(cand);
                    break;
                }
            }
            let Some(head) = head else {
                bail!("no common join head for level {lvl} targets {targets:?}");
            };
            // The level's block set: everything reachable from the head
            // within the shared join, staying at this level (AFTER takes
            // everything remaining); out-of-level edges are boundary
            // targets for outer pools.
            let mut set = BTreeSet::from([head]);
            let mut queue = std::collections::VecDeque::from([head]);
            let mut boundary: Vec<BlockId> = Vec::new();
            while let Some(b) = queue.pop_front() {
                for s in block_succs(self.module, b) {
                    if !self.shared_join.contains(&s) {
                        continue;
                    }
                    if self.pending_joins.iter().any(|js| js.contains(&s)) {
                        continue; // enclosed — covered by an outer tower
                    }
                    if self.emitted_joins.contains(&s) {
                        bail!("join reaches an already-emitted join block");
                    }
                    let ls = level_of(self, s);
                    if ls == lvl {
                        if set.insert(s) {
                            queue.push_back(s);
                        }
                    } else {
                        if ls < lvl {
                            bail!("join boundary flows inward (level {ls} from {lvl})");
                        }
                        boundary.push(s);
                    }
                }
            }
            // Every pool target must be inside the closure.
            if !targets.iter().all(|t| set.contains(t)) {
                bail!("join closure from B{} missed a pool target", head.index());
            }
            for bt in boundary {
                let ls = level_of(self, bt);
                pools[ls].insert(bt);
            }
            joins[lvl] = Some((head, set));
        }
        let non_empty = |lvl_x: usize| joins[lvl_x].is_some();
        // Every local cut must target the first non-empty level at or
        // above its clause level (its fall-out position).
        for &(h, _s, lvl) in &local {
            let c = clause[tower.iter().position(|&x| x == h).expect("tower handler")];
            let Some(first) = (c..=m).find(|&lvl_x| non_empty(lvl_x)) else {
                bail!("local cut with no local join level");
            };
            if first != lvl {
                bail!("cut target level {lvl} is not the fall-out level {first}");
            }
        }
        let join_union: BTreeSet<BlockId> = joins
            .iter()
            .flatten()
            .flat_map(|(_, s)| s.iter().copied())
            .collect();
        // Foreign cut edges into this tower's joins (a NESTED tower's
        // handler — its plan's protected set sits inside a tower
        // handler's unique body or inside a join set, so its tower is
        // emitted within this one). Sound when (a) the nested wrap's
        // site has only trampolines between it and the cut target (the
        // fall-out runs nothing the bytecode path wouldn't) and (b)
        // the target is at the fall-out position: for a site in a
        // unique body, the head of the body's fall-out level; for a
        // site in a join set, a top-level block of that join's tree
        // (checked below).
        let all_handlers = self.all_handlers.clone();
        let mut foreign: Vec<BlockId> = Vec::new(); // targets needing top-level
        for hp in all_handlers {
            if tower.contains(&hp) {
                continue;
            }
            let Some(uset) = self.uniq_sets.get(&hp).cloned() else {
                if self
                    .handler_approx
                    .get(&hp)
                    .is_some_and(|a| a.iter().any(|b| join_union.contains(b)))
                {
                    bail!("exotic foreign handler reaches a join block");
                }
                continue;
            };
            for &b in &uset {
                for s in block_succs(self.module, b) {
                    if !join_union.contains(&s) {
                        continue;
                    }
                    let nested = self.foreign_cut_ok(hp, s, &tower, &clause, &joins, m);
                    if !nested {
                        bail!(
                            "foreign cut B{}→B{} into the tower's joins",
                            b.index(),
                            s.index()
                        );
                    }
                    foreign.push(s);
                }
            }
        }
        // Tower-handler cuts into non-head join blocks also need the
        // top-level guarantee (their fall-out lands at the level head
        // and must reach the target by fall-through alone).
        for &(h, s, _) in &local {
            let _ = h;
            foreign.push(s);
        }
        // Structure every join level; every member with an external
        // Normal predecessor (a rejoin target) must sit at the tree's
        // top level, and the foreign/enclosed targets must be top-level
        // in their sets.
        let mut join_blocks_total = 0usize;
        for (head, set) in joins.iter().flatten() {
            // Loops inside a join are beyond v1 (the fall-out physics
            // of a join that iterates).
            if set.iter().any(|b| {
                self.frames[0].loop_headers.contains(b) || self.f().loop_headers.contains(b)
            }) {
                bail!("loop header inside a join level");
            }
            let Some((tree, _plans)) = self.join_tree(*head, set) else {
                bail!("join set did not structure");
            };
            let top = tree_top_blocks(&tree);
            for &b in set {
                // The head is the tree's entry (verified by
                // `build_join_tree`): cut edges to it land at the
                // tree's start by construction.
                if b == *head {
                    continue;
                }
                let has_external_pred = self.module.block(b).is_some_and(|bb| {
                    bb.preds
                        .iter()
                        .any(|e| e.kind == abcd_ir::EdgeKind::Normal && !set.contains(&e.from))
                });
                if has_external_pred && !top.contains(&b) {
                    if debug {
                        eprintln!("JOIN-TREE head=B{} set={:?}:", head.index(), set);
                        for (j, node) in tree.nodes().iter().enumerate() {
                            eprintln!("  R{j}: {node:?}");
                        }
                    }
                    bail!(
                        "rejoin target B{} buried below the join tree's top level",
                        b.index()
                    );
                }
            }
            join_blocks_total += set.len();
        }
        // Enclosed targets: top-level in their pending join tree.
        for &(_, s) in &enclosed {
            let Some(js) = self.pending_joins.iter().find(|js| js.contains(&s)) else {
                continue;
            };
            let Some(Some((tree, _))) = self.join_memo.get(js) else {
                bail!("enclosed cut target in an unverified pending join");
            };
            if !tree_top_blocks(tree).contains(&s) {
                bail!("enclosed cut target not at the pending join's top level");
            }
        }
        // The AFTER join's boundary edges into the main universe must
        // land on the caller's verified continuation (the legacy
        // fall-out rule).
        let mut follow_chain: Vec<BlockId> = Vec::new();
        if let Follow::Entry(fb) = follow {
            let mut cur = fb;
            loop {
                if !follow_chain.contains(&cur) {
                    follow_chain.push(cur);
                }
                let parts = self.block_parts(cur);
                if !parts.main.is_empty() || !parts.phi.is_empty() {
                    break;
                }
                match parts.term {
                    Term::Branch(d) if !follow_chain.contains(&d) => cur = d,
                    _ => break,
                }
                if follow_chain.len() > 16 {
                    break;
                }
            }
        }
        if let Some((_, aset)) = &joins[m] {
            for &b in aset {
                for s in block_succs(self.module, b) {
                    if self.shared_join.contains(&s) {
                        continue;
                    }
                    if !follow_chain.contains(&s) {
                        bail!(
                            "after-join boundary to B{} is not the verified continuation",
                            s.index()
                        );
                    }
                }
            }
        }

        // ── Emission ────────────────────────────────────────────────
        let (region, cuts_flag) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts)
        };
        {
            let f = self.f_mut();
            *f.wrap_counts.entry(p).or_insert(0) += 1;
        }
        if cuts_flag {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        self.stats.tower_deabsorbs += 1;
        self.stats.deabsorb_join_blocks += join_blocks_total;
        if debug {
            eprintln!(
                "DEAB-OK fn={} region={} chain={} joins={}",
                self.rf.func.index(),
                region,
                m,
                join_blocks_total
            );
        }
        let mut body = Vec::new();
        if cuts_flag {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        for &id in ids {
            self.emit_content(id, Some(p), follow, &mut body);
        }
        let pending_mark = self.pending_wraps.len();
        let joins_mark = self.pending_joins.len();
        for cp in &chain_prots {
            self.pending_wraps.push(cp.clone());
        }
        for j in joins.iter().flatten() {
            self.pending_joins.push(j.1.clone());
        }
        for &b in &follow_chain {
            self.verified_fallout.push(b);
        }
        // The fall-out head for a clause level: the first non-empty
        // join level at or above it. Pure trampolines past the head
        // are transparent to a fall-out (the legacy verified-chain
        // rule), so the whole chain is verified — a handler guard
        // whose cut targets the chain end (A7_T2's B116 → B118 past
        // the B115 trampoline) keeps its conditional.
        let chain_at = |ctx: &Self, c: usize| -> Vec<BlockId> {
            let Some(lvl_x) = (c..=m).find(|&lvl_x| non_empty(lvl_x)) else {
                return Vec::new();
            };
            let Some((head, set)) = &joins[lvl_x] else {
                return Vec::new();
            };
            let mut out = vec![*head];
            let mut cur = *head;
            loop {
                let parts = ctx.block_parts(cur);
                if !parts.main.is_empty() || !parts.phi.is_empty() {
                    break;
                }
                match parts.term {
                    Term::Branch(d) if set.contains(&d) && !out.contains(&d) => {
                        out.push(d);
                        cur = d;
                    }
                    _ => break,
                }
                if out.len() > 16 {
                    break;
                }
            }
            out
        };
        // p's handlers (clause level 0): suppressed wraps are the whole
        // chain (their clauses sit inside every chain try body).
        let mut catches = Vec::new();
        {
            let suppress_mark = self.suppress_wraps.len();
            for cp in &chain_prots {
                self.suppress_wraps.push(cp.clone());
            }
            let vf = chain_at(self, 0);
            for &b in &vf {
                self.verified_fallout.push(b);
            }
            let encl: Vec<BlockId> = enclosed
                .iter()
                .filter(|(x, _)| handlers.contains(x))
                .map(|&(_, s)| s)
                .collect();
            for &s in &encl {
                self.verified_fallout.push(s);
            }
            let mut seen = HashSet::new();
            for h in &handlers {
                if seen.insert(*h) {
                    catches.push(self.emit_handler_unique(*h));
                }
            }
            for _ in &encl {
                self.verified_fallout.pop();
            }
            for _ in &vf {
                self.verified_fallout.pop();
            }
            self.suppress_wraps.truncate(suppress_mark);
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
            finally: None,
        };
        for (k, &(fq, q)) in chain.iter().enumerate() {
            let (qregion, qhandlers) = {
                let plan = &self.frames[fq].plans[q];
                (plan.region, plan.handlers.clone())
            };
            {
                let f = &mut self.frames[fq];
                *f.wrap_counts.entry(q).or_insert(0) += 1;
            }
            self.stats.try_catches += 1;
            // The join for this level lands inside chain[k]'s try body,
            // right after the inner construct (both the inner node's
            // fall-outs and its normal completion reach it).
            let mut inner = vec![node];
            if let Some((jhead, jset)) = &joins[k] {
                self.emit_join_level(*jhead, jset, &mut inner);
            }
            let mut qcatches = Vec::new();
            {
                let suppress_mark = self.suppress_wraps.len();
                for cp in &chain_prots[k + 1..] {
                    self.suppress_wraps.push(cp.clone());
                }
                let vf = chain_at(self, k + 1);
                for &b in &vf {
                    self.verified_fallout.push(b);
                }
                let encl: Vec<BlockId> = enclosed
                    .iter()
                    .filter(|(x, _)| qhandlers.contains(x))
                    .map(|&(_, s)| s)
                    .collect();
                for &s in &encl {
                    self.verified_fallout.push(s);
                }
                let mut seen = HashSet::new();
                for h in &qhandlers {
                    if seen.insert(*h) {
                        qcatches.push(self.emit_handler_unique(*h));
                    }
                }
                for _ in &encl {
                    self.verified_fallout.pop();
                }
                for _ in &vf {
                    self.verified_fallout.pop();
                }
                self.suppress_wraps.truncate(suppress_mark);
            }
            let qnote = if qcatches.len() > 1 {
                self.stats.multi_catch += 1;
                Some(format!(
                    "try region {qregion}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                    qcatches.len()
                ))
            } else {
                None
            };
            node = SNode::Try {
                body: inner,
                catches: qcatches,
                note: qnote,
                finally: None,
            };
        }
        self.pending_wraps.truncate(pending_mark);
        out.push(node);
        // The unprotected continuation: emitted once, after the
        // outermost try/catch.
        if let Some((ahead, aset)) = &joins[m] {
            self.emit_join_level(*ahead, aset, out);
        }
        self.pending_joins.truncate(joins_mark);
        for _ in &follow_chain {
            self.verified_fallout.pop();
        }
        // Record the emitted joins: a re-wrapped plan's tower must not
        // emit them twice (its analysis bails to the legacy path).
        for s in join_union {
            self.emitted_joins.insert(s);
        }
        true
    }

    //
    // A Mixed-coverage `If` whose head is protected is wrapped whole by
    // the generic path (the condition evaluation must stay protected).
    // But when one arm is terminal (throw/return), the acyclic region
    // tree absorbs the try's CONTINUATION — the join the handlers also
    // rejoin — into the other arm's sequence, and wrapping whole makes
    // the join unreachable from the catch path (dream gate:
    // branch-elimination/test-under-try-catch printed "true" for want
    // "true\ngood1"; opt-try-catch-func/test-passes-under-try-catch
    // lost the post-try print the same way). The VM's PC-range
    // dispatch rejoins the handler at the continuation, so the correct
    // projection is `try { <protected skeleton> } catch { … }` with
    // the unprotected tail emitted AFTER the try/catch.

    /// The innermost plan of the first protected block in emission
    /// order (the candidate plan a mixed `Seq`'s join hoist wraps).
    /// `None` when the node carries no protected content.
    fn leading_plan(&mut self, id: RegionId) -> Option<usize> {
        match self.f().node(id).clone() {
            RegionNode::Block(b) => self.f_mut().plan_of(b),
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                children.iter().find_map(|&c| self.leading_plan(c))
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                self.leading_plan(body)
            }
            RegionNode::If { head, .. } => self.f_mut().plan_of(head),
            RegionNode::Irreducible { blocks, .. } => {
                blocks.iter().find_map(|&b| self.f_mut().plan_of(b))
            }
        }
    }

    /// Phase 1: classify a Mixed node into protected skeleton +
    /// deferred tail for plan `p` (no emission, no mutation).
    fn cut_classify(&mut self, id: RegionId, p: usize) -> Option<CutSplit> {
        match self.f_mut().cov(id) {
            Cov::Uniform(Some(q)) if q == p => Some(CutSplit::Prot),
            Cov::Uniform(None) => Some(CutSplit::Defer),
            Cov::Uniform(Some(_)) => None, // a different plan — not splittable
            Cov::Mixed => {
                let node = self.f().node(id).clone();
                match node {
                    RegionNode::Seq(children) => {
                        // Protected prefix, then at most one recursively
                        // splitting child, then a fully-unprotected tail.
                        let mut i = 0;
                        let mut inner = None;
                        while i < children.len() {
                            match self.f_mut().cov(children[i]) {
                                Cov::Uniform(Some(q)) if q == p => i += 1,
                                Cov::Mixed => {
                                    let s = self.cut_classify(children[i], p)?;
                                    if matches!(s, CutSplit::Prot) {
                                        return None;
                                    }
                                    inner = Some(Box::new(s));
                                    i += 1;
                                    break;
                                }
                                _ => break,
                            }
                        }
                        for &c in &children[i..] {
                            if self.f_mut().cov(c) != Cov::Uniform(None) {
                                return None;
                            }
                        }
                        if inner.is_none() && i >= children.len() {
                            return None; // no tail at all (not Mixed — defensive)
                        }
                        if inner.is_none() && i == 0 {
                            return Some(CutSplit::Defer); // whole sequence defers
                        }
                        let split_at = if inner.is_some() { i - 1 } else { i };
                        Some(CutSplit::Seq { split_at, inner })
                    }
                    RegionNode::If {
                        head,
                        then,
                        otherwise,
                        ..
                    } => {
                        // The condition evaluation must stay protected.
                        if self.f_mut().plan_of(head) != Some(p) {
                            return None;
                        }
                        let mut has_split = false;
                        let then = self.cut_classify_arm(then, p, &mut has_split)?;
                        let otherwise = self.cut_classify_arm(otherwise, p, &mut has_split)?;
                        if !has_split {
                            return None;
                        }
                        Some(CutSplit::If { then, otherwise })
                    }
                    // Loops, labels, alternates, irreducible cores:
                    // beyond the v1 hoist — the generic wrap applies.
                    _ => None,
                }
            }
        }
    }

    /// Classify one `If` arm for the join hoist: fully-protected arms
    /// must be terminal-only (falling out would incorrectly route
    /// through the hoisted tail); at most one arm may split.
    fn cut_classify_arm(
        &mut self,
        arm: Option<RegionId>,
        p: usize,
        has_split: &mut bool,
    ) -> Option<Option<ArmCut>> {
        let Some(a) = arm else {
            return Some(None);
        };
        match self.f_mut().cov(a) {
            Cov::Uniform(Some(q)) if q == p => {
                if self.arm_exits_terminal(a) {
                    Some(Some(ArmCut::Terminal))
                } else {
                    None
                }
            }
            Cov::Mixed => {
                if *has_split {
                    return None; // two tails cannot merge into one rejoin
                }
                let s = self.cut_classify(a, p)?;
                if matches!(s, CutSplit::Prot) {
                    return None;
                }
                *has_split = true;
                Some(Some(ArmCut::Splits(Box::new(s))))
            }
            // A whole-arm defer (unprotected arm behind a protected
            // condition) or a foreign plan: beyond the v1 hoist.
            _ => None,
        }
    }

    /// Every exit path of a fully-protected arm is terminal: each
    /// out-of-arm edge carries a structural action (break/continue/
    /// alternates-arm jump) and each no-out-edge block ends in
    /// `throw`/`return`.
    fn arm_exits_terminal(&mut self, id: RegionId) -> bool {
        let blocks = self.f_mut().node_blocks(id);
        for b in &blocks {
            let parts = self.block_parts(*b);
            match parts.term {
                Term::None => {
                    let last = parts
                        .main
                        .iter()
                        .rposition(|s| !matches!(s, Stmt::Unreachable));
                    match last {
                        Some(i) if matches!(parts.main[i], Stmt::Throw(_) | Stmt::Return(_)) => {}
                        _ => return false,
                    }
                }
                Term::Branch(d) => {
                    if !blocks.contains(&d) && !self.edge_has_action(*b, d) {
                        return false;
                    }
                }
                Term::Cond(_, t, f) => {
                    if !blocks.contains(&t) && !self.edge_has_action(*b, t) {
                        return false;
                    }
                    if !blocks.contains(&f) && !self.edge_has_action(*b, f) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Collect the deferred tail's region nodes, in emission order.
    fn collect_defers(&mut self, id: RegionId, split: &CutSplit, out: &mut Vec<RegionId>) {
        match split {
            CutSplit::Prot => {}
            CutSplit::Defer => out.push(id),
            CutSplit::Seq { split_at, inner } => {
                let children = match self.f().node(id) {
                    RegionNode::Seq(c) => c.clone(),
                    _ => unreachable!("cut split shape mirrors the region node"),
                };
                let start = if let Some(inner) = inner {
                    self.collect_defers(children[*split_at], inner, out);
                    split_at + 1
                } else {
                    *split_at
                };
                for &c in &children[start..] {
                    out.push(c);
                }
            }
            CutSplit::If { then, otherwise } => {
                let (t, o) = match self.f().node(id) {
                    RegionNode::If {
                        then, otherwise, ..
                    } => (*then, *otherwise),
                    _ => unreachable!("cut split shape mirrors the region node"),
                };
                for (arm, cut) in [(t, then), (o, otherwise)] {
                    if let (Some(a), Some(ArmCut::Splits(s))) = (arm, cut) {
                        self.collect_defers(a, s, out);
                    }
                }
            }
        }
    }

    /// The join-hoist correctness condition, generalized: every
    /// out-of-shim Normal edge of every handler of plan `p` (the
    /// handlers' continuations, which the shim model cuts) must target
    /// the entry of one of the deferred tail's nodes, and all such
    /// edges must target the SAME tail node — the point where the VM's
    /// PC-range dispatch rejoins. Returns that node's index in
    /// `defers`. A nonzero index is only usable when the skipped
    /// prefix is try-path-only and cannot throw (phi wiring) — the
    /// caller checks [`Ctx::defer_prefix_phi_only`].
    fn handler_rejoin_index(&self, p: usize, defers: &[RegionId]) -> Option<usize> {
        let mut index: Option<usize> = None;
        for &h in &self.f().plans[p].handlers {
            let Some(set) = self.shim_sets.get(&h) else {
                return None; // exotic handler shape — no shim, no hoist
            };
            if !set.contains(&h) {
                return None;
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) {
                        let k = defers
                            .iter()
                            .position(|&d| self.entry_of(d) == Follow::Entry(s))?;
                        if index.is_some_and(|i| i != k) {
                            return None;
                        }
                        index = Some(k);
                    }
                }
            }
        }
        index
    }

    /// Whether a deferred-tail prefix is pure phi wiring (phi decls /
    /// assigns, elided guards — nothing that can throw). Only then may
    /// it stay inline in the try body: it is reachable solely from the
    /// try path, and over-protection is impossible when no instruction
    /// can raise (dream gate: test-passes-under-try-catch's B5, d-P5).
    fn defer_prefix_phi_only(&mut self, prefix: &[RegionId]) -> bool {
        for &id in prefix {
            let blocks = self.f_mut().node_blocks(id);
            for b in blocks {
                let parts = self.block_parts(b);
                if !parts.main.iter().all(|s| {
                    matches!(
                        s,
                        Stmt::PhiDecl { .. } | Stmt::PhiAssign { .. } | Stmt::Elided { .. }
                    )
                }) {
                    return false;
                }
            }
        }
        true
    }

    /// The join-hoist driver: split the cut node, emit
    /// `try { skeleton } catch { … }`, then the hoisted tail. Returns
    /// false (the caller falls back to the generic whole-wrap) unless
    /// every guard holds.
    fn emit_cut_try(
        &mut self,
        id: RegionId,
        p: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_CUT_DEBUG").is_some();
        // Phase 1 — pure analysis.
        let Some(split) = self.cut_classify(id, p) else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: classify failed");
            }
            return false;
        };
        if matches!(split, CutSplit::Prot) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: all-protected");
            }
            return false;
        }
        let mut defers = Vec::new();
        self.collect_defers(id, &split, &mut defers);
        let Some(&first) = defers.first() else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: no defers");
            }
            return false;
        };
        if !matches!(self.entry_of(first), Follow::Entry(_)) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: tail entry unknown");
            }
            return false;
        }
        // The handlers' rejoin point within the tail. A nonzero index
        // means the handlers rejoin LATER in the tail; the skipped
        // prefix stays inline in the try body (try-path-only) and must
        // be pure phi wiring (it would otherwise be over-protected).
        let Some(rejoin) = self.handler_rejoin_index(p, &defers) else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: handler rejoin not in the tail");
            }
            return false;
        };
        if rejoin > 0 && !self.defer_prefix_phi_only(&defers[..rejoin]) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: try-path prefix can throw");
            }
            return false;
        }
        let hoisted = &defers[rejoin..];
        let handlers = self.f().plans[p].handlers.clone();
        // v1: no outer finally-chain around this plan (the hoisted
        // tail's placement relative to chain wraps needs the generic
        // path).
        if self
            .outer_wrap_plan(
                &[self.f().plans[p].protected.clone()].into_iter().collect(),
                &handlers,
            )
            .is_some()
        {
            if debug {
                eprintln!("CUT-BAIL plan={p}: outer finally-chain present");
            }
            return false;
        }

        // Phase 2 — `try { skeleton } catch { … }` (the same
        // bookkeeping as `wrap_try_run`, plus the hoist note).
        let (region, cuts) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts)
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
        self.stats.try_join_hoists += 1;
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
        // The note wording names where the join was buried: a
        // protected conditional arm (the d-P5 `If` case) or below the
        // protected run in the region tree (the N69 `Seq` case — the
        // try range spans a loop and its post-loop statements while
        // the unprotected continuation is nested one level down).
        let buried = if matches!(self.f().node(id), RegionNode::If { .. }) {
            "nested inside a protected conditional arm"
        } else {
            "nested below the protected run in the region tree"
        };
        if rejoin > 0 {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the rejoin suffix is hoisted to after the try/catch; the try-path-only phi prefix stays inline (it cannot throw, so over-protection is impossible)"
            )));
        } else {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the unprotected tail is hoisted out of the try body to after the try/catch (the VM's PC-range dispatch rejoins there)"
            )));
        }
        let defer_ids: HashSet<RegionId> = hoisted.iter().copied().collect();
        self.f_mut().cut_defer = Some(CutDefer { ids: defer_ids });
        self.emit_content(id, Some(p), follow, &mut body);
        let leftover = match self.f_mut().cut_defer.take() {
            Some(cd) => !cd.ids.is_empty(),
            None => false,
        };
        if leftover {
            // Defensive: analysis/emission mismatch — a deferred node
            // was never intercepted. It is emitted in the tail below
            // (phase 3 walks the full list), so nothing is dropped.
            body.push(SNode::Honest(format!(
                "try region {region}: join-hoist analysis/emission mismatch — part of the tail stayed inline (phase-3 tail remains authoritative)"
            )));
        }
        // While the catch clauses are emitted, the hoisted tail's entry
        // is the verified physical fall-out target of every handler cut
        // edge (handler_rejoin_index proved it) — record it so the
        // shim-tail duplication stands down for those edges.
        let rejoin_entry = hoisted.first().and_then(|&d| match self.entry_of(d) {
            Follow::Entry(b) => Some(b),
            _ => None,
        });
        if let Some(b) = rejoin_entry {
            self.hoist_rejoins.push(b);
        }
        let mut catches = Vec::new();
        let mut seen = HashSet::new();
        for h in &handlers {
            if seen.insert(*h) {
                catches.push(self.emit_handler(*h));
            }
        }
        if rejoin_entry.is_some() {
            self.hoist_rejoins.pop();
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
        out.push(SNode::Try {
            body,
            catches,
            note,
            finally: None,
        });

        // Phase 3 — the hoisted tail: emitted with the caller's active
        // plan, follows threaded through the tail's own entries.
        for (i, &d) in hoisted.iter().enumerate() {
            let fl = if i + 1 < hoisted.len() {
                self.entry_of(hoisted[i + 1])
            } else {
                follow
            };
            self.emit_node(d, active, fl, out);
        }
        true
    }

    /// N78 (test262 try/S12.14_A9_T5): a try range CUTS a loop — the
    /// protected region is the loop header plus a body prefix, and the
    /// catch's continuation is the IN-LOOP test (es2abc lowers
    /// `do { … try {…} catch (e) { …; continue; } … } while (c)` with
    /// the catch body's `jmp` aimed at the test block). The legacy
    /// `emit_mixed` Loop rule wraps the WHOLE loop in the try; the
    /// catch clause then falls out PAST the loop (the in-loop rejoin
    /// is unreachable from there) — A9_T5's `#1.4` failure: one caught
    /// iteration, then `fin !== 10`. The d-P5 join hoist cannot repair
    /// it either: the rejoin sits behind a try-path-only prefix two
    /// nested `If`s deep, not at a flat Seq tail entry.
    ///
    /// When every guard below holds, emit the source shape instead:
    ///
    /// ```text
    /// do {
    ///   try {                        // the outer chain plan (finally idiom), when present
    ///     try { <protected skeleton> }              // p0
    ///     catch (e0) { …; continue; }               // continue → the do-while test
    ///     <prefix: chain-protected or phi-only>     // normal-path only
    ///   } catch (e1) { … }         // falls out at its own rejoin (mid tail)
    ///   <unprotected mid tail>
    ///   <test statements>
    /// } while (<test cond>);
    /// ```
    ///
    /// Soundness sketch: a `continue` in a do-while body evaluates the
    /// test next — exactly the handler's bytecode rejoin — and skips
    /// the prefix/mid-tail (the handler inlined the finally body). The
    /// normal path runs skeleton → prefix → mid tail → test. The chain
    /// plan's catch falls out at the mid tail's head (its handler's
    /// rejoin). The prefix may sit inside the chain plan's try only
    /// because every one of its blocks is chain-protected or pure phi
    /// wiring (over-protection is then impossible). All guards are
    /// structural; any deviation returns false and the caller keeps
    /// the legacy whole-loop wrap.
    fn try_loop_cut_do_while(
        &mut self,
        header: BlockId,
        body_r: RegionId,
        p0: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_LOOPCUT_DEBUG").is_some();
        macro_rules! bail {
            ($($arg:tt)*) => {{
                if debug {
                    eprintln!(
                        "LOOPCUT-BAIL fn={} plan={p0}: {}",
                        self.rf.func.index(),
                        format!($($arg)*)
                    );
                }
                self.stats.loop_cut_bails += 1;
                return false;
            }};
        }
        // v1 scope: the main frame, no enclosing plan, no labeled loop
        // (a labeled exit's form is fine, but the label bookkeeping is
        // the legacy path's).
        if self.frames.len() != 1 || active.is_some() {
            bail!("nested emission context");
        }
        if self.f().loop_labels.contains_key(&header) {
            bail!("labeled loop");
        }
        if self.entry_of(body_r) != Follow::Entry(header) {
            bail!("the body does not start at the header (not body-first)");
        }
        let handlers0 = self.f().plans[p0].handlers.clone();
        if handlers0.is_empty() {
            bail!("no handlers");
        }
        // The outward handler-protecting chain: at most one outer plan,
        // in THIS frame (the es2abc finally idiom over the cut try).
        let chain = self.select_wrap_chain(p0, &handlers0);
        if chain.len() > 1 {
            bail!("outer chain longer than 1");
        }
        let p1 = match chain.first() {
            Some(&(0, q)) => Some(q),
            Some(_) => bail!("chain step in another frame"),
            None => None,
        };
        let body_blocks = self.f_mut().node_blocks(body_r);
        // No nested loops inside the body (their header/latch
        // consumption interplays with the tail deferral).
        {
            let mut stack = vec![body_r];
            while let Some(id) = stack.pop() {
                match self.f().node(id) {
                    RegionNode::Loop { .. } => bail!("nested loop in the cut body"),
                    RegionNode::Seq(c) | RegionNode::Alternates(c) => {
                        stack.extend(c.iter().copied())
                    }
                    RegionNode::If {
                        then, otherwise, ..
                    } => stack.extend([then, otherwise].into_iter().flatten().copied()),
                    RegionNode::Labeled { body, .. } => stack.push(*body),
                    _ => {}
                }
            }
        }
        // No third plan touches the loop body.
        for (q, plan) in self.f().plans.iter().enumerate() {
            if q == p0 || Some(q) == p1 {
                continue;
            }
            if plan.protected.iter().any(|b| body_blocks.contains(b)) {
                bail!(
                    "a third plan (region {}) intersects the loop body",
                    plan.region
                );
            }
        }
        // p0's handlers must ALL rejoin at ONE block T inside the loop
        // (their only continuation — the catch clause gets a
        // `continue`). A handler that never leaves the shim needs no
        // repair but breaks the uniform shape — v1 bails.
        let mut test: Option<BlockId> = None;
        for &h in &handlers0 {
            let Some(set) = self.shim_sets.get(&h) else {
                bail!("handler B{} has no shim", h.index());
            };
            if !set.contains(&h) {
                bail!("handler B{} entry outside its shim", h.index());
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if set.contains(&s) {
                        continue;
                    }
                    if test.is_some_and(|t| t != s) {
                        bail!("handlers rejoin at more than one block");
                    }
                    test = Some(s);
                }
            }
        }
        let Some(test) = test else {
            bail!("no handler cut edge");
        };
        if test == header {
            bail!("the rejoin is the header (a while-shape — not body-first)");
        }
        if !body_blocks.contains(&test) {
            // The rejoin is outside the loop: the legacy whole-wrap's
            // fall-out is already correct.
            bail!("rejoin B{} is outside the loop", test.index());
        }
        // The chain plan's handlers rejoin at ONE block r1 inside the
        // body (the finally-dispatch fall-out), distinct from T.
        let mut rejoin1: Option<BlockId> = None;
        if let Some(q1) = p1 {
            let handlers1 = self.f().plans[q1].handlers.clone();
            if handlers1.is_empty() {
                bail!("chain plan without handlers");
            }
            for &h in &handlers1 {
                let Some(set) = self.shim_sets.get(&h) else {
                    bail!("chain handler B{} has no shim", h.index());
                };
                if !set.contains(&h) {
                    bail!("chain handler B{} entry outside its shim", h.index());
                }
                for &b in set {
                    for s in block_succs(self.module, b) {
                        if set.contains(&s) {
                            continue;
                        }
                        if rejoin1.is_some_and(|r| r != s) {
                            bail!("chain handlers rejoin at more than one block");
                        }
                        rejoin1 = Some(s);
                    }
                }
            }
            let r1 = rejoin1.expect("checked non-empty handlers");
            if r1 == test || !body_blocks.contains(&r1) {
                bail!("chain rejoin B{} not a distinct in-loop block", r1.index());
            }
            rejoin1 = Some(r1);
        }
        // No FOREIGN handler cuts into the loop body (its fall-out
        // position is not this driver's to place).
        let own: HashSet<BlockId> = handlers0.iter().copied().collect();
        let own1: HashSet<BlockId> = p1
            .map(|q| self.f().plans[q].handlers.iter().copied().collect())
            .unwrap_or_default();
        for (&h, set) in &self.shim_sets {
            if own.contains(&h) || own1.contains(&h) {
                continue;
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) && body_blocks.contains(&s) {
                        bail!("foreign handler B{} cuts into the loop body", h.index());
                    }
                }
            }
        }
        // T is the do-while test: a conditional whose one edge reaches
        // the header through pure trampolines (the latch) and whose
        // other is the loop exit at the structural continuation. No phi
        // wiring on the test/latch edges (v1).
        let tparts = self.block_parts(test);
        let Term::Cond(cond, tb, fb) = tparts.term.clone() else {
            bail!("rejoin B{} is not a conditional", test.index());
        };
        if !tparts.phi.is_empty() {
            bail!("the test block carries phi wiring");
        }
        let latch_chain = |ctx: &Self, start: BlockId| -> Option<Vec<BlockId>> {
            let mut chain = Vec::new();
            let mut cur = start;
            loop {
                if cur == header {
                    return Some(chain);
                }
                if chain.len() >= 4 || !ctx.is_trampoline(cur) {
                    return None;
                }
                chain.push(cur);
                cur = match ctx.block_parts(cur).term {
                    Term::Branch(d) => d,
                    _ => return None,
                };
            }
        };
        let (cond_true_continues, exit, tramps) =
            match (latch_chain(self, tb), latch_chain(self, fb)) {
                (Some(ch), None) => (true, fb, ch),
                (None, Some(ch)) => (false, tb, ch),
                _ => bail!("the test edges do not split into stay/exit"),
            };
        if body_blocks.contains(&exit) {
            bail!("the test's exit edge stays in the loop");
        }
        if !matches!(
            self.f().eclass.get(&(test, exit)),
            Some(EdgeClass::Break { labeled: false, .. })
        ) {
            bail!("the exit edge is not a plain break");
        }
        if !self.plain_break_ok(exit, follow) {
            bail!("the exit is not the structural continuation");
        }
        let latch_from = tramps.last().copied().unwrap_or(test);
        if !matches!(
            self.f().eclass.get(&(latch_from, header)),
            Some(EdgeClass::Continue { labeled: false, .. })
        ) {
            bail!("the latch edge is not a plain continue");
        }
        // The ONLY unlabeled loop-flow edges out of body blocks are this
        // loop's own: in the do-while form an unlabeled `continue` lands
        // at the TEST (not the header top) and an unlabeled `break`
        // exits THIS loop, so any other classification would misroute.
        for (&(from, to), class) in self.f().eclass.iter() {
            if !body_blocks.contains(&from) {
                continue;
            }
            match class {
                EdgeClass::Continue { labeled: false, .. } => {
                    if !(to == header && from == latch_from) {
                        bail!("extra unlabeled continue B{}→B{}", from.index(), to.index());
                    }
                }
                EdgeClass::Break {
                    labeled: false,
                    header: h2,
                } if *h2 != header => {
                    bail!("unlabeled break owned by an outer loop B{}", h2.index());
                }
                _ => {}
            }
        }
        // The spine walk: from the body region down to the test region.
        // `If` levels stay in the skeleton (the head must be protected
        // by p0 — the condition evaluation is protected — and the
        // non-spine arm protected by p0 and terminal-only: falling out
        // of it would route through the tail the try path owns). The
        // tail below the deepest `If` is a Seq spine whose items before
        // the test are the prefix/mid tail.
        let mut spine = body_r;
        let defer_root = loop {
            match self.f().node(spine).clone() {
                RegionNode::If {
                    head,
                    then,
                    otherwise,
                    ..
                } => {
                    if self.f_mut().plan_of(head) != Some(p0) {
                        bail!(
                            "spine If head B{} not protected by the cut plan",
                            head.index()
                        );
                    }
                    let then_has =
                        then.is_some_and(|a| self.f_mut().node_blocks(a).contains(&test));
                    let else_has =
                        otherwise.is_some_and(|a| self.f_mut().node_blocks(a).contains(&test));
                    if then_has == else_has {
                        bail!("the test is not on exactly one arm of B{}", head.index());
                    }
                    let (arm, other) = if then_has {
                        (then.expect("checked"), otherwise)
                    } else {
                        (otherwise.expect("checked"), then)
                    };
                    // A missing non-spine arm means the head's other
                    // edge falls out of the `If` — with the spine arm
                    // deferred, that fall-out would land inside the
                    // try body at an unverified target. Bail.
                    let Some(o) = other else {
                        bail!("spine If B{} has a missing arm", head.index());
                    };
                    {
                        let ok = matches!(self.f_mut().cov(o), Cov::Uniform(Some(q)) if q == p0);
                        if !ok || !self.arm_exits_terminal(o) {
                            bail!(
                                "non-spine arm of B{} is not protected+terminal",
                                head.index()
                            );
                        }
                    }
                    // The head's edge into the spine arm must be
                    // structural: an action (break/continue) would be
                    // emitted inside the try while the arm is deferred.
                    match self.entry_of(arm) {
                        Follow::Entry(se) if !self.edge_has_action(head, se) => {}
                        _ => bail!("spine edge out of B{} carries an action", head.index()),
                    }
                    spine = arm;
                }
                _ => break spine,
            }
        };
        if defer_root == body_r {
            bail!("no protected If above the tail (a flat sequence — the d-P5 hoist owns it)");
        }
        // The tail: nested Seqs from defer_root down to the test region
        // ({test} + the latch trampolines). The items before the test,
        // in emission order, are the prefix/mid tail.
        let tramp_set: BTreeSet<BlockId> = tramps.iter().copied().collect();
        let mut items: Vec<RegionId> = Vec::new();
        let mut cur = defer_root;
        let test_region = loop {
            let blocks = self.f_mut().node_blocks(cur);
            if blocks.contains(&test) && blocks.iter().all(|&b| b == test || tramp_set.contains(&b))
            {
                if self.entry_of(cur) != Follow::Entry(test) {
                    bail!("the test is not the entry of its region");
                }
                break cur;
            }
            match self.f().node(cur).clone() {
                RegionNode::Seq(children) => {
                    let Some(pos) = children
                        .iter()
                        .position(|&c| self.f_mut().node_blocks(c).contains(&test))
                    else {
                        bail!("the test is not below the deferred tail");
                    };
                    if pos + 1 != children.len() {
                        bail!("content after the loop test in the tail");
                    }
                    items.extend_from_slice(&children[..pos]);
                    cur = children[pos];
                }
                _ => bail!("the tail spine is not a plain sequence"),
            }
        };
        // Split the items at the chain plan's rejoin: the prefix sits
        // inside the chain plan's try body (each block chain-protected
        // or pure phi wiring — anything else would be over-protected),
        // the mid tail follows the chain try/catch unprotected.
        let split = match rejoin1 {
            Some(r1) => {
                let Some(k) = items
                    .iter()
                    .position(|&i| self.entry_of(i) == Follow::Entry(r1))
                else {
                    bail!("chain rejoin B{} is not a tail item entry", r1.index());
                };
                if k == 0 {
                    bail!("chain rejoin at the tail head");
                }
                k
            }
            None => 0,
        };
        let (prefix, midtail) = (&items[..split], &items[split..]);
        for &item in prefix {
            for b in self.f_mut().node_blocks(item) {
                if self.f_mut().plan_of(b) == Some(p0) {
                    bail!("prefix block B{} is protected by the cut plan", b.index());
                }
                let by_chain = p1.is_some_and(|q| self.f().plans[q].protected.contains(&b));
                if !by_chain {
                    let parts = self.block_parts(b);
                    let phi_only = parts.main.iter().all(|s| {
                        matches!(
                            s,
                            Stmt::PhiDecl { .. } | Stmt::PhiAssign { .. } | Stmt::Elided { .. }
                        )
                    });
                    if !phi_only {
                        bail!("prefix block B{} can throw (over-protection)", b.index());
                    }
                }
            }
        }
        for &item in midtail.iter().chain(std::iter::once(&test_region)) {
            for b in self.f_mut().node_blocks(item) {
                if self.f_mut().plan_of(b).is_some() {
                    bail!("tail block B{} is protected", b.index());
                }
            }
        }
        // The do-while condition cannot see body-scoped `const`/`let`
        // temporaries (the block scope ends before `while (…)`): inline
        // the test block's pure-atom temporaries into the condition;
        // anything else keeps the legacy whole-wrap.
        let mut cond = cond;
        let mut kept_main: Vec<Stmt> = Vec::new();
        for s in &tparts.main {
            match s {
                Stmt::Declare {
                    name,
                    mutable: false,
                    value,
                    ..
                } if matches!(value, Expr::Lit(_) | Expr::Ident(_) | Expr::Temp { .. }) => {
                    subst_expr(&mut cond, name, value);
                }
                _ => kept_main.push(s.clone()),
            }
        }
        if !clean_while_main_ok(&kept_main, &cond) {
            bail!("the test condition reads a body-scoped temporary");
        }

        // ── Emission ────────────────────────────────────────────────
        let (region0, cuts0) = {
            let plan = &self.f().plans[p0];
            (plan.region, plan.cuts)
        };
        let wraps = {
            let f = self.f_mut();
            let n = f.wrap_counts.entry(p0).or_insert(0);
            *n += 1;
            *n
        };
        if wraps > 1 {
            self.stats.try_splits += 1;
        }
        if cuts0 {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        let mut skel = Vec::new();
        if cuts0 {
            skel.push(SNode::Honest(format!(
                "try region {region0}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        if wraps > 1 {
            skel.push(SNode::Honest(format!(
                "try region {region0}: protected statements are not contiguous in the structured output — this is wrapper #{wraps} for the same region (catch body duplicated, finally-style)"
            )));
        }
        skel.push(SNode::Honest(format!(
            "try region {region0}: the protected range cuts a do-while loop — the try/catch is placed INSIDE the loop body and the catch's `continue` targets the in-loop test (the handlers' bytecode rejoin)"
        )));
        // The skeleton with the tail deferred (intercepted in
        // `emit_node`, emitted below by this driver).
        let skeleton_follow = prefix
            .first()
            .or_else(|| midtail.first())
            .map(|&i| self.entry_of(i))
            .unwrap_or(Follow::Entry(test));
        self.f_mut().cut_defer = Some(CutDefer {
            ids: [defer_root].into_iter().collect(),
        });
        self.emit_content(body_r, Some(p0), skeleton_follow, &mut skel);
        let leftover = match self.f_mut().cut_defer.take() {
            Some(cd) => !cd.ids.is_empty(),
            None => false,
        };
        if leftover {
            // Defensive: the deferred tail was never intercepted (the
            // spine walk above proved the path is If-arms all the way,
            // so this cannot happen). Nothing was pushed to `out`.
            bail!("the deferred tail stayed inline (analysis/emission mismatch)");
        }
        // p0's handlers: emitted with the chain pending/suppressed
        // (legacy parity — their clauses sit inside the chain's try
        // body), each gaining the `continue` that targets the loop test
        // (in a do-while the test is exactly what `continue` runs next).
        let pending_mark = self.pending_wraps.len();
        let suppress_mark = self.suppress_wraps.len();
        if let Some(q1) = p1 {
            let prot = self.f().plans[q1].protected.clone();
            self.pending_wraps.push(prot.clone());
            self.suppress_wraps.push(prot);
        }
        let mut catches0 = Vec::new();
        let mut seen = HashSet::new();
        for &h in &handlers0 {
            if seen.insert(h) {
                let mut c = self.emit_handler(h);
                c.body.push(SNode::Continue { label: None });
                catches0.push(c);
            }
        }
        self.suppress_wraps.truncate(suppress_mark);
        let note0 = if catches0.len() > 1 {
            self.stats.multi_catch += 1;
            Some(format!(
                "try region {region0}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                catches0.len()
            ))
        } else {
            None
        };
        let node0 = SNode::Try {
            body: skel,
            catches: catches0,
            note: note0,
            finally: None,
        };
        let mut loop_body: Vec<SNode> = Vec::new();
        if let Some(q1) = p1 {
            let (region1, cuts1) = {
                let plan = &self.f().plans[q1];
                (plan.region, plan.cuts)
            };
            let wraps = {
                let f = self.f_mut();
                let n = f.wrap_counts.entry(q1).or_insert(0);
                *n += 1;
                *n
            };
            if wraps > 1 {
                self.stats.try_splits += 1;
            }
            if cuts1 {
                self.stats.try_cuts += 1;
            }
            self.stats.try_catches += 1;
            let mut p1_body = Vec::new();
            if cuts1 {
                p1_body.push(SNode::Honest(format!(
                    "try region {region1}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
                )));
            }
            p1_body.push(SNode::Honest(format!(
                "try region {region1}: handler-protecting outer try (finally idiom) — wrapped around region {region0}'s in-loop try/catch"
            )));
            p1_body.push(node0);
            // The normal-path-only prefix (chain-protected or pure phi
            // wiring — verified above): the chain plan's catch must NOT
            // run it, so it sits inside the chain try body and the
            // catch's fall-out is the mid tail's head.
            for (i, &item) in prefix.iter().enumerate() {
                let fl = if i + 1 < prefix.len() {
                    self.entry_of(prefix[i + 1])
                } else {
                    self.entry_of(midtail[0])
                };
                self.emit_node(item, Some(q1), fl, &mut p1_body);
            }
            // The chain plan's handlers fall out at the mid tail's head
            // (verified: it is emitted right after this try/catch).
            let r1 = rejoin1.expect("p1 implies rejoin1");
            self.hoist_rejoins.push(r1);
            let handlers1 = self.f().plans[q1].handlers.clone();
            let mut catches1 = Vec::new();
            let mut seen = HashSet::new();
            for &h in &handlers1 {
                if seen.insert(h) {
                    catches1.push(self.emit_handler(h));
                }
            }
            self.hoist_rejoins.pop();
            let note1 = if catches1.len() > 1 {
                self.stats.multi_catch += 1;
                Some(format!(
                    "try region {region1}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                    catches1.len()
                ))
            } else {
                None
            };
            loop_body.push(SNode::Try {
                body: p1_body,
                catches: catches1,
                note: note1,
                finally: None,
            });
        } else {
            loop_body.push(node0);
        }
        self.pending_wraps.truncate(pending_mark);
        // The unprotected mid tail (headed by the chain handler's
        // rejoin), then the test block's statements.
        for (i, &item) in midtail.iter().enumerate() {
            let fl = if i + 1 < midtail.len() {
                self.entry_of(midtail[i + 1])
            } else {
                Follow::Entry(test)
            };
            self.emit_node(item, None, fl, &mut loop_body);
        }
        Self::push_stmts(&mut loop_body, Self::stmts_leaves(&kept_main));
        let while_cond = if cond_true_continues {
            cond
        } else {
            negate(&cond)
        };
        self.stats.loops_do_while += 1;
        self.stats.loop_cut_rewrites += 1;
        out.push(SNode::DoWhile {
            label: None,
            body: loop_body,
            cond: while_cond,
        });
        true
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
            RegionNode::Seq(children) => {
                // N69: a try range spanning nested sequence levels (a
                // protected prefix at THIS level whose continuation
                // plan keeps going inside a nested child — e.g. a try
                // over a loop and its post-loop statements while the
                // unprotected join sits one level down) would fragment
                // into per-level wrappers, with the catch path falling
                // through into protected statements. When the cut
                // split has a protected prefix here AND a nested split
                // below, route the whole node through the join hoist
                // (one try/catch; the unprotected tail emitted after
                // it). Flat protected-prefix + flat-tail sequences are
                // already handled correctly by the run coalescing in
                // `emit_seq_children`, so they keep the legacy path.
                let p = children.iter().find_map(|&c| self.leading_plan(c));
                if let Some(p) = p
                    && Some(p) != active
                    && matches!(
                        self.cut_classify(id, p),
                        Some(CutSplit::Seq { inner: Some(_), .. })
                    )
                    && self.emit_cut_try(id, p, active, follow, out)
                {
                    return;
                }
                self.emit_seq_children(&children, active, follow, out)
            }
            RegionNode::If { head, .. } => {
                let hp = self.f_mut().plan_of(head);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    // The d-P5 join hoist: when the try's continuation
                    // is buried in an arm, split instead of wrapping
                    // whole; otherwise the generic wrap.
                    if !self.emit_cut_try(id, p, active, follow, out) {
                        self.wrap_try(id, p, follow, out);
                    }
                } else {
                    self.emit_if(id, active, follow, out);
                }
            }
            RegionNode::Loop { header, kind, body } => {
                let hp = self.f_mut().plan_of(header);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    // N78: a try range cutting the loop whose handlers
                    // rejoin at the in-loop test emits as the source
                    // do-while (the try/catch inside the body, the
                    // catch's `continue` targeting the test). Any guard
                    // failure keeps the legacy whole-loop wrap.
                    if self.try_loop_cut_do_while(header, body, p, active, follow, out) {
                        return;
                    }
                    self.wrap_try(id, p, follow, out);
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
        // Handler-shim cut edge: the skip target is outside the shim's
        // block set, so it is reachable only by falling out of the
        // catch clause onto it. That is sound when the try/catch's
        // physical continuation IS that block (a verified fall-out —
        // the enclosing wrap_try_run saw a concrete `follow`, or a
        // join hoist hoisted the tail there); otherwise bail to the
        // leaf emitter, whose shim-tail duplication inlines the small
        // terminal tail into the skip arm instead (N76).
        if self.f().shim_of.is_some()
            && self.frame_shim_set().is_some_and(|s| !s.contains(&skip))
            && !self.verified_fallout.contains(&skip)
            && !self.hoist_rejoins.contains(&skip)
        {
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
                // The arm's last block DIVERGES from the local run:
                // its out-edge carries a terminator action (an
                // alternates-arm `break L$…` from the shared-tail
                // decomposition, a loop break/continue, …), so the arm
                // never falls through and the skip path alone must
                // land on the continuation. Without this case the fold
                // bails and the leaf emitter silently drops the skip
                // edge's jump (N76: switch/S12.11_A1_T2's
                // `case 1:`/`default:` split).
                Term::Branch(d)
                    if self.edge_has_action(sb, d)
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
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
        if matches!(parts.term, Term::None) {
            // No control out-edge (return/throw/end): main + phi run
            // together (the helper moves the exception-dispatch flush
            // before a terminal `throw`).
            Self::push_main_phi(out, &parts.main, &parts.phi);
            return;
        }
        Self::push_stmts(out, Self::stmts_leaves(&parts.main));
        match parts.term {
            Term::None => unreachable!("handled above"),
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
                } else if let Some((tail, _)) = self.shim_tail_dup(dest) {
                    // A handler-shim cut edge whose continuation is not
                    // physically reachable by fall-out: duplicate the
                    // (small, terminal) tail inline (N76).
                    out.extend(tail);
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
                // Handler-shim cut edges (out-of-set targets whose
                // continuation fall-out is not guaranteed): duplicate
                // the small terminal tail into the matching arm.
                let tail_t = if act_t.is_none() && dup_t.is_none() {
                    self.shim_tail_dup(t).map(|(nodes, _)| nodes)
                } else {
                    None
                };
                let tail_f = if act_f.is_none() && dup_f.is_none() {
                    self.shim_tail_dup(f).map(|(nodes, _)| nodes)
                } else {
                    None
                };
                let mut then: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
                then.extend(act_t);
                if let Some(dup) = dup_t {
                    then.extend(dup);
                }
                if let Some(tail) = tail_t {
                    then.extend(tail);
                }
                let mut otherwise: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                otherwise.extend(act_f);
                if let Some(dup) = dup_f {
                    otherwise.extend(dup);
                }
                if let Some(tail) = tail_f {
                    otherwise.extend(tail);
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
        // The head's out-edge action (break/continue) belongs AFTER the
        // arm's content, not before it: when the acyclic tree threads a
        // loop-exit TAIL into the arm (the arm's blocks no longer reach
        // the latch, so the head's edge into them is classified
        // Break/Continue), the arm still has to RUN — its finally
        // bodies, loop-carried phi assigns — before the exit happens.
        // Emitted first, the action makes the whole arm dead code
        // (dream gate: opt-try-catch-func/test-nested-try-catch's
        // `j === 5 → break` arm hung the inner loop, d-P5). When the
        // arm's own exits already carry their actions the head's action
        // is harmlessly dead after them; when the arm falls through it
        // is the required exit.
        let act_t = self.edge_action(head, t);
        let no_act_t = act_t.is_none();
        let mut then: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
        let mut duped_t = false;
        if act_t.is_none()
            && self.f().cross_arm.contains(&(head, t))
            && let Some(dup) = self.try_cross_arm_fold(head, t, follow)
        {
            then.extend(dup);
            duped_t = true;
        }
        if let Some(r) = then_r {
            self.emit_node(r, active, follow, &mut then);
        }
        then.extend(act_t);
        // A handler-shim head whose out-edge was CUT at the set
        // boundary (no arm region, no structural action): the target's
        // small terminal tail is duplicated into the arm, or the path
        // falls out of the catch clause to nowhere (N76,
        // try/S12.14_A15's finally-break dispatch).
        if no_act_t
            && then_r.is_none()
            && !duped_t
            && let Some((tail, _)) = self.shim_tail_dup(t)
        {
            then.extend(tail);
        }
        let act_f = self.edge_action(head, f);
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
        if let Some(r) = else_r {
            self.emit_node(r, active, follow, &mut otherwise);
        }
        otherwise.extend(act_f);
        if no_act_f
            && else_r.is_none()
            && !duped_f
            && let Some((tail, _)) = self.shim_tail_dup(f)
        {
            otherwise.extend(tail);
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
    // Emission context facets (region/block ids, active plan, follow,
    // sink); a bundling struct would only rename the plumbing.
    #[allow(clippy::too_many_arguments)]
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
                // The exit-phi assigns of a clean `while (cond)` are
                // emitted AFTER the loop (exactly-once on condition
                // termination). Any OTHER unlabeled break out of this
                // loop lands at exactly that point, so it would run
                // the header's exit-edge assigns and CLOBBER the values
                // its own path already delivered — including the
                // acyclic tree's exit-TAIL arms, whose head-edge
                // `Break { header }` classification marks them as loop
                // exits even though the target sits textually inside
                // the body region (dream gate:
                // opt-try-catch-func/test-nested-try-catch — the
                // `j === 5 → break` path re-entered with the
                // pre-increment j, d-P5). With such a break the general
                // `while (true)` form is required: it places the
                // exit-phi assigns on the condition-exit edge itself.
                let (_, phi_exit, _) = Self::partition_phi(&parts.phi, stay, exit);
                let exit_phis_bypassed = !phi_exit.is_empty()
                    && self.f().eclass.iter().any(|(&(from, _), class)| {
                        from != header
                            && body_blocks.contains(&from)
                            && matches!(
                                class,
                                EdgeClass::Break {
                                    labeled: false,
                                    header: h
                                } if *h == header
                            )
                    });
                if exit_is_break
                    && !exit_phis_bypassed
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
                // Same bypass hazard as the clean-while form: the
                // latch's exit-phi assigns land after the loop, where
                // any other unlabeled break out of this loop would run
                // them.
                let (_, phi_exit, _) = Self::partition_phi(&lp.phi, cont_dest, exit);
                let exit_phis_bypassed = !phi_exit.is_empty()
                    && self.f().eclass.iter().any(|(&(from, _), class)| {
                        from != latch
                            && body_blocks.contains(&from)
                            && matches!(
                                class,
                                EdgeClass::Break {
                                    labeled: false,
                                    header: h
                                } if *h == header
                            )
                    });
                if exit_is_break && !exit_phis_bypassed && self.plain_break_ok(exit, follow) {
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
    #[allow(clippy::too_many_arguments)] // loop-shape facets; see emit_loop
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
    #[allow(clippy::too_many_arguments)] // loop-shape facets; see emit_loop
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
            Self::push_main_phi(&mut body, &parts.main, &parts.phi);
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
            Self::push_main_phi(&mut body, &parts.main, &parts.phi);
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
        let mut frame = Frame::new(tree, plans);
        frame.shim_of = Some(h);
        if std::env::var_os("ABCD_SHIM_TREE_DEBUG").is_some() {
            eprintln!("--- shim tree for handler B{}", h.index());
            for (j, node) in frame.tree.nodes().iter().enumerate() {
                eprintln!("  R{j}: {:?}", node);
            }
            eprintln!("  cross_arms: {:?}", frame.tree.cross_arm_edges);
        }
        self.frames.push(frame);
        if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, &mut body);
        }
        self.frames.pop();
        CatchClause { binding, body }
    }

    /// N77: emit one catch handler's UNIQUE prefix through its
    /// de-absorption shim tree (the shared-join continuation is left
    /// to the enclosing tower's join emission; the cut edges fall out
    /// to it — verified by [`Ctx::emit_deabsorb_tower`]).
    fn emit_handler_unique(&mut self, h: BlockId) -> CatchClause {
        let binding = self
            .bmap
            .get(&h)
            .and_then(|&bi| self.rf.blocks[bi].stmts.first())
            .and_then(|s| match s {
                Stmt::CatchBind { name } => Some(name.clone()),
                _ => None,
            });
        let Some(tree) = self.uniq_trees.get(&h).cloned() else {
            return CatchClause {
                binding,
                body: vec![SNode::Honest(format!(
                    "handler B{}: unique-prefix body unavailable (no shim)",
                    h.index()
                ))],
            };
        };
        let plans = self.uniq_plans.get(&h).cloned().unwrap_or_default();
        let mut body = Vec::new();
        let mut frame = Frame::new(tree, plans);
        frame.shim_of = Some(h);
        frame.shim_uniq = true;
        self.frames.push(frame);
        if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, &mut body);
        }
        self.frames.pop();
        CatchClause { binding, body }
    }
}

/// Every block of a raw region tree (N77 join-shim verification).
fn tree_blocks(tree: &RegionTree) -> BTreeSet<BlockId> {
    fn walk(tree: &RegionTree, id: RegionId, out: &mut BTreeSet<BlockId>) {
        match tree.node(id) {
            RegionNode::Block(b) => {
                out.insert(*b);
            }
            RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                for &c in children {
                    walk(tree, c, out);
                }
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                walk(tree, *body, out)
            }
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => {
                out.insert(*head);
                for c in [then, otherwise].into_iter().flatten() {
                    walk(tree, *c, out);
                }
            }
        }
    }
    let mut out = BTreeSet::new();
    if let Some(root) = tree.root {
        walk(tree, root, &mut out);
    }
    out
}

/// The first-executed block of a raw region tree (N77 join-shim
/// verification; mirrors [`Ctx::entry_of`]).
fn tree_entry(tree: &RegionTree, id: RegionId) -> Option<BlockId> {
    match tree.node(id) {
        RegionNode::Block(b) => Some(*b),
        RegionNode::If { head, .. } => Some(*head),
        RegionNode::Loop { header, .. } => Some(*header),
        RegionNode::Labeled { label, .. } => Some(*label),
        RegionNode::Seq(children) => children.first().and_then(|&c| tree_entry(tree, c)),
        RegionNode::Alternates(_) | RegionNode::Irreducible { .. } => None,
    }
}

/// The ENTRY blocks of a tree's top-level emission positions
/// (reachable from the root through `Seq` nesting only): falling out
/// of anything inside the construct lands on the next top-level
/// construct's entry, so a handler-rejoin target must be one of these
/// (the N76 external-pred demotion guarantees it; N77 verifies it).
fn tree_top_blocks(tree: &RegionTree) -> BTreeSet<BlockId> {
    fn walk(tree: &RegionTree, id: RegionId, out: &mut BTreeSet<BlockId>) {
        match tree.node(id) {
            RegionNode::Seq(children) => {
                for &c in children {
                    walk(tree, c, out);
                }
            }
            _ => {
                if let Some(e) = tree_entry(tree, id) {
                    out.insert(e);
                }
            }
        }
    }
    let mut out = BTreeSet::new();
    if let Some(root) = tree.root {
        walk(tree, root, &mut out);
    }
    out
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

/// Replace every `Ident`/`Temp` named `name` in `e` with `value` (the
/// N78 loop-cut driver inlines the do-while test block's pure-atom
/// temporaries into the condition — a block-scoped `const` is invisible
/// to `while (…)`).
fn subst_expr(e: &mut Expr, name: &str, value: &Expr) {
    let hit = match e {
        Expr::Ident(n) => n == name,
        Expr::Temp { name: n, .. } => n == name,
        _ => false,
    };
    if hit {
        *e = value.clone();
        return;
    }
    for c in crate::folds::expr_children_mut(e) {
        subst_expr(c, name, value);
    }
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
