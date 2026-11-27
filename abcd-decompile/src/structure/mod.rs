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

use crate::expr::{Expr, Lit};
use crate::recover::{RecoveredFunc, Stmt};

pub mod regions;
mod try_project;

use self::regions::{
    CfgSubgraph, EdgeClass, EscapeHatch, LoopKind, RegionId, RegionNode, RegionTree,
    structure_regions, structure_subgraph,
};

/// A leaf statement: Stage-A statements plus Stage-B synthetic forms
/// (the desugar folds in [`crate::folds`] add [`Leaf::Destructure`];
/// the irreducible fallback uses [`Leaf::Decl`]/[`Leaf::Assign`]).
#[derive(Clone, Debug, PartialEq, Eq)]
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
pub enum SNode {
    /// A run of leaf statements (one block's content or a phi partition).
    Stmts(Vec<Leaf>),
    /// A bare lexical scope block: `{ body }`.
    Block(Vec<SNode>),
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
    /// re-detection fold output ([`crate::folds`]; the IR lowers switch
    /// cascades to compare/branch chains by design — `design/ir.md`,
    /// `design/decisions.md`).
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
pub struct CatchClause {
    /// The `catch (e)` binding (`None` = unavailable — honesty path).
    pub binding: Option<String>,
    /// The handler body.
    pub body: Vec<SNode>,
}

/// One case of [`SNode::Switch`]; `tests` empty = `default:`.
pub struct SwitchCase {
    /// The case test expressions.
    pub tests: Vec<Expr>,
    /// The case body.
    pub body: Vec<SNode>,
}

fn drain_snode_children(node: &mut SNode, stack: &mut Vec<SNode>) {
    match node {
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        SNode::Block(body) => {
            stack.extend(std::mem::take(body));
        }
        SNode::If {
            then, otherwise, ..
        } => {
            stack.extend(std::mem::take(then));
            stack.extend(std::mem::take(otherwise));
        }
        SNode::While { body, .. }
        | SNode::DoWhile { body, .. }
        | SNode::Labeled { body, .. }
        | SNode::ForOf { body, .. }
        | SNode::ForIn { body, .. } => {
            stack.extend(std::mem::take(body));
        }
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            stack.extend(std::mem::take(body));
            for mut c in std::mem::take(catches) {
                stack.extend(std::mem::take(&mut c.body));
            }
            if let Some(fin) = finally.take() {
                stack.extend(fin);
            }
        }
        SNode::Switch { cases, .. } => {
            for mut c in std::mem::take(cases) {
                stack.extend(std::mem::take(&mut c.body));
            }
        }
    }
}

impl Drop for SNode {
    fn drop(&mut self) {
        let mut stack: Vec<SNode> = Vec::new();
        drain_snode_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_snode_children(&mut cur, &mut stack);
        }
    }
}

impl Drop for CatchClause {
    fn drop(&mut self) {
        let mut stack: Vec<SNode> = std::mem::take(&mut self.body);
        while let Some(mut cur) = stack.pop() {
            drain_snode_children(&mut cur, &mut stack);
        }
    }
}

impl Clone for CatchClause {
    fn clone(&self) -> Self {
        Self {
            binding: self.binding.clone(),
            body: self.body.clone(),
        }
    }
}

impl PartialEq for CatchClause {
    fn eq(&self, other: &Self) -> bool {
        self.binding == other.binding && self.body == other.body
    }
}

impl Eq for CatchClause {}

impl std::fmt::Debug for CatchClause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CatchClause")
            .field("binding", &self.binding)
            .field("body", &self.body)
            .finish()
    }
}

impl Drop for SwitchCase {
    fn drop(&mut self) {
        let mut stack: Vec<SNode> = std::mem::take(&mut self.body);
        while let Some(mut cur) = stack.pop() {
            drain_snode_children(&mut cur, &mut stack);
        }
    }
}

impl Clone for SwitchCase {
    fn clone(&self) -> Self {
        Self {
            tests: self.tests.clone(),
            body: self.body.clone(),
        }
    }
}

impl PartialEq for SwitchCase {
    fn eq(&self, other: &Self) -> bool {
        self.tests == other.tests && self.body == other.body
    }
}

impl Eq for SwitchCase {}

impl std::fmt::Debug for SwitchCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SwitchCase")
            .field("tests", &self.tests)
            .field("body", &self.body)
            .finish()
    }
}

impl Clone for SNode {
    fn clone(&self) -> Self {
        enum Step<'a> {
            Eval(&'a SNode),
            FinishBlock(usize),
            FinishIf {
                cond: Expr,
                then_len: usize,
                else_len: usize,
            },
            FinishWhile {
                label: Option<String>,
                cond: Option<Expr>,
                body_len: usize,
            },
            FinishDoWhile {
                label: Option<String>,
                cond: Expr,
                body_len: usize,
            },
            FinishLabeled {
                label: String,
                body_len: usize,
            },
            FinishTry {
                note: Option<String>,
                body_len: usize,
                catch_meta: Vec<(Option<String>, usize)>,
                finally_len: Option<usize>,
            },
            FinishForOf {
                is_await: bool,
                binding: String,
                iter: Expr,
                body_len: usize,
            },
            FinishForIn {
                binding: String,
                obj: Expr,
                body_len: usize,
            },
            FinishSwitch {
                disc: Expr,
                case_meta: Vec<(Vec<Expr>, usize)>,
            },
        }
        match self {
            SNode::Stmts(leaves) => return SNode::Stmts(leaves.clone()),
            SNode::Break { label } => {
                return SNode::Break {
                    label: label.clone(),
                };
            }
            SNode::Continue { label } => {
                return SNode::Continue {
                    label: label.clone(),
                };
            }
            SNode::Honest(s) => return SNode::Honest(s.clone()),
            _ => {}
        }
        let mut steps: Vec<Step<'_>> = vec![Step::Eval(self)];
        let mut vals: Vec<SNode> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Eval(n) => match n {
                    SNode::Stmts(leaves) => vals.push(SNode::Stmts(leaves.clone())),
                    SNode::Block(body) => {
                        steps.push(Step::FinishBlock(body.len()));
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::Break { label } => vals.push(SNode::Break {
                        label: label.clone(),
                    }),
                    SNode::Continue { label } => vals.push(SNode::Continue {
                        label: label.clone(),
                    }),
                    SNode::Honest(s) => vals.push(SNode::Honest(s.clone())),
                    SNode::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        steps.push(Step::FinishIf {
                            cond: cond.clone(),
                            then_len: then.len(),
                            else_len: otherwise.len(),
                        });
                        for c in otherwise.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                        for c in then.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::While { label, cond, body } => {
                        steps.push(Step::FinishWhile {
                            label: label.clone(),
                            cond: cond.clone(),
                            body_len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::DoWhile { label, body, cond } => {
                        steps.push(Step::FinishDoWhile {
                            label: label.clone(),
                            cond: cond.clone(),
                            body_len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::Labeled { label, body } => {
                        steps.push(Step::FinishLabeled {
                            label: label.clone(),
                            body_len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::Try {
                        body,
                        catches,
                        note,
                        finally,
                    } => {
                        let catch_meta = catches
                            .iter()
                            .map(|c| (c.binding.clone(), c.body.len()))
                            .collect();
                        steps.push(Step::FinishTry {
                            note: note.clone(),
                            body_len: body.len(),
                            catch_meta,
                            finally_len: finally.as_ref().map(Vec::len),
                        });
                        if let Some(fin) = finally {
                            for c in fin.iter().rev() {
                                steps.push(Step::Eval(c));
                            }
                        }
                        for catch in catches.iter().rev() {
                            for c in catch.body.iter().rev() {
                                steps.push(Step::Eval(c));
                            }
                        }
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::ForOf {
                        is_await,
                        binding,
                        iter,
                        body,
                    } => {
                        steps.push(Step::FinishForOf {
                            is_await: *is_await,
                            binding: binding.clone(),
                            iter: iter.clone(),
                            body_len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::ForIn { binding, obj, body } => {
                        steps.push(Step::FinishForIn {
                            binding: binding.clone(),
                            obj: obj.clone(),
                            body_len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    SNode::Switch { disc, cases } => {
                        let case_meta = cases
                            .iter()
                            .map(|c| (c.tests.clone(), c.body.len()))
                            .collect();
                        steps.push(Step::FinishSwitch {
                            disc: disc.clone(),
                            case_meta,
                        });
                        for case in cases.iter().rev() {
                            for c in case.body.iter().rev() {
                                steps.push(Step::Eval(c));
                            }
                        }
                    }
                },
                Step::FinishBlock(body_len) => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::Block(body));
                }
                Step::FinishIf {
                    cond,
                    then_len,
                    else_len,
                } => {
                    let otherwise = vals.split_off(vals.len() - else_len);
                    let then = vals.split_off(vals.len() - then_len);
                    vals.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                }
                Step::FinishWhile {
                    label,
                    cond,
                    body_len,
                } => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::While { label, cond, body });
                }
                Step::FinishDoWhile {
                    label,
                    cond,
                    body_len,
                } => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::DoWhile { label, body, cond });
                }
                Step::FinishLabeled { label, body_len } => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::Labeled { label, body });
                }
                Step::FinishTry {
                    note,
                    body_len,
                    catch_meta,
                    finally_len,
                } => {
                    let finally = finally_len.map(|flen| vals.split_off(vals.len() - flen));
                    let mut catches = Vec::with_capacity(catch_meta.len());
                    for (binding, clen) in catch_meta.into_iter().rev() {
                        let cbody = vals.split_off(vals.len() - clen);
                        catches.push(CatchClause {
                            binding,
                            body: cbody,
                        });
                    }
                    catches.reverse();
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::Try {
                        body,
                        catches,
                        note,
                        finally,
                    });
                }
                Step::FinishForOf {
                    is_await,
                    binding,
                    iter,
                    body_len,
                } => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::ForOf {
                        is_await,
                        binding,
                        iter,
                        body,
                    });
                }
                Step::FinishForIn {
                    binding,
                    obj,
                    body_len,
                } => {
                    let body = vals.split_off(vals.len() - body_len);
                    vals.push(SNode::ForIn { binding, obj, body });
                }
                Step::FinishSwitch { disc, case_meta } => {
                    let mut cases = Vec::with_capacity(case_meta.len());
                    for (tests, clen) in case_meta.into_iter().rev() {
                        let cbody = vals.split_off(vals.len() - clen);
                        cases.push(SwitchCase { tests, body: cbody });
                    }
                    cases.reverse();
                    vals.push(SNode::Switch { disc, cases });
                }
            }
        }
        vals.pop().unwrap_or_else(|| SNode::Honest(String::new()))
    }
}

impl PartialEq for SNode {
    fn eq(&self, other: &Self) -> bool {
        let mut stack: Vec<(&SNode, &SNode)> = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (SNode::Stmts(x), SNode::Stmts(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (SNode::Block(b1), SNode::Block(b2)) => {
                    if b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (SNode::Break { label: x }, SNode::Break { label: y })
                | (SNode::Continue { label: x }, SNode::Continue { label: y }) => {
                    if x != y {
                        return false;
                    }
                }
                (SNode::Honest(x), SNode::Honest(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (
                    SNode::If {
                        cond: c1,
                        then: t1,
                        otherwise: o1,
                    },
                    SNode::If {
                        cond: c2,
                        then: t2,
                        otherwise: o2,
                    },
                ) => {
                    if c1 != c2 || t1.len() != t2.len() || o1.len() != o2.len() {
                        return false;
                    }
                    stack.extend(o1.iter().zip(o2.iter()));
                    stack.extend(t1.iter().zip(t2.iter()));
                }
                (
                    SNode::While {
                        label: l1,
                        cond: c1,
                        body: b1,
                    },
                    SNode::While {
                        label: l2,
                        cond: c2,
                        body: b2,
                    },
                ) => {
                    if l1 != l2 || c1 != c2 || b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::DoWhile {
                        label: l1,
                        body: b1,
                        cond: c1,
                    },
                    SNode::DoWhile {
                        label: l2,
                        body: b2,
                        cond: c2,
                    },
                ) => {
                    if l1 != l2 || c1 != c2 || b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::Labeled {
                        label: l1,
                        body: b1,
                    },
                    SNode::Labeled {
                        label: l2,
                        body: b2,
                    },
                ) => {
                    if l1 != l2 || b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::Try {
                        body: b1,
                        catches: c1,
                        note: n1,
                        finally: f1,
                    },
                    SNode::Try {
                        body: b2,
                        catches: c2,
                        note: n2,
                        finally: f2,
                    },
                ) => {
                    if n1 != n2
                        || b1.len() != b2.len()
                        || c1.len() != c2.len()
                        || f1.as_ref().map(Vec::len) != f2.as_ref().map(Vec::len)
                    {
                        return false;
                    }
                    for (cc1, cc2) in c1.iter().zip(c2.iter()) {
                        if cc1.binding != cc2.binding || cc1.body.len() != cc2.body.len() {
                            return false;
                        }
                        stack.extend(cc1.body.iter().zip(cc2.body.iter()));
                    }
                    if let (Some(ff1), Some(ff2)) = (f1, f2) {
                        stack.extend(ff1.iter().zip(ff2.iter()));
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::ForOf {
                        is_await: a1,
                        binding: bn1,
                        iter: i1,
                        body: b1,
                    },
                    SNode::ForOf {
                        is_await: a2,
                        binding: bn2,
                        iter: i2,
                        body: b2,
                    },
                ) => {
                    if a1 != a2 || bn1 != bn2 || i1 != i2 || b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::ForIn {
                        binding: bn1,
                        obj: o1,
                        body: b1,
                    },
                    SNode::ForIn {
                        binding: bn2,
                        obj: o2,
                        body: b2,
                    },
                ) => {
                    if bn1 != bn2 || o1 != o2 || b1.len() != b2.len() {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (
                    SNode::Switch {
                        disc: d1,
                        cases: c1,
                    },
                    SNode::Switch {
                        disc: d2,
                        cases: c2,
                    },
                ) => {
                    if d1 != d2 || c1.len() != c2.len() {
                        return false;
                    }
                    for (sc1, sc2) in c1.iter().zip(c2.iter()) {
                        if sc1.tests != sc2.tests || sc1.body.len() != sc2.body.len() {
                            return false;
                        }
                        stack.extend(sc1.body.iter().zip(sc2.body.iter()));
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SNode {}

impl std::fmt::Debug for SNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Node(&'a SNode),
            Nodes(&'a [SNode]),
            Raw(&'static str),
            Owned(String),
        }
        fn push_node_list<'a>(tasks: &mut Vec<Task<'a>>, slice: &'a [SNode]) {
            tasks.push(Task::Raw("]"));
            if !slice.is_empty() {
                tasks.push(Task::Nodes(slice));
            }
            tasks.push(Task::Raw("["));
        }
        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Raw(s) => f.write_str(s)?,
                Task::Owned(s) => f.write_str(&s)?,
                Task::Nodes(slice) => {
                    if let Some((first, rest)) = slice.split_first() {
                        if !rest.is_empty() {
                            tasks.push(Task::Nodes(rest));
                            tasks.push(Task::Raw(", "));
                        }
                        tasks.push(Task::Node(first));
                    }
                }
                Task::Node(node) => match node {
                    SNode::Stmts(leaves) => write!(f, "Stmts({leaves:?})")?,
                    SNode::Block(body) => {
                        f.write_str("Block(")?;
                        tasks.push(Task::Raw(")"));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        write!(f, "If {{ cond: {cond:?}, then: ")?;
                        tasks.push(Task::Raw(" }"));
                        push_node_list(&mut tasks, otherwise);
                        tasks.push(Task::Raw(", otherwise: "));
                        push_node_list(&mut tasks, then);
                    }
                    SNode::While { label, cond, body } => {
                        write!(f, "While {{ label: {label:?}, cond: {cond:?}, body: ")?;
                        tasks.push(Task::Raw(" }"));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::DoWhile { label, body, cond } => {
                        write!(f, "DoWhile {{ label: {label:?}, body: ")?;
                        tasks.push(Task::Owned(format!(", cond: {cond:?} }}")));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::Break { label } => write!(f, "Break {{ label: {label:?} }}")?,
                    SNode::Continue { label } => write!(f, "Continue {{ label: {label:?} }}")?,
                    SNode::Labeled { label, body } => {
                        write!(f, "Labeled {{ label: {label:?}, body: ")?;
                        tasks.push(Task::Raw(" }"));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::Try {
                        body,
                        catches,
                        note,
                        finally,
                    } => {
                        f.write_str("Try { body: ")?;
                        tasks.push(Task::Raw(" }"));
                        match finally {
                            Some(fin) => {
                                tasks.push(Task::Raw(")"));
                                push_node_list(&mut tasks, fin);
                                tasks
                                    .push(Task::Owned(format!(", note: {note:?}, finally: Some(")));
                            }
                            None => {
                                tasks.push(Task::Owned(format!(", note: {note:?}, finally: None")));
                            }
                        }
                        tasks.push(Task::Raw("]"));
                        for (ci, c) in catches.iter().enumerate().rev() {
                            tasks.push(Task::Raw(" }"));
                            push_node_list(&mut tasks, &c.body);
                            let prefix = if ci > 0 { ", " } else { "" };
                            tasks.push(Task::Owned(format!(
                                "{prefix}CatchClause {{ binding: {:?}, body: ",
                                c.binding
                            )));
                        }
                        tasks.push(Task::Raw(", catches: ["));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::ForOf {
                        is_await,
                        binding,
                        iter,
                        body,
                    } => {
                        write!(
                            f,
                            "ForOf {{ is_await: {is_await:?}, binding: {binding:?}, iter: {iter:?}, body: "
                        )?;
                        tasks.push(Task::Raw(" }"));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::ForIn { binding, obj, body } => {
                        write!(f, "ForIn {{ binding: {binding:?}, obj: {obj:?}, body: ")?;
                        tasks.push(Task::Raw(" }"));
                        push_node_list(&mut tasks, body);
                    }
                    SNode::Switch { disc, cases } => {
                        write!(f, "Switch {{ disc: {disc:?}, cases: [")?;
                        tasks.push(Task::Raw("] }"));
                        for (ci, c) in cases.iter().enumerate().rev() {
                            tasks.push(Task::Raw(" }"));
                            push_node_list(&mut tasks, &c.body);
                            let prefix = if ci > 0 { ", " } else { "" };
                            tasks.push(Task::Owned(format!(
                                "{prefix}SwitchCase {{ tests: {:?}, body: ",
                                c.tests
                            )));
                        }
                    }
                    SNode::Honest(s) => write!(f, "Honest({s:?})")?,
                },
            }
        }
        Ok(())
    }
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
    fn partition_phi(phi: &[Stmt], t: BlockId, f: BlockId) -> (Vec<Stmt>, Vec<Stmt>, Vec<Stmt>) {
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

    fn stmts_leaves(stmts: &[Stmt]) -> Vec<Leaf> {
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
    fn push_main_phi(&self, out: &mut Vec<SNode>, main: &[Stmt], phi: &[Stmt]) {
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
        self.edge_action_with_follow(from, to, Follow::Unknown)
    }

    fn edge_action_with_follow(
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
    fn plain_break_ok(&self, to: BlockId, follow: Follow) -> bool {
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
        self.cross_arm_dup_inner(site, target, false)
    }

    fn cross_arm_dup_inner(
        &mut self,
        site: BlockId,
        target: BlockId,
        dry_run: bool,
    ) -> Option<(Vec<SNode>, DupStop, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 128;
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
                if self.frames.len() > 16 {
                    return None;
                }
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
                    self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                    stop = Some(DupStop::Terminal);
                    None
                }
                Term::Branch(dest) => {
                    self.push_main_phi(&mut blk, &parts.main, &parts.phi);
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
                    let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                    self.push_main_phi(&mut tree_nodes, &parts.main, &rest);
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
        if dry_run {
            return Some((Vec::new(), stop, visited.len()));
        }
        // Assemble: segments whose plan differs from the site's get
        // their own try/catch wrapper (catch clauses are populated iteratively
        // on `Ctx::run_emit_tasks` via `deferred_try_catches` — zero recursion).
        let mut out: Vec<SNode> = Vec::new();
        for (plan, nodes) in segs {
            if plan != site_plan
                && let Some(p) = plan
            {
                let handlers = self.f().plans[p].handlers.clone();
                let p_region = self.f().plans[p].region;
                let wraps = {
                    let w = self.f_mut().wrap_counts.entry(p).or_insert(0);
                    *w += 1;
                    *w
                };
                if wraps > 1 {
                    self.stats.try_splits += 1;
                }
                self.stats.try_catches += 1;
                let tok = self.deferred_try_counter;
                self.deferred_try_counter += 1;
                self.deferred_try_catches
                    .push((tok, p_region, handlers, wraps));
                out.push(SNode::Try {
                    body: nodes,
                    catches: Vec::new(),
                    note: Some(deferred_try_marker(tok)),
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
        root_cur: BlockId,
        boundary: &BTreeSet<BlockId>,
        root_stop_at: Option<BlockId>,
        visited: &mut BTreeSet<BlockId>,
        stmts: &mut usize,
        root_depth: usize,
    ) -> Option<(Vec<SNode>, DupStop)> {
        enum DupTask {
            Visit {
                cur: BlockId,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterBranchTail,
            AfterThen {
                cond: Expr,
                main: Vec<Stmt>,
                rest: Vec<Stmt>,
                f: BlockId,
                phi_f: Vec<Stmt>,
                local_stop: Option<BlockId>,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterElse {
                cond: Expr,
                main: Vec<Stmt>,
                rest: Vec<Stmt>,
                then: Vec<SNode>,
                then_stop: DupStop,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterMergeTail,
        }
        const MAX_BLOCKS: usize = 12;
        const MAX_STMTS: usize = 128;
        const MAX_DEPTH: usize = 3;

        let mut tasks: Vec<DupTask> = vec![DupTask::Visit {
            cur: root_cur,
            stop_at: root_stop_at,
            depth: root_depth,
        }];
        let mut results: Vec<(Vec<SNode>, DupStop)> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                DupTask::Visit {
                    cur,
                    stop_at,
                    depth,
                } => {
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
                    match parts.term {
                        Term::None => {
                            let last = parts
                                .main
                                .iter()
                                .rposition(|s| !matches!(s, Stmt::Unreachable));
                            match last {
                                Some(i)
                                    if matches!(
                                        parts.main[i],
                                        Stmt::Return(_) | Stmt::Throw(_)
                                    ) => {}
                                _ => return None,
                            }
                            let mut blk = Vec::new();
                            self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                            results.push((blk, DupStop::Terminal));
                        }
                        Term::Branch(d) => {
                            let mut blk: Vec<SNode> = Vec::new();
                            self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                            if Some(d) == stop_at || !boundary.contains(&d) {
                                results.push((blk, DupStop::Rejoin(d)));
                            } else {
                                results.push((blk, DupStop::Terminal));
                                tasks.push(DupTask::AfterBranchTail);
                                tasks.push(DupTask::Visit {
                                    cur: d,
                                    stop_at,
                                    depth,
                                });
                            }
                        }
                        Term::Cond(cond, t, f) => {
                            let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                            let merge = self.tail_merge(t, f, boundary, stop_at);
                            let local_stop = merge.or(stop_at);
                            let mut head_t: Vec<SNode> = Vec::new();
                            Self::push_stmts(&mut head_t, Self::stmts_leaves(&phi_t));
                            tasks.push(DupTask::AfterThen {
                                cond,
                                main: parts.main,
                                rest,
                                f,
                                phi_f,
                                local_stop,
                                stop_at,
                                depth,
                            });
                            if Some(t) == local_stop {
                                results.push((head_t, DupStop::Rejoin(t)));
                            } else {
                                results.push((head_t, DupStop::Terminal));
                                tasks.push(DupTask::AfterBranchTail);
                                tasks.push(DupTask::Visit {
                                    cur: t,
                                    stop_at: local_stop,
                                    depth: depth + 1,
                                });
                            }
                        }
                    }
                }
                DupTask::AfterBranchTail | DupTask::AfterMergeTail => {
                    let (mut tail, stop) = results.pop()?;
                    let (mut head, _) = results.pop()?;
                    head.append(&mut tail);
                    results.push((head, stop));
                }
                DupTask::AfterThen {
                    cond,
                    main,
                    rest,
                    f,
                    phi_f,
                    local_stop,
                    stop_at,
                    depth,
                } => {
                    let (then, then_stop) = results.pop()?;
                    let mut head_f: Vec<SNode> = Vec::new();
                    Self::push_stmts(&mut head_f, Self::stmts_leaves(&phi_f));
                    tasks.push(DupTask::AfterElse {
                        cond,
                        main,
                        rest,
                        then,
                        then_stop,
                        stop_at,
                        depth,
                    });
                    if Some(f) == local_stop {
                        results.push((head_f, DupStop::Rejoin(f)));
                    } else {
                        results.push((head_f, DupStop::Terminal));
                        tasks.push(DupTask::AfterBranchTail);
                        tasks.push(DupTask::Visit {
                            cur: f,
                            stop_at: local_stop,
                            depth: depth + 1,
                        });
                    }
                }
                DupTask::AfterElse {
                    cond,
                    main,
                    rest,
                    then,
                    then_stop,
                    stop_at,
                    depth,
                } => {
                    let (otherwise, else_stop) = results.pop()?;
                    let cont = match (then_stop, else_stop) {
                        (DupStop::Terminal, DupStop::Terminal) => None,
                        (DupStop::Rejoin(a), DupStop::Rejoin(b)) if a == b => Some(a),
                        (DupStop::Terminal, DupStop::Rejoin(b)) => Some(b),
                        (DupStop::Rejoin(a), DupStop::Terminal) => Some(a),
                        _ => return None,
                    };
                    let mut nodes: Vec<SNode> = Vec::new();
                    self.push_main_phi(&mut nodes, &main, &rest);
                    nodes.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                    match cont {
                        None => results.push((nodes, DupStop::Terminal)),
                        Some(r) if Some(r) == stop_at => results.push((nodes, DupStop::Rejoin(r))),
                        Some(m) => {
                            results.push((nodes, DupStop::Terminal));
                            tasks.push(DupTask::AfterMergeTail);
                            tasks.push(DupTask::Visit {
                                cur: m,
                                stop_at,
                                depth,
                            });
                        }
                    }
                }
            }
        }
        results.pop()
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
        macro_rules! bail {
            ($why:expr) => {{
                let _ = $why;
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
                    self.push_main_phi(&mut out, &parts.main, &parts.phi);
                    self.stats.handler_tail_dups += 1;
                    self.stats.handler_tail_dup_blocks += visited.len();
                    return Some((out, visited.len()));
                }
                Term::Branch(d) => {
                    if set.contains(d) {
                        bail!("re-enters handler set");
                    }
                    self.push_main_phi(&mut out, &parts.main, &parts.phi);
                    cur = *d;
                }
                // A conditional mid-tail is beyond this fold (the same
                // bound as the cross-arm fold).
                Term::Cond(..) => bail!("conditional mid-tail"),
            }
        }
    }

    /// Non-Ramsey action check used by `try_run_fold`: speculative Ramsey
    /// scopes allow small plain `if` runs to fold inline without labels.
    fn edge_has_non_ramsey_action(&self, from: BlockId, to: BlockId) -> bool {
        self.f()
            .arm_scopes
            .iter()
            .any(|s| s.entry == to && !s.ramsey)
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

    // ── Emission (iterative heap workstack) ─────────────────────────

    fn emit_node(
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

impl<'m> Ctx<'m> {
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
        if skip == next_entry || self.edge_has_non_ramsey_action(b, skip) {
            return 0;
        }
        let skip_is_ramsey = self.edge_has_action(b, skip);
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
                    if !self.edge_has_non_ramsey_action(sb, d)
                        && d == rejoin
                        && (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
                    break true;
                }
                // The arm's last block is terminal: only the skip arm
                // falls through, to the continuation after the run.
                Term::None
                    if (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
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
                        && (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
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
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        self.push_main_phi(out, &parts.main, &rest);
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
        } else if self.f().cross_arm.contains(&(b, skip)) {
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

    /// Sequence emission step with [`RegionNode::Alternates`] pre-registration.
    fn step_seq(
        &mut self,
        children: Vec<RegionId>,
        idx: &mut usize,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        while *idx < children.len() {
            let i = *idx;
            if let Some(cd) = self.f_mut().cut_defer.as_mut()
                && cd.ids.remove(&children[i])
            {
                *idx += 1;
                continue;
            }
            if let Cov::Uniform(Some(p)) = self.f_mut().cov(children[i])
                && Some(p) != active
            {
                let mut j = i + 1;
                while j < children.len() && self.f_mut().cov(children[j]) == Cov::Uniform(Some(p)) {
                    j += 1;
                }
                if !self.is_suppressed(p) {
                    if j < children.len() && self.f_mut().cov(children[j]) == Cov::Mixed {
                        let after_fl = if j + 1 < children.len() {
                            self.entry_of(children[j + 1])
                        } else {
                            follow
                        };
                        if (i > 0 || j + 1 < children.len())
                            && let Some(plan) = self.plan_cut_try_slice(&children[i..=j], p, active)
                        {
                            let slice = children[i..=j].to_vec();
                            ts.tasks.push(StructTask::SeqStep {
                                children,
                                idx: j + 1,
                                active,
                                follow,
                            });
                            self.start_cut_try(
                                plan,
                                CutTryInput::Slice(slice),
                                p,
                                active,
                                after_fl,
                                ts,
                            );
                            return;
                        }
                        if let RegionNode::If { head, .. } = *self.f().node(children[j])
                            && self.f_mut().plan_of(head) == Some(p)
                            && !self.can_cut_try(children[j], p, active)
                        {
                            j += 1;
                        }
                    }
                    if let Some((core_start, core_end, core_p, prologues)) =
                        self.try_telescope_prologues(&children, i, j, p)
                    {
                        let fl = if core_end < children.len() {
                            self.entry_of(children[core_end])
                        } else {
                            follow
                        };
                        let core_ids = children[core_start..core_end].to_vec();
                        ts.tasks.push(StructTask::SeqStep {
                            children,
                            idx: core_end,
                            active,
                            follow,
                        });
                        ts.tasks.push(StructTask::WrapTryRun {
                            ids: core_ids,
                            p: core_p,
                            prologues,
                            follow: fl,
                        });
                        return;
                    }
                }
                let fl = if j < children.len() {
                    self.entry_of(children[j])
                } else {
                    follow
                };
                let run_ids = children[i..j].to_vec();
                ts.tasks.push(StructTask::SeqStep {
                    children,
                    idx: j,
                    active,
                    follow,
                });
                ts.tasks.push(StructTask::WrapTryRun {
                    ids: run_ids,
                    p,
                    prologues: Vec::new(),
                    follow: fl,
                });
                return;
            }
            let next_alt = (i..children.len()).find(|&j| {
                matches!(self.f().node(children[j]), RegionNode::Alternates(_))
                    && self.f_mut().cov(children[j]) == Cov::Uniform(active)
            });
            let Some(j) = next_alt else {
                let consumed = if let Some(mut sink) = ts.sinks.pop() {
                    let c = self.try_run_fold(&children, i, active, follow, &mut sink);
                    ts.sinks.push(sink);
                    c
                } else {
                    0
                };
                if consumed > 0 {
                    *idx += consumed;
                    continue;
                }
                if let Some((off, m)) =
                    self.find_ramsey_forward_merge(&children[i..], active, follow)
                {
                    let d_max = i + off;
                    let label = format!("L${}", m.index());
                    self.f_mut().arm_scopes.push(ArmScope {
                        entry: m,
                        label: label.clone(),
                        fallthrough_ok: true,
                        ramsey: true,
                    });
                    ts.sinks.push(Vec::new());
                    if d_max < children.len() {
                        ts.tasks.push(StructTask::SeqStep {
                            children: children[d_max..].to_vec(),
                            idx: 0,
                            active,
                            follow,
                        });
                    }
                    ts.tasks.push(StructTask::FinishRamseyScope { label });
                    ts.tasks.push(StructTask::SeqStep {
                        children: children[i..d_max].to_vec(),
                        idx: 0,
                        active,
                        follow: Follow::Entry(m),
                    });
                    return;
                }
                let fl = if i + 1 < children.len() {
                    self.entry_of(children[i + 1])
                } else {
                    follow
                };
                let child = children[i];
                ts.tasks.push(StructTask::SeqStep {
                    children,
                    idx: i + 1,
                    active,
                    follow,
                });
                ts.tasks.push(StructTask::EmitNode {
                    id: child,
                    active,
                    follow: fl,
                });
                return;
            };
            let scopes: Vec<ArmScope> = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms
                    .iter()
                    .filter_map(|&a| match self.f().node(a) {
                        RegionNode::Labeled { label, .. } => Some(ArmScope {
                            entry: *label,
                            label: format!("L${}", label.index()),
                            fallthrough_ok: false,
                            ramsey: false,
                        }),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let popped = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms.len(),
                _ => 0,
            };
            for s in scopes {
                self.f_mut().arm_scopes.push(s);
            }
            ts.tasks.push(StructTask::SeqAltPrefixStep {
                children,
                idx: i,
                alt_idx: j,
                popped,
                active,
                follow,
            });
            return;
        }
    }

    /// The first-executed block of a region (iterative over `Seq`).
    fn entry_of(&self, mut id: RegionId) -> Follow {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Follow::Entry(*b),
                RegionNode::If { head, .. } => return Follow::Entry(*head),
                RegionNode::Loop { header, .. } => return Follow::Entry(*header),
                RegionNode::Labeled { label, .. } => return Follow::Entry(*label),
                RegionNode::Seq(children) => match children.first() {
                    Some(&c) => id = c,
                    None => return Follow::Tail,
                },
                RegionNode::Alternates(_) | RegionNode::Irreducible { .. } => {
                    return Follow::Unknown;
                }
            }
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
            // before the first throwing statement).
            self.push_main_phi(out, &parts.main, &parts.phi);
            return;
        }
        match parts.term {
            Term::None => unreachable!("handled above"),
            Term::Branch(dest) => {
                self.push_main_phi(out, &parts.main, &parts.phi);
                if let Some(act) = self.edge_action_with_follow(b, dest, follow) {
                    out.push(act);
                } else if Follow::Entry(dest) != follow
                    && self.f().cross_arm.contains(&(b, dest))
                    && let Some(dup) = self.try_cross_arm_fold(b, dest, follow)
                {
                    // The edge jumps into a sibling arm (the es2abc
                    // `goto shared` idiom): duplicate the shared tail.
                    out.extend(dup);
                } else if Follow::Entry(dest) != follow
                    && let Some((tail, _)) = self.shim_tail_dup(dest)
                {
                    // A handler-shim cut edge whose continuation is not
                    // physically reachable by fall-out: duplicate the
                    // (small, terminal) tail inline (N76).
                    out.extend(tail);
                }
            }
            Term::Cond(cond, t, f) => {
                let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                self.push_main_phi(out, &parts.main, &rest);
                let act_t = self.edge_action_with_follow(b, t, follow);
                let act_f = self.edge_action_with_follow(b, f, follow);
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

    /// Emit an `If` node iteratively: head statements, partitioned phi assigns, arms.
    fn step_emit_if(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
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
        let Term::Cond(cond, t, f) = parts.term else {
            if let Some(mut sink) = ts.sinks.pop() {
                self.push_main_phi(&mut sink, &parts.main, &parts.phi);
                sink.push(SNode::Honest(format!(
                    "region If head B{} has no conditional terminator (data shape) — arms emitted sequentially",
                    head.index()
                )));
                ts.sinks.push(sink);
            }
            if let Some(r) = else_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: r,
                    active,
                    follow,
                });
            }
            if let Some(r) = then_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: r,
                    active,
                    follow,
                });
            }
            return;
        };
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        if let Some(mut sink) = ts.sinks.pop() {
            self.push_main_phi(&mut sink, &parts.main, &rest);
            ts.sinks.push(sink);
        }

        // Ramsey forward labeled-block merge (`D4` / `R5-1`): when one arm of
        // this `If` carries a `cross_arm` edge into the entry of its sibling
        // arm that `try_cross_arm_fold` cannot inline-duplicate (budget, loop,
        // complex diamond, or try boundary), wrap the jumping arm in
        // `L$<target_entry>: { if (cond) { <src_arm>; [break A$k;] } } <tgt_arm>`
        // inside `[A$k: { ... }]` so zero control-flow edges are ever dropped.
        let else_entry = else_r.and_then(|er| match self.entry_of(er) {
            Follow::Entry(e) => Some((e, er)),
            _ => None,
        });
        let then_entry = then_r.and_then(|tr| match self.entry_of(tr) {
            Follow::Entry(e) => Some((e, tr)),
            _ => None,
        });
        let ramsey_then_to_else = else_entry.and_then(|(ee, er)| {
            self.arm_has_unfoldable_cross_edge(head, t, then_r, ee, follow)
                .then_some((false, ee, er))
        });
        let ramsey_choice = ramsey_then_to_else.or_else(|| {
            then_entry.and_then(|(te, tr)| {
                self.arm_has_unfoldable_cross_edge(head, f, else_r, te, follow)
                    .then_some((true, te, tr))
            })
        });
        if let Some((else_to_then, tgt_entry, tgt_r)) = ramsey_choice {
            let (if_cond, src_dest, src_phi, src_r, tgt_phi) = if !else_to_then {
                (cond, t, phi_t, then_r, phi_f)
            } else {
                (negate(&cond), f, phi_f, else_r, phi_t)
            };
            let tgt_label = format!("L${}", tgt_entry.index());
            self.f_mut().arm_scopes.push(ArmScope {
                entry: tgt_entry,
                label: tgt_label.clone(),
                fallthrough_ok: true,
                ramsey: false,
            });
            let mut src_init = Vec::new();
            Self::push_stmts(&mut src_init, Self::stmts_leaves(&src_phi));
            ts.sinks.push(src_init);
            ts.tasks.push(StructTask::RamseyIfAfterSrc {
                head,
                if_cond,
                src_dest,
                src_r_is_none: src_r.is_none(),
                tgt_label,
                tgt_phi,
                tgt_r,
                active,
                follow,
            });
            if let Some(sr) = src_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: sr,
                    active,
                    follow,
                });
            }
            return;
        }

        let act_t = if then_r.is_none() {
            self.edge_action_with_follow(head, t, follow)
        } else {
            self.edge_action(head, t)
        };
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
        ts.sinks.push(then);
        ts.tasks.push(StructTask::IfAfterThen {
            head,
            cond,
            t,
            f,
            phi_f,
            act_t,
            no_act_t,
            then_r_is_none: then_r.is_none(),
            duped_t,
            else_r,
            active,
            follow,
        });
        if let Some(r) = then_r {
            ts.tasks.push(StructTask::EmitNode {
                id: r,
                active,
                follow,
            });
        }
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "loop emission threads region/header ids, loop kind, active plan, follow, and task state"
    )]
    pub(in crate::structure) fn step_emit_loop(
        &mut self,
        id: RegionId,
        header: BlockId,
        kind: LoopKind,
        body_r: RegionId,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        let _ = id;
        let label = self.f().loop_labels.get(&header).cloned();
        let body_blocks = self.f_mut().node_blocks(body_r);
        let parts = self.block_parts(header);

        if kind == LoopKind::While
            && self.first_block(body_r) == Some(header)
            && let Term::Cond(cond, t, f) = parts.term.clone()
        {
            let t_in = body_blocks.contains(&t);
            let f_in = body_blocks.contains(&f);
            if t_in != f_in {
                let (stay, exit) = if t_in { (t, f) } else { (f, t) };
                if self.clean_while_main_ok(header, &body_blocks, &parts, stay, exit, &cond) {
                    let exit_is_break = matches!(
                        self.f().eclass.get(&(header, exit)),
                        Some(EdgeClass::Break { labeled: false, .. })
                    );
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
                        let (phi_stay, phi_exit, rest) =
                            Self::partition_phi(&parts.phi, stay, exit);
                        let mut body: Vec<SNode> = Vec::new();
                        let mut hdr_phi = phi_stay;
                        hdr_phi.extend(rest);
                        self.push_main_phi(&mut body, &parts.main, &hdr_phi);
                        self.f_mut().skip_blocks.insert(header);
                        let while_cond = if t_in { cond } else { negate(&cond) };
                        ts.sinks.push(body);
                        ts.tasks.push(StructTask::FinishCleanWhile {
                            label,
                            while_cond,
                            phi_exit,
                        });
                        ts.tasks.push(StructTask::EmitNode {
                            id: body_r,
                            active,
                            follow: Follow::Tail,
                        });
                        return;
                    }
                }
            }
        }

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
                let (phi_cont, phi_exit, rest) = Self::partition_phi(&lp.phi, cont_dest, exit);
                let while_cond = if cond_true_continues {
                    cond.clone()
                } else {
                    negate(&cond)
                };
                let mut cond_reads: HashSet<&str> = HashSet::new();
                collect_expr_ident_refs(&while_cond, &mut cond_reads);
                let phi_clobbers_cond = phi_cont.iter().chain(rest.iter()).any(|s| {
                    matches!(
                        s,
                        Stmt::PhiAssign { target, .. } if cond_reads.contains(target.as_str())
                    )
                });
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
                if exit_is_break
                    && !phi_clobbers_cond
                    && !exit_phis_bypassed
                    && self.plain_break_ok(exit, follow)
                {
                    self.stats.loops_do_while += 1;
                    let mut latch_phi = phi_cont;
                    latch_phi.extend(rest);
                    let phi_exit = Self::stmts_leaves(&phi_exit);
                    self.f_mut().skip_blocks.insert(latch);
                    ts.sinks.push(Vec::new());
                    ts.tasks.push(StructTask::FinishDoWhile {
                        label,
                        lp_main: lp.main,
                        latch_phi,
                        while_cond,
                        phi_exit,
                    });
                    ts.tasks.push(StructTask::EmitNode {
                        id: body_r,
                        active,
                        follow: Follow::Tail,
                    });
                    return;
                }
            }
        }

        self.stats.loops_while_true += 1;
        ts.sinks.push(Vec::new());
        ts.tasks.push(StructTask::FinishWhileTrue { label });
        ts.tasks.push(StructTask::EmitNode {
            id: body_r,
            active,
            follow: Follow::Tail,
        });
    }

    /// The first block a region emits (iterative over `Seq`).
    fn first_block(&self, mut id: RegionId) -> Option<BlockId> {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Some(*b),
                RegionNode::Seq(children) => {
                    id = *children.first()?;
                }
                _ => return None,
            }
        }
    }

    /// The last block a region emits (iterative over `Seq`/`Labeled`).
    fn last_block(&self, mut id: RegionId) -> Option<BlockId> {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Some(*b),
                RegionNode::Seq(children) => {
                    id = *children.last()?;
                }
                RegionNode::Labeled { body, .. } => {
                    id = *body;
                }
                _ => return None,
            }
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

    /// Find the furthest forward merge `M` (`off >= 2`, skipping at least
    /// `slice[1]`) targeted by an unhandled Normal edge `(u, M)` from `u`
    /// inside `slice[0]`, where `M` is either `entry_of(slice[off])`
    /// (`off < slice.len()`) or the sequence's own `follow` (`off == slice.len()`).
    fn find_ramsey_forward_merge(
        &mut self,
        slice: &[RegionId],
        active: Option<usize>,
        follow: Follow,
    ) -> Option<(usize, BlockId)> {
        if slice.len() < 2 {
            return None;
        }
        if self.f_mut().cov(slice[0]) != Cov::Uniform(active) {
            return None;
        }
        let src_blocks = self.f_mut().node_blocks(slice[0]);
        for off in (2..=slice.len()).rev() {
            let m = if off < slice.len() {
                let Follow::Entry(m) = self.entry_of(slice[off]) else {
                    continue;
                };
                m
            } else {
                let Follow::Entry(m) = follow else {
                    continue;
                };
                m
            };
            if self.f().arm_scopes.iter().any(|s| s.entry == m) {
                continue;
            }
            if self.f().shim_of.is_some()
                && self.frame_shim_set().is_some_and(|s| !s.contains(&m))
                && !self.verified_fallout.contains(&m)
                && !self.hoist_rejoins.contains(&m)
            {
                continue;
            }
            if off < slice.len() {
                if self
                    .f()
                    .cut_defer
                    .as_ref()
                    .is_some_and(|cd| cd.ids.contains(&slice[off]))
                {
                    continue;
                }
                if let Cov::Uniform(Some(p)) = self.f_mut().cov(slice[off - 1])
                    && Some(p) != active
                    && self.f_mut().cov(slice[off]) == Cov::Uniform(Some(p))
                {
                    continue;
                }
            }
            if self
                .f()
                .arm_bodies
                .last()
                .is_some_and(|ab| !ab.slice.contains(&m))
            {
                continue;
            }
            let mut has_jump = false;
            for &u in &src_blocks {
                if self.edge_has_action(u, m) {
                    continue;
                }
                let parts = self.block_parts(u);
                let hits_m = match parts.term {
                    Term::Branch(d) => d == m,
                    Term::Cond(_, t, f) => t == m || f == m,
                    Term::None => false,
                };
                if !hits_m {
                    continue;
                }
                if self.f().cross_arm.contains(&(u, m))
                    && self
                        .cross_arm_dup_inner(u, m, true)
                        .is_some_and(|(_, stop, _)| Self::dup_ok_for_follow(stop, Follow::Entry(m)))
                {
                    continue;
                }
                has_jump = true;
                break;
            }
            if has_jump {
                return Some((off, m));
            }
        }
        None
    }

    /// Whether the arm `arm_r` (or bare `head -> branch_dest` when `arm_r` is
    /// `None`) contains a `cross_arm` edge to `target_entry` that
    /// `try_cross_arm_fold` cannot inline-duplicate.
    fn arm_has_unfoldable_cross_edge(
        &mut self,
        head: BlockId,
        branch_dest: BlockId,
        arm_r: Option<RegionId>,
        target_entry: BlockId,
        follow: Follow,
    ) -> bool {
        if self.f().arm_scopes.iter().any(|s| s.entry == target_entry) {
            return false;
        }
        match arm_r {
            None => {
                if branch_dest != target_entry
                    || !self.f().cross_arm.contains(&(head, target_entry))
                    || self.edge_has_action(head, target_entry)
                {
                    return false;
                }
                match self.cross_arm_dup_inner(head, target_entry, true) {
                    None => true,
                    Some((_, stop, _)) => !Self::dup_ok_for_follow(stop, follow),
                }
            }
            Some(ar) => {
                let ar_blocks = self.f_mut().node_blocks(ar);
                let candidates: Vec<BlockId> = ar_blocks
                    .iter()
                    .copied()
                    .filter(|&u| {
                        self.f().cross_arm.contains(&(u, target_entry))
                            && !self.edge_has_action(u, target_entry)
                    })
                    .collect();
                for u in candidates {
                    let fails = match self.cross_arm_dup_inner(u, target_entry, true) {
                        None => true,
                        Some((_, stop, _)) => match stop {
                            DupStop::Terminal => follow == Follow::Unknown,
                            DupStop::Rejoin(dest) => {
                                !ar_blocks.contains(&dest) && !Self::dup_ok_for_follow(stop, follow)
                            }
                        },
                    };
                    if fails {
                        return true;
                    }
                }
                false
            }
        }
    }

    /// Emit an `Irreducible` node as the state-variable dispatch escape
    /// hatch of design §4.2.4 (with the honesty comment).
    fn emit_irreducible(&mut self, id: RegionId, active: Option<usize>, out: &mut Vec<SNode>) {
        let blocks = match self.f().node(id) {
            RegionNode::Irreducible { blocks, .. } => blocks.clone(),
            _ => unreachable!("emit_irreducible on non-Irreducible"),
        };
        self.stats.irreducible_fallbacks += 1;
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
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
        self.emit_dispatch_loop(&blocks, entry, active, out);
    }

    /// The whole-function state-machine fallback (see `build`): d-P1
    /// detects irreducible cores and CrossEdge escape hatches, but the
    /// region tree still threads those blocks acyclically — the
    /// back-flow is not representable as loops, so the whole reachable
    /// function (including reachable catch handlers) falls back to
    /// state-variable dispatch.
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
            for tr in &f.try_regions {
                if tr.protected.contains(&b) {
                    for c in &tr.catches {
                        if set.insert(c.handler) {
                            queue.push_back(c.handler);
                        }
                    }
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
                EscapeHatch::CrossEdge { from, to } => {
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
        self.emit_dispatch_loop(&blocks, entry, None, out);
    }

    /// Unified state-variable dispatch loop over `blocks` (`R5-5`):
    /// preserves `TryRegion` exception routing, partitions `CondBranch`
    /// `PhiAssign`s per outgoing edge, and qualifies `continue D$k;` /
    /// `break D$k;` with an explicit dispatch-loop label.
    fn emit_dispatch_loop(
        &mut self,
        blocks: &[BlockId],
        entry: BlockId,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
        self.stats.state_machine_blocks += blocks.len();
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
        let idx = self.state_counter;
        self.state_counter += 1;
        let state = format!("s${idx}");
        let dispatch_label = format!("D${idx}");
        let catch_tmp = format!("e${idx}");

        let mut order: Vec<BlockId> = vec![entry];
        order.extend(blocks.iter().copied().filter(|&b| b != entry));

        // Predeclare catch-binding locals for in-set handlers so catch arms
        // can assign `<catch_name> = e$k; s$k = <handler>; continue D$k;`.
        let mut handler_catch_names: HashMap<BlockId, String> = HashMap::new();
        let mut predeclared_catch_vars: Vec<String> = Vec::new();
        let mut seen_catch_vars: BTreeSet<String> = BTreeSet::new();
        for &b in &order {
            let Some(p) = self.f_mut().plan_of(b) else {
                continue;
            };
            if Some(p) == active {
                continue;
            }
            let handlers = self.f().plans[p].handlers.clone();
            for h in handlers {
                if !set.contains(&h) || handler_catch_names.contains_key(&h) {
                    continue;
                }
                if let Some(cname) = self
                    .bmap
                    .get(&h)
                    .and_then(|&bi| self.rf.blocks[bi].stmts.first())
                    .and_then(|s| match s {
                        Stmt::CatchBind { name } => Some(name.clone()),
                        _ => None,
                    })
                {
                    if seen_catch_vars.insert(cname.clone()) {
                        predeclared_catch_vars.push(cname.clone());
                    }
                    handler_catch_names.insert(h, cname);
                }
            }
        }
        for cname in predeclared_catch_vars {
            out.push(SNode::Stmts(vec![Leaf::Decl {
                name: cname,
                mutable: true,
                value: None,
            }]));
        }

        out.push(SNode::Stmts(vec![Leaf::Decl {
            name: state.clone(),
            mutable: true,
            value: Some(num_lit(entry.index() as f64)),
        }]));

        let mut arms: Vec<(BlockId, Vec<SNode>)> = Vec::new();
        for b in order {
            let parts = self.block_parts(b);
            let mut body = Vec::new();
            match parts.term {
                Term::None => {
                    self.push_main_phi(&mut body, &parts.main, &parts.phi);
                }
                Term::Branch(dest) => {
                    self.push_main_phi(&mut body, &parts.main, &parts.phi);
                    if set.contains(&dest) {
                        body.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(dest.index() as f64),
                        }]));
                        body.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut body, b, dest, &dispatch_label);
                    }
                }
                Term::Cond(cond, t, f) => {
                    let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                    self.push_main_phi(&mut body, &parts.main, &rest);
                    let mut then = Vec::new();
                    Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
                    if set.contains(&t) {
                        then.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(t.index() as f64),
                        }]));
                        then.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut then, b, t, &dispatch_label);
                    }
                    let mut otherwise = Vec::new();
                    Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                    if set.contains(&f) {
                        otherwise.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(f.index() as f64),
                        }]));
                        otherwise.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut otherwise, b, f, &dispatch_label);
                    }
                    body.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                }
            }

            if let Some(p) = self.f_mut().plan_of(b)
                && Some(p) != active
            {
                let handlers = self.f().plans[p].handlers.clone();
                let p_region = self.f().plans[p].region;
                if let Some(&h0) = handlers.first() {
                    self.stats.try_catches += 1;
                    if set.contains(&h0) {
                        let mut c_leaves = Vec::new();
                        if let Some(cname) = handler_catch_names.get(&h0) {
                            c_leaves.push(Leaf::Assign {
                                target: cname.clone(),
                                value: Expr::Ident(catch_tmp.clone()),
                            });
                        }
                        c_leaves.push(Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(h0.index() as f64),
                        });
                        let mut cbody = vec![SNode::Stmts(c_leaves)];
                        if handlers.len() > 1 {
                            self.stats.multi_catch += 1;
                            cbody.insert(
                                0,
                                SNode::Honest(format!(
                                    "try region {p_region}: multiple typed catch handlers merged into primary dispatch handler B{}",
                                    h0.index()
                                )),
                            );
                        }
                        cbody.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                        body = vec![SNode::Try {
                            body,
                            catches: vec![CatchClause {
                                binding: Some(catch_tmp.clone()),
                                body: cbody,
                            }],
                            note: None,
                            finally: None,
                        }];
                    } else {
                        let tok = self.deferred_try_counter;
                        self.deferred_try_counter += 1;
                        self.deferred_try_catches.push((tok, p_region, handlers, 0));
                        body = vec![SNode::Try {
                            body,
                            catches: Vec::new(),
                            note: Some(deferred_try_marker(tok)),
                            finally: None,
                        }];
                    }
                }
            }
            arms.push((b, body));
        }

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
            label: Some(dispatch_label),
            cond: None,
            body: chain,
        });
    }

    /// Clean-`while` precondition (`D2`): `emit_clean_while` moves `parts.main`
    /// into the top of `body` (AFTER `while (cond)`), which is only sound when:
    /// - `parts.phi` carries no exceptional-edge phi flush if `cond` may throw;
    /// - every statement in `parts.main` is `PhiAssign` / `PhiDecl` / `Elided`
    ///   or a `Declare { name, value, value_id, .. }` such that:
    ///   - `name` is NOT referenced in `cond`,
    ///   - `value` is side-effect-free (`expr_is_pure`), and
    ///   - `name` / `value_id` is NOT referenced in `phi_exit` or in any
    ///     block outside `{header} ∪ body_blocks` (verified via both Stage-A
    ///     statements and `UseDefChains`).
    fn clean_while_main_ok(
        &mut self,
        header: BlockId,
        body_blocks: &BTreeSet<BlockId>,
        parts: &BlockParts,
        stay: BlockId,
        exit: BlockId,
        cond: &Expr,
    ) -> bool {
        if !cond_avoids_main_decls(&parts.main, cond) {
            return false;
        }
        let (_, phi_exit, rest) = Self::partition_phi(&parts.phi, stay, exit);
        let has_xphi = rest.iter().any(|s| {
            matches!(
                s,
                Stmt::PhiAssign {
                    exceptional: true,
                    ..
                }
            )
        });
        if has_xphi && expr_may_throw(cond, &self.safe_idents) {
            return false;
        }
        let mut decls: Vec<(&str, abcd_ir::ValueId)> = Vec::new();
        for s in &parts.main {
            match s {
                Stmt::PhiAssign { .. } | Stmt::PhiDecl { .. } | Stmt::Elided { .. } => {}
                Stmt::Declare {
                    name,
                    value,
                    value_id,
                    ..
                } => {
                    if !expr_is_pure(value, &self.safe_idents) {
                        return false;
                    }
                    decls.push((name.as_str(), *value_id));
                }
                _ => return false,
            }
        }
        if decls.is_empty() {
            return true;
        }
        let mut exit_reads: HashSet<&str> = HashSet::new();
        for s in &phi_exit {
            if let Stmt::PhiAssign { value, .. } = s {
                collect_expr_ident_refs(value, &mut exit_reads);
            }
        }
        for &(name, _) in &decls {
            if exit_reads.contains(name) {
                return false;
            }
        }
        let decl_names: HashSet<&str> = decls.iter().map(|&(n, _)| n).collect();
        for blk in &self.rf.blocks {
            if blk.block == header || body_blocks.contains(&blk.block) {
                continue;
            }
            for stmt in &blk.stmts {
                if stmt_reads_any_name(stmt, &decl_names) {
                    return false;
                }
            }
        }
        let module = self.module;
        let func = self.rf.func;
        let chains = self
            .chains
            .get_or_insert_with(|| abcd_analysis::dataflow::UseDefChains::build(module, func));
        for &(_, vid) in &decls {
            for &use_iid in chains.users_of(vid) {
                let Some(uinst) = module.inst(use_iid) else {
                    return false;
                };
                if uinst.block != header && !body_blocks.contains(&uinst.block) {
                    return false;
                }
            }
            for &(phi_iid, edge) in chains.phi_users(vid) {
                let Some(pinst) = module.inst(phi_iid) else {
                    return false;
                };
                if (pinst.block != header && !body_blocks.contains(&pinst.block))
                    || (edge.from != header && !body_blocks.contains(&edge.from))
                {
                    return false;
                }
            }
        }
        true
    }
}

/// Collect every `Expr::Ident` / `Expr::Temp` name referenced inside `e`
/// iteratively (zero recursion).
fn collect_expr_ident_refs<'a>(e: &'a Expr, out: &mut HashSet<&'a str>) {
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

fn stmt_reads_any_name(stmt: &Stmt, names: &HashSet<&str>) -> bool {
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

fn stmt_may_throw(s: &Stmt, safe_idents: &HashSet<String>) -> bool {
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

fn deferred_try_marker(tok: usize) -> String {
    format!("__DEFERRED_TRY_CATCH_{tok}__")
}

fn resolve_deferred_try_in_task_state(
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

fn nodes_use_label(nodes: &[SNode], target: &str) -> bool {
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

/// A number literal expression.
pub(in crate::structure) fn num_lit(v: f64) -> Expr {
    Expr::Lit(Lit::Number(v.to_bits()))
}

/// Whether a node is a control-flow terminal (break/continue/return/
/// throw) — used to avoid appending dead `break`s after alternates arms
/// and switch cases.
pub fn is_terminal_node(mut n: &SNode) -> bool {
    loop {
        match n {
            SNode::Block(body) => match body.last() {
                Some(last) => n = last,
                None => return false,
            },
            SNode::Break { .. } | SNode::Continue { .. } => return true,
            SNode::Stmts(s) => {
                return matches!(
                    s.last(),
                    Some(Leaf::Raw(
                        Stmt::Return(_) | Stmt::Throw(_) | Stmt::Unreachable
                    ))
                );
            }
            _ => return false,
        }
    }
}

/// Check that `cond` does not reference any block-scoped `Declare` in `main`
/// (shared with `try_loop_cut_do_while` where `main` stays inside `do { … }`
/// before `while (cond)`).
pub(in crate::structure) fn cond_avoids_main_decls(main: &[Stmt], cond: &Expr) -> bool {
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
pub(in crate::structure) fn subst_expr(e: &mut Expr, name: &str, value: &Expr) {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        let hit = match cur {
            Expr::Ident(n) => n == name,
            Expr::Temp { name: n, .. } => n == name,
            _ => false,
        };
        if hit {
            *cur = value.clone();
            continue;
        }
        stack.extend(crate::folds::expr_children_mut(cur));
    }
}

/// Negate a condition, simplifying the wrapper forms es2abc produces
/// (`istrue`/`isfalse`/logical-not and NaN-safe equality comparisons — `D4`:
/// relational `<`/`<=`/`>`/`>=` are NOT flipped because `!(NaN < 1)` is `true`
/// while `NaN >= 1` is `false`).
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
            op: UnOp::JumpNez,
            operand,
        } => Expr::Unary {
            op: UnOp::JumpEqz,
            operand: operand.clone(),
        },
        Expr::Unary {
            op: UnOp::JumpEqz,
            operand,
        } => Expr::Unary {
            op: UnOp::JumpNez,
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
                CmpOp::Less
                | CmpOp::GreaterEq
                | CmpOp::Greater
                | CmpOp::LessEq
                | CmpOp::In
                | CmpOp::InstanceOf => None,
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
