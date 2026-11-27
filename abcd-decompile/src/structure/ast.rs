//! Structured statement AST (`SNode`, `Leaf`, `CatchClause`, `SwitchCase`),
//! iterative heap-workstack trait implementations, `StructStats`, and condition helpers.

use std::collections::BTreeSet;

use abcd_ir::op::{CmpOp, UnOp};

use crate::expr::{Expr, Lit};
use crate::recover::Stmt;

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
///
/// Intentional JS readability contract (`ADR-21` `R5-D1`, pinned by
/// `emit/tests/batch_and_stack.rs:561-652`): `UnOp::JumpNez` and `UnOp::JumpEqz`
/// flip symmetrically here and render as idiomatic JS truthiness/falsiness,
/// while `abcd-ir`, `abcd-lift`, `abcd-opt`, and `abcd-lower` preserve exact
/// `R3-X1` raw VM `jeqz`/`jnez` semantics for optimization and binary rewriting.
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
        // Intentional `ADR-21` `R5-D1` JS readability contract (pinned by
        // `emit/tests/batch_and_stack.rs:561-652`): render `JumpNez(p)` /
        // `JumpEqz(p)` as idiomatic JS truthiness/falsiness (`!!p` / `!p` and
        // `if (p)` / `if (!p)`), while `abcd-ir`, `abcd-lift`, `abcd-opt`, and
        // `abcd-lower` preserve exact `R3-X1` raw VM `jeqz`/`jnez` semantics.
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
