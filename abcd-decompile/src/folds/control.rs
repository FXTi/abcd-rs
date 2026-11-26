//! Control-flow desugaring folds: `switch` re-detection and duplicated-`finally` folding.

use super::*;

// ── Fold 5: switch re-detection ──────────────────────────────────────

pub(in crate::folds) fn fold_switches(nodes: &mut [SNode], stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let Some((disc, cases)) = match_switch_chain(&nodes[i]) else {
            i += 1;
            continue;
        };
        if cases.len() < 2 {
            i += 1;
            continue;
        }
        stats.switch += 1;
        nodes[i] = SNode::Switch { disc, cases };
        i += 1;
    }
}

/// Match an `if (x === lit) {…} else if (x === lit) {…} …` chain.
pub(in crate::folds) fn match_switch_chain(n: &SNode) -> Option<(Expr, Vec<SwitchCase>)> {
    let SNode::If {
        cond,
        then,
        otherwise,
    } = n
    else {
        return None;
    };
    // Polarity-aware: a `isfalse(x === lit)` / `!(x === lit)` test puts
    // the case body in the FALSE arm and the chain continuation in the
    // true arm (dream gate: the polarity-blind form swapped the arms of
    // `x ?? y` — local/optional-chain).
    let (disc, lit, positive) = switch_test(cond)?;
    let (case_body, cont) = if positive {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    // An unlabeled `break` in a case arm changes meaning under the
    // fold: before the fold it exits the enclosing LOOP; inside a
    // `switch` it would exit the switch (dream gate:
    // opt-try-catch-func/test-nested-try-catch hung —
    // `case 5.0: break` fell back into the loop, d-P5). The fold is
    // cosmetic; keep the if-chain instead. (Labeled breaks name their
    // target and `continue` ignores switches, so both are safe.)
    if arm_has_loop_break(case_body) {
        return None;
    }
    let mut cases = vec![SwitchCase {
        tests: vec![lit],
        body: with_break(case_body.clone()),
    }];
    let mut rest = cont;
    loop {
        match rest.as_slice() {
            [
                SNode::If {
                    cond: c2,
                    then: t2,
                    otherwise: o2,
                },
            ] => {
                let (d2, lit2, pos2) = switch_test(c2)?;
                if d2 != disc {
                    return None;
                }
                let (body2, cont2) = if pos2 { (t2, o2) } else { (o2, t2) };
                if arm_has_loop_break(body2) {
                    return None;
                }
                cases.push(SwitchCase {
                    tests: vec![lit2],
                    body: with_break(body2.clone()),
                });
                rest = cont2;
            }
            [] => break,
            // A nested switch on the SAME discriminant (a chain folded
            // bottom-up, or the state-machine dispatch chain) flattens
            // into this one's cases.
            [
                SNode::Switch {
                    disc: d2,
                    cases: c2,
                },
            ] if *d2 == disc => {
                cases.extend(c2.iter().cloned());
                break;
            }
            other => {
                if arm_has_loop_break(other) {
                    return None;
                }
                cases.push(SwitchCase {
                    tests: vec![],
                    body: other.to_vec(),
                });
                break;
            }
        }
    }
    Some((disc, cases))
}

/// Whether an arm of a foldable if-chain contains an unlabeled `break`
/// at case-arm depth — a loop exit that a `switch` wrapper would
/// reinterpret as a switch exit. Nested loops/switches intercept their
/// own breaks, so the walk does not descend into them.
pub(in crate::folds) fn arm_has_loop_break(nodes: &[SNode]) -> bool {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(seq) = stack.pop() {
        for n in seq {
            match n {
                SNode::Break { label: None } => return true,
                SNode::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::Labeled { body, .. } => stack.push(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(f) = finally {
                        stack.push(f);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::While { .. }
                | SNode::DoWhile { .. }
                | SNode::ForOf { .. }
                | SNode::ForIn { .. }
                | SNode::Switch { .. }
                | SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
        }
    }
    false
}

/// The `(discriminant, case-literal)` of a POSITIVE `x === lit`
/// condition. Only the truth-preserving `istrue` wrapper may be
/// stripped — `isfalse`/`!` invert the arms and a `case lit:` body
/// would run on the WRONG polarity (d-P4 dream gate: `x ?? y`'s
/// `isfalse(x === undefined)` chain folded into a switch with the
/// undefined/default arms swapped — local/optional-chain).
pub(in crate::folds) fn switch_test(cond: &Expr) -> Option<(Expr, Expr, bool)> {
    let mut c = cond;
    let mut positive = true;
    loop {
        match c {
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsTrue | abcd_ir::op::UnOp::JumpNez,
                operand,
            } => c = operand,
            Expr::Unary {
                op:
                    abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::JumpEqz
                    | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => {
                positive = !positive;
                c = operand;
            }
            _ => break,
        }
    }
    match c {
        Expr::Compare {
            op: abcd_ir::op::CmpOp::StrictEq | abcd_ir::op::CmpOp::Eq,
            left,
            right,
        } => {
            let is_disc = |e: &Expr| matches!(e, Expr::Temp { .. } | Expr::Ident(_));
            if is_disc(left) && matches!(right.as_ref(), Expr::Lit(_)) {
                Some((left.as_ref().clone(), right.as_ref().clone(), positive))
            } else if is_disc(right) && matches!(left.as_ref(), Expr::Lit(_)) {
                Some((right.as_ref().clone(), left.as_ref().clone(), positive))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Append a `break` to a case body unless it already ends terminal.
pub(in crate::folds) fn with_break(mut body: Vec<SNode>) -> Vec<SNode> {
    let terminal = body.last().is_some_and(crate::structure::is_terminal_node);
    if !terminal {
        body.push(SNode::Break { label: None });
    }
    body
}

// ── d-P8: the finally fold (design/decompile.md §4.2 item 5) ───────
//
// es2abc has no `finally` marker: it duplicates the finally body onto
// every exit path of the protected construct and registers an
// exception DISPATCH handler that runs the finally body once and
// rethrows. d-P3's try machinery emits that faithfully but verbosely:
// a handler-protecting outer `try` (the "finally idiom" note) whose
// catch is a phi dispatch — a switch on a phi temp whose
// `case undefined:` arm holds the finally body, followed by a
// rethrow-unless-hole conditional — plus the finally body inlined
// before every `return`/exiting `break`/`continue` and on the
// normal-completion fall-through path.
//
// This fold recognizes that exact shape and re-factors it into
// `try { … } catch … finally { F }`. The equivalence is the JS
// finally completion semantics: F runs on normal completion, before
// any return/break/continue completes, and on exceptional exit —
// exactly the paths es2abc duplicated F onto. The dispatch's
// `default:` arm (skip F when the exception came from F itself)
// matches the finally clause's run-F-once semantics.
//
// Every check is conservative: any shape doubt keeps the duplicated
// form with its honesty notes (the fallback-honesty rule).

/// A flattened statement-list token for the finally fold: one leaf, or
/// one whole nested node (nested nodes never appear in a foldable
/// finally template, so they never match — conservatism for free).
#[derive(Clone, Debug, PartialEq)]
pub(in crate::folds) enum FTok {
    /// A single statement.
    Leaf(Leaf),
    /// A nested structured node.
    Node(SNode),
}

/// Flatten a statement list to tokens (a `Stmts` run becomes one token
/// per leaf; any other node is one opaque token).
pub(in crate::folds) fn ft_flatten(nodes: &[SNode]) -> Vec<FTok> {
    let mut out = Vec::new();
    for n in nodes {
        match n {
            SNode::Stmts(ls) => out.extend(ls.iter().cloned().map(FTok::Leaf)),
            other => out.push(FTok::Node(other.clone())),
        }
    }
    out
}

/// Regroup tokens into a statement list (consecutive leaves share one
/// `Stmts` node; empty runs are dropped). Semantics-neutral: emission
/// iterates leaves regardless of grouping.
pub(in crate::folds) fn ft_regroup(toks: Vec<FTok>) -> Vec<SNode> {
    let mut out: Vec<SNode> = Vec::new();
    let mut run: Vec<Leaf> = Vec::new();
    for t in toks {
        match t {
            FTok::Leaf(l) => run.push(l),
            FTok::Node(n) => {
                if !run.is_empty() {
                    out.push(SNode::Stmts(std::mem::take(&mut run)));
                }
                out.push(n);
            }
        }
    }
    if !run.is_empty() {
        out.push(SNode::Stmts(run));
    }
    out
}

/// The definition-site names of a token run (first-occurrence order) —
/// the names each duplicated finally copy binds for itself (the
/// legalizer disambiguates the copies: `print$1`/`print$2`/…).
pub(in crate::folds) fn ftok_def_names(toks: &[FTok]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut push = |n: &String| {
        if !out.contains(n) {
            out.push(n.clone());
        }
    };
    for t in toks {
        let FTok::Leaf(l) = t else { continue };
        match l {
            Leaf::Raw(Stmt::Declare { name, .. })
            | Leaf::Raw(Stmt::PhiDecl { name, .. })
            | Leaf::Raw(Stmt::CatchBind { name })
            | Leaf::Decl { name, .. } => push(name),
            Leaf::Destructure { keys, rest, .. } => {
                for (_, target) in keys {
                    push(target);
                }
                push(rest);
            }
            _ => {}
        }
    }
    out
}

/// Rename a temp/ident occurrence when it is one of the run's own
/// definition-site names.
pub(in crate::folds) fn canon_name(
    name: &mut String,
    map: &std::collections::HashMap<String, String>,
) {
    if let Some(r) = map.get(name) {
        *name = r.clone();
    }
}

/// Alpha-rename a run-local name inside an expression and erase the
/// SSA provenance of temp references (copies sit at different SSA
/// values; their NAMES carry the identity).
pub(in crate::folds) fn canon_expr(e: &mut Expr, map: &std::collections::HashMap<String, String>) {
    let mut stack: Vec<&mut Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Temp { value, name } => {
                canon_name(name, map);
                *value = abcd_ir::ValueId::new(0);
            }
            Expr::Ident(name) => canon_name(name, map),
            _ => {}
        }
        for c in expr_children_mut(cur).into_iter().rev() {
            stack.push(c);
        }
    }
}

/// Alpha-rename/provenance-erase one statement.
pub(in crate::folds) fn canon_stmt(s: &mut Stmt, map: &std::collections::HashMap<String, String>) {
    match s {
        Stmt::Declare {
            name,
            value,
            value_id,
            ..
        } => {
            canon_name(name, map);
            canon_expr(value, map);
            *value_id = abcd_ir::ValueId::new(0);
        }
        Stmt::PhiDecl { name, value_id } => {
            canon_name(name, map);
            *value_id = abcd_ir::ValueId::new(0);
        }
        Stmt::PhiAssign {
            target, value, to, ..
        } => {
            canon_name(target, map);
            canon_expr(value, map);
            *to = abcd_ir::BlockId::new(0);
        }
        Stmt::Expr(e) | Stmt::Throw(e) => canon_expr(e, map),
        Stmt::Return(Some(e)) => canon_expr(e, map),
        Stmt::StoreProp { object, value, .. } => {
            canon_expr(object, map);
            canon_expr(value, map);
        }
        Stmt::StoreIndex {
            object,
            index,
            value,
            ..
        } => {
            canon_expr(object, map);
            canon_expr(index, map);
            canon_expr(value, map);
        }
        Stmt::StoreDyn {
            object, key, value, ..
        } => {
            canon_expr(object, map);
            canon_expr(key, map);
            canon_expr(value, map);
        }
        Stmt::DefineMethod { object, func, .. } => {
            canon_expr(object, map);
            canon_expr(func, map);
        }
        Stmt::StorePrivate { object, value, .. } => {
            canon_expr(object, map);
            canon_expr(value, map);
        }
        Stmt::StoreSuper { key, value, .. } => {
            if let Some(k) = key {
                canon_expr(k, map);
            }
            canon_expr(value, map);
        }
        Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => canon_expr(value, map),
        Stmt::CatchBind { name } => canon_name(name, map),
        Stmt::Elided { loc, .. } | Stmt::Fallback { loc, .. } => *loc = None,
        _ => {}
    }
}

/// Alpha-rename/provenance-erase one token.
pub(in crate::folds) fn canon_tok(t: &mut FTok, map: &std::collections::HashMap<String, String>) {
    let FTok::Leaf(l) = t else { return };
    match l {
        Leaf::Raw(s) => canon_stmt(s, map),
        Leaf::Destructure { obj, keys, rest } => {
            canon_expr(obj, map);
            for (_, target) in keys {
                canon_name(target, map);
            }
            canon_name(rest, map);
        }
        Leaf::Decl { name, value, .. } => {
            canon_name(name, map);
            if let Some(v) = value {
                canon_expr(v, map);
            }
        }
        Leaf::Assign { target, value } => {
            canon_name(target, map);
            canon_expr(value, map);
        }
    }
}

/// The canonical form of a token run: run-local definition names
/// replaced by first-occurrence placeholders (`#d0`, `#d1`, …) and SSA
/// provenance erased. Two duplicated finally copies are structurally
/// equal IFF their canonical forms are equal (external names — same
/// SSA temps, same literals — compare verbatim).
pub(in crate::folds) fn ft_canon(toks: &[FTok]) -> Vec<FTok> {
    let mut out = toks.to_vec();
    let map: std::collections::HashMap<String, String> = ftok_def_names(toks)
        .into_iter()
        .enumerate()
        .map(|(i, n)| (n, format!("#d{i}")))
        .collect();
    for t in out.iter_mut() {
        canon_tok(t, &map);
    }
    out
}

/// Bookkeeping-only leaf of the es2abc finally dispatch: phi wiring
/// whose value is a plain temp/identifier/literal copy. Anything
/// effectful (calls, stores, real computation) is NOT bookkeeping.
pub(in crate::folds) fn ft_bookkeeping(l: &Leaf) -> bool {
    let simple = |e: &Expr| matches!(e, Expr::Temp { .. } | Expr::Ident(_) | Expr::Lit(_));
    match l {
        Leaf::Raw(Stmt::PhiDecl { .. })
        | Leaf::Raw(Stmt::Unreachable)
        | Leaf::Raw(Stmt::CatchBind { .. }) => true,
        Leaf::Raw(Stmt::PhiAssign { value, .. }) => simple(value),
        Leaf::Raw(Stmt::Declare { value, .. }) => simple(value),
        _ => false,
    }
}

/// The extracted finally idiom.
pub(in crate::folds) struct FinallyIdiom {
    /// The finally body, as raw tokens (emitted verbatim).
    pub(in crate::folds) body: Vec<FTok>,
    /// Its canonical form (the match template).
    pub(in crate::folds) canon: Vec<FTok>,
    /// The phi declarations the dissolved dispatch owned (re-hoisted
    /// before the folded try so surviving dead phi assigns still
    /// resolve to a `var` — module mode is strict).
    pub(in crate::folds) decls: Vec<Leaf>,
}

/// Extract the finally body from a dispatch-shaped handler body (the
/// outer wrapper's catch): phi bookkeeping + exactly one switch whose
/// `case undefined:` arm holds the finally body (default arm pure
/// bookkeeping) + the rethrow-unless-hole conditional whose thrown
/// temp traces through the copy chain to the catch binding.
pub(in crate::folds) fn ft_extract_dispatch(body: &[SNode], binding: &str) -> Option<FinallyIdiom> {
    let toks = ft_flatten(body);
    let mut switch_idx = None;
    let mut rethrow_idx = None;
    for (i, t) in toks.iter().enumerate() {
        match t {
            FTok::Node(SNode::Switch { .. }) => {
                if switch_idx.is_some() {
                    return None; // one dispatch switch only
                }
                switch_idx = Some(i);
            }
            FTok::Node(SNode::If { .. }) => {
                if rethrow_idx.is_some() {
                    return None; // one rethrow conditional only
                }
                rethrow_idx = Some(i);
            }
            FTok::Leaf(l) if ft_bookkeeping(l) => {}
            _ => return None, // anything else is real handler code
        }
    }
    let si = switch_idx?;
    let ri = rethrow_idx?;
    if ri < si {
        return None; // the rethrow follows the dispatch
    }
    // The dispatch switch: disc is a temp/ident; exactly two cases —
    // `case undefined:` (the finally run arm) and `default:` (pure
    // bookkeeping, no re-run of F — matches run-once semantics).
    let FTok::Node(SNode::Switch { disc, cases }) = &toks[si] else {
        unreachable!()
    };
    temp_name(disc)?;
    if cases.len() != 2 {
        return None;
    }
    let run = cases
        .iter()
        .find(|c| c.tests.len() == 1 && matches!(&c.tests[0], Expr::Lit(Lit::Undefined)))?;
    let default = cases.iter().find(|c| c.tests.is_empty())?;
    let run_toks = ft_flatten(&run.body);
    let default_toks = ft_flatten(&default.body);
    // The default arm: pure bookkeeping plus an optional closing break.
    let default_ok = default_toks.iter().all(|t| match t {
        FTok::Leaf(l) => ft_bookkeeping(l),
        FTok::Node(SNode::Break { label: None }) => true,
        _ => false,
    });
    if !default_ok {
        return None;
    }
    // The run arm: [finally body] [trailing bookkeeping] [break?].
    let mut f_len = run_toks.len();
    while f_len > 0 {
        let bk = match &run_toks[f_len - 1] {
            FTok::Leaf(l) => ft_bookkeeping(l),
            FTok::Node(SNode::Break { label: None }) => true,
            _ => false,
        };
        if bk {
            f_len -= 1;
        } else {
            break;
        }
    }
    let fbody: Vec<FTok> = run_toks[..f_len].to_vec();
    if fbody.is_empty() {
        return None;
    }
    // The template: flat statements only, no control transfers, no
    // nested nodes (v1 conservatism — copies must match leaf-for-leaf).
    let template_ok = fbody.iter().all(|t| match t {
        FTok::Leaf(Leaf::Raw(
            Stmt::Return(_) | Stmt::Throw(_) | Stmt::Branch { .. } | Stmt::CondBranch { .. },
        )) => false,
        FTok::Leaf(_) => true,
        FTok::Node(_) => false,
    });
    if !template_ok {
        return None;
    }
    // The rethrow conditional: `if (!(hole != X)) { return; } else {
    // throw X; }` (either polarity), and X must trace through the
    // bookkeeping copy chain to the catch binding.
    let FTok::Node(SNode::If {
        cond,
        then,
        otherwise,
    }) = &toks[ri]
    else {
        unreachable!()
    };
    let thrown = ft_rethrow_temp(cond, then, otherwise)?;
    // Copy chain: target <- source over all bookkeeping assigns.
    let mut edges: Vec<(String, String)> = Vec::new();
    for t in &toks {
        if let FTok::Leaf(l) = t {
            match l {
                Leaf::Raw(Stmt::PhiAssign { target, value, .. })
                | Leaf::Assign { target, value } => {
                    if let Some(src) = temp_name(value) {
                        edges.push((target.clone(), src.to_string()));
                    }
                }
                Leaf::Raw(Stmt::Declare { name, value, .. }) => {
                    if let Some(src) = temp_name(value) {
                        edges.push((name.clone(), src.to_string()));
                    }
                }
                _ => {}
            }
        }
    }
    // BFS from the thrown temp to the binding.
    let mut frontier = vec![thrown];
    let mut seen = std::collections::HashSet::new();
    let mut reaches = false;
    while let Some(x) = frontier.pop() {
        if x == binding {
            reaches = true;
            break;
        }
        if !seen.insert(x.clone()) {
            continue;
        }
        for (t, s) in &edges {
            if *t == x {
                frontier.push(s.clone());
            }
        }
    }
    if !reaches {
        return None;
    }
    // Hoist the dispatch's phi declarations (dead assigns elsewhere in
    // the function still reference them).
    let decls: Vec<Leaf> = toks
        .iter()
        .filter_map(|t| match t {
            FTok::Leaf(l @ Leaf::Raw(Stmt::PhiDecl { .. })) => Some(l.clone()),
            _ => None,
        })
        .collect();
    let canon = ft_canon(&fbody);
    Some(FinallyIdiom {
        body: fbody,
        canon,
        decls,
    })
}

/// The `(hole != X)` rethrow conditional, either polarity; returns the
/// rethrown temp's name when the shape is `{ return; }` vs `{ throw X; }`.
pub(in crate::folds) fn ft_rethrow_temp(
    cond: &Expr,
    then: &[SNode],
    otherwise: &[SNode],
) -> Option<String> {
    let mut e = cond;
    let mut negated = false;
    loop {
        match e {
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsTrue | abcd_ir::op::UnOp::JumpNez,
                operand,
            } => e = operand,
            Expr::Unary {
                op:
                    abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::JumpEqz
                    | abcd_ir::op::UnOp::LogicalNot,
                operand,
            } => {
                negated = !negated;
                e = operand;
            }
            _ => break,
        }
    }
    let Expr::Compare {
        op: abcd_ir::op::CmpOp::NotEq | abcd_ir::op::CmpOp::StrictNotEq,
        left,
        right,
    } = e
    else {
        return None;
    };
    let x = if matches!(left.as_ref(), Expr::Lit(Lit::Hole)) {
        temp_name(right)?
    } else if matches!(right.as_ref(), Expr::Lit(Lit::Hole)) {
        temp_name(left)?
    } else {
        return None;
    };
    // `!(hole != X)`: then = return, else = throw. Un-negated, swapped.
    let (ret_arm, throw_arm) = if negated {
        (then, otherwise)
    } else {
        (otherwise, then)
    };
    // `Ok(None)` = the return arm is clean; `Ok(Some(name))` = the
    // throw arm rethrows `name`.
    let arm_ok = |arm: &[SNode], want_throw: bool| -> Option<Option<String>> {
        let toks = ft_flatten(arm);
        let mut thrown = None;
        let mut saw_terminal = false;
        for t in &toks {
            match t {
                FTok::Leaf(Leaf::Raw(Stmt::Return(None))) if !want_throw => {
                    saw_terminal = true;
                }
                FTok::Leaf(Leaf::Raw(Stmt::Throw(v))) if want_throw => {
                    thrown = Some(temp_name(v)?.to_string());
                    saw_terminal = true;
                }
                FTok::Leaf(l) if ft_bookkeeping(l) => {}
                _ => return None,
            }
        }
        if !saw_terminal {
            return None;
        }
        Some(thrown)
    };
    arm_ok(ret_arm, false)?;
    let thrown = arm_ok(throw_arm, true)??;
    if thrown != x {
        return None; // the hole-guard and the rethrow must agree
    }
    Some(thrown)
}

/// May this statement list complete normally (fall through to whatever
/// follows)? Conservative: any doubt answers `true` (the fold then
/// REQUIRES the normal-completion finally copy — absence bails).
pub(in crate::folds) fn ft_list_fallthrough(nodes: &[SNode]) -> bool {
    run_ft_steps(FtStep::List(nodes))
}

#[cfg(test)]
pub(in crate::folds) fn ft_node_fallthrough(n: &SNode) -> bool {
    run_ft_steps(FtStep::Node(n))
}

enum FtStep<'a> {
    List(&'a [SNode]),
    Node(&'a SNode),
    All(usize),
    Any(usize),
}

fn run_ft_steps(initial: FtStep<'_>) -> bool {
    let mut steps: Vec<FtStep<'_>> = vec![initial];
    let mut vals: Vec<bool> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            FtStep::List(slice) => {
                if slice.is_empty() {
                    vals.push(true);
                } else {
                    steps.push(FtStep::All(slice.len()));
                    for n in slice.iter().rev() {
                        steps.push(FtStep::Node(n));
                    }
                }
            }
            FtStep::Node(n) => match n {
                SNode::Stmts(ls) => {
                    vals.push(!ls.iter().any(|l| {
                        matches!(
                            l,
                            Leaf::Raw(Stmt::Return(_))
                                | Leaf::Raw(Stmt::Throw(_))
                                | Leaf::Raw(Stmt::Branch { .. })
                                | Leaf::Raw(Stmt::CondBranch { .. })
                        )
                    }));
                }
                SNode::If {
                    then, otherwise, ..
                } => {
                    steps.push(FtStep::All(2));
                    steps.push(FtStep::List(otherwise));
                    steps.push(FtStep::List(then));
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    // An exceptional path is not a NORMAL completion; a
                    // finally clause runs either way and changes nothing.
                    let _ = finally;
                    if catches.is_empty() {
                        steps.push(FtStep::List(body));
                    } else {
                        steps.push(FtStep::Any(1 + catches.len()));
                        for c in catches.iter().rev() {
                            steps.push(FtStep::List(&c.body));
                        }
                        steps.push(FtStep::List(body));
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } => vals.push(false),
                // Loops, switches, labeled blocks, honesty comments: may
                // complete (a loop can break out, a comment says nothing).
                SNode::While { .. }
                | SNode::DoWhile { .. }
                | SNode::ForOf { .. }
                | SNode::ForIn { .. }
                | SNode::Switch { .. }
                | SNode::Labeled { .. }
                | SNode::Honest(_) => vals.push(true),
            },
            FtStep::All(k) => {
                let start = vals.len().saturating_sub(k);
                let r = vals.drain(start..).all(|x| x);
                vals.push(r);
            }
            FtStep::Any(k) => {
                let start = vals.len().saturating_sub(k);
                let r = vals.drain(start..).any(|x| x);
                vals.push(r);
            }
        }
    }
    vals.pop().unwrap_or(true)
}

/// Loop/switch nesting context for exit classification within the
/// protected construct C (a `break`/`continue` intercepted INSIDE C
/// needs no finally copy; one leaving C does).
#[derive(Clone, Copy)]
pub(in crate::folds) struct FtCtx {
    /// Enclosing loops within C.
    pub(in crate::folds) loops: usize,
    /// Enclosing loops + switches within C.
    pub(in crate::folds) breakables: usize,
}

fn take_ft_child(
    n: &mut SNode,
    slot: usize,
    ctx: FtCtx,
) -> Option<(Vec<SNode>, FtCtx, Option<String>)> {
    match n {
        SNode::If {
            then, otherwise, ..
        } => match slot {
            0 => Some((std::mem::take(then), ctx, None)),
            1 => Some((std::mem::take(otherwise), ctx, None)),
            _ => None,
        },
        SNode::While { label, body, .. } | SNode::DoWhile { label, body, .. } => {
            (slot == 0).then(|| {
                (
                    std::mem::take(body),
                    FtCtx {
                        loops: ctx.loops + 1,
                        breakables: ctx.breakables + 1,
                    },
                    label.clone(),
                )
            })
        }
        SNode::ForOf { body, .. } | SNode::ForIn { body, .. } => (slot == 0).then(|| {
            (
                std::mem::take(body),
                FtCtx {
                    loops: ctx.loops + 1,
                    breakables: ctx.breakables + 1,
                },
                None,
            )
        }),
        SNode::Switch { cases, .. } => cases.get_mut(slot).map(|c| {
            (
                std::mem::take(&mut c.body),
                FtCtx {
                    loops: ctx.loops,
                    breakables: ctx.breakables + 1,
                },
                None,
            )
        }),
        SNode::Labeled { label, body } => {
            (slot == 0).then(|| (std::mem::take(body), ctx, Some(label.clone())))
        }
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            if slot == 0 {
                Some((std::mem::take(body), ctx, None))
            } else if slot <= catches.len() {
                Some((std::mem::take(&mut catches[slot - 1].body), ctx, None))
            } else if slot == 1 + catches.len() {
                finally.as_mut().map(|f| (std::mem::take(f), ctx, None))
            } else {
                None
            }
        }
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => None,
    }
}

fn put_ft_child(n: &mut SNode, slot: usize, child: Vec<SNode>) {
    match n {
        SNode::If {
            then, otherwise, ..
        } => match slot {
            0 => *then = child,
            1 => *otherwise = child,
            _ => {}
        },
        SNode::While { body, .. }
        | SNode::DoWhile { body, .. }
        | SNode::ForOf { body, .. }
        | SNode::ForIn { body, .. }
        | SNode::Labeled { body, .. } => {
            if slot == 0 {
                *body = child;
            }
        }
        SNode::Switch { cases, .. } => {
            if let Some(c) = cases.get_mut(slot) {
                c.body = child;
            }
        }
        SNode::Try {
            body,
            catches,
            finally,
            ..
        } => {
            if slot == 0 {
                *body = child;
            } else if slot <= catches.len() {
                catches[slot - 1].body = child;
            } else if slot == 1 + catches.len()
                && let Some(f) = finally
            {
                *f = child;
            }
        }
        SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
    }
}

fn ft_strip_exits_flat(
    nodes: &mut Vec<SNode>,
    idiom: &FinallyIdiom,
    ctx: FtCtx,
    labels: &[String],
    strips: &mut usize,
) -> Result<(), ()> {
    let k = idiom.canon.len();
    let toks = ft_flatten(nodes);
    let mut remove: Vec<usize> = Vec::new();
    for j in 0..toks.len() {
        let needs = match &toks[j] {
            FTok::Leaf(Leaf::Raw(Stmt::Return(_))) => true,
            FTok::Node(SNode::Break { label }) => match label {
                None => ctx.breakables == 0,
                Some(l) => !labels.contains(l),
            },
            FTok::Node(SNode::Continue { label }) => match label {
                None => ctx.loops == 0,
                Some(l) => !labels.contains(l),
            },
            _ => false,
        };
        if !needs {
            continue;
        }
        if j < k {
            return Err(());
        }
        let cand = &toks[j - k..j];
        if ft_canon(cand) != idiom.canon {
            return Err(());
        }
        if let FTok::Leaf(Leaf::Raw(Stmt::Return(Some(v)))) = &toks[j] {
            let mut assigned: Vec<&str> = Vec::new();
            for t in cand {
                if let FTok::Leaf(
                    Leaf::Raw(Stmt::PhiAssign { target, .. }) | Leaf::Assign { target, .. },
                ) = t
                {
                    assigned.push(target);
                }
            }
            if assigned.iter().any(|n| expr_uses_name(v, n)) {
                return Err(());
            }
        }
        remove.extend(j - k..j);
        *strips += 1;
    }
    if remove.is_empty() {
        return Ok(());
    }
    let kept: Vec<FTok> = toks
        .into_iter()
        .enumerate()
        .filter_map(|(i, t)| (!remove.contains(&i)).then_some(t))
        .collect();
    *nodes = ft_regroup(kept);
    Ok(())
}

/// Strip the inlined finally copies preceding every exit of the
/// protected construct. `Err(())` = an exit without its copy — the
/// fold bails and the duplicated form stays (honesty rule).
pub(in crate::folds) fn ft_strip_exits(
    nodes: &mut Vec<SNode>,
    idiom: &FinallyIdiom,
    ctx: FtCtx,
    labels: &mut Vec<String>,
    strips: &mut usize,
) -> Result<(), ()> {
    struct Frame {
        seq: Vec<SNode>,
        idx: usize,
        next_slot: usize,
        has_detached_child: bool,
        ctx: FtCtx,
        pop_label: bool,
    }

    let mut stack = vec![Frame {
        seq: std::mem::take(nodes),
        idx: 0,
        next_slot: 0,
        has_detached_child: false,
        ctx,
        pop_label: false,
    }];
    let mut completed_child: Option<Vec<SNode>> = None;

    while let Some(top) = stack.last_mut() {
        if let Some(child_seq) = completed_child.take() {
            put_ft_child(&mut top.seq[top.idx], top.next_slot - 1, child_seq);
            top.has_detached_child = false;
        }
        if top.idx < top.seq.len() {
            let slot = top.next_slot;
            if let Some((child_seq, child_ctx, push_lbl)) =
                take_ft_child(&mut top.seq[top.idx], slot, top.ctx)
            {
                top.next_slot = slot + 1;
                top.has_detached_child = true;
                let pop_label = push_lbl.is_some();
                if let Some(l) = push_lbl {
                    labels.push(l);
                }
                stack.push(Frame {
                    seq: child_seq,
                    idx: 0,
                    next_slot: 0,
                    has_detached_child: false,
                    ctx: child_ctx,
                    pop_label,
                });
            } else {
                top.idx += 1;
                top.next_slot = 0;
            }
            continue;
        }

        let res = ft_strip_exits_flat(&mut top.seq, idiom, top.ctx, labels, strips);
        if res.is_err() {
            while stack.len() > 1 {
                let Some(child_frame) = stack.pop() else {
                    break;
                };
                if child_frame.pop_label {
                    labels.pop();
                }
                if let Some(parent) = stack.last_mut()
                    && parent.has_detached_child
                {
                    put_ft_child(
                        &mut parent.seq[parent.idx],
                        parent.next_slot - 1,
                        child_frame.seq,
                    );
                    parent.has_detached_child = false;
                }
            }
            if let Some(root) = stack.pop() {
                *nodes = root.seq;
            }
            return Err(());
        }

        let Some(done) = stack.pop() else {
            break;
        };
        if done.pop_label {
            labels.pop();
        }
        if stack.is_empty() {
            *nodes = done.seq;
            return Ok(());
        }
        completed_child = Some(done.seq);
    }
    Ok(())
}

/// Attempt the finally fold at `nodes[i]` (a handler-protecting outer
/// try carrying the "finally idiom" note). Returns the replacement for
/// `nodes[i..]` on success — the fold may also consume the
/// normal-completion finally copy in the following siblings.
pub(in crate::folds) fn ft_fold_at(nodes: &[SNode], i: usize) -> Option<Vec<SNode>> {
    let SNode::Try {
        body,
        catches,
        note,
        finally: None,
    } = &nodes[i]
    else {
        return None;
    };
    if !note.as_deref().is_some_and(|n| n.contains("finally idiom")) {
        return None;
    }
    if catches.len() != 1 {
        return None;
    }
    let binding = catches[0].binding.clone()?;
    let idiom = ft_extract_dispatch(&catches[0].body, &binding)?;

    // Strip the inlined copies inside the protected construct.
    let mut stripped_body = body.clone();
    let mut labels: Vec<String> = Vec::new();
    let mut strips = 0usize;
    ft_strip_exits(
        &mut stripped_body,
        &idiom,
        FtCtx {
            loops: 0,
            breakables: 0,
        },
        &mut labels,
        &mut strips,
    )
    .ok()?;

    // Unwrap a sole inner try/catch: `try { try{A} catch{B} } finally{F}`
    // reads as `try { A } catch { B } finally { F }`.
    let inner_try = if stripped_body.len() == 1
        && matches!(
            &stripped_body[0],
            SNode::Try {
                finally: None,
                catches,
                ..
            } if !catches.is_empty()
        ) {
        match stripped_body.pop() {
            Some(SNode::Try {
                body: ref mut ibody,
                catches: ref mut icatches,
                note: ref mut inote,
                finally: None,
            }) => Some((
                std::mem::take(ibody),
                std::mem::take(icatches),
                inote.take(),
            )),
            _ => None,
        }
    } else {
        None
    };
    let (folded_try, construct_ft) = if let Some((ibody, icatches, inote)) = inner_try {
        let ft =
            ft_list_fallthrough(&ibody) || icatches.iter().any(|c| ft_list_fallthrough(&c.body));
        (
            SNode::Try {
                body: ibody,
                catches: icatches,
                note: inote,
                finally: Some(ft_regroup(idiom.body.clone())),
            },
            ft,
        )
    } else {
        let ft = ft_list_fallthrough(&stripped_body);
        (
            SNode::Try {
                body: stripped_body,
                catches: Vec::new(),
                note: None,
                finally: Some(ft_regroup(idiom.body.clone())),
            },
            ft,
        )
    };

    // The normal-completion copy: when the construct can fall through,
    // es2abc placed its finally copy right after the protected span —
    // the immediately following siblings. Consume it, or bail.
    let mut tail = ft_flatten(&nodes[i + 1..]);
    if construct_ft {
        if tail.len() < idiom.canon.len() || ft_canon(&tail[..idiom.canon.len()]) != idiom.canon {
            return None;
        }
        tail.drain(..idiom.canon.len());
    }

    let mut out: Vec<SNode> = Vec::new();
    if !idiom.decls.is_empty() {
        out.push(SNode::Stmts(idiom.decls.clone()));
    }
    out.push(SNode::Honest(format!(
        "finally recovered from es2abc's duplicated-finally idiom (the dispatch handler was finally+rethrow; {strips} inlined copy/copies folded)"
    )));
    out.push(folded_try);
    out.extend(ft_regroup(tail));
    Some(out)
}

/// The finally fold driver over one statement list.
pub(in crate::folds) fn fold_finally(nodes: &mut Vec<SNode>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < nodes.len() {
        let idiom = matches!(
            &nodes[i],
            SNode::Try {
                note: Some(n),
                catches,
                finally: None,
                ..
            } if n.contains("finally idiom") && catches.len() == 1
        );
        if idiom && let Some(replacement) = ft_fold_at(nodes, i) {
            nodes.splice(i.., replacement);
            stats.finally_fold += 1;
            // Do not advance: the replacement's own nested trys were
            // already folded by the children-first recursion.
            continue;
        }
        i += 1;
    }
}
