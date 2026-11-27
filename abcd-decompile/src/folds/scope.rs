//! Lexical slot scope reconstruction, TDZ-preserving late declarations, and rest parameters.

use super::*;

// ── d-P8: LexStore scope reconstruction (design §4.3 "Names") ──────
//
// v1 (d-P4) printed every lexical binding as a function-top `let n;`
// plus plain `n = value;` assignments, with `/* scope-push […] */`
// comments marking the `NewLexEnv*` sites. This fold reconstructs the
// declaration site where provable: es2abc initializes a pushed frame's
// slots with `stlexvar 0, slot` IMMEDIATELY after the push (the TDZ
// hole + the elided `ThrowUndefinedIfHoleWithName` guard prove every
// read is post-init), so the first store to a slot right after its
// push IS the source's `let` declaration.
//
// Provable means ALL of:
//   - the store sits in the same statement run as the push, at level 0
//     (the just-pushed frame), with a slot index inside the frame;
//   - every store to the same NAME anywhere in the function lives in
//     that same run after the push (a store elsewhere would become an
//     assignment to a binding the block declaration does not cover);
//   - the name is not a parameter (redeclaration is a SyntaxError) and
//     was not already block-declared by this fold (same-named frames
//     stay comments + plain assignments — the honesty rule).
//
// `const` is deliberately NOT inferred: a capturing closure can
// reassign the slot from a nested function body (cross-function proof
// is out of scope) — declarations are uniformly `let`.
//
// Where the shape is unprovable the `/* scope-push […] */` comment and
// the plain assignments stay, unchanged.

/// One LexStore occurrence: which `Stmts` run (walk order) and leaf.
pub(in crate::folds) struct LexStoreSite {
    /// The run's walk-order id.
    pub(in crate::folds) run: usize,
    /// The leaf index within the run.
    pub(in crate::folds) index: usize,
}

/// Reconstruct block-scoped declarations at provable lexenv push
/// sites and balanced `ScopePush`..`ScopePop` lexical blocks.
/// Runs AFTER the desugar folds (it consumes their output).
pub fn scope_fold(nodes: &mut Vec<SNode>, params: &[String], stats: &mut FoldStats) {
    wrap_lexical_scope_blocks(nodes, params, stats);

    // Pass 1: census of every LexStore name → its sites.
    let mut runs = 0usize;
    let mut stores: std::collections::HashMap<String, Vec<LexStoreSite>> =
        std::collections::HashMap::new();
    let mut cstack: Vec<&[SNode]> = vec![nodes.as_slice()];
    while let Some(seq) = cstack.pop() {
        let Some((first, rest)) = seq.split_first() else {
            continue;
        };
        if !rest.is_empty() {
            cstack.push(rest);
        }
        match first {
            SNode::Stmts(leaves) => {
                let run = runs;
                runs += 1;
                for (index, l) in leaves.iter().enumerate() {
                    if let Leaf::Raw(Stmt::LexStore { name, .. }) = l {
                        stores
                            .entry(name.clone())
                            .or_default()
                            .push(LexStoreSite { run, index });
                    }
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                cstack.push(otherwise);
                cstack.push(then);
            }
            SNode::Block(body)
            | SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::Labeled { body, .. }
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. } => cstack.push(body),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                if let Some(f) = finally {
                    cstack.push(f);
                }
                for c in catches.iter().rev() {
                    cstack.push(&c.body);
                }
                cstack.push(body);
            }
            SNode::Switch { cases, .. } => {
                for c in cases.iter().rev() {
                    cstack.push(&c.body);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }

    // Pass 2: convert the provable initializations.
    let mut converted: std::collections::HashSet<String> = std::collections::HashSet::new();
    #[allow(
        clippy::too_many_arguments,
        reason = "per-run scope conversion threads run id, store table, params, converted set, and stats"
    )]
    fn convert_run(
        leaves: &mut Vec<Leaf>,
        run: usize,
        stores: &std::collections::HashMap<String, Vec<LexStoreSite>>,
        params: &[String],
        converted: &mut std::collections::HashSet<String>,
        stats: &mut FoldStats,
    ) {
        let mut push_at: Vec<usize> = Vec::new();
        for (i, l) in leaves.iter().enumerate() {
            if matches!(l, Leaf::Raw(Stmt::ScopePush { .. })) {
                push_at.push(i);
            }
        }
        // Apply edits back-to-front so indices stay valid.
        for &p in push_at.iter().rev() {
            let Leaf::Raw(Stmt::ScopePush { names }) = &leaves[p] else {
                unreachable!()
            };
            let slot_count = names.len();
            // The immediate initialization run: level-0 slot stores
            // (re-stores of already-initialized slots, elided-guard
            // markers, and honesty comments may interleave).
            let mut inits: Vec<(usize, u16)> = Vec::new(); // (leaf index, slot)
            let mut j = p + 1;
            while j < leaves.len() {
                match &leaves[j] {
                    Leaf::Raw(Stmt::LexStore {
                        level,
                        slot,
                        own: true,
                        ..
                    }) if *level == 0 && (*slot as usize) < slot_count => {
                        if inits.iter().any(|&(_, s)| s == *slot) {
                            // A re-store of an initialized slot ends the
                            // initialization run (conservative).
                            break;
                        }
                        inits.push((j, *slot));
                        j += 1;
                    }
                    Leaf::Raw(Stmt::Elided { .. } | Stmt::Fallback { .. }) => {
                        j += 1;
                    }
                    _ => break,
                }
            }
            if inits.is_empty() {
                continue;
            }
            // Which inits are provable declarations?
            let mut declared_slots: Vec<u16> = Vec::new();
            let mut decl_edits: Vec<(usize, Leaf)> = Vec::new();
            for &(idx, slot) in &inits {
                let Leaf::Raw(Stmt::LexStore { name, .. }) = &leaves[idx] else {
                    unreachable!()
                };
                let name = name.clone();
                if params.contains(&name) || converted.contains(&name) {
                    continue;
                }
                // Same-name slots within this push: only the first may
                // become a declaration (a second `let n` in one scope is
                // a SyntaxError).
                if decl_edits.iter().any(|(_, l)| {
                    matches!(l, Leaf::Decl { name: dn, .. } if *dn == crate::legalize::sanitize(&name))
                }) {
                    continue;
                }
                // Every store to this name must live in THIS run after
                // the push (else the block declaration would not cover
                // it — strict-mode ReferenceError, or a shadowed
                // binding).
                let ok = stores
                    .get(&name)
                    .into_iter()
                    .flatten()
                    .all(|s| s.run == run && s.index > p);
                if !ok {
                    continue;
                }
                let Leaf::Raw(Stmt::LexStore { value, .. }) = &leaves[idx] else {
                    unreachable!()
                };
                decl_edits.push((
                    idx,
                    Leaf::Decl {
                        name: crate::legalize::sanitize(&name),
                        mutable: true,
                        value: Some(value.clone()),
                    },
                ));
                declared_slots.push(slot);
                converted.insert(name);
            }
            if decl_edits.is_empty() {
                continue;
            }
            let mut declared_raw: Vec<String> = Vec::new();
            for (idx, leaf) in decl_edits {
                if let Leaf::Decl { name, .. } = &leaf {
                    declared_raw.push(name.clone());
                }
                leaves[idx] = leaf;
                stats.scope_fold += 1;
            }
            // The name's OTHER stores in this run (the `ok` check above
            // proved they all live here, after the push) print as plain
            // assignments — but left as raw `LexStore` leaves they still
            // count toward emit's hoisted `lex_decls` whenever the push
            // comment survives (an unprovable sibling slot keeps
            // `own > level`), printing a second `let n;` at the function
            // top — a same-scope redeclaration (SyntaxError in strict/module
            // JS). Rewrite them to plain assignment leaves so the
            // block declaration is the ONLY declaration of the name.
            for l in leaves.iter_mut().skip(p + 1) {
                if let Leaf::Raw(Stmt::LexStore { name, value, .. }) = l
                    && declared_raw
                        .iter()
                        .any(|d| *d == crate::legalize::sanitize(name))
                {
                    *l = Leaf::Assign {
                        target: crate::legalize::sanitize(name),
                        value: value.clone(),
                    };
                }
            }
            // The push comment: consumed when every slot was declared;
            // otherwise it stays, listing the undeclared slots only.
            let Leaf::Raw(Stmt::ScopePush { names }) = &mut leaves[p] else {
                unreachable!()
            };
            let remaining: Vec<Option<String>> = names
                .iter()
                .enumerate()
                .filter(|&(i, _)| !declared_slots.contains(&(i as u16)))
                .map(|(_, n)| n.clone())
                .collect();
            if remaining.is_empty() {
                // Back-to-front push processing makes removal safe.
                leaves.remove(p);
            } else {
                *names = remaining;
            }
        }
    }
    let mut runs = 0usize;
    walk_stmts_runs_mut(nodes, |leaves| {
        let run = runs;
        runs += 1;
        convert_run(leaves, run, &stores, params, &mut converted, stats);
    });
}

/// Wrap balanced `ScopePush` .. `ScopePop` spans into `SNode::Block` scopes
/// with local `let` declarations (e.g. per-iteration loop `let` closures and
/// sibling lexical blocks), unwrapping redundant single-block bodies whose
/// parent construct already introduces a JS block scope.
fn wrap_lexical_scope_blocks(nodes: &mut Vec<SNode>, params: &[String], stats: &mut FoldStats) {
    fold_snode_vecs_postorder(nodes, |seq| wrap_seq_scopes(seq, params, stats));
    unwrap_redundant_single_blocks(nodes);
}

fn seq_has_push_and_pop_markers(seq: &[SNode]) -> bool {
    let mut saw_push = false;
    for n in seq {
        if let SNode::Stmts(leaves) = n {
            for l in leaves {
                match l {
                    Leaf::Raw(Stmt::ScopePush { .. }) => saw_push = true,
                    Leaf::Raw(Stmt::ScopePop) if saw_push => return true,
                    _ => {}
                }
            }
        }
    }
    false
}

fn split_seq_at_scope_markers(seq: Vec<SNode>) -> Vec<SNode> {
    let mut out = Vec::with_capacity(seq.len());
    for mut n in seq {
        if let SNode::Stmts(leaves) = &mut n
            && leaves
                .iter()
                .any(|l| matches!(l, Leaf::Raw(Stmt::ScopePush { .. } | Stmt::ScopePop)))
        {
            let taken = std::mem::take(leaves);
            let mut cur = Vec::new();
            for l in taken {
                if matches!(l, Leaf::Raw(Stmt::ScopePush { .. } | Stmt::ScopePop)) {
                    if !cur.is_empty() {
                        out.push(SNode::Stmts(std::mem::take(&mut cur)));
                    }
                    out.push(SNode::Stmts(vec![l]));
                } else {
                    cur.push(l);
                }
            }
            if !cur.is_empty() {
                out.push(SNode::Stmts(cur));
            }
        } else {
            out.push(n);
        }
    }
    out
}

fn leaves_tail_diverges(tail: &[Leaf]) -> bool {
    tail.iter().any(|l| {
        matches!(
            l,
            Leaf::Raw(Stmt::Return(_) | Stmt::Throw(_) | Stmt::Unreachable)
        )
    })
}

fn slice_diverges_after(nodes: &[SNode]) -> bool {
    for n in nodes {
        if crate::structure::is_terminal_node(n) {
            return true;
        }
        if let SNode::Stmts(ls) = n
            && leaves_tail_diverges(ls)
        {
            return true;
        }
    }
    false
}

/// Verify that compound subtrees inside `span` contain no unwrapped `ScopePush`
/// and that any nested `ScopePop` occurs only on a diverging early-exit path.
fn subtrees_valid_for_scope_wrap(span: &[SNode]) -> bool {
    let mut stack: Vec<&[SNode]> = Vec::new();
    for n in span {
        match n {
            SNode::Stmts(_) | SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
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
        }
    }
    while let Some(slice) = stack.pop() {
        for (ni, n) in slice.iter().enumerate() {
            match n {
                SNode::Stmts(leaves) => {
                    for (li, l) in leaves.iter().enumerate() {
                        match l {
                            Leaf::Raw(Stmt::ScopePush { .. }) => return false,
                            Leaf::Raw(Stmt::ScopePop) => {
                                let diverges = leaves_tail_diverges(&leaves[li + 1..])
                                    || slice_diverges_after(&slice[ni + 1..]);
                                if !diverges {
                                    return false;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                SNode::Block(_) => {
                    // Already-wrapped inner blocks adjusted their internal
                    // LexStore levels; inspect their leaves only for raw
                    // unwrapped ScopePush/ScopePop leaks.
                    if let SNode::Block(body) = n {
                        stack.push(body);
                    }
                }
                SNode::While { body, .. }
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
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    true
}

fn nodes_contain_closure(nodes: &[SNode]) -> bool {
    let mut found = false;
    walk_leaves(nodes, &mut |l| {
        if found {
            return;
        }
        for e in leaf_exprs(l) {
            let mut estack = vec![e];
            while let Some(cur) = estack.pop() {
                if matches!(cur, Expr::Closure { .. }) {
                    found = true;
                    return;
                }
                estack.extend(expr_children(cur));
            }
        }
    });
    found
}

fn wrap_seq_scopes(seq: &mut Vec<SNode>, params: &[String], stats: &mut FoldStats) {
    if !seq_has_push_and_pop_markers(seq) {
        return;
    }
    let mut work = split_seq_at_scope_markers(std::mem::take(seq));
    let mut wrapped_any = false;
    let mut blocked_pushes: BTreeSet<usize> = BTreeSet::new();

    loop {
        let mut candidate: Option<(usize, usize)> = None;
        let mut last_open: Option<usize> = None;
        for (idx, n) in work.iter().enumerate() {
            if let SNode::Stmts(ls) = n
                && ls.len() == 1
            {
                match &ls[0] {
                    Leaf::Raw(Stmt::ScopePush { .. }) => {
                        if !blocked_pushes.contains(&idx) {
                            last_open = Some(idx);
                        } else {
                            last_open = None;
                        }
                    }
                    Leaf::Raw(Stmt::ScopePop) => {
                        if let Some(p_idx) = last_open.take() {
                            candidate = Some((p_idx, idx));
                            break;
                        }
                    }
                    _ => {}
                }
            }
        }
        let Some((p_idx, q_idx)) = candidate else {
            break;
        };
        let push_names: Vec<Option<String>> = match &work[p_idx] {
            SNode::Stmts(ls) => match &ls[0] {
                Leaf::Raw(Stmt::ScopePush { names }) => names.clone(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        let span = &work[p_idx + 1..q_idx];
        if !subtrees_valid_for_scope_wrap(span) {
            blocked_pushes.insert(p_idx);
            continue;
        }

        let has_closure = nodes_contain_closure(span);
        let slot_count = push_names.len();
        let mut slot_idents: Vec<Option<String>> = push_names
            .iter()
            .map(|opt| opt.as_deref().map(crate::legalize::sanitize))
            .collect();
        let mut saw_own_level0 = false;
        let mut ok = true;

        walk_leaves(span, &mut |l| {
            if !ok {
                return;
            }
            if let Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot,
                own: true,
                name,
                ..
            }) = l
            {
                let s = *slot as usize;
                if s >= slot_count {
                    ok = false;
                    return;
                }
                saw_own_level0 = true;
                let san = crate::legalize::sanitize(name);
                match &slot_idents[s] {
                    Some(existing) if existing != &san => {
                        ok = false;
                    }
                    None => {
                        if has_closure {
                            ok = false;
                        } else {
                            slot_idents[s] = Some(san);
                        }
                    }
                    Some(_) => {}
                }
            }
        });

        if !ok || !saw_own_level0 {
            blocked_pushes.insert(p_idx);
            continue;
        }
        // If any unnamed slot has no store and a closure exists inside, bail
        // so module-top G1 orphan fallback stays intact.
        if has_closure && slot_idents.iter().any(Option::is_none) {
            blocked_pushes.insert(p_idx);
            continue;
        }

        let mut seen_names = BTreeSet::new();
        for sname in slot_idents.iter().flatten() {
            if params.contains(sname)
                || matches!(sname.as_str(), "undefined" | "NaN" | "Infinity")
                || !seen_names.insert(sname.clone())
            {
                ok = false;
                break;
            }
        }
        if !ok {
            blocked_pushes.insert(p_idx);
            continue;
        }

        wrapped_any = true;
        blocked_pushes.clear();
        let mut drained: Vec<SNode> = work.drain(p_idx..=q_idx).collect();
        // Remove opening `ScopePush` and closing `ScopePop`.
        drained.pop();
        drained.remove(0);

        // Strip early-exit `ScopePop`s inside `drained` and drop empty runs.
        fold_snode_vecs_postorder(&mut drained, |s| {
            s.retain_mut(|n| match n {
                SNode::Stmts(ls) => {
                    ls.retain(|l| !matches!(l, Leaf::Raw(Stmt::ScopePop)));
                    !ls.is_empty()
                }
                _ => true,
            });
        });

        // Convert leading immediate `level == 0, own == true` initializers in
        // place when RHS does not self-reference the binding (avoiding TDZ).
        let mut declared_slots = vec![false; slot_count];
        if let Some(SNode::Stmts(first_leaves)) = drained.first_mut() {
            for l in first_leaves.iter_mut() {
                match l {
                    Leaf::Raw(Stmt::LexStore {
                        level: 0,
                        slot,
                        own: true,
                        name,
                        value,
                    }) => {
                        let s = *slot as usize;
                        if declared_slots[s] {
                            break;
                        }
                        let san = crate::legalize::sanitize(name);
                        if expr_uses_name(value, &san) {
                            break;
                        }
                        let val = value.clone();
                        *l = Leaf::Decl {
                            name: san,
                            mutable: true,
                            value: Some(val),
                        };
                        declared_slots[s] = true;
                    }
                    Leaf::Raw(Stmt::Elided { .. } | Stmt::Fallback { .. }) => {}
                    _ => break,
                }
            }
        }

        let mut prelude_decls = Vec::new();
        let mut num_decls = declared_slots.iter().filter(|&&d| d).count();
        for (s, maybe_ident) in slot_idents.iter().enumerate() {
            if !declared_slots[s]
                && let Some(ident_name) = maybe_ident
            {
                prelude_decls.push(Leaf::Decl {
                    name: ident_name.clone(),
                    mutable: true,
                    value: None,
                });
                num_decls += 1;
            }
        }
        if !prelude_decls.is_empty() {
            match drained.first_mut() {
                Some(SNode::Stmts(first_leaves)) => {
                    prelude_decls.append(first_leaves);
                    *first_leaves = prelude_decls;
                }
                _ => drained.insert(0, SNode::Stmts(prelude_decls)),
            }
        }

        // Rewrite remaining `level == 0, own == true` LexStores to Assign, and
        // shift outer `level > 0, own == true` LexStores down by 1.
        walk_stmts_runs_mut(&mut drained, |leaves| {
            for l in leaves.iter_mut() {
                if let Leaf::Raw(Stmt::LexStore {
                    level,
                    own: true,
                    name,
                    value,
                    ..
                }) = l
                {
                    if *level == 0 {
                        let san = crate::legalize::sanitize(name);
                        let val = value.clone();
                        *l = Leaf::Assign {
                            target: san,
                            value: val,
                        };
                    } else {
                        *level -= 1;
                    }
                }
            }
        });

        stats.scope_fold += num_decls;
        work.insert(p_idx, SNode::Block(drained));
    }

    let _ = wrapped_any;
    let mut merged: Vec<SNode> = Vec::with_capacity(work.len());
    for mut n in work {
        if let (Some(SNode::Stmts(prev)), SNode::Stmts(next)) = (merged.last_mut(), &mut n) {
            prev.append(next);
        } else {
            merged.push(n);
        }
    }
    *seq = merged;
}

fn unwrap_single_block_vec(v: &mut Vec<SNode>) {
    while v.len() == 1 && matches!(v[0], SNode::Block(_)) {
        if let SNode::Block(inner) = &mut v[0] {
            let extracted = std::mem::take(inner);
            *v = extracted;
        }
    }
}

fn unwrap_redundant_single_blocks(root: &mut Vec<SNode>) {
    fold_snode_vecs_postorder(root, |seq| {
        for n in seq.iter_mut() {
            match n {
                SNode::Block(body) => unwrap_single_block_vec(body),
                SNode::If {
                    then, otherwise, ..
                } => {
                    unwrap_single_block_vec(then);
                    unwrap_single_block_vec(otherwise);
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => unwrap_single_block_vec(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    unwrap_single_block_vec(body);
                    for c in catches {
                        unwrap_single_block_vec(&mut c.body);
                    }
                    if let Some(fin) = finally {
                        unwrap_single_block_vec(fin);
                    }
                }
                SNode::Switch { .. }
                | SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
        }
    });
    unwrap_single_block_vec(root);
}

// ── N74-W4: late declaration-site reconstruction (TDZ honesty) ─────
//
// The v1 scope model hoists every lexical/global binding: `let n;`
// from emit's `lex_decls`, `var g;` at module top for global stores
// (es2abc compiles function bodies STRICT — an undeclared STORE is a
// ReferenceError, so the hoist cannot simply be dropped). Hoisting is
// sound for value flow but DESTROYS the initialization window: a read
// or closure call between scope entry and the first store sees
// `undefined` where the original program's binding was still the TDZ
// hole (lexical: `ldlexvar` + `ThrowUndefinedIfHoleWithName` →
// ReferenceError) or did not exist at all (sloppy global:
// undeclared-read ReferenceError). test262's `*-before-initialization`
// rows and the "undeclared variable" operator rows (`x > (x = 1)`)
// observe exactly this window.
//
// This fold reconstructs the window when it is PROVABLY faithful: the
// binding's textually first store sits in a DECLARATION-CAPABLE run —
// the function body's root statement run, or the root run of a `try`
// BODY (a try body executes unconditionally up to the first throw, and
// block-scope is safe there only when nothing references the name
// outside that try body — checked). The first store becomes
// `let n = <value>;` at that exact position; all other stores become
// plain assignments; the hoisted `let n;` vanishes because
// `lex_decls` only counts remaining `LexStore` leaves (the module-top
// `var g;` stays — a function-scope `let` legally shadows it, and the
// shadow IS the binding every in-function reference resolves to).
// Every access executing before the declaration line then hits the JS
// TDZ — the same ReferenceError the original program produced — and
// every access after sees the stored value. Stores in nested functions
// are capture-assignments to the same binding and stay assignments
// (each function body is folded separately; their stores fail the
// level/ownership check).
//
// Provable means ALL of:
//   - the name is stored by exactly one KIND of store (lexical or
//     global — a mix means the scope model is inconsistent);
//   - for lexical stores, every store targets an OWN frame slot
//     (level < own-push count, the `lex_decls` rule) — a capture store
//     at level ≥ own belongs to an ancestor's binding;
//   - global stores convert only at the TOP LEVEL (a `let` inside a
//     nested function would shadow the global — dream gate:
//     params-dflt-gen-meth's `callCount` died to exactly that);
//   - the textually first store sits in a declaration-capable run, and
//     when that run is inside a `try` body, NO reference to the name
//     exists outside that try body (an outside reference would
//     silently read the module-top `var` instead);
//   - the name is not a parameter, was not already declared by
//     [`scope_fold`], and is not a read-only global name
//     (`undefined`/`NaN`/`Infinity` — the read-only-global collision
//     lane owns those).
//
// Where the shape is unprovable the hoisted-`let`/hoisted-`var`
// emission stays, unchanged (the honesty rule).

/// One store occurrence for the late-decl fold.
pub(in crate::folds) struct LateStore {
    /// Sanitized binding name.
    pub(in crate::folds) name: String,
    /// The store's value defines a function/class (the module's PUBLIC
    /// surface: an external reader — e.g. a test driver appended after
    /// `func_main_0.call(this)` — reads the module-scope binding, so the
    /// store must NOT become a shadowing local `let`; N74 yield-star
    /// golden/node regression).
    pub(in crate::folds) func_valued: bool,
    /// Lexical store (vs global store).
    pub(in crate::folds) lexical: bool,
    /// Whether the lexical store targets an own pushed frame of this function.
    pub(in crate::folds) own: bool,
    /// The scope-chain level (lexical only; 0 for globals).
    pub(in crate::folds) level: u16,
    /// The innermost DECLARATION-CAPABLE region: `Some(0)` at the root
    /// list, `Some(try-id)` inside a chain of `try` bodies; `None` when
    /// the store sits in a run no declaration may occupy (an `if` arm,
    /// a loop body, a `catch`/`finally`, …).
    pub(in crate::folds) region: Option<usize>,
    /// The enclosing try-body ids (innermost last) — the nesting check.
    pub(in crate::folds) stack: Vec<usize>,
    /// Whole-tree pre-order sequence number.
    pub(in crate::folds) seq: usize,
}

/// The fold's whole-tree context.
pub(in crate::folds) struct LateDeclCx {
    /// Own lexenv pushes (the `lex_decls` ownership rule).
    pub(in crate::folds) pushes: usize,
    /// Names already declared (`scope_fold` conversions, params).
    pub(in crate::folds) declared: std::collections::HashSet<String>,
    /// Store sites, in pre-order.
    pub(in crate::folds) stores: Vec<LateStore>,
    /// `(name, try-stack-membership)`: a name read (or store target)
    /// that appears OUTSIDE some try body — per try-id disqualifiers.
    /// We record for every name-use the full try-stack; a candidate
    /// with `try_id = Some(t)` dies if any use's stack lacks `t`.
    pub(in crate::folds) uses: Vec<(String, Vec<usize>)>,
    /// Monotonic try-body ids.
    pub(in crate::folds) next_try: usize,
    /// Pre-order counter.
    pub(in crate::folds) seq: usize,
    /// Sequence positions of every ScopePush/ScopePop (a name whose
    /// use/store SPAN contains one may be re-pushed mid-span — a
    /// different binding with the same name; N74-W4 corpus regression
    /// for-update-continue-1: `let v2_0` declared twice for two
    /// iterations' slots, the inner shadowing the outer's read).
    pub(in crate::folds) scope_edges: Vec<usize>,
}

impl LateDeclCx {
    fn new() -> Self {
        Self {
            pushes: 0,
            declared: std::collections::HashSet::new(),
            stores: Vec::new(),
            uses: Vec::new(),
            next_try: 1,
            seq: 0,
            scope_edges: Vec::new(),
        }
    }
}

/// Whether `e` mentions `name` as an identifier (a read of the
/// binding; declaration sites and store targets are recorded by the
/// caller).
pub(in crate::folds) fn collect_ident_uses(
    e: &Expr,
    try_stack: &[usize],
    out: &mut Vec<(String, Vec<usize>)>,
) {
    let mut stack: Vec<&Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        if let Expr::Ident(name) = cur {
            out.push((name.clone(), try_stack.to_vec()));
        }
        for c in expr_children(cur).into_iter().rev() {
            stack.push(c);
        }
    }
}

/// Census for the late-decl fold. `region_stack` = enclosing
/// DECLARATION-CAPABLE region ids (root list, try bodies, `if` arms,
/// catch/finally bodies, labeled blocks — innermost last; loops and
/// switch cases are NOT capable: a `let` there is per-iteration /
/// fallthrough-unsafe). A store may become a declaration only when its
/// run sits directly in a capable container (`capable_here`).
pub(in crate::folds) fn late_decl_census(
    nodes: &[SNode],
    capable_here: bool,
    region_stack: &mut Vec<usize>,
    cx: &mut LateDeclCx,
) {
    enum Task<'a> {
        EnterRegion {
            nodes: &'a [SNode],
            capable: bool,
            push_new_id: bool,
        },
        PopRegion,
        Nodes {
            slice: &'a [SNode],
            capable: bool,
        },
        Expr(&'a Expr),
        SwitchCases(&'a [SwitchCase]),
    }

    let mut stack = vec![Task::Nodes {
        slice: nodes,
        capable: capable_here,
    }];
    while let Some(task) = stack.pop() {
        match task {
            Task::EnterRegion {
                nodes,
                capable,
                push_new_id,
            } => {
                if push_new_id {
                    let id = cx.next_try;
                    cx.next_try += 1;
                    region_stack.push(id);
                    stack.push(Task::PopRegion);
                }
                stack.push(Task::Nodes {
                    slice: nodes,
                    capable,
                });
            }
            Task::PopRegion => {
                region_stack.pop();
            }
            Task::Expr(e) => {
                collect_ident_uses(e, region_stack, &mut cx.uses);
            }
            Task::SwitchCases(cases) => {
                if let Some((first, rest)) = cases.split_first() {
                    if !rest.is_empty() {
                        stack.push(Task::SwitchCases(rest));
                    }
                    stack.push(Task::Nodes {
                        slice: &first.body,
                        capable: false,
                    });
                    for t in first.tests.iter().rev() {
                        stack.push(Task::Expr(t));
                    }
                }
            }
            Task::Nodes { slice, capable } => {
                let Some((first, rest)) = slice.split_first() else {
                    continue;
                };
                if !rest.is_empty() {
                    stack.push(Task::Nodes {
                        slice: rest,
                        capable,
                    });
                }
                match first {
                    SNode::Stmts(leaves) => {
                        for l in leaves {
                            cx.seq += 1;
                            match l {
                                Leaf::Raw(Stmt::ScopePush { .. }) => {
                                    cx.pushes += 1;
                                    cx.scope_edges.push(cx.seq);
                                }
                                Leaf::Raw(Stmt::LexStore {
                                    level,
                                    own,
                                    name,
                                    value,
                                    ..
                                }) => {
                                    let name = crate::legalize::sanitize(name);
                                    collect_ident_uses(value, region_stack, &mut cx.uses);
                                    cx.uses.push((name.clone(), region_stack.clone()));
                                    cx.stores.push(LateStore {
                                        func_valued: matches!(
                                            value,
                                            Expr::Closure { .. } | Expr::Class { .. }
                                        ),
                                        name,
                                        lexical: true,
                                        own: *own,
                                        level: *level,
                                        region: capable
                                            .then(|| region_stack.last().copied().unwrap_or(0)),
                                        stack: region_stack.clone(),
                                        seq: cx.seq,
                                    });
                                }
                                Leaf::Raw(Stmt::GlobalStore { name, value, .. }) => {
                                    let name = crate::legalize::sanitize(name);
                                    collect_ident_uses(value, region_stack, &mut cx.uses);
                                    cx.uses.push((name.clone(), region_stack.clone()));
                                    cx.stores.push(LateStore {
                                        func_valued: matches!(
                                            value,
                                            Expr::Closure { .. } | Expr::Class { .. }
                                        ),
                                        name,
                                        lexical: false,
                                        own: true,
                                        level: 0,
                                        region: capable
                                            .then(|| region_stack.last().copied().unwrap_or(0)),
                                        stack: region_stack.clone(),
                                        seq: cx.seq,
                                    });
                                }
                                Leaf::Decl { name, value, .. } => {
                                    cx.declared.insert(name.clone());
                                    if let Some(v) = value {
                                        collect_ident_uses(v, region_stack, &mut cx.uses);
                                    }
                                }
                                Leaf::Raw(Stmt::ScopePop) => {
                                    cx.scope_edges.push(cx.seq);
                                }
                                Leaf::Assign { target, value } => {
                                    collect_ident_uses(value, region_stack, &mut cx.uses);
                                    cx.uses.push((target.clone(), region_stack.clone()));
                                }
                                Leaf::Raw(s) => {
                                    for e in stmt_exprs_of(s) {
                                        collect_ident_uses(e, region_stack, &mut cx.uses);
                                    }
                                }
                                Leaf::Destructure { obj, .. } => {
                                    collect_ident_uses(obj, region_stack, &mut cx.uses);
                                }
                            }
                        }
                    }
                    SNode::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        stack.push(Task::EnterRegion {
                            nodes: otherwise,
                            capable: true,
                            push_new_id: true,
                        });
                        stack.push(Task::EnterRegion {
                            nodes: then,
                            capable: true,
                            push_new_id: true,
                        });
                        collect_ident_uses(cond, region_stack, &mut cx.uses);
                    }
                    SNode::While { cond, body, .. } => {
                        stack.push(Task::Nodes {
                            slice: body,
                            capable: false,
                        });
                        if let Some(c) = cond {
                            collect_ident_uses(c, region_stack, &mut cx.uses);
                        }
                    }
                    SNode::DoWhile { body, cond, .. } => {
                        stack.push(Task::Expr(cond));
                        stack.push(Task::Nodes {
                            slice: body,
                            capable: false,
                        });
                    }
                    SNode::Block(body) | SNode::Labeled { body, .. } => {
                        stack.push(Task::EnterRegion {
                            nodes: body,
                            capable: true,
                            push_new_id: true,
                        });
                    }
                    SNode::ForOf { iter, body, .. } => {
                        stack.push(Task::Nodes {
                            slice: body,
                            capable: false,
                        });
                        collect_ident_uses(iter, region_stack, &mut cx.uses);
                    }
                    SNode::ForIn { obj, body, .. } => {
                        stack.push(Task::Nodes {
                            slice: body,
                            capable: false,
                        });
                        collect_ident_uses(obj, region_stack, &mut cx.uses);
                    }
                    SNode::Try {
                        body,
                        catches,
                        finally,
                        ..
                    } => {
                        if let Some(f) = finally {
                            stack.push(Task::EnterRegion {
                                nodes: f,
                                capable: true,
                                push_new_id: true,
                            });
                        }
                        for c in catches.iter().rev() {
                            stack.push(Task::EnterRegion {
                                nodes: &c.body,
                                capable: true,
                                push_new_id: true,
                            });
                        }
                        stack.push(Task::EnterRegion {
                            nodes: body,
                            capable: true,
                            push_new_id: true,
                        });
                    }
                    SNode::Switch { disc, cases } => {
                        if !cases.is_empty() {
                            stack.push(Task::SwitchCases(cases));
                        }
                        collect_ident_uses(disc, region_stack, &mut cx.uses);
                    }
                    SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
                }
            }
        }
    }
}

/// All expression positions of a raw statement (for the use census).
pub(in crate::folds) fn stmt_exprs_of(s: &Stmt) -> Vec<&Expr> {
    match s {
        Stmt::Declare { value, .. } => vec![value],
        Stmt::PhiAssign { value, .. } => vec![value],
        Stmt::Expr(e) => vec![e],
        Stmt::StoreProp { object, value, .. } => vec![object, value],
        Stmt::StoreIndex {
            object,
            index,
            value,
            ..
        } => vec![object, index, value],
        Stmt::StoreDyn {
            object, key, value, ..
        } => vec![object, key, value],
        Stmt::DefineMethod { object, func, .. } => vec![object, func],
        Stmt::StorePrivate { object, value, .. } => vec![object, value],
        Stmt::StoreSuper { key, value, .. } => key.iter().chain(std::iter::once(value)).collect(),
        Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => vec![value],
        Stmt::Throw(e) => vec![e],
        Stmt::Return(Some(e)) => vec![e],
        Stmt::CondBranch { cond, .. } => vec![cond],
        _ => Vec::new(),
    }
}

/// See the section comment. Runs AFTER [`scope_fold`] (it consumes the
/// stores scope_fold could not turn into declarations). `top_level`
/// gates the global-store half (nested functions would shadow).
pub fn late_decl_fold(
    nodes: &mut [SNode],
    params: &[String],
    top_level: bool,
    stats: &mut FoldStats,
) {
    let mut cx = LateDeclCx::new();
    late_decl_census(nodes, true, &mut Vec::new(), &mut cx);

    // Group by name; the qualifying set.
    let mut names: Vec<String> = cx.stores.iter().map(|s| s.name.clone()).collect();
    names.sort();
    names.dedup();
    let mut convert: std::collections::HashMap<String, Vec<usize>> =
        std::collections::HashMap::new();
    for name in names {
        let sites: Vec<&LateStore> = cx.stores.iter().filter(|s| s.name == name).collect();
        // One store kind only (a lexical/global mix means the scope
        // model is inconsistent — the honest fallback stays).
        if sites.iter().any(|s| s.lexical) && sites.iter().any(|s| !s.lexical) {
            continue;
        }
        // Lexical stores must all target OWN frame slots (the
        // `lex_decls` rule); a capture store belongs to an ancestor.
        if sites
            .iter()
            .any(|s| s.lexical && (!s.own || s.level as usize >= cx.pushes))
        {
            continue;
        }
        // Global stores convert only at the top level.
        if sites.iter().any(|s| !s.lexical) && !top_level {
            continue;
        }
        // A function/class-valued binding AT THE MODULE TOP is the
        // module's public surface: converting its first store to a local
        // `let` shadows the module-scope `var` hoist and external readers
        // (e.g. a test driver appended after `func_main_0.call(this)`)
        // see `undefined` (the yield-star golden/node regression).
        // Function-local closures keep the `let` conversion (s38).
        if top_level && sites.iter().any(|s| s.func_valued) {
            continue;
        }
        // Not a parameter, not already declared by scope_fold, not a
        // read-only global name (the sister lane's collision class).
        if params.contains(&name)
            || cx.declared.contains(&name)
            || matches!(name.as_str(), "undefined" | "NaN" | "Infinity")
        {
            continue;
        }
        // Coverage model (N74-W4). When the root run holds a store the
        // declaration goes to the root (a function-scope `let` covering
        // everything; nested stores stay assignments). Otherwise each
        // declaration-capable region holding a store gets its own `let`
        // (sibling `try` bodies etc. — S13.2.1_A7_T4's independent
        // `x = x` probes), provided:
        //   - every OTHER store and every READ of the name is COVERED
        //     by a converted region — the reference's region stack
        //     contains the region id (region 0, the root, covers
        //     everything) — otherwise that reference would silently
        //     read the module-top `var`/outer binding instead;
        //   - no converted region nests inside another (an inner `let`
        //     would shadow the outer region's binding mid-window).
        let root_has = sites.iter().any(|s| s.region == Some(0));
        if root_has {
            // Same-name re-push mid-span → distinct bindings; bail.
            let span_lo = sites.iter().map(|s| s.seq).min().unwrap_or(0);
            let mut span_hi = span_lo;
            for s in sites.iter() {
                span_hi = span_hi.max(s.seq);
            }
            if cx.scope_edges.iter().any(|e| *e > span_lo && *e < span_hi) {
                continue;
            }
            convert.insert(name, vec![0]);
            continue;
        }
        let store_regions: std::collections::HashSet<usize> =
            sites.iter().filter_map(|s| s.region).collect();
        if store_regions.is_empty() {
            continue;
        }
        let nested = cx.stores.iter().filter(|st| st.name == name).any(|st| {
            st.region.is_some()
                && st
                    .stack
                    .iter()
                    .any(|t| store_regions.contains(t) && Some(*t) != st.region)
        });
        if nested {
            continue;
        }
        let covered = |stack: &Vec<usize>| {
            store_regions.contains(&0) || stack.iter().any(|t| store_regions.contains(t))
        };
        if cx
            .uses
            .iter()
            .filter(|(n, _)| *n == name)
            .any(|(_, stack)| !covered(stack))
        {
            continue;
        }
        // Same-name re-push mid-span → distinct bindings; bail.
        let span_lo = sites.iter().map(|s| s.seq).min().unwrap_or(0);
        let mut span_hi = span_lo;
        for s in sites.iter() {
            span_hi = span_hi.max(s.seq);
        }
        if cx.scope_edges.iter().any(|e| *e > span_lo && *e < span_hi) {
            continue;
        }
        convert.insert(name, store_regions.iter().copied().collect());
    }
    if convert.is_empty() {
        return;
    }

    // Rewrite: per (name, region), the first store becomes the `let`;
    // every other store becomes a plain assignment. Region ids are
    // recomputed with the census's traversal (same walk, same ids).
    let mut declared_now: std::collections::HashSet<(String, usize)> =
        std::collections::HashSet::new();
    enum RewriteTask<'a> {
        EnterRegion {
            nodes: &'a mut [SNode],
            capable: bool,
            push_new_id: bool,
        },
        PopRegion,
        Nodes {
            slice: &'a mut [SNode],
            capable: bool,
        },
    }

    let mut next_try = 1usize;
    let mut region_stack: Vec<usize> = Vec::new();
    let mut rstack = vec![RewriteTask::Nodes {
        slice: nodes,
        capable: true,
    }];
    while let Some(task) = rstack.pop() {
        match task {
            RewriteTask::EnterRegion {
                nodes,
                capable,
                push_new_id,
            } => {
                if push_new_id {
                    let id = next_try;
                    next_try += 1;
                    region_stack.push(id);
                    rstack.push(RewriteTask::PopRegion);
                }
                rstack.push(RewriteTask::Nodes {
                    slice: nodes,
                    capable,
                });
            }
            RewriteTask::PopRegion => {
                region_stack.pop();
            }
            RewriteTask::Nodes { slice, capable } => {
                let Some((first, rest)) = slice.split_first_mut() else {
                    continue;
                };
                if !rest.is_empty() {
                    rstack.push(RewriteTask::Nodes {
                        slice: rest,
                        capable,
                    });
                }
                match first {
                    SNode::Stmts(leaves) => {
                        let region = capable.then(|| region_stack.last().copied().unwrap_or(0));
                        for l in leaves.iter_mut() {
                            let name_regions = match l {
                                Leaf::Raw(Stmt::LexStore { name, .. })
                                | Leaf::Raw(Stmt::GlobalStore { name, .. }) => convert
                                    .get(&crate::legalize::sanitize(name))
                                    .map(|r| (crate::legalize::sanitize(name), r)),
                                _ => None,
                            };
                            let Some((name, regions)) = name_regions else {
                                continue;
                            };
                            let value = match l {
                                Leaf::Raw(Stmt::LexStore { value, .. })
                                | Leaf::Raw(Stmt::GlobalStore { value, .. }) => value.clone(),
                                _ => unreachable!(),
                            };
                            let key = region.map(|r| (name.clone(), r));
                            if let Some(key) = key
                                && regions.contains(&key.1)
                                && !declared_now.contains(&key)
                            {
                                declared_now.insert(key);
                                *l = Leaf::Decl {
                                    name,
                                    mutable: true,
                                    value: Some(value),
                                };
                                stats.late_decl += 1;
                            } else {
                                *l = Leaf::Assign {
                                    target: name,
                                    value,
                                };
                            }
                        }
                    }
                    SNode::If {
                        then, otherwise, ..
                    } => {
                        rstack.push(RewriteTask::EnterRegion {
                            nodes: otherwise,
                            capable: true,
                            push_new_id: true,
                        });
                        rstack.push(RewriteTask::EnterRegion {
                            nodes: then,
                            capable: true,
                            push_new_id: true,
                        });
                    }
                    SNode::While { body, .. }
                    | SNode::DoWhile { body, .. }
                    | SNode::ForOf { body, .. }
                    | SNode::ForIn { body, .. } => rstack.push(RewriteTask::Nodes {
                        slice: body,
                        capable: false,
                    }),
                    SNode::Block(body) | SNode::Labeled { body, .. } => {
                        rstack.push(RewriteTask::EnterRegion {
                            nodes: body,
                            capable: true,
                            push_new_id: true,
                        });
                    }
                    SNode::Try {
                        body,
                        catches,
                        finally,
                        ..
                    } => {
                        if let Some(f) = finally {
                            rstack.push(RewriteTask::EnterRegion {
                                nodes: f,
                                capable: true,
                                push_new_id: true,
                            });
                        }
                        for c in catches.iter_mut().rev() {
                            rstack.push(RewriteTask::EnterRegion {
                                nodes: &mut c.body,
                                capable: true,
                                push_new_id: true,
                            });
                        }
                        rstack.push(RewriteTask::EnterRegion {
                            nodes: body,
                            capable: true,
                            push_new_id: true,
                        });
                    }
                    SNode::Switch { cases, .. } => {
                        for c in cases.iter_mut().rev() {
                            rstack.push(RewriteTask::Nodes {
                                slice: &mut c.body,
                                capable: false,
                            });
                        }
                    }
                    SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
                }
            }
        }
    }
}

// ── N74-W4: rest-parameter reconstruction ──────────────────────────
//
// es2abc lowers `(...rest)` / `(a, ...rest)` to `copyrestargs k` (k =
// the named-parameter count) plus ONE extra frame slot past the named
// params (the rest array's staging slot — recover sees it as a spurious
// trailing visible parameter `pN`). The generic emission prints
// `[...arguments].slice(k) /*CopyRestArgs*/` — wrong in arrows and
// closures (`arguments` is the OUTER function's; test262's
// arrowparameters-cover-rest rows read the outer script's empty
// arguments) and wrong for `.length` (the spurious slot inflates it —
// rest-parameters/expected-argument-count). When the body holds exactly
// one `CopyRestArgs` shape, rewrite it to a real rest parameter: every
// `Expr::RestArgs` becomes the rest name, the visible params at-or-past
// `k` drop (the staging slot), and `...<name>` joins the printed
// signature. Bails — keeping the loud approximation — when any dropped
// parameter is referenced in the body.

/// Apply `f` to every expression position in the tree (leaves AND
/// node conditions — the mutation counterpart of the use-census walk).
pub(in crate::folds) fn map_exprs_mut(nodes: &mut [SNode], f: &mut impl FnMut(&mut Expr)) {
    fn one_expr(e: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
        let mut stack: Vec<&mut Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            f(cur);
            for c in expr_children_mut(cur).into_iter().rev() {
                stack.push(c);
            }
        }
    }
    fn one_leaf(l: &mut Leaf, f: &mut impl FnMut(&mut Expr)) {
        match l {
            Leaf::Raw(s) => match s {
                Stmt::Declare { value, .. }
                | Stmt::PhiAssign { value, .. }
                | Stmt::Expr(value)
                | Stmt::Throw(value) => one_expr(value, f),
                Stmt::Return(Some(e)) => one_expr(e, f),
                Stmt::StoreProp { object, value, .. } => {
                    one_expr(object, f);
                    one_expr(value, f);
                }
                Stmt::StoreIndex {
                    object,
                    index,
                    value,
                    ..
                } => {
                    one_expr(object, f);
                    one_expr(index, f);
                    one_expr(value, f);
                }
                Stmt::StoreDyn {
                    object, key, value, ..
                } => {
                    one_expr(object, f);
                    one_expr(key, f);
                    one_expr(value, f);
                }
                Stmt::DefineMethod { object, func, .. } => {
                    one_expr(object, f);
                    one_expr(func, f);
                }
                Stmt::StorePrivate { object, value, .. } => {
                    one_expr(object, f);
                    one_expr(value, f);
                }
                Stmt::StoreSuper { key, value, .. } => {
                    if let Some(k) = key {
                        one_expr(k, f);
                    }
                    one_expr(value, f);
                }
                Stmt::LexStore { value, .. }
                | Stmt::GlobalStore { value, .. }
                | Stmt::ModuleStore { value, .. } => one_expr(value, f),
                Stmt::CondBranch { cond, .. } => one_expr(cond, f),
                _ => {}
            },
            Leaf::Destructure { obj, .. } => one_expr(obj, f),
            Leaf::Decl { value: Some(v), .. } => one_expr(v, f),
            Leaf::Decl { value: None, .. } => {}
            Leaf::Assign { value, .. } => one_expr(value, f),
        }
    }

    enum Task<'a> {
        Nodes(&'a mut [SNode]),
        Expr(&'a mut Expr),
        SwitchCases(&'a mut [SwitchCase]),
    }

    let mut stack = vec![Task::Nodes(nodes)];
    while let Some(task) = stack.pop() {
        match task {
            Task::Expr(e) => one_expr(e, f),
            Task::SwitchCases(cases) => {
                if let Some((first, rest)) = cases.split_first_mut() {
                    if !rest.is_empty() {
                        stack.push(Task::SwitchCases(rest));
                    }
                    stack.push(Task::Nodes(&mut first.body));
                    for t in first.tests.iter_mut().rev() {
                        stack.push(Task::Expr(t));
                    }
                }
            }
            Task::Nodes(slice) => {
                let Some((first, rest)) = slice.split_first_mut() else {
                    continue;
                };
                if !rest.is_empty() {
                    stack.push(Task::Nodes(rest));
                }
                match first {
                    SNode::Stmts(run) => {
                        for l in run {
                            one_leaf(l, f);
                        }
                    }
                    SNode::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        one_expr(cond, f);
                        stack.push(Task::Nodes(otherwise));
                        stack.push(Task::Nodes(then));
                    }
                    SNode::While { cond, body, .. } => {
                        if let Some(c) = cond {
                            one_expr(c, f);
                        }
                        stack.push(Task::Nodes(body));
                    }
                    SNode::DoWhile { body, cond, .. } => {
                        stack.push(Task::Expr(cond));
                        stack.push(Task::Nodes(body));
                    }
                    SNode::Block(body) | SNode::Labeled { body, .. } => {
                        stack.push(Task::Nodes(body));
                    }
                    SNode::ForOf { iter, body, .. } => {
                        one_expr(iter, f);
                        stack.push(Task::Nodes(body));
                    }
                    SNode::ForIn { obj, body, .. } => {
                        one_expr(obj, f);
                        stack.push(Task::Nodes(body));
                    }
                    SNode::Try {
                        body,
                        catches,
                        finally,
                        ..
                    } => {
                        if let Some(fin) = finally {
                            stack.push(Task::Nodes(fin));
                        }
                        for c in catches.iter_mut().rev() {
                            stack.push(Task::Nodes(&mut c.body));
                        }
                        stack.push(Task::Nodes(body));
                    }
                    SNode::Switch { disc, cases } => {
                        one_expr(disc, f);
                        if !cases.is_empty() {
                            stack.push(Task::SwitchCases(cases));
                        }
                    }
                    SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
                }
            }
        }
    }
}

/// See the section comment. Mutates `params` (drops the staging slots,
/// appends `...<rest>`) and rewrites the body's `RestArgs` exprs.
/// `hidden` is the ABI-slot count (`params[hidden..]` are visible).
pub fn rest_param_fold(
    nodes: &mut [SNode],
    params: &mut Vec<String>,
    hidden: usize,
    stats: &mut FoldStats,
) {
    // Exactly one CopyRestArgs shape?
    let mut starts = BTreeSet::new();
    map_exprs_mut(nodes, &mut |e| {
        if let Expr::RestArgs { start_index } = e {
            starts.insert(*start_index);
        }
    });
    let collected: Vec<u16> = starts.into_iter().collect();
    let [k] = collected[..] else {
        return;
    };
    let k = k as usize;
    let visible = params.len() - hidden.min(params.len());
    if visible < k {
        return; // shape mismatch — keep the approximation
    }
    // The dropped slots (the staging slot + anything past it) must be
    // unreferenced.
    let dropped: Vec<String> = params[hidden + k..].to_vec();
    let mut dropped_used = false;
    map_exprs_mut(nodes, &mut |e| {
        if let Expr::Ident(n) = e
            && dropped.iter().any(|d| d == n)
        {
            dropped_used = true;
        }
    });
    if dropped_used {
        return;
    }
    // Mint a collision-free rest name over every name the body knows.
    let mut taken: BTreeSet<String> = params.iter().cloned().collect();
    map_exprs_mut(nodes, &mut |e| match e {
        Expr::Ident(n) => {
            taken.insert(n.clone());
        }
        Expr::Temp { name, .. } => {
            taken.insert(name.clone());
        }
        _ => {}
    });
    walk_leaves(nodes, &mut |l| match l {
        Leaf::Raw(Stmt::Declare { name, .. }) | Leaf::Raw(Stmt::PhiDecl { name, .. }) => {
            taken.insert(name.clone());
        }
        Leaf::Raw(Stmt::PhiAssign { target, .. }) => {
            taken.insert(target.clone());
        }
        Leaf::Raw(Stmt::LexStore { name, .. }) | Leaf::Raw(Stmt::GlobalStore { name, .. }) => {
            taken.insert(crate::legalize::sanitize(name));
        }
        Leaf::Decl { name, .. } => {
            taken.insert(name.clone());
        }
        Leaf::Assign { target, .. } => {
            taken.insert(target.clone());
        }
        _ => {}
    });
    let mut rest = "rest".to_string();
    let mut i = 1usize;
    while taken.contains(&rest) {
        rest = format!("rest${i}");
        i += 1;
    }
    // Rewrite. A bare `rest;` expression-statement (an unused
    // CopyRestArgs result — keep-alive evidence, recover.rs) is
    // consumed, not rewritten.
    let rest_expr = Expr::Ident(rest.clone());
    walk_stmts_runs_mut(nodes, |run| {
        run.retain(|l| !matches!(l, Leaf::Raw(Stmt::Expr(Expr::RestArgs { .. }))));
    });
    map_exprs_mut(nodes, &mut |e| {
        if matches!(e, Expr::RestArgs { .. }) {
            *e = rest_expr.clone();
        }
    });
    params.truncate(hidden + k);
    params.push(format!("...{rest}"));
    stats.rest_param += 1;
}
