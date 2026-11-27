//! Object/array literal builders, tagged-template folds, and rest destructuring.

use super::*;
use crate::folds::loops::subst_temp_in_expr;

// ── Fold 1: literal builders ─────────────────────────────────────────

pub(in crate::folds) fn fold_leaves_with_uses(
    leaves: &mut Vec<Leaf>,
    global_uses: Option<&BTreeMap<ValueId, usize>>,
    stats: &mut FoldStats,
) {
    fold_rest_destructure(leaves, stats);
    fold_literal_builders_with_uses(leaves, global_uses, stats);
}

// ── Tagged-template call fold (#30) ──────────────────────────────────

pub(in crate::folds) fn fold_tagged_templates(nodes: &mut [SNode]) {
    let mut use_counts: std::collections::HashMap<ValueId, usize> =
        std::collections::HashMap::new();
    collect_value_uses_in_snodes(nodes, &mut use_counts);
    fold_tagged_in_snodes(nodes, &use_counts);
}

pub(in crate::folds) fn collect_value_uses_in_expr(
    e: &Expr,
    counts: &mut std::collections::HashMap<ValueId, usize>,
) {
    let mut stack: Vec<&Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        if let Expr::Temp { value, .. } = cur {
            *counts.entry(*value).or_insert(0) += 1;
        }
        stack.extend(expr_children(cur));
    }
}

pub(in crate::folds) fn collect_value_uses_in_leaf(
    l: &Leaf,
    counts: &mut std::collections::HashMap<ValueId, usize>,
) {
    match l {
        Leaf::Raw(s) => match s {
            Stmt::Declare { value, .. }
            | Stmt::PhiAssign { value, .. }
            | Stmt::LexStore { value, .. }
            | Stmt::GlobalStore { value, .. }
            | Stmt::ModuleStore { value, .. } => collect_value_uses_in_expr(value, counts),
            Stmt::Expr(e) | Stmt::Throw(e) => collect_value_uses_in_expr(e, counts),
            Stmt::Return(Some(e)) => collect_value_uses_in_expr(e, counts),
            Stmt::StoreProp { object, value, .. } | Stmt::StorePrivate { object, value, .. } => {
                collect_value_uses_in_expr(object, counts);
                collect_value_uses_in_expr(value, counts);
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
                collect_value_uses_in_expr(object, counts);
                collect_value_uses_in_expr(key, counts);
                collect_value_uses_in_expr(value, counts);
            }
            Stmt::DefineMethod { object, func, .. } => {
                collect_value_uses_in_expr(object, counts);
                collect_value_uses_in_expr(func, counts);
            }
            Stmt::StoreSuper { key, value, .. } => {
                if let Some(k) = key {
                    collect_value_uses_in_expr(k, counts);
                }
                collect_value_uses_in_expr(value, counts);
            }
            Stmt::CondBranch { cond, .. } => collect_value_uses_in_expr(cond, counts),
            _ => {}
        },
        Leaf::Destructure { obj, .. } => collect_value_uses_in_expr(obj, counts),
        Leaf::Decl { value: Some(v), .. } | Leaf::Assign { value: v, .. } => {
            collect_value_uses_in_expr(v, counts)
        }
        Leaf::Decl { value: None, .. } => {}
    }
}

pub(in crate::folds) fn collect_value_uses_in_snodes(
    nodes: &[SNode],
    counts: &mut std::collections::HashMap<ValueId, usize>,
) {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(seq) = stack.pop() {
        for n in seq {
            match n {
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        collect_value_uses_in_leaf(l, counts);
                    }
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    collect_value_uses_in_expr(cond, counts);
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        collect_value_uses_in_expr(c, counts);
                    }
                    stack.push(body);
                }
                SNode::DoWhile { cond, body, .. } => {
                    collect_value_uses_in_expr(cond, counts);
                    stack.push(body);
                }
                SNode::ForOf { iter, body, .. } => {
                    collect_value_uses_in_expr(iter, counts);
                    stack.push(body);
                }
                SNode::ForIn { obj, body, .. } => {
                    collect_value_uses_in_expr(obj, counts);
                    stack.push(body);
                }
                SNode::Switch { disc, cases, .. } => {
                    collect_value_uses_in_expr(disc, counts);
                    for c in cases.iter().rev() {
                        for t in &c.tests {
                            collect_value_uses_in_expr(t, counts);
                        }
                        stack.push(&c.body);
                    }
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        stack.push(fin);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::Labeled { body, .. } | SNode::Block(body) => stack.push(body),
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
}

pub(in crate::folds) fn fold_tagged_in_snodes(
    nodes: &mut [SNode],
    use_counts: &std::collections::HashMap<ValueId, usize>,
) {
    walk_stmts_runs_mut(nodes, |leaves| fold_tagged_in_leaves(leaves, use_counts));
}

pub(in crate::folds) fn member_expr_object(e: &Expr) -> Option<&Expr> {
    match e {
        Expr::PropName { object, .. }
        | Expr::PropIndex { object, .. }
        | Expr::PropDyn { object, .. } => Some(object),
        _ => None,
    }
}

pub(in crate::folds) fn is_pure_template_setup_leaf(l: &Leaf) -> bool {
    match l {
        Leaf::Raw(Stmt::Declare {
            mutable: false,
            value,
            ..
        }) => matches!(
            value,
            Expr::Lit(_) | Expr::ArrayLit { .. } | Expr::ArrayBuild { .. }
        ),
        Leaf::Raw(Stmt::StoreProp { own: true, .. })
        | Leaf::Raw(Stmt::StoreIndex { own: true, .. })
        | Leaf::Raw(Stmt::StoreDyn { own: true, .. }) => true,
        _ => false,
    }
}

pub(in crate::folds) fn leaf_mutates_ident(l: &Leaf, ident: &str) -> bool {
    match l {
        Leaf::Assign { target, .. } => target == ident,
        Leaf::Raw(
            Stmt::PhiAssign { target, .. }
            | Stmt::LexStore { name: target, .. }
            | Stmt::GlobalStore { name: target, .. },
        ) => target == ident,
        _ => false,
    }
}

pub(in crate::folds) fn try_rewrite_tagged_call_in_expr(
    e: &mut Expr,
    tpl_vid: ValueId,
    quasis: &[String],
    prior_leaves: &[Leaf],
    intervening_leaves: &[Leaf],
    use_counts: &std::collections::HashMap<ValueId, usize>,
) -> Option<Option<usize>> {
    let mut stack: Vec<&mut Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        if let Expr::Call {
            callee,
            this,
            args,
            kind: abcd_ir::op::CallKind::Direct | abcd_ir::op::CallKind::Dynamic,
        } = cur
            && args.len() == quasis.len()
            && temp_value(&args[0]) == Some(tpl_vid)
        {
            match this {
                None => {
                    // `tag(...)` without receiver: `tag` must not be a bare member
                    // expression (which in JS `` obj.m`...` `` would bind `this = obj`).
                    if member_expr_object(callee).is_none()
                        && !matches!(
                            callee.as_ref(),
                            Expr::PrivateLoad { .. } | Expr::SuperProp { .. }
                        )
                    {
                        let mutated = temp_name(callee).is_some_and(|nm| {
                            intervening_leaves.iter().any(|l| leaf_mutates_ident(l, nm))
                        });
                        if !mutated {
                            let subs = args[1..].to_vec();
                            let tag = callee.clone();
                            *cur = Expr::TaggedTemplate {
                                tag,
                                quasis: quasis.to_vec(),
                                exprs: subs,
                            };
                            return Some(None);
                        }
                    }
                }
                Some(recv) => {
                    if member_expr_object(callee) == Some(recv.as_ref()) {
                        let subs = args[1..].to_vec();
                        let tag = callee.clone();
                        *cur = Expr::TaggedTemplate {
                            tag,
                            quasis: quasis.to_vec(),
                            exprs: subs,
                        };
                        return Some(None);
                    }
                    if let Some(fn_vid) = temp_value(callee)
                        && use_counts.get(&fn_vid).copied() == Some(1)
                        && matches!(
                            recv.as_ref(),
                            Expr::Ident(_) | Expr::Temp { .. } | Expr::GlobalThis
                        )
                    {
                        let found_c = prior_leaves.iter().enumerate().rev().find_map(|(c, l)| {
                            if let Leaf::Raw(Stmt::Declare {
                                mutable: false,
                                value,
                                value_id,
                                ..
                            }) = l
                                && *value_id == fn_vid
                            {
                                Some((c, value))
                            } else {
                                None
                            }
                        });
                        if let Some((c, member_val)) = found_c
                            && member_expr_object(member_val) == Some(recv.as_ref())
                            && prior_leaves[c + 1..]
                                .iter()
                                .all(is_pure_template_setup_leaf)
                            && temp_name(recv).is_none_or(|nm| {
                                !intervening_leaves.iter().any(|l| leaf_mutates_ident(l, nm))
                            })
                        {
                            let subs = args[1..].to_vec();
                            let tag = Box::new(member_val.clone());
                            *cur = Expr::TaggedTemplate {
                                tag,
                                quasis: quasis.to_vec(),
                                exprs: subs,
                            };
                            return Some(Some(c));
                        }
                    }
                }
            }
        }
        for child in expr_children_mut(cur).into_iter().rev() {
            stack.push(child);
        }
    }
    None
}

pub(in crate::folds) fn try_rewrite_tagged_call_in_leaf(
    leaf: &mut Leaf,
    tpl_vid: ValueId,
    quasis: &[String],
    prior_leaves: &[Leaf],
    intervening_leaves: &[Leaf],
    use_counts: &std::collections::HashMap<ValueId, usize>,
) -> Option<Option<usize>> {
    match leaf {
        Leaf::Raw(s) => match s {
            Stmt::Declare { value, .. }
            | Stmt::PhiAssign { value, .. }
            | Stmt::LexStore { value, .. }
            | Stmt::GlobalStore { value, .. }
            | Stmt::ModuleStore { value, .. }
            | Stmt::Expr(value)
            | Stmt::Throw(value)
            | Stmt::Return(Some(value)) => try_rewrite_tagged_call_in_expr(
                value,
                tpl_vid,
                quasis,
                prior_leaves,
                intervening_leaves,
                use_counts,
            ),
            Stmt::StoreProp { object, value, .. } | Stmt::StorePrivate { object, value, .. } => {
                try_rewrite_tagged_call_in_expr(
                    object,
                    tpl_vid,
                    quasis,
                    prior_leaves,
                    intervening_leaves,
                    use_counts,
                )
                .or_else(|| {
                    try_rewrite_tagged_call_in_expr(
                        value,
                        tpl_vid,
                        quasis,
                        prior_leaves,
                        intervening_leaves,
                        use_counts,
                    )
                })
            }
            Stmt::StoreIndex {
                object,
                index: key,
                value,
                ..
            }
            | Stmt::StoreDyn {
                object, key, value, ..
            } => try_rewrite_tagged_call_in_expr(
                object,
                tpl_vid,
                quasis,
                prior_leaves,
                intervening_leaves,
                use_counts,
            )
            .or_else(|| {
                try_rewrite_tagged_call_in_expr(
                    key,
                    tpl_vid,
                    quasis,
                    prior_leaves,
                    intervening_leaves,
                    use_counts,
                )
            })
            .or_else(|| {
                try_rewrite_tagged_call_in_expr(
                    value,
                    tpl_vid,
                    quasis,
                    prior_leaves,
                    intervening_leaves,
                    use_counts,
                )
            }),
            Stmt::CondBranch { cond, .. } => try_rewrite_tagged_call_in_expr(
                cond,
                tpl_vid,
                quasis,
                prior_leaves,
                intervening_leaves,
                use_counts,
            ),
            _ => None,
        },
        Leaf::Decl { value: Some(v), .. } | Leaf::Assign { value: v, .. } => {
            try_rewrite_tagged_call_in_expr(
                v,
                tpl_vid,
                quasis,
                prior_leaves,
                intervening_leaves,
                use_counts,
            )
        }
        _ => None,
    }
}

pub(in crate::folds) fn fold_tagged_in_leaves(
    leaves: &mut Vec<Leaf>,
    use_counts: &std::collections::HashMap<ValueId, usize>,
) {
    let mut k = 0;
    while k < leaves.len() {
        let candidate = match &leaves[k] {
            Leaf::Raw(Stmt::Declare {
                mutable: false,
                value:
                    Expr::TemplateObject {
                        raw: Some(raw_lits),
                        ..
                    },
                value_id,
                ..
            }) if !raw_lits.is_empty() && use_counts.get(value_id).copied() == Some(1) => {
                let quasis: Option<Vec<String>> = raw_lits
                    .iter()
                    .map(|l| match l {
                        Lit::String(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect();
                quasis.map(|q| (*value_id, q))
            }
            _ => None,
        };
        let Some((tpl_vid, quasis)) = candidate else {
            k += 1;
            continue;
        };

        let mut target_m: Option<usize> = None;
        for (m, leaf) in leaves.iter().enumerate().skip(k + 1) {
            let mut local_uses = std::collections::HashMap::new();
            collect_value_uses_in_leaf(leaf, &mut local_uses);
            if local_uses.get(&tpl_vid).copied().unwrap_or(0) > 0 {
                target_m = Some(m);
                break;
            }
        }
        let Some(m) = target_m else {
            k += 1;
            continue;
        };

        let (head, tail) = leaves.split_at_mut(m);
        let prior_leaves = &head[..k];
        let intervening_leaves = &head[k + 1..];
        let rewritten = try_rewrite_tagged_call_in_leaf(
            &mut tail[0],
            tpl_vid,
            &quasis,
            prior_leaves,
            intervening_leaves,
            use_counts,
        );
        if let Some(extra_remove_c) = rewritten {
            leaves.remove(k);
            if let Some(c) = extra_remove_c {
                leaves.remove(c);
                k = k.saturating_sub(1);
            }
        } else {
            k += 1;
        }
    }
}

#[cfg(test)]
pub(in crate::folds) fn fold_literal_builders(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    fold_literal_builders_with_uses(leaves, None, stats);
}

pub(in crate::folds) fn fold_literal_builders_with_uses(
    leaves: &mut Vec<Leaf>,
    global_uses: Option<&BTreeMap<ValueId, usize>>,
    stats: &mut FoldStats,
) {
    let owned_run_uses;
    let run_uses = match global_uses {
        Some(u) => u,
        None => {
            let mut m = BTreeMap::new();
            for l in leaves.iter() {
                for e in leaf_exprs(l) {
                    let mut st = vec![e];
                    while let Some(cur) = st.pop() {
                        if let Expr::Temp { value, .. } = cur {
                            *m.entry(*value).or_insert(0) += 1;
                        }
                        st.extend(expr_children(cur));
                    }
                }
            }
            owned_run_uses = m;
            &owned_run_uses
        }
    };
    let mut i = 0;
    while i < leaves.len() {
        let (vid, is_array) = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                value: Expr::ObjectLit { .. },
                value_id,
                ..
            }) => (*value_id, false),
            Leaf::Raw(Stmt::Declare {
                value: Expr::ArrayLit { .. },
                value_id,
                ..
            }) => (*value_id, true),
            _ => {
                i += 1;
                continue;
            }
        };
        // Absorb the consecutive builder sequence at i+1…
        // N74-W4: the array shape's own element count seeds the
        // contiguity index — a store to index N is absorbable only when
        // N is exactly the next slot (a gap would silently drop the
        // hole and shift every later element left: test262 `[, 1, 2]`
        // decompiled to `[1, 2]`).
        let shape_len = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                value: Expr::ArrayLit { elements },
                ..
            }) => elements.len() as u64,
            _ => 0,
        };
        let mut absorbed: Vec<Absorb> = Vec::new();
        let mut absorbed_idx: Vec<usize> = Vec::new();
        let mut skipped_idx: Vec<usize> = Vec::new();
        // N74-W4: pure-literal declares interleaved in the builder
        // sequence (the computed-key temporaries of an accessor
        // definition) do not end it — they are RE-EMITTED above the
        // folded declaration (pure, so the reorder is free).
        let mut skipped: Vec<Leaf> = Vec::new();
        let mut j = i + 1;
        while j < leaves.len() {
            match absorb_one(&leaves[j], vid, is_array, &absorbed, shape_len) {
                Some(a) => {
                    absorbed.push(a);
                    absorbed_idx.push(j);
                    j += 1;
                }
                // N74-W4: a declare interleaved in the builder sequence
                // (an accessor's computed-key temporary, possibly a
                // call — key evaluation order inside the literal matches
                // the original statement order) does not end the
                // sequence; single-use temps inline into the entries at
                // rebuild, unused pure ones drop.
                None if matches!(&leaves[j], Leaf::Raw(Stmt::Declare { .. })) => {
                    skipped.push(leaves[j].clone());
                    skipped_idx.push(j);
                    j += 1;
                }
                None => break,
            }
        }
        if absorbed.is_empty() {
            i += 1;
            continue;
        }
        // Trailing `Declare`s after the last absorbed store belong to
        // subsequent statements, not this literal builder sequence.
        if let Some(&last_abs) = absorbed_idx.last() {
            let keep = skipped_idx.partition_point(|&idx| idx < last_abs);
            skipped.truncate(keep);
            skipped_idx.truncate(keep);
        }
        // N74-W4: resolve the skipped interleaved declares BEFORE
        // rebuilding: a temp used exactly ONCE across the absorbed
        // entries (or another skipped declare's value) inlines at that
        // use — inside the literal the computed-key evaluation order is
        // the original statement order; an unused pure-literal declare
        // drops; any other shape re-seats ABOVE the folded declaration.
        let mut bail = false;
        {
            // (vid, value, keep?) per skipped declare.
            let mut skip_vals: Vec<(abcd_ir::ValueId, Expr, bool)> = Vec::new();
            for leaf in &skipped {
                let Leaf::Raw(Stmt::Declare {
                    value, value_id, ..
                }) = leaf
                else {
                    unreachable!()
                };
                skip_vals.push((*value_id, value.clone(), true));
            }
            let count_uses =
                |vid: abcd_ir::ValueId,
                 absorbed: &[Absorb],
                 skip_vals: &[(abcd_ir::ValueId, Expr, bool)]| {
                    let mut n = 0usize;
                    for a in absorbed {
                        for e in absorb_exprs(a) {
                            n += expr_count_value(e, vid);
                        }
                    }
                    for (_, v, _) in skip_vals {
                        n += expr_count_value(v, vid);
                    }
                    n
                };
            let mut inline: Vec<(abcd_ir::ValueId, Expr, usize)> = Vec::new();
            for k in 0..skip_vals.len() {
                let (vid, value, _) = &skip_vals[k];
                let (vid, is_lit, value) = (*vid, matches!(value, Expr::Lit(_)), value.clone());
                let local_n = count_uses(vid, &absorbed, &skip_vals);
                let total_n = run_uses.get(&vid).copied().unwrap_or(local_n);
                match (local_n, total_n) {
                    (0, 0) if is_lit => skip_vals[k].2 = false, // dead pure: drop
                    (1, 1) => {
                        inline.push((vid, value, skipped_idx[k]));
                        skip_vals[k].2 = false;
                    }
                    // Multi-use or used elsewhere in the function (including
                    // control headers and `finally`): bail the whole fold.
                    _ => {
                        bail = true;
                    }
                }
            }
            if !bail && !literal_eval_order_ok(&absorbed, &absorbed_idx, &inline) {
                bail = true;
            }
            // Inline in decision order: an earlier inline may feed a
            // later one (temp chains), so substitute into the later
            // inline values too.
            if !bail {
                for pos in 0..inline.len() {
                    let (vid, value, _) = inline[pos].clone();
                    for later in inline.iter_mut().skip(pos + 1) {
                        subst_temp_in_expr(&mut later.1, vid, &value);
                    }
                    for (_, v, _) in skip_vals.iter_mut() {
                        subst_temp_in_expr(v, vid, &value);
                    }
                    for a in absorbed.iter_mut() {
                        for e in absorb_exprs_mut(a) {
                            subst_temp_in_expr(e, vid, &value);
                        }
                    }
                }
            }
            if bail {
                i += 1;
                continue;
            }
        }
        if is_array {
            stats.array_lit += 1;
        } else {
            stats.object_lit += 1;
        }
        let new_value = match leaves.remove(i) {
            Leaf::Raw(Stmt::Declare {
                name,
                mutable,
                mut value,
                value_id,
            }) => {
                let folded = match &mut value {
                    Expr::ObjectLit { entries } => {
                        let mut out: Vec<ObjEntry> = std::mem::take(entries)
                            .into_iter()
                            .map(|(k, v)| match k {
                                Lit::String(ref s) if s == "__proto__" => {
                                    ObjEntry::Computed(Expr::Lit(k), Expr::Lit(v))
                                }
                                _ => ObjEntry::KeyValue(k, Expr::Lit(v)),
                            })
                            .collect();
                        for a in absorbed {
                            match a {
                                Absorb::ObjKV(k, v) => match k {
                                    Lit::String(ref s) if s == "__proto__" => {
                                        out.push(ObjEntry::Computed(Expr::Lit(k), v));
                                    }
                                    _ => out.push(ObjEntry::KeyValue(k, v)),
                                },
                                Absorb::ObjComputed(k, v) => out.push(ObjEntry::Computed(k, v)),
                                Absorb::ObjSpread(s) => out.push(ObjEntry::Spread(s)),
                                Absorb::ObjProto(p) => out.push(ObjEntry::Proto(p)),
                                Absorb::ObjMethod(n, f) => out.push(ObjEntry::Method(n, f)),
                                Absorb::ObjAccessors {
                                    mut key,
                                    getter,
                                    setter,
                                } => {
                                    let k = match &mut key {
                                        Expr::Lit(Lit::String(s)) => {
                                            crate::expr::ObjKey::Name(std::mem::take(s))
                                        }
                                        _ => crate::expr::ObjKey::Computed(Box::new(key)),
                                    };
                                    if let Some(g) = getter {
                                        out.push(ObjEntry::Getter(k.clone(), g));
                                    }
                                    if let Some(st) = setter {
                                        out.push(ObjEntry::Setter(k, st));
                                    }
                                }
                                Absorb::ArrItem(_) | Absorb::ArrSpread(_) => {
                                    unreachable!("object fold absorbed an array entry")
                                }
                            }
                        }
                        Expr::ObjectBuild { entries: out }
                    }
                    Expr::ArrayLit { elements } => {
                        let mut out: Vec<ArrayElem> = std::mem::take(elements)
                            .into_iter()
                            .map(|e| ArrayElem::Item(Expr::Lit(e)))
                            .collect();
                        for a in absorbed {
                            match a {
                                Absorb::ArrItem(v) => out.push(ArrayElem::Item(v)),
                                Absorb::ArrSpread(s) => out.push(ArrayElem::Spread(s)),
                                _ => unreachable!("array fold absorbed an object entry"),
                            }
                        }
                        Expr::ArrayBuild { elements: out }
                    }
                    _ => unreachable!("filtered above"),
                };
                Leaf::Raw(Stmt::Declare {
                    name,
                    mutable,
                    value: folded,
                    value_id,
                })
            }
            other => other,
        };
        // Remove the absorbed AND skipped statements by index
        // (descending; the `leaves.remove(i)` above shifted everything
        // past `i` down by one), then re-seat the skipped declares that
        // survived immediately above the folded declaration.
        let mut gone: Vec<usize> = absorbed_idx
            .iter()
            .chain(skipped_idx.iter())
            .map(|x| x - 1)
            .collect();
        gone.sort_unstable_by(|a, b| b.cmp(a));
        for idx in gone {
            leaves.remove(idx);
        }
        leaves.insert(i, new_value);
        i += 1;
    }
}

/// One absorbed builder statement.
pub(in crate::folds) enum Absorb {
    ObjKV(Lit, Expr),
    ObjComputed(Expr, Expr),
    ObjSpread(Expr),
    ObjProto(Expr),
    ObjMethod(String, Expr),
    /// A `DefineGetterSetterByValue` against the object being built
    /// (N74-W4) — key + optional getter/setter closures. Folding it
    /// into the literal is BOTH more idiomatic and the only form whose
    /// accessors carry a [[HomeObject]] (super-using bodies) — and the
    /// literal's accessors are enumerable like the source's (the
    /// defineProperty emission's `enumerable: false` default was not).
    ObjAccessors {
        key: Expr,
        getter: Option<Expr>,
        setter: Option<Expr>,
    },
    ArrItem(Expr),
    ArrSpread(Expr),
}

/// The expression positions of an absorbed builder statement
/// (immutable — the use census).
pub(in crate::folds) fn absorb_exprs(a: &Absorb) -> Vec<&Expr> {
    match a {
        Absorb::ObjKV(_, v) => vec![v],
        Absorb::ObjComputed(k, v) => vec![k, v],
        Absorb::ObjSpread(s) | Absorb::ObjProto(s) => vec![s],
        Absorb::ObjMethod(_, f) => vec![f],
        Absorb::ObjAccessors {
            key,
            getter,
            setter,
        } => {
            let mut out = vec![key];
            out.extend(getter.iter());
            out.extend(setter.iter());
            out
        }
        Absorb::ArrItem(v) | Absorb::ArrSpread(v) => vec![v],
    }
}

/// The mutable counterpart of [`absorb_exprs`] (the inline rewrite).
pub(in crate::folds) fn absorb_exprs_mut(a: &mut Absorb) -> Vec<&mut Expr> {
    match a {
        Absorb::ObjKV(_, v) => vec![v],
        Absorb::ObjComputed(k, v) => vec![k, v],
        Absorb::ObjSpread(s) | Absorb::ObjProto(s) => vec![s],
        Absorb::ObjMethod(_, f) => vec![f],
        Absorb::ObjAccessors {
            key,
            getter,
            setter,
        } => {
            let mut out = vec![key];
            out.extend(getter.iter_mut());
            out.extend(setter.iter_mut());
            out
        }
        Absorb::ArrItem(v) | Absorb::ArrSpread(v) => vec![v],
    }
}

/// How often an expression references a temp by SSA value (`O(|Expr|)`
/// iterative stack walk, `#87.3`).
pub(in crate::folds) fn expr_count_value(e: &Expr, vid: abcd_ir::ValueId) -> usize {
    let mut n = 0usize;
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        if temp_value(cur) == Some(vid) {
            n += 1;
        }
        stack.extend(expr_children(cur));
    }
    n
}

fn expr_root_is_pure_for_lit(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Lit(_)
            | Expr::Temp { .. }
            | Expr::Closure { .. }
            | Expr::RegExp { .. }
            | Expr::ObjectLit { .. }
            | Expr::ArrayLit { .. }
            | Expr::Arguments
            | Expr::NewTarget
            | Expr::GlobalThis
            | Expr::SelfFunction(_)
            | Expr::SuperMarker
            | Expr::ModuleNamespace { .. }
            | Expr::Unary {
                op: abcd_ir::op::UnOp::LogicalNot
                    | abcd_ir::op::UnOp::IsTrue
                    | abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::Void
                    | abcd_ir::op::UnOp::JumpEqz
                    | abcd_ir::op::UnOp::JumpNez,
                ..
            }
            | Expr::Compare {
                op: abcd_ir::op::CmpOp::StrictEq | abcd_ir::op::CmpOp::StrictNotEq,
                ..
            }
    )
}

/// Verify that inlining skipped `Declare`s into `absorbed` preserves the
/// original leaf execution order of all non-pure expressions (`#87.3`).
fn literal_eval_order_ok(
    absorbed: &[Absorb],
    absorbed_idx: &[usize],
    inline: &[(abcd_ir::ValueId, Expr, usize)],
) -> bool {
    let inline_map: std::collections::HashMap<abcd_ir::ValueId, (&Expr, usize)> = inline
        .iter()
        .map(|(vid, expr, orig_j)| (*vid, (expr, *orig_j)))
        .collect();
    let mut last_effect_idx = 0usize;

    for (m, a) in absorbed.iter().enumerate() {
        let abs_j = absorbed_idx[m];
        for root_expr in absorb_exprs(a) {
            // Explicit post-order stack: `(expr, owner_leaf_idx, expanded)`.
            let mut stack: Vec<(&Expr, usize, bool)> = vec![(root_expr, abs_j, false)];
            let mut active_inlines: std::collections::HashSet<abcd_ir::ValueId> =
                std::collections::HashSet::new();
            let mut unmark_stack: Vec<abcd_ir::ValueId> = Vec::new();

            while let Some((cur, owner_j, expanded)) = stack.pop() {
                if expanded {
                    if let Some(vid) = temp_value(cur)
                        && inline_map.contains_key(&vid)
                    {
                        if let Some(done_vid) = unmark_stack.pop() {
                            active_inlines.remove(&done_vid);
                        }
                        continue;
                    }
                    if !expr_root_is_pure_for_lit(cur) {
                        if owner_j < last_effect_idx {
                            return false;
                        }
                        last_effect_idx = owner_j;
                    }
                    continue;
                }

                if let Some(vid) = temp_value(cur)
                    && let Some(&(inlined_expr, inlined_j)) = inline_map.get(&vid)
                    && active_inlines.insert(vid)
                {
                    unmark_stack.push(vid);
                    stack.push((cur, owner_j, true));
                    stack.push((inlined_expr, inlined_j, false));
                    continue;
                }

                stack.push((cur, owner_j, true));
                let children = expr_children(cur);
                for child in children.into_iter().rev() {
                    stack.push((child, owner_j, false));
                }
            }
        }
    }
    true
}

/// Whether leaf `l` is a builder statement targeting temp `vid` that
/// can be absorbed (self-reference-free). `shape_len` is the array
/// shape's own element count (0 for objects) — the array absorb index
/// is checked against `shape_len + <absorbed items>` exactly.
pub(in crate::folds) fn absorb_one(
    l: &Leaf,
    vid: abcd_ir::ValueId,
    is_array: bool,
    so_far: &[Absorb],
    shape_len: u64,
) -> Option<Absorb> {
    let is_target = |e: &Expr| temp_value(e) == Some(vid);
    let clean = |e: &Expr| !expr_uses_value(e, vid);
    match l {
        Leaf::Raw(Stmt::StoreProp {
            object,
            name,
            value,
            own: true,
            ..
        }) if !is_array && is_target(object) && clean(value) => {
            Some(Absorb::ObjKV(Lit::String(name.clone()), value.clone()))
        }
        Leaf::Raw(Stmt::StoreDyn {
            object,
            key,
            value,
            own: true,
        }) if !is_array && is_target(object) && clean(key) && clean(value) => Some(match key {
            Expr::Lit(l @ (Lit::String(_) | Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_))) => {
                Absorb::ObjKV(l.clone(), value.clone())
            }
            _ => Absorb::ObjComputed(key.clone(), value.clone()),
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object,
            index,
            value,
            own,
        }) if is_target(object) && clean(index) && clean(value) => {
            if is_array {
                // Strict contiguity (N74-W4): the store's integer index
                // must be EXACTLY the next slot — shape elements plus
                // already-absorbed items. Anything else (a hole gap, an
                // out-of-order store) stays a statement, which preserves
                // the sparse semantics the literal form would destroy.
                // A spread makes the running index unknowable — absorb
                // no items after one.
                let base = match &index {
                    Expr::Lit(Lit::Number(bits)) => {
                        let v = f64::from_bits(*bits);
                        (v.fract() == 0.0 && v >= 0.0).then_some(v as u64)
                    }
                    Expr::Lit(Lit::Int64(v)) => u64::try_from(*v).ok(),
                    Expr::Lit(Lit::UInt64(v)) => Some(*v),
                    _ => None,
                };
                let next = if so_far.iter().any(|a| matches!(a, Absorb::ArrSpread(_))) {
                    None
                } else {
                    Some(
                        shape_len
                            + so_far
                                .iter()
                                .filter(|a| matches!(a, Absorb::ArrItem(_)))
                                .count() as u64,
                    )
                };
                match base {
                    Some(idx) if *own && Some(idx) == next => Some(Absorb::ArrItem(value.clone())),
                    _ => None,
                }
            } else if *own {
                match index {
                    Expr::Lit(
                        l @ (Lit::String(_) | Lit::Number(_) | Lit::Int64(_) | Lit::UInt64(_)),
                    ) => Some(Absorb::ObjKV(l.clone(), value.clone())),
                    _ => Some(Absorb::ObjComputed(index.clone(), value.clone())),
                }
            } else {
                None
            }
        }
        Leaf::Raw(Stmt::Expr(Expr::CopyDataProps { dst, src }))
            if !is_array && is_target(dst) && clean(src) =>
        {
            Some(Absorb::ObjSpread(src.as_ref().clone()))
        }
        Leaf::Raw(Stmt::Expr(Expr::SetObjectWithProto { obj, proto }))
            if !is_array && is_target(obj) && clean(proto) =>
        {
            Some(Absorb::ObjProto(proto.as_ref().clone()))
        }
        Leaf::Raw(Stmt::Expr(Expr::ArraySpread { dst, src, .. }))
            if is_array && is_target(dst) && clean(src) =>
        {
            Some(Absorb::ArrSpread(src.as_ref().clone()))
        }
        Leaf::Raw(Stmt::DefineMethod {
            object, name, func, ..
        }) if !is_array && is_target(object) && clean(func) => {
            Some(Absorb::ObjMethod(name.clone(), func.clone()))
        }
        // Accessor definition against the object being built. The
        // getter/setter slots must be closures or the `undefined`
        // absence marker (the recover.rs undef-through resolution).
        Leaf::Raw(Stmt::Expr(Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        })) if !is_array
            && is_target(obj)
            && clean(key)
            && clean(getter)
            && clean(setter)
            && matches!(
                getter.as_ref(),
                Expr::Closure { .. } | Expr::Lit(Lit::Undefined)
            )
            && matches!(
                setter.as_ref(),
                Expr::Closure { .. } | Expr::Lit(Lit::Undefined)
            ) =>
        {
            let getter = match getter.as_ref() {
                Expr::Lit(Lit::Undefined) => None,
                g => Some(g.clone()),
            };
            let setter = match setter.as_ref() {
                Expr::Lit(Lit::Undefined) => None,
                st => Some(st.clone()),
            };
            if getter.is_none() && setter.is_none() {
                return None;
            }
            Some(Absorb::ObjAccessors {
                key: key.as_ref().clone(),
                getter,
                setter,
            })
        }
        _ => None,
    }
}

// ── Fold 2: rest destructuring ───────────────────────────────────────

pub(in crate::folds) fn fold_rest_destructure(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    let mut i = 0;
    while i < leaves.len() {
        let (rest_name, obj, keys) = match &leaves[i] {
            Leaf::Raw(Stmt::Declare {
                name,
                value: Expr::RestObject { obj, excluded },
                ..
            }) => {
                let keys: Option<Vec<String>> = excluded
                    .iter()
                    .map(|k| match k {
                        Expr::Lit(Lit::String(s)) => Some(s.clone()),
                        Expr::Unary {
                            op: abcd_ir::op::UnOp::ToPropertyKey,
                            operand,
                        } => match operand.as_ref() {
                            Expr::Lit(Lit::String(s)) => Some(s.clone()),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect();
                match keys {
                    Some(keys) if !keys.is_empty() => (name.clone(), obj.as_ref().clone(), keys),
                    _ => {
                        i += 1;
                        continue;
                    }
                }
            }
            _ => {
                i += 1;
                continue;
            }
        };
        // `obj` must be a repeatable pure reference, and excluded keys must not
        // contain duplicates (duplicate indices in `drop` would shift/panic).
        if !matches!(obj, Expr::Temp { .. } | Expr::Ident(_)) {
            i += 1;
            continue;
        }
        let mut seen_keys = BTreeSet::new();
        if keys.iter().any(|k| !seen_keys.insert(k.as_str())) {
            i += 1;
            continue;
        }
        // Find one distinct sibling declare per excluded key: `const t = obj.k`
        // (or `obj["k"]`) with a structurally equal object expression.
        let mut found: Vec<(usize, String, String, ValueId)> = Vec::new();
        let mut used_indices = BTreeSet::new();
        let mut ok = true;
        for key in &keys {
            let hit = leaves.iter().enumerate().find(|(idx, l)| {
                *idx != i
                    && !used_indices.contains(idx)
                    && matches!(l, Leaf::Raw(Stmt::Declare { value, .. }) if key_load_target(value, &obj) == Some(key))
            });
            match hit {
                Some((idx, Leaf::Raw(Stmt::Declare { name, value_id, .. }))) => {
                    used_indices.insert(idx);
                    found.push((idx, key.clone(), name.clone(), *value_id));
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            i += 1;
            continue;
        }
        let span_lo = used_indices.iter().copied().min().unwrap_or(i).min(i);
        let span_hi = used_indices.iter().copied().max().unwrap_or(i).max(i);
        for (m, leaf_m) in leaves.iter().enumerate().take(span_hi + 1).skip(span_lo) {
            if m == i || used_indices.contains(&m) {
                continue;
            }
            if !is_pure_intervening_for_rest(leaf_m) {
                ok = false;
                break;
            }
            // Any matched load at `d < m < i` moves down to `i`, so `leaf_m`
            // must not read its temporary/name before `i` (TDZ / ordering).
            if m < i {
                let reads_moved = found.iter().any(|(d, _, tname, tvid)| {
                    *d < m && leaf_mentions_temp_or_ident(leaf_m, *tvid, tname)
                });
                if reads_moved {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            i += 1;
            continue;
        }
        stats.rest += 1;
        let pairs: Vec<(String, String)> = found
            .iter()
            .map(|(_, k, t, _)| (k.clone(), t.clone()))
            .collect();
        let mut drop: Vec<usize> = found.iter().map(|(idx, _, _, _)| *idx).collect();
        drop.sort_unstable_by(|a, b| b.cmp(a));
        for d in drop {
            leaves.remove(d);
            if d < i {
                i -= 1;
            }
        }
        leaves[i] = Leaf::Destructure {
            obj,
            keys: pairs,
            rest: rest_name,
        };
        i += 1;
    }
}

fn is_pure_intervening_for_rest(l: &Leaf) -> bool {
    match l {
        Leaf::Raw(Stmt::Elided { .. }) => true,
        Leaf::Raw(Stmt::Declare { value, .. })
        | Leaf::Decl {
            value: Some(value), ..
        } => {
            let mut stack = vec![value];
            while let Some(cur) = stack.pop() {
                if !expr_root_is_pure_for_lit(cur) {
                    return false;
                }
                stack.extend(expr_children(cur));
            }
            true
        }
        Leaf::Decl { value: None, .. } => true,
        _ => false,
    }
}

fn leaf_mentions_temp_or_ident(l: &Leaf, vid: ValueId, ident: &str) -> bool {
    for e in leaf_exprs(l) {
        let mut stack = vec![e];
        while let Some(cur) = stack.pop() {
            match cur {
                Expr::Temp { value, name } if *value == vid || name == ident => return true,
                Expr::Ident(n) if n == ident => return true,
                _ => {}
            }
            stack.extend(expr_children(cur));
        }
    }
    false
}

/// The key a `obj.k` / `obj["k"]` load extracts, when `value` is such
/// a load on `obj`.
pub(in crate::folds) fn key_load_target<'v>(value: &'v Expr, obj: &Expr) -> Option<&'v String> {
    let lit_str = |e: &'v Expr| match e {
        Expr::Lit(Lit::String(s)) => Some(s),
        Expr::Unary {
            op: abcd_ir::op::UnOp::ToPropertyKey,
            operand,
        } => match operand.as_ref() {
            Expr::Lit(Lit::String(s)) => Some(s),
            _ => None,
        },
        _ => None,
    };
    match value {
        Expr::PropName { object, name, .. } if object.as_ref() == obj => Some(name),
        Expr::PropDyn { object, key } if object.as_ref() == obj => lit_str(key),
        Expr::PropIndex { object, index } if object.as_ref() == obj => lit_str(index),
        _ => None,
    }
}
