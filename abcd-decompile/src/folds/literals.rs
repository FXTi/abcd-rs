//! Object/array literal builders, tagged-template folds, and rest destructuring.

use super::*;
use crate::folds::loops::subst_temp_in_expr;

// ── Fold 1: literal builders ─────────────────────────────────────────

pub(in crate::folds) fn fold_leaves(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
    fold_rest_destructure(leaves, stats);
    fold_literal_builders(leaves, stats);
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
    if let Expr::Temp { value, .. } = e {
        *counts.entry(*value).or_insert(0) += 1;
    }
    for c in expr_children(e) {
        collect_value_uses_in_expr(c, counts);
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
    for n in nodes {
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
                collect_value_uses_in_snodes(then, counts);
                collect_value_uses_in_snodes(otherwise, counts);
            }
            SNode::While { cond, body, .. } => {
                if let Some(c) = cond {
                    collect_value_uses_in_expr(c, counts);
                }
                collect_value_uses_in_snodes(body, counts);
            }
            SNode::DoWhile { cond, body, .. } => {
                collect_value_uses_in_expr(cond, counts);
                collect_value_uses_in_snodes(body, counts);
            }
            SNode::ForOf { iter, body, .. } => {
                collect_value_uses_in_expr(iter, counts);
                collect_value_uses_in_snodes(body, counts);
            }
            SNode::ForIn { obj, body, .. } => {
                collect_value_uses_in_expr(obj, counts);
                collect_value_uses_in_snodes(body, counts);
            }
            SNode::Switch { disc, cases, .. } => {
                collect_value_uses_in_expr(disc, counts);
                for c in cases {
                    for t in &c.tests {
                        collect_value_uses_in_expr(t, counts);
                    }
                    collect_value_uses_in_snodes(&c.body, counts);
                }
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                collect_value_uses_in_snodes(body, counts);
                for c in catches {
                    collect_value_uses_in_snodes(&c.body, counts);
                }
                if let Some(fin) = finally {
                    collect_value_uses_in_snodes(fin, counts);
                }
            }
            SNode::Labeled { body, .. } => collect_value_uses_in_snodes(body, counts),
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
}

pub(in crate::folds) fn fold_tagged_in_snodes(
    nodes: &mut [SNode],
    use_counts: &std::collections::HashMap<ValueId, usize>,
) {
    for n in nodes.iter_mut() {
        match n {
            SNode::Stmts(leaves) => fold_tagged_in_leaves(leaves, use_counts),
            SNode::If {
                then, otherwise, ..
            } => {
                fold_tagged_in_snodes(then, use_counts);
                fold_tagged_in_snodes(otherwise, use_counts);
            }
            SNode::While { body, .. }
            | SNode::DoWhile { body, .. }
            | SNode::ForOf { body, .. }
            | SNode::ForIn { body, .. }
            | SNode::Labeled { body, .. } => fold_tagged_in_snodes(body, use_counts),
            SNode::Switch { cases, .. } => {
                for c in cases {
                    fold_tagged_in_snodes(&mut c.body, use_counts);
                }
            }
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                fold_tagged_in_snodes(body, use_counts);
                for c in catches {
                    fold_tagged_in_snodes(&mut c.body, use_counts);
                }
                if let Some(fin) = finally {
                    fold_tagged_in_snodes(fin, use_counts);
                }
            }
            SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
        }
    }
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
    if let Expr::Call {
        callee,
        this,
        args,
        kind: abcd_ir::op::CallKind::Direct | abcd_ir::op::CallKind::Dynamic,
    } = e
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
                        *e = Expr::TaggedTemplate {
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
                    *e = Expr::TaggedTemplate {
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
                        *e = Expr::TaggedTemplate {
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
    for child in expr_children_mut(e) {
        if let Some(res) = try_rewrite_tagged_call_in_expr(
            child,
            tpl_vid,
            quasis,
            prior_leaves,
            intervening_leaves,
            use_counts,
        ) {
            return Some(res);
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

pub(in crate::folds) fn fold_literal_builders(leaves: &mut Vec<Leaf>, stats: &mut FoldStats) {
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
            let mut inline: Vec<(abcd_ir::ValueId, Expr)> = Vec::new();
            for k in 0..skip_vals.len() {
                let (vid, value, _) = &skip_vals[k];
                let (vid, is_lit, value) = (*vid, matches!(value, Expr::Lit(_)), value.clone());
                match count_uses(vid, &absorbed, &skip_vals) {
                    0 if is_lit => skip_vals[k].2 = false, // dead pure: drop
                    1 => {
                        inline.push((vid, value));
                        skip_vals[k].2 = false;
                    }
                    // Multi-use or used elsewhere: reordering the
                    // declare is unprovable — bail the WHOLE fold
                    // (nothing is mutated yet).
                    _ => {
                        bail = true;
                    }
                }
            }
            // Inline in decision order: an earlier inline may feed a
            // later one (temp chains), so substitute into the later
            // inline values too.
            for pos in 0..inline.len() {
                let (vid, value) = inline[pos].clone();
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
                value,
                value_id,
            }) => {
                let folded = match value {
                    Expr::ObjectLit { entries } => {
                        let mut out: Vec<ObjEntry> = entries
                            .into_iter()
                            .map(|(k, v)| ObjEntry::KeyValue(k, Expr::Lit(v)))
                            .collect();
                        for a in absorbed {
                            match a {
                                Absorb::ObjKV(k, v) => out.push(ObjEntry::KeyValue(k, v)),
                                Absorb::ObjComputed(k, v) => out.push(ObjEntry::Computed(k, v)),
                                Absorb::ObjSpread(s) => out.push(ObjEntry::Spread(s)),
                                Absorb::ObjProto(p) => out.push(ObjEntry::Proto(p)),
                                Absorb::ObjMethod(n, f) => out.push(ObjEntry::Method(n, f)),
                                Absorb::ObjAccessors {
                                    key,
                                    getter,
                                    setter,
                                } => {
                                    let k = match key {
                                        Expr::Lit(Lit::String(s)) => crate::expr::ObjKey::Name(s),
                                        other => crate::expr::ObjKey::Computed(Box::new(other)),
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
                        let mut out: Vec<ArrayElem> = elements
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

/// How often an expression references a temp by SSA value.
pub(in crate::folds) fn expr_count_value(e: &Expr, vid: abcd_ir::ValueId) -> usize {
    let mut n = usize::from(expr_uses_value(e, vid) && temp_value(e) == Some(vid));
    for c in expr_children(e) {
        n += expr_count_value(c, vid);
    }
    n
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
            Expr::Lit(l @ (Lit::String(_) | Lit::Number(_))) => {
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
                    Expr::Lit(l @ (Lit::String(_) | Lit::Number(_))) => {
                        Some(Absorb::ObjKV(l.clone(), value.clone()))
                    }
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
        // Find one sibling declare per excluded key: `const t = obj.k`
        // (or `obj["k"]`) with a structurally equal object expression.
        let mut found: Vec<(usize, String, String)> = Vec::new(); // (leaf idx, key, target)
        let mut ok = true;
        for key in &keys {
            let hit = leaves.iter().enumerate().find(|(idx, l)| {
                *idx != i
                    && matches!(l, Leaf::Raw(Stmt::Declare { value, .. }) if key_load_target(value, &obj) == Some(key))
            });
            match hit {
                Some((idx, Leaf::Raw(Stmt::Declare { name, .. }))) => {
                    found.push((idx, key.clone(), name.clone()))
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
        stats.rest += 1;
        let pairs: Vec<(String, String)> = found
            .iter()
            .map(|(_, k, t)| (k.clone(), t.clone()))
            .collect();
        let mut drop: Vec<usize> = found.iter().map(|(idx, _, _)| *idx).collect();
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

/// The key a `obj.k` / `obj["k"]` load extracts, when `value` is such
/// a load on `obj`.
pub(in crate::folds) fn key_load_target<'v>(value: &'v Expr, obj: &Expr) -> Option<&'v String> {
    match value {
        Expr::PropName { object, name, .. } if object.as_ref() == obj => Some(name),
        Expr::PropDyn { object, key } if object.as_ref() == obj => match key.as_ref() {
            Expr::Lit(Lit::String(s)) => Some(s),
            _ => None,
        },
        Expr::PropIndex { object, index } if object.as_ref() == obj => match index.as_ref() {
            Expr::Lit(Lit::String(s)) => Some(s),
            _ => None,
        },
        _ => None,
    }
}
