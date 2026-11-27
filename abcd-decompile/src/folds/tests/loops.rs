//! Iterator-loop (`for..of`, `for..in`, `for await..of`) and loop-test fold unit tests.

use super::*;

#[test]
fn for_of_fold_positive_and_normalized_test_form() {
    let mut nodes = for_of_site();
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_of, 1);
    assert_eq!(
        nodes,
        vec![SNode::ForOf {
            is_await: false,
            binding: "v".to_string(),
            iter: ident("src"),
            body: vec![run(vec![expr_stmt(call1(ident("print"), tm("v", 26)))])],
        }]
    );
    // The `while (true) { wiring; if (t) break; … }` emission form
    // normalizes to the same fold: the loop test becomes an
    // `if (done) break` after the header wiring run.
    let mut nodes = for_of_site();
    let SNode::While { body, cond, .. } = &mut nodes[1] else {
        unreachable!()
    };
    let test_if = if_node(
        cond.take().unwrap(),
        vec![SNode::Break { label: None }],
        vec![],
    );
    body.insert(1, test_if);
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_of, 1);
    assert!(matches!(&nodes[0], SNode::ForOf { .. }));
    // An async iterator marks the folded loop `for await…of`.
    let mut nodes = for_of_site();
    let SNode::Stmts(pre) = &mut nodes[0] else {
        unreachable!()
    };
    pre[0] = decl(
        "it",
        10,
        Expr::Iter {
            op: IterOp::GetAsyncIterator,
            obj: bx(ident("src")),
            status: NodeStatus::Plumbing,
        },
    );
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_await_of, 1);
    assert!(matches!(&nodes[0], SNode::ForOf { is_await: true, .. }));
}

#[test]
fn for_of_match_bail_pins() {
    let site = for_of_site();
    let (pre, wcond, body) = {
        let SNode::While { cond, body, .. } = &site[1] else {
            unreachable!()
        };
        let pre = match &site[0] {
            SNode::Stmts(l) => l.clone(),
            _ => unreachable!(),
        };
        (pre, cond.clone().unwrap(), body.clone())
    };
    assert!(match_for_of(&pre, &wcond, &body).is_some());
    // Truncated pre-run: no room for the iterator pair.
    assert!(match_for_of(&pre[..1], &wcond, &body).is_none());
    // The iterator declare must be GetIterator/GetAsyncIterator.
    let mut bad = pre.clone();
    bad[0] = decl("it", 10, ident("notiter"));
    assert!(match_for_of(&bad, &wcond, &body).is_none());
    // The `next` declare must load `.next` off the iterator.
    let mut bad = pre.clone();
    bad[1] = decl("next", 11, prop(tm("it", 10), "previous"));
    assert!(match_for_of(&bad, &wcond, &body).is_none());
    // The header must be a statement run.
    let mut bbody = body.clone();
    bbody[0] = SNode::Honest("h".to_string());
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    // … and carry at least one phi.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr.remove(0);
    hdr.remove(0);
    // (phi decls removed; res call's callee is then no phi)
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    // The res call must be an argument-free call of a header phi.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr[2] = decl("res", 23, call1(tm("np", 20), ident("x")));
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr[2] = decl("res", 23, call0(tm("other", 99)));
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    // Elided guards between the call and the done decl are skipped.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr.insert(3, elided("Guard"));
    assert!(match_for_of(&pre, &wcond, &bbody).is_some());
    // The done decl must read `.done` off the res temp.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr[3] = decl("done", 25, prop(tm("res", 23), "finished"));
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    // Trailing header junk bails.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr.push(expr_stmt(ident("extra")));
    assert!(match_for_of(&pre, &wcond, &bbody).is_none());
    // The while test must be the done temp (wrappers stripped).
    assert!(match_for_of(&pre, &isfalse(tm("done", 25)), &body).is_some());
    assert!(match_for_of(&pre, &ident("other"), &body).is_none());
    assert!(match_for_of(&pre, &num(1.0), &body).is_none());
    // The pre-loop assigns must wire `next` into the call's phi.
    let mut bad = pre.clone();
    bad[2] = phi_assign("np", tm("it", 10));
    assert!(match_for_of(&bad, &wcond, &body).is_none());
}

#[test]
fn for_in_fold_positive_with_hoisted_phi_and_copy_elimination() {
    let mut nodes = for_in_site();
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_in, 1);
    // The pass-through phi's wiring is hoisted above the loop.
    assert_eq!(
        nodes[0],
        run(vec![
            phi_decl("xp", 21),
            phi_assign("xp", ident("invariant"))
        ])
    );
    let SNode::ForIn { binding, obj, body } = &nodes[1] else {
        panic!("expected ForIn: {nodes:?}")
    };
    assert_eq!(binding, "k");
    assert_eq!(obj, &ident("src"));
    // The copy-phi chain and self-assigns are gone.
    assert_eq!(
        body.as_slice(),
        [
            run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
            if_node(ident("c"), vec![], vec![]),
        ]
    );
}

#[test]
fn for_in_match_bail_pins() {
    let site = for_in_site();
    let (pre, wcond, body) = {
        let SNode::While { cond, body, .. } = &site[1] else {
            unreachable!()
        };
        let pre = match &site[0] {
            SNode::Stmts(l) => l.clone(),
            _ => unreachable!(),
        };
        (pre, cond.clone().unwrap(), body.clone())
    };
    assert!(match_for_in(&pre, &wcond, &body).is_some());
    // Header: phi decls then exactly the NextPropName declare.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr.push(expr_stmt(ident("extra")));
    assert!(match_for_in(&pre, &wcond, &bbody).is_none());
    // NextPropName must read a header phi.
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr[2] = decl(
        "k",
        31,
        Expr::Iter {
            op: IterOp::NextPropName,
            obj: bx(tm("other", 99)),
            status: NodeStatus::Plumbing,
        },
    );
    assert!(match_for_in(&pre, &wcond, &bbody).is_none());
    // Every header phi needs exactly one wiring assign.
    let mut bad = pre.clone();
    bad.remove(1);
    assert!(match_for_in(&bad, &wcond, &body).is_none());
    // The iterator phi's value must be the GetPropIterator.
    let mut bad = pre.clone();
    bad[0] = phi_assign("ip", ident("src"));
    assert!(match_for_in(&bad, &wcond, &body).is_none());
    // An extra phi's initial value must not reference the internals.
    let mut bad = pre.clone();
    bad[1] = phi_assign("xp", tm("ip", 20));
    assert!(match_for_in(&bad, &wcond, &body).is_none());
    // The condition must be `undefined == k` (either order/op).
    assert!(match_for_in(&pre, &cmp(CmpOp::NotEq, tm("k", 31), undef()), &body).is_some());
    assert!(match_for_in(&pre, &cmp(CmpOp::Eq, ident("u"), tm("k", 31)), &body).is_none());
    assert!(match_for_in(&pre, &ident("k"), &body).is_none());
}

#[test]
fn elim_internal_copy_phis_bail_pins() {
    let mut roots: BTreeMap<String, Expr> = BTreeMap::new();
    roots.insert("r".to_string(), tm("r", 60));
    // A phi with a non-temp source is not a copy.
    let mut out = vec![run(vec![
        phi_decl("cp", 40),
        phi_assign("cp", num(1.0)),
        expr_stmt(tm("cp", 40)),
    ])];
    elim_internal_copy_phis(&mut out, &roots);
    assert!(nodes_use_any(&out, &["cp".to_string()]));
    // Sources resolving to different roots disqualify the phi.
    roots.insert("s".to_string(), tm("s", 61));
    let mut out = vec![run(vec![
        phi_decl("cp", 40),
        phi_assign("cp", tm("r", 60)),
        phi_assign("cp", tm("s", 61)),
    ])];
    elim_internal_copy_phis(&mut out, &roots);
    let SNode::Stmts(kept) = &out[0] else {
        unreachable!()
    };
    assert!(kept.len() == 3, "not a copy: {kept:?}");
    // An assign-less phi is skipped entirely.
    let mut out = vec![run(vec![phi_decl("cp", 40)])];
    elim_internal_copy_phis(&mut out, &roots);
    assert_eq!(out.len(), 1);
    // drop_self_assign_tail shapes.
    let mut out: Vec<SNode> = vec![];
    drop_self_assign_tail(&mut out);
    let mut out = vec![SNode::Continue { label: None }];
    drop_self_assign_tail(&mut out);
    assert_eq!(out.len(), 1);
    let mut out = vec![run(vec![phi_assign("q", ident("z"))])];
    drop_self_assign_tail(&mut out);
    assert_eq!(out.len(), 1, "not a self-assign run");
    let mut out = vec![
        run(vec![expr_stmt(ident("a"))]),
        run(vec![phi_assign("q", tm("q", 5))]),
        SNode::Break { label: None },
    ];
    drop_self_assign_tail(&mut out);
    assert_eq!(out.len(), 2, "the self-assign run before a break drops");
    // take_value_declare: only a leading `.value` load declare.
    let mut leaves = vec![decl("v", 1, prop(tm("res", 2), "value"))];
    assert_eq!(
        take_value_declare(&mut leaves, "res"),
        Some("v".to_string())
    );
    assert!(leaves.is_empty());
    let mut leaves = vec![decl("v", 1, prop(tm("res", 2), "other"))];
    assert_eq!(take_value_declare(&mut leaves, "res"), None);
}

#[test]
fn single_pass_for_in_positive_and_bail_pins() {
    let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_in, 1);
    // The assign run survives (its other leaves stay); the folded
    // ForIn replaces the header run + exit test.
    assert!(matches!(&nodes[0], SNode::Stmts(_)));
    let SNode::ForIn { binding, obj, body } = &nodes[1] else {
        panic!("expected ForIn: {nodes:?}")
    };
    assert_eq!(binding, "k");
    assert_eq!(obj, &ident("src"));
    // The non-diverging one-shot body gains a trailing break.
    assert_eq!(body.last(), Some(&SNode::Break { label: None }), "{body:?}");
    // Polarity variants: NotEq puts the body on the then arm.
    let mut site = single_pass_for_in_site(cmp(CmpOp::NotEq, tm("k", 31), undef()));
    let SNode::If {
        then, otherwise, ..
    } = &mut site[2]
    else {
        unreachable!()
    };
    let body_nodes = std::mem::take(otherwise);
    *then = body_nodes;
    assert!(match_single_pass_for_in(&site, 1).is_some());
    // Wrapped tests (isfalse/isnot invert the arms).
    let mut site = single_pass_for_in_site(isfalse(cmp(CmpOp::Eq, tm("k", 31), undef())));
    let SNode::If {
        then, otherwise, ..
    } = &mut site[2]
    else {
        unreachable!()
    };
    let body_nodes = std::mem::take(otherwise);
    *then = body_nodes;
    assert!(match_single_pass_for_in(&site, 1).is_some());
    let site = single_pass_for_in_site(istrue(cmp(CmpOp::StrictEq, undef(), tm("k", 31))));
    assert!(match_single_pass_for_in(&site, 1).is_some());

    let good = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
    // The header must be exactly [PhiDecl it, NextPropName declare].
    let mut bad = good.clone();
    bad[1] = SNode::Honest("h".to_string());
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    let mut bad = good.clone();
    let SNode::Stmts(hdr) = &mut bad[1] else {
        unreachable!()
    };
    hdr.push(expr_stmt(ident("x")));
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // The NextPropName must read the phi-declared iterator.
    let mut bad = good.clone();
    let SNode::Stmts(hdr) = &mut bad[1] else {
        unreachable!()
    };
    hdr[1] = decl(
        "k",
        31,
        Expr::Iter {
            op: IterOp::NextPropName,
            obj: bx(tm("other", 99)),
            status: NodeStatus::Plumbing,
        },
    );
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // There must be a previous non-Honest statement run…
    assert!(match_single_pass_for_in(&good[1..], 0).is_none());
    // … whose last leaf is the GetPropIterator phi-assign…
    let mut bad = good.clone();
    bad[0] = SNode::Honest("h".to_string());
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    let mut bad = good.clone();
    let SNode::Stmts(pre) = &mut bad[0] else {
        unreachable!()
    };
    pre[1] = phi_assign("it", ident("src"));
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // … targeting the same iterator temp.
    let mut bad = good.clone();
    let SNode::Stmts(pre) = &mut bad[0] else {
        unreachable!()
    };
    pre[1] = phi_assign(
        "other",
        Expr::Iter {
            op: IterOp::GetPropIterator,
            obj: bx(ident("src")),
            status: NodeStatus::Plumbing,
        },
    );
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // The exit test must be an if…
    let mut bad = good.clone();
    bad[2] = SNode::Honest("h".to_string());
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // … a compare against undefined …
    let mut bad = good.clone();
    bad[2] = if_node(ident("k"), vec![], vec![run(vec![])]);
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    let mut bad = good.clone();
    bad[2] = if_node(cmp(CmpOp::Eq, ident("u"), ident("v")), vec![], vec![]);
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // … with the body on the not-done arm and the other arm empty.
    let mut bad = good.clone();
    bad[2] = if_node(
        cmp(CmpOp::Eq, tm("k", 31), undef()),
        vec![run(vec![expr_stmt(ident("x"))])],
        vec![run(vec![expr_stmt(ident("y"))])],
    );
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // The iterated expression must not reference the internals.
    let mut bad = good.clone();
    let SNode::Stmts(pre) = &mut bad[0] else {
        unreachable!()
    };
    pre[1] = phi_assign(
        "it",
        Expr::Iter {
            op: IterOp::GetPropIterator,
            obj: bx(tm("k", 31)),
            status: NodeStatus::Plumbing,
        },
    );
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // Nothing outside the matched trio may use the internals.
    let mut bad = good.clone();
    bad.push(run(vec![expr_stmt(tm("k", 31))]));
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // The assign run's earlier leaves must not use them either.
    let mut bad = good.clone();
    let SNode::Stmts(pre) = &mut bad[0] else {
        unreachable!()
    };
    pre[0] = expr_stmt(tm("it", 30));
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // The body must not reference the iterator plumbing…
    let mut bad = good.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    otherwise[0] = run(vec![expr_stmt(tm("it", 30))]);
    assert!(match_single_pass_for_in(&bad, 1).is_none());
    // … nor grow a stray continue.
    let mut bad = good.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    otherwise.push(SNode::Continue { label: None });
    assert!(match_single_pass_for_in(&bad, 1).is_none());
}

#[test]
fn normalize_loop_test_and_pre_leaf_trims() {
    // normalize_loop_test shape guards.
    let body = vec![
        run(vec![expr_stmt(ident("a"))]),
        if_node(ident("t"), vec![SNode::Break { label: None }], vec![]),
        run(vec![expr_stmt(ident("b"))]),
    ];
    let (test, new_body) = normalize_loop_test(&body).expect("the d-P4 form");
    assert_eq!(test, ident("t"));
    assert_eq!(new_body.len(), 2);
    // Not [Stmts, If, ..].
    assert!(normalize_loop_test(&[run(vec![])]).is_none());
    assert!(
        normalize_loop_test(&[SNode::Honest("h".to_string()), SNode::Break { label: None }])
            .is_none()
    );
    // The break arm must be exactly an unlabeled break with no else.
    assert!(
        normalize_loop_test(&[run(vec![]), if_node(ident("t"), vec![run(vec![])], vec![]),])
            .is_none()
    );
    assert!(
        normalize_loop_test(&[
            run(vec![]),
            if_node(
                ident("t"),
                vec![SNode::Break { label: None }],
                vec![run(vec![])]
            ),
        ])
        .is_none()
    );
    // merged_pre_leaves concatenates adjacent runs only.
    let nodes = vec![
        SNode::Honest("h".to_string()),
        run(vec![expr_stmt(ident("a"))]),
        run(vec![expr_stmt(ident("b"))]),
        SNode::Break { label: None },
    ];
    assert_eq!(merged_pre_leaves(&nodes, 3).len(), 2);
    assert!(merged_pre_leaves(&nodes, 1).is_empty());
    // trim_pre_leaves walks backwards, removing emptied nodes and
    // stopping at a non-run node.
    let mut nodes = vec![
        SNode::Honest("h".to_string()),
        run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
        run(vec![expr_stmt(ident("c"))]),
        SNode::Break { label: None },
    ];
    let removed = trim_pre_leaves(&mut nodes, 3, 3);
    assert_eq!(removed, 2);
    assert_eq!(
        nodes,
        vec![SNode::Honest("h".to_string()), SNode::Break { label: None }]
    );
    // An Honest node stops the backwards walk before the cut
    // completes; already-empty runs still count as removals.
    let mut nodes = vec![
        SNode::Honest("h".to_string()),
        run(vec![expr_stmt(ident("a"))]),
        SNode::Break { label: None },
    ];
    let removed = trim_pre_leaves(&mut nodes, 2, 5);
    assert_eq!(removed, 1);
    assert_eq!(nodes.len(), 2);
    // trim_driver_pre_leaves skips honesty comments and empty runs.
    let mut nodes = vec![
        run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
        SNode::Honest("h".to_string()),
        run(vec![]),
        run(vec![expr_stmt(ident("c"))]),
        SNode::Break { label: None },
    ];
    let removed = trim_driver_pre_leaves(&mut nodes, 4, 3);
    assert_eq!(removed, 3);
    assert_eq!(nodes.len(), 2, "{nodes:?}");
    assert!(matches!(&nodes[0], SNode::Honest(_)));
    // gather_driver_pre_leaves likewise skips comments/empty runs.
    let nodes = vec![
        run(vec![expr_stmt(ident("a"))]),
        SNode::Honest("h".to_string()),
        run(vec![]),
        run(vec![expr_stmt(ident("b"))]),
        SNode::Break { label: None },
    ];
    let got = gather_driver_pre_leaves(&nodes, 4);
    assert_eq!(got.len(), 2);
}

#[test]
fn dead_loop_exit_throw_sweep() {
    // The N70 residue: an unlabeled `while (true)` whose header
    // declares an uncaught-await temp, followed by `throw <temp>`.
    let site = || {
        vec![
            SNode::While {
                label: None,
                cond: None,
                body: vec![
                    run(vec![decl(
                        "a",
                        50,
                        Expr::Await {
                            value: bx(ident("p")),
                            uncaught: true,
                        },
                    )]),
                    SNode::Honest("h".to_string()),
                ],
            },
            run(vec![Leaf::Raw(Stmt::Throw(tm("a", 50)))]),
        ]
    };
    let mut nodes = site();
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 1);
    assert!(matches!(&nodes[1], SNode::Honest(_)));
    // A trailing `Unreachable` marker rides along.
    let mut nodes = site();
    let SNode::Stmts(tail) = &mut nodes[1] else {
        unreachable!()
    };
    tail.push(Leaf::Raw(Stmt::Unreachable));
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 1);
    // Bails: a loop with a label is never a candidate.
    let mut nodes = site();
    let SNode::While { label, .. } = &mut nodes[0] else {
        unreachable!()
    };
    *label = Some("l".to_string());
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // The residue must be a sibling run…
    let mut nodes = site();
    nodes.pop();
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // … of exactly the throw (+marker) shape…
    let mut nodes = site();
    nodes[1] = run(vec![expr_stmt(ident("x"))]);
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // … throwing a header await temp…
    let mut nodes = site();
    nodes[1] = run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))]);
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // … with no header await, nothing is swept.
    let mut nodes = site();
    let SNode::While { body, .. } = &mut nodes[0] else {
        unreachable!()
    };
    body[0] = run(vec![decl("a", 50, ident("p"))]);
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // A live exit break keeps the residue.
    let mut nodes = site();
    let SNode::While { body, .. } = &mut nodes[0] else {
        unreachable!()
    };
    body.push(SNode::Break { label: None });
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // A labeled jump anywhere in the subtree keeps it too.
    let mut nodes = site();
    let SNode::While { body, .. } = &mut nodes[0] else {
        unreachable!()
    };
    body.push(SNode::Break {
        label: Some("l".to_string()),
    });
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // Honest markers and empty runs between the loop and the
    // residue are skipped by the sibling scan.
    let mut nodes = site();
    nodes.insert(1, SNode::Honest("cut".to_string()));
    nodes.insert(2, run(vec![]));
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 1);
    // A caught await (uncaught: false) is not the dispatch temp.
    let mut nodes = site();
    let SNode::While { body, .. } = &mut nodes[0] else {
        unreachable!()
    };
    body[0] = run(vec![decl(
        "a",
        50,
        Expr::Await {
            value: bx(ident("p")),
            uncaught: false,
        },
    )]);
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
}

#[test]
fn for_await_driver_positive_fold() {
    let mut nodes = driver_shape();
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_await_of, 1);
    let SNode::ForOf {
        is_await: true,
        binding,
        iter,
        body,
    } = &nodes[0]
    else {
        panic!("expected the folded for-await: {nodes:?}")
    };
    assert_eq!(binding, "x");
    assert_eq!(iter, &ident("src"));
    // The bookkeeping phi collapsed to its invariant source.
    assert_eq!(
        body.as_slice(),
        [run(vec![Leaf::Raw(Stmt::StoreProp {
            object: ident("out"),
            name: "items".to_string(),
            dot_legal: true,
            value: tm("x", 26),
            own: false,
        })])]
    );
    // The done-arm tail was re-homed after the loop.
    assert_eq!(
        nodes[1],
        run(vec![expr_stmt(call1(ident("print"), ident("out")))])
    );
    assert_eq!(nodes.len(), 2);
}

#[test]
fn for_await_driver_try_wrapped_binding() {
    let mut nodes = driver_shape();
    let body = driver_body(&mut nodes);
    let SNode::If { otherwise, .. } = &mut body[3] else {
        unreachable!()
    };
    otherwise[0] = SNode::Try {
        body: vec![run(vec![
            decl("x", 26, prop(tm("aw", 24), "value")),
            Leaf::Raw(Stmt::StoreProp {
                object: tm("bk", 22),
                name: "items".to_string(),
                dot_legal: true,
                value: tm("x", 26),
                own: false,
            }),
        ])],
        catches: vec![catch(
            "ce",
            vec![run(vec![
                decl("rr", 55, prop(ident("it2"), "return")),
                Leaf::Raw(Stmt::Throw(tm("ce", 56))),
            ])],
        )],
        note: None,
        finally: None,
    };
    assert!(match_for_await_driver(&nodes, 1).is_some());
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_await_of, 1);
    let SNode::ForOf { body, .. } = &nodes[0] else {
        unreachable!()
    };
    // The cleanup try dissolved loudly; the store survived.
    assert!(matches!(&body[0], SNode::Honest(_)), "{body:?}");
    assert!(matches!(&body[1], SNode::Stmts(_)));
    // A handler that is NOT the cleanup shape bails the fold.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        otherwise[0] = SNode::Try {
            body: vec![run(vec![decl("x", 26, prop(tm("aw", 24), "value"))])],
            catches: vec![catch("ce", vec![run(vec![expr_stmt(ident("x"))])])],
            note: None,
            finally: None,
        };
    });
}

#[test]
fn for_await_driver_bail_pins() {
    // The iterator setup must be a GetAsyncIterator declare…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[0] = decl(
            "it",
            10,
            Expr::Iter {
                op: IterOp::GetIterator,
                obj: bx(ident("src")),
                status: NodeStatus::Plumbing,
            },
        );
    });
    // … followed by the `.next` load on it.
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[1] = decl("next", 11, prop(tm("it", 10), "previous"));
    });
    // Every trailing assign must target a header phi.
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.push(phi_assign("stray", ident("v")));
    });
    // The body scan accepts only runs / honesty comments before the
    // dispatch.
    driver_bails(|nodes| {
        driver_body(nodes).insert(1, SNode::Break { label: None });
    });
    // Nothing significant may follow the dispatch.
    driver_bails(|nodes| {
        driver_body(nodes).push(run(vec![expr_stmt(ident("extra"))]));
    });
    // The header must open with phi decls.
    driver_bails(|nodes| {
        driver_body(nodes)[0] = run(vec![]);
    });
    // The res call must be an argument-free call…
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[0] = decl(
            "res",
            23,
            Expr::Call {
                callee: bx(tm("np", 20)),
                this: Some(bx(tm("ip", 21))),
                args: vec![ident("x")],
                kind: CallKind::Direct,
            },
        );
    });
    // … of a header phi…
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[0] = decl("res", 23, call0(tm("other", 99)));
    });
    // … with the receiver phi as `this`.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[0] = decl("res", 23, call0(tm("np", 20)));
    });
    // The folded dispatch's await of `res` is required…
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[2] = decl(
            "aw",
            24,
            Expr::Await {
                value: bx(tm("res", 23)),
                uncaught: false,
            },
        );
    });
    // … and `done` must load `.done` off the await temp.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[4] = decl("done", 25, prop(tm("aw", 24), "finished"));
    });
    // No trailing header junk.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr.push(expr_stmt(ident("extra")));
    });
    // The wiring must feed both call phis.
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[2] = phi_assign("np", tm("it", 10));
    });
    // The done test is a POSITIVE test of the done temp: an
    // inverted or foreign test bails.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { cond, .. } = &mut body[3] else {
            unreachable!()
        };
        *cond = isfalse(tm("done", 25));
    });
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { cond, .. } = &mut body[3] else {
            unreachable!()
        };
        *cond = istrue(tm("other", 99));
    });
    // The done arm must end in the exit break.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        then.retain(|n| !matches!(n, SNode::Break { .. }));
    });
    // The else arm must yield the value binding…
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(bind) = &mut otherwise[0] else {
            unreachable!()
        };
        bind.remove(0);
    });
    // … from a run or cleanup try, not an arbitrary node.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        otherwise[0] = SNode::While {
            label: None,
            cond: None,
            body: vec![],
        };
    });
    // A bookkeeping phi with two different sources…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.push(phi_assign("bk", ident("other")));
    });
    // … or an effectful source…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[4] = phi_assign("bk", call0(ident("f")));
    });
    // … or a phi-valued source…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[4] = phi_assign("bk", tm("np", 20));
    });
    // … bails. So does an unread-source phi still read in the body…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.remove(4);
    });
    // … or referenced after the loop.
    driver_bails(|nodes| {
        nodes.push(run(vec![expr_stmt(tm("bk", 22))]));
    });
    // An internal temp surviving in the kept body bails.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(bind) = &mut otherwise[0] else {
            unreachable!()
        };
        bind.push(expr_stmt(tm("res", 23)));
    });
    // A surviving declare of a folded phi bails (without counting
    // as a use — the synthetic decl is name-only).
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(bind) = &mut otherwise[0] else {
            unreachable!()
        };
        bind.push(Leaf::Decl {
            name: "np".to_string(),
            mutable: true,
            value: None,
        });
    });
}

#[test]
fn for_of_cleanup_try_binding() {
    // The value binding may sit inside the iterator-cleanup try
    // (which dissolves loudly when the handlers are cleanup-shaped).
    let mut nodes = for_of_site();
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    let binding_run = body[1].clone();
    body[1] = SNode::Try {
        body: vec![SNode::Honest("cut".to_string()), binding_run],
        catches: vec![catch(
            "ce",
            vec![run(vec![
                decl("rr", 55, prop(tm("it", 10), "return")),
                Leaf::Raw(Stmt::Throw(tm("ce", 56))),
            ])],
        )],
        note: None,
        finally: None,
    };
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_of, 1);
    let SNode::ForOf { body, .. } = &nodes[0] else {
        unreachable!()
    };
    assert!(matches!(&body[0], SNode::Honest(_)), "{body:?}");
    assert!(
        body.iter().any(|n| matches!(n, SNode::Stmts(_))),
        "{body:?}"
    );
    // A non-cleanup handler keeps the loop unfolded.
    let mut nodes = for_of_site();
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    let binding_run = body[1].clone();
    body[1] = SNode::Try {
        body: vec![binding_run],
        catches: vec![catch("ce", vec![run(vec![expr_stmt(ident("x"))])])],
        note: None,
        finally: None,
    };
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_of, 0);
    // A try whose body lacks the binding is just the body.
    let mut nodes = for_of_site();
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    body[1] = SNode::Try {
        body: vec![run(vec![expr_stmt(ident("unrelated"))])],
        catches: vec![],
        note: None,
        finally: None,
    };
    let mut nodes2 = body.clone();
    // rebuild_loop_body with the binding still in the NEXT run.
    let mut stats = FoldStats::default();
    fold(&mut nodes2, &mut stats);
    let _ = nodes;
    let _ = stats;
}

#[test]
fn for_await_driver_same_source_backedge() {
    // A bookkeeping phi fed the SAME invariant source by two
    // pre-loop assigns (the try-splitting duplicates regions).
    let mut nodes = driver_shape();
    let SNode::Stmts(pre) = &mut nodes[0] else {
        unreachable!()
    };
    pre.push(phi_assign("bk", ident("out")));
    assert!(match_for_await_driver(&nodes, 1).is_some());
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_await_of, 1);
}

#[test]
fn residual_driver_checkpoint_pins() {
    // The candidate node must be an unlabeled `while (true)`.
    let mut nodes = driver_shape();
    nodes[1] = SNode::Honest("h".to_string());
    assert!(match_for_await_driver(&nodes, 1).is_none());
    let mut nodes = driver_shape();
    let SNode::While { label, .. } = &mut nodes[1] else {
        unreachable!()
    };
    *label = Some("l".to_string());
    assert!(match_for_await_driver(&nodes, 1).is_none());
    // The call's receiver must be a header phi (callee covered
    // elsewhere).
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::Stmts(hdr) = &mut body[2] else {
            unreachable!()
        };
        hdr[0] = decl(
            "res",
            23,
            Expr::Call {
                callee: bx(tm("np", 20)),
                this: Some(bx(tm("not_a_phi", 99))),
                args: vec![],
                kind: CallKind::Direct,
            },
        );
    });
    // The binding scan skips leading honesty comments in the body.
    let mut nodes = driver_shape();
    {
        let body = driver_body(&mut nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        otherwise.insert(0, SNode::Honest("note".to_string()));
    }
    assert!(match_for_await_driver(&nodes, 1).is_some());
    // A cleanup try WITHOUT the value binding ends the scan with
    // none.
    driver_bails(|nodes| {
        let body = driver_body(nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        otherwise[0] = try_node(vec![run(vec![expr_stmt(ident("x"))])], vec![]);
    });
    // A no-source bookkeeping phi is foldable only when unused:
    // unused folds (dropped assigns)…
    let mut nodes = driver_shape();
    {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.remove(4); // the bk ← out entry assign
        let body = driver_body(&mut nodes);
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(bind) = &mut otherwise[0] else {
            unreachable!()
        };
        bind.remove(1); // and the store reading bk
    }
    assert!(match_for_await_driver(&nodes, 1).is_some());
    // … used in the re-homed tail bails…
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre.remove(4);
        let body = driver_body(nodes);
        let SNode::If {
            otherwise, then, ..
        } = &mut body[3]
        else {
            unreachable!()
        };
        let SNode::Stmts(bind) = &mut otherwise[0] else {
            unreachable!()
        };
        bind.remove(1);
        let SNode::Stmts(tail) = &mut then[0] else {
            unreachable!()
        };
        tail.push(expr_stmt(tm("bk", 22)));
    });
    // … and a phi source that is itself a header phi bails (no
    // chains).
    driver_bails(|nodes| {
        let SNode::Stmts(pre) = &mut nodes[0] else {
            unreachable!()
        };
        pre[4] = phi_assign("bk", tm("ip", 21));
    });
}

#[test]
fn rebuild_loop_body_shape_bails() {
    let folded = || LoopFold {
        is_await: false,
        is_in: false,
        iter: ident("src"),
        pre_cut: 0,
        phi_names: vec!["np".to_string()],
        res_name: Some("res".to_string()),
        done_name: Some("done".to_string()),
        extra_internals: vec!["it".to_string(), "next".to_string()],
        hoisted: vec![],
    };
    let hdr = || {
        run(vec![
            phi_decl("np", 20),
            decl("res", 23, call0(tm("np", 20))),
            decl("done", 25, prop(tm("res", 23), "done")),
        ])
    };
    let binding = || {
        run(vec![
            decl("v", 26, prop(tm("res", 23), "value")),
            expr_stmt(call1(ident("print"), tm("v", 26))),
        ])
    };
    // The positive: header + binding run.
    let body = vec![hdr(), binding()];
    let (b, out) = rebuild_loop_body(&body, &folded()).expect("corpus shape");
    assert_eq!(b, "v");
    assert_eq!(out.len(), 1);
    // The body must outlive its header.
    assert!(rebuild_loop_body(&[], &folded()).is_none());
    // The binding must be a `.value` declare…
    assert!(rebuild_loop_body(&[hdr(), run(vec![expr_stmt(ident("x"))])], &folded()).is_none());
    // … in a run or cleanup try, not an arbitrary node.
    assert!(rebuild_loop_body(&[hdr(), SNode::Honest("h".to_string())], &folded()).is_none());
    // Internal temps must not survive in the kept body.
    assert!(
        rebuild_loop_body(
            &[hdr(), {
                let mut b = binding();
                let SNode::Stmts(r) = &mut b else {
                    unreachable!()
                };
                r.push(expr_stmt(tm("np", 20)));
                b
            }],
            &folded(),
        )
        .is_none()
    );
    // The for-in rebuild: header must be a run, and the binding is
    // its last declare.
    let folded_in = || LoopFold {
        is_await: false,
        is_in: true,
        iter: ident("src"),
        pre_cut: 0,
        phi_names: vec!["ip".to_string()],
        res_name: None,
        done_name: None,
        extra_internals: vec!["ip".to_string()],
        hoisted: vec![],
    };
    let in_hdr = || {
        run(vec![
            phi_decl("ip", 20),
            decl(
                "k",
                31,
                Expr::Iter {
                    op: IterOp::NextPropName,
                    obj: bx(tm("ip", 20)),
                    status: NodeStatus::Plumbing,
                },
            ),
        ])
    };
    let (b, out) = rebuild_loop_body(
        &[
            in_hdr(),
            run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
        ],
        &folded_in(),
    )
    .expect("for-in rebuild");
    assert_eq!(b, "k");
    assert_eq!(out.len(), 1);
    assert!(rebuild_loop_body(&[SNode::Honest("h".to_string())], &folded_in()).is_none());
    assert!(rebuild_loop_body(&[run(vec![phi_decl("ip", 20)])], &folded_in()).is_none());
    // … and the internals must not be read post-elimination.
    assert!(
        rebuild_loop_body(
            &[in_hdr(), run(vec![expr_stmt(tm("ip", 20))])],
            &folded_in(),
        )
        .is_none()
    );
    // fold_loops leaves a non-matching loop alone.
    let mut nodes = vec![SNode::While {
        label: Some("l".to_string()),
        cond: Some(ident("c")),
        body: vec![],
    }];
    let before = nodes.clone();
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(nodes, before);
}

#[test]
fn single_pass_residual_pins() {
    // A pre-run holding ONLY the wiring assign is consumed whole.
    let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
    let SNode::Stmts(pre) = &mut nodes[0] else {
        unreachable!()
    };
    pre.remove(0); // drop the setup call; only the assign remains
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_in, 1);
    assert_eq!(nodes.len(), 1, "the emptied run is removed: {nodes:?}");
    // The nearest previous non-Honest node must be a statement run.
    let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
    nodes[0] = SNode::Break { label: None };
    assert!(match_single_pass_for_in(&nodes, 1).is_none());
    // Honest markers between the assign run and the header are
    // skipped by the backward scan.
    let mut nodes = single_pass_for_in_site(cmp(CmpOp::Eq, tm("k", 31), undef()));
    nodes.insert(1, SNode::Honest("dissolved".to_string()));
    assert!(match_single_pass_for_in(&nodes, 2).is_some());
}
