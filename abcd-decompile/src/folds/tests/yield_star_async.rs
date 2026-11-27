//! Asynchronous `yield*` tail, yield-dispatch, setup/init/exit, and polarity fold unit tests.

use super::*;

#[test]
fn yield_star_async_positive() {
    let mut nodes = ys_async_shape();
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(stats.yield_star_bound, 1);
    assert_eq!(
        nodes,
        vec![
            run(vec![decl(
                "vval",
                150,
                Expr::YieldStar {
                    value: bx(ident("src")),
                },
            )]),
            run(vec![expr_stmt(tm("vval", 150))]),
        ],
        "{nodes:?}"
    );
    // Stripped catch-context `PhiAssign` placeholders (`run(vec![])`) left by
    // `async_generator_machine_fold` inside the loop body are pruned at entry.
    let mut with_empty = ys_async_shape();
    if let SNode::While { body, .. } = ys_while(&mut with_empty) {
        body.insert(1, run(vec![]));
    }
    let mut stats2 = FoldStats::default();
    yield_star_fold(&mut with_empty, FunctionKind::AsyncGenerator, &mut stats2);
    assert_eq!(stats2.yield_star_sites, 1);
}

#[test]
fn ys_match_loop_tail_async_bail_pins() {
    fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = ys_async_shape();
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        mutate(body);
        assert!(
            ys_match_loop(&nodes[2], true).is_none(),
            "near-miss matched"
        );
    }
    // The async tail is exactly [precall, await-dispatch] past the
    // header + dispatch.
    bail(|body| {
        body.truncate(3);
    });
    // The precall's exit phi must be declared there.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.remove(0);
    });
    // The call must name a precall phi…
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl("vres", 112, call1(tm("other", 99), tm("vrv", 101)));
    });
    // … with the iterator as `this`…
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl(
            "vres",
            112,
            Expr::Call {
                callee: bx(tm("vm", 111)),
                this: Some(bx(tm("other", 99))),
                args: vec![tm("vrv", 101)],
                kind: CallKind::Dynamic,
            },
        );
    });
    // … and a phi as the argument.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl(
            "vres",
            112,
            Expr::Call {
                callee: bx(tm("vm", 111)),
                this: Some(bx(tm("vit", 102))),
                args: vec![tm("other", 99)],
                kind: CallKind::Dynamic,
            },
        );
    });
    // The inner await must read the call result…
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[3] = decl(
            "aw0",
            141,
            Expr::Await {
                value: bx(tm("other", 99)),
                uncaught: true,
            },
        );
    });
    // … and the pass-through yield must yield the awaited value.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[4] = expr_stmt(Expr::Yield {
            value: bx(tm("other", 99)),
        });
    });
    // The resume decl must be ResumeGenerator on a header genobj…
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[5] = decl("vres1", 142, ident("not_a_driver"));
    });
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[5] = decl(
            "vres1",
            142,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("other", 99)),
            },
        );
    });
    // The await-dispatch must be an if.
    bail(|body| {
        body[3] = run(vec![]);
    });
    // … testing THROW on an inline GetResumeMode…
    bail(|body| {
        let SNode::If { cond, .. } = &mut body[3] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::Eq, tm("vg", 103), num(1.0)));
    });
    // … whose else arm is `throw res1; unreachable; break`.
    bail(|body| {
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        *otherwise = vec![];
    });
    bail(|body| {
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(tr) = &mut otherwise[0] else {
            unreachable!()
        };
        tr[0] = Leaf::Raw(Stmt::Throw(tm("other", 99)));
    });
    // The continuation: [done run, done test].
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        then.remove(0);
    });
    // The done run loads `res1.done` (the elided guard rides free).
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(dr) = &mut then[0] else {
            unreachable!()
        };
        dr[1] = decl("vdone", 113, prop(tm("other", 99), "done"));
    });
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(dr) = &mut then[0] else {
            unreachable!()
        };
        dr.push(expr_stmt(ident("extra")));
    });
    // The done test must be a positive flag test of `done`.
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut then[1] else {
            unreachable!()
        };
        *cond = isfalse(tm("vdone", 113));
    });
    // The done arm is [exit dispatch, break].
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        done.remove(1); // no break
    });
    // The exit test must be `!exitReturn`.
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut done[0] else {
            unreachable!()
        };
        *cond = istrue(tm("vexit", 110));
    });
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut done[0] else {
            unreachable!()
        };
        *cond = isfalse(tm("other", 99));
    });
    // The normal arm opens with the completion-value load…
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { then: normal, .. } = &mut done[0] else {
            unreachable!()
        };
        let SNode::Stmts(nr) = &mut normal[0] else {
            unreachable!()
        };
        nr[0] = decl("vval", 150, prop(tm("other", 99), "value"));
    });
    // … and the return arm is `v2 = res1.value; return v2`.
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut done[0] else {
            unreachable!()
        };
        let SNode::Stmts(rr) = &mut otherwise[0] else {
            unreachable!()
        };
        rr[1] = Leaf::Raw(Stmt::Return(Some(tm("other", 99))));
    });
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut done[0] else {
            unreachable!()
        };
        otherwise[0] = run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))]);
    });
    // The not-done arm must be the async yield machinery.
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut then[1] else {
            unreachable!()
        };
        *otherwise = vec![];
    });
}

#[test]
fn ys_match_async_yield_bail_pins() {
    // A near-miss pin: mutate the not-done arm of the async shape;
    // the loop match must fail.
    fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = ys_async_shape();
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut then[1] else {
                unreachable!()
            };
            mutate(otherwise);
        }
        assert!(
            ys_match_loop(&nodes[2], true).is_none(),
            "near-miss matched"
        );
    }
    // Baseline: the shape matches.
    let nodes = ys_async_shape();
    assert!(ys_match_loop(&nodes[2], true).is_some());
    // The not-done arm is [head run, mode if].
    bail(|next| {
        next.truncate(1);
    });
    // The head: `[value = res1.value, av = await value, yield av,
    // res2 = ResumeGenerator(g)]`.
    bail(|next| {
        let SNode::Stmts(head) = &mut next[0] else {
            unreachable!()
        };
        head[0] = decl("v2", 143, prop(tm("other", 99), "value"));
    });
    bail(|next| {
        let SNode::Stmts(head) = &mut next[0] else {
            unreachable!()
        };
        head[1] = decl(
            "av2",
            144,
            Expr::Await {
                value: bx(tm("other", 99)),
                uncaught: true,
            },
        );
    });
    bail(|next| {
        let SNode::Stmts(head) = &mut next[0] else {
            unreachable!()
        };
        head[2] = expr_stmt(Expr::Yield {
            value: bx(tm("other", 99)),
        });
    });
    bail(|next| {
        let SNode::Stmts(head) = &mut next[0] else {
            unreachable!()
        };
        head[3] = decl("vres2", 145, ident("not_a_driver"));
    });
    // The mode if: the THROW dispatch on the new pair…
    bail(|next| {
        let SNode::If { cond, .. } = &mut next[1] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::Eq, tm("vg", 103), num(1.0)));
    });
    // … with `throw res2; unreachable; break` in the else.
    bail(|next| {
        let SNode::If { otherwise, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(tr) = &mut otherwise[0] else {
            unreachable!()
        };
        tr[0] = Leaf::Raw(Stmt::Throw(tm("other", 99)));
    });
    // The resumption re-entry skeleton: [pair, next-if, await run,
    // throw-if, loopback, continue].
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        then.truncate(1);
    });
    // The pair: `[r3 = ResumeGenerator(g), m3 = GetResumeMode(g)]`.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(pair) = &mut then[0] else {
            unreachable!()
        };
        pair[1] = decl("m3", 147, ident("not_a_driver"));
    });
    // The NEXT test: `if (m3 != RETURN) { loop back; continue }`.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut then[1] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::Eq, tm("other", 99), num(0.0)));
    });
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::If { then: lb, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut lb[0] else {
            unreachable!()
        };
        assigns[1] = phi_assign("vrv", tm("other", 99));
    });
    // The RETURN await run shape.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(ar) = &mut then[2] else {
            unreachable!()
        };
        ar[0] = decl(
            "aw3",
            148,
            Expr::Await {
                value: bx(tm("other", 99)),
                uncaught: true,
            },
        );
    });
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(ar) = &mut then[2] else {
            unreachable!()
        };
        ar[3] = decl("m4", 153, ident("not_a_driver"));
    });
    // The THROW test: `if (m4 == THROW) { loop back; continue }`.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut then[3] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::NotEq, tm("other", 99), num(1.0)));
    });
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::If { then: lb, .. } = &mut then[3] else {
            unreachable!()
        };
        let SNode::Stmts(assigns) = &mut lb[0] else {
            unreachable!()
        };
        assigns[0] = phi_assign("vrt", tm("other", 99));
    });
    // The final loop-back: `rt ← RETURN(0)`, `rv ← r4`.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(fin) = &mut then[4] else {
            unreachable!()
        };
        fin[0] = phi_assign("vrt", num(1.0));
    });
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(fin) = &mut then[4] else {
            unreachable!()
        };
        fin[1] = phi_assign("vrv", tm("other", 99));
    });
}

#[test]
fn ys_setup_init_exit_matchers() {
    let full = ys_sync_shape();
    let mut uses = BTreeMap::new();
    count_temp_uses(&full, &mut uses);
    // ys_match_setup.
    let (delegate, iter, next, prefix) =
        ys_match_setup(&full[0], false, &uses).expect("the setup run");
    assert_eq!(delegate, ident("src"));
    assert_eq!(iter, ValueId::new(200));
    assert_eq!(next, ValueId::new(201));
    assert!(prefix.is_empty());
    // Not a run; too short; the last two must be the declares…
    assert!(ys_match_setup(&SNode::Honest("h".to_string()), false, &uses).is_none());
    assert!(ys_match_setup(&run(vec![]), false, &uses).is_none());
    assert!(ys_match_setup(&run(vec![expr_stmt(ident("x"))]), false, &uses).is_none());
    let bad = run(vec![
        expr_stmt(ident("x")),
        decl("vnext", 201, prop(tm("vit0", 200), "next")),
    ]);
    assert!(ys_match_setup(&bad, false, &uses).is_none());
    // … the second-to-last an Iter of the right kind…
    let bad = run(vec![
        decl("vit0", 200, ident("not_iter")),
        decl("vnext", 201, prop(tm("vit0", 200), "next")),
    ]);
    assert!(ys_match_setup(&bad, false, &uses).is_none());
    let bad = run(vec![
        decl(
            "vit0",
            200,
            Expr::Iter {
                op: IterOp::GetIterator,
                obj: bx(ident("src")),
                status: NodeStatus::Plumbing,
            },
        ),
        decl("vnext", 201, prop(tm("vit0", 200), "next")),
    ]);
    assert!(
        ys_match_setup(&bad, true, &uses).is_none(),
        "sync op in an async fold"
    );
    assert!(ys_match_setup(&bad, false, &uses).is_some());
    // … and `next` must load `.next` off the iterator.
    let bad = run(vec![
        decl(
            "vit0",
            200,
            Expr::Iter {
                op: IterOp::GetIterator,
                obj: bx(ident("src")),
                status: NodeStatus::Plumbing,
            },
        ),
        decl("vnext", 201, prop(tm("vit0", 200), "previous")),
    ]);
    assert!(ys_match_setup(&bad, false, &uses).is_none());
    // A single-use temp delegate inlines into the yield*.
    let with_temp_delegate = run(vec![
        decl("td", 205, call0(ident("make_iter"))),
        decl(
            "vit0",
            200,
            Expr::Iter {
                op: IterOp::GetIterator,
                obj: bx(tm("td", 205)),
                status: NodeStatus::Plumbing,
            },
        ),
        decl("vnext", 201, prop(tm("vit0", 200), "next")),
    ]);
    let mut uses = BTreeMap::new();
    uses.insert(ValueId::new(205), 1);
    let (delegate, .., prefix) =
        ys_match_setup(&with_temp_delegate, false, &uses).expect("temp delegate");
    assert_eq!(delegate, call0(ident("make_iter")));
    assert!(prefix.is_empty());
    // A shared temp stays a delegate reference with the prefix kept.
    let mut uses = BTreeMap::new();
    uses.insert(ValueId::new(205), 2);
    let (delegate, .., prefix) =
        ys_match_setup(&with_temp_delegate, false, &uses).expect("shared temp");
    assert_eq!(delegate, tm("td", 205));
    assert_eq!(prefix.len(), 1);

    // ys_match_init (against the loop match's extracted phis).
    let lp = ys_match_loop(&full[2], false).expect("the sync loop");
    assert!(ys_match_init(&full[1], &lp, ValueId::new(200), ValueId::new(201)).is_some());
    // Not a run / empty.
    assert!(
        ys_match_init(
            &SNode::Honest("h".to_string()),
            &lp,
            ValueId::new(200),
            ValueId::new(201)
        )
        .is_none()
    );
    assert!(ys_match_init(&run(vec![]), &lp, ValueId::new(200), ValueId::new(201)).is_none());
    // A non-assign leaf…
    let bad = run(vec![phi_assign("vrt", num(2.0)), expr_stmt(ident("x"))]);
    assert!(ys_match_init(&bad, &lp, ValueId::new(200), ValueId::new(201)).is_none());
    // … assigns split across blocks…
    let bad = run(vec![
        phi_assign("vrt", num(2.0)),
        phi_assign("vrv", undef()),
        phi_assign("vflag", boolean(false)),
        phi_assign("vit", tm("vit0", 200)),
        phi_assign("vg", tm("vg0", 202)),
        phi_assign("vm", tm("vnext", 201)),
        Leaf::Raw(Stmt::PhiAssign {
            target: "vx".to_string(),
            value: ident("x"),
            to: BlockId::new(8),
            exceptional: false,
        }),
    ]);
    assert!(ys_match_init(&bad, &lp, ValueId::new(200), ValueId::new(201)).is_none());
    // … and must anchor mode=2, received=undefined, flag=false,
    // the iterator, the genobj, and exactly one method.
    for (i, leaf) in [
        phi_assign("vrt", num(1.0)),
        phi_assign("vrv", boolean(false)),
        phi_assign("vflag", boolean(true)),
        phi_assign("vit", tm("other", 99)),
        phi_assign("vm", tm("other", 99)),
    ]
    .into_iter()
    .enumerate()
    {
        let SNode::Stmts(init) = &full[1] else {
            unreachable!()
        };
        let mut bad = init.clone();
        bad[i] = leaf;
        assert!(
            ys_match_init(&run(bad), &lp, ValueId::new(200), ValueId::new(201)).is_none(),
            "mutation {i}"
        );
    }
    // The genobj assign is required.
    let SNode::Stmts(init) = &full[1] else {
        unreachable!()
    };
    let mut bad = init.clone();
    bad.remove(4);
    assert!(ys_match_init(&run(bad), &lp, ValueId::new(200), ValueId::new(201)).is_none());
    // An exceptional assign rides along free.
    let mut good = init.clone();
    good.push(exc_assign("vx", ident("z")));
    assert!(ys_match_init(&run(good), &lp, ValueId::new(200), ValueId::new(201)).is_some());

    // ys_match_exit.
    let res = ys_sync_res(&full[2]).expect("the res temp");
    assert_eq!(res, ValueId::new(112));
    let exit = ys_match_exit(&full[3], lp.exit_phi.0, res).expect("the exit dispatch");
    assert_eq!(exit.0, Some(("vval".to_string(), ValueId::new(150))));
    // Must be an if…
    assert!(ys_match_exit(&SNode::Honest("h".to_string()), lp.exit_phi.0, res).is_none());
    // … testing `!exitReturn`…
    let bad = if_node(istrue(tm("vexit", 110)), vec![], vec![]);
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    let bad = if_node(isfalse(tm("other", 99)), vec![], vec![]);
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // … with the completion load opening the normal arm…
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![SNode::Honest("h".to_string())],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
        ])],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(ident("x"))])],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
        ])],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // … (a dead Expr load instead of a declare is the unused form)…
    let unused = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
        ])],
    );
    let exit = ys_match_exit(&unused, lp.exit_phi.0, res).expect("unused completion value");
    assert_eq!(exit.0, None);
    // … and the return arm returning what it loaded…
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("other", 99)))),
        ])],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // … in exactly one run…
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![
            run(vec![decl("vv2", 151, prop(tm("vres", 112), "value"))]),
            run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))]),
        ],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // … with only dead plumbing assigns trailing.
    let with_plumbing = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            phi_assign("pz", ident("z")),
        ])],
    );
    assert!(ys_match_exit(&with_plumbing, lp.exit_phi.0, res).is_some());
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![run(vec![
            decl("vv2", 151, prop(tm("vres", 112), "value")),
            Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            expr_stmt(ident("x")),
        ])],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // ys_sync_res: the loop's call-result temp.
    assert!(ys_sync_res(&SNode::Honest("h".to_string())).is_none());
    assert!(ys_sync_res(&full[0]).is_none());
    let no_call = SNode::While {
        label: None,
        cond: None,
        body: vec![run(vec![]), run(vec![]), run(vec![])],
    };
    assert!(ys_sync_res(&no_call).is_none());
    // ys_innermost_body: non-try / single / nested wrappers.
    assert!(ys_innermost_body(&SNode::Honest("h".to_string())).is_none());
    let t = try_node(vec![run(vec![expr_stmt(ident("x"))])], vec![]);
    assert_eq!(ys_innermost_body(&t).map(Vec::len), Some(1));
    let t2 = try_node(vec![t], vec![]);
    assert_eq!(ys_innermost_body(&t2).map(Vec::len), Some(1));
}

#[test]
fn ys_small_matcher_tables() {
    // ys_is_exc_run / ys_sig.
    let exc = || {
        run(vec![
            exc_assign("a", ident("x")),
            exc_assign("b", ident("y")),
        ])
    };
    assert!(ys_is_exc_run(&exc()));
    assert!(!ys_is_exc_run(&run(vec![])));
    assert!(!ys_is_exc_run(&run(vec![phi_assign("a", ident("x"))])));
    assert!(!ys_is_exc_run(&SNode::Honest("h".to_string())));
    let nodes = vec![exc(), run(vec![expr_stmt(ident("a"))])];
    assert_eq!(ys_sig(&nodes).len(), 1);
    // ys_assign_run: phi assigns to ONE block (exceptional skipped).
    assert_eq!(
        ys_assign_run(&run(vec![
            phi_assign("a", ident("x")),
            exc_assign("b", ident("y")),
            phi_assign("c", ident("z")),
        ])),
        Some(BlockId::new(7))
    );
    assert!(ys_assign_run(&SNode::Honest("h".to_string())).is_none());
    assert!(ys_assign_run(&run(vec![])).is_none());
    assert!(ys_assign_run(&run(vec![expr_stmt(ident("x"))])).is_none());
    assert!(
        ys_assign_run(&run(vec![
            phi_assign("a", ident("x")),
            Leaf::Raw(Stmt::PhiAssign {
                target: "b".to_string(),
                value: ident("y"),
                to: BlockId::new(8),
                exceptional: false,
            }),
        ]))
        .is_none()
    );
    // ys_phi_decls: the leading phi decls, by name.
    let got = ys_phi_decls(&run(vec![
        phi_decl("a", 1),
        phi_decl("b", 2),
        expr_stmt(ident("x")),
        phi_decl("c", 3),
    ]));
    assert_eq!(got.map(|m| m.len()), Some(2));
    assert!(ys_phi_decls(&SNode::Honest("h".to_string())).is_none());
    // ys_mode_test: `IsFalse(StrictEq(t, num))` in either order.
    assert_eq!(
        ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), num(2.0))), 2.0),
        Some(ValueId::new(5))
    );
    assert_eq!(
        ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, num(2.0), tm("t", 5))), 2.0),
        Some(ValueId::new(5))
    );
    assert!(ys_mode_test(&cmp(CmpOp::StrictEq, tm("t", 5), num(2.0)), 2.0).is_none());
    assert!(ys_mode_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), num(2.0))), 2.0).is_none());
    assert!(ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, ident("t"), num(2.0))), 2.0).is_none());
    assert!(ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, ident("t"), ident("u"))), 2.0).is_none());
    assert!(ys_mode_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), num(1.0))), 2.0).is_none());
    // ys_flag_test: wrapper polarity.
    assert_eq!(ys_flag_test(&tm("t", 5)), Some((ValueId::new(5), true)));
    assert_eq!(
        ys_flag_test(&istrue(tm("t", 5))),
        Some((ValueId::new(5), true))
    );
    assert_eq!(
        ys_flag_test(&isfalse(tm("t", 5))),
        Some((ValueId::new(5), false))
    );
    assert_eq!(
        ys_flag_test(&isfalse(isfalse(tm("t", 5)))),
        Some((ValueId::new(5), true))
    );
    assert_eq!(ys_flag_test(&ident("t")), None);
    // ys_undefined_test: `IsFalse(Eq(t, undefined))` in either order.
    assert_eq!(
        ys_undefined_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), undef()))),
        Some((ValueId::new(5), true))
    );
    assert_eq!(
        ys_undefined_test(&isfalse(cmp(CmpOp::Eq, undef(), tm("t", 5)))),
        Some((ValueId::new(5), true))
    );
    assert_eq!(
        ys_undefined_test(&cmp(CmpOp::Eq, tm("t", 5), undef())),
        Some((ValueId::new(5), false))
    );
    assert!(ys_undefined_test(&isfalse(cmp(CmpOp::StrictEq, tm("t", 5), undef()))).is_none());
    assert!(ys_undefined_test(&isfalse(cmp(CmpOp::Eq, tm("t", 5), ident("u")))).is_none());
    // ys_driver / ys_prop / ys_declare_of.
    let drv = Expr::GeneratorDriver {
        resume: true,
        genobj: bx(tm("g", 7)),
    };
    assert!(ys_driver(&drv, true, ValueId::new(7)));
    assert!(!ys_driver(&drv, false, ValueId::new(7)));
    assert!(!ys_driver(&drv, true, ValueId::new(8)));
    assert!(!ys_driver(&ident("x"), true, ValueId::new(7)));
    assert_eq!(
        ys_prop(&prop(tm("o", 5), "next"), "next"),
        Some(ValueId::new(5))
    );
    assert_eq!(ys_prop(&prop(tm("o", 5), "next"), "done"), None);
    assert_eq!(ys_prop(&ident("o"), "next"), None);
    let d = decl("x", 5, ident("v"));
    assert_eq!(
        ys_declare_of(&d).map(|(n, i, _)| (n, i)),
        Some(("x", ValueId::new(5)))
    );
    assert_eq!(ys_declare_of(&expr_stmt(ident("x"))), None);
    // ys_contains_elided.
    assert!(ys_contains_elided(
        &[run(vec![elided("ThrowNotExists")])],
        "ThrowNotExists"
    ));
    assert!(!ys_contains_elided(
        &[run(vec![elided("Other")])],
        "ThrowNotExists"
    ));
    // ys_mode_num_test via the eq/neq wrappers + the wrong-op arm.
    assert!(
        ys_mode_neq_test(
            &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(0.0))),
            ValueId::new(5),
            0.0
        )
        .is_some()
    );
    assert!(
        ys_mode_eq_test(
            &isfalse(cmp(CmpOp::NotEq, tm("m", 5), num(1.0))),
            ValueId::new(5),
            1.0
        )
        .is_some()
    );
    assert!(
        ys_mode_eq_test(
            &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(1.0))),
            ValueId::new(5),
            1.0
        )
        .is_none()
    );
    assert!(
        ys_mode_neq_test(&cmp(CmpOp::Eq, tm("m", 5), num(0.0)), ValueId::new(5), 0.0).is_none()
    );
    assert!(ys_mode_neq_test(&isfalse(ident("c")), ValueId::new(5), 0.0).is_none());
    assert!(
        ys_mode_neq_test(
            &isfalse(cmp(CmpOp::Eq, tm("m", 5), num(1.0))),
            ValueId::new(5),
            0.0
        )
        .is_none()
    );
    // ys_loopback directly.
    let lb = |tail: Vec<Leaf>| vec![run(tail)];
    assert!(
        ys_loopback(
            &{
                let mut v = lb(vec![
                    phi_assign("rt", tm("m", 5)),
                    phi_assign("rv", tm("r", 6)),
                ]);
                v.push(SNode::Continue { label: None });
                v
            },
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_some()
    );
    // … without the trailing continue…
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", tm("m", 5)),
                phi_assign("rv", tm("r", 6))
            ]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_some()
    );
    // … with exceptional plumbing interspersed…
    assert!(
        ys_loopback(
            &lb(vec![
                exc_assign("x", ident("y")),
                phi_assign("rt", tm("m", 5)),
                phi_assign("rv", tm("r", 6)),
            ]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_some()
    );
    // … or with mode as the RETURN literal.
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", num(0.0)),
                phi_assign("rv", tm("r", 6))
            ]),
            &[],
            "rt",
            "rv",
            None,
            Some(ValueId::new(6)),
            true,
        )
        .is_some()
    );
    // Bails: non-empty else / bad skeleton / not a run / empty run /
    // foreign leaf / mixed blocks / wrong mode / wrong value /
    // missing anchors.
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", tm("m", 5)),
                phi_assign("rv", tm("r", 6))
            ]),
            &[run(vec![expr_stmt(ident("x"))])],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_none()
    );
    assert!(ys_loopback(&[], &[], "rt", "rv", None, None, false).is_none());
    assert!(
        ys_loopback(
            &[
                SNode::Honest("h".to_string()),
                SNode::Honest("i".to_string())
            ],
            &[],
            "rt",
            "rv",
            None,
            None,
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &[SNode::Honest("h".to_string())],
            &[],
            "rt",
            "rv",
            None,
            None,
            false
        )
        .is_none()
    );
    assert!(ys_loopback(&lb(vec![]), &[], "rt", "rv", None, None, false).is_none());
    assert!(
        ys_loopback(
            &lb(vec![expr_stmt(ident("x"))]),
            &[],
            "rt",
            "rv",
            None,
            None,
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", tm("m", 5)),
                Leaf::Raw(Stmt::PhiAssign {
                    target: "rv".to_string(),
                    value: tm("r", 6),
                    to: BlockId::new(8),
                    exceptional: false,
                }),
            ]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", tm("other", 9)),
                phi_assign("rv", tm("r", 6))
            ]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", tm("m", 5)),
                phi_assign("rv", tm("other", 9))
            ]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &lb(vec![phi_assign("rt", tm("m", 5))]),
            &[],
            "rt",
            "rv",
            Some(ValueId::new(5)),
            Some(ValueId::new(6)),
            false,
        )
        .is_none()
    );
    assert!(
        ys_loopback(
            &lb(vec![
                phi_assign("rt", num(1.0)),
                phi_assign("rv", tm("r", 6))
            ]),
            &[],
            "rt",
            "rv",
            None,
            Some(ValueId::new(6)),
            true,
        )
        .is_none()
    );
    // ys_async_throw_dispatch directly.
    let drv_g = |resume: bool| Expr::GeneratorDriver {
        resume,
        genobj: bx(tm("g", 7)),
    };
    let throw_else = vec![
        run(vec![
            Leaf::Raw(Stmt::Throw(tm("r", 6))),
            Leaf::Raw(Stmt::Unreachable),
        ]),
        SNode::Break { label: None },
    ];
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6),
        )
        .is_some()
    );
    // … the driver on either side of the Eq…
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, num(1.0), drv_g(false))),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6),
        )
        .is_some()
    );
    assert!(
        ys_async_throw_dispatch(
            &cmp(CmpOp::Eq, drv_g(false), num(1.0)),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6)
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(ident("c")),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6)
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(false), num(2.0))),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6)
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(true), num(1.0))),
            &throw_else,
            ValueId::new(7),
            ValueId::new(6)
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
            &[],
            ValueId::new(7),
            ValueId::new(6)
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
            &[run(vec![Leaf::Raw(Stmt::Throw(tm("other", 9)))])],
            ValueId::new(7),
            ValueId::new(6),
        )
        .is_none()
    );
    assert!(
        ys_async_throw_dispatch(
            &isfalse(cmp(CmpOp::Eq, drv_g(false), num(1.0))),
            &[
                run(vec![expr_stmt(ident("x"))]),
                SNode::Break { label: None }
            ],
            ValueId::new(7),
            ValueId::new(6),
        )
        .is_none()
    );
}

#[test]
fn ys_tail_residual_pins() {
    // ── sync tail residuals ──
    fn bail_sync(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = ys_sync_shape();
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        mutate(body);
        assert!(
            ys_match_loop(&nodes[2], false).is_none(),
            "near-miss matched"
        );
    }
    // The call must carry `this` (a temp receiver)…
    bail_sync(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl("vres", 112, call0(tm("vm", 111)));
    });
    // … and a temp as its only argument.
    bail_sync(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl(
            "vres",
            112,
            Expr::Call {
                callee: bx(tm("vm", 111)),
                this: Some(bx(tm("vit", 102))),
                args: vec![ident("not_a_temp")],
                kind: CallKind::Dynamic,
            },
        );
    });
    // The precall must contain the call at all.
    bail_sync(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.remove(2);
    });
    // The done test must be an if.
    bail_sync(|body| {
        body[3] = run(vec![]);
    });
    // The suspend must be a statement run of the exact pair shape.
    bail_sync(|body| {
        body[4] = SNode::Honest("h".to_string());
    });
    bail_sync(|body| {
        let SNode::Stmts(susp) = &mut body[4] else {
            unreachable!()
        };
        susp.push(elided("Guard"));
    });
    // The loop-back must be a statement run of phi assigns.
    bail_sync(|body| {
        body[5] = SNode::Honest("h".to_string());
    });
    bail_sync(|body| {
        let SNode::Stmts(lb) = &mut body[5] else {
            unreachable!()
        };
        lb.push(expr_stmt(ident("x")));
    });
    // Positive: an elided ThrowIfNotObject guard rides the precall.
    let mut nodes = ys_sync_shape();
    {
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.insert(3, elided("ThrowIfNotObject"));
    }
    assert!(ys_match_loop(&nodes[2], false).is_some());

    // ── async tail residuals ──
    fn bail_async(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = ys_async_shape();
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        mutate(body);
        assert!(
            ys_match_loop(&nodes[2], true).is_none(),
            "near-miss matched"
        );
    }
    // The async skeleton is exactly [header, dispatch, precall,
    // await-dispatch].
    bail_async(|body| {
        body.push(run(vec![]));
    });
    // The precall tail must be the exact four-leaf shape.
    bail_async(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.push(elided("Extra"));
    });
    // The call carries `this` and a temp argument.
    bail_async(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl("vres", 112, call0(tm("vm", 111)));
    });
    bail_async(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl(
            "vres",
            112,
            Expr::Call {
                callee: bx(tm("vm", 111)),
                this: Some(bx(tm("vit", 102))),
                args: vec![ident("not_a_temp")],
                kind: CallKind::Dynamic,
            },
        );
    });
    // The continuation must open with the done run…
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        then[0] = SNode::Honest("h".to_string());
    });
    // … containing the done load…
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::Stmts(dr) = &mut then[0] else {
            unreachable!()
        };
        dr.remove(1);
    });
    // … and the done test must be an if.
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        then[1] = run(vec![]);
    });
    // The done arm's exit dispatch must be an if…
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        done[0] = run(vec![]);
    });
    // … testing the exit phi flag.
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut done[0] else {
            unreachable!()
        };
        *cond = cmp(CmpOp::Eq, tm("vexit", 110), undef());
    });
    // The normal arm opens with a run holding the value declare…
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { then: normal, .. } = &mut done[0] else {
            unreachable!()
        };
        normal[0] = SNode::Honest("h".to_string());
    });
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { then: normal, .. } = &mut done[0] else {
            unreachable!()
        };
        let SNode::Stmts(nr) = &mut normal[0] else {
            unreachable!()
        };
        nr[0] = expr_stmt(ident("x"));
    });
    // … and the return arm opens with a run.
    bail_async(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        let SNode::If { then: done, .. } = &mut then[1] else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut done[0] else {
            unreachable!()
        };
        otherwise[0] = SNode::Honest("h".to_string());
    });
}

#[test]
fn ys_async_yield_residual_pins() {
    fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
        let mut nodes = ys_async_shape();
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::If { then, .. } = &mut body[3] else {
                unreachable!()
            };
            let SNode::If { otherwise, .. } = &mut then[1] else {
                unreachable!()
            };
            mutate(otherwise);
        }
        assert!(
            ys_match_loop(&nodes[2], true).is_none(),
            "near-miss matched"
        );
    }
    // The head's four leaves are exactly [declare, declare, yield
    // expr, declare]…
    bail(|next| {
        let SNode::Stmts(head) = &mut next[0] else {
            unreachable!()
        };
        head[0] = expr_stmt(ident("x"));
    });
    // … then the mode dispatch is an if…
    bail(|next| {
        next[1] = run(vec![]);
    });
    // … the resumption pair is exactly two declares…
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(pair) = &mut then[0] else {
            unreachable!()
        };
        pair[0] = expr_stmt(ident("x"));
    });
    // … the NEXT test is an if…
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        then[1] = run(vec![]);
    });
    // … the RETURN await run keeps its four-leaf shape…
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        let SNode::Stmts(ar) = &mut then[2] else {
            unreachable!()
        };
        ar[0] = expr_stmt(ident("x"));
    });
    // … and the THROW test is an if.
    bail(|next| {
        let SNode::If { then, .. } = &mut next[1] else {
            unreachable!()
        };
        then[3] = run(vec![]);
    });
}

#[test]
fn round3_yield_star_polarity_in_loop_exit_and_async_gen_resolve() {
    let jnez = |e: Expr| Expr::Unary {
        op: UnOp::JumpNez,
        operand: bx(e),
    };
    // 1. dissolve_rethrow_trys: SetGeneratorState + rethrow dissolves; SetGeneratorState alone stays.
    let mut nodes = vec![
        try_node(
            vec![run(vec![expr_stmt(ident("body"))])],
            vec![catch(
                "e",
                vec![run(vec![
                    elided("SetGeneratorState"),
                    Leaf::Raw(Stmt::Throw(tm("e", 1))),
                ])],
            )],
        ),
        try_node(
            vec![run(vec![expr_stmt(ident("keep"))])],
            vec![catch("e", vec![run(vec![elided("SetGeneratorState")])])],
        ),
    ];
    dissolve_rethrow_trys(&mut nodes);
    assert!(matches!(&nodes[0], SNode::Honest(_)), "{nodes:?}");
    assert!(matches!(&nodes[2], SNode::Try { .. }), "{nodes:?}");

    // 2. Sync R3-M1/R3-X1 shape: positive mode/undefined/throw polarities + 4-node in-loop exit.
    let pos_ret = |async_: bool| {
        let mut out = vec![run(vec![
            decl("vt", 120, boolean(true)),
            decl("vret", 121, prop(tm("vit", 102), "return")),
        ])];
        if !async_ {
            out.push(run(vec![
                elided("SetGeneratorState"),
                Leaf::Raw(Stmt::Return(Some(tm("vrv", 101)))),
                exc_assign("vex", tm("vg", 103)),
            ]));
        }
        out.push(if_node(
            jnez(cmp(CmpOp::Eq, tm("vret", 121), undef())),
            vec![SNode::Break { label: None }],
            vec![run(vec![
                phi_assign("vexit", tm("vt", 120)),
                phi_assign("vm1", tm("vnext", 201)),
            ])],
        ));
        out
    };
    let pos_throw = || {
        vec![
            run(vec![
                decl("vthrow", 130, prop(tm("vit", 102), "throw")),
                decl("veq", 131, cmp(CmpOp::Eq, tm("vthrow", 130), undef())),
            ]),
            if_node(
                jnez(tm("veq", 131)),
                vec![SNode::Break { label: None }],
                vec![run(vec![phi_assign("vexit", tm("vexit0", 105))])],
            ),
            if_node(
                istrue(tm("vflag", 104)),
                vec![run(vec![elided("ThrowNotExists")])],
                vec![run(vec![])],
            ),
        ]
    };
    let pos_dispatch = |async_: bool| {
        if_node(
            jnez(cmp(CmpOp::StrictEq, tm("vrt", 100), num(2.0))),
            vec![run(vec![phi_assign("vm0", tm("vnext", 201))])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("vrt", 100), num(1.0)),
                pos_throw(),
                pos_ret(async_),
            )],
        )
    };
    let drv = |resume: bool| Expr::GeneratorDriver {
        resume,
        genobj: bx(tm("vg", 103)),
    };
    let exit_if = |res_name: &str, res_id: u32| {
        if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![
                decl("vval", 150, prop(tm(res_name, res_id), "value")),
                expr_stmt(tm("vval", 150)),
            ])],
            vec![run(vec![
                decl("vv2", 151, prop(tm(res_name, res_id), "value")),
                elided("SetGeneratorState"),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            ])],
        )
    };
    let sync_w = SNode::While {
        label: None,
        cond: None,
        body: vec![
            ys_header(),
            pos_dispatch(false),
            ys_sync_tail().into_iter().next().unwrap(),
            if_node(
                istrue(tm("vdone", 113)),
                vec![exit_if("vres", 112), SNode::Break { label: None }],
                vec![
                    run(vec![
                        expr_stmt(Expr::Yield {
                            value: bx(tm("vres", 112)),
                        }),
                        elided("SetGeneratorState"),
                        decl("vresume", 140, drv(true)),
                        phi_assign("vrt", drv(false)),
                        phi_assign("vrv", tm("vresume", 140)),
                        exc_assign("vex", tm("vg", 103)),
                    ]),
                    SNode::Continue { label: None },
                ],
            ),
        ],
    };
    let [setup, init] = ys_setup_init(false);
    let mut bare = vec![setup.clone(), init.clone(), sync_w.clone()];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut bare, FunctionKind::Generator, &mut stats);
    assert_eq!((stats.yield_star_sites, stats.yield_star_bound), (1, 1));
    assert_eq!(bare.len(), 2, "{bare:?}");

    let mut frags = vec![
        try_node(vec![setup, init], vec![]),
        try_node(vec![sync_w], vec![]),
    ];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut frags, FunctionKind::Generator, &mut stats);
    assert_eq!((stats.yield_star_sites, stats.yield_star_bound), (1, 1));

    // 3. Async R3-C2/R3-X1 shape: AsyncGeneratorResolve + SetGeneratorState + positive throw/mode.
    let [asetup, ainit] = ys_setup_init(true);
    let mut async_nodes = vec![
        asetup,
        ainit,
        SNode::While {
            label: None,
            cond: None,
            body: vec![
                ys_header(),
                pos_dispatch(true),
                run(vec![
                    phi_decl("vexit", 110),
                    phi_decl("vm", 111),
                    decl(
                        "vres",
                        112,
                        Expr::Call {
                            callee: bx(tm("vm", 111)),
                            this: Some(bx(tm("vit", 102))),
                            args: vec![tm("vrv", 101)],
                            kind: CallKind::Dynamic,
                        },
                    ),
                    decl(
                        "aw0",
                        141,
                        Expr::Await {
                            value: bx(tm("vres", 112)),
                            uncaught: true,
                        },
                    ),
                    elided("SetGeneratorState"),
                    expr_stmt(Expr::Yield {
                        value: bx(tm("aw0", 141)),
                    }),
                    decl("vres1", 142, drv(true)),
                    exc_assign("vex", tm("vg", 103)),
                ]),
                if_node(
                    cmp(CmpOp::Eq, drv(false), num(1.0)),
                    vec![
                        run(vec![
                            Leaf::Raw(Stmt::Throw(tm("vres1", 142))),
                            Leaf::Raw(Stmt::Unreachable),
                        ]),
                        SNode::Break { label: None },
                    ],
                    vec![
                        run(vec![
                            elided("ThrowIfNotObject"),
                            decl("vdone", 113, prop(tm("vres1", 142), "done")),
                        ]),
                        if_node(
                            istrue(tm("vdone", 113)),
                            vec![exit_if("vres1", 142), SNode::Break { label: None }],
                            vec![
                                run(vec![
                                    decl("v2", 143, prop(tm("vres1", 142), "value")),
                                    decl(
                                        "av2",
                                        144,
                                        Expr::Await {
                                            value: bx(tm("v2", 143)),
                                            uncaught: true,
                                        },
                                    ),
                                    elided("SetGeneratorState"),
                                    expr_stmt(Expr::Yield {
                                        value: bx(tm("av2", 144)),
                                    }),
                                    decl("vres2", 145, drv(true)),
                                ]),
                                if_node(
                                    cmp(CmpOp::Eq, drv(false), num(1.0)),
                                    vec![
                                        run(vec![
                                            Leaf::Raw(Stmt::Throw(tm("vres2", 145))),
                                            Leaf::Raw(Stmt::Unreachable),
                                        ]),
                                        SNode::Break { label: None },
                                    ],
                                    vec![
                                        run(vec![
                                            decl("vf", 160, boolean(false)),
                                            decl(
                                                "agr",
                                                161,
                                                Expr::AsyncGeneratorResolve {
                                                    genobj: bx(tm("vg", 103)),
                                                    value: bx(tm("vres2", 145)),
                                                    done: bx(tm("vf", 160)),
                                                },
                                            ),
                                            elided("SetGeneratorState"),
                                            expr_stmt(Expr::Yield {
                                                value: bx(tm("agr", 161)),
                                            }),
                                            decl("r3", 146, drv(true)),
                                            decl("m3", 147, drv(false)),
                                            exc_assign("vex", tm("vg", 103)),
                                        ]),
                                        if_node(
                                            cmp(CmpOp::NotEq, tm("m3", 147), num(0.0)),
                                            vec![
                                                run(vec![
                                                    phi_assign("vrt", tm("m3", 147)),
                                                    phi_assign("vrv", tm("r3", 146)),
                                                ]),
                                                SNode::Continue { label: None },
                                            ],
                                            vec![],
                                        ),
                                        run(vec![
                                            decl(
                                                "aw3",
                                                148,
                                                Expr::Await {
                                                    value: bx(tm("r3", 146)),
                                                    uncaught: true,
                                                },
                                            ),
                                            elided("SetGeneratorState"),
                                            expr_stmt(Expr::Yield {
                                                value: bx(tm("aw3", 148)),
                                            }),
                                            decl("r4", 152, drv(true)),
                                            decl("m4", 153, drv(false)),
                                        ]),
                                        if_node(
                                            cmp(CmpOp::Eq, tm("m4", 153), num(1.0)),
                                            vec![
                                                run(vec![
                                                    phi_assign("vrt", tm("m4", 153)),
                                                    phi_assign("vrv", tm("r4", 152)),
                                                ]),
                                                SNode::Continue { label: None },
                                            ],
                                            vec![],
                                        ),
                                        run(vec![
                                            phi_assign("vrt", num(0.0)),
                                            phi_assign("vrv", tm("r4", 152)),
                                        ]),
                                        SNode::Continue { label: None },
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        },
    ];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut async_nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!((stats.yield_star_sites, stats.yield_star_bound), (1, 1));
    assert_eq!(async_nodes.len(), 2, "{async_nodes:?}");
}
