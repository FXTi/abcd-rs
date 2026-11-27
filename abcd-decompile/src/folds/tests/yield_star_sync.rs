//! Synchronous `yield*` loop, arm, tail, bare, and fragment fold unit tests.

use super::*;

#[test]
fn yield_star_sync_positive() {
    let mut nodes = ys_sync_shape();
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
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
    // The kind gate: only Generator/AsyncGenerator.
    let mut nodes = ys_sync_shape();
    let before = nodes.clone();
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(nodes, before);
}

#[test]
fn ys_match_loop_bail_pins() {
    // A helper: mutate the While of the sync shape; the loop match
    // must fail.
    fn bail(mutate: impl FnOnce(&mut SNode)) {
        let mut nodes = ys_sync_shape();
        mutate(ys_while(&mut nodes));
        assert!(
            ys_match_loop(&nodes[2], false).is_none(),
            "near-miss matched"
        );
    }
    // The candidate must be a `while (true)`.
    bail(|w| {
        let SNode::While { cond, .. } = w else {
            unreachable!()
        };
        *cond = Some(ident("c"));
    });
    // The significant-node skeleton: [header, dispatch, precall, …].
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body.truncate(2);
    });
    // The header must be a statement run…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body[0] = SNode::Honest("h".to_string());
    });
    // … non-empty…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body[0] = run(vec![]);
    });
    // … of phi decls…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body[0] = run(vec![
            expr_stmt(ident("x")),
            decl("vexit0", 105, boolean(false)),
        ]);
    });
    // … closed by the `exitReturn = false` declare.
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::Stmts(hdr) = &mut body[0] else {
            unreachable!()
        };
        hdr[5] = decl("vexit0", 105, boolean(true));
    });
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::Stmts(hdr) = &mut body[0] else {
            unreachable!()
        };
        hdr[5] = phi_decl("vexit0", 105);
    });
    // The dispatch must be an if…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body[1] = run(vec![phi_assign("vm0", tm("vnext", 201))]);
    });
    // … testing the mode phi…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut body[1] else {
            unreachable!()
        };
        *cond = istrue(tm("vrt", 100));
    });
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut body[1] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::StrictEq, tm("other", 99), num(2.0)));
    });
    // … whose NEXT arm opens with the call-block assigns.
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut body[1] else {
            unreachable!()
        };
        otherwise[0] = SNode::Honest("h".to_string());
    });
    // The THROW/RETURN split must be a single if…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { then, .. } = &mut body[1] else {
            unreachable!()
        };
        *then = vec![];
    });
    // … testing the same mode temp for THROW(1).
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { then, .. } = &mut body[1] else {
            unreachable!()
        };
        let SNode::If { cond, .. } = &mut then[0] else {
            unreachable!()
        };
        *cond = isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(2.0)));
    });
    // The RETURN arm must match…
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { then, .. } = &mut body[1] else {
            unreachable!()
        };
        let SNode::If { then: ret, .. } = &mut then[0] else {
            unreachable!()
        };
        *ret = vec![];
    });
    // … and so must the THROW arm.
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        let SNode::If { then, .. } = &mut body[1] else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut then[0] else {
            unreachable!()
        };
        *otherwise = vec![];
    });
    // … and the tail must match.
    bail(|w| {
        let SNode::While { body, .. } = w else {
            unreachable!()
        };
        body.truncate(6); // drop the trailing continue
    });
}

#[test]
fn ys_match_return_arm_bail_pins() {
    let phis: BTreeMap<String, ValueId> = [
        ("vrt".to_string(), ValueId::new(100)),
        ("vrv".to_string(), ValueId::new(101)),
        ("vit".to_string(), ValueId::new(102)),
    ]
    .into_iter()
    .collect();
    let arm: Vec<SNode> = ys_ret_arm(false);
    let refs: Vec<&SNode> = arm.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_some());
    // The undefined test must be a `method == undefined` test…
    let mut bad = arm.clone();
    let SNode::If { cond, .. } = &mut bad[2] else {
        unreachable!()
    };
    *cond = isfalse(tm("vret", 121));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // … on the looked-up method temp.
    let mut bad = arm.clone();
    let SNode::If { cond, .. } = &mut bad[2] else {
        unreachable!()
    };
    *cond = isfalse(cmp(CmpOp::Eq, tm("other", 99), undef()));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // The method-exists arm must be exactly one assign run…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[2] else {
        unreachable!()
    };
    *then = vec![];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // … to the call block…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[2] else {
        unreachable!()
    };
    let SNode::Stmts(assigns) = &mut then[0] else {
        unreachable!()
    };
    assigns[0] = Leaf::Raw(Stmt::PhiAssign {
        target: "vexit".to_string(),
        value: tm("vt", 120),
        to: BlockId::new(8),
        exceptional: false,
    });
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // … wiring the exitReturn phi to the `true` decl…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[2] else {
        unreachable!()
    };
    let SNode::Stmts(assigns) = &mut then[0] else {
        unreachable!()
    };
    assigns[0] = phi_assign("vexit", tm("other", 99));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // … with the not-exists arm being exactly `break`.
    let mut bad = arm.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    *otherwise = vec![];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // The arm contains only runs and the method-test if.
    let mut bad = arm.clone();
    bad.push(SNode::Continue { label: None });
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // No method test at all.
    let bad = [arm[0].clone(), arm[1].clone()];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // The sync propagation return must read a header phi.
    let mut bad = arm.clone();
    bad[1] = run(vec![Leaf::Raw(Stmt::Return(Some(tm("other", 99))))]);
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), false).is_none());
    // The async form: no propagation return needed.
    let arm: Vec<SNode> = ys_ret_arm(true);
    let refs: Vec<&SNode> = arm.iter().collect();
    assert!(ys_match_return_arm(&refs, &phis, BlockId::new(7), true).is_some());
}

#[test]
fn ys_match_throw_arm_bail_pins() {
    let phis: BTreeMap<String, ValueId> = [("vflag".to_string(), ValueId::new(104))]
        .into_iter()
        .collect();
    let arm: Vec<SNode> = ys_throw_arm();
    let refs: Vec<&SNode> = arm.iter().collect();
    let ok = ys_match_throw_arm(
        &refs,
        ValueId::new(102),
        "vexit",
        ValueId::new(105),
        BlockId::new(7),
        &phis,
    );
    assert_eq!(ok, Some(ValueId::new(104)));
    // The method lookup must read `it.throw`…
    let mut bad = arm.clone();
    let SNode::Stmts(decls) = &mut bad[0] else {
        unreachable!()
    };
    decls[0] = decl("vthrow", 130, prop(tm("other", 99), "throw"));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // … with the `throwM == undefined` temp tested next.
    let mut bad = arm.clone();
    let SNode::Stmts(decls) = &mut bad[0] else {
        unreachable!()
    };
    decls[1] = decl("veq", 131, cmp(CmpOp::Eq, tm("other", 99), undef()));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // The method-exists if must test `!eqM`…
    let mut bad = arm.clone();
    let SNode::If { cond, .. } = &mut bad[1] else {
        unreachable!()
    };
    *cond = istrue(tm("veq", 131));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // … its then being exactly the call-block assigns…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[1] else {
        unreachable!()
    };
    *then = vec![];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // … to the right block…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[1] else {
        unreachable!()
    };
    let SNode::Stmts(assigns) = &mut then[0] else {
        unreachable!()
    };
    assigns[0] = Leaf::Raw(Stmt::PhiAssign {
        target: "vexit".to_string(),
        value: tm("vexit0", 105),
        to: BlockId::new(8),
        exceptional: false,
    });
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // … wiring the exit phi to the exitReturn decl…
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[1] else {
        unreachable!()
    };
    let SNode::Stmts(assigns) = &mut then[0] else {
        unreachable!()
    };
    assigns[0] = phi_assign("vexit", tm("other", 99));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // … with an empty else.
    let mut bad = arm.clone();
    let SNode::If { otherwise, .. } = &mut bad[1] else {
        unreachable!()
    };
    *otherwise = vec![SNode::Break { label: None }];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // The close if must contain the elided ThrowNotExists.
    let mut bad = arm.clone();
    let SNode::If { then, .. } = &mut bad[2] else {
        unreachable!()
    };
    *then = vec![run(vec![expr_stmt(ident("x"))])];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // No close if at all.
    let bad = [arm[0].clone(), arm[1].clone()];
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // An if on a non-phi temp is neither dispatch.
    let mut bad = arm.clone();
    let SNode::If { cond, .. } = &mut bad[2] else {
        unreachable!()
    };
    *cond = istrue(tm("other", 99));
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
    // The arm contains only runs and ifs.
    let mut bad = arm.clone();
    bad.push(SNode::Break { label: None });
    let refs: Vec<&SNode> = bad.iter().collect();
    assert!(
        ys_match_throw_arm(
            &refs,
            ValueId::new(102),
            "vexit",
            ValueId::new(105),
            BlockId::new(7),
            &phis
        )
        .is_none()
    );
}

#[test]
fn ys_match_loop_tail_sync_bail_pins() {
    fn bail(mutate: impl FnOnce(&mut Vec<SNode>)) {
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
    // The precall run opens with the phi decls incl. the exit phi.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.remove(0); // the exitReturn phi decl
    });
    // The call's callee must be a precall phi…
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl("vres", 112, call1(tm("other", 99), tm("vrv", 101)));
    });
    // … its `this` must be the iterator phi…
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
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[2] = decl("vres", 112, call0(tm("vm", 111)));
    });
    // … and its single argument the received-value phi.
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
    // `done` must read `.done` off the call result.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre[3] = decl("vdone", 113, prop(tm("vres", 112), "finished"));
    });
    // Foreign precall leaves bail.
    bail(|body| {
        let SNode::Stmts(pre) = &mut body[2] else {
            unreachable!()
        };
        pre.push(expr_stmt(ident("extra")));
    });
    // The done test must be a positive flag test of `done`…
    bail(|body| {
        let SNode::If { cond, .. } = &mut body[3] else {
            unreachable!()
        };
        *cond = isfalse(tm("vdone", 113));
    });
    bail(|body| {
        let SNode::If { cond, .. } = &mut body[3] else {
            unreachable!()
        };
        *cond = istrue(tm("other", 99));
    });
    // … whose then arm is exactly `break`…
    bail(|body| {
        let SNode::If { then, .. } = &mut body[3] else {
            unreachable!()
        };
        *then = vec![];
    });
    // … with an empty else.
    bail(|body| {
        let SNode::If { otherwise, .. } = &mut body[3] else {
            unreachable!()
        };
        *otherwise = vec![run(vec![expr_stmt(ident("x"))])];
    });
    // The suspend run: `[yield res, resume = ResumeGenerator(g)]`.
    bail(|body| {
        let SNode::Stmts(susp) = &mut body[4] else {
            unreachable!()
        };
        susp[0] = expr_stmt(Expr::Yield {
            value: bx(tm("other", 99)),
        });
    });
    bail(|body| {
        let SNode::Stmts(susp) = &mut body[4] else {
            unreachable!()
        };
        susp[1] = decl("vresume", 140, ident("not_a_driver"));
    });
    bail(|body| {
        let SNode::Stmts(susp) = &mut body[4] else {
            unreachable!()
        };
        susp[1] = decl(
            "vresume",
            140,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("other", 99)),
            },
        );
    });
    // The loop-back assigns must carry both the mode and the value.
    bail(|body| {
        let SNode::Stmts(lb) = &mut body[5] else {
            unreachable!()
        };
        lb.remove(0);
    });
    bail(|body| {
        let SNode::Stmts(lb) = &mut body[5] else {
            unreachable!()
        };
        lb[1] = phi_assign("vrv", tm("other", 99));
    });
}

#[test]
fn ys_apply_bare_bail_pins() {
    // The loop must match…
    let mut nodes = ys_sync_shape();
    let SNode::While { body, .. } = ys_while(&mut nodes) else {
        unreachable!()
    };
    body.truncate(2);
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
    // … and sit at index ≥ 2 (setup + init precede it).
    let mut full = ys_sync_shape();
    let mut nodes = full.split_off(2);
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
    // The setup run must match.
    let mut nodes = ys_sync_shape();
    nodes[0] = run(vec![expr_stmt(ident("x"))]);
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
    // The init run must match.
    let mut nodes = ys_sync_shape();
    nodes[1] = run(vec![expr_stmt(ident("x"))]);
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
    // The sync completion dispatch must be the next sibling.
    let mut nodes = ys_sync_shape();
    nodes.pop();
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
    let mut nodes = ys_sync_shape();
    nodes[3] = SNode::Honest("h".to_string());
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 0);
}

#[test]
fn ys_apply_fragments_sync_positive_and_bails() {
    // Arrangement B: the structurer's try-fragment split.
    let sync_fragments = || {
        let [setup, init] = ys_setup_init(false);
        let full = ys_sync_shape();
        let w = full[2].clone();
        let exit = full[3].clone();
        vec![
            try_node(vec![setup, init], vec![]),
            try_node(vec![w], vec![]),
            try_node(vec![exit], vec![]),
        ]
    };
    let mut nodes = sync_fragments();
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(stats.yield_star_bound, 1);
    // The loop fragment now holds the yield* stmt; the setup
    // fragment dropped both plumbing runs; the exit fragment holds
    // the continuation.
    let SNode::Try { body, .. } = &nodes[1] else {
        unreachable!()
    };
    assert!(
        matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::Declare { value: Expr::YieldStar { .. }, .. }))),
        "{body:?}"
    );
    let SNode::Try { body, .. } = &nodes[0] else {
        unreachable!()
    };
    assert!(body.is_empty(), "{body:?}");
    let SNode::Try { body, .. } = &nodes[2] else {
        unreachable!()
    };
    assert!(
        matches!(&body[0], SNode::Stmts(run) if run.len() == 1),
        "the exit fragment holds the continuation: {body:?}"
    );
    // Nested single-child try wrappers descend to the innermost.
    let mut nodes = sync_fragments();
    nodes[1] = try_node(vec![nodes[1].clone()], vec![]);
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    // Bail pins (each refuses the fold).
    let bail = |mut nodes: Vec<SNode>| {
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 0, "{nodes:?}");
    };
    // The loop fragment must be a try holding a While…
    bail(vec![SNode::Honest("h".to_string())]);
    // … at the END of its innermost body.
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[1] else {
        unreachable!()
    };
    body.push(SNode::Honest("h".to_string()));
    bail(bad);
    // … matching the full driver shape.
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[1] else {
        unreachable!()
    };
    body[0] = SNode::While {
        label: None,
        cond: None,
        body: vec![],
    };
    bail(bad);
    // The setup fragment must exist…
    let bad = sync_fragments().split_off(1);
    bail(bad);
    // … be a try…
    let mut bad = sync_fragments();
    bad[0] = run(vec![]);
    bail(bad);
    // … with at least the setup + init runs…
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[0] else {
        unreachable!()
    };
    body.truncate(1);
    bail(bad);
    // … whose setup matches…
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[0] else {
        unreachable!()
    };
    body[0] = run(vec![expr_stmt(ident("x"))]);
    bail(bad);
    // … and whose init matches.
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[0] else {
        unreachable!()
    };
    body[1] = run(vec![expr_stmt(ident("x"))]);
    bail(bad);
    // The sync exit fragment must exist…
    let mut bad = sync_fragments();
    bad.pop();
    bail(bad);
    // … and match the completion dispatch.
    let mut bad = sync_fragments();
    let SNode::Try { body, .. } = &mut bad[2] else {
        unreachable!()
    };
    body[0] = run(vec![expr_stmt(ident("x"))]);
    bail(bad);
}

#[test]
fn ys_apply_fragments_async_positive() {
    let [setup, init] = ys_setup_init(true);
    let full = ys_async_shape();
    let w = full[2].clone();
    let mut nodes = vec![
        try_node(vec![setup, init], vec![]),
        try_node(vec![w], vec![]),
    ];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(stats.yield_star_bound, 1);
    // The loop fragment holds the yield* stmt + the in-loop
    // continuation; no exit fragment is needed for async.
    let SNode::Try { body, .. } = &nodes[1] else {
        unreachable!()
    };
    assert!(
        matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::Declare { value: Expr::YieldStar { .. }, .. }))),
        "{body:?}"
    );
    assert!(
        body.len() == 2,
        "yield* + the done-arm continuation: {body:?}"
    );
}

#[test]
fn ys_unbound_and_prefixed_positives() {
    // The unbound form: the completion value unused → bare
    // `yield* src;`.
    let mut nodes = ys_sync_shape();
    let SNode::If { then, .. } = &mut nodes[3] else {
        unreachable!()
    };
    *then = vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(stats.yield_star_bound, 0);
    assert_eq!(
        nodes[0],
        run(vec![expr_stmt(Expr::YieldStar {
            value: bx(ident("src")),
        })])
    );
    // A setup prefix survives the fold, hoisted above the yield*.
    let mut nodes = ys_sync_shape();
    let SNode::Stmts(setup) = &mut nodes[0] else {
        unreachable!()
    };
    setup.insert(0, expr_stmt(call0(ident("warmup"))));
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(nodes[0], run(vec![expr_stmt(call0(ident("warmup")))]));
    // … and likewise through the fragments arrangement.
    let mut nodes = ys_sync_shape();
    let SNode::Stmts(setup) = &mut nodes[0] else {
        unreachable!()
    };
    setup.insert(0, expr_stmt(call0(ident("warmup"))));
    let mut nodes = vec![
        try_node(vec![nodes[0].clone(), nodes[1].clone()], vec![]),
        try_node(vec![nodes[2].clone()], vec![]),
        try_node(vec![nodes[3].clone()], vec![]),
    ];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    let SNode::Try { body, .. } = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(body.len(), 1, "the prefix replaced the setup run: {body:?}");
    // A temp delegate with an empty prefix stops the inline walk.
    let run0 = run(vec![
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
    let uses: BTreeMap<ValueId, usize> = [(ValueId::new(205), 1)].into_iter().collect();
    let (delegate, ..) = ys_match_setup(&run0, false, &uses).expect("temp delegate, no prefix");
    assert_eq!(delegate, tm("td", 205));
    // ys_match_exit: the return arm's run must be the load+return pair.
    let full = ys_sync_shape();
    let lp = ys_match_loop(&full[2], false).expect("loop");
    let res = ys_sync_res(&full[2]).unwrap();
    let bad = if_node(
        isfalse(tm("vexit", 110)),
        vec![run(vec![expr_stmt(prop(tm("vres", 112), "value"))])],
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("vv2", 151))))])],
    );
    assert!(ys_match_exit(&bad, lp.exit_phi.0, res).is_none());
    // ys_apply_fragments directly: the entry guards.
    let mut nodes = vec![SNode::Honest("h".to_string())];
    let uses = BTreeMap::new();
    let mut stats = FoldStats::default();
    assert!(!ys_apply_fragments(&mut nodes, 0, false, &uses, &mut stats));
    let mut nodes = vec![try_node(vec![], vec![])];
    assert!(!ys_apply_fragments(&mut nodes, 0, false, &uses, &mut stats));
    // The setup fragment must be a try.
    let mut full = vec![
        try_node(
            vec![
                ys_setup_init(false)[0].clone(),
                ys_setup_init(false)[1].clone(),
            ],
            vec![],
        ),
        try_node(vec![ys_sync_shape()[2].clone()], vec![]),
        try_node(vec![ys_sync_shape()[3].clone()], vec![]),
    ];
    full[0] = SNode::Honest("h".to_string());
    assert!(!ys_apply_fragments(&mut full, 1, false, &uses, &mut stats));
    // The exit fragment's innermost body must hold a significant
    // node.
    let mut full = vec![
        try_node(
            vec![
                ys_setup_init(false)[0].clone(),
                ys_setup_init(false)[1].clone(),
            ],
            vec![],
        ),
        try_node(vec![ys_sync_shape()[2].clone()], vec![]),
        try_node(vec![SNode::Honest("h".to_string())], vec![]),
    ];
    assert!(!ys_apply_fragments(&mut full, 1, false, &uses, &mut stats));
}
