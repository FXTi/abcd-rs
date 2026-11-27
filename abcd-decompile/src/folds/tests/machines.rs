//! Generator (`function*`), `async` driver/machine (`await`), and async-generator (`async function*`) unit tests.

use super::*;

/// The mode dispatch on `m`: `if (m == 0) return r; if (m == 1)
/// throw r; <continuation>`.
fn gen_dispatch(m: &str, mv: u32, r: &str, rv: u32, cont: Vec<SNode>) -> SNode {
    if_node(
        cmp(CmpOp::Eq, tm(m, mv), num(0.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm(r, rv))))])],
        vec![if_node(
            cmp(CmpOp::Eq, tm(m, mv), num(1.0)),
            vec![run(vec![
                Leaf::Raw(Stmt::Throw(tm(r, rv))),
                Leaf::Raw(Stmt::Unreachable),
            ])],
            cont,
        )],
    )
}

/// A generator body: the entry site, one yield point whose resume
/// value is used (`const r1 = yield v`), and one whose is not.
/// Each site is ONE run: `[yield-stmt, r = ResumeGenerator(g),
/// m = GetResumeMode(g)]` followed by the mode dispatch sibling.
fn generator_body() -> Vec<SNode> {
    let site = |pre: Leaf, r: &str, rv: u32, m: &str, mv: u32| {
        run(vec![
            pre,
            decl(
                r,
                rv,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 50)),
                },
            ),
            decl(
                m,
                mv,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 50)),
                },
            ),
        ])
    };
    let yield_stmt = |v: &str| {
        expr_stmt(Expr::Yield {
            value: bx(Expr::IterResultObj {
                value: bx(ident(v)),
                done: bx(boolean(false)),
            }),
        })
    };
    vec![
        run(vec![
            decl(
                "g",
                50,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            expr_stmt(Expr::Yield { value: bx(undef()) }),
            decl(
                "r0",
                51,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 50)),
                },
            ),
            decl(
                "m0",
                52,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 50)),
                },
            ),
        ]),
        gen_dispatch("m0", 52, "r0", 51, vec![]),
        site(yield_stmt("v"), "r1", 53, "m1", 54),
        gen_dispatch("m1", 54, "r1", 53, vec![run(vec![expr_stmt(tm("r1", 53))])]),
        site(yield_stmt("w"), "r2", 55, "m2", 56),
        gen_dispatch(
            "m2",
            56,
            "r2",
            55,
            vec![run(vec![expr_stmt(ident("cont"))])],
        ),
    ]
}

#[test]
fn generator_machine_fold_positive() {
    let mut nodes = generator_body();
    let mut stats = FoldStats::default();
    generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.gen_driver_entry, 1);
    assert_eq!(stats.gen_driver_sites, 3);
    assert_eq!(stats.gen_driver_bound, 1);
    // The funcObj temp is swept once nothing references it.
    assert!(!nodes_use_temp(&nodes, ValueId::new(50)));
    // The bound yield keeps its resume temp as a declare.
    let bound = nodes.iter().any(|n| {
        matches!(
            n,
            SNode::Stmts(run) if run.iter().any(|l| matches!(
                l,
                Leaf::Raw(Stmt::Declare {
                    name,
                    value: Expr::Yield { .. },
                    ..
                }) if name == "r1"
            ))
        )
    });
    assert!(bound, "{nodes:?}");
    // The unbound yield is a bare expression statement.
    let bare = nodes.iter().any(|n| {
        matches!(
            n,
            SNode::Stmts(run) if run.iter().any(|l| matches!(
                l,
                Leaf::Raw(Stmt::Expr(Expr::Yield { value }))
                    if value.as_ref() == &ident("w")
            ))
        )
    });
    assert!(bare, "{nodes:?}");
    // Non-generator kinds are a no-op.
    let mut nodes = generator_body();
    let before = nodes.clone();
    let mut stats = FoldStats::default();
    generator_machine_fold(&mut nodes, FunctionKind::Function, &mut stats);
    assert_eq!(nodes, before);
    assert_eq!(stats.gen_driver_sites, 0);
    // Two CreateGenerator temps are not the vendor shape.
    let mut nodes = generator_body();
    let SNode::Stmts(entry) = &mut nodes[0] else {
        unreachable!()
    };
    entry.push(decl(
        "g2",
        90,
        Expr::CreateGenerator {
            func: bx(closure("h")),
        },
    ));
    let mut stats = FoldStats::default();
    generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.gen_driver_sites, 0);
    // The entry gate: the dispatch must follow the pair.
    let mut nodes = generator_body();
    nodes[1] = run(vec![expr_stmt(ident("not_a_dispatch"))]);
    let mut stats = FoldStats::default();
    generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.gen_driver_entry, 0);
}

#[test]
fn generator_entry_nested_in_regions() {
    // entry_site_matches recurses through if/loop/try regions.
    for wrap in [
        |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::While {
                label: None,
                cond: Some(ident("c")),
                body: site,
            }]
        },
        |site: Vec<SNode>| {
            vec![SNode::Labeled {
                label: "l".to_string(),
                body: site,
            }]
        },
        |site: Vec<SNode>| vec![try_node(site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::Try {
                body: vec![],
                catches: vec![catch("e", site)],
                note: None,
                finally: Some(vec![]),
            }]
        },
    ] {
        let mut nodes = wrap(generator_body());
        let mut stats = FoldStats::default();
        generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.gen_driver_entry, 1, "nested entry gate");
    }
}

#[test]
fn generator_driver_site_bail_pins() {
    let body = generator_body();
    let mut cx = GenDriverCx {
        genobj: ValueId::new(50),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
    };
    assert!(match_driver_site(&body, 0, &mut cx).is_some());
    assert!(match_driver_site(&body, 2, &mut cx).is_some());
    // The site must be a statement run…
    assert!(match_driver_site(&[SNode::Honest("h".to_string())], 0, &mut cx).is_none());
    // … ending in the ResumeGenerator/GetResumeMode pair.
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site.pop();
    assert!(match_driver_site(&bad, 0, &mut cx).is_none());
    // … on the SAME genobj temp.
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site[3] = decl(
        "m0",
        52,
        Expr::GeneratorDriver {
            resume: false,
            genobj: bx(tm("other", 99)),
        },
    );
    assert!(match_driver_site(&bad, 0, &mut cx).is_none());
    // The pre leaf must be a yield…
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site[1] = expr_stmt(ident("x"));
    assert!(match_driver_site(&bad, 0, &mut cx).is_none());
    // … wrapping a `done: false` iter-result at a real yield point…
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[2] else {
        unreachable!()
    };
    site[0] = expr_stmt(Expr::Yield {
        value: bx(Expr::IterResultObj {
            value: bx(ident("v")),
            done: bx(boolean(true)),
        }),
    });
    assert!(match_driver_site(&bad, 2, &mut cx).is_none());
    // … or the entry undefined, and the entry's run must declare the
    // genobj it suspends.
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site.remove(0);
    assert!(!entry_site_matches(&bad, &mut cx));
}

#[test]
fn generator_dispatch_bail_pins() {
    let mut consumed = BTreeSet::new();
    let env = BTreeMap::new();
    let ok = gen_dispatch("m", 52, "r", 51, vec![run(vec![expr_stmt(ident("cont"))])]);
    let cont = match_dispatch(&ok, ValueId::new(52), ValueId::new(51), &env, &mut consumed);
    assert_eq!(cont, Some(vec![run(vec![expr_stmt(ident("cont"))])]));
    // The dispatch node must be an if.
    assert!(
        match_dispatch(
            &SNode::Honest("h".to_string()),
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed,
        )
        .is_none()
    );
    // … on a `mode == number` test…
    let bad = if_node(ident("c"), vec![], vec![]);
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // … of the matched mode temp…
    let bad = if_node(
        cmp(CmpOp::Eq, tm("other", 99), num(0.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // … with a resolvable immediate (a literal or known const temp).
    let bad = if_node(
        cmp(CmpOp::Eq, tm("m", 52), tm("c", 98)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    let bad = if_node(
        cmp(CmpOp::Eq, tm("m", 52), call0(ident("f"))),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // Only RETURN(0)/THROW(1) cases…
    let bad = if_node(
        cmp(CmpOp::Eq, tm("m", 52), num(5.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // … each once: a second RETURN test mid-chain bails.
    let bad = if_node(
        cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![if_node(
            cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
            vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            vec![],
        )],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // The chain descends through a pure-const run (the optimized
    // profile) but nothing else.
    let env: BTreeMap<ValueId, u64> = [(ValueId::new(98), 1.0f64.to_bits())].into_iter().collect();
    let good = if_node(
        cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![
            run(vec![decl("c1", 98, num(1.0))]),
            if_node(
                cmp(CmpOp::Eq, tm("m", 52), tm("c1", 98)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 51)))])],
                vec![run(vec![expr_stmt(ident("cont"))])],
            ),
        ],
    );
    let cont = match_dispatch(
        &good,
        ValueId::new(52),
        ValueId::new(51),
        &env,
        &mut consumed,
    );
    assert_eq!(cont, Some(vec![run(vec![expr_stmt(ident("cont"))])]));
    assert!(consumed.contains(&ValueId::new(98)));
    let bad = if_node(
        cmp(CmpOp::Eq, tm("m", 52), num(0.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
        vec![run(vec![decl("c1", 98, ident("not_a_const"))])],
    );
    assert!(
        match_dispatch(
            &bad,
            ValueId::new(52),
            ValueId::new(51),
            &env,
            &mut consumed
        )
        .is_none()
    );
    // mode_test: polarity wraps and operand order.
    let (bits, pos) = mode_test(
        &isfalse(cmp(CmpOp::Eq, num(1.0), tm("m", 52))),
        ValueId::new(52),
        &env,
        &mut consumed,
    )
    .expect("wrapped reversed");
    assert_eq!(f64::from_bits(bits), 1.0);
    assert!(!pos);
    let (.., pos) = mode_test(
        &istrue(cmp(CmpOp::Eq, tm("m", 52), num(0.0))),
        ValueId::new(52),
        &env,
        &mut consumed,
    )
    .unwrap();
    assert!(pos);
    assert!(mode_test(&ident("c"), ValueId::new(52), &env, &mut consumed).is_none());
    // check_return_arm / check_throw_arm shapes.
    let resume = ValueId::new(51);
    assert!(
        check_return_arm(
            &[run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))])],
            resume
        )
        .is_some()
    );
    // … with dead loop-bookkeeping breaks after the return.
    assert!(
        check_return_arm(
            &[
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))]),
                SNode::Break { label: None },
            ],
            resume,
        )
        .is_some()
    );
    assert!(check_return_arm(&[SNode::Honest("h".to_string())], resume).is_none());
    assert!(
        check_return_arm(
            &[
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("r", 51))))]),
                run(vec![expr_stmt(ident("x"))]),
            ],
            resume,
        )
        .is_none()
    );
    assert!(
        check_return_arm(
            &[run(vec![Leaf::Raw(Stmt::Return(Some(tm("x", 99))))])],
            resume
        )
        .is_none()
    );
    assert!(check_return_arm(&[run(vec![expr_stmt(ident("x"))])], resume).is_none());
    assert!(check_throw_arm(&[run(vec![Leaf::Raw(Stmt::Throw(tm("r", 51)))])], resume).is_some());
    assert!(
        check_throw_arm(
            &[run(vec![
                Leaf::Raw(Stmt::Throw(tm("r", 51))),
                Leaf::Raw(Stmt::Unreachable),
            ])],
            resume,
        )
        .is_some()
    );
    assert!(check_throw_arm(&[SNode::Honest("h".to_string())], resume).is_none());
    assert!(check_throw_arm(&[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 99)))])], resume).is_none());
    assert!(check_throw_arm(&[run(vec![expr_stmt(ident("x"))])], resume).is_none());
    // resolve_num directly.
    assert_eq!(
        resolve_num(&num(2.0), &env, &mut consumed),
        Some(2.0f64.to_bits())
    );
    assert_eq!(
        resolve_num(&tm("c1", 98), &env, &mut consumed),
        Some(1.0f64.to_bits())
    );
    assert_eq!(resolve_num(&tm("unknown", 97), &env, &mut consumed), None);
    assert_eq!(resolve_num(&ident("x"), &env, &mut consumed), None);
}

// ── N68/G6: the async-completion fold ──────────────────────────

#[test]
fn async_driver_fold_direct_and_temp_forms() {
    // The inlined form: `return asyncDriver(v)` directly.
    for (resolve, is_throw) in [(true, false), (false, true)] {
        let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
            Expr::AsyncDriver {
                resolve,
                value: bx(ident("v")),
            },
        )))])];
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_driver, 1);
        let SNode::Stmts(run) = &nodes[0] else {
            unreachable!()
        };
        if is_throw {
            assert!(matches!(&run[0], Leaf::Raw(Stmt::Throw(e)) if *e == ident("v")));
        } else {
            assert!(matches!(&run[0], Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("v")));
        }
    }
    // The temp form: `const t = asyncDriver(v); return t;`.
    let mut nodes = vec![run(vec![
        decl(
            "t",
            60,
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
        ),
        Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
    ])];
    let mut stats = FoldStats::default();
    async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_driver, 1);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(matches!(&got[0], Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("v")));
    assert_eq!(got.len(), 1);
    // … and `reject` + `throw t`.
    let mut nodes = vec![run(vec![
        decl(
            "t",
            60,
            Expr::AsyncDriver {
                resolve: false,
                value: bx(ident("e")),
            },
        ),
        Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
    ])];
    let mut stats = FoldStats::default();
    async_driver_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.async_driver, 1);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(matches!(&got[0], Leaf::Raw(Stmt::Throw(e)) if *e == ident("e")));
    // The temp form requires the adjacent return…
    let mut nodes = vec![run(vec![
        decl(
            "t",
            60,
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
        ),
        expr_stmt(ident("gap")),
        Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
    ])];
    let mut stats = FoldStats::default();
    async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_driver, 0);
    // … and no other uses of the temp.
    let mut nodes = vec![run(vec![
        decl(
            "t",
            60,
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
        ),
        Leaf::Raw(Stmt::Return(Some(tm("t", 60)))),
        expr_stmt(tm("t", 60)),
    ])];
    let mut stats = FoldStats::default();
    async_driver_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_driver, 0);
    // Non-async kinds are a no-op.
    let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
        Expr::AsyncDriver {
            resolve: true,
            value: bx(ident("v")),
        },
    )))])];
    let mut stats = FoldStats::default();
    async_driver_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.async_driver, 0);
}

// ── N68: the async suspend/resume machine fold ─────────────────

#[test]
fn async_machine_fold_positive_with_const_env() {
    let mut nodes = async_body();
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 1);
    // The machinery, the entry temp, AND the consumed mode const
    // are all swept; the folded await + the continuation remain.
    assert_eq!(
        nodes,
        vec![
            run(vec![expr_stmt(Expr::Await {
                value: bx(ident("p")),
                uncaught: true,
            })]),
            run(vec![expr_stmt(ident("cont"))]),
        ],
        "{nodes:?}"
    );
    // A used resume temp binds at the await site (`const r = await p`).
    let mut nodes = async_body();
    let SNode::If { otherwise, .. } = &mut nodes[1] else {
        unreachable!()
    };
    otherwise[0] = run(vec![expr_stmt(tm("r", 13))]);
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 1);
    assert_eq!(stats.async_machine_bound, 1);
    assert!(matches!(
        &nodes[0],
        SNode::Stmts(run)
            if matches!(&run[0], Leaf::Raw(Stmt::Declare { name, value: Expr::Await { .. }, .. }) if name == "r")
    ));
    // The inlined form: the suspend carries the await directly.
    let mut nodes = async_body();
    let SNode::Stmts(site) = &mut nodes[0] else {
        unreachable!()
    };
    site.remove(2); // the await decl
    site[2] = expr_stmt(Expr::Yield {
        value: bx(Expr::Await {
            value: bx(ident("p")),
            uncaught: true,
        }),
    });
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 1);
    // The inlined mode test: no mode decl, GetResumeMode inline in
    // the condition; the throw arm throws an inlined ResumeGenerator.
    let mut nodes = async_body();
    let SNode::Stmts(site) = &mut nodes[0] else {
        unreachable!()
    };
    site.pop(); // the mode decl
    site.remove(4); // and the resume decl (the throw is inlined too)
    let SNode::If { cond, then, .. } = &mut nodes[1] else {
        unreachable!()
    };
    *cond = cmp(
        CmpOp::Eq,
        Expr::GeneratorDriver {
            resume: false,
            genobj: bx(tm("g", 10)),
        },
        tm("cn", 11),
    );
    then[0] = run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
        resume: true,
        genobj: bx(tm("g", 10)),
    }))]);
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 1);
    // Kind gate + entry gate.
    let mut nodes = async_body();
    let before = nodes.clone();
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Function, &mut stats);
    assert_eq!(nodes, before);
    let mut nodes = async_body();
    let SNode::Stmts(site) = &mut nodes[0] else {
        unreachable!()
    };
    site.remove(0); // no AsyncFunctionEnter temp
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 0);
    // Two entry temps are not the vendor shape.
    let mut nodes = async_body();
    let SNode::Stmts(site) = &mut nodes[0] else {
        unreachable!()
    };
    site.insert(
        1,
        decl(
            "g2",
            19,
            Expr::Fallback {
                op: "AsyncFunctionEnter",
                note: "entry protocol",
                operands: vec![],
            },
        ),
    );
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 0);
    // A funcObj use outside the machinery keeps everything loud.
    let mut nodes = async_body();
    nodes.push(run(vec![expr_stmt(call1(ident("f"), tm("g", 10)))]));
    let mut stats = FoldStats::default();
    async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
    assert_eq!(stats.async_machine_sites, 0);
}

#[test]
fn async_machine_await_site_and_dispatch_bails() {
    let mk_cx = |nodes: &Vec<SNode>| {
        let mut uses = BTreeMap::new();
        count_temp_uses(nodes, &mut uses);
        let mut const_env = BTreeMap::new();
        walk_leaves(nodes, &mut |l| {
            if let Leaf::Raw(Stmt::Declare {
                value: Expr::Lit(Lit::Number(bits)),
                value_id,
                ..
            }) = l
            {
                const_env.insert(*value_id, *bits);
            }
        });
        AsyncMachineCx {
            genobj: ValueId::new(10),
            aliases: [ValueId::new(10)].into_iter().collect(),
            exit_throws: BTreeSet::new(),
            const_env,
            consumed_consts: BTreeSet::new(),
            uses,
        }
    };
    let body = async_body();
    let mut cx = mk_cx(&body);
    assert!(match_await_site(&body, 0, &mut cx).is_some());
    // The site must be a statement run.
    assert!(match_await_site(&[SNode::Honest("h".to_string())], 0, &mut cx).is_none());
    // … with a suspend before the pair…
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site.remove(3);
    let mut cx = mk_cx(&bad);
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // … whose declared await temp is used only by the suspend.
    let mut bad = body.clone();
    bad.push(run(vec![expr_stmt(tm("a", 12))]));
    let mut cx = mk_cx(&bad);
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // … and the await declare must precede it.
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site[2] = decl("a", 12, ident("p"));
    let mut cx = mk_cx(&bad);
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // The dispatch must follow (past phi-partition runs).
    let mut bad = body.clone();
    bad[1] = run(vec![expr_stmt(ident("not_a_dispatch"))]);
    let mut cx = mk_cx(&bad);
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // A phi-partition run between the site and the dispatch is
    // skipped by the offset walk.
    let mut good = body.clone();
    good.insert(1, run(vec![phi_assign("pb", tm("a", 12))]));
    // (the phi-assign use of `a` breaks the single-use rule, so
    // drop the check by using an unrelated value)
    let SNode::Stmts(part) = &mut good[1] else {
        unreachable!()
    };
    part[0] = phi_assign("pb", ident("z"));
    let mut cx = mk_cx(&good);
    let site = match_await_site(&good, 0, &mut cx).expect("dispatch past a phi partition");
    assert_eq!(site.dispatch_off, 2);

    // match_async_dispatch, directly.
    let mut cx = mk_cx(&body);
    let dispatch = if_node(
        cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
        vec![run(vec![expr_stmt(ident("cont"))])],
    );
    assert!(
        match_async_dispatch(
            &dispatch,
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx
        )
        .is_some()
    );
    // The negative-polarity form puts the throw in the else arm.
    let dispatch_neg = if_node(
        isfalse(cmp(CmpOp::Eq, tm("m", 14), num(1.0))),
        vec![run(vec![expr_stmt(ident("cont"))])],
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
    );
    assert!(
        match_async_dispatch(
            &dispatch_neg,
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx
        )
        .is_some()
    );
    // Not an if / not a compare / not the mode operand / not THROW.
    assert!(
        match_async_dispatch(
            &SNode::Honest("h".to_string()),
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_none()
    );
    assert!(
        match_async_dispatch(
            &if_node(ident("c"), vec![], vec![]),
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_none()
    );
    assert!(
        match_async_dispatch(
            &if_node(cmp(CmpOp::Eq, tm("x", 99), num(1.0)), vec![], vec![]),
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_none()
    );
    assert!(
        match_async_dispatch(
            &if_node(
                cmp(CmpOp::Eq, tm("m", 14), num(0.0)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
                vec![],
            ),
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_none()
    );
    // A THROW arm matching neither check refuses the site.
    assert!(
        match_async_dispatch(
            &if_node(
                cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
                vec![run(vec![expr_stmt(ident("x"))])],
                vec![],
            ),
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_none()
    );
}

#[test]
fn async_machine_throw_and_break_arms() {
    let genobj: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    // check_async_throw_arm shapes.
    assert!(
        check_async_throw_arm(
            &[run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
            Some(ValueId::new(13)),
            &genobj,
        )
        .is_some()
    );
    // … with the dead marker, phi partitions, and dead breaks.
    assert!(
        check_async_throw_arm(
            &[
                run(vec![phi_assign("p", ident("z"))]),
                run(vec![
                    Leaf::Raw(Stmt::Throw(tm("r", 13))),
                    Leaf::Raw(Stmt::Unreachable),
                ]),
                SNode::Break { label: None },
            ],
            Some(ValueId::new(13)),
            &genobj,
        )
        .is_some()
    );
    // … or the inlined ResumeGenerator when nothing was declared.
    assert!(
        check_async_throw_arm(
            &[run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 10)),
            }))])],
            None,
            &genobj,
        )
        .is_some()
    );
    // Two significant runs / a wrong temp / no throw at all bail.
    assert!(
        check_async_throw_arm(
            &[
                run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))]),
                run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))]),
            ],
            Some(ValueId::new(13)),
            &genobj,
        )
        .is_none()
    );
    assert!(
        check_async_throw_arm(
            &[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 99)))])],
            Some(ValueId::new(13)),
            &genobj,
        )
        .is_none()
    );
    assert!(check_async_throw_arm(&[], Some(ValueId::new(13)), &genobj).is_none());
    assert!(
        check_async_throw_arm(
            &[if_node(ident("c"), vec![], vec![])],
            Some(ValueId::new(13)),
            &genobj,
        )
        .is_none()
    );
    // check_async_break_arm: the loop-exit routing needs the
    // pre-verified continuation throw.
    let cx = AsyncMachineCx {
        genobj: ValueId::new(10),
        aliases: genobj.clone(),
        exit_throws: [ValueId::new(13)].into_iter().collect(),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
        uses: BTreeMap::new(),
    };
    assert!(
        check_async_break_arm(
            &[
                run(vec![phi_assign("p", ident("z"))]),
                SNode::Break { label: None }
            ],
            Some(ValueId::new(13)),
            &cx,
        )
        .is_some()
    );
    assert!(check_async_break_arm(&[], Some(ValueId::new(13)), &cx).is_none());
    assert!(
        check_async_break_arm(
            &[SNode::Break {
                label: Some("l".to_string()),
            }],
            Some(ValueId::new(13)),
            &cx,
        )
        .is_none()
    );
    assert!(
        check_async_break_arm(
            &[run(vec![expr_stmt(ident("x"))])],
            Some(ValueId::new(13)),
            &cx,
        )
        .is_none()
    );
    let cx_missing = AsyncMachineCx {
        exit_throws: BTreeSet::new(),
        ..cx
    };
    assert!(
        check_async_break_arm(
            &[SNode::Break { label: None }],
            Some(ValueId::new(13)),
            &cx_missing,
        )
        .is_none()
    );
    assert!(check_async_break_arm(&[SNode::Break { label: None }], None, &cx_missing).is_none());
}

#[test]
fn async_machine_alias_and_sweep_machinery() {
    // funcobj_aliases: the phi-alias closure of the funcObj.
    let nodes = vec![run(vec![
        phi_decl("p1", 20),
        phi_decl("p2", 21),
        phi_decl("p3", 22),
        phi_decl("dead", 23),
        phi_assign("p1", tm("g", 10)),  // real source
        phi_assign("p2", tm("p1", 20)), // chained alias
        phi_assign("p2", tm("p2", 21)), // self-assign: neutral
        phi_assign("p3", ident("x")),   // foreign source: not an alias
    ])];
    let aliases = funcobj_aliases(&nodes, ValueId::new(10));
    assert!(aliases.contains(&ValueId::new(20)));
    assert!(aliases.contains(&ValueId::new(21)));
    assert!(!aliases.contains(&ValueId::new(22)));
    assert!(!aliases.contains(&ValueId::new(23)));
    // funcobj_uses_are_machinery: genobj-slot operands and phi
    // routing are machinery; anything richer is not.
    let ok = vec![
        run(vec![decl(
            "r",
            30,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 10)),
            },
        )]),
        run(vec![phi_assign("p1", tm("g", 10))]),
    ];
    assert!(funcobj_uses_are_machinery(&ok, &aliases));
    let bad = vec![run(vec![expr_stmt(call1(ident("f"), tm("g", 10)))])];
    assert!(!funcobj_uses_are_machinery(&bad, &aliases));
    let bad = vec![run(vec![phi_assign("p1", call1(ident("f"), tm("g", 10)))])];
    assert!(!funcobj_uses_are_machinery(&bad, &aliases));
    let bad = vec![run(vec![decl(
        "r",
        30,
        Expr::GeneratorDriver {
            resume: true,
            genobj: bx(call1(ident("f"), tm("g", 10))),
        },
    )])];
    assert!(!funcobj_uses_are_machinery(&bad, &aliases));
    // sweep_async_machinery: the dead bookkeeping web goes away.
    let mut nodes = vec![run(vec![
        phi_decl("pa", 20),
        phi_assign("pa", tm("g", 10)),
        decl("c0", 24, num(1.0)),
    ])];
    let consumed: BTreeSet<ValueId> = [ValueId::new(24)].into_iter().collect();
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &consumed);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(got.is_empty(), "the whole web stripped: {got:?}");
    // A live alias (a phi read elsewhere) keeps the web.
    let mut nodes = vec![run(vec![
        phi_decl("pa", 20),
        phi_assign("pa", tm("g", 10)),
        expr_stmt(tm("pa", 20)),
    ])];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10), ValueId::new(20)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(got.len(), 3, "live alias keeps everything: {got:?}");
    // A chain feeding a live alias stays alive transitively.
    let mut nodes = vec![run(vec![
        phi_decl("pa", 20),
        phi_decl("pb", 21),
        phi_assign("pa", tm("g", 10)),
        phi_assign("pb", tm("pa", 20)),
        expr_stmt(tm("pb", 21)),
    ])];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10), ValueId::new(20), ValueId::new(21)]
        .into_iter()
        .collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(got.len(), 5, "transitively alive: {got:?}");
    // An alias-valued assign into a dead non-alias phi loses just
    // the assign.
    let mut nodes = vec![
        run(vec![phi_decl("pa", 20), phi_assign("pa", tm("g", 10))]),
        run(vec![phi_decl("pb", 21), phi_assign("pb", tm("g", 10))]),
    ];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(got.is_empty(), "dead alias phi stripped: {got:?}");
    // The non-alias phi run kept its assign-less decl… wait: `pb`
    // has no PhiDecl — only the assign, which is stripped.
    let SNode::Stmts(got) = &nodes[1] else {
        unreachable!()
    };
    assert!(got.is_empty(), "{got:?}");
    // A richer phi-assign value reading an alias is a real use.
    let mut nodes = vec![run(vec![phi_assign("pa", call1(ident("f"), tm("g", 10)))])];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(got.len(), 1, "a real use keeps the assign");
}

#[test]
fn loop_exit_throw_collection() {
    // The continuation-throw collector descends past phi partitions
    // and try wrappers, and recurses into every region kind.
    let t = || tm("rt", 40);
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        SNode::Honest("h".to_string()),
        run(vec![phi_assign("p", ident("z"))]),
        run(vec![Leaf::Raw(Stmt::Throw(t()))]),
    ];
    let out = collect_loop_exit_throws(&nodes);
    assert!(out.contains(&ValueId::new(40)), "{out:?}");
    // A loop inside a region whose OWN continuation has nothing:
    // the search ascends the stack.
    let nodes = vec![
        SNode::Try {
            body: vec![
                SNode::If {
                    cond: ident("c"),
                    then: vec![SNode::While {
                        label: None,
                        cond: None,
                        body: vec![],
                    }],
                    otherwise: vec![],
                },
                SNode::DoWhile {
                    label: None,
                    body: vec![],
                    cond: ident("d"),
                },
                SNode::Labeled {
                    label: "l".to_string(),
                    body: vec![SNode::While {
                        label: None,
                        cond: None,
                        body: vec![],
                    }],
                },
            ],
            catches: vec![catch(
                "e",
                vec![SNode::While {
                    label: None,
                    cond: None,
                    body: vec![],
                }],
            )],
            note: None,
            finally: Some(vec![SNode::While {
                label: None,
                cond: None,
                body: vec![],
            }]),
        },
        run(vec![Leaf::Raw(Stmt::Throw(t()))]),
    ];
    let out = collect_loop_exit_throws(&nodes);
    // The nested loops' continuation (the try's catch-less tail)
    // is not a throw; only the sibling-after-try reading differs.
    let _ = out;
    // first_significant_stmt shapes, via the collector's result:
    // a loop followed by a non-throw significant statement yields
    // nothing.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        run(vec![expr_stmt(ident("x"))]),
    ];
    assert!(collect_loop_exit_throws(&nodes).is_empty());
    // A synthetic leaf is not a throw.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        run(vec![Leaf::Decl {
            name: "d".to_string(),
            mutable: true,
            value: None,
        }]),
    ];
    assert!(collect_loop_exit_throws(&nodes).is_empty());
    // An if/switch after the loop: no unique first statement.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        if_node(ident("c"), vec![], vec![]),
    ];
    assert!(collect_loop_exit_throws(&nodes).is_empty());
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        SNode::Switch {
            disc: ident("d"),
            cases: vec![],
        },
    ];
    assert!(collect_loop_exit_throws(&nodes).is_empty());
    // An empty try wrapper falls through to the next sibling.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        try_node(vec![], vec![]),
        run(vec![Leaf::Raw(Stmt::Throw(t()))]),
    ];
    let out = collect_loop_exit_throws(&nodes);
    assert!(out.contains(&ValueId::new(40)));
    // A try whose body's first significant statement is a throw.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        try_node(vec![run(vec![Leaf::Raw(Stmt::Throw(t()))])], vec![]),
    ];
    let out = collect_loop_exit_throws(&nodes);
    assert!(out.contains(&ValueId::new(40)));
}

// ── d-P14: the async-generator machine fold ────────────────────

#[test]
fn async_generator_fold_entry_yield_and_completion() {
    let mut nodes = agen_body();
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 1);
    assert_eq!(stats.agen_yields, 1);
    assert_eq!(stats.agen_returns, 1);
    // The yield point folded to a bare `yield v`; the completion
    // resolve to `return undefinedv`.
    let yield_stmt = nodes.iter().any(|n| {
        matches!(
            n,
            SNode::Stmts(run) if run.iter().any(|l| matches!(
                l,
                Leaf::Raw(Stmt::Expr(Expr::Yield { value }))
                    if value.as_ref() == &ident("v")
            ))
        )
    });
    assert!(yield_stmt, "{nodes:?}");
    let ret = nodes.iter().any(|n| {
        matches!(
            n,
            SNode::Stmts(run) if run.iter().any(|l| matches!(
                l,
                Leaf::Raw(Stmt::Return(Some(e))) if *e == ident("undefinedv")
            ))
        )
    });
    assert!(ret, "{nodes:?}");
    // The genobj temp is swept.
    assert!(!nodes_use_temp(&nodes, ValueId::new(20)));
    // The kind gate: only async generators.
    let mut nodes = agen_body();
    let before = nodes.clone();
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(nodes, before);
    // Two genobj temps are not the vendor shape.
    let mut nodes = agen_body();
    let SNode::Stmts(entry) = &mut nodes[0] else {
        unreachable!()
    };
    entry.push(decl(
        "g2",
        90,
        Expr::CreateGenerator {
            func: bx(closure("h")),
        },
    ));
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 0);
    // A non-machinery genobj use keeps everything loud.
    let mut nodes = agen_body();
    nodes.push(run(vec![expr_stmt(call1(ident("f"), tm("g", 20)))]));
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 0);
}

#[test]
fn agen_entry_elision_variants_and_bails() {
    // The entry site elides inside if/loop/catch regions too.
    for wrap in [
        |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::While {
                label: None,
                cond: Some(ident("c")),
                body: site,
            }]
        },
        |site: Vec<SNode>| {
            vec![SNode::Labeled {
                label: "l".to_string(),
                body: site,
            }]
        },
        |site: Vec<SNode>| vec![try_node(site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::Try {
                body: vec![run(vec![expr_stmt(ident("x"))])],
                catches: vec![catch("e", site)],
                note: None,
                finally: None,
            }]
        },
    ] {
        let mut nodes = wrap(vec![run(vec![
            decl(
                "g",
                20,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            expr_stmt(Expr::Yield { value: bx(undef()) }),
        ])]);
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 1, "nested entry elision");
    }
    // The entry suspend must follow the decl (past const decls).
    let mut nodes = vec![run(vec![
        decl(
            "g",
            20,
            Expr::CreateGenerator {
                func: bx(closure("f")),
            },
        ),
        expr_stmt(ident("not_a_suspend")),
    ])];
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 0);
    // No CreateGenerator decl at all.
    let mut nodes = vec![run(vec![expr_stmt(ident("x"))])];
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 0);
    // agen_uses_are_machinery directly: slot positions only.
    assert!(agen_uses_are_machinery(&agen_body(), ValueId::new(20)));
    let bad = vec![run(vec![expr_stmt(call1(ident("f"), tm("g", 20)))])];
    assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
    // … the IterResultObj done slot is not a legal position…
    let bad = vec![run(vec![Leaf::Raw(Stmt::Return(Some(
        Expr::IterResultObj {
            value: bx(ident("x")),
            done: bx(tm("g", 20)),
        },
    )))])];
    assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
    // … and a rich phi-assign value reading the genobj is not
    // machinery (a plain `phi = g` self-route is).
    let ok = vec![run(vec![phi_assign("p", tm("g", 20))])];
    assert!(agen_uses_are_machinery(&ok, ValueId::new(20)));
    let bad = vec![run(vec![phi_assign("p", call1(ident("f"), tm("g", 20)))])];
    assert!(!agen_uses_are_machinery(&bad, ValueId::new(20)));
}

#[test]
fn agen_fold_run_explicit_return_and_bails() {
    // The explicit-return site: `[decl a = await v, suspend(a),
    // decl r = ResumeGenerator(g), return r]` → `return v`.
    let site_run = || {
        vec![
            decl(
                "a",
                40,
                Expr::Await {
                    value: bx(ident("v")),
                    uncaught: true,
                },
            ),
            expr_stmt(Expr::Yield {
                value: bx(tm("a", 40)),
            }),
            decl(
                "r",
                41,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                },
            ),
            Leaf::Raw(Stmt::Return(Some(tm("r", 41)))),
        ]
    };
    let mut leaves = site_run();
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 1);
    assert_eq!(
        leaves,
        vec![Leaf::Raw(Stmt::Return(Some(ident("v"))))],
        "{leaves:?}"
    );
    // Phi assigns interleave freely.
    let mut leaves = site_run();
    leaves.insert(2, phi_assign("p", ident("z")));
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 1);
    // Bails: no return-of-temp …
    let mut leaves = vec![expr_stmt(ident("x"))];
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // … the resume decl must precede the return…
    let mut leaves = site_run();
    leaves.remove(2);
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // … on the same genobj…
    let mut leaves = site_run();
    leaves[2] = decl(
        "r",
        41,
        Expr::GeneratorDriver {
            resume: true,
            genobj: bx(tm("other", 99)),
        },
    );
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // … and return ITS temp.
    let mut leaves = site_run();
    leaves[3] = Leaf::Raw(Stmt::Return(Some(tm("other", 99))));
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // The suspend must be a yield of the await temp…
    let mut leaves = site_run();
    leaves[1] = expr_stmt(ident("x"));
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    let mut leaves = site_run();
    leaves[1] = expr_stmt(Expr::Yield {
        value: bx(ident("not_a_temp")),
    });
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // … and the await declare must be THAT temp's.
    let mut leaves = site_run();
    leaves.remove(0);
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    let mut leaves = site_run();
    leaves[0] = decl(
        "a",
        99,
        Expr::Await {
            value: bx(ident("v")),
            uncaught: true,
        },
    );
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // A caught (non-uncaught) await is not this shape.
    let mut leaves = site_run();
    leaves[0] = decl(
        "a",
        40,
        Expr::Await {
            value: bx(ident("v")),
            uncaught: false,
        },
    );
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
}

#[test]
fn agen_yield_site_and_three_way_bails() {
    let body = agen_body();
    let mut cx = agen_cx(&body);
    assert!(match_ag_yield(&body, 1, &mut cx).is_some());
    // The pre-yield resume value's only use may be the throw arm.
    let mut bad = body.clone();
    let SNode::Stmts(site) = &mut bad[1] else {
        unreachable!()
    };
    site.push(expr_stmt(tm("r1", 31)));
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
    // The continuation must open with the resumption pair run.
    let mut bad = body.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    otherwise[0] = SNode::Honest("h".to_string());
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
    let mut bad = body.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    otherwise[1] = run(vec![phi_assign("pp", ident("z"))]);
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
    // The yield-point resume decl must read the genobj…
    let mut bad = body.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    let SNode::Stmts(pair) = &mut otherwise[1] else {
        unreachable!()
    };
    pair[0] = decl(
        "ry",
        33,
        Expr::GeneratorDriver {
            resume: true,
            genobj: bx(tm("other", 99)),
        },
    );
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
    // … and a non-pair trailing leaf bails.
    let mut bad = body.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    let SNode::Stmts(pair) = &mut otherwise[1] else {
        unreachable!()
    };
    pair.push(expr_stmt(ident("extra")));
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());
    // The three-way dispatch ends the continuation.
    let mut bad = body.clone();
    let SNode::If { otherwise, .. } = &mut bad[2] else {
        unreachable!()
    };
    otherwise.push(run(vec![expr_stmt(ident("extra"))]));
    let mut cx = agen_cx(&bad);
    assert!(match_ag_yield(&bad, 1, &mut cx).is_none());

    // match_ag_three_way directly.
    let three_way = |ret: SNode, throw: SNode, next: SNode| {
        if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
            vec![ret],
            vec![if_node(
                cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                vec![throw],
                vec![next],
            )],
        )
    };
    let ret_arm = || {
        run(vec![decl(
            "a2",
            35,
            Expr::Await {
                value: bx(tm("ry", 33)),
                uncaught: true,
            },
        )])
    };
    let ret_done = || run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]);
    let throw_arm = || run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))]);
    let next = || run(vec![expr_stmt(ident("next_cont"))]);
    // The RETURN arm carries the folded await+return pair.
    let good = if_node(
        cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
        vec![ret_arm(), ret_done()],
        vec![if_node(
            cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
            vec![throw_arm()],
            vec![next()],
        )],
    );
    let mut cx = agen_cx(&body);
    assert!(match_ag_three_way(&good, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_some());
    // Must be an if; the tests must be mode tests; RETURN before
    // THROW, each once.
    assert!(
        match_ag_three_way(
            &SNode::Honest("h".to_string()),
            Some(ValueId::new(34)),
            ValueId::new(33),
            &mut cx,
        )
        .is_none()
    );
    let bad = three_way(if_node(ident("c"), vec![], vec![]), throw_arm(), next());
    assert!(match_ag_three_way(&bad, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_none());
    // A NEXT(2) test is not part of the dispatch chain.
    let bad = if_node(
        cmp(CmpOp::Eq, tm("my", 34), num(2.0)),
        vec![ret_arm()],
        vec![next()],
    );
    assert!(match_ag_three_way(&bad, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_none());
    // check_ag_return_arm shapes: phi partitions and dead breaks
    // ride along; a wrong await or return temp bails.
    let mut cx = agen_cx(&body);
    assert!(
        check_ag_return_arm(
            &[
                run(vec![phi_assign("p", ident("z"))]),
                ret_arm(),
                SNode::Break { label: None },
                ret_done(),
            ],
            ValueId::new(33),
        )
        .is_some()
    );
    assert!(check_ag_return_arm(&[ret_arm()], ValueId::new(33)).is_none());
    assert!(
        check_ag_return_arm(
            &[
                run(vec![decl(
                    "a2",
                    35,
                    Expr::Await {
                        value: bx(tm("other", 99)),
                        uncaught: true,
                    },
                )]),
                ret_done()
            ],
            ValueId::new(33),
        )
        .is_none()
    );
    assert!(
        check_ag_return_arm(
            &[
                ret_arm(),
                run(vec![Leaf::Raw(Stmt::Return(Some(tm("x", 99))))])
            ],
            ValueId::new(33),
        )
        .is_none()
    );
    assert!(check_ag_return_arm(&[SNode::Continue { label: None }], ValueId::new(33)).is_none());
    let _ = &mut cx;
    // ag_mode_test: wrappers, operand order, the inlined form.
    let (bits, pos) = ag_mode_test(
        &cmp(CmpOp::Eq, tm("my", 34), num(2.0)),
        Some(ValueId::new(34)),
        &mut agen_cx(&body),
    )
    .unwrap();
    assert_eq!(f64::from_bits(bits), 2.0);
    assert!(pos);
    let (.., pos) = ag_mode_test(
        &isfalse(cmp(CmpOp::Eq, num(1.0), tm("my", 34))),
        Some(ValueId::new(34)),
        &mut agen_cx(&body),
    )
    .unwrap();
    assert!(!pos);
    let (bits, ..) = ag_mode_test(
        &cmp(
            CmpOp::Eq,
            Expr::GeneratorDriver {
                resume: false,
                genobj: bx(tm("g", 20)),
            },
            num(1.0),
        ),
        None,
        &mut agen_cx(&body),
    )
    .expect("inlined GetResumeMode");
    assert_eq!(f64::from_bits(bits), 1.0);
    assert!(ag_mode_test(&ident("c"), Some(ValueId::new(34)), &mut agen_cx(&body)).is_none());
    assert!(
        ag_mode_test(
            &cmp(CmpOp::Eq, tm("other", 99), num(1.0)),
            Some(ValueId::new(34)),
            &mut agen_cx(&body),
        )
        .is_none()
    );
    // The yield-point guard: a source-level await whose
    // continuation opens with the resumption pair on the same
    // genobj is yield machinery, not an await site.
    let guard_body = vec![
        run(vec![
            decl(
                "a",
                30,
                Expr::Await {
                    value: bx(ident("v")),
                    uncaught: true,
                },
            ),
            expr_stmt(Expr::Yield {
                value: bx(tm("a", 30)),
            }),
        ]),
        if_node(
            cmp(
                CmpOp::Eq,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                },
                num(1.0),
            ),
            vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 20)),
            }))])],
            vec![run(vec![decl(
                "ry",
                33,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                },
            )])],
        ),
    ];
    let mut cx = agen_cx(&guard_body);
    assert!(match_await_site(&guard_body, 0, &mut cx).is_some());
    assert!(match_ag_await(&guard_body, 0, &mut cx).is_none());
}

// ── d-P15: the YieldStar driver fold ───────────────────────────
//
// The full vendor shapes, probe-verified against the matchers:
// header phis {rt, rv, it, g, flag} + the exitReturn decl, the
// NEXT/THROW mode dispatch, the RETURN arm (method lookup +
// undefined test + exit-phi wiring), the THROW arm (method lookup
// + close machinery with the elided ThrowNotExists), then the
// per-kind tail.

#[test]
fn machine_folds_recurse_into_regions() {
    // async_machine_fold: an await site nested in an if arm and in
    // a catch body.
    for wrap in [
        |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::DoWhile {
                label: None,
                body: site,
                cond: ident("d"),
            }]
        },
        |site: Vec<SNode>| {
            vec![SNode::Labeled {
                label: "l".to_string(),
                body: site,
            }]
        },
        |site: Vec<SNode>| vec![try_node(site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::Try {
                body: vec![run(vec![expr_stmt(ident("x"))])],
                catches: vec![catch("e", site)],
                note: None,
                finally: None,
            }]
        },
    ] {
        let mut nodes = wrap(async_body());
        let mut stats = FoldStats::default();
        async_machine_fold(&mut nodes, FunctionKind::Async, &mut stats);
        assert_eq!(stats.async_machine_sites, 1, "nested await site");
    }
    // async_driver_fold through nested regions.
    for wrap in [
        |site: Vec<SNode>| vec![if_node(ident("c"), site, vec![])],
        |site: Vec<SNode>| {
            vec![SNode::DoWhile {
                label: None,
                body: site,
                cond: ident("d"),
            }]
        },
        |site: Vec<SNode>| vec![try_node(site, vec![])],
    ] {
        let mut nodes = wrap(vec![run(vec![Leaf::Raw(Stmt::Return(Some(
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
        )))])]);
        let mut stats = FoldStats::default();
        async_driver_fold(&mut nodes, FunctionKind::AsyncArrow, &mut stats);
        assert_eq!(stats.async_driver, 1, "nested async driver site");
    }
    // yield_star_fold through an if arm.
    let mut nodes = vec![if_node(ident("c"), ys_sync_shape(), vec![])];
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1, "nested yield* site");
    // async_generator_machine_fold through a try body.
    let mut nodes = vec![try_node(agen_body(), vec![])];
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_yields, 1, "nested yield site");
}

#[test]
fn agen_plain_await_site() {
    // A source-level await inside an async generator (d-P13's site
    // — no resumption pair in its continuation).
    let mut nodes = vec![
        run(vec![
            decl(
                "g",
                20,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            expr_stmt(Expr::Yield { value: bx(undef()) }),
        ]),
        run(vec![
            decl(
                "a",
                30,
                Expr::Await {
                    value: bx(ident("x")),
                    uncaught: true,
                },
            ),
            expr_stmt(Expr::Yield {
                value: bx(tm("a", 30)),
            }),
        ]),
        if_node(
            cmp(
                CmpOp::Eq,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                },
                num(1.0),
            ),
            vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 20)),
            }))])],
            vec![run(vec![expr_stmt(ident("cont"))])],
        ),
    ];
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 1);
    assert_eq!(stats.agen_awaits, 1);
    assert_eq!(stats.agen_yields, 0);
    // The folded `await x` sits in the site run.
    let SNode::Stmts(site) = &nodes[1] else {
        unreachable!()
    };
    assert!(
        matches!(&site[0], Leaf::Raw(Stmt::Expr(Expr::Await { value, .. })) if value.as_ref() == &ident("x")),
        "{site:?}"
    );
}

#[test]
fn residual_match_arm_pins() {
    // match_for_in: the header's last leaf must be the NextPropName
    // declare…
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
    let mut bbody = body.clone();
    let SNode::Stmts(hdr) = &mut bbody[0] else {
        unreachable!()
    };
    hdr[2] = decl("k", 31, ident("not_nextpropname"));
    assert!(match_for_in(&pre, &wcond, &bbody).is_none());
    // … and the wiring scan stops at the first non-assign leaf.
    let mut pre2 = vec![decl("prelude", 5, ident("x"))];
    pre2.extend(pre.clone());
    assert!(match_for_in(&pre2, &wcond, &body).is_some());
    // A for-in whose internals are still read after elimination
    // vetoes the fold.
    let mut nodes = for_in_site();
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    let SNode::Stmts(use_run) = &mut body[1] else {
        unreachable!()
    };
    use_run.push(expr_stmt(tm("ip", 20)));
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_in, 0);
    // match_await_site: the await declare must be THE suspended
    // temp's…
    let mut bad = async_body();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site[2] = decl(
        "a",
        99,
        Expr::Await {
            value: bx(ident("p")),
            uncaught: true,
        },
    );
    let mut uses = BTreeMap::new();
    count_temp_uses(&bad, &mut uses);
    let mut cx = AsyncMachineCx {
        genobj: ValueId::new(10),
        aliases: [ValueId::new(10)].into_iter().collect(),
        exit_throws: BTreeSet::new(),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
        uses,
    };
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // … and the suspend value is a temp or an inlined await.
    let mut bad = async_body();
    let SNode::Stmts(site) = &mut bad[0] else {
        unreachable!()
    };
    site[3] = expr_stmt(Expr::Yield {
        value: bx(ident("neither")),
    });
    let mut uses = BTreeMap::new();
    count_temp_uses(&bad, &mut uses);
    let mut cx = AsyncMachineCx {
        genobj: ValueId::new(10),
        aliases: [ValueId::new(10)].into_iter().collect(),
        exit_throws: BTreeSet::new(),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
        uses,
    };
    assert!(match_await_site(&bad, 0, &mut cx).is_none());
    // match_async_dispatch: the istrue wrapper keeps polarity.
    let mut cx = AsyncMachineCx {
        genobj: ValueId::new(10),
        aliases: [ValueId::new(10)].into_iter().collect(),
        exit_throws: BTreeSet::new(),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
        uses: BTreeMap::new(),
    };
    let dispatch = if_node(
        istrue(cmp(CmpOp::Eq, tm("m", 14), num(1.0))),
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
        vec![run(vec![expr_stmt(ident("cont"))])],
    );
    assert!(
        match_async_dispatch(
            &dispatch,
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_some()
    );
    // The break-routed throw arm: the dispatch falls back to the
    // break check when the inline-throw check refuses.
    let mut cx = AsyncMachineCx {
        genobj: ValueId::new(10),
        aliases: [ValueId::new(10)].into_iter().collect(),
        exit_throws: [ValueId::new(13)].into_iter().collect(),
        const_env: BTreeMap::new(),
        consumed_consts: BTreeSet::new(),
        uses: BTreeMap::new(),
    };
    let dispatch = if_node(
        cmp(CmpOp::Eq, tm("m", 14), num(1.0)),
        vec![SNode::Break { label: None }],
        vec![run(vec![expr_stmt(ident("cont"))])],
    );
    assert!(
        match_async_dispatch(
            &dispatch,
            Some(ValueId::new(14)),
            Some(ValueId::new(13)),
            &mut cx,
        )
        .is_some()
    );
}

#[test]
fn agen_residual_pins() {
    // The phi-partition skip between the pair run and the dispatch.
    let mut nodes = agen_body();
    let SNode::If { otherwise, .. } = &mut nodes[2] else {
        unreachable!()
    };
    otherwise.insert(2, run(vec![phi_assign("pp3", ident("z"))]));
    let mut cx = agen_cx(&nodes);
    assert!(match_ag_yield(&nodes, 1, &mut cx).is_some());
    // agen_entry_elide: the if arm's otherwise side recurses too.
    for wrap in [
        |site: Vec<SNode>| vec![if_node(ident("c"), vec![], site)],
        |site: Vec<SNode>| {
            vec![SNode::DoWhile {
                label: None,
                body: site,
                cond: ident("d"),
            }]
        },
    ] {
        let mut nodes = wrap(vec![run(vec![
            decl(
                "g",
                20,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            expr_stmt(Expr::Yield { value: bx(undef()) }),
        ])]);
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_entry, 1);
    }
}

#[test]
fn machine_fold_seq_region_wraps() {
    // The *_seq recursion arms for While/DoWhile/Labeled (the
    // If/Try wraps live in machine_folds_recurse_into_regions).
    for wrap in [
        |site: Vec<SNode>| {
            vec![SNode::While {
                label: None,
                cond: Some(ident("c")),
                body: site,
            }]
        },
        |site: Vec<SNode>| {
            vec![SNode::DoWhile {
                label: None,
                body: site,
                cond: ident("d"),
            }]
        },
        |site: Vec<SNode>| {
            vec![SNode::Labeled {
                label: "l".to_string(),
                body: site,
            }]
        },
    ] {
        let mut nodes = wrap(ys_sync_shape());
        let mut stats = FoldStats::default();
        yield_star_fold(&mut nodes, FunctionKind::Generator, &mut stats);
        assert_eq!(stats.yield_star_sites, 1, "wrapped yield* site");
        let mut nodes = wrap(agen_body());
        let mut stats = FoldStats::default();
        async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
        assert_eq!(stats.agen_yields, 1, "wrapped agen yield site");
    }
    // A stray Honest sibling exercises the scan's no-op arm.
    let mut nodes = vec![
        SNode::Honest("stray".to_string()),
        try_node(
            vec![run(vec![
                decl(
                    "g",
                    20,
                    Expr::CreateGenerator {
                        func: bx(closure("f")),
                    },
                ),
                expr_stmt(Expr::Yield { value: bx(undef()) }),
            ])],
            vec![],
        ),
    ];
    let mut stats = FoldStats::default();
    async_generator_machine_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.agen_entry, 1);
}

#[test]
fn final_residual_pins() {
    // ys_match_loop: the NEXT arm must hold at least one
    // significant node.
    let mut nodes = ys_sync_shape();
    {
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut body[1] else {
            unreachable!()
        };
        otherwise.clear();
    }
    assert!(ys_match_loop(&nodes[2], false).is_none());
    // … and its first significant node must be the assign run.
    let mut nodes = ys_sync_shape();
    {
        let SNode::While { body, .. } = ys_while(&mut nodes) else {
            unreachable!()
        };
        let SNode::If { otherwise, .. } = &mut body[1] else {
            unreachable!()
        };
        otherwise[0] = run(vec![exc_assign("vx", ident("z"))]);
    }
    assert!(ys_match_loop(&nodes[2], false).is_none());
    // The sync/async call's `this` must be a TEMP (not just
    // present).
    for async_ in [false, true] {
        let mut nodes = if async_ {
            ys_async_shape()
        } else {
            ys_sync_shape()
        };
        {
            let SNode::While { body, .. } = ys_while(&mut nodes) else {
                unreachable!()
            };
            let SNode::Stmts(pre) = &mut body[2] else {
                unreachable!()
            };
            pre[2] = decl(
                "vres",
                112,
                Expr::Call {
                    callee: bx(tm("vm", 111)),
                    this: Some(bx(ident("not_a_temp"))),
                    args: vec![tm("vrv", 101)],
                    kind: CallKind::Dynamic,
                },
            );
        }
        assert!(ys_match_loop(&nodes[2], async_).is_none());
    }
    // ys_apply_bare (async): a setup prefix is re-homed above the
    // yield* statement.
    let mut nodes = ys_async_shape();
    {
        let SNode::Stmts(setup) = &mut nodes[0] else {
            unreachable!()
        };
        setup.insert(0, expr_stmt(call0(ident("warmup"))));
    }
    let mut stats = FoldStats::default();
    yield_star_fold(&mut nodes, FunctionKind::AsyncGenerator, &mut stats);
    assert_eq!(stats.yield_star_sites, 1);
    assert_eq!(nodes[0], run(vec![expr_stmt(call0(ident("warmup")))]));
    // ag_mode_test: the istrue wrapper keeps polarity.
    let body = agen_body();
    let (.., pos) = ag_mode_test(
        &istrue(cmp(CmpOp::Eq, tm("my", 34), num(2.0))),
        Some(ValueId::new(34)),
        &mut agen_cx(&body),
    )
    .unwrap();
    assert!(pos);
    // match_ag_three_way: a foreign run before the next test bails
    // the descent.
    let bad = if_node(
        cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
        vec![
            run(vec![decl(
                "a2",
                35,
                Expr::Await {
                    value: bx(tm("ry", 33)),
                    uncaught: true,
                },
            )]),
            run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]),
        ],
        vec![
            run(vec![expr_stmt(ident("junk"))]),
            if_node(
                cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                vec![run(vec![expr_stmt(ident("next_cont"))])],
            ),
        ],
    );
    assert!(
        match_ag_three_way(
            &bad,
            Some(ValueId::new(34)),
            ValueId::new(33),
            &mut agen_cx(&body)
        )
        .is_none()
    );
    // … and a pure-const run before it is skipped.
    let good = if_node(
        cmp(CmpOp::Eq, tm("my", 34), num(0.0)),
        vec![
            run(vec![decl(
                "a2",
                35,
                Expr::Await {
                    value: bx(tm("ry", 33)),
                    uncaught: true,
                },
            )]),
            run(vec![Leaf::Raw(Stmt::Return(Some(tm("a2", 35))))]),
        ],
        vec![
            run(vec![decl("c1", 90, num(1.0))]),
            if_node(
                cmp(CmpOp::Eq, tm("my", 34), tm("c1", 90)),
                vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                vec![run(vec![expr_stmt(ident("next_cont"))])],
            ),
        ],
    );
    let mut cx = agen_cx(&body);
    cx.const_env.insert(ValueId::new(90), 1.0f64.to_bits());
    assert!(match_ag_three_way(&good, Some(ValueId::new(34)), ValueId::new(33), &mut cx).is_some());
    // sweep_async_machinery: a non-alias temp value passes the walk;
    // a foreign assign survives the strip and keeps the decl census.
    let mut nodes = vec![run(vec![
        phi_decl("pa", 20),
        phi_assign("pa", tm("g", 10)),
        phi_assign("other", tm("q", 77)),
    ])];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(
        got.iter()
            .any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "other")),
        "the foreign assign survives: {got:?}"
    );
    assert!(
        !got.iter()
            .any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "pa"))
    );
    // match_ag_await: phi-partition runs at the continuation head
    // are skipped by the yield-point guard.
    let guard_body = vec![
        run(vec![
            decl(
                "a",
                30,
                Expr::Await {
                    value: bx(ident("v")),
                    uncaught: true,
                },
            ),
            expr_stmt(Expr::Yield {
                value: bx(tm("a", 30)),
            }),
        ]),
        if_node(
            cmp(
                CmpOp::Eq,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                },
                num(1.0),
            ),
            vec![run(vec![Leaf::Raw(Stmt::Throw(Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 20)),
            }))])],
            vec![
                run(vec![phi_assign("pp", ident("z"))]),
                run(vec![expr_stmt(ident("cont"))]),
            ],
        ),
    ];
    let mut cx = agen_cx(&guard_body);
    assert!(match_ag_await(&guard_body, 0, &mut cx).is_some());
    // agen_fold_run: nothing before the resume decl.
    let mut leaves = vec![
        decl(
            "r",
            41,
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 20)),
            },
        ),
        Leaf::Raw(Stmt::Return(Some(tm("r", 41)))),
    ];
    let mut stats = FoldStats::default();
    agen_fold_run(&mut leaves, ValueId::new(20), &mut stats);
    assert_eq!(stats.agen_returns, 0);
    // absorb_one: a non-own index store on the object is no entry.
    assert!(
        absorb_one(
            &Leaf::Raw(Stmt::StoreIndex {
                object: tm("o", 10),
                index: num(0.0),
                value: ident("v"),
                own: false,
            }),
            ValueId::new(10),
            false,
            &[],
            0,
        )
        .is_none()
    );
    // key_load_target: a PropIndex with a non-literal index is no
    // key load.
    assert_eq!(
        key_load_target(
            &Expr::PropIndex {
                object: bx(ident("o")),
                index: bx(ident("k")),
            },
            &ident("o"),
        ),
        None
    );
}
