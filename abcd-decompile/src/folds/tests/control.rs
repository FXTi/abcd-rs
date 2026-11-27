//! `switch` cascade, `finally` canonicalization/idiom, and rethrow-try dissolution unit tests.

use super::*;

// ── the finally fold's canonicalization helpers ────────────────

fn canon_map() -> std::collections::HashMap<String, String> {
    [("a".to_string(), "#d0".to_string())].into_iter().collect()
}

#[test]
fn canon_stmt_covers_every_statement_kind() {
    let map = canon_map();
    // Declare: name renamed, value canon'd, provenance erased.
    let mut s = Stmt::Declare {
        name: "a".to_string(),
        mutable: false,
        value: tm("a", 5),
        value_id: ValueId::new(5),
    };
    canon_stmt(&mut s, &map);
    assert_eq!(
        s,
        Stmt::Declare {
            name: "#d0".to_string(),
            mutable: false,
            value: tm("#d0", 0),
            value_id: ValueId::new(0),
        }
    );
    let mut s = Stmt::PhiDecl {
        name: "a".to_string(),
        value_id: ValueId::new(5),
    };
    canon_stmt(&mut s, &map);
    assert_eq!(
        s,
        Stmt::PhiDecl {
            name: "#d0".to_string(),
            value_id: ValueId::new(0),
        }
    );
    let mut s = Stmt::PhiAssign {
        target: "a".to_string(),
        value: tm("a", 5),
        to: BlockId::new(9),
        exceptional: true,
    };
    canon_stmt(&mut s, &map);
    assert_eq!(
        s,
        Stmt::PhiAssign {
            target: "#d0".to_string(),
            value: tm("#d0", 0),
            to: BlockId::new(0),
            exceptional: true,
        }
    );
    // Expression-carrying arms.
    let value_arms: Vec<fn(Expr) -> Stmt> = vec![
        Stmt::Expr,
        Stmt::Throw,
        |e| Stmt::Return(Some(e)),
        |e| Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: "l".to_string(),
            value: e,
        },
        |e| Stmt::GlobalStore {
            name: "g".to_string(),
            value: e,
            tolerant: false,
        },
        |e| Stmt::ModuleStore {
            index: 0,
            name: "m".to_string(),
            value: e,
        },
    ];
    for mk in value_arms {
        let mut s = mk(tm("a", 5));
        canon_stmt(&mut s, &map);
        let exprs = stmt_exprs_of(&s);
        assert_eq!(exprs, vec![&tm("#d0", 0)]);
    }
    // Store arms rewrite every expression field.
    let mut s = Stmt::StoreProp {
        object: tm("a", 5),
        name: "k".to_string(),
        dot_legal: true,
        value: tm("a", 6),
        own: false,
    };
    canon_stmt(&mut s, &map);
    assert_eq!(
        s,
        Stmt::StoreProp {
            object: tm("#d0", 0),
            name: "k".to_string(),
            dot_legal: true,
            value: tm("#d0", 0),
            own: false,
        }
    );
    let mut s = Stmt::StoreIndex {
        object: tm("a", 5),
        index: tm("a", 6),
        value: ident("v"),
        own: false,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::StoreIndex { object, index, .. }
            if object == tm("#d0", 0) && index == tm("#d0", 0)
    ));
    let mut s = Stmt::StoreDyn {
        object: tm("a", 5),
        key: tm("a", 6),
        value: ident("v"),
        own: false,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::StoreDyn { object, key, .. }
            if object == tm("#d0", 0) && key == tm("#d0", 0)
    ));
    let mut s = Stmt::DefineMethod {
        object: tm("a", 5),
        name: "m".to_string(),
        func: tm("a", 6),
        length: 0,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::DefineMethod { object, func, .. }
            if object == tm("#d0", 0) && func == tm("#d0", 0)
    ));
    let mut s = Stmt::StorePrivate {
        object: tm("a", 5),
        name: "p".to_string(),
        value: tm("a", 6),
        define: true,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::StorePrivate { object, value, .. }
            if object == tm("#d0", 0) && value == tm("#d0", 0)
    ));
    let mut s = Stmt::StoreSuper {
        name: None,
        key: Some(tm("a", 5)),
        value: tm("a", 6),
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::StoreSuper {
            key: Some(k),
            value,
            ..
        } if k == tm("#d0", 0) && value == tm("#d0", 0)
    ));
    let mut s = Stmt::StoreSuper {
        name: Some("k".to_string()),
        key: None,
        value: tm("a", 6),
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(
        s,
        Stmt::StoreSuper { key: None, value, .. } if value == tm("#d0", 0)
    ));
    // CatchBind renames the binding.
    let mut s = Stmt::CatchBind {
        name: "a".to_string(),
    };
    canon_stmt(&mut s, &map);
    assert_eq!(
        s,
        Stmt::CatchBind {
            name: "#d0".to_string()
        }
    );
    // Elided/Fallback lose their source locations.
    let loc = Some(abcd_ir::function::Loc {
        line: 1,
        column: Some(2),
    });
    let mut s = Stmt::Elided {
        op: "op",
        reason: "r",
        loc,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(s, Stmt::Elided { loc: None, .. }));
    let mut s = Stmt::Fallback {
        op: "op",
        note: "n",
        loc,
    };
    canon_stmt(&mut s, &map);
    assert!(matches!(s, Stmt::Fallback { loc: None, .. }));
    // The catch-all arm leaves the statement alone.
    for s in [
        Stmt::Return(None),
        Stmt::ScopePop,
        Stmt::Unreachable,
        Stmt::Branch {
            dest: BlockId::new(0),
        },
        Stmt::CondBranch {
            cond: tm("a", 5),
            true_dest: BlockId::new(1),
            false_dest: BlockId::new(2),
        },
    ] {
        let mut m = s.clone();
        canon_stmt(&mut m, &map);
        assert_eq!(m, s);
    }
}

#[test]
fn canon_tok_and_def_names_cover_every_leaf_kind() {
    let map = canon_map();
    // A nested node token is opaque to canonicalization.
    let mut t = FTok::Node(SNode::Break { label: None });
    canon_tok(&mut t, &map);
    assert_eq!(t, FTok::Node(SNode::Break { label: None }));
    // Destructure: object canon'd, key targets + rest renamed.
    let mut t = FTok::Leaf(Leaf::Destructure {
        obj: tm("a", 5),
        keys: vec![("k".to_string(), "a".to_string())],
        rest: "a".to_string(),
    });
    canon_tok(&mut t, &map);
    assert_eq!(
        t,
        FTok::Leaf(Leaf::Destructure {
            obj: tm("#d0", 0),
            keys: vec![("k".to_string(), "#d0".to_string())],
            rest: "#d0".to_string(),
        })
    );
    // Synthetic decl / assign.
    let mut t = FTok::Leaf(Leaf::Decl {
        name: "a".to_string(),
        mutable: true,
        value: Some(tm("a", 5)),
    });
    canon_tok(&mut t, &map);
    assert_eq!(
        t,
        FTok::Leaf(Leaf::Decl {
            name: "#d0".to_string(),
            mutable: true,
            value: Some(tm("#d0", 0)),
        })
    );
    let mut t = FTok::Leaf(Leaf::Decl {
        name: "a".to_string(),
        mutable: true,
        value: None,
    });
    canon_tok(&mut t, &map);
    assert!(matches!(
        t,
        FTok::Leaf(Leaf::Decl { name, value: None, .. }) if name == "#d0"
    ));
    let mut t = FTok::Leaf(Leaf::Assign {
        target: "a".to_string(),
        value: tm("a", 5),
    });
    canon_tok(&mut t, &map);
    assert_eq!(
        t,
        FTok::Leaf(Leaf::Assign {
            target: "#d0".to_string(),
            value: tm("#d0", 0),
        })
    );
    // Definition-site census: first-occurrence order, nodes skipped.
    let toks = vec![
        FTok::Leaf(decl("a", 1, ident("v"))),
        FTok::Node(SNode::Honest("h".to_string())),
        FTok::Leaf(phi_decl("b", 2)),
        FTok::Leaf(Leaf::Raw(Stmt::CatchBind {
            name: "c".to_string(),
        })),
        FTok::Leaf(Leaf::Decl {
            name: "d".to_string(),
            mutable: true,
            value: None,
        }),
        FTok::Leaf(Leaf::Destructure {
            obj: ident("o"),
            keys: vec![("k".to_string(), "t1".to_string())],
            rest: "r".to_string(),
        }),
        FTok::Leaf(decl("a", 9, ident("w"))),
        FTok::Leaf(expr_stmt(ident("x"))),
    ];
    assert_eq!(ftok_def_names(&toks), vec!["a", "b", "c", "d", "t1", "r"]);
    // ft_canon placeholders follow that order.
    let out = ft_canon(&[
        FTok::Leaf(decl("a", 1, tm("a", 1))),
        FTok::Leaf(decl("b", 2, tm("a", 1))),
    ]);
    assert_eq!(
        out,
        vec![
            FTok::Leaf(decl("#d0", 0, tm("#d0", 0))),
            FTok::Leaf(decl("#d1", 0, tm("#d0", 0))),
        ]
    );
}

#[test]
fn ft_regroup_interleaves_nodes_and_runs() {
    let out = ft_regroup(vec![
        FTok::Node(SNode::Honest("h".to_string())),
        FTok::Leaf(expr_stmt(ident("a"))),
        FTok::Leaf(expr_stmt(ident("b"))),
        FTok::Node(SNode::Break { label: None }),
        FTok::Leaf(expr_stmt(ident("c"))),
    ]);
    assert_eq!(
        out,
        vec![
            SNode::Honest("h".to_string()),
            run(vec![expr_stmt(ident("a")), expr_stmt(ident("b"))]),
            SNode::Break { label: None },
            run(vec![expr_stmt(ident("c"))]),
        ]
    );
    assert!(ft_regroup(vec![]).is_empty());
    // ft_flatten is the inverse view.
    let flat = ft_flatten(&out);
    assert_eq!(flat.len(), 5);
    assert!(matches!(flat[0], FTok::Node(SNode::Honest(_))));
}

#[test]
fn ft_fallthrough_covers_every_node_kind() {
    let plain = || run(vec![expr_stmt(ident("a"))]);
    // Statement runs: control-transfer leaves end fall-through.
    assert!(ft_node_fallthrough(&plain()));
    for l in [
        Stmt::Return(None),
        Stmt::Throw(ident("e")),
        Stmt::Branch {
            dest: BlockId::new(0),
        },
        Stmt::CondBranch {
            cond: ident("c"),
            true_dest: BlockId::new(1),
            false_dest: BlockId::new(2),
        },
    ] {
        let msg = format!("{l:?}");
        assert!(!ft_node_fallthrough(&run(vec![Leaf::Raw(l)])), "{msg}");
    }
    // If: both arms must fall through.
    assert!(ft_node_fallthrough(&if_node(
        ident("c"),
        vec![plain()],
        vec![plain()]
    )));
    assert!(!ft_node_fallthrough(&if_node(
        ident("c"),
        vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        vec![plain()],
    )));
    // Try: body falls through, or a catch does (catches required).
    assert!(ft_node_fallthrough(&SNode::Try {
        body: vec![plain()],
        catches: vec![],
        note: None,
        finally: None,
    }));
    assert!(ft_node_fallthrough(&SNode::Try {
        body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        catches: vec![catch("e", vec![plain()])],
        note: None,
        finally: Some(vec![plain()]),
    }));
    assert!(!ft_node_fallthrough(&SNode::Try {
        body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        catches: vec![],
        note: None,
        finally: None,
    }));
    // Exits do not fall through; everything else may complete.
    assert!(!ft_node_fallthrough(&SNode::Break { label: None }));
    assert!(!ft_node_fallthrough(&SNode::Continue { label: None }));
    for n in [
        SNode::While {
            label: None,
            cond: None,
            body: vec![],
        },
        SNode::DoWhile {
            label: None,
            body: vec![],
            cond: ident("c"),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: vec![],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: vec![],
        },
        SNode::Switch {
            disc: ident("d"),
            cases: vec![],
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: vec![],
        },
        SNode::Honest("h".to_string()),
    ] {
        assert!(ft_node_fallthrough(&n), "{n:?}");
    }
    assert!(ft_list_fallthrough(&[
        plain(),
        SNode::Honest("h".to_string())
    ]));
    assert!(!ft_list_fallthrough(&[
        plain(),
        SNode::Break { label: None }
    ]));
}

// ── fold 5: the switch re-detection ────────────────────────────

fn chain_3_no_else() -> SNode {
    if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![expr_stmt(call0(ident("a")))])],
        vec![if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
            vec![run(vec![expr_stmt(call0(ident("b")))])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
                vec![run(vec![expr_stmt(call0(ident("c")))])],
                vec![],
            )],
        )],
    )
}

#[test]
fn switch_chain_extension_loop_and_default_arm() {
    // The no-else chain: the ONLY route through the extension loop.
    let mut nodes = vec![chain_3_no_else()];
    let mut stats = FoldStats::default();
    fold_switches(&mut nodes, &mut stats);
    assert_eq!(stats.switch, 1);
    let SNode::Switch { disc, cases } = &nodes[0] else {
        panic!("expected Switch: {nodes:?}")
    };
    assert_eq!(disc, &tm("x", 1));
    assert_eq!(cases.len(), 3);
    assert_eq!(cases[0].tests, vec![num(1.0)]);
    // Each folded case body gains a trailing break.
    assert_eq!(cases[0].body.last(), Some(&SNode::Break { label: None }));
    // A terminal case body keeps its own ending.
    let single = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(9.0)),
        vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        vec![],
    );
    let (disc, cases) = match_switch_chain(&single).expect("one case");
    assert_eq!(disc, tm("x", 1));
    assert_eq!(cases.len(), 1);
    assert!(!matches!(cases[0].body.last(), Some(SNode::Break { .. })));
    // … but a lone case never becomes a switch.
    let mut nodes = vec![single];
    let mut stats = FoldStats::default();
    fold_switches(&mut nodes, &mut stats);
    assert_eq!(stats.switch, 0);
    // A trailing else becomes the default case.
    let mut chain = chain_3_no_else();
    let SNode::If { otherwise, .. } = &mut chain else {
        unreachable!()
    };
    let SNode::If {
        otherwise: inner, ..
    } = &mut otherwise[0]
    else {
        unreachable!()
    };
    inner[0] = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
        vec![run(vec![expr_stmt(call0(ident("c")))])],
        vec![run(vec![expr_stmt(call0(ident("d")))])],
    );
    let mut nodes = vec![chain];
    let mut stats = FoldStats::default();
    fold_switches(&mut nodes, &mut stats);
    assert_eq!(stats.switch, 1);
    let SNode::Switch { cases, .. } = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(cases.len(), 4);
    assert!(cases[3].tests.is_empty(), "default arm: {cases:?}");
    // A nested switch on the same discriminant flattens (the inner
    // chain folds first when driving the full `fold` recursion).
    let nested = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![expr_stmt(call0(ident("a")))])],
        vec![if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
            vec![run(vec![expr_stmt(call0(ident("b")))])],
            vec![if_node(
                cmp(CmpOp::StrictEq, tm("x", 1), num(3.0)),
                vec![run(vec![expr_stmt(call0(ident("c")))])],
                vec![],
            )],
        )],
    );
    let mut nodes = vec![nested];
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.switch, 2);
    let SNode::Switch { cases, .. } = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(cases.len(), 3, "flattened: {cases:?}");
    // A nested switch on a FOREIGN discriminant becomes the default
    // case (the flatten guard refuses it, the default arm takes it).
    let mixed = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![expr_stmt(call0(ident("a")))])],
        vec![SNode::Switch {
            disc: tm("y", 2),
            cases: vec![SwitchCase {
                tests: vec![num(1.0)],
                body: vec![],
            }],
        }],
    );
    let mut nodes = vec![mixed];
    let mut stats = FoldStats::default();
    fold_switches(&mut nodes, &mut stats);
    assert_eq!(stats.switch, 1);
    let SNode::Switch { cases, .. } = &nodes[0] else {
        unreachable!()
    };
    assert_eq!(cases.len(), 2);
    assert!(
        cases[1].tests.is_empty(),
        "the foreign switch is the default"
    );
    assert!(matches!(cases[1].body[0], SNode::Switch { .. }));
}

#[test]
fn switch_chain_bail_pins() {
    // The case body must not hold an unlabeled (loop) break.
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![SNode::Break { label: None }],
        vec![],
    );
    assert!(match_switch_chain(&bad).is_none());
    // … even nested inside an if/labeled/try in the arm…
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![SNode::Labeled {
            label: "l".to_string(),
            body: vec![SNode::Break { label: None }],
        }],
        vec![],
    );
    assert!(match_switch_chain(&bad).is_none());
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![try_node(
            vec![],
            vec![catch("e", vec![SNode::Break { label: None }])],
        )],
        vec![],
    );
    assert!(match_switch_chain(&bad).is_none());
    // … while a nested loop intercepts its own breaks.
    let ok = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![SNode::While {
            label: None,
            cond: None,
            body: vec![SNode::Break { label: None }],
        }],
        vec![],
    );
    assert!(match_switch_chain(&ok).is_some());
    // A nested chain on a DIFFERENT discriminant kills the fold
    // (the extension loop refuses the mismatched if).
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![])],
        vec![if_node(
            cmp(CmpOp::StrictEq, tm("y", 2), num(2.0)),
            vec![run(vec![])],
            vec![],
        )],
    );
    assert!(match_switch_chain(&bad).is_none());
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![])],
        vec![if_node(
            cmp(CmpOp::StrictEq, tm("x", 1), num(2.0)),
            vec![SNode::Break { label: None }],
            vec![],
        )],
    );
    assert!(match_switch_chain(&bad).is_none());
    // Non-if / non-chain nodes are not chains.
    assert!(match_switch_chain(&SNode::Honest("h".to_string())).is_none());
    assert!(match_switch_chain(&if_node(ident("c"), vec![], vec![])).is_none());
    // switch_test: polarity and operand-order variants (strict `===` only;
    // loose `==` is rejected so coercing cascades never mis-fold into `switch`).
    let (d, l, pos) = switch_test(&cmp(CmpOp::StrictEq, tm("x", 1), num(1.0))).unwrap();
    assert!(pos && d == tm("x", 1) && l == num(1.0));
    let (d, l, pos) = switch_test(&cmp(CmpOp::StrictEq, num(1.0), tm("x", 1))).unwrap();
    assert!(pos && d == tm("x", 1) && l == num(1.0));
    let (.., pos) = switch_test(&isfalse(cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)))).unwrap();
    assert!(!pos);
    let (.., pos) = switch_test(&isfalse(isfalse(cmp(
        CmpOp::StrictEq,
        tm("x", 1),
        num(1.0),
    ))))
    .unwrap();
    assert!(pos);
    assert!(switch_test(&cmp(CmpOp::Eq, tm("x", 1), num(1.0))).is_none());
    assert!(switch_test(&cmp(CmpOp::NotEq, tm("x", 1), num(1.0))).is_none());
    assert!(switch_test(&cmp(CmpOp::StrictEq, num(1.0), num(2.0))).is_none());
    assert!(switch_test(&cmp(CmpOp::StrictEq, tm("x", 1), tm("y", 2))).is_none());
    assert!(switch_test(&ident("c")).is_none());
    // A negative-polarity head swaps the case/continuation arms.
    let swapped = if_node(
        isfalse(cmp(CmpOp::StrictEq, tm("x", 1), num(1.0))),
        vec![run(vec![expr_stmt(call0(ident("cont")))])],
        vec![run(vec![expr_stmt(call0(ident("case")))])],
    );
    let (.., cases) = match_switch_chain(&swapped).expect("polarity-swapped chain");
    assert_eq!(cases.len(), 2, "case + default: {cases:?}");
    // arm_has_loop_break: the remaining direct arms.
    assert!(arm_has_loop_break(&[SNode::Break { label: None }]));
    assert!(!arm_has_loop_break(&[SNode::Break {
        label: Some("l".to_string()),
    }]));
    assert!(arm_has_loop_break(&[if_node(
        ident("c"),
        vec![],
        vec![SNode::Break { label: None }],
    )]));
    assert!(!arm_has_loop_break(&[SNode::Switch {
        disc: ident("d"),
        cases: vec![SwitchCase {
            tests: vec![],
            body: vec![SNode::Break { label: None }],
        }],
    }]));
    assert!(!arm_has_loop_break(&[SNode::Continue { label: None }]));
    assert!(!arm_has_loop_break(&[SNode::Honest("h".to_string())]));
    assert!(!arm_has_loop_break(&[run(vec![])]));
}

// ── d-P8: the finally-idiom family ─────────────────────────────

/// The finally-body template shared by the dispatch's run arm and
/// every inlined copy. Rich enough to walk every canon arm.
fn finally_template() -> Vec<Leaf> {
    vec![
        decl("f1", 70, call0(ident("notify"))),
        phi_decl("f2", 71),
        phi_assign("f3", ident("w")),
        Leaf::Raw(Stmt::StoreProp {
            object: ident("o"),
            name: "p".to_string(),
            dot_legal: true,
            value: tm("f1", 70),
            own: false,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: ident("o"),
            index: num(1.0),
            value: ident("v"),
            own: false,
        }),
        Leaf::Raw(Stmt::StoreDyn {
            object: ident("o"),
            key: ident("k"),
            value: ident("v"),
            own: false,
        }),
        Leaf::Raw(Stmt::DefineMethod {
            object: ident("o"),
            name: "m".to_string(),
            func: ident("f"),
            length: 0,
        }),
        Leaf::Raw(Stmt::StorePrivate {
            object: ident("o"),
            name: "q".to_string(),
            value: ident("v"),
            define: true,
        }),
        Leaf::Raw(Stmt::StoreSuper {
            name: None,
            key: Some(ident("k")),
            value: ident("v"),
        }),
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: "lx".to_string(),
            value: ident("v"),
        }),
        Leaf::Raw(Stmt::GlobalStore {
            name: "g".to_string(),
            value: ident("v"),
            tolerant: false,
        }),
        Leaf::Raw(Stmt::ModuleStore {
            index: 0,
            name: "m0".to_string(),
            value: ident("v"),
        }),
        Leaf::Raw(Stmt::CatchBind {
            name: "cb".to_string(),
        }),
        elided("ThrowIfTypeError"),
        Leaf::Destructure {
            obj: ident("o"),
            keys: vec![("k".to_string(), "dt".to_string())],
            rest: "dr".to_string(),
        },
        Leaf::Decl {
            name: "ld".to_string(),
            mutable: true,
            value: Some(ident("v")),
        },
        Leaf::Assign {
            target: "la".to_string(),
            value: ident("v"),
        },
    ]
}

/// The dispatch-shaped catch body: bookkeeping, the phi-dispatch
/// switch (`case undefined:` runs the finally body; default is pure
/// bookkeeping), then the rethrow-unless-hole conditional.
fn dispatch_body() -> Vec<SNode> {
    vec![
        run(vec![phi_decl("pd", 60), phi_assign("x", tm("e", 61))]),
        SNode::Switch {
            disc: tm("d", 62),
            cases: vec![
                SwitchCase {
                    tests: vec![undef()],
                    body: vec![
                        run(finally_template()),
                        run(vec![phi_assign("pz", ident("w"))]),
                        SNode::Break { label: None },
                    ],
                },
                SwitchCase {
                    tests: vec![],
                    body: vec![
                        run(vec![phi_assign("pz2", ident("z"))]),
                        SNode::Break { label: None },
                    ],
                },
            ],
        },
        if_node(
            cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
            vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        ),
    ]
}

/// The protected construct: every region kind nesting an inlined
/// finally copy before its exits. All regions fall through after
/// stripping, so the fold also consumes the normal-completion copy
/// in the tail.
fn protected_body() -> Vec<SNode> {
    let copy = || run(finally_template());
    let ret = || run(vec![Leaf::Raw(Stmt::Return(Some(ident("retv"))))]);
    vec![
        SNode::While {
            label: Some("wl".to_string()),
            cond: Some(ident("wc")),
            body: vec![copy(), ret()],
        },
        SNode::Labeled {
            label: "lbl".to_string(),
            body: vec![
                copy(),
                SNode::Break {
                    label: Some("outer".to_string()),
                },
            ],
        },
        SNode::DoWhile {
            label: None,
            body: vec![
                run(vec![expr_stmt(ident("x"))]),
                SNode::Break { label: None },
            ],
            cond: ident("dc"),
        },
        SNode::Switch {
            disc: ident("sd"),
            cases: vec![SwitchCase {
                tests: vec![num(1.0)],
                body: vec![copy(), ret()],
            }],
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("it"),
            body: vec![copy(), ret()],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("ob"),
            body: vec![copy(), ret()],
        },
        SNode::Try {
            body: vec![copy(), ret()],
            catches: vec![
                catch("e2", vec![copy(), ret()]),
                catch("e3", vec![run(vec![expr_stmt(ident("ok"))])]),
            ],
            note: None,
            finally: Some(vec![
                copy(),
                SNode::Break {
                    label: Some("outer".to_string()),
                },
            ]),
        },
    ]
}

/// The full idiom site: the handler-protecting outer try, the
/// normal-completion copy, and a post-copy tail mixing a leaf run
/// and a control-flow node.
fn finally_site() -> Vec<SNode> {
    vec![
        SNode::Try {
            body: protected_body(),
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        },
        run(finally_template()),
        run(vec![expr_stmt(ident("mid"))]),
        if_node(
            ident("tailc"),
            vec![run(vec![expr_stmt(ident("tc"))])],
            vec![],
        ),
        run(vec![expr_stmt(ident("tailend"))]),
    ]
}

/// The dispatch's finally body as tokens (for expectations).
fn finally_template_tokens() -> Vec<FTok> {
    finally_template().into_iter().map(FTok::Leaf).collect()
}

#[test]
fn finally_fold_non_unwrap_construct_with_tail_consumption() {
    let mut nodes = finally_site();
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.finally_fold, 1);
    // [hoisted phi decls, honesty note, try{…}finally{F}, tail…]
    assert_eq!(nodes[0], run(vec![phi_decl("pd", 60)]));
    assert!(matches!(&nodes[1], SNode::Honest(_)));
    let SNode::Try {
        body,
        catches,
        finally: Some(fin),
        ..
    } = &nodes[2]
    else {
        panic!("expected the folded try/finally: {nodes:?}")
    };
    assert!(catches.is_empty());
    assert_eq!(fin, &ft_regroup(finally_template_tokens()));
    // The inlined copies are gone from every region.
    let SNode::While { body: wbody, .. } = &body[0] else {
        unreachable!()
    };
    assert_eq!(
        wbody.as_slice(),
        [run(vec![Leaf::Raw(Stmt::Return(Some(ident("retv"))))])]
    );
    // The tail survived past the consumed normal-completion copy.
    assert_eq!(nodes[3], run(vec![expr_stmt(ident("mid"))]));
    assert!(matches!(&nodes[4], SNode::If { .. }));
    assert_eq!(nodes[5], run(vec![expr_stmt(ident("tailend"))]));
    assert_eq!(nodes.len(), 6);
}

#[test]
fn ft_extract_dispatch_bail_pins() {
    let ok = dispatch_body();
    let idiom = ft_extract_dispatch(&ok, "e").expect("the corpus dispatch");
    assert_eq!(idiom.decls, vec![phi_decl("pd", 60)]);
    assert_eq!(idiom.canon, ft_canon(&idiom.body));
    // Only one dispatch switch may be present.
    let mut bad = ok.clone();
    bad.insert(2, ok[1].clone());
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // Only one rethrow conditional may be present.
    let mut bad = ok.clone();
    bad.push(ok[2].clone());
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // Real handler code (a non-bookkeeping leaf) bails.
    let mut bad = ok.clone();
    bad.insert(0, run(vec![expr_stmt(call0(ident("side_effect")))]));
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // A declare with an effectful initializer is not bookkeeping.
    let mut bad = ok.clone();
    bad.insert(0, run(vec![decl("eff", 65, call0(ident("f")))]));
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The rethrow must FOLLOW the dispatch.
    let mut bad = ok.clone();
    bad.swap(1, 2);
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The dispatch switch must have exactly two cases…
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases.push(SwitchCase {
        tests: vec![num(1.0)],
        body: vec![],
    });
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … one keyed `undefined` …
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[0].tests = vec![num(1.0)];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … and one default.
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[1].tests = vec![num(2.0)];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The default arm must be pure bookkeeping (+ a break).
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[1].body = vec![run(vec![expr_stmt(call0(ident("f")))])];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … while a labeled break there is not bookkeeping.
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[1].body = vec![SNode::Break {
        label: Some("l".to_string()),
    }];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The run arm must contain a non-bookkeeping finally body.
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[0].body = vec![
        run(vec![phi_assign("pz", ident("w"))]),
        SNode::Break { label: None },
    ];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The finally template forbids control transfers.
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[0].body = vec![
        run(vec![
            expr_stmt(ident("x")),
            Leaf::Raw(Stmt::Return(Some(ident("v")))),
        ]),
        SNode::Break { label: None },
    ];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … and nested control-flow nodes.
    let mut bad = ok.clone();
    let SNode::Switch { cases, .. } = &mut bad[1] else {
        unreachable!()
    };
    cases[0].body = vec![
        run(vec![expr_stmt(ident("x"))]),
        if_node(ident("c"), vec![], vec![]),
        SNode::Break { label: None },
    ];
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // The rethrow conditional must be a `hole != X` compare…
    let mut bad = ok.clone();
    bad[2] = if_node(ident("c"), vec![], vec![]);
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … with a hole operand…
    let mut bad = ok.clone();
    bad[2] = if_node(
        cmp(CmpOp::StrictNotEq, tm("x", 63), tm("y", 64)),
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
        vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
    );
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … and the guard and rethrow must agree on the temp…
    let mut bad = ok.clone();
    bad[2] = if_node(
        cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))])],
        vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
    );
    assert!(ft_extract_dispatch(&bad, "e").is_none());
    // … which must trace through the copy chain to the binding.
    let mut bad = ok.clone();
    let SNode::Stmts(bk) = &mut bad[0] else {
        unreachable!()
    };
    bk[1] = phi_assign("x", tm("note", 98));
    assert!(ft_extract_dispatch(&bad, "e").is_none());
}

#[test]
fn ft_rethrow_temp_polarities_and_bails() {
    let ret_arm = || vec![run(vec![Leaf::Raw(Stmt::Return(None))])];
    let throw_arm = || vec![run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])];
    // Un-negated: `hole != x` → then throws, else returns.
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &throw_arm(),
            &ret_arm(),
        ),
        Some("x".to_string())
    );
    // Hole on the right, NotEq, bookkeeping tolerated in the arms.
    let mut padded_ret = ret_arm();
    padded_ret.insert(0, run(vec![phi_assign("p", ident("q"))]));
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::NotEq, tm("x", 63), Expr::Lit(Lit::Hole)),
            &throw_arm(),
            &padded_ret,
        ),
        Some("x".to_string())
    );
    // Negated: `!(hole != x)` swaps the arms.
    assert_eq!(
        ft_rethrow_temp(
            &isfalse(cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63))),
            &ret_arm(),
            &throw_arm(),
        ),
        Some("x".to_string())
    );
    // The condition must be a != compare against the hole.
    assert_eq!(ft_rethrow_temp(&ident("c"), &throw_arm(), &ret_arm()), None);
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::Eq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &throw_arm(),
            &ret_arm(),
        ),
        None
    );
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Null), tm("x", 63)),
            &throw_arm(),
            &ret_arm(),
        ),
        None
    );
    // The return arm must contain a bare return…
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &throw_arm(),
            &[run(vec![Leaf::Raw(Stmt::Return(Some(ident("v"))))])],
        ),
        None
    );
    // … and no foreign leaves…
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &throw_arm(),
            &[run(vec![
                expr_stmt(call0(ident("f"))),
                Leaf::Raw(Stmt::Return(None)),
            ])],
        ),
        None
    );
    // … and the throw arm must throw a temp/ident…
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), ident("x")),
            &[run(vec![Leaf::Raw(Stmt::Throw(ident("x")))])],
            &ret_arm(),
        ),
        Some("x".to_string()),
        "idents rethrow fine"
    );
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &[run(vec![Leaf::Raw(Stmt::Throw(num(1.0)))])],
            &ret_arm(),
        ),
        None
    );
    // An arm without a terminal at all bails.
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &[run(vec![expr_stmt(ident("x"))])],
            &ret_arm(),
        ),
        None
    );
}

/// A minimal idiom for driving `ft_strip_exits` directly.
fn test_idiom() -> FinallyIdiom {
    let body = vec![
        FTok::Leaf(decl("f1", 70, ident("v"))),
        FTok::Leaf(phi_assign("f3", ident("w"))),
    ];
    FinallyIdiom {
        canon: ft_canon(&body),
        body,
        decls: vec![],
    }
}

fn strip(nodes: &mut Vec<SNode>, idiom: &FinallyIdiom) -> (Result<(), ()>, usize) {
    let mut labels = Vec::new();
    let mut strips = 0;
    let r = ft_strip_exits(
        nodes,
        idiom,
        FtCtx {
            loops: 0,
            breakables: 0,
        },
        &mut labels,
        &mut strips,
    );
    (r, strips)
}

#[test]
fn ft_strip_exits_exit_kinds_and_mismatch_bails() {
    let idiom = test_idiom();
    let copy = || {
        run(vec![
            decl("f1", 70, ident("v")),
            phi_assign("f3", ident("w")),
        ])
    };
    // An unlabeled break/continue at construct level needs a copy.
    let mut nodes = vec![copy(), SNode::Break { label: None }];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 1);
    assert_eq!(nodes.len(), 1);
    let mut nodes = vec![copy(), SNode::Continue { label: None }];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 1);
    // A copy-free construct is untouched.
    let mut nodes = vec![run(vec![expr_stmt(ident("a"))])];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 0);
    // If arms recurse.
    let mut nodes = vec![if_node(
        ident("c"),
        vec![copy(), run(vec![Leaf::Raw(Stmt::Return(None))])],
        vec![copy(), run(vec![Leaf::Raw(Stmt::Return(None))])],
    )];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 2);
    // An exit without room for its copy.
    let mut nodes = vec![run(vec![Leaf::Raw(Stmt::Return(None))])];
    let (r, _) = strip(&mut nodes, &idiom);
    assert!(r.is_err());
    // An exit whose copy differs.
    let mut nodes = vec![
        run(vec![decl("f1", 70, ident("v"))]),
        run(vec![Leaf::Raw(Stmt::Return(None))]),
    ];
    let (r, _) = strip(&mut nodes, &idiom);
    assert!(r.is_err());
    // The return-value guard: the copy rebinds a name the return
    // reads.
    let mut nodes = vec![
        run(vec![
            decl("f1", 70, ident("v")),
            phi_assign("f3", ident("w")),
        ]),
        run(vec![Leaf::Raw(Stmt::Return(Some(tm("f3", 71))))]),
    ];
    let (r, _) = strip(&mut nodes, &idiom);
    assert!(r.is_err());
    // … but a copy assigning names the value does not read is fine.
    let mut nodes = vec![
        copy(),
        run(vec![Leaf::Raw(Stmt::Return(Some(ident("safe"))))]),
    ];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 1);
    // Loop-intercepted exits need no copy.
    let mut nodes = vec![SNode::While {
        label: None,
        cond: None,
        body: vec![
            run(vec![expr_stmt(ident("x"))]),
            SNode::Break { label: None },
            SNode::Continue { label: None },
        ],
    }];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 0);
    // A labeled exit naming an enclosing (pushed) label needs none.
    let mut nodes = vec![SNode::While {
        label: Some("wl".to_string()),
        cond: None,
        body: vec![
            run(vec![expr_stmt(ident("x"))]),
            SNode::Continue {
                label: Some("wl".to_string()),
            },
        ],
    }];
    let (r, strips) = strip(&mut nodes, &idiom);
    assert!(r.is_ok() && strips == 0);
}

#[test]
fn ft_fold_at_bail_pins() {
    // A catch body that is not the dispatch shape.
    let nodes = vec![SNode::Try {
        body: vec![],
        catches: vec![catch("e", vec![run(vec![expr_stmt(ident("x"))])])],
        note: Some("protected body (finally idiom)".to_string()),
        finally: None,
    }];
    assert!(ft_fold_at(&nodes, 0).is_none());
    // An exit in the protected construct without its copy.
    let nodes = vec![SNode::Try {
        body: vec![run(vec![Leaf::Raw(Stmt::Return(None))])],
        catches: vec![catch("e", dispatch_body())],
        note: Some("protected body (finally idiom)".to_string()),
        finally: None,
    }];
    assert!(ft_fold_at(&nodes, 0).is_none());
    // A fall-through construct whose tail lacks the copy.
    let mut nodes = vec![SNode::Try {
        body: vec![run(vec![expr_stmt(ident("a"))])],
        catches: vec![catch("e", dispatch_body())],
        note: Some("protected body (finally idiom)".to_string()),
        finally: None,
    }];
    assert!(ft_fold_at(&nodes, 0).is_none());
    // … and with the right tail, the bare construct folds.
    nodes.push(run(finally_template()));
    let out = ft_fold_at(&nodes, 0).expect("tail copy consumed");
    assert!(matches!(&out[1], SNode::Honest(_)));
    let SNode::Try {
        finally: Some(fin), ..
    } = &out[2]
    else {
        unreachable!()
    };
    assert_eq!(fin.len(), 1, "the template regroups to one run");
    // A copy differing in the tail position bails.
    let mut nodes = vec![SNode::Try {
        body: vec![run(vec![expr_stmt(ident("a"))])],
        catches: vec![catch("e", dispatch_body())],
        note: Some("protected body (finally idiom)".to_string()),
        finally: None,
    }];
    nodes.push(run(vec![decl("f1", 70, ident("DIFFERENT"))]));
    assert!(ft_fold_at(&nodes, 0).is_none());
    // The unwrap form (sole inner try/catch) also folds; the inner
    // catch falls through, so the tail copy is consumed too.
    let inner = try_node(
        vec![
            run(finally_template()),
            run(vec![Leaf::Raw(Stmt::Return(None))]),
        ],
        vec![catch("ie", vec![run(vec![expr_stmt(ident("h"))])])],
    );
    let nodes = vec![
        SNode::Try {
            body: vec![inner],
            catches: vec![catch("e", dispatch_body())],
            note: Some("protected body (finally idiom)".to_string()),
            finally: None,
        },
        run(finally_template()),
    ];
    let out = ft_fold_at(&nodes, 0).expect("the unwrap construct");
    let SNode::Try {
        catches,
        finally: Some(_),
        ..
    } = &out[2]
    else {
        unreachable!()
    };
    assert_eq!(catches.len(), 1, "the inner catch survives the unwrap");
    // The idiom note is required (the driver pre-filter).
    let mut nodes = vec![SNode::Try {
        body: vec![],
        catches: vec![catch("e", dispatch_body())],
        note: Some("some other note".to_string()),
        finally: None,
    }];
    let mut stats = FoldStats::default();
    fold_finally(&mut nodes, &mut stats);
    assert_eq!(stats.finally_fold, 0);
    // … and a `finally: Some` try is never re-folded.
    let mut nodes = vec![SNode::Try {
        body: vec![],
        catches: vec![catch("e", dispatch_body())],
        note: Some("protected body (finally idiom)".to_string()),
        finally: Some(vec![]),
    }];
    let mut stats = FoldStats::default();
    fold_finally(&mut nodes, &mut stats);
    assert_eq!(stats.finally_fold, 0);
}

#[test]
fn dissolve_rethrow_trys_variants() {
    // The bare-rethrow wrapper dissolves loudly (Honest + body).
    let mut nodes = vec![try_node(
        vec![run(vec![expr_stmt(ident("protected"))])],
        vec![catch(
            "e",
            vec![run(vec![
                Leaf::Raw(Stmt::Throw(tm("e", 60))),
                Leaf::Raw(Stmt::Unreachable),
            ])],
        )],
    )];
    dissolve_rethrow_trys(&mut nodes);
    assert_eq!(
        nodes,
        vec![
            SNode::Honest("rethrow-only try/catch dissolved (semantic no-op)".to_string()),
            run(vec![expr_stmt(ident("protected"))]),
        ]
    );
    // An empty try body stays; so does a catch doing anything else.
    let mut nodes = vec![try_node(
        vec![],
        vec![catch(
            "e",
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("e", 60)))])],
        )],
    )];
    dissolve_rethrow_trys(&mut nodes);
    assert_eq!(nodes.len(), 1);
    let mut nodes = vec![try_node(
        vec![run(vec![expr_stmt(ident("protected"))])],
        vec![catch(
            "e",
            vec![run(vec![
                Leaf::Raw(Stmt::Throw(tm("e", 60))),
                expr_stmt(ident("extra")),
            ])],
        )],
    )];
    dissolve_rethrow_trys(&mut nodes);
    assert!(matches!(&nodes[0], SNode::Try { .. }));
    // A catch throwing a DIFFERENT temp is not a bare rethrow.
    let mut nodes = vec![try_node(
        vec![run(vec![expr_stmt(ident("protected"))])],
        vec![catch(
            "e",
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("other", 99)))])],
        )],
    )];
    dissolve_rethrow_trys(&mut nodes);
    assert!(matches!(&nodes[0], SNode::Try { .. }));
    // A non-run catch body stays.
    let mut nodes = vec![try_node(
        vec![run(vec![expr_stmt(ident("protected"))])],
        vec![catch("e", vec![SNode::Break { label: None }])],
    )];
    dissolve_rethrow_trys(&mut nodes);
    assert!(matches!(&nodes[0], SNode::Try { .. }));
    // A bare throw of the binding with NO body…
    let mut nodes = vec![try_node(
        vec![run(vec![expr_stmt(ident("protected"))])],
        vec![CatchClause {
            binding: None,
            body: vec![run(vec![Leaf::Raw(Stmt::Throw(ident("e")))])],
        }],
    )];
    dissolve_rethrow_trys(&mut nodes);
    // binding None → "" — the thrown ident "e" ≠ "" → kept.
    assert!(matches!(&nodes[0], SNode::Try { .. }));
}

#[test]
fn residual_ft_extract_and_strip_pins() {
    // Copy-chain edges through Declare leaves trace too (Assign
    // leaves are never bookkeeping, so that edge arm is filtered
    // out upstream).
    let mut body = dispatch_body();
    let SNode::Stmts(bk) = &mut body[0] else {
        unreachable!()
    };
    // y ← e via a Declare, x ← y via the phi assign: x traces.
    bk[1] = decl("y", 66, tm("e", 61));
    bk.push(phi_assign("x", tm("y", 66)));
    assert!(ft_extract_dispatch(&body, "e").is_some());
    // … but the guard/rethrow temp must still trace to the binding:
    // with the phi assign gone and no Declare edge, x dangles.
    let mut body = dispatch_body();
    let SNode::Stmts(bk) = &mut body[0] else {
        unreachable!()
    };
    bk.remove(1);
    assert!(ft_extract_dispatch(&body, "e").is_none());
    // A cyclic copy chain still terminates the BFS.
    let mut body = dispatch_body();
    let SNode::Stmts(bk) = &mut body[0] else {
        unreachable!()
    };
    bk[1] = phi_assign("x", tm("y", 97));
    bk.push(phi_assign("y", tm("x", 63)));
    assert!(ft_extract_dispatch(&body, "e").is_none());
    // ft_rethrow_temp: an arm of pure bookkeeping has no terminal.
    assert_eq!(
        ft_rethrow_temp(
            &cmp(CmpOp::StrictNotEq, Expr::Lit(Lit::Hole), tm("x", 63)),
            &[run(vec![Leaf::Raw(Stmt::Throw(tm("x", 63)))])],
            &[run(vec![phi_assign("p", ident("q"))])],
        ),
        None
    );
    // ft_fold_at's own entry guards (the driver normally
    // pre-filters; the matcher is total on its own).
    let not_try = vec![SNode::Honest("h".to_string())];
    assert!(ft_fold_at(&not_try, 0).is_none());
    let no_note = vec![SNode::Try {
        body: vec![],
        catches: vec![catch("e", dispatch_body())],
        note: None,
        finally: None,
    }];
    assert!(ft_fold_at(&no_note, 0).is_none());
    let two_catches = vec![SNode::Try {
        body: vec![],
        catches: vec![catch("e", dispatch_body()), catch("e2", vec![])],
        note: Some("protected body (finally idiom)".to_string()),
        finally: None,
    }];
    assert!(ft_fold_at(&two_catches, 0).is_none());
    // ft_strip_exits: a DIFFERENT copy at a far-enough exit hits
    // the canon comparison (not the room check).
    let idiom = test_idiom();
    let mut nodes = vec![
        run(vec![
            decl("f1", 70, ident("DIFFERENT")),
            phi_assign("f3", ident("w")),
        ]),
        run(vec![Leaf::Raw(Stmt::Return(None))]),
    ];
    let (r, _) = strip(&mut nodes, &idiom);
    assert!(r.is_err());
}

#[test]
fn last_residual_pins() {
    // The driver pre-run walks stop at a non-run, non-comment
    // sibling.
    let mut nodes = driver_shape();
    nodes.insert(0, SNode::Break { label: None });
    // (the While now sits at index 2; match directly)
    assert!(match_for_await_driver(&nodes, 2).is_some());
    let mut stats = FoldStats::default();
    fold(&mut nodes, &mut stats);
    assert_eq!(stats.for_await_of, 1);
    assert!(matches!(&nodes[0], SNode::Break { .. }), "{nodes:?}");
    // match_switch_chain: a loop break inside the trailing-else
    // (default) arm refuses the fold.
    let bad = if_node(
        cmp(CmpOp::StrictEq, tm("x", 1), num(1.0)),
        vec![run(vec![expr_stmt(call0(ident("a")))])],
        vec![SNode::Break { label: None }],
    );
    assert!(match_switch_chain(&bad).is_none());
}
