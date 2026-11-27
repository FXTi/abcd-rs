//! Object/array/spread literal builders, rest destructuring, `scope_fold`, `late_decl`, and `rest_param` tests.

use super::*;

/// control-flow region (bare keep-alive statements plus one real
/// use), a `rest` name collision, and every census leaf kind.
fn rest_param_body() -> Vec<SNode> {
    let bare = || run(vec![expr_stmt(Expr::RestArgs { start_index: 1 })]);
    vec![
        run(vec![
            phi_assign("p", ident("z")),
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
            Leaf::Decl {
                name: "ld".to_string(),
                mutable: true,
                value: None,
            },
            Leaf::Assign {
                target: "la".to_string(),
                value: ident("v"),
            },
            phi_decl("pd", 61),
            // The collision: `rest` is already taken.
            expr_stmt(ident("rest")),
            // The one real use of the rest array.
            decl("args", 60, Expr::RestArgs { start_index: 1 }),
        ]),
        if_node(ident("c"), vec![bare()], vec![bare()]),
        SNode::While {
            label: None,
            cond: Some(ident("w")),
            body: vec![bare()],
        },
        SNode::DoWhile {
            label: None,
            body: vec![bare()],
            cond: ident("dw"),
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: vec![bare()],
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: vec![bare()],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: vec![bare()],
        },
        SNode::Try {
            body: vec![bare()],
            catches: vec![catch("e", vec![bare()])],
            note: None,
            finally: Some(vec![bare()]),
        },
        SNode::Switch {
            disc: ident("s"),
            cases: vec![SwitchCase {
                tests: vec![num(1.0)],
                body: vec![bare()],
            }],
        },
        SNode::Break { label: None },
        SNode::Continue { label: None },
        SNode::Honest("h".to_string()),
    ]
}

#[test]
fn rest_param_fold_with_control_flow_and_name_collision() {
    let mut nodes = rest_param_body();
    let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
    assert_eq!(stats.rest_param, 1);
    // The staging slot dropped; the collision-free name joined.
    assert_eq!(params, vec!["h0", "a", "...rest$1"]);
    // The real use now reads the rest parameter…
    let SNode::Stmts(first) = &nodes[0] else {
        unreachable!()
    };
    assert!(
        first.iter().any(
            |l| matches!(l, Leaf::Raw(Stmt::Declare { value, .. }) if *value == ident("rest$1"))
        ),
        "{first:?}"
    );
    // … and every bare keep-alive statement is gone.
    let mut bare = 0usize;
    map_exprs_mut(&mut nodes, &mut |e| {
        if matches!(e, Expr::RestArgs { .. }) {
            bare += 1;
        }
    });
    assert_eq!(bare, 0);
    let mut leaves = 0usize;
    walk_leaves(&nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::Expr(_))) {
            leaves += 1;
        }
    });
    assert_eq!(leaves, 1, "only the collision probe remains");
}

#[test]
fn rest_param_fold_bail_pins() {
    // More than one CopyRestArgs shape.
    let mut nodes = vec![run(vec![
        decl("a", 60, Expr::RestArgs { start_index: 1 }),
        decl("b", 61, Expr::RestArgs { start_index: 2 }),
    ])];
    let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
    let before = params.clone();
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
    assert_eq!(stats.rest_param, 0);
    assert_eq!(params, before);
    // Fewer visible params than the rest index.
    let mut nodes = vec![run(vec![decl("a", 60, Expr::RestArgs { start_index: 1 })])];
    let mut params = vec!["h0".to_string()];
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
    assert_eq!(stats.rest_param, 0);
    // A dropped staging slot referenced in the body.
    let mut nodes = vec![run(vec![
        decl("a", 60, Expr::RestArgs { start_index: 1 }),
        expr_stmt(ident("p2")),
    ])];
    let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
    assert_eq!(stats.rest_param, 0);
    // The no-collision fast path keeps the plain name.
    let mut nodes = vec![run(vec![decl("a", 60, Expr::RestArgs { start_index: 1 })])];
    let mut params = vec!["h0".to_string(), "a".to_string(), "p2".to_string()];
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 1, &mut stats);
    assert_eq!(stats.rest_param, 1);
    assert_eq!(params, vec!["h0", "a", "...rest"]);
}

// ── N74-W4: late declaration-site reconstruction ───────────────

/// A conversion-candidate body touching every declaration-capable
/// and non-capable region.
fn late_decl_body() -> Vec<SNode> {
    let store = |slot: u16, name: &str| {
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot,
            own: true,
            name: name.to_string(),
            value: ident("v"),
        })
    };
    vec![
        run(vec![Leaf::Raw(Stmt::ScopePush {
            names: vec![Some("a".to_string())],
        })]),
        // Root: converted (function-scope let).
        run(vec![store(0, "r"), expr_stmt(ident("r"))]),
        // A labeled block is declaration-capable.
        SNode::Labeled {
            label: "lbl".to_string(),
            body: vec![run(vec![store(0, "l")])],
        },
        // So are the try body, catch, and finally regions.
        SNode::Try {
            body: vec![run(vec![store(0, "t")])],
            catches: vec![catch("e", vec![run(vec![store(0, "c")])])],
            note: None,
            finally: Some(vec![run(vec![store(0, "f")])]),
        },
        // Loops and switch cases are not capable: stores there stay
        // plain assignments (the name is also declared at the root
        // so the coverage model is satisfied).
        SNode::While {
            label: None,
            cond: None,
            body: vec![run(vec![store(0, "w")])],
        },
        SNode::DoWhile {
            label: None,
            body: vec![run(vec![store(0, "dw")])],
            cond: ident("dc"),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("it"),
            body: vec![run(vec![store(0, "fo")])],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("ob"),
            body: vec![run(vec![store(0, "fi")])],
        },
        SNode::Switch {
            disc: ident("sd"),
            cases: vec![SwitchCase {
                tests: vec![num(1.0)],
                body: vec![run(vec![store(0, "sw")])],
            }],
        },
        // An if arm is a capable region of its own.
        if_node(ident("ic"), vec![run(vec![store(0, "ia")])], vec![]),
        // Census-only leaf kinds (uses feeding the coverage model).
        run(vec![
            Leaf::Raw(Stmt::ScopePop),
            Leaf::Assign {
                target: "asg".to_string(),
                value: ident("v"),
            },
            Leaf::Raw(Stmt::Throw(ident("th"))),
            Leaf::Destructure {
                obj: ident("ob"),
                keys: vec![],
                rest: "rest".to_string(),
            },
        ]),
        SNode::Break { label: None },
        SNode::Honest("h".to_string()),
    ]
}

#[test]
fn late_decl_fold_regions_and_conversions() {
    let mut nodes = late_decl_body();
    let mut stats = FoldStats::default();
    late_decl_fold(&mut nodes, &[], true, &mut stats);
    // r (root) + l (labeled) + t/c/f (try regions) + ia (if arm).
    assert_eq!(stats.late_decl, 6, "{stats:?}");
    // The labeled-region store became the declaration.
    let SNode::Labeled { body, .. } = &nodes[2] else {
        unreachable!()
    };
    assert!(
        matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "l"))
    );
    // The try regions converted too.
    let SNode::Try {
        body,
        catches,
        finally: Some(fin),
        ..
    } = &nodes[3]
    else {
        unreachable!()
    };
    assert!(
        matches!(&body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "t"))
    );
    assert!(
        matches!(&catches[0].body[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "c"))
    );
    assert!(
        matches!(&fin[0], SNode::Stmts(run) if matches!(&run[0], Leaf::Decl { name, .. } if name == "f"))
    );
    // The loop store is NOT declaration-capable: unchanged.
    let SNode::While { body, .. } = &nodes[4] else {
        unreachable!()
    };
    assert!(matches!(
        &body[0],
        SNode::Stmts(run) if matches!(&run[0], Leaf::Raw(Stmt::LexStore { name, .. }) if name == "w")
    ));
    // The root store became a declaration; its read is intact.
    let SNode::Stmts(root) = &nodes[1] else {
        unreachable!()
    };
    assert!(matches!(&root[0], Leaf::Decl { name, .. } if name == "r"));
}

#[test]
fn late_decl_fold_bail_pins() {
    let store = |name: &str| {
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: name.to_string(),
            value: ident("v"),
        })
    };
    let push = || {
        run(vec![Leaf::Raw(Stmt::ScopePush {
            names: vec![Some("a".to_string())],
        })])
    };
    let bail = |nodes: Vec<SNode>, params: &[String], top: bool| {
        let mut nodes = nodes;
        let mut stats = FoldStats::default();
        late_decl_fold(&mut nodes, params, top, &mut stats);
        assert_eq!(stats.late_decl, 0, "{nodes:?}");
        nodes
    };
    // A lexical/global mix for one name.
    bail(
        vec![
            push(),
            run(vec![
                store("m"),
                Leaf::Raw(Stmt::GlobalStore {
                    name: "m".to_string(),
                    value: ident("v"),
                    tolerant: false,
                }),
            ]),
        ],
        &[],
        true,
    );
    // A capture-level store (level >= own pushes).
    bail(
        vec![
            push(),
            run(vec![Leaf::Raw(Stmt::LexStore {
                level: 5,
                slot: 0,
                own: false,
                name: "cap".to_string(),
                value: ident("v"),
            })]),
        ],
        &[],
        true,
    );
    // A global store below the top level.
    bail(
        vec![run(vec![Leaf::Raw(Stmt::GlobalStore {
            name: "g".to_string(),
            value: ident("v"),
            tolerant: false,
        })])],
        &[],
        false,
    );
    // A function-valued binding at the module top.
    bail(
        vec![
            push(),
            run(vec![Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot: 0,
                own: true,
                name: "fv".to_string(),
                value: Expr::Closure {
                    body: FuncId::new(0),
                    name: "f".to_string(),
                    kind: FunctionKind::Function,
                    captures: vec![],
                },
            })]),
        ],
        &[],
        true,
    );
    // A parameter / an already-declared name.
    bail(
        vec![push(), run(vec![store("p")])],
        &["p".to_string()],
        true,
    );
    bail(
        vec![
            push(),
            run(vec![
                Leaf::Decl {
                    name: "d".to_string(),
                    mutable: true,
                    value: None,
                },
                store("d"),
            ]),
        ],
        &[],
        true,
    );
    // A read outside the store's region is not covered.
    bail(
        vec![
            push(),
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![run(vec![store("u")])],
            },
            run(vec![expr_stmt(ident("u"))]),
        ],
        &[],
        true,
    );
    // Nested converted regions (store in a try body AND in an if
    // arm inside it).
    bail(
        vec![
            push(),
            SNode::Try {
                body: vec![
                    run(vec![store("n")]),
                    if_node(ident("c"), vec![run(vec![store("n")])], vec![]),
                ],
                catches: vec![],
                note: None,
                finally: None,
            },
        ],
        &[],
        true,
    );
    // A same-name re-push mid-span splits the binding.
    bail(
        vec![push(), run(vec![store("s")]), push(), run(vec![store("s")])],
        &[],
        true,
    );
    // The root fast path: one store covering everything converts.
    let mut nodes = vec![push(), run(vec![store("ok")])];
    let mut stats = FoldStats::default();
    late_decl_fold(&mut nodes, &[], true, &mut stats);
    assert_eq!(stats.late_decl, 1);
    // A second store of a converted name becomes an assignment.
    let mut nodes = vec![push(), run(vec![store("ok"), store("ok")])];
    let mut stats = FoldStats::default();
    late_decl_fold(&mut nodes, &[], true, &mut stats);
    assert_eq!(stats.late_decl, 1);
    let SNode::Stmts(got) = &nodes[1] else {
        unreachable!()
    };
    assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "ok"));
    assert!(matches!(&got[1], Leaf::Assign { target, .. } if target == "ok"));
}

#[test]
fn scope_fold_push_site_variants() {
    let push = |names: &[&str]| {
        Leaf::Raw(Stmt::ScopePush {
            names: names.iter().map(|n| Some(n.to_string())).collect(),
        })
    };
    let store = |slot: u16, name: &str| {
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot,
            own: true,
            name: name.to_string(),
            value: ident("v"),
        })
    };
    // Both slots declared: the push is consumed.
    let mut nodes = vec![run(vec![push(&["a", "b"]), store(0, "a"), store(1, "b")])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 2);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "a"));
    assert_eq!(got.len(), 2, "the push was consumed: {got:?}");
    // A re-store of an initialized slot ends the init run; the
    // later re-store becomes a plain assignment.
    let mut nodes = vec![run(vec![push(&["a"]), store(0, "a"), store(0, "a")])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 1);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(matches!(&got[1], Leaf::Assign { target, .. } if target == "a"));
    // Elided/fallback markers interleave with the init run.
    let mut nodes = vec![run(vec![push(&["a"]), elided("Guard"), store(0, "a")])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 1);
    // A non-store leaf ends the init run: nothing converts.
    let mut nodes = vec![run(vec![
        push(&["a"]),
        expr_stmt(ident("x")),
        store(0, "a"),
    ])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 0);
    // A parameter name is never redeclared.
    let mut nodes = vec![run(vec![push(&["a"]), store(0, "a")])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &["a".to_string()], &mut stats);
    assert_eq!(stats.scope_fold, 0);
    // Two same-named slots in one push: only the first declares;
    // the push stays for the other slot.
    let mut nodes = vec![run(vec![push(&["n", "n"]), store(0, "n"), store(1, "n")])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 1);
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    assert!(
        matches!(&got[0], Leaf::Raw(Stmt::ScopePush { names }) if names.len() == 1),
        "the undeclared slot keeps the push: {got:?}"
    );
    // A store of the same name in ANOTHER run blocks the fold.
    let mut nodes = vec![
        run(vec![push(&["a"]), store(0, "a")]),
        run(vec![store(0, "a")]),
    ];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 0);
    // A second push of an already-converted name skips it (same
    // run: the name declares at its first push only).
    let mut nodes = vec![run(vec![
        push(&["a"]),
        store(0, "a"),
        push(&["a"]),
        store(0, "a"),
    ])];
    let mut stats = FoldStats::default();
    scope_fold(&mut nodes, &[], &mut stats);
    assert_eq!(stats.scope_fold, 1, "a once: {nodes:?}");
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    // The first push was consumed (its slot declared); the second
    // push stays (its re-store was not an init-run candidate).
    assert!(matches!(&got[0], Leaf::Decl { name, .. } if name == "a"));
    assert!(
        got.iter()
            .any(|l| matches!(l, Leaf::Assign { target, .. } if target == "a"))
    );
}

#[test]
fn object_literal_full_absorb_matrix() {
    // One builder sequence with every absorbable statement kind:
    // literal-key dynamic store, computed dynamic store, literal
    // and computed index stores, spread, __proto__, a method, and
    // both accessor forms — plus an interleaved key temp that
    // inlines into the folded literal.
    let leaves = vec![
        decl(
            "o",
            10,
            Expr::ObjectLit {
                entries: vec![(Lit::String("a".to_string()), Lit::Number(1.0f64.to_bits()))],
            },
        ),
        decl("ck", 11, call0(ident("key_fn"))), // skipped, used once
        Leaf::Raw(Stmt::StoreDyn {
            object: tm("o", 10),
            key: tm("ck", 11),
            value: num(2.0),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreDyn {
            object: tm("o", 10),
            key: strlit("lit"),
            value: num(3.0),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("o", 10),
            index: num(7.0),
            value: num(4.0),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("o", 10),
            index: tm("ix", 12),
            value: num(5.0),
            own: true,
        }),
        expr_stmt(Expr::CopyDataProps {
            dst: bx(tm("o", 10)),
            src: bx(ident("src")),
        }),
        expr_stmt(Expr::SetObjectWithProto {
            obj: bx(tm("o", 10)),
            proto: bx(ident("proto")),
        }),
        Leaf::Raw(Stmt::DefineMethod {
            object: tm("o", 10),
            name: "m".to_string(),
            func: closure("mf"),
            length: 0,
        }),
        expr_stmt(Expr::DefineGetterSetter {
            obj: bx(tm("o", 10)),
            key: bx(strlit("acc")),
            getter: bx(closure("ag")),
            setter: bx(Expr::Lit(Lit::Undefined)),
        }),
        expr_stmt(Expr::DefineGetterSetter {
            obj: bx(tm("o", 10)),
            key: bx(num(9.0)),
            getter: bx(Expr::Lit(Lit::Undefined)),
            setter: bx(closure("as")),
        }),
        expr_stmt(call0(ident("unrelated"))),
    ];
    let mut leaves = leaves;
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 1);
    let [
        Leaf::Raw(Stmt::Declare { value, .. }),
        Leaf::Raw(Stmt::Expr(_)),
    ] = leaves.as_slice()
    else {
        panic!("declare + trailing stmt: {leaves:?}")
    };
    let Expr::ObjectBuild { entries } = value else {
        panic!("folded literal: {value:?}")
    };
    let kinds: Vec<&str> = entries
        .iter()
        .map(|e| match e {
            ObjEntry::KeyValue(..) => "kv",
            ObjEntry::Computed(..) => "computed",
            ObjEntry::Spread(..) => "spread",
            ObjEntry::Proto(..) => "proto",
            ObjEntry::Method(..) => "method",
            ObjEntry::Getter(..) => "getter",
            ObjEntry::Setter(..) => "setter",
        })
        .collect();
    assert_eq!(
        kinds,
        [
            "kv", "computed", "kv", "kv", "computed", "spread", "proto", "method", "getter",
            "setter"
        ]
    );
    // The skipped key temp inlined into the computed entry.
    assert_eq!(
        entries[1],
        ObjEntry::Computed(call0(ident("key_fn")), num(2.0))
    );
    // Literal keys via StoreDyn/StoreIndex keep the literal form.
    assert_eq!(
        entries[2],
        ObjEntry::KeyValue(Lit::String("lit".to_string()), num(3.0))
    );
    assert_eq!(
        entries[3],
        ObjEntry::KeyValue(Lit::Number(7.0f64.to_bits()), num(4.0))
    );
    // The accessor keys: a literal name and a computed expression.
    assert!(matches!(&entries[8], ObjEntry::Getter(ObjKey::Name(n), _) if n == "acc"));
    assert!(matches!(
        &entries[9],
        ObjEntry::Setter(ObjKey::Computed(_), _)
    ));
}

#[test]
fn array_literal_contiguity_and_spread() {
    // Strict contiguity from the shape length; a spread ends the
    // absorbable run of items.
    let leaves = vec![
        decl(
            "a",
            20,
            Expr::ArrayLit {
                elements: vec![Lit::Number(0.0f64.to_bits())],
            },
        ),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(1.0),
            value: ident("e1"),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(2.0),
            value: ident("e2"),
            own: true,
        }),
        expr_stmt(Expr::ArraySpread {
            dst: bx(tm("a", 20)),
            index: bx(num(3.0)),
            src: bx(ident("rest")),
        }),
        // Past a spread the running index is unknowable: stays.
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(3.0),
            value: ident("e3"),
            own: true,
        }),
    ];
    let mut leaves = leaves;
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.array_lit, 1);
    let Leaf::Raw(Stmt::Declare { value, .. }) = &leaves[0] else {
        unreachable!()
    };
    let Expr::ArrayBuild { elements } = value else {
        panic!("folded array: {value:?}")
    };
    assert_eq!(elements.len(), 4);
    assert!(matches!(&elements[3], ArrayElem::Spread(e) if *e == ident("rest")));
    assert!(
        matches!(&leaves[1], Leaf::Raw(Stmt::StoreIndex { .. })),
        "the post-spread store stays: {leaves:?}"
    );
    // A gap index keeps the store out of the literal.
    let mut leaves = vec![
        decl("a", 20, Expr::ArrayLit { elements: vec![] }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(5.0),
            value: ident("e1"),
            own: true,
        }),
    ];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.array_lit, 0);
    assert_eq!(leaves.len(), 2);
    // A non-literal index / a non-own store are never items.
    let mut leaves = vec![
        decl("a", 20, Expr::ArrayLit { elements: vec![] }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: ident("i"),
            value: ident("e1"),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(0.0),
            value: ident("e2"),
            own: false,
        }),
    ];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.array_lit, 0);
    // A fractional/negative index is not an array slot.
    let mut leaves = vec![
        decl("a", 20, Expr::ArrayLit { elements: vec![] }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(1.5),
            value: ident("e1"),
            own: true,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: tm("a", 20),
            index: num(-1.0),
            value: ident("e2"),
            own: true,
        }),
    ];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.array_lit, 0);
}

#[test]
fn literal_builder_bail_pins() {
    let obj = || decl("o", 10, Expr::ObjectLit { entries: vec![] });
    // absorb_one guards, one per arm.
    let vid = ValueId::new(10);
    // A non-own store is not a literal entry.
    assert!(
        absorb_one(
            &Leaf::Raw(Stmt::StoreProp {
                object: tm("o", 10),
                name: "k".to_string(),
                dot_legal: true,
                value: ident("v"),
                own: false,
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // A self-referential value can never be reordered.
    assert!(
        absorb_one(
            &Leaf::Raw(Stmt::StoreProp {
                object: tm("o", 10),
                name: "k".to_string(),
                dot_legal: true,
                value: tm("o", 10),
                own: true,
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // A computed-key store whose KEY mentions the object.
    assert!(
        absorb_one(
            &Leaf::Raw(Stmt::StoreDyn {
                object: tm("o", 10),
                key: tm("o", 10),
                value: ident("v"),
                own: true,
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // A spread whose source mentions the object.
    assert!(
        absorb_one(
            &expr_stmt(Expr::CopyDataProps {
                dst: bx(tm("o", 10)),
                src: bx(tm("o", 10)),
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // A proto set on a different object.
    assert!(
        absorb_one(
            &expr_stmt(Expr::SetObjectWithProto {
                obj: bx(ident("other")),
                proto: bx(ident("p")),
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // An array spread is not an object entry (and vice versa).
    assert!(
        absorb_one(
            &expr_stmt(Expr::ArraySpread {
                dst: bx(tm("o", 10)),
                index: bx(num(0.0)),
                src: bx(ident("s")),
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // Accessors must be closures or the undefined absence marker…
    assert!(
        absorb_one(
            &expr_stmt(Expr::DefineGetterSetter {
                obj: bx(tm("o", 10)),
                key: bx(strlit("k")),
                getter: bx(call0(ident("not_a_closure_value"))),
                setter: bx(Expr::Lit(Lit::Undefined)),
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // … and at least one of them must exist.
    assert!(
        absorb_one(
            &expr_stmt(Expr::DefineGetterSetter {
                obj: bx(tm("o", 10)),
                key: bx(strlit("k")),
                getter: bx(Expr::Lit(Lit::Undefined)),
                setter: bx(Expr::Lit(Lit::Undefined)),
            }),
            vid,
            false,
            &[],
            0,
        )
        .is_none()
    );
    // An unrelated statement is never absorbable.
    assert!(absorb_one(&expr_stmt(ident("x")), vid, false, &[], 0).is_none());
    let _ = obj;

    // The skipped-declare resolution (N74-W4).
    // A pure unused declare interleaved in the sequence drops.
    let mut leaves = vec![
        obj(),
        decl("dead", 11, strlit("pure")),
        Leaf::Raw(Stmt::StoreProp {
            object: tm("o", 10),
            name: "k".to_string(),
            dot_legal: true,
            value: ident("v"),
            own: true,
        }),
    ];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 1);
    assert_eq!(leaves.len(), 1, "the dead declare dropped: {leaves:?}");
    // A temp chain inlines in decision order (k1 → k2 → the entry).
    let mut leaves = vec![
        obj(),
        decl("k1", 11, strlit("one")),
        decl("k2", 12, tm("k1", 11)),
        Leaf::Raw(Stmt::StoreDyn {
            object: tm("o", 10),
            key: tm("k2", 12),
            value: ident("v"),
            own: true,
        }),
    ];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 1);
    let Leaf::Raw(Stmt::Declare { value, .. }) = &leaves[0] else {
        unreachable!()
    };
    let Expr::ObjectBuild { entries } = value else {
        unreachable!()
    };
    assert_eq!(
        entries[0],
        ObjEntry::Computed(strlit("one"), ident("v")),
        "chained inline: {entries:?}"
    );
    // A temp used twice cannot inline: the whole fold bails.
    let mut leaves = vec![
        obj(),
        decl("ck", 11, call0(ident("key_fn"))),
        Leaf::Raw(Stmt::StoreDyn {
            object: tm("o", 10),
            key: tm("ck", 11),
            value: tm("ck", 11),
            own: true,
        }),
    ];
    let before = leaves.clone();
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 0);
    assert_eq!(leaves, before);
    // An impure skipped declare used nowhere also bails the fold.
    let mut leaves = vec![
        obj(),
        decl("ck", 11, call0(ident("key_fn"))),
        Leaf::Raw(Stmt::StoreProp {
            object: tm("o", 10),
            name: "k".to_string(),
            dot_legal: true,
            value: ident("v"),
            own: true,
        }),
    ];
    let before = leaves.clone();
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 0);
    assert_eq!(leaves, before);
    // A declare of a non-literal value is not a builder start.
    let mut leaves = vec![decl("o", 10, ident("not_a_literal"))];
    let mut stats = FoldStats::default();
    fold_literal_builders(&mut leaves, &mut stats);
    assert_eq!(stats.object_lit, 0);
}

#[test]
fn rest_destructure_key_forms_and_bails() {
    // The excluded keys resolve through PropName / PropDyn /
    // PropIndex loads (literals only for the computed forms).
    let mut leaves = vec![
        decl("x", 21, prop(ident("o"), "a")),
        decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![strlit("a"), strlit("b"), strlit("c")],
            },
        ),
        decl(
            "y",
            22,
            Expr::PropDyn {
                object: bx(ident("o")),
                key: bx(strlit("b")),
            },
        ),
        decl(
            "z",
            23,
            Expr::PropIndex {
                object: bx(ident("o")),
                index: bx(strlit("c")),
            },
        ),
    ];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 1);
    assert_eq!(
        leaves,
        vec![Leaf::Destructure {
            obj: ident("o"),
            keys: vec![
                ("a".to_string(), "x".to_string()),
                ("b".to_string(), "y".to_string()),
                ("c".to_string(), "z".to_string()),
            ],
            rest: "rest".to_string(),
        }]
    );
    // A non-string excluded key is not a destructure.
    let mut leaves = vec![decl(
        "rest",
        20,
        Expr::RestObject {
            obj: bx(ident("o")),
            excluded: vec![num(1.0)],
        },
    )];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 0);
    // An empty exclusion list is not this shape.
    let mut leaves = vec![decl(
        "rest",
        20,
        Expr::RestObject {
            obj: bx(ident("o")),
            excluded: vec![],
        },
    )];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 0);
    // A missing sibling declare keeps the shape loud.
    let mut leaves = vec![decl(
        "rest",
        20,
        Expr::RestObject {
            obj: bx(ident("o")),
            excluded: vec![strlit("a")],
        },
    )];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 0);
    // A computed load with a non-literal key is no key load.
    let mut leaves = vec![
        decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![strlit("a")],
            },
        ),
        decl(
            "y",
            22,
            Expr::PropDyn {
                object: bx(ident("o")),
                key: bx(ident("k")),
            },
        ),
    ];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 0);
    // The load's object must be the rest source (structurally).
    let mut leaves = vec![
        decl(
            "rest",
            20,
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![strlit("a")],
            },
        ),
        decl("y", 22, prop(ident("OTHER"), "a")),
    ];
    let mut stats = FoldStats::default();
    fold_rest_destructure(&mut leaves, &mut stats);
    assert_eq!(stats.rest, 0);
    // key_load_target directly: the catch-all arm.
    assert_eq!(key_load_target(&call0(ident("f")), &ident("o")), None);
    assert_eq!(
        key_load_target(&prop(ident("o"), "k"), &ident("o")),
        Some(&"k".to_string())
    );
}

// ── d-P11: the generator driver fold ───────────────────────────
