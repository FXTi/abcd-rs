//! Fold AST/Stmt/Leaf/SNode walker, flow, jump, and sweep unit tests.

use super::*;

// ── name/expr walkers: every statement & expression kind ───────

/// Statements carrying one temp `x`/42 in each expression position.
fn stmts_with_x() -> Vec<Stmt> {
    let x = || tm("x", 42);
    vec![
        Stmt::Declare {
            name: "d".to_string(),
            mutable: false,
            value: x(),
            value_id: ValueId::new(1),
        },
        Stmt::PhiAssign {
            target: "p".to_string(),
            value: x(),
            to: BlockId::new(3),
            exceptional: false,
        },
        Stmt::Expr(x()),
        Stmt::Throw(x()),
        Stmt::Return(Some(x())),
        Stmt::StoreProp {
            object: x(),
            name: "k".to_string(),
            dot_legal: true,
            value: ident("y"),
            own: false,
        },
        Stmt::StoreIndex {
            object: ident("y"),
            index: x(),
            value: ident("y"),
            own: false,
        },
        Stmt::StoreDyn {
            object: ident("y"),
            key: ident("y"),
            value: x(),
            own: false,
        },
        Stmt::DefineMethod {
            object: x(),
            name: "m".to_string(),
            func: ident("f"),
            length: 0,
        },
        Stmt::StorePrivate {
            object: ident("y"),
            name: "p".to_string(),
            value: x(),
            define: false,
        },
        Stmt::StoreSuper {
            name: None,
            key: Some(x()),
            value: ident("y"),
        },
        Stmt::StoreSuper {
            name: Some("k".to_string()),
            key: None,
            value: x(),
        },
        Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: "l".to_string(),
            value: x(),
        },
        Stmt::GlobalStore {
            name: "g".to_string(),
            value: x(),
            tolerant: false,
        },
        Stmt::ModuleStore {
            index: 0,
            name: "m0".to_string(),
            value: x(),
        },
        Stmt::CondBranch {
            cond: x(),
            true_dest: BlockId::new(1),
            false_dest: BlockId::new(2),
        },
    ]
}

#[test]
fn name_use_walkers_cover_every_statement_kind() {
    for s in stmts_with_x() {
        assert!(stmt_uses_name(&s, "x"), "{s:?}");
        assert!(!stmt_uses_name(&s, "absent"), "{s:?}");
    }
    // Binding-position name matches.
    assert!(stmt_uses_name(
        &Stmt::Declare {
            name: "x".to_string(),
            mutable: true,
            value: ident("y"),
            value_id: ValueId::new(1),
        },
        "x"
    ));
    assert!(stmt_uses_name(
        &Stmt::PhiDecl {
            name: "x".to_string(),
            value_id: ValueId::new(1),
        },
        "x"
    ));
    assert!(stmt_uses_name(
        &Stmt::PhiAssign {
            target: "x".to_string(),
            value: ident("y"),
            to: BlockId::new(3),
            exceptional: false,
        },
        "x"
    ));
    assert!(stmt_uses_name(
        &Stmt::LexStore {
            level: 0,
            slot: 0,
            own: true,
            name: "x".to_string(),
            value: ident("y"),
        },
        "x"
    ));
    // The catch-all arm: statements without expression positions.
    for s in [
        Stmt::Return(None),
        Stmt::ScopePop,
        Stmt::Unreachable,
        Stmt::Debugger,
        Stmt::Branch {
            dest: BlockId::new(0),
        },
        Stmt::CatchBind {
            name: "x".to_string(),
        },
    ] {
        assert!(!stmt_uses_name(&s, "x"), "{s:?}");
    }
    // Leaf-level dispatch arms.
    assert!(leaf_uses_name(
        &Leaf::Destructure {
            obj: tm("x", 42),
            keys: vec![("k".to_string(), "t".to_string())],
            rest: "r".to_string(),
        },
        "x"
    ));
    assert!(!leaf_uses_name(
        &Leaf::Destructure {
            obj: ident("y"),
            keys: vec![],
            rest: "x".to_string(),
        },
        "x"
    ));
    assert!(leaf_uses_name(
        &Leaf::Decl {
            name: "d".to_string(),
            mutable: true,
            value: Some(tm("x", 42)),
        },
        "x"
    ));
    assert!(!leaf_uses_name(
        &Leaf::Decl {
            name: "d".to_string(),
            mutable: true,
            value: None,
        },
        "x"
    ));
    assert!(leaf_uses_name(
        &Leaf::Assign {
            target: "x".to_string(),
            value: ident("y"),
        },
        "x"
    ));
    assert!(leaf_uses_name(
        &Leaf::Assign {
            target: "z".to_string(),
            value: tm("x", 42),
        },
        "x"
    ));
    assert!(leaves_use_name(
        &[Leaf::Assign {
            target: "z".to_string(),
            value: tm("x", 42),
        }],
        "x"
    ));
    // temp_name / temp_value / expr_uses_value primitives.
    assert_eq!(temp_name(&tm("x", 42)), Some("x"));
    assert_eq!(temp_name(&ident("x")), Some("x"));
    assert_eq!(temp_name(&num(1.0)), None);
    assert_eq!(temp_value(&tm("x", 42)), Some(ValueId::new(42)));
    assert_eq!(temp_value(&ident("x")), None);
    assert!(expr_uses_value(&call0(tm("x", 42)), ValueId::new(42)));
    assert!(!expr_uses_value(&call0(tm("x", 42)), ValueId::new(7)));
    assert!(expr_uses_name(&call0(ident("x")), "x"));
    assert!(!expr_uses_name(&num(1.0), "x"));
}

/// One specimen per `Expr` variant, with its direct-child count.
fn all_exprs() -> Vec<(Expr, usize)> {
    vec![
        (Expr::Lit(Lit::Null), 0),
        (ident("a"), 0),
        (tm("t", 1), 0),
        (prop(ident("o"), "n"), 1),
        (
            Expr::PropIndex {
                object: bx(ident("o")),
                index: bx(num(0.0)),
            },
            2,
        ),
        (
            Expr::PropDyn {
                object: bx(ident("o")),
                key: bx(ident("k")),
            },
            2,
        ),
        (
            Expr::PrivateLoad {
                object: bx(ident("o")),
                name: "p".to_string(),
            },
            1,
        ),
        (
            Expr::PrivateTest {
                object: bx(ident("o")),
                name: "p".to_string(),
            },
            1,
        ),
        (
            Expr::SuperProp {
                name: Some("n".to_string()),
                key: None,
            },
            0,
        ),
        (
            Expr::SuperProp {
                name: None,
                key: Some(bx(ident("k"))),
            },
            1,
        ),
        (
            Expr::Call {
                callee: bx(ident("f")),
                this: Some(bx(ident("t"))),
                args: vec![ident("a")],
                kind: CallKind::Direct,
            },
            3,
        ),
        (call0(ident("f")), 1),
        (Expr::SuperMarker, 0),
        (
            Expr::DynamicImport {
                specifier: bx(strlit("m")),
            },
            1,
        ),
        (
            Expr::Unary {
                op: UnOp::LogicalNot,
                operand: bx(ident("a")),
            },
            1,
        ),
        (
            Expr::Delete {
                target: bx(ident("a")),
            },
            1,
        ),
        (
            Expr::Binary {
                op: BinOp::Add,
                left: bx(ident("a")),
                right: bx(num(1.0)),
            },
            2,
        ),
        (cmp(CmpOp::Eq, ident("a"), ident("b")), 2),
        (
            Expr::RegExp {
                pattern: "x".to_string(),
                flags: "g".to_string(),
            },
            0,
        ),
        (Expr::ObjectLit { entries: vec![] }, 0),
        (Expr::ArrayLit { elements: vec![] }, 0),
        (
            Expr::Closure {
                body: FuncId::new(0),
                name: "f".to_string(),
                kind: FunctionKind::Function,
                captures: vec![("c".to_string(), ident("cap"))],
            },
            1,
        ),
        (
            Expr::Class {
                ctor: FuncId::new(0),
                name: "C".to_string(),
                heritage: Some(bx(ident("B"))),
                members: ConstId::new(0),
                member_attrs: vec![],
                sendable: false,
            },
            1,
        ),
        (
            Expr::Class {
                ctor: FuncId::new(0),
                name: "C".to_string(),
                heritage: None,
                members: ConstId::new(0),
                member_attrs: vec![],
                sendable: false,
            },
            0,
        ),
        (
            Expr::Yield {
                value: bx(ident("v")),
            },
            1,
        ),
        (
            Expr::YieldStar {
                value: bx(ident("v")),
            },
            1,
        ),
        (
            Expr::Await {
                value: bx(ident("v")),
                uncaught: false,
            },
            1,
        ),
        (Expr::NewTarget, 0),
        (Expr::GlobalThis, 0),
        (Expr::SelfFunction("f".to_string()), 0),
        (Expr::Arguments, 0),
        (Expr::RestArgs { start_index: 0 }, 0),
        (
            Expr::TemplateObject {
                raw: None,
                cooked: None,
            },
            0,
        ),
        (
            Expr::IterResultObj {
                value: bx(ident("v")),
                done: bx(boolean(false)),
            },
            2,
        ),
        (
            Expr::Iter {
                op: IterOp::GetIterator,
                obj: bx(ident("o")),
                status: NodeStatus::Plumbing,
            },
            1,
        ),
        (
            Expr::CreateGenerator {
                func: bx(ident("f")),
            },
            1,
        ),
        (
            Expr::GeneratorDriver {
                resume: true,
                genobj: bx(ident("g")),
            },
            1,
        ),
        (
            Expr::AsyncDriver {
                resolve: true,
                value: bx(ident("v")),
            },
            1,
        ),
        (
            Expr::CopyDataProps {
                dst: bx(ident("d")),
                src: bx(ident("s")),
            },
            2,
        ),
        (
            Expr::SetObjectWithProto {
                obj: bx(ident("o")),
                proto: bx(ident("p")),
            },
            2,
        ),
        (
            Expr::ArraySpread {
                dst: bx(ident("d")),
                index: bx(num(0.0)),
                src: bx(ident("s")),
            },
            3,
        ),
        (
            Expr::RestObject {
                obj: bx(ident("o")),
                excluded: vec![strlit("k")],
            },
            2,
        ),
        (
            Expr::DefineGetterSetter {
                obj: bx(ident("o")),
                key: bx(strlit("k")),
                getter: bx(ident("g")),
                setter: bx(ident("s")),
            },
            4,
        ),
        (Expr::ModuleNamespace { index: 0 }, 0),
        (
            Expr::ObjectBuild {
                entries: vec![
                    ObjEntry::KeyValue(Lit::String("a".to_string()), ident("v1")),
                    ObjEntry::Computed(ident("k"), ident("v2")),
                    ObjEntry::Spread(ident("s")),
                    ObjEntry::Proto(ident("p")),
                    ObjEntry::Method("m".to_string(), ident("f")),
                    ObjEntry::Getter(ObjKey::Computed(bx(ident("gk"))), ident("gf")),
                    ObjEntry::Setter(ObjKey::Name("sn".to_string()), ident("sf")),
                ],
            },
            9,
        ),
        (
            Expr::ArrayBuild {
                elements: vec![ArrayElem::Item(ident("i")), ArrayElem::Spread(ident("s"))],
            },
            2,
        ),
        (
            Expr::Fallback {
                op: "op",
                note: "n",
                operands: vec![ident("o")],
            },
            1,
        ),
    ]
}

#[test]
fn expr_children_tables_cover_every_expr_kind() {
    for (e, want) in all_exprs() {
        assert_eq!(expr_children(&e).len(), want, "{e:?}");
    }
    for (mut e, want) in all_exprs() {
        {
            let kids = expr_children_mut(&mut e);
            assert_eq!(kids.len(), want, "{e:?}");
            for k in kids {
                *k = Expr::Lit(Lit::Null);
            }
        }
        // Every enumerated child was mutable in place.
        assert_eq!(
            expr_children(&e)
                .iter()
                .filter(|c| matches!(c, Expr::Lit(Lit::Null)))
                .count(),
            want,
            "{e:?}"
        );
    }
}

/// One specimen per leaf/statement kind, with its expression count.
fn all_leaves() -> Vec<(Leaf, usize)> {
    vec![
        (decl("d", 1, ident("v")), 1),
        (phi_assign("p", ident("v")), 1),
        (expr_stmt(ident("e")), 1),
        (
            Leaf::Raw(Stmt::StoreProp {
                object: ident("o"),
                name: "n".to_string(),
                dot_legal: true,
                value: ident("v"),
                own: false,
            }),
            2,
        ),
        (
            Leaf::Raw(Stmt::StoreIndex {
                object: ident("o"),
                index: num(0.0),
                value: ident("v"),
                own: false,
            }),
            3,
        ),
        (
            Leaf::Raw(Stmt::StoreDyn {
                object: ident("o"),
                key: ident("k"),
                value: ident("v"),
                own: false,
            }),
            3,
        ),
        (
            Leaf::Raw(Stmt::DefineMethod {
                object: ident("o"),
                name: "m".to_string(),
                func: ident("f"),
                length: 0,
            }),
            2,
        ),
        (
            Leaf::Raw(Stmt::StorePrivate {
                object: ident("o"),
                name: "p".to_string(),
                value: ident("v"),
                define: false,
            }),
            2,
        ),
        (
            Leaf::Raw(Stmt::StoreSuper {
                name: None,
                key: Some(ident("k")),
                value: ident("v"),
            }),
            2,
        ),
        (
            Leaf::Raw(Stmt::StoreSuper {
                name: Some("n".to_string()),
                key: None,
                value: ident("v"),
            }),
            1,
        ),
        (
            Leaf::Raw(Stmt::LexStore {
                level: 0,
                slot: 0,
                own: true,
                name: "l".to_string(),
                value: ident("v"),
            }),
            1,
        ),
        (
            Leaf::Raw(Stmt::GlobalStore {
                name: "g".to_string(),
                value: ident("v"),
                tolerant: false,
            }),
            1,
        ),
        (
            Leaf::Raw(Stmt::ModuleStore {
                index: 0,
                name: "m".to_string(),
                value: ident("v"),
            }),
            1,
        ),
        (Leaf::Raw(Stmt::Throw(ident("e"))), 1),
        (Leaf::Raw(Stmt::Return(Some(ident("v")))), 1),
        (
            Leaf::Raw(Stmt::CondBranch {
                cond: ident("c"),
                true_dest: BlockId::new(1),
                false_dest: BlockId::new(2),
            }),
            1,
        ),
        (phi_decl("p", 1), 0),
        (Leaf::Raw(Stmt::Return(None)), 0),
        (Leaf::Raw(Stmt::ScopePop), 0),
        (
            Leaf::Destructure {
                obj: ident("o"),
                keys: vec![],
                rest: "r".to_string(),
            },
            1,
        ),
        (
            Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: Some(ident("v")),
            },
            1,
        ),
        (
            Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: None,
            },
            0,
        ),
        (
            Leaf::Assign {
                target: "a".to_string(),
                value: ident("v"),
            },
            1,
        ),
    ]
}

#[test]
fn leaf_expr_tables_cover_every_leaf_kind() {
    for (l, want) in all_leaves() {
        assert_eq!(leaf_exprs(&l).len(), want, "{l:?}");
        if let Leaf::Raw(s) = &l {
            assert_eq!(stmt_exprs_of(s).len(), want, "{s:?}");
        }
    }
}

#[test]
fn subst_temp_covers_every_leaf_and_node_kind() {
    let repl = ident("replacement");
    // Every leaf kind with an expression position routes through.
    for (l, _) in all_leaves() {
        let mut l = l;
        subst_temp_in_leaf(&mut l, ValueId::new(9), &repl);
        let _ = l;
    }
    // The substitution actually rewrites each position.
    let cases: Vec<Leaf> = stmts_with_x()
        .into_iter()
        .map(Leaf::Raw)
        .chain([
            Leaf::Destructure {
                obj: tm("x", 42),
                keys: vec![],
                rest: "r".to_string(),
            },
            Leaf::Decl {
                name: "d".to_string(),
                mutable: true,
                value: Some(tm("x", 42)),
            },
            Leaf::Assign {
                target: "a".to_string(),
                value: tm("x", 42),
            },
        ])
        .collect();
    for mut l in cases {
        subst_temp_in_leaf(&mut l, ValueId::new(42), &repl);
        assert!(
            !leaf_exprs(&l)
                .iter()
                .any(|e| expr_uses_value(e, ValueId::new(42))),
            "{l:?}"
        );
    }
    // No-op arms: binding-only leaves stay untouched.
    let untouched = [
        phi_decl("p", 42),
        Leaf::Raw(Stmt::CatchBind {
            name: "x".to_string(),
        }),
        Leaf::Raw(Stmt::Return(None)),
        Leaf::Raw(Stmt::ScopePop),
        Leaf::Decl {
            name: "d".to_string(),
            mutable: true,
            value: None,
        },
    ];
    for l in untouched {
        let mut m = l.clone();
        subst_temp_in_leaf(&mut m, ValueId::new(42), &repl);
        assert_eq!(m, l);
    }
    // Every node kind routes the substitution through.
    let tree = vec![
        run(vec![decl("d", 1, tm("v", 42))]),
        if_node(tm("v", 42), vec![], vec![]),
        SNode::While {
            label: None,
            cond: Some(tm("v", 42)),
            body: vec![],
        },
        SNode::DoWhile {
            label: None,
            body: vec![],
            cond: tm("v", 42),
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: vec![run(vec![expr_stmt(tm("v", 42))])],
        },
        SNode::Try {
            body: vec![run(vec![expr_stmt(tm("v", 42))])],
            catches: vec![catch("e", vec![run(vec![expr_stmt(tm("v", 42))])])],
            note: None,
            finally: Some(vec![run(vec![expr_stmt(tm("v", 42))])]),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: tm("v", 42),
            body: vec![],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: tm("v", 42),
            body: vec![],
        },
        SNode::Switch {
            disc: tm("v", 42),
            cases: vec![SwitchCase {
                tests: vec![tm("v", 42)],
                body: vec![run(vec![expr_stmt(tm("v", 42))])],
            }],
        },
        SNode::Break { label: None },
        SNode::Continue { label: None },
        SNode::Honest("h".to_string()),
    ];
    let mut t = tree.clone();
    subst_temp_in_nodes(&mut t, ValueId::new(42), &repl);
    assert!(!nodes_use_temp(&t, ValueId::new(42)));
    // The control-transfer nodes are untouched.
    assert_eq!(t[9], tree[9]);
    assert_eq!(t[10], tree[10]);
    assert_eq!(t[11], tree[11]);
}

/// A tree carrying the temp `v`/77 in every node-kind position.
fn rich_tree() -> Vec<SNode> {
    vec![
        run(vec![decl("d", 1, tm("v", 77))]),
        if_node(
            tm("v", 77),
            vec![run(vec![expr_stmt(ident("a"))])],
            vec![run(vec![expr_stmt(tm("v", 77))])],
        ),
        SNode::While {
            label: None,
            cond: Some(tm("v", 77)),
            body: vec![run(vec![expr_stmt(ident("a"))])],
        },
        SNode::DoWhile {
            label: None,
            body: vec![run(vec![expr_stmt(ident("a"))])],
            cond: tm("v", 77),
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: vec![run(vec![expr_stmt(tm("v", 77))])],
        },
        SNode::Try {
            body: vec![run(vec![expr_stmt(ident("b"))])],
            catches: vec![catch("e", vec![run(vec![expr_stmt(tm("v", 77))])])],
            note: None,
            finally: Some(vec![run(vec![expr_stmt(tm("v", 77))])]),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: tm("v", 77),
            body: vec![],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: tm("v", 77),
            body: vec![],
        },
        SNode::Switch {
            disc: tm("v", 77),
            cases: vec![SwitchCase {
                tests: vec![tm("v", 77)],
                body: vec![run(vec![expr_stmt(tm("v", 77))])],
            }],
        },
        SNode::Break { label: None },
        SNode::Continue { label: None },
        SNode::Honest("h".to_string()),
    ]
}

#[test]
fn node_use_walkers_cover_every_node_kind() {
    let names: Vec<String> = vec!["v".to_string()];
    let tree = rich_tree();
    // Every kind mentions the temp; a fresh tree does not.
    assert!(nodes_use_any(&tree, &names));
    assert!(nodes_use_temp(&tree, ValueId::new(77)));
    let clean = vec![
        run(vec![decl("d", 1, ident("d0"))]),
        if_node(ident("c"), vec![], vec![]),
        SNode::While {
            label: None,
            cond: Some(ident("c")),
            body: vec![],
        },
        SNode::DoWhile {
            label: None,
            body: vec![],
            cond: ident("c"),
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: vec![],
        },
        SNode::Try {
            body: vec![],
            catches: vec![],
            note: None,
            finally: None,
        },
        SNode::ForOf {
            is_await: true,
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
        SNode::Break { label: None },
        SNode::Continue { label: None },
        SNode::Honest("h".to_string()),
    ];
    assert!(!nodes_use_any(&clean, &names));
    assert!(!nodes_use_temp(&clean, ValueId::new(77)));
    // Node-level dispatch: each kind answers through node_uses_any.
    for n in &tree[..9] {
        assert!(node_uses_any(n, &names), "{n:?}");
    }
    for n in &clean {
        assert!(!node_uses_any(n, &names), "{n:?}");
    }
    // walk_leaves visits every leaf exactly once.
    let mut seen = 0usize;
    walk_leaves(&tree, &mut |_| seen += 1);
    assert_eq!(seen, 10);
    // nodes_declare_or_assign: binding sites by name.
    assert!(nodes_declare_or_assign(
        &[run(vec![phi_assign("q", ident("z"))])],
        "q"
    ));
    assert!(nodes_declare_or_assign(
        &[run(vec![Leaf::Decl {
            name: "q".to_string(),
            mutable: true,
            value: None,
        }])],
        "q"
    ));
    assert!(nodes_declare_or_assign(
        &[run(vec![Leaf::Assign {
            target: "q".to_string(),
            value: ident("z"),
        }])],
        "q"
    ));
    assert!(!nodes_declare_or_assign(
        &[run(vec![expr_stmt(tm("q", 5))])],
        "q"
    ));
    assert!(!nodes_declare_or_assign(
        &[SNode::Honest("h".to_string())],
        "q"
    ));
}

#[test]
fn flow_analysis_covers_every_node_kind() {
    let throw_run = || run(vec![Leaf::Raw(Stmt::Throw(ident("e")))]);
    let plain_run = || run(vec![expr_stmt(ident("a"))]);
    // Statement runs.
    assert!(node_flow(&throw_run()).diverges);
    assert!(node_flow(&run(vec![Leaf::Raw(Stmt::Return(None))])).diverges);
    assert!(node_flow(&run(vec![Leaf::Raw(Stmt::Unreachable)])).diverges);
    let f = node_flow(&plain_run());
    assert!(!f.diverges && !f.live_break);
    let f = node_flow(&run(vec![
        expr_stmt(ident("a")),
        Leaf::Raw(Stmt::Unreachable),
    ]));
    assert!(!f.diverges, "mixed run falls through");
    // Exits.
    let f = node_flow(&SNode::Break { label: None });
    assert!(f.live_break && f.diverges);
    let f = node_flow(&SNode::Continue { label: None });
    assert!(!f.live_break && f.diverges);
    let f = node_flow(&SNode::Honest("h".to_string()));
    assert!(!f.live_break && !f.diverges);
    // If: diverges only when both non-empty arms diverge.
    let f = node_flow(&if_node(ident("c"), vec![throw_run()], vec![throw_run()]));
    assert!(f.diverges && !f.live_break);
    let f = node_flow(&if_node(ident("c"), vec![throw_run()], vec![]));
    assert!(!f.diverges);
    let f = node_flow(&if_node(
        ident("c"),
        vec![SNode::Break { label: None }],
        vec![plain_run()],
    ));
    assert!(f.live_break && !f.diverges);
    // while (true) with no live break diverges; a live break completes it.
    let f = node_flow(&SNode::While {
        label: None,
        cond: None,
        body: vec![plain_run()],
    });
    assert!(f.diverges && !f.live_break);
    let f = node_flow(&SNode::While {
        label: None,
        cond: None,
        body: vec![SNode::Break { label: None }],
    });
    assert!(!f.diverges && !f.live_break);
    // Conditional loops / for-of / for-in / switch may complete.
    for n in [
        SNode::While {
            label: None,
            cond: Some(ident("c")),
            body: vec![SNode::Break { label: None }],
        },
        SNode::DoWhile {
            label: None,
            body: vec![SNode::Break { label: None }],
            cond: ident("c"),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: vec![SNode::Break { label: None }],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: vec![SNode::Break { label: None }],
        },
        SNode::Switch {
            disc: ident("d"),
            cases: vec![SwitchCase {
                tests: vec![],
                body: vec![SNode::Break { label: None }],
            }],
        },
    ] {
        let f = node_flow(&n);
        assert!(!f.live_break && !f.diverges, "{n:?}");
    }
    // A labeled block is transparent to its body's flow.
    let f = node_flow(&SNode::Labeled {
        label: "l".to_string(),
        body: vec![SNode::Break { label: None }],
    });
    assert!(f.live_break && f.diverges);
    // Try: breaks in body/catch/finally are live; never diverges.
    let f = node_flow(&SNode::Try {
        body: vec![SNode::Break { label: None }],
        catches: vec![],
        note: None,
        finally: None,
    });
    assert!(f.live_break && !f.diverges);
    let f = node_flow(&SNode::Try {
        body: vec![throw_run()],
        catches: vec![catch("e", vec![SNode::Break { label: None }])],
        note: None,
        finally: Some(vec![plain_run()]),
    });
    assert!(f.live_break && !f.diverges);
    // Sequence flow: nodes after a diverging node are dead.
    let f = seq_flow(&[throw_run(), SNode::Break { label: None }]);
    assert!(!f.live_break && f.diverges);
    let f = seq_flow(&[plain_run(), SNode::Break { label: None }]);
    assert!(f.live_break && f.diverges);
    let f = seq_flow(&[]);
    assert!(!f.live_break && !f.diverges);
}

#[test]
fn subtree_jump_scans_cover_every_node_kind() {
    // subtree_has_continue: any continue, except inside nested loops.
    assert!(subtree_has_continue(&[SNode::Continue { label: None }]));
    assert!(subtree_has_continue(&[if_node(
        ident("c"),
        vec![],
        vec![SNode::Continue { label: None }],
    )]));
    assert!(subtree_has_continue(&[SNode::Labeled {
        label: "l".to_string(),
        body: vec![SNode::Continue { label: None }],
    }]));
    assert!(subtree_has_continue(&[SNode::Try {
        body: vec![],
        catches: vec![catch("e", vec![SNode::Continue { label: None }])],
        note: None,
        finally: None,
    }]));
    assert!(subtree_has_continue(&[SNode::Try {
        body: vec![],
        catches: vec![],
        note: None,
        finally: Some(vec![SNode::Continue { label: None }]),
    }]));
    assert!(subtree_has_continue(&[SNode::Switch {
        disc: ident("d"),
        cases: vec![SwitchCase {
            tests: vec![],
            body: vec![SNode::Continue { label: None }],
        }],
    }]));
    for n in [
        SNode::While {
            label: None,
            cond: None,
            body: vec![SNode::Continue { label: None }],
        },
        SNode::DoWhile {
            label: None,
            body: vec![SNode::Continue { label: None }],
            cond: ident("c"),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: vec![SNode::Continue { label: None }],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: vec![SNode::Continue { label: None }],
        },
    ] {
        let msg = format!("{n:?}");
        assert!(!subtree_has_continue(&[n]), "{msg}");
    }
    assert!(!subtree_has_continue(&[
        run(vec![]),
        SNode::Break { label: None },
        SNode::Honest("h".to_string()),
    ]));
    // subtree_has_labeled_jump: labeled exits anywhere.
    assert!(subtree_has_labeled_jump(&[SNode::Break {
        label: Some("l".to_string()),
    }]));
    assert!(subtree_has_labeled_jump(&[SNode::Continue {
        label: Some("l".to_string()),
    }]));
    assert!(subtree_has_labeled_jump(&[if_node(
        ident("c"),
        vec![SNode::Break {
            label: Some("l".to_string()),
        }],
        vec![],
    )]));
    for n in [
        SNode::While {
            label: None,
            cond: None,
            body: vec![SNode::Break {
                label: Some("l".to_string()),
            }],
        },
        SNode::DoWhile {
            label: None,
            body: vec![SNode::Break {
                label: Some("l".to_string()),
            }],
            cond: ident("c"),
        },
        SNode::Labeled {
            label: "m".to_string(),
            body: vec![SNode::Break {
                label: Some("l".to_string()),
            }],
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: vec![SNode::Break {
                label: Some("l".to_string()),
            }],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: vec![SNode::Break {
                label: Some("l".to_string()),
            }],
        },
        SNode::Try {
            body: vec![],
            catches: vec![catch(
                "e",
                vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            )],
            note: None,
            finally: None,
        },
        SNode::Try {
            body: vec![],
            catches: vec![],
            note: None,
            finally: Some(vec![SNode::Break {
                label: Some("l".to_string()),
            }]),
        },
        SNode::Switch {
            disc: ident("d"),
            cases: vec![SwitchCase {
                tests: vec![],
                body: vec![SNode::Break {
                    label: Some("l".to_string()),
                }],
            }],
        },
    ] {
        let msg = format!("{n:?}");
        assert!(subtree_has_labeled_jump(&[n]), "{msg}");
    }
    assert!(!subtree_has_labeled_jump(&[
        run(vec![]),
        SNode::Break { label: None },
        SNode::Continue { label: None },
        SNode::Honest("h".to_string()),
    ]));
}

#[test]
fn cleanup_walker_and_alias_collection() {
    // A cleanup-shaped handler: the alias declares and the rethrow
    // are siblings at the handler's top level (walk_cleanup
    // re-collects aliases per recursion level), with the return
    // load and benign nested structures alongside.
    let good = vec![catch(
        "e",
        vec![
            run(vec![
                decl("a", 50, tm("e", 49)),   // alias of the binding
                phi_assign("b", tm("a", 50)), // transitive alias
                decl(
                    "r",
                    51,
                    Expr::PropDyn {
                        object: bx(tm("it", 52)),
                        key: bx(strlit("return")),
                    },
                ),
                Leaf::Raw(Stmt::Throw(tm("b", 53))),
            ]),
            if_node(ident("c"), vec![run(vec![expr_stmt(ident("x"))])], vec![]),
            SNode::While {
                label: None,
                cond: Some(ident("w")),
                body: vec![run(vec![expr_stmt(ident("y"))])],
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![run(vec![expr_stmt(ident("z"))])],
            },
            try_node(vec![run(vec![expr_stmt(ident("w"))])], vec![]),
        ],
    )];
    assert!(cleanup_handlers_ok(&good));
    // expr_has_return_load forms.
    assert!(expr_has_return_load(&prop(ident("o"), "return")));
    assert!(expr_has_return_load(&Expr::PropIndex {
        object: bx(ident("o")),
        index: bx(strlit("return")),
    }));
    assert!(expr_has_return_load(&call1(
        ident("f"),
        prop(ident("o"), "return")
    )));
    assert!(!expr_has_return_load(&prop(ident("o"), "other")));
    assert!(!expr_has_return_load(&ident("return")));
    // A handler without the return load.
    assert!(!cleanup_handlers_ok(&[catch(
        "e",
        vec![run(vec![Leaf::Raw(Stmt::Throw(tm("e", 49)))])],
    )]));
    // A handler with a foreign throw / a side-effecting store is bad.
    assert!(!cleanup_handlers_ok(&[catch(
        "e",
        vec![
            run(vec![decl("r", 51, prop(tm("it", 52), "return"))]),
            run(vec![Leaf::Raw(Stmt::Throw(ident("other")))]),
        ],
    )]));
    assert!(!cleanup_handlers_ok(&[catch(
        "e",
        vec![
            run(vec![
                decl("r", 51, prop(tm("it", 52), "return")),
                Leaf::Raw(Stmt::StoreProp {
                    object: ident("o"),
                    name: "p".to_string(),
                    dot_legal: true,
                    value: ident("v"),
                    own: false,
                },)
            ]),
            run(vec![Leaf::Raw(Stmt::Throw(tm("e", 49)))]),
        ],
    )]));
    // No catch at all.
    assert!(!cleanup_handlers_ok(&[]));
}

#[test]
fn absorb_expr_pairs_enumerate_every_variant() {
    let cases: Vec<(Absorb, usize)> = vec![
        (Absorb::ObjKV(Lit::String("k".to_string()), ident("v")), 1),
        (Absorb::ObjComputed(ident("k"), ident("v")), 2),
        (Absorb::ObjSpread(ident("s")), 1),
        (Absorb::ObjProto(ident("p")), 1),
        (Absorb::ObjMethod("m".to_string(), ident("f")), 1),
        (
            Absorb::ObjAccessors {
                key: ident("k"),
                getter: Some(ident("g")),
                setter: Some(ident("s")),
            },
            3,
        ),
        (
            Absorb::ObjAccessors {
                key: ident("k"),
                getter: None,
                setter: None,
            },
            1,
        ),
        (Absorb::ArrItem(ident("v")), 1),
        (Absorb::ArrSpread(ident("s")), 1),
    ];
    for (a, want) in cases {
        assert_eq!(absorb_exprs(&a).len(), want);
        let mut a = a;
        assert_eq!(absorb_exprs_mut(&mut a).len(), want);
    }
    // expr_count_value counts occurrences transitively.
    let e = call1(ident("f"), tm("x", 42));
    assert_eq!(expr_count_value(&e, ValueId::new(42)), 1);
    assert_eq!(expr_count_value(&tm("x", 42), ValueId::new(42)), 1);
    assert_eq!(expr_count_value(&call0(tm("x", 42)), ValueId::new(1)), 0);
}

#[test]
fn sweep_walkers_recurse_into_every_region() {
    // Drive the strip/sweep walkers over a fully nested tree.
    let nested = |leaf: Leaf| -> Vec<SNode> {
        vec![
            if_node(ident("c"), vec![run(vec![leaf.clone()])], vec![]),
            SNode::While {
                label: None,
                cond: None,
                body: vec![run(vec![leaf.clone()])],
            },
            SNode::DoWhile {
                label: None,
                body: vec![run(vec![leaf.clone()])],
                cond: ident("d"),
            },
            SNode::Labeled {
                label: "l".to_string(),
                body: vec![run(vec![leaf.clone()])],
            },
            SNode::Try {
                body: vec![run(vec![leaf.clone()])],
                catches: vec![catch("e", vec![run(vec![leaf.clone()])])],
                note: None,
                finally: Some(vec![run(vec![leaf.clone()])]),
            },
            SNode::Switch {
                disc: ident("s"),
                cases: vec![SwitchCase {
                    tests: vec![],
                    body: vec![run(vec![leaf.clone()])],
                }],
            },
            SNode::ForOf {
                is_await: false,
                binding: "k".to_string(),
                iter: ident("i"),
                body: vec![run(vec![leaf.clone()])],
            },
            SNode::ForIn {
                binding: "k".to_string(),
                obj: ident("o"),
                body: vec![run(vec![leaf.clone()])],
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
        ]
    };
    // sweep_dead_decls: the dead declare disappears everywhere.
    let mut nodes = nested(decl("dead", 42, ident("v")));
    sweep_dead_decls(&mut nodes, &[ValueId::new(42)].into_iter().collect());
    assert!(!nodes_use_temp(&nodes, ValueId::new(42)));
    let mut found = false;
    walk_leaves(&nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::Declare { name, .. }) if name == "dead") {
            found = true;
        }
    });
    assert!(!found);
    // strip_genobj_phi_assigns: target-name + alias-value pairs go.
    let mut nodes = nested(phi_assign("victim", tm("g", 10)));
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    strip_genobj_phi_assigns(
        &mut nodes,
        &aliases,
        &["victim".to_string()].into_iter().collect(),
    );
    let mut found = false;
    walk_leaves(&nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "victim") {
            found = true;
        }
    });
    assert!(!found);
    // strip_dead_phi_decls: only decls with no remaining assigns
    // and no reads.
    let mut nodes = nested(phi_decl("victim", 42));
    strip_dead_phi_decls(
        &mut nodes,
        &["victim".to_string()].into_iter().collect(),
        &BTreeSet::new(),
        &BTreeMap::new(),
    );
    let mut found = false;
    walk_leaves(&nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::PhiDecl { name, .. }) if name == "victim") {
            found = true;
        }
    });
    assert!(!found);
    // … but a decl with surviving assigns stays.
    let mut nodes = nested(phi_decl("victim", 42));
    strip_dead_phi_decls(
        &mut nodes,
        &["victim".to_string()].into_iter().collect(),
        &["victim".to_string()].into_iter().collect(),
        &BTreeMap::new(),
    );
    let mut found = false;
    walk_leaves(&nodes, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::PhiDecl { name, .. }) if name == "victim") {
            found = true;
        }
    });
    assert!(found);
    // map_exprs_mut reaches every expression position incl. node
    // conditions, discriminants, and case tests.
    let mut nodes = vec![
        if_node(ident("a"), vec![], vec![]),
        SNode::While {
            label: None,
            cond: Some(ident("b")),
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
            iter: ident("d"),
            body: vec![],
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("e"),
            body: vec![],
        },
        SNode::Switch {
            disc: ident("f"),
            cases: vec![SwitchCase {
                tests: vec![ident("g")],
                body: vec![run(vec![expr_stmt(ident("h"))])],
            }],
        },
        run(vec![decl("i", 1, ident("j"))]),
    ];
    map_exprs_mut(&mut nodes, &mut |e| {
        if let Expr::Ident(n) = e {
            *n = format!("{n}_mapped");
        }
    });
    let names = ["a", "b", "c", "d", "e", "f", "g", "h", "j"];
    for n in names {
        assert!(
            nodes_use_any(&nodes, &[format!("{n}_mapped")]),
            "{n} not mapped"
        );
    }
}

#[test]
fn residual_walker_and_sweep_pins() {
    // nodes_declare_or_assign: the Declare/PhiDecl arms and the
    // early exit.
    assert!(nodes_declare_or_assign(
        &[
            run(vec![decl("q", 1, ident("v"))]),
            run(vec![decl("q", 1, ident("v"))]),
        ],
        "q"
    ));
    assert!(nodes_declare_or_assign(&[run(vec![phi_decl("q", 1)])], "q"));
    // walk_cleanup: the do-while recursion arm and the catch-all.
    let mut bad = false;
    let (mut rt, mut rl) = (false, false);
    walk_cleanup(
        &[
            SNode::DoWhile {
                label: None,
                body: vec![run(vec![decl("r", 51, prop(tm("it", 52), "return"))])],
                cond: ident("c"),
            },
            SNode::Break { label: None },
            SNode::Continue { label: None },
            SNode::Honest("h".to_string()),
            SNode::Switch {
                disc: ident("d"),
                cases: vec![],
            },
        ],
        "e",
        &mut rt,
        &mut rl,
        &mut bad,
    );
    assert!(rl && !rt && !bad);
    // collect_aliases: the do-while arm and the catch-all.
    let mut aliases = vec!["e".to_string()];
    let mut grew = true;
    while grew {
        grew = false;
        collect_aliases(
            &[
                SNode::DoWhile {
                    label: None,
                    body: vec![run(vec![decl("a", 50, tm("e", 49))])],
                    cond: ident("c"),
                },
                SNode::Break { label: None },
                SNode::Switch {
                    disc: ident("d"),
                    cases: vec![],
                },
            ],
            &mut aliases,
            &mut grew,
        );
    }
    assert!(aliases.contains(&"a".to_string()));
    // expr_has_return_load: a "return" load nested under a
    // non-matching PropDyn key.
    assert!(expr_has_return_load(&Expr::PropDyn {
        object: bx(prop(ident("o"), "return")),
        key: bx(strlit("other")),
    }));
    // residue_match: a non-run significant sibling bails.
    let nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![run(vec![decl(
                "a",
                50,
                Expr::Await {
                    value: bx(ident("p")),
                    uncaught: true,
                },
            )])],
        },
        SNode::Break { label: None },
    ];
    let mut nodes = nodes;
    let mut stats = FoldStats::default();
    sweep_dead_loop_exit_throws(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0);
    // sweep_async_machinery: non-alias phi values pass through;
    // alias-valued assigns into LIVE phis count as real uses; a
    // surviving foreign assign keeps the decl census honest.
    let mut nodes = vec![run(vec![
        phi_decl("pa", 20),
        phi_decl("live", 21),
        phi_assign("foreign", ident("z")),
        phi_assign("pa", tm("g", 10)),
        phi_assign("live", tm("g", 10)),
        expr_stmt(tm("live", 21)),
    ])];
    let aliases: BTreeSet<ValueId> = [ValueId::new(10)].into_iter().collect();
    sweep_async_machinery(&mut nodes, ValueId::new(10), &aliases, &BTreeSet::new());
    let SNode::Stmts(got) = &nodes[0] else {
        unreachable!()
    };
    // The foreign assign stays; the live phi's machinery assign
    // stays (it is a real use); the dead alias phi's decl stays
    // (its assign was stripped but the alias web is alive).
    assert!(
        got.iter()
            .any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "foreign"))
    );
    assert!(
        got.iter()
            .any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { target, .. }) if target == "live"))
    );
}

#[test]
fn map_exprs_mut_store_arms() {
    // The store-kind arms of the map walker (via rest_param_fold's
    // census walks).
    let mut nodes = vec![run(vec![
        Leaf::Raw(Stmt::StoreProp {
            object: ident("o"),
            name: "p".to_string(),
            dot_legal: true,
            value: ident("v"),
            own: false,
        }),
        Leaf::Raw(Stmt::StoreIndex {
            object: ident("o"),
            index: ident("i"),
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
            define: false,
        }),
        Leaf::Raw(Stmt::StoreSuper {
            name: None,
            key: Some(ident("k")),
            value: ident("v"),
        }),
        Leaf::Raw(Stmt::StoreSuper {
            name: Some("s".to_string()),
            key: None,
            value: ident("v"),
        }),
        Leaf::Raw(Stmt::CondBranch {
            cond: ident("c"),
            true_dest: BlockId::new(1),
            false_dest: BlockId::new(2),
        }),
        decl("args", 60, Expr::RestArgs { start_index: 0 }),
        expr_stmt(tm("temp", 61)),
    ])];
    let mut params = vec!["p2".to_string()];
    let mut stats = FoldStats::default();
    rest_param_fold(&mut nodes, &mut params, 0, &mut stats);
    assert_eq!(stats.rest_param, 1);
}

#[test]
fn strip_internal_phi_plumbing_recursion() {
    // Copy plumbing nested inside every region kind is stripped.
    let mut roots: BTreeMap<String, Expr> = BTreeMap::new();
    roots.insert("ip".to_string(), tm("ip", 60));
    let plumbing = || {
        vec![run(vec![
            phi_decl("cp", 40),
            phi_assign("cp", tm("ip", 60)),
            phi_assign("ip", tm("ip", 60)),
        ])]
    };
    let mut out = vec![
        if_node(ident("c"), plumbing(), plumbing()),
        SNode::While {
            label: None,
            cond: None,
            body: plumbing(),
        },
        SNode::DoWhile {
            label: None,
            body: plumbing(),
            cond: ident("d"),
        },
        SNode::Labeled {
            label: "l".to_string(),
            body: plumbing(),
        },
        SNode::ForOf {
            is_await: false,
            binding: "k".to_string(),
            iter: ident("i"),
            body: plumbing(),
        },
        SNode::ForIn {
            binding: "k".to_string(),
            obj: ident("o"),
            body: plumbing(),
        },
        SNode::Try {
            body: plumbing(),
            catches: vec![catch("e", plumbing())],
            note: None,
            finally: Some(plumbing()),
        },
        SNode::Switch {
            disc: ident("s"),
            cases: vec![SwitchCase {
                tests: vec![],
                body: plumbing(),
            }],
        },
        plumbing()[0].clone(),
        SNode::Honest("h".to_string()),
    ];
    elim_internal_copy_phis(&mut out, &roots);
    // Every copy phi and self-assign vanished, leaving empty
    // regions behind.
    let mut assigns = 0usize;
    walk_leaves(&out, &mut |l| {
        if matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })) {
            assigns += 1;
        }
        if matches!(l, Leaf::Raw(Stmt::PhiDecl { .. })) {
            assigns += 1;
        }
    });
    assert_eq!(assigns, 0, "{out:?}");
}
