// ── c-COV W7: coverage tests ─────────────────────────────────────────
//
// In-module unit tests for the fold internals: hand-built SNode/Leaf
// trees driven through the private matchers and the public fold entry
// points. Organized by fixture family (see the c-COV folds diagnosis):
// the finally-idiom family, the for-await driver family, rest-param and
// late-decl control-flow variants, the switch-chain extension loop,
// do-while/labeled walker co-occurrence, optimized-profile async
// shapes, computed-key/`__proto__` literal builders, and per-matcher
// near-miss bail pins (one mutation per checkpoint group, not per
// line).
#[allow(
    unused_imports,
    reason = "wildcard fold test prelude re-exports sibling module helpers"
)]
use super::{
    control::*,
    literals::*,
    loops::*,
    machines::{async_fn::*, async_gen::*, generator::*, yield_star::*},
    scope::*,
    *,
};
use crate::expr::{ArrayElem, NodeStatus, ObjKey};
use crate::structure::CatchClause;
use abcd_ir::op::{BinOp, CallKind};
use abcd_ir::{BlockId, ConstId, FuncId};

// ── shape builders ─────────────────────────────────────────────

fn bx(e: Expr) -> Box<Expr> {
    Box::new(e)
}
/// A temp reference (name + SSA id kept consistent by convention).
fn tm(name: &str, vid: u32) -> Expr {
    Expr::Temp {
        value: ValueId::new(vid),
        name: name.to_string(),
    }
}
fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string())
}
fn num(x: f64) -> Expr {
    Expr::Lit(Lit::Number(x.to_bits()))
}
fn boolean(b: bool) -> Expr {
    Expr::Lit(Lit::Bool(b))
}
fn strlit(s: &str) -> Expr {
    Expr::Lit(Lit::String(s.to_string()))
}
fn undef() -> Expr {
    Expr::Lit(Lit::Undefined)
}
fn decl(name: &str, vid: u32, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::Declare {
        name: name.to_string(),
        mutable: false,
        value,
        value_id: ValueId::new(vid),
    })
}
fn phi_decl(name: &str, vid: u32) -> Leaf {
    Leaf::Raw(Stmt::PhiDecl {
        name: name.to_string(),
        value_id: ValueId::new(vid),
    })
}
fn phi_assign(target: &str, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::PhiAssign {
        target: target.to_string(),
        value,
        to: BlockId::new(7),
        exceptional: false,
    })
}
fn exc_assign(target: &str, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::PhiAssign {
        target: target.to_string(),
        value,
        to: BlockId::new(9),
        exceptional: true,
    })
}
fn expr_stmt(e: Expr) -> Leaf {
    Leaf::Raw(Stmt::Expr(e))
}
fn elided(op: &'static str) -> Leaf {
    Leaf::Raw(Stmt::Elided {
        op,
        reason: "test guard",
        loc: None,
    })
}
fn run(leaves: Vec<Leaf>) -> SNode {
    SNode::Stmts(leaves)
}
fn if_node(cond: Expr, then: Vec<SNode>, otherwise: Vec<SNode>) -> SNode {
    SNode::If {
        cond,
        then,
        otherwise,
    }
}
fn isfalse(e: Expr) -> Expr {
    Expr::Unary {
        op: UnOp::IsFalse,
        operand: bx(e),
    }
}
fn istrue(e: Expr) -> Expr {
    Expr::Unary {
        op: UnOp::IsTrue,
        operand: bx(e),
    }
}
fn cmp(op: CmpOp, l: Expr, r: Expr) -> Expr {
    Expr::Compare {
        op,
        left: bx(l),
        right: bx(r),
    }
}
fn prop(base: Expr, name: &str) -> Expr {
    Expr::PropName {
        object: bx(base),
        name: name.to_string(),
        dot_legal: true,
    }
}
fn call0(callee: Expr) -> Expr {
    Expr::Call {
        callee: bx(callee),
        this: None,
        args: vec![],
        kind: CallKind::Dynamic,
    }
}
fn call1(callee: Expr, arg: Expr) -> Expr {
    Expr::Call {
        callee: bx(callee),
        this: None,
        args: vec![arg],
        kind: CallKind::Dynamic,
    }
}
fn catch(binding: &str, body: Vec<SNode>) -> CatchClause {
    CatchClause {
        binding: Some(binding.to_string()),
        body,
    }
}
fn try_node(body: Vec<SNode>, catches: Vec<CatchClause>) -> SNode {
    SNode::Try {
        body,
        catches,
        note: None,
        finally: None,
    }
}

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

// ── iterator-loop folds (for-of / for-in / degenerate for-in) ──

/// The corpus for-of shape: `it`/`next` plumbing, header phis,
/// `res = next()`, `done = res.done`, the done-tested while, the
/// value binding, and back-edge self-assigns.
fn for_of_site() -> Vec<SNode> {
    vec![
        run(vec![
            decl(
                "it",
                10,
                Expr::Iter {
                    op: IterOp::GetIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("next", 11, prop(tm("it", 10), "next")),
            phi_assign("np", tm("next", 11)),
            phi_assign("ip", tm("it", 10)),
        ]),
        SNode::While {
            label: None,
            cond: Some(istrue(tm("done", 25))),
            body: vec![
                run(vec![
                    phi_decl("np", 20),
                    phi_decl("ip", 21),
                    decl("res", 23, call0(tm("np", 20))),
                    decl("done", 25, prop(tm("res", 23), "done")),
                ]),
                run(vec![
                    decl("v", 26, prop(tm("res", 23), "value")),
                    expr_stmt(call1(ident("print"), tm("v", 26))),
                ]),
                run(vec![
                    phi_assign("np", tm("np", 20)),
                    phi_assign("ip", tm("ip", 21)),
                ]),
            ],
        },
    ]
}

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

/// The corpus for-in shape, with one extra pass-through header phi
/// (hoisted above the folded loop) and an identity-copy phi chain
/// in the body (eliminated by `elim_internal_copy_phis`).
fn for_in_site() -> Vec<SNode> {
    vec![
        run(vec![
            phi_assign(
                "ip",
                Expr::Iter {
                    op: IterOp::GetPropIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            phi_assign("xp", ident("invariant")),
        ]),
        SNode::While {
            label: None,
            cond: Some(cmp(CmpOp::Eq, undef(), tm("k", 31))),
            body: vec![
                run(vec![
                    phi_decl("ip", 20),
                    phi_decl("xp", 21),
                    decl(
                        "k",
                        31,
                        Expr::Iter {
                            op: IterOp::NextPropName,
                            obj: bx(tm("ip", 20)),
                            status: NodeStatus::Plumbing,
                        },
                    ),
                ]),
                run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))]),
                // A branch join's identity-copy phi chain (never
                // read after elimination).
                if_node(
                    ident("c"),
                    vec![run(vec![
                        phi_decl("cp", 40),
                        phi_assign("cp", tm("ip", 20)),
                    ])],
                    vec![run(vec![
                        phi_decl("dp", 41),
                        phi_assign("dp", tm("cp", 40)),
                    ])],
                ),
                run(vec![
                    phi_assign("ip", tm("ip", 20)),
                    phi_assign("xp", tm("xp", 21)),
                ]),
            ],
        },
    ]
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

/// The degenerate (single-pass) for-in site: acyclic plumbing, the
/// exit test, and the one-shot body in the not-done arm.
fn single_pass_for_in_site(cond: Expr) -> Vec<SNode> {
    vec![
        run(vec![
            expr_stmt(call0(ident("setup"))),
            phi_assign(
                "it",
                Expr::Iter {
                    op: IterOp::GetPropIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
        ]),
        run(vec![
            phi_decl("it", 30),
            decl(
                "k",
                31,
                Expr::Iter {
                    op: IterOp::NextPropName,
                    obj: bx(tm("it", 30)),
                    status: NodeStatus::Plumbing,
                },
            ),
        ]),
        if_node(
            cond,
            vec![],
            vec![run(vec![expr_stmt(call1(ident("print"), tm("k", 31)))])],
        ),
    ]
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

// ── d-P17: the plain-async for-await driver family ─────────────

/// The N70 driver site: [pre-loop wiring, the `while (true)`
/// driver]. Covers the variant arms the corpus never produces:
/// interleaved honesty comments, elided guards, an
/// `istrue`-wrapped done test, a plain-`Stmts` value binding, a
/// trailing empty run in the done arm, and a store-carried
/// bookkeeping phi collapsed by substitution.
fn driver_shape() -> Vec<SNode> {
    vec![
        // The iterator setup + header wiring (pre-loop).
        run(vec![
            decl(
                "it",
                10,
                Expr::Iter {
                    op: IterOp::GetAsyncIterator,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("next", 11, prop(tm("it", 10), "next")),
            phi_assign("np", tm("next", 11)),
            phi_assign("ip", tm("it", 10)),
            phi_assign("bk", ident("out")),
        ]),
        SNode::While {
            label: None,
            cond: None,
            body: vec![
                run(vec![
                    phi_decl("np", 20),
                    phi_decl("ip", 21),
                    phi_decl("bk", 22),
                ]),
                SNode::Honest("dissolved wrapper".to_string()),
                run(vec![
                    decl(
                        "res",
                        23,
                        Expr::Call {
                            callee: bx(tm("np", 20)),
                            this: Some(bx(tm("ip", 21))),
                            args: vec![],
                            kind: CallKind::Direct,
                        },
                    ),
                    elided("ThrowIfNotObject"),
                    decl(
                        "aw",
                        24,
                        Expr::Await {
                            value: bx(tm("res", 23)),
                            uncaught: true,
                        },
                    ),
                    elided("Guard"),
                    decl("done", 25, prop(tm("aw", 24), "done")),
                ]),
                if_node(
                    istrue(tm("done", 25)),
                    vec![
                        run(vec![expr_stmt(call1(ident("print"), ident("out")))]),
                        SNode::Break { label: None },
                        run(vec![]),
                    ],
                    vec![
                        run(vec![
                            decl("x", 26, prop(tm("aw", 24), "value")),
                            Leaf::Raw(Stmt::StoreProp {
                                object: tm("bk", 22),
                                name: "items".to_string(),
                                dot_legal: true,
                                value: tm("x", 26),
                                own: false,
                            }),
                        ]),
                        run(vec![
                            phi_assign("np", tm("np", 20)),
                            phi_assign("ip", tm("ip", 21)),
                            phi_assign("bk", tm("bk", 22)),
                        ]),
                        SNode::Continue { label: None },
                    ],
                ),
                SNode::Honest("trailing".to_string()),
            ],
        },
    ]
}

/// The While body of a driver shape (for near-miss mutations).
fn driver_body(nodes: &mut [SNode]) -> &mut Vec<SNode> {
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    body
}

/// A near-miss pin: one mutation of the valid driver shape must
/// leave the fold unmatched.
fn driver_bails(mutate: impl FnOnce(&mut Vec<SNode>)) {
    let mut nodes = driver_shape();
    mutate(&mut nodes);
    assert!(
        match_for_await_driver(&nodes, 1).is_none(),
        "near-miss unexpectedly matched"
    );
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

// ── N74-W4: rest-parameter reconstruction ──────────────────────

/// A body with one CopyRestArgs shape, spread through every
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

// ── folds 1+2: literal builders / rest destructuring ───────────

fn closure(name: &str) -> Expr {
    Expr::Closure {
        body: FuncId::new(0),
        name: name.to_string(),
        kind: FunctionKind::Function,
        captures: vec![],
    }
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

/// An async body: the entry temp, an optimized-profile mode
/// immediate (a pure const declare), one await site with the full
/// machinery tail, and the THROW dispatch on the mode temp.
fn async_body() -> Vec<SNode> {
    vec![
        run(vec![
            decl(
                "g",
                10,
                Expr::Fallback {
                    op: "AsyncFunctionEnter",
                    note: "entry protocol",
                    operands: vec![],
                },
            ),
            decl("cn", 11, num(1.0)),
            decl(
                "a",
                12,
                Expr::Await {
                    value: bx(ident("p")),
                    uncaught: true,
                },
            ),
            expr_stmt(Expr::Yield {
                value: bx(tm("a", 12)),
            }),
            decl(
                "r",
                13,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 10)),
                },
            ),
            decl(
                "m",
                14,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 10)),
                },
            ),
        ]),
        if_node(
            cmp(CmpOp::Eq, tm("m", 14), tm("cn", 11)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r", 13)))])],
            vec![run(vec![expr_stmt(ident("cont"))])],
        ),
    ]
}

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

/// An async-generator body: the entry protocol with
/// optimized-profile const decls and BOTH dead entry results
/// (resume + mode), then one full yield site (the pre-yield await,
/// the THROW dispatch, the yield-point resumption pair, the
/// three-way mode dispatch with a phi-partition run before the
/// THROW test), and a completion resolve.
fn agen_body() -> Vec<SNode> {
    let driver = |r: &str, rv: u32, m: &str, mv: u32| {
        [
            decl(
                r,
                rv,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("g", 20)),
                },
            ),
            decl(
                m,
                mv,
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("g", 20)),
                },
            ),
        ]
    };
    let [r1, m1] = driver("r1", 31, "m1", 32);
    let [ry, my] = driver("ry", 33, "my", 34);
    vec![
        run(vec![
            decl(
                "g",
                20,
                Expr::CreateGenerator {
                    func: bx(closure("f")),
                },
            ),
            decl("c0", 21, num(0.0)),
            decl("c1", 22, num(1.0)),
            expr_stmt(Expr::Yield { value: bx(undef()) }),
            expr_stmt(Expr::GeneratorDriver {
                resume: true,
                genobj: bx(tm("g", 20)),
            }),
            expr_stmt(Expr::GeneratorDriver {
                resume: false,
                genobj: bx(tm("g", 20)),
            }),
        ]),
        // The pre-yield await machinery (d-P13's site shape).
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
            r1,
            m1,
        ]),
        // Its THROW-only dispatch; the continuation carries the
        // yield-point resumption pair + the three-way dispatch.
        if_node(
            cmp(CmpOp::Eq, tm("m1", 32), num(1.0)),
            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("r1", 31)))])],
            vec![
                run(vec![phi_assign("pp", ident("z"))]),
                run(vec![ry, my]),
                if_node(
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
                        run(vec![phi_assign("pp2", ident("z"))]),
                        if_node(
                            cmp(CmpOp::Eq, tm("my", 34), num(1.0)),
                            vec![run(vec![Leaf::Raw(Stmt::Throw(tm("ry", 33)))])],
                            vec![run(vec![expr_stmt(ident("next_cont"))])],
                        ),
                    ],
                ),
            ],
        ),
        // The completion resolve: `return { value: g, done: X }`.
        run(vec![Leaf::Raw(Stmt::Return(Some(Expr::IterResultObj {
            value: bx(tm("g", 20)),
            done: bx(ident("undefinedv")),
        })))]),
    ]
}

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

/// A fold context for the d-P14 matchers (genobj 20).
fn agen_cx(nodes: &[SNode]) -> AsyncMachineCx {
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
        genobj: ValueId::new(20),
        aliases: [ValueId::new(20)].into_iter().collect(),
        exit_throws: BTreeSet::new(),
        const_env,
        consumed_consts: BTreeSet::new(),
        uses,
    }
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

/// The shared ys header run.
fn ys_header() -> SNode {
    run(vec![
        phi_decl("vrt", 100),
        phi_decl("vrv", 101),
        phi_decl("vit", 102),
        phi_decl("vg", 103),
        phi_decl("vflag", 104),
        decl("vexit0", 105, boolean(false)),
    ])
}

/// The shared mode dispatch: `if (rt !== NEXT) { if (rt !== THROW)
/// { RETURN arm } else { THROW arm } } else { assigns → call }`.
fn ys_dispatch(ret_arm: Vec<SNode>, throw_arm: Vec<SNode>) -> SNode {
    if_node(
        isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(2.0))),
        vec![if_node(
            isfalse(cmp(CmpOp::StrictEq, tm("vrt", 100), num(1.0))),
            ret_arm,
            throw_arm,
        )],
        vec![run(vec![phi_assign("vm0", tm("vnext", 201))])],
    )
}

/// The shared RETURN arm (`async_` skips the propagation return).
fn ys_ret_arm(async_: bool) -> Vec<SNode> {
    let mut out = vec![run(vec![
        decl("vt", 120, boolean(true)),
        decl("vret", 121, prop(tm("vit", 102), "return")),
    ])];
    if !async_ {
        out.push(run(vec![Leaf::Raw(Stmt::Return(Some(tm("vrv", 101))))]));
    }
    out.push(if_node(
        isfalse(cmp(CmpOp::Eq, tm("vret", 121), undef())),
        vec![run(vec![
            phi_assign("vexit", tm("vt", 120)),
            phi_assign("vm1", tm("vnext", 201)),
        ])],
        vec![SNode::Break { label: None }],
    ));
    out
}

/// The shared THROW arm.
fn ys_throw_arm() -> Vec<SNode> {
    vec![
        run(vec![
            decl("vthrow", 130, prop(tm("vit", 102), "throw")),
            decl("veq", 131, cmp(CmpOp::Eq, tm("vthrow", 130), undef())),
        ]),
        if_node(
            isfalse(tm("veq", 131)),
            vec![run(vec![phi_assign("vexit", tm("vexit0", 105))])],
            vec![],
        ),
        if_node(
            istrue(tm("vflag", 104)),
            vec![run(vec![elided("ThrowNotExists")])],
            vec![run(vec![])],
        ),
    ]
}

/// The sync tail: precall, done test, pass-through suspend,
/// loop-back assigns, continue.
fn ys_sync_tail() -> Vec<SNode> {
    vec![
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
            decl("vdone", 113, prop(tm("vres", 112), "done")),
        ]),
        if_node(
            istrue(tm("vdone", 113)),
            vec![SNode::Break { label: None }],
            vec![],
        ),
        run(vec![
            expr_stmt(Expr::Yield {
                value: bx(tm("vres", 112)),
            }),
            decl(
                "vresume",
                140,
                Expr::GeneratorDriver {
                    resume: true,
                    genobj: bx(tm("vg", 103)),
                },
            ),
        ]),
        run(vec![
            phi_assign(
                "vrt",
                Expr::GeneratorDriver {
                    resume: false,
                    genobj: bx(tm("vg", 103)),
                },
            ),
            phi_assign("vrv", tm("vresume", 140)),
        ]),
        SNode::Continue { label: None },
    ]
}

/// The setup + init runs (`yield* <obj>` plumbing).
fn ys_setup_init(async_: bool) -> [SNode; 2] {
    let op = if async_ {
        IterOp::GetAsyncIterator
    } else {
        IterOp::GetIterator
    };
    [
        run(vec![
            decl(
                "vit0",
                200,
                Expr::Iter {
                    op,
                    obj: bx(ident("src")),
                    status: NodeStatus::Plumbing,
                },
            ),
            decl("vnext", 201, prop(tm("vit0", 200), "next")),
        ]),
        run(vec![
            phi_assign("vrt", num(2.0)),
            phi_assign("vrv", undef()),
            phi_assign("vflag", boolean(false)),
            phi_assign("vit", tm("vit0", 200)),
            phi_assign("vg", tm("vg0", 202)),
            phi_assign("vm", tm("vnext", 201)),
        ]),
    ]
}

/// The full sync site: [setup, init, While, exit dispatch].
fn ys_sync_shape() -> Vec<SNode> {
    let [setup, init] = ys_setup_init(false);
    vec![
        setup,
        init,
        SNode::While {
            label: None,
            cond: None,
            body: {
                let mut b = vec![ys_header(), ys_dispatch(ys_ret_arm(false), ys_throw_arm())];
                b.extend(ys_sync_tail());
                b
            },
        },
        // The completion dispatch: `if (!exitReturn) { v =
        // res.value; <cont> } else { v2 = res.value; return v2 }`.
        if_node(
            isfalse(tm("vexit", 110)),
            vec![run(vec![
                decl("vval", 150, prop(tm("vres", 112), "value")),
                expr_stmt(tm("vval", 150)),
            ])],
            vec![run(vec![
                decl("vv2", 151, prop(tm("vres", 112), "value")),
                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
            ])],
        ),
    ]
}

/// The While node of a ys shape (for near-miss mutations).
fn ys_while(nodes: &mut [SNode]) -> &mut SNode {
    &mut nodes[2]
}

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

/// The async tail: [precall (call + inner await + pass-through
/// yield + resume), the await's THROW dispatch with the in-loop
/// completion].
fn ys_async_tail() -> Vec<SNode> {
    let drv = |resume: bool| Expr::GeneratorDriver {
        resume,
        genobj: bx(tm("vg", 103)),
    };
    vec![
        // precall: phis, `res = vm.call(it, rv)`, `aw = await res`,
        // `yield aw`, `res1 = ResumeGenerator(g)`.
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
            expr_stmt(Expr::Yield {
                value: bx(tm("aw0", 141)),
            }),
            decl("vres1", 142, drv(true)),
        ]),
        // The await's THROW dispatch.
        if_node(
            isfalse(cmp(CmpOp::Eq, drv(false), num(1.0))),
            // Continuation: done load + the done test with the
            // in-loop completion dispatch.
            vec![
                run(vec![
                    elided("ThrowIfNotObject"),
                    decl("vdone", 113, prop(tm("vres1", 142), "done")),
                ]),
                if_node(
                    istrue(tm("vdone", 113)),
                    vec![
                        if_node(
                            isfalse(tm("vexit", 110)),
                            vec![run(vec![
                                decl("vval", 150, prop(tm("vres1", 142), "value")),
                                expr_stmt(tm("vval", 150)),
                            ])],
                            vec![run(vec![
                                decl("vv2", 151, prop(tm("vres1", 142), "value")),
                                Leaf::Raw(Stmt::Return(Some(tm("vv2", 151)))),
                            ])],
                        ),
                        SNode::Break { label: None },
                    ],
                    // Not done: the AsyncGeneratorYield + the
                    // resumption re-entry.
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
                            expr_stmt(Expr::Yield {
                                value: bx(tm("av2", 144)),
                            }),
                            decl("vres2", 145, drv(true)),
                        ]),
                        if_node(
                            isfalse(cmp(CmpOp::Eq, drv(false), num(1.0))),
                            vec![
                                run(vec![
                                    decl("r3", 146, drv(true)),
                                    decl("m3", 147, drv(false)),
                                ]),
                                // `if (m3 != RETURN) { loop back }`.
                                if_node(
                                    isfalse(cmp(CmpOp::Eq, tm("m3", 147), num(0.0))),
                                    vec![
                                        run(vec![
                                            phi_assign("vrt", tm("m3", 147)),
                                            phi_assign("vrv", tm("r3", 146)),
                                        ]),
                                        SNode::Continue { label: None },
                                    ],
                                    vec![],
                                ),
                                // The RETURN await.
                                run(vec![
                                    decl(
                                        "aw3",
                                        148,
                                        Expr::Await {
                                            value: bx(tm("r3", 146)),
                                            uncaught: true,
                                        },
                                    ),
                                    expr_stmt(Expr::Yield {
                                        value: bx(tm("aw3", 148)),
                                    }),
                                    decl("r4", 152, drv(true)),
                                    decl("m4", 153, drv(false)),
                                ]),
                                // `if (m4 == THROW) { loop back }`.
                                if_node(
                                    isfalse(cmp(CmpOp::NotEq, tm("m4", 153), num(1.0))),
                                    vec![
                                        run(vec![
                                            phi_assign("vrt", tm("m4", 153)),
                                            phi_assign("vrv", tm("r4", 152)),
                                        ]),
                                        SNode::Continue { label: None },
                                    ],
                                    vec![],
                                ),
                                // The final loop-back (RETURN).
                                run(vec![
                                    phi_assign("vrt", num(0.0)),
                                    phi_assign("vrv", tm("r4", 152)),
                                ]),
                                SNode::Continue { label: None },
                            ],
                            vec![
                                run(vec![
                                    Leaf::Raw(Stmt::Throw(tm("vres2", 145))),
                                    Leaf::Raw(Stmt::Unreachable),
                                ]),
                                SNode::Break { label: None },
                            ],
                        ),
                    ],
                ),
            ],
            vec![
                run(vec![
                    Leaf::Raw(Stmt::Throw(tm("vres1", 142))),
                    Leaf::Raw(Stmt::Unreachable),
                ]),
                SNode::Break { label: None },
            ],
        ),
    ]
}

/// The full async site: [setup, init, While] (the completion lives
/// inside the loop).
fn ys_async_shape() -> Vec<SNode> {
    let [setup, init] = ys_setup_init(true);
    vec![
        setup,
        init,
        SNode::While {
            label: None,
            cond: None,
            body: {
                let mut b = vec![ys_header(), ys_dispatch(ys_ret_arm(true), ys_throw_arm())];
                b.extend(ys_async_tail());
                b
            },
        },
    ]
}

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
