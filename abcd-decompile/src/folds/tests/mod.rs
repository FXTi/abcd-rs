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

pub(super) fn bx(e: Expr) -> Box<Expr> {
    Box::new(e)
}
/// A temp reference (name + SSA id kept consistent by convention).
pub(super) fn tm(name: &str, vid: u32) -> Expr {
    Expr::Temp {
        value: ValueId::new(vid),
        name: name.to_string(),
    }
}
pub(super) fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string())
}
pub(super) fn num(x: f64) -> Expr {
    Expr::Lit(Lit::Number(x.to_bits()))
}
pub(super) fn boolean(b: bool) -> Expr {
    Expr::Lit(Lit::Bool(b))
}
pub(super) fn strlit(s: &str) -> Expr {
    Expr::Lit(Lit::String(s.to_string()))
}
pub(super) fn undef() -> Expr {
    Expr::Lit(Lit::Undefined)
}
pub(super) fn decl(name: &str, vid: u32, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::Declare {
        name: name.to_string(),
        mutable: false,
        value,
        value_id: ValueId::new(vid),
    })
}
pub(super) fn phi_decl(name: &str, vid: u32) -> Leaf {
    Leaf::Raw(Stmt::PhiDecl {
        name: name.to_string(),
        value_id: ValueId::new(vid),
    })
}
pub(super) fn phi_assign(target: &str, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::PhiAssign {
        target: target.to_string(),
        value,
        to: BlockId::new(7),
        exceptional: false,
    })
}
pub(super) fn exc_assign(target: &str, value: Expr) -> Leaf {
    Leaf::Raw(Stmt::PhiAssign {
        target: target.to_string(),
        value,
        to: BlockId::new(9),
        exceptional: true,
    })
}
pub(super) fn expr_stmt(e: Expr) -> Leaf {
    Leaf::Raw(Stmt::Expr(e))
}
pub(super) fn elided(op: &'static str) -> Leaf {
    Leaf::Raw(Stmt::Elided {
        op,
        reason: "test guard",
        loc: None,
    })
}
pub(super) fn run(leaves: Vec<Leaf>) -> SNode {
    SNode::Stmts(leaves)
}
pub(super) fn if_node(cond: Expr, then: Vec<SNode>, otherwise: Vec<SNode>) -> SNode {
    SNode::If {
        cond,
        then,
        otherwise,
    }
}
pub(super) fn isfalse(e: Expr) -> Expr {
    Expr::Unary {
        op: UnOp::IsFalse,
        operand: bx(e),
    }
}
pub(super) fn istrue(e: Expr) -> Expr {
    Expr::Unary {
        op: UnOp::IsTrue,
        operand: bx(e),
    }
}
pub(super) fn cmp(op: CmpOp, l: Expr, r: Expr) -> Expr {
    Expr::Compare {
        op,
        left: bx(l),
        right: bx(r),
    }
}
pub(super) fn prop(base: Expr, name: &str) -> Expr {
    Expr::PropName {
        object: bx(base),
        name: name.to_string(),
        dot_legal: true,
    }
}
pub(super) fn call0(callee: Expr) -> Expr {
    Expr::Call {
        callee: bx(callee),
        this: None,
        args: vec![],
        kind: CallKind::Dynamic,
    }
}
pub(super) fn call1(callee: Expr, arg: Expr) -> Expr {
    Expr::Call {
        callee: bx(callee),
        this: None,
        args: vec![arg],
        kind: CallKind::Dynamic,
    }
}
pub(super) fn catch(binding: &str, body: Vec<SNode>) -> CatchClause {
    CatchClause {
        binding: Some(binding.to_string()),
        body,
    }
}
pub(super) fn try_node(body: Vec<SNode>, catches: Vec<CatchClause>) -> SNode {
    SNode::Try {
        body,
        catches,
        note: None,
        finally: None,
    }
}

/// `res = next()`, `done = res.done`, the done-tested while, the
/// value binding, and back-edge self-assigns.
pub(super) fn for_of_site() -> Vec<SNode> {
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

/// (hoisted above the folded loop) and an identity-copy phi chain
/// in the body (eliminated by `elim_internal_copy_phis`).
pub(super) fn for_in_site() -> Vec<SNode> {
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

/// The degenerate (single-pass) for-in site: acyclic plumbing, the
/// exit test, and the one-shot body in the not-done arm.
pub(super) fn single_pass_for_in_site(cond: Expr) -> Vec<SNode> {
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

/// `istrue`-wrapped done test, a plain-`Stmts` value binding, a
/// trailing empty run in the done arm, and a store-carried
/// bookkeeping phi collapsed by substitution.
pub(super) fn driver_shape() -> Vec<SNode> {
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
pub(super) fn driver_body(nodes: &mut [SNode]) -> &mut Vec<SNode> {
    let SNode::While { body, .. } = &mut nodes[1] else {
        unreachable!()
    };
    body
}

/// A near-miss pin: one mutation of the valid driver shape must
/// leave the fold unmatched.
pub(super) fn driver_bails(mutate: impl FnOnce(&mut Vec<SNode>)) {
    let mut nodes = driver_shape();
    mutate(&mut nodes);
    assert!(
        match_for_await_driver(&nodes, 1).is_none(),
        "near-miss unexpectedly matched"
    );
}

// ── folds 1+2: literal builders / rest destructuring ───────────

pub(super) fn closure(name: &str) -> Expr {
    Expr::Closure {
        body: FuncId::new(0),
        name: name.to_string(),
        kind: FunctionKind::Function,
        captures: vec![],
    }
}

/// immediate (a pure const declare), one await site with the full
/// machinery tail, and the THROW dispatch on the mode temp.
pub(super) fn async_body() -> Vec<SNode> {
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

/// three-way mode dispatch with a phi-partition run before the
/// THROW test), and a completion resolve.
pub(super) fn agen_body() -> Vec<SNode> {
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

/// A fold context for the d-P14 matchers (genobj 20).
pub(super) fn agen_cx(nodes: &[SNode]) -> AsyncMachineCx {
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

/// The shared ys header run.
pub(super) fn ys_header() -> SNode {
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
pub(super) fn ys_dispatch(ret_arm: Vec<SNode>, throw_arm: Vec<SNode>) -> SNode {
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
pub(super) fn ys_ret_arm(async_: bool) -> Vec<SNode> {
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
pub(super) fn ys_throw_arm() -> Vec<SNode> {
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
pub(super) fn ys_sync_tail() -> Vec<SNode> {
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
pub(super) fn ys_setup_init(async_: bool) -> [SNode; 2] {
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
pub(super) fn ys_sync_shape() -> Vec<SNode> {
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
pub(super) fn ys_while(nodes: &mut [SNode]) -> &mut SNode {
    &mut nodes[2]
}

/// yield + resume), the await's THROW dispatch with the in-loop
/// completion].
pub(super) fn ys_async_tail() -> Vec<SNode> {
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
pub(super) fn ys_async_shape() -> Vec<SNode> {
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

mod control;
mod literals_scope;
mod loops;
mod machines;
mod walkers;
mod yield_star_async;
mod yield_star_sync;
