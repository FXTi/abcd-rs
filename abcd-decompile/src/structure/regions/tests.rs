//! Unit and small-stack tests for `structure::regions`.

use super::*;
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, Catch, FunctionData, Inst, Value};
use abcd_ir::module::{ClassData, FunctionKind};
use abcd_ir::ty::Ty;
use abcd_ir::{ClassId, Edge, InstId, Op, ValueDef, ValueId};

fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData::new(name, name));
    m
}

fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

fn add_func(m: &mut Module) -> FuncId {
    let name = m.sym.intern("f");
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    m.classes[0].methods.push(id);
    add_block(m, id);
    id
}

fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    push_inst(m, b, op)
}

fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    let cid = m.consts.push(Const::number(x));
    let inst = push_inst(m, b, Op::LoadConst(cid));
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

fn add_exception_param(m: &mut Module, handler: BlockId) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(handler),
        ty: Ty::Any,
    });
    val
}

fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId, exc: ValueId) {
    for &p in &protected {
        m.block_mut(handler).unwrap().preds.push(Edge {
            from: p,
            kind: EdgeKind::Exceptional,
        });
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_class: None,
        }],
    });
}

/// `cond`-terminated block helper.
fn cond_branch(m: &mut abcd_ir::Module, b: BlockId, t: BlockId, f: BlockId) {
    let c = load_number(m, b, 1.0);
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: f,
        },
    );
}

fn branch(m: &mut abcd_ir::Module, b: BlockId, to: BlockId) {
    emit_void(m, b, Op::Branch { dest: to });
}

fn ret(m: &mut abcd_ir::Module, b: BlockId) {
    emit_void(m, b, Op::Return { value: None });
}

/// Find a classified edge.
fn edge(tree: &RegionTree, from: BlockId, to: BlockId) -> EdgeClass {
    tree.edges
        .iter()
        .find(|e| e.from == from && e.to == to)
        .unwrap_or_else(|| panic!("edge {from:?} -> {to:?} not classified"))
        .class
}

/// The single Loop node of the tree, if exactly one.
fn loops_in(tree: &RegionTree) -> Vec<&RegionNode> {
    tree.nodes()
        .iter()
        .filter(|n| matches!(n, RegionNode::Loop { .. }))
        .collect()
}

/// Diamond: entry → {a, b} → join → exit.
#[test]
fn diamond_conditional() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    cond_branch(&mut m, entry, a, b);
    branch(&mut m, a, join);
    branch(&mut m, b, join);
    branch(&mut m, join, exit);
    ret(&mut m, exit);
    link(&mut m, entry, a);
    link(&mut m, entry, b);
    link(&mut m, a, join);
    link(&mut m, b, join);
    link(&mut m, join, exit);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    assert!(tree.loops.is_empty());
    let RegionNode::Seq(items) = tree.root_node().unwrap() else {
        panic!("root must be Seq: {:?}", tree.root_node());
    };
    let RegionNode::If {
        head,
        then,
        otherwise,
        merge,
    } = tree.node(items[0])
    else {
        panic!("first item must be If: {:?}", tree.node(items[0]));
    };
    assert_eq!(*head, entry);
    assert_eq!(*merge, Some(join));
    assert_eq!(then.map(|r| tree.node(r)), Some(&RegionNode::Block(a)));
    assert_eq!(otherwise.map(|r| tree.node(r)), Some(&RegionNode::Block(b)));
    // Continuation: join → exit.
    let RegionNode::Seq(cont) = tree.node(items[1]) else {
        panic!("continuation must be Seq: {:?}", tree.node(items[1]));
    };
    assert_eq!(tree.node(cont[0]), &RegionNode::Block(join));
    assert_eq!(tree.node(cont[1]), &RegionNode::Block(exit));
    // All five edges are internal flow.
    for e in &tree.edges {
        assert_eq!(e.class, EdgeClass::Internal, "{e:?}");
    }
}

/// Nested loops: entry → outer-header → {inner-header, exit};
/// inner-header → {inner-body, outer-latch}; inner-body → inner-header;
/// outer-latch → outer-header.
#[test]
fn nested_loops() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let oh = add_block(&mut m, f);
    let ih = add_block(&mut m, f);
    let ib = add_block(&mut m, f);
    let ol = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    branch(&mut m, entry, oh);
    cond_branch(&mut m, oh, ih, exit);
    cond_branch(&mut m, ih, ib, ol);
    branch(&mut m, ib, ih);
    branch(&mut m, ol, oh);
    ret(&mut m, exit);
    link(&mut m, entry, oh);
    link(&mut m, oh, ih);
    link(&mut m, oh, exit);
    link(&mut m, ih, ib);
    link(&mut m, ih, ol);
    link(&mut m, ib, ih);
    link(&mut m, ol, oh);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    assert!(tree.irreducible.is_empty());
    assert_eq!(tree.loops.len(), 2);
    // Both headers carry the exit test.
    assert!(tree.loops.iter().all(|l| l.kind == LoopKind::While));
    // Nesting: inner ⊆ outer, parent link set.
    let inner = tree.loops.iter().find(|l| l.header == ih).unwrap();
    let outer = tree.loops.iter().find(|l| l.header == oh).unwrap();
    assert_eq!(inner.blocks, vec![ih, ib]);
    assert_eq!(outer.blocks.len(), 4);
    let outer_idx = tree.loops.iter().position(|l| l.header == oh).unwrap();
    assert_eq!(inner.parent, Some(outer_idx));
    assert_eq!(outer.parent, None);
    // Two Loop nodes, the inner nested under the outer's body.
    assert_eq!(loops_in(&tree).len(), 2);
    // Edge classes: plain continues.
    assert_eq!(
        edge(&tree, ib, ih),
        EdgeClass::Continue {
            header: ih,
            labeled: false
        }
    );
    assert_eq!(
        edge(&tree, ol, oh),
        EdgeClass::Continue {
            header: oh,
            labeled: false
        }
    );
    assert_eq!(
        edge(&tree, oh, exit),
        EdgeClass::Break {
            header: oh,
            labeled: false
        }
    );
    // ih → ol leaves the inner loop (ol is the outer latch): unlabeled
    // break from the inner loop.
    assert_eq!(
        edge(&tree, ih, ol),
        EdgeClass::Break {
            header: ih,
            labeled: false
        }
    );
}

/// Labeled multi-exit: an inner-loop block breaks out of the OUTER loop
/// (labeled break) and another continues the outer loop (labeled
/// continue).
///
/// entry → oh → {ih, after}; ih → {ib, ol}; ib → {after, ib2};
/// ib2 → {oh, ih}; ol → oh; after returns.
#[test]
fn labeled_break_and_continue() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let oh = add_block(&mut m, f);
    let ih = add_block(&mut m, f);
    let ib = add_block(&mut m, f);
    let ib2 = add_block(&mut m, f);
    let ol = add_block(&mut m, f);
    let after = add_block(&mut m, f);
    branch(&mut m, entry, oh);
    cond_branch(&mut m, oh, ih, after);
    cond_branch(&mut m, ih, ib, ol);
    cond_branch(&mut m, ib, after, ib2);
    cond_branch(&mut m, ib2, oh, ih);
    branch(&mut m, ol, oh);
    ret(&mut m, after);
    for (u, v) in [
        (entry, oh),
        (oh, ih),
        (oh, after),
        (ih, ib),
        (ih, ol),
        (ib, after),
        (ib, ib2),
        (ib2, oh),
        (ib2, ih),
        (ol, oh),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.irreducible.is_empty(), "{:?}", tree.irreducible);
    assert_eq!(tree.loops.len(), 2);
    // ib → after breaks out of BOTH loops: labeled by the outer header.
    assert_eq!(
        edge(&tree, ib, after),
        EdgeClass::Break {
            header: oh,
            labeled: true
        }
    );
    // ib2 → oh continues the OUTER loop across the inner: labeled.
    assert_eq!(
        edge(&tree, ib2, oh),
        EdgeClass::Continue {
            header: oh,
            labeled: true
        }
    );
    // ib2 → ih is the inner loop's plain continue.
    assert_eq!(
        edge(&tree, ib2, ih),
        EdgeClass::Continue {
            header: ih,
            labeled: false
        }
    );
    // oh → after exits only the outer loop: unlabeled break.
    assert_eq!(
        edge(&tree, oh, after),
        EdgeClass::Break {
            header: oh,
            labeled: false
        }
    );
    // Determinism: a second run produces an identical tree.
    let again = structure_regions(&m, f);
    assert_eq!(tree, again);
}

/// Switch-like multi-way: a cascade of two-way conditionals reconverging
/// at a common join.
#[test]
fn switch_like_cascade() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let c1 = add_block(&mut m, f);
    let d2 = add_block(&mut m, f);
    let c2 = add_block(&mut m, f);
    let c3 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    cond_branch(&mut m, entry, c1, d2);
    cond_branch(&mut m, d2, c2, c3);
    branch(&mut m, c1, join);
    branch(&mut m, c2, join);
    branch(&mut m, c3, join);
    ret(&mut m, join);
    link(&mut m, entry, c1);
    link(&mut m, entry, d2);
    link(&mut m, d2, c2);
    link(&mut m, d2, c3);
    link(&mut m, c1, join);
    link(&mut m, c2, join);
    link(&mut m, c3, join);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    let RegionNode::Seq(items) = tree.root_node().unwrap() else {
        panic!("root must be Seq");
    };
    let RegionNode::If {
        head,
        then,
        otherwise,
        merge,
    } = tree.node(items[0])
    else {
        panic!("first item must be If");
    };
    assert_eq!(*head, entry);
    assert_eq!(*merge, Some(join));
    assert_eq!(then.map(|r| tree.node(r)), Some(&RegionNode::Block(c1)));
    // The else arm is the nested dispatch conditional.
    let RegionNode::If {
        head: h2,
        then: t2,
        otherwise: o2,
        merge: m2,
    } = tree.node(otherwise.unwrap())
    else {
        panic!("else arm must be If");
    };
    assert_eq!(*h2, d2);
    assert_eq!(*m2, None); // the join lives outside the arm set
    assert_eq!(t2.map(|r| tree.node(r)), Some(&RegionNode::Block(c2)));
    assert_eq!(o2.map(|r| tree.node(r)), Some(&RegionNode::Block(c3)));
}

/// Try/handler: protected blocks structure normally; the handler is
/// Normal-unreachable (dead for structuring) and appears in the TryPlan.
#[test]
fn try_handler_projection() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t2 = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    branch(&mut m, entry, t2);
    branch(&mut m, t2, exit);
    ret(&mut m, exit);
    let exc = add_exception_param(&mut m, handler);
    emit_void(&mut m, handler, Op::Return { value: Some(exc) });
    link(&mut m, entry, t2);
    link(&mut m, t2, exit);
    add_try(&mut m, f, vec![entry, t2], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.dead_blocks, vec![handler]);
    assert_eq!(tree.try_plans.len(), 1);
    let plan = &tree.try_plans[0];
    assert_eq!(plan.region, 0);
    assert_eq!(plan.entry, Some(entry));
    assert_eq!(plan.protected, vec![entry, t2]);
    assert_eq!(plan.handlers, vec![handler]);
    assert_eq!(plan.span, tree.root);
}

/// Interleaved try regions are a hard error (reported, never panicked).
#[test]
fn interleaved_try_regions_are_hard_errors() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let b = add_block(&mut m, f);
    let c = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let h2 = add_block(&mut m, f);
    branch(&mut m, entry, b);
    branch(&mut m, b, c);
    branch(&mut m, c, exit);
    ret(&mut m, exit);
    let e1 = add_exception_param(&mut m, h1);
    ret(&mut m, h1);
    let e2 = add_exception_param(&mut m, h2);
    ret(&mut m, h2);
    link(&mut m, entry, b);
    link(&mut m, b, c);
    link(&mut m, c, exit);
    // {entry, b} and {b, c} intersect without nesting.
    add_try(&mut m, f, vec![entry, b], h1, e1);
    add_try(&mut m, f, vec![b, c], h2, e2);

    let tree = structure_regions(&m, f);
    assert!(
        tree.errors
            .iter()
            .any(|e| matches!(e, RegionError::InterleavedTryRegions { a: 0, b: 1 })),
        "{:?}",
        tree.errors
    );
}

/// Irreducible jump-into-loop: entry → {h, b}; h → b; b → {h, exit}.
/// The cycle {h, b} has no dominating header (entry → b bypasses h), so
/// there is no dominance back edge at all. Detected and reported, and
/// structuring still produces a total tree.
#[test]
fn irreducible_jump_into_loop() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    cond_branch(&mut m, entry, h, b);
    branch(&mut m, h, b);
    cond_branch(&mut m, b, h, exit);
    ret(&mut m, exit);
    link(&mut m, entry, h);
    link(&mut m, entry, b);
    link(&mut m, h, b);
    link(&mut m, b, h);
    link(&mut m, b, exit);

    let tree = structure_regions(&m, f);
    assert!(tree.root.is_some());
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    // One irreducible core over exactly the cycle blocks.
    assert_eq!(tree.irreducible.len(), 1);
    assert_eq!(tree.irreducible[0].blocks, {
        let mut v = vec![h, b];
        v.sort();
        v
    });
    // No natural loops exist (no dominance back edge).
    assert!(tree.loops.is_empty());
    // The backward edge b → h is flagged as a cross edge, not a
    // continue.
    assert!(
        tree.escape_hatches
            .iter()
            .any(|e| matches!(e, EscapeHatch::CrossEdge { from, to } if *from == b && *to == h)),
        "{:?}",
        tree.escape_hatches
    );
    assert_eq!(edge(&tree, b, h), EdgeClass::Internal);
    // Determinism on the irreducible shape too.
    assert_eq!(tree, structure_regions(&m, f));
}

/// Self-loop on the entry block: `while (c) { … }` at the function
/// entry.
#[test]
fn self_loop_entry() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let exit = add_block(&mut m, f);
    cond_branch(&mut m, entry, entry, exit);
    ret(&mut m, exit);
    link(&mut m, entry, entry);
    link(&mut m, entry, exit);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.loops.len(), 1);
    assert_eq!(tree.loops[0].kind, LoopKind::While);
    let RegionNode::Seq(items) = tree.root_node().unwrap() else {
        panic!("root must be Seq");
    };
    let RegionNode::Loop { header, kind, body } = tree.node(items[0]) else {
        panic!("first item must be Loop: {:?}", tree.node(items[0]));
    };
    assert_eq!(*header, entry);
    assert_eq!(*kind, LoopKind::While);
    assert_eq!(tree.node(*body), &RegionNode::Block(entry));
    assert_eq!(tree.node(items[1]), &RegionNode::Block(exit));
    assert_eq!(
        edge(&tree, entry, entry),
        EdgeClass::Continue {
            header: entry,
            labeled: false
        }
    );
    assert_eq!(
        edge(&tree, entry, exit),
        EdgeClass::Break {
            header: entry,
            labeled: false
        }
    );
}

/// do-while: header falls through unconditionally, the latch carries
/// the exit test.
#[test]
fn do_while_kind() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    branch(&mut m, entry, h);
    branch(&mut m, h, b);
    cond_branch(&mut m, b, h, exit);
    ret(&mut m, exit);
    link(&mut m, entry, h);
    link(&mut m, h, b);
    link(&mut m, b, h);
    link(&mut m, b, exit);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.loops.len(), 1);
    assert_eq!(tree.loops[0].kind, LoopKind::DoWhile);
    let loops = loops_in(&tree);
    assert_eq!(loops.len(), 1);
    assert!(matches!(
        loops[0],
        RegionNode::Loop {
            kind: LoopKind::DoWhile,
            header,
            ..
        } if *header == h
    ));
}

/// Multi-entry continuation: a loop whose two exit edges target
/// disjoint tails. The remainder becomes labeled alternates.
#[test]
fn multi_exit_alternates() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let tail_a = add_block(&mut m, f);
    let tail_b = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, body, tail_a);
    cond_branch(&mut m, body, h, tail_b);
    ret(&mut m, tail_a);
    ret(&mut m, tail_b);
    link(&mut m, entry, h);
    link(&mut m, h, body);
    link(&mut m, h, tail_a);
    link(&mut m, body, h);
    link(&mut m, body, tail_b);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    let RegionNode::Seq(items) = tree.root_node().unwrap() else {
        panic!("root must be Seq");
    };
    // [Block(entry), Seq[Loop, Alternates]] — the straight-line entry
    // peel precedes the loop.
    assert_eq!(tree.node(items[0]), &RegionNode::Block(entry));
    let RegionNode::Seq(inner) = tree.node(items[1]) else {
        panic!("second item must be Seq: {:?}", tree.node(items[1]));
    };
    assert!(matches!(tree.node(inner[0]), RegionNode::Loop { .. }));
    let RegionNode::Alternates(arms) = tree.node(inner[1]) else {
        panic!("continuation must be Alternates: {:?}", tree.node(inner[1]));
    };
    assert_eq!(arms.len(), 2);
    let labels: Vec<BlockId> = arms
        .iter()
        .map(|&a| match tree.node(a) {
            RegionNode::Labeled { label, .. } => *label,
            n => panic!("arm must be Labeled: {n:?}"),
        })
        .collect();
    assert_eq!(labels, {
        let mut v = vec![tail_a, tail_b];
        v.sort();
        v
    });
    assert_eq!(
        edge(&tree, h, tail_a),
        EdgeClass::Break {
            header: h,
            labeled: false
        }
    );
    assert_eq!(
        edge(&tree, body, tail_b),
        EdgeClass::Break {
            header: h,
            labeled: false
        }
    );
    assert_eq!(
        edge(&tree, body, h),
        EdgeClass::Continue {
            header: h,
            labeled: false
        }
    );
}

/// Degenerate shape: a bare-return function structures to one Block.
#[test]
fn bare_return_is_single_block() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    ret(&mut m, entry);
    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty());
    assert_eq!(tree.root_node(), Some(&RegionNode::Block(entry)));
    assert!(tree.edges.is_empty());
    assert!(tree.loops.is_empty());
}

/// Stack-depth regression guard for the ASan corpus stack-overflow
/// (lift-analysis gate, rayon worker thread): region structuring must
/// be driven by an explicit heap stack, never by native recursion with
/// input-driven depth. Deeply nested shapes must structure on a
/// 256 KiB stack.
///
/// `if (c1) { if (c2) { … } }` nesting, N levels deep: every level is
/// a two-successor head whose then-arm contains the whole inner nest
/// (an empty else, the merge chained to the outer merge).
#[test]
fn deep_nested_ifs_structure_on_small_stack() {
    const N: usize = 1000;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut m = mk_module();
            let f = add_func(&mut m);
            let h: Vec<BlockId> = (0..N)
                .map(|i| {
                    if i == 0 {
                        entry_of(&m, f)
                    } else {
                        add_block(&mut m, f)
                    }
                })
                .collect();
            let leaf = add_block(&mut m, f);
            let merges: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
            let exit = add_block(&mut m, f);
            for i in 0..N - 1 {
                cond_branch(&mut m, h[i], h[i + 1], merges[i]);
                link(&mut m, h[i], h[i + 1]);
                link(&mut m, h[i], merges[i]);
            }
            cond_branch(&mut m, h[N - 1], leaf, merges[N - 1]);
            link(&mut m, h[N - 1], leaf);
            link(&mut m, h[N - 1], merges[N - 1]);
            branch(&mut m, leaf, merges[N - 1]);
            link(&mut m, leaf, merges[N - 1]);
            for i in (1..N).rev() {
                branch(&mut m, merges[i], merges[i - 1]);
                link(&mut m, merges[i], merges[i - 1]);
            }
            branch(&mut m, merges[0], exit);
            link(&mut m, merges[0], exit);
            ret(&mut m, exit);

            let tree = structure_regions(&m, f);
            assert!(tree.errors.is_empty(), "{:?}", tree.errors);
            assert!(tree.root.is_some());
            assert!(tree.loops.is_empty());
            // Every block structured: 2N+2 block-carrying nodes.
            let covered = tree
                .nodes()
                .iter()
                .filter(|n| matches!(n, RegionNode::Block(_) | RegionNode::If { .. }))
                .count();
            assert_eq!(covered, 2 * N + 2);
        })
        .expect("spawn");
    handle
        .join()
        .expect("structuring must not overflow the stack");
}

/// Same guard through the loop-peel path: N nested `while` loops, each
/// level's body being the next inner loop, exits chaining to the outer
/// latch.
#[test]
fn deep_nested_loops_structure_on_small_stack() {
    const N: usize = 400;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut m = mk_module();
            let f = add_func(&mut m);
            let entry = entry_of(&m, f);
            let h: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
            let body = add_block(&mut m, f);
            let latches: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
            let exits: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
            let exit = add_block(&mut m, f);
            branch(&mut m, entry, h[0]);
            link(&mut m, entry, h[0]);
            for i in 0..N - 1 {
                cond_branch(&mut m, h[i], h[i + 1], exits[i]);
                link(&mut m, h[i], h[i + 1]);
                link(&mut m, h[i], exits[i]);
            }
            cond_branch(&mut m, h[N - 1], body, exits[N - 1]);
            link(&mut m, h[N - 1], body);
            link(&mut m, h[N - 1], exits[N - 1]);
            branch(&mut m, body, latches[N - 1]);
            link(&mut m, body, latches[N - 1]);
            for i in 0..N {
                branch(&mut m, latches[i], h[i]);
                link(&mut m, latches[i], h[i]);
            }
            // An exit out of loop i lands on the outer latch (still
            // inside loop i-1's body); the outermost exit returns.
            for i in 1..N {
                branch(&mut m, exits[i], latches[i - 1]);
                link(&mut m, exits[i], latches[i - 1]);
            }
            branch(&mut m, exits[0], exit);
            link(&mut m, exits[0], exit);
            ret(&mut m, exit);

            let tree = structure_regions(&m, f);
            assert!(tree.errors.is_empty(), "{:?}", tree.errors);
            assert!(tree.root.is_some());
            assert_eq!(tree.loops.len(), N);
            // Determinism on the deep shape too.
            assert_eq!(tree, structure_regions(&m, f));
        })
        .expect("spawn");
    handle
        .join()
        .expect("structuring must not overflow the stack");
}

/// Same guard through the TryRegion projection walk: a protected set
/// covering a deeply nested tree makes `walk_region` descend the full
/// tree depth.
#[test]
fn deep_nested_tree_try_projection_on_small_stack() {
    const N: usize = 1000;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut m = mk_module();
            let f = add_func(&mut m);
            let h: Vec<BlockId> = (0..N)
                .map(|i| {
                    if i == 0 {
                        entry_of(&m, f)
                    } else {
                        add_block(&mut m, f)
                    }
                })
                .collect();
            let leaf = add_block(&mut m, f);
            let merges: Vec<BlockId> = (0..N).map(|_| add_block(&mut m, f)).collect();
            let exit = add_block(&mut m, f);
            for i in 0..N - 1 {
                cond_branch(&mut m, h[i], h[i + 1], merges[i]);
                link(&mut m, h[i], h[i + 1]);
                link(&mut m, h[i], merges[i]);
            }
            cond_branch(&mut m, h[N - 1], leaf, merges[N - 1]);
            link(&mut m, h[N - 1], leaf);
            link(&mut m, h[N - 1], merges[N - 1]);
            branch(&mut m, leaf, merges[N - 1]);
            link(&mut m, leaf, merges[N - 1]);
            for i in (1..N).rev() {
                branch(&mut m, merges[i], merges[i - 1]);
                link(&mut m, merges[i], merges[i - 1]);
            }
            branch(&mut m, merges[0], exit);
            link(&mut m, merges[0], exit);
            ret(&mut m, exit);
            // One try region protecting every structured block.
            let handler = add_block(&mut m, f);
            let exc = add_exception_param(&mut m, handler);
            ret(&mut m, handler);
            let protected: Vec<BlockId> = h
                .iter()
                .chain(std::iter::once(&leaf))
                .chain(merges.iter())
                .chain(std::iter::once(&exit))
                .copied()
                .collect();
            add_try(&mut m, f, protected, handler, exc);

            let tree = structure_regions(&m, f);
            assert!(tree.errors.is_empty(), "{:?}", tree.errors);
            assert_eq!(tree.try_plans.len(), 1);
            assert_eq!(tree.try_plans[0].span, tree.root);
        })
        .expect("spawn");
    handle
        .join()
        .expect("projection must not overflow the stack");
}

/// Multi-block single-predecessor return chains (`InLoop -> Ret1 -> Ret2`,
/// as produced by `R2-C1` protected-block splitting) are treated as leaf
/// tails in `loop_merge` rather than poisoning reconvergence at `Merge`.
#[test]
fn loop_merge_ignores_split_return_leaf_chain() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let h = entry_of(&m, f);
    let exit_pre = add_block(&mut m, f);
    let in_loop = add_block(&mut m, f);
    let ret1 = add_block(&mut m, f);
    let ret2 = add_block(&mut m, f);
    let brk = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let merge = add_block(&mut m, f);
    let ret_end = add_block(&mut m, f);

    // Header: `H -> InLoop` (loop body) or `H -> ExitPre -> Merge -> Ret`.
    cond_branch(&mut m, h, in_loop, exit_pre);
    link(&mut m, h, in_loop);
    link(&mut m, h, exit_pre);

    branch(&mut m, exit_pre, merge);
    link(&mut m, exit_pre, merge);

    // InLoop: `InLoop -> Ret1 -> Ret2 (Return)` or `InLoop -> Brk`.
    cond_branch(&mut m, in_loop, brk, ret1);
    link(&mut m, in_loop, brk);
    link(&mut m, in_loop, ret1);

    branch(&mut m, ret1, ret2);
    link(&mut m, ret1, ret2);
    ret(&mut m, ret2);

    // Brk: `Brk -> Merge` (break) or `Brk -> Latch -> H`.
    cond_branch(&mut m, brk, merge, latch);
    link(&mut m, brk, merge);
    link(&mut m, brk, latch);

    branch(&mut m, latch, h);
    link(&mut m, latch, h);

    branch(&mut m, merge, ret_end);
    link(&mut m, merge, ret_end);
    ret(&mut m, ret_end);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(
        tree.escape_hatches.is_empty(),
        "unexpected escape hatches: {:?}",
        tree.escape_hatches
    );
    assert!(
        !tree
            .nodes
            .iter()
            .any(|n| matches!(n, RegionNode::Irreducible { .. })),
        "unexpected Irreducible node in {:?}",
        tree.nodes
    );
}

/// Single-exit `while (true) { if (done) break; } finish1 -> finish2 (Return)`
/// keeps `finish1` as the post-loop continuation (`Seq([Loop, ...])`) rather
/// than absorbing it as an in-loop leaf tail.
#[test]
fn while_true_single_break_chain_stays_post_loop_continuation() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let h = entry_of(&m, f);
    let latch = add_block(&mut m, f);
    let finish1 = add_block(&mut m, f);
    let finish2 = add_block(&mut m, f);

    cond_branch(&mut m, h, finish1, latch);
    link(&mut m, h, finish1);
    link(&mut m, h, latch);

    branch(&mut m, latch, h);
    link(&mut m, latch, h);

    branch(&mut m, finish1, finish2);
    link(&mut m, finish1, finish2);
    ret(&mut m, finish2);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    let root = tree.root.expect("root");
    assert!(
        matches!(tree.node(root), RegionNode::Seq(items) if matches!(tree.node(items[0]), RegionNode::Loop { .. })),
        "expected Seq starting with Loop, got {:?}",
        tree.nodes
    );
}
