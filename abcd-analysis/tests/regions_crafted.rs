//! Crafted-CFG region-structuring arm coverage (c-COV W10): the bail
//! and demote arms the corpus never produces — root multi-entry escape,
//! then/else handler-rejoin demotions, shared-tail plan success and
//! each reachable bail, cross-arm edges, the loop-exit absorption and
//! infinite-loop kind fallback, the `RegionError` reporting arms, and
//! the `walk_region` projection's Loop/If/Irreducible descent. Each
//! test asserts the exact tree shape / escape-hatch / error record.

mod common;

use abcd_analysis::control::{
    EscapeHatch, LoopKind, RegionError, RegionNode, RegionTree, structure_regions,
};
use abcd_ir::{BlockId, FuncId, Module, Op};
use common::*;

/// `cond`-terminated block helper.
fn cond_branch(m: &mut Module, b: BlockId, t: BlockId, f: BlockId) {
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

fn branch(m: &mut Module, b: BlockId, to: BlockId) {
    emit_void(m, b, Op::Branch { dest: to });
}

fn ret(m: &mut Module, b: BlockId) {
    emit_void(m, b, Op::Return { value: None });
}

/// Depth-first collection of the tree's Block leaves.
fn leaf_blocks(tree: &RegionTree) -> Vec<BlockId> {
    let mut out = Vec::new();
    let mut stack = vec![tree.root.expect("root")];
    while let Some(id) = stack.pop() {
        match tree.node(id) {
            RegionNode::Block(b) => out.push(*b),
            RegionNode::Seq(cs) | RegionNode::Alternates(cs) => stack.extend(cs.iter().copied()),
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => stack.push(*body),
            RegionNode::If {
                then, otherwise, ..
            } => {
                stack.extend(then.iter().copied());
                stack.extend(otherwise.iter().copied());
            }
            RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
        }
    }
    out.sort();
    out
}

/// Missing and bodyless functions structure to the empty tree (the
/// `empty` closure and both call sites).
#[test]
fn missing_and_bodyless_functions_structure_empty() {
    let mut m = mk_module();
    let tree = structure_regions(&m, FuncId::new(999));
    assert!(tree.root.is_none());
    assert!(tree.nodes().is_empty());
    assert!(tree.dead_blocks.is_empty());
    assert!(tree.errors.is_empty());

    // A function record with no blocks at all (external-style).
    let f = add_external_func(&mut m, "nobody");
    let tree = structure_regions(&m, f);
    assert!(tree.root.is_none());
    assert!(tree.dead_blocks.is_empty());
    assert!(tree.errors.is_empty());
}

/// An infinite loop with no exit on header or latch still structures;
/// the kind falls back to `While`.
#[test]
fn infinite_loop_structures_as_while() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let b = add_block(&mut m, f);
    branch(&mut m, entry, b);
    branch(&mut m, b, entry);
    link(&mut m, entry, b);
    link(&mut m, b, entry);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.loops.len(), 1);
    assert_eq!(tree.loops[0].kind, LoopKind::While);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
}

/// Loop-exit-tail absorption: the break/else tails whose in-set
/// predecessors are all in the body are absorbed into the loop region
/// before the continuation is structured.
///
/// `entry -> h ->{b | X}; b ->{t1 | t2}; t1 -> h; t2 -> out; X -> out;
/// out -> ret`. The loop's merge is `out`; the exit tails `t2` and then
/// `X` are absorbed.
#[test]
fn loop_exit_tails_are_absorbed() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let t1 = add_block(&mut m, f);
    let t2 = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let out = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, b, x);
    cond_branch(&mut m, b, t1, t2);
    branch(&mut m, t1, h);
    branch(&mut m, t2, out);
    branch(&mut m, x, out);
    branch(&mut m, out, ret_b);
    ret(&mut m, ret_b);
    for (u, v) in [
        (entry, h),
        (h, b),
        (h, x),
        (b, t1),
        (b, t2),
        (t1, h),
        (t2, out),
        (x, out),
        (out, ret_b),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
    assert_eq!(tree.loops.len(), 1);
    // The loop FOREST records the natural loop only; the exit-tail
    // absorption lives in the region tree: the Loop node's body covers
    // the tail blocks t2 and x too.
    let mut forest = tree.loops[0].blocks.clone();
    forest.sort();
    let mut want_forest = vec![h, b, t1];
    want_forest.sort();
    assert_eq!(forest, want_forest, "the natural loop");
    let loop_node = tree
        .nodes()
        .iter()
        .find(|n| matches!(n, RegionNode::Loop { header, .. } if *header == h))
        .expect("the loop node");
    let mut region_body = leaf_blocks_from(&tree, loop_node);
    region_body.sort();
    let mut want = vec![h, b, t1, t2, x];
    want.sort();
    assert_eq!(
        region_body, want,
        "the exit tails were absorbed into the loop's region body"
    );
    // Both exit targets were absorbed, so no header/latch exit remains:
    // the kind falls back to While.
    assert_eq!(tree.loops[0].kind, LoopKind::While);
}

/// The Block leaves under a region node.
fn leaf_blocks_from(tree: &RegionTree, node: &RegionNode) -> Vec<BlockId> {
    let mut out = Vec::new();
    let mut stack: Vec<RegionNode> = vec![node.clone()];
    while let Some(n) = stack.pop() {
        match &n {
            RegionNode::Block(b) => out.push(*b),
            RegionNode::Seq(cs) | RegionNode::Alternates(cs) => {
                stack.extend(cs.iter().map(|&c| tree.node(c).clone()));
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                stack.push(tree.node(*body).clone());
            }
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => {
                out.push(*head);
                stack.extend(then.iter().map(|&c| tree.node(c).clone()));
                stack.extend(otherwise.iter().map(|&c| tree.node(c).clone()));
            }
            RegionNode::Irreducible { blocks, .. } => out.extend(blocks.iter().copied()),
        }
    }
    out
}

/// An arm-internal block with a predecessor in the CONTINUATION (an
/// irreducible jump-into-the-arm shape): the arm's `start_set` sees a
/// second entry and escapes.
///
/// `entry ->{t | f}; t -> x; x -> join; f -> join; join ->{x | out}`:
/// `x` belongs to the then arm but is also reached from the merge.
#[test]
fn arm_internal_multi_entry_escapes() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let fb = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let out = add_block(&mut m, f);
    cond_branch(&mut m, entry, t, fb);
    branch(&mut m, t, x);
    branch(&mut m, x, join);
    branch(&mut m, fb, join);
    cond_branch(&mut m, join, x, out);
    ret(&mut m, out);
    for (u, v) in [
        (entry, t),
        (entry, fb),
        (t, x),
        (x, join),
        (fb, join),
        (join, x),
        (join, out),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    let hatch = tree
        .escape_hatches
        .iter()
        .find_map(|e| match e {
            EscapeHatch::MultiEntry { blocks, entries } => Some((blocks.clone(), entries.clone())),
            _ => None,
        })
        .expect("the arm's second entry escapes");
    assert_eq!(hatch.1, vec![x], "the continuation-reached arm block");
    let mut want = vec![t, x];
    want.sort();
    assert_eq!(hatch.0, want);
    // The {x, join} cycle (no dominance back edge) is irreducible.
    assert!(
        !tree.irreducible.is_empty(),
        "the cross cycle is an irreducible core: {:?}",
        tree.irreducible
    );
}

/// The handler-rejoin demotion (N76), THEN-arm side: the false-side
/// entry carries a Normal pred from outside the universe, so the then
/// arm is the only conditional arm and the false side becomes the
/// continuation.
#[test]
fn handler_rejoin_demotes_then_side() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let fb = add_block(&mut m, f);
    let g = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    let dead = add_block(&mut m, f);
    cond_branch(&mut m, entry, t, fb);
    ret(&mut m, t); // the then side leaves the region: no merge
    branch(&mut m, fb, g);
    branch(&mut m, g, ret_b);
    ret(&mut m, ret_b);
    ret(&mut m, dead);
    link(&mut m, entry, t);
    link(&mut m, entry, fb);
    link(&mut m, fb, g);
    link(&mut m, g, ret_b);
    // The handler-side rejoin edge onto the FALSE arm entry.
    link(&mut m, dead, fb);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(tree.escape_hatches.is_empty(), "{:?}", tree.escape_hatches);
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
    assert_eq!(then.map(|r| tree.node(r)), Some(&RegionNode::Block(t)));
    assert_eq!(*otherwise, None, "the false side was demoted");
    assert_eq!(*merge, None);
    // The demoted side heads the continuation.
    let RegionNode::Seq(cont) = tree.node(items[1]) else {
        panic!("continuation must be Seq: {:?}", tree.node(items[1]));
    };
    assert_eq!(tree.node(cont[0]), &RegionNode::Block(fb));
}

/// The mirror image: the TRUE-side entry carries the external pred, so
/// the else arm is the conditional arm.
#[test]
fn handler_rejoin_demotes_else_side() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let fb = add_block(&mut m, f);
    let g = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    let dead = add_block(&mut m, f);
    cond_branch(&mut m, entry, t, fb);
    branch(&mut m, t, g);
    branch(&mut m, g, ret_b);
    ret(&mut m, ret_b);
    ret(&mut m, fb); // the false side leaves the region
    ret(&mut m, dead);
    link(&mut m, entry, t);
    link(&mut m, entry, fb);
    link(&mut m, t, g);
    link(&mut m, g, ret_b);
    link(&mut m, dead, t); // the external pred on the TRUE entry

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
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
    assert_eq!(*then, None, "the true side was demoted");
    assert_eq!(
        otherwise.map(|r| tree.node(r)),
        Some(&RegionNode::Block(fb))
    );
    assert_eq!(*merge, None);
    let RegionNode::Seq(cont) = tree.node(items[1]) else {
        panic!("continuation must be Seq: {:?}", tree.node(items[1]));
    };
    assert_eq!(tree.node(cont[0]), &RegionNode::Block(t));
}

/// The cross-arm hint: an arm's edge into the sibling arm's entry (the
/// es2abc `if (c) goto shared; …` idiom).
///
/// `entry ->{A | B}; A ->{B | q}; q -> m; B -> m; m -> ret`.
#[test]
fn cross_arm_edge_is_recorded() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let q = add_block(&mut m, f);
    let mm = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    cond_branch(&mut m, entry, a, b);
    cond_branch(&mut m, a, b, q);
    branch(&mut m, q, mm);
    branch(&mut m, b, mm);
    branch(&mut m, mm, ret_b);
    ret(&mut m, ret_b);
    for (u, v) in [
        (entry, a),
        (entry, b),
        (a, b),
        (a, q),
        (q, mm),
        (b, mm),
        (mm, ret_b),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(
        tree.cross_arm_edges.contains(&(a, b)),
        "the goto-sibling edge is recorded: {:?}",
        tree.cross_arm_edges
    );
}

/// The shared-tail decomposition SUCCEEDS: a merge-less conditional
/// whose arms reconverge on a shared tail through two overlapping
/// entries (the es2abc switch fall-through shape).
///
/// `entry ->{A | B}; A ->{u1 | u2}; B ->{u1 | u2}; u1 -> t; u2 -> t;
/// t -> ret`.
#[test]
fn shared_tail_plan_succeeds() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let u1 = add_block(&mut m, f);
    let u2 = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    cond_branch(&mut m, entry, a, b);
    cond_branch(&mut m, a, u1, u2);
    cond_branch(&mut m, b, u1, u2);
    branch(&mut m, u1, t);
    branch(&mut m, u2, t);
    branch(&mut m, t, ret_b);
    ret(&mut m, ret_b);
    for (x, y) in [
        (entry, a),
        (entry, b),
        (a, u1),
        (a, u2),
        (b, u1),
        (b, u2),
        (u1, t),
        (u2, t),
        (t, ret_b),
    ] {
        link(&mut m, x, y);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(
        tree.escape_hatches.is_empty(),
        "the tail plan succeeds: {:?}",
        tree.escape_hatches
    );
    // Find the Alternates node: tail arm first, then one arm per
    // non-empty exclusive prefix.
    let alternates = tree
        .nodes()
        .iter()
        .find_map(|n| match n {
            RegionNode::Alternates(arms) => Some(arms.clone()),
            _ => None,
        })
        .expect("the shared-tail alternates");
    assert_eq!(alternates.len(), 3);
    let labels: Vec<BlockId> = alternates
        .iter()
        .map(|&r| match tree.node(r) {
            RegionNode::Labeled { label, .. } => *label,
            other => panic!("arm must be Labeled: {other:?}"),
        })
        .collect();
    assert_eq!(labels[0], t, "the tail arm comes first");
    let mut prefix_labels = labels[1..].to_vec();
    prefix_labels.sort();
    let mut want = vec![u1, u2];
    want.sort();
    assert_eq!(prefix_labels, want);
    // Totality: every non-head block is a leaf under the alternates
    // (the entry is the If's head, carried not wrapped).
    let mut all = vec![a, b, u1, u2, t, ret_b];
    all.sort();
    assert_eq!(leaf_blocks(&tree), all);
}

/// The shared-tail bail: TWO distinct tail blocks are targeted by
/// edges from outside the tail (a prefix block jumps past the tail
/// entry). The continuation escapes as MultiEntry.
///
/// Loop `h <-> body` with exits to X (from h) and Y (from body);
/// `X -> p; X -> p is the only X succ; p ->{T | rt}; Y ->{T | ry};
/// T -> rt; rx/ry/rt return`. Tail = {T, rt}; `p -> rt` lands mid-tail.
#[test]
fn shared_tail_multi_entry_tail_bails() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let y = add_block(&mut m, f);
    let p = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let rt = add_block(&mut m, f);
    let ry = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, body, x);
    cond_branch(&mut m, body, h, y);
    branch(&mut m, x, p);
    cond_branch(&mut m, p, t, rt);
    cond_branch(&mut m, y, t, ry);
    branch(&mut m, t, rt);
    ret(&mut m, rt);
    ret(&mut m, ry);
    for (u, v) in [
        (entry, h),
        (h, body),
        (h, x),
        (body, h),
        (body, y),
        (x, p),
        (p, t),
        (p, rt),
        (y, t),
        (y, ry),
        (t, rt),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.loops.len(), 1);
    let hatch = tree
        .escape_hatches
        .iter()
        .find_map(|e| match e {
            EscapeHatch::MultiEntry { entries, .. } => Some(entries.clone()),
            _ => None,
        })
        .expect("the mid-tail edge bails to MultiEntry");
    assert_eq!(hatch, vec![x, y]);
}

/// The shared-tail bail: the exclusive prefixes OVERLAP (a block is
/// reachable from two entries but is not in the common tail).
///
/// Loop `h -> body | X1; body -> b2 | X2; b2 -> h | X3` (latch `b2`).
/// `X1 -> X2` pins X2 against absorption; `X1 ->{X2 | r1};
/// X2 ->{t | r2}; X3 ->{mm | r3}; mm -> t`: `X2` is reachable from BOTH
/// X1 and X2 but not from X3 — an overlapping prefix, not tail.
#[test]
fn shared_tail_overlapping_prefixes_bail() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let x1 = add_block(&mut m, f);
    let x2 = add_block(&mut m, f);
    let x3 = add_block(&mut m, f);
    let mm = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let r1 = add_block(&mut m, f);
    let r2 = add_block(&mut m, f);
    let r3 = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, body, x1);
    cond_branch(&mut m, body, b2, x2);
    cond_branch(&mut m, b2, h, x3);
    cond_branch(&mut m, x1, x2, r1);
    cond_branch(&mut m, x2, t, r2);
    cond_branch(&mut m, x3, mm, r3);
    branch(&mut m, mm, t);
    ret(&mut m, t);
    ret(&mut m, r1);
    ret(&mut m, r2);
    ret(&mut m, r3);
    for (u, v) in [
        (entry, h),
        (h, body),
        (h, x1),
        (body, b2),
        (body, x2),
        (b2, h),
        (b2, x3),
        (x1, x2),
        (x1, r1),
        (x2, t),
        (x2, r2),
        (x3, mm),
        (x3, r3),
        (mm, t),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    let hatch = tree
        .escape_hatches
        .iter()
        .find_map(|e| match e {
            EscapeHatch::MultiEntry { entries, .. } => Some(entries.clone()),
            _ => None,
        })
        .expect("the overlapping prefixes bail to MultiEntry");
    assert_eq!(hatch, vec![x1, x2, x3]);
}

/// The shared-tail fold-compatibility bail: an arm entry's predecessor
/// belongs to a loop not wholly inside the set (the loop-exit shape the
/// vendor-machinery folds pattern-match).
///
/// Loop `h <-> body`, exits to X (from h) and Y (from body);
/// `X ->{p | rx}; Y ->{T | ry}; p -> T; T -> rt; rx/ry/rt return`.
/// The plan's preconditions all pass except the loop-pred rule.
#[test]
fn shared_tail_loop_pred_bails() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let y = add_block(&mut m, f);
    let p = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let rt = add_block(&mut m, f);
    let rx = add_block(&mut m, f);
    let ry = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, body, x);
    cond_branch(&mut m, body, h, y);
    cond_branch(&mut m, x, p, rx);
    cond_branch(&mut m, y, t, ry);
    branch(&mut m, p, t);
    branch(&mut m, t, rt);
    ret(&mut m, rt);
    ret(&mut m, rx);
    ret(&mut m, ry);
    for (u, v) in [
        (entry, h),
        (h, body),
        (h, x),
        (body, h),
        (body, y),
        (x, p),
        (x, rx),
        (y, t),
        (y, ry),
        (p, t),
        (t, rt),
    ] {
        link(&mut m, u, v);
    }

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.loops.len(), 1);
    let hatch = tree
        .escape_hatches
        .iter()
        .find_map(|e| match e {
            EscapeHatch::MultiEntry { entries, .. } => Some(entries.clone()),
            _ => None,
        })
        .expect("the loop-pred bail escapes to MultiEntry");
    assert_eq!(hatch, vec![x, y]);
}

/// A catch handler inside its own protected set is a hard error
/// (reported, never panicked).
#[test]
fn handler_inside_protected_is_an_error() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let handler = add_block(&mut m, f);
    branch(&mut m, entry, handler);
    ret(&mut m, handler);
    link(&mut m, entry, handler);
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![entry, handler], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(
        tree.errors
            .iter()
            .any(|e| matches!(e, RegionError::HandlerInsideProtected { region: 0, handler: h } if *h == handler)),
        "{:?}",
        tree.errors
    );
}

/// A protected Normal-connected component with two Normal entries is a
/// hard error, and its plan carries no surface entry.
#[test]
fn try_region_multiple_entries_is_an_error() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    cond_branch(&mut m, entry, b1, b2);
    branch(&mut m, b1, b2);
    branch(&mut m, b2, ret_b);
    ret(&mut m, ret_b);
    ret(&mut m, handler);
    link(&mut m, entry, b1);
    link(&mut m, entry, b2);
    link(&mut m, b1, b2);
    link(&mut m, b2, ret_b);
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![b1, b2], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(
        tree.errors.iter().any(|e| matches!(
            e,
            RegionError::TryMultipleEntries { region: 0, entries } if entries == &vec![b1, b2]
        )),
        "{:?}",
        tree.errors
    );
    assert_eq!(tree.try_plans.len(), 1);
    assert_eq!(
        tree.try_plans[0].entry, None,
        "no single surface entry on the error shape"
    );
}

/// The tree-projection walk descends Loop / If / Irreducible nodes:
/// a protected set partially covering a Loop or Irreducible node sets
/// `cuts_structured_region`; one inside an If records the If as span.
#[test]
fn try_projection_walks_loop_if_and_irreducible_nodes() {
    // (a) Loop cut: protect the header but not the latch.
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let out = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    branch(&mut m, entry, h);
    cond_branch(&mut m, h, b, out);
    branch(&mut m, b, h);
    ret(&mut m, out);
    ret(&mut m, handler);
    link(&mut m, entry, h);
    link(&mut m, h, b);
    link(&mut m, h, out);
    link(&mut m, b, h);
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![h], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert_eq!(tree.try_plans.len(), 1);
    assert!(
        tree.try_plans[0].cuts_structured_region,
        "the protected set cuts the Loop node: {:?}",
        tree.try_plans[0]
    );

    // (b) If span: protect the head and the then arm of a diamond.
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    cond_branch(&mut m, entry, a, b);
    branch(&mut m, a, join);
    branch(&mut m, b, join);
    ret(&mut m, join);
    ret(&mut m, handler);
    link(&mut m, entry, a);
    link(&mut m, entry, b);
    link(&mut m, a, join);
    link(&mut m, b, join);
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![entry, a], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    let span = tree.try_plans[0].span.expect("a span");
    assert!(
        matches!(tree.node(span), RegionNode::If { .. }),
        "the smallest node covering the protected set is the If: {:?}",
        tree.node(span)
    );

    // (c) Irreducible cut: protect one block of a collapsed arm (the
    // `arm_internal_multi_entry_escapes` shape: `entry ->{t | fb};
    // t -> x; x -> join; fb -> join; join ->{x | out}` — the then arm
    // {t, x} collapses to an Irreducible node).
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let fb = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let out = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    cond_branch(&mut m, entry, t, fb);
    branch(&mut m, t, x);
    branch(&mut m, x, join);
    branch(&mut m, fb, join);
    cond_branch(&mut m, join, x, out);
    ret(&mut m, out);
    ret(&mut m, handler);
    for (u, v) in [
        (entry, t),
        (entry, fb),
        (t, x),
        (x, join),
        (fb, join),
        (join, x),
        (join, out),
    ] {
        link(&mut m, u, v);
    }
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![t], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    assert!(
        tree.try_plans[0].cuts_structured_region,
        "the protected set cuts the Irreducible node: {:?}",
        tree.try_plans[0]
    );
}

/// The demote FILTER's refusal: the demote candidate's arm has an exit
/// landing PAST the demoted entry (but inside the region) — the
/// `if (c) { arm } <continuation>` shape cannot express it, so the
/// conditional structures normally (both arms present).
///
/// `entry ->{t | f}; t ->{x | y}; x -> ret1; y -> g; f -> g; g -> ret2`
/// with a dead edge into `f` (the handler-rejoin marker). The arm's
/// exit `y -> g` lands mid-continuation.
#[test]
fn demote_filter_refuses_past_entry_exits() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let y = add_block(&mut m, f);
    let fb = add_block(&mut m, f);
    let g = add_block(&mut m, f);
    let ret1 = add_block(&mut m, f);
    let ret2 = add_block(&mut m, f);
    let dead = add_block(&mut m, f);
    cond_branch(&mut m, entry, t, fb);
    cond_branch(&mut m, t, x, y);
    ret(&mut m, x);
    branch(&mut m, y, g);
    branch(&mut m, fb, g);
    branch(&mut m, g, ret2);
    ret(&mut m, ret1);
    ret(&mut m, ret2);
    ret(&mut m, dead);
    for (u, v) in [
        (entry, t),
        (entry, fb),
        (t, x),
        (t, y),
        (y, g),
        (fb, g),
        (g, ret2),
    ] {
        link(&mut m, u, v);
    }
    // The handler-side rejoin edge onto the FALSE entry.
    link(&mut m, dead, fb);

    let tree = structure_regions(&m, f);
    assert!(tree.errors.is_empty(), "{:?}", tree.errors);
    // No demotion: the If keeps BOTH arms.
    let RegionNode::Seq(items) = tree.root_node().unwrap() else {
        panic!("root must be Seq: {:?}", tree.root_node());
    };
    let RegionNode::If {
        head,
        then,
        otherwise,
        ..
    } = tree.node(items[0])
    else {
        panic!("first item must be If: {:?}", tree.node(items[0]));
    };
    assert_eq!(*head, entry);
    assert!(then.is_some() && otherwise.is_some(), "no side was demoted");
}

/// A protected Normal-connected component with ZERO Normal entries (a
/// dispatch-entered handler-side sub-CFG) is NOT an error — its plan
/// entry falls back to the component's first block.
#[test]
fn try_region_zero_entry_component_is_not_an_error() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let a = add_block(&mut m, f);
    let ret_b = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let dead = add_block(&mut m, f);
    branch(&mut m, entry, a);
    branch(&mut m, a, ret_b);
    ret(&mut m, ret_b);
    ret(&mut m, handler);
    ret(&mut m, dead);
    link(&mut m, entry, a);
    link(&mut m, a, ret_b);
    let exc = add_exception_param(&mut m, handler);
    // protected[0] is the dead block: a zero-Normal-entry component.
    add_try(&mut m, f, vec![dead, a], handler, exc);

    let tree = structure_regions(&m, f);
    assert!(
        !tree
            .errors
            .iter()
            .any(|e| matches!(e, RegionError::TryMultipleEntries { .. })),
        "a zero-entry component is not a violation: {:?}",
        tree.errors
    );
    assert_eq!(
        tree.try_plans[0].entry,
        Some(dead),
        "the plan entry is the component's first block"
    );
}
