//! Opt-in corpus agreement test (gate 5): `abcd_analysis::control::
//! Dominators` must agree with `abcd_ir::verify`'s PRIVATE minimal
//! dominator computation (the N45 check) on every corpus function.
//!
//! Layering is one-way (`abcd-ir` never depends on `abcd-analysis`), so
//! the verifier keeps its own implementation; this test is the pin
//! between the two. The reference below is a VERBATIM port of the
//! verifier's iterative set-based algorithm (abcd-ir/src/verify.rs,
//! `verify_dominance`), reading the same stored
//! [`EdgeKind::Normal`] predecessors. The contract (also documented in
//! `abcd_analysis::control`'s module docs):
//!
//! > Over all blocks with a Normal-edge path from the entry, the two
//! > implementations compute the same dominator SETS.
//!
//! Blocks without such a path are excluded: the verifier's iterative sets
//! degenerate there (an unreachable Normal-edge cycle keeps the initial
//! "everything" set), while `Dominators` reports unreachable blocks as
//! dominated only by themselves — both are dead-code cases the verifier
//! exempts from N45 anyway.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-analysis --test corpus_dom_agreement --release -- --ignored
//! ```

mod common;

use std::collections::{HashMap, HashSet};

use abcd_analysis::control::Dominators;
use abcd_ir::{BlockId, EdgeKind, FuncId, Module};
use abcd_lift::lift_file;

/// Verbatim port of abcd-ir/src/verify.rs's iterative dominator sets over
/// the Normal-edge CFG (stored predecessors). Returns, per
/// `func.blocks` index, that block's dominator set as block indices.
fn verify_reference_dom_sets(module: &Module, func_id: FuncId) -> Vec<HashSet<usize>> {
    let func = module.func(func_id).expect("function");
    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    let n = func.blocks.len();
    let entry_i = 0usize;

    // Normal-edge predecessors per block (in-function only).
    let mut npreds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let i = index[&bb];
        for edge in &block.preds {
            if edge.kind == EdgeKind::Normal {
                if let Some(&p) = index.get(&edge.from) {
                    npreds[i].push(p);
                }
            }
        }
    }

    // Iterative dominator sets over the Normal-edge CFG.
    let all: HashSet<usize> = (0..n).collect();
    let mut dom: Vec<HashSet<usize>> = vec![all; n];
    dom[entry_i] = HashSet::from([entry_i]);
    loop {
        let mut changed = false;
        for i in 0..n {
            if i == entry_i {
                continue;
            }
            let mut new: HashSet<usize> = if npreds[i].is_empty() {
                HashSet::new()
            } else {
                let mut acc = dom[npreds[i][0]].clone();
                for &p in &npreds[i][1..] {
                    acc = acc.intersection(&dom[p]).copied().collect();
                }
                acc
            };
            new.insert(i);
            if new != dom[i] {
                dom[i] = new;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    dom
}

/// Check one function: agreement over all Normal-reachable blocks.
fn check_function(module: &Module, func_id: FuncId) -> (usize, usize) {
    let func = module.func(func_id).expect("function");
    if func.blocks.is_empty() {
        return (0, 0);
    }
    let index_of = |b: BlockId| {
        func.blocks
            .iter()
            .position(|&x| x == b)
            .expect("in-function")
    };

    // The shared relation: Normal-edge successors = inverse of the stored
    // Normal predecessors (in-function only). Both implementations see
    // exactly this graph.
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for edge in &block.preds {
            if edge.kind == EdgeKind::Normal && func.blocks.contains(&edge.from) {
                succs.entry(edge.from).or_default().push(bb);
            }
        }
    }
    let succ_of = |b: BlockId| succs.get(&b).cloned().unwrap_or_default();

    let dom = Dominators::over(module, func_id, &succ_of);
    let reference = verify_reference_dom_sets(module, func_id);
    let entry = func.blocks[0];

    // The agreement domain: blocks reachable from the entry over the
    // Normal relation (BFS). For these, the verifier's `dom[i]` contains
    // the entry and equals the tree-derived dominator set.
    let reachable = abcd_analysis::control::reachable_blocks(module, func_id, &succ_of);

    let mut compared = 0usize;
    for &b in &reachable {
        let i = index_of(b);
        let reference_set: std::collections::BTreeSet<BlockId> =
            reference[i].iter().map(|&j| func.blocks[j]).collect();
        let mine: std::collections::BTreeSet<BlockId> =
            dom.dominator_chain(b).into_iter().collect();
        assert_eq!(
            mine, reference_set,
            "dominator-set disagreement in {func_id:?} block {b:?} (entry {entry:?})"
        );
        compared += 1;
    }
    (compared, func.blocks.len())
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn dominators_agree_with_verifier_on_corpus() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut blocks_compared = 0usize;
    let mut blocks_total = 0usize;

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;
        for fi in 0..module.functions.len() {
            let (compared, total) = check_function(&module, FuncId::new(fi as u32));
            functions += 1;
            blocks_compared += compared;
            blocks_total += total;
        }
    }

    eprintln!(
        "DOM-AGREEMENT fixtures={fixtures} functions={functions} \
         blocks_compared={blocks_compared} blocks_total={blocks_total}"
    );
    assert!(blocks_compared > 0);
}
