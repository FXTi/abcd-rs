//! Shared helpers for `abcd-analysis` corpus/integration tests.
//!
//! - Corpus harness (`corpus_root` / `manifest_paths`): the exported GHCR
//!   corpus + python3 manifest pattern of
//!   `abcd-lift/tests/corpus_lift_verify.rs`.
//! - The dominator-agreement reference (`verify_reference_dom_sets` /
//!   `check_function`): a VERBATIM port of `abcd-ir/src/verify.rs`'s
//!   private iterative dominator computation (`verify_dominance`, the N45
//!   check). `abcd-ir` cannot depend on `abcd-analysis` (one-way
//!   layering), so the pin between the two implementations lives here.

// Each test binary uses a different subset.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::process::Command;

use abcd_analysis::control::Dominators;
use abcd_ir::{BlockId, EdgeKind, FuncId, Module};

/// The corpus root: `$ABCD_CORPUS_ROOT` or `exports/corpus`.
pub fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

/// Every fixture path in the manifest (all 5517 rows, sorted for
/// determinism), parsed with python3's standard JSON library.
pub fn manifest_paths(root: &PathBuf) -> Vec<String> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        assert "\n" not in row["abc"] and "\t" not in row["abc"]
        paths.append(row["abc"])
for path in sorted(paths):
    print(path)
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 fixture paths")
        .lines()
        .map(str::to_string)
        .collect()
}

/// Verbatim port of abcd-ir/src/verify.rs's iterative dominator sets over
/// the Normal-edge CFG (stored predecessors). Returns, per
/// `func.blocks` index, that block's dominator set as block indices.
pub fn verify_reference_dom_sets(module: &Module, func_id: FuncId) -> Vec<HashSet<usize>> {
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

/// Check one function: the dominance agreement contract (also documented
/// in `abcd_analysis::control`'s module docs) — over all blocks BOTH
/// implementations consider Normal-reachable (reachable from the entry in
/// `Dominators`' tree AND containing the entry in the verifier's
/// `dom[b]`), the two compute the same dominator SETS.
///
/// Two documented divergence classes are excluded (both dead-code shapes
/// the verifier's N45 check exempts anyway):
///
/// 1. Unreachable Normal-edge cycles keep the verifier's initial
///    "everything" set (so they look entry-dominated) while the tree
///    reports them unreachable.
/// 2. A reachable block with an unreachable Normal predecessor is
///    *polluted* by the verifier's all-set initialization: the
///    intersection with the dead predecessor's degenerate set empties it,
///    so the verifier treats the block as unreachable; the CHK tree
///    computes dominators on the reachable subgraph (the graph-theoretic
///    answer). The divergence always weakens the verifier's check, never
///    strengthens it, and `abcd-ir` is frozen for this task — so the
///    contract is the intersection domain.
///
/// Returns `(blocks compared, blocks skipped by divergence, blocks total)`.
pub fn check_function(module: &Module, func_id: FuncId, ctx: &str) -> (usize, usize, usize) {
    let func = module.func(func_id).expect("function");
    if func.blocks.is_empty() {
        return (0, 0, 0);
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
    let mut skipped = 0usize;
    let entry_i = 0usize;
    for &b in &reachable {
        let i = index_of(b);
        // Divergence classes (see the contract above): skip blocks the
        // verifier's sets treat as unreachable despite the tree reaching
        // them.
        if !reference[i].contains(&entry_i) {
            skipped += 1;
            continue;
        }
        let reference_set: std::collections::BTreeSet<BlockId> =
            reference[i].iter().map(|&j| func.blocks[j]).collect();
        let mine: std::collections::BTreeSet<BlockId> =
            dom.dominator_chain(b).into_iter().collect();
        assert_eq!(
            mine, reference_set,
            "dominator-set disagreement in {ctx} {func_id:?} block {b:?} (entry {entry:?})"
        );
        compared += 1;
    }
    (compared, skipped, func.blocks.len())
}
