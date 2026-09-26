//! Shared helpers for the root package's cross-crate integration suites
//! (`tests/<flow>/`), adapted from the crate-local `tests/common/mod.rs`
//! files of abcd-analysis / abcd-taint / abcd-decompile (the abcd-lower
//! and abcd-opt commons serve only in-crate L1 tests and stay put).
//!
//! - Corpus harness (`corpus_root` / `manifest_paths` /
//!   `runtime_passed_paths` / `lift_fixture`): the exported GHCR corpus +
//!   python3 manifest pattern, deduplicated — the crate-local copies were
//!   identical modulo the runtime-passed filter. Because the root
//!   package's `CARGO_MANIFEST_DIR` IS the repo root, the crate-local
//!   `../exports/corpus` fallback resolves here as `exports/corpus`.
//! - The dominator-agreement reference (`verify_reference_dom_sets` /
//!   `check_function`): a VERBATIM port of `abcd-ir/src/verify.rs`'s
//!   private iterative dominator computation (`verify_dominance`, the N45
//!   check), from abcd-analysis's common. `abcd-ir` cannot depend on
//!   `abcd-analysis` (one-way layering), so the pin between the two
//!   implementations lives here.
//! - Hand-built IR module scaffolding: the abcd-taint and abcd-decompile
//!   commons each carry a scaffolding set that LOOKS similar but diverges
//!   semantically (`add_param`'s arity; `add`'s operand order — the
//!   decompile one encodes the N36 acc/vreg swap), so they are kept as
//!   two verbatim submodules rather than falsely deduplicated:
//!   [`taint_scaffold`] (used by `tests/lift-taint/probes.rs`) and
//!   [`decompile_scaffold`] (used by `tests/lift-decompile/async_node.rs`).

// Each test target uses a different subset.
#![allow(dead_code)]

pub mod decompile_scaffold;
pub mod taint_scaffold;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use abcd_analysis::control::Dominators;
use abcd_ir::{BlockId, EdgeKind, FuncId, Module};

/// The corpus root: `$ABCD_CORPUS_ROOT` or `exports/corpus` (the root
/// package's manifest dir is the repo root).
pub fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"))
}

/// Every fixture path in the manifest (all 5517 rows, sorted for
/// determinism), parsed with python3's standard JSON library.
pub fn manifest_paths(root: &Path) -> Vec<String> {
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

/// The non-test262 fixture paths (2832 rows: the project + upstream
/// corpus plus the gen-opcode fixtures, sorted for determinism).
///
/// The Stage-A/Stage-B decompile corpus gates are scoped to this set
/// (c-P3): test262 decompile is a later phase per
/// `design/test262-feasibility.md`, so the 2685 compiled test262 rows
/// gate lift+verify (`tests/file-lift`) only.
pub fn project_manifest_paths(root: &Path) -> Vec<String> {
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
        if row["origin"]["kind"] == "test262":
            continue
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

/// The 1149 runtime-passed fixture paths (sorted for determinism),
/// parsed with python3's standard JSON library.
pub fn runtime_passed_paths(root: &Path) -> Vec<String> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        if row["runtime"]["status"] == "passed":
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

/// Decode + lift one corpus fixture to a module.
pub fn lift_fixture(root: &Path, relative: &str) -> Module {
    let data = std::fs::read(root.join(relative)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    abcd_lift::lift_file(&file).expect("lift fixture")
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
