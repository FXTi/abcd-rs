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
//! cargo test -p abcd-rs --test lift-analysis --release -- --ignored corpus_dom_agreement
//! ```
//!
//! Migrated from `abcd-analysis/tests/corpus_dom_agreement.rs` to the
//! root package's `tests/lift-analysis/` target; the shared helpers
//! moved to the root package's `tests/common/`.

use crate::common;

use abcd_ir::FuncId;
use abcd_lift::lift_file;
use rayon::prelude::*;

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn dominators_agree_with_verifier_on_corpus() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 5517, "expected the full 5517-fixture corpus");

    // Parallel per-fixture agreement checks (rayon); the per-fixture
    // (functions, compared, skipped, total) counts sum
    // order-independently, and the in-check assertions fail the gate on
    // any disagreement regardless of scheduling.
    let (functions, blocks_compared, blocks_skipped, blocks_total) = paths
        .par_iter()
        .map(|relative| {
            let data = std::fs::read(root.join(relative)).expect("read fixture");
            let file = abcd_file::decode(&data).expect("decode fixture");
            let module = lift_file(&file).expect("lift fixture");
            let mut functions = 0usize;
            let mut compared = 0usize;
            let mut skipped = 0usize;
            let mut total = 0usize;
            for fi in 0..module.functions.len() {
                let (c, s, t) = common::check_function(&module, FuncId::new(fi as u32), relative);
                functions += 1;
                compared += c;
                skipped += s;
                total += t;
            }
            (functions, compared, skipped, total)
        })
        .reduce(
            || (0, 0, 0, 0),
            |(a1, b1, c1, d1), (a2, b2, c2, d2)| (a1 + a2, b1 + b2, c1 + c2, d1 + d2),
        );
    let fixtures = paths.len();

    eprintln!(
        "DOM-AGREEMENT fixtures={fixtures} functions={functions} \
         blocks_compared={blocks_compared} blocks_skipped={blocks_skipped} \
         blocks_total={blocks_total}"
    );
    assert!(blocks_compared > 0);
}
