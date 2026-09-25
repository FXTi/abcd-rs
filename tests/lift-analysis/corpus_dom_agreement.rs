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

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn dominators_agree_with_verifier_on_corpus() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut blocks_compared = 0usize;
    let mut blocks_skipped = 0usize;
    let mut blocks_total = 0usize;

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;
        for fi in 0..module.functions.len() {
            let (compared, skipped, total) =
                common::check_function(&module, FuncId::new(fi as u32), relative);
            functions += 1;
            blocks_compared += compared;
            blocks_skipped += skipped;
            blocks_total += total;
        }
    }

    eprintln!(
        "DOM-AGREEMENT fixtures={fixtures} functions={functions} \
         blocks_compared={blocks_compared} blocks_skipped={blocks_skipped} \
         blocks_total={blocks_total}"
    );
    assert!(blocks_compared > 0);
}
