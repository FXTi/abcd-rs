//! Opt-in corpus frequency counter for global-name call sites — the
//! evidence base for the top-20 builtin summary set (task §5: "count
//! global-name call sites across the corpus and take the top ~20").
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-taint --test corpus_callee_names --release -- --ignored
//! ```

mod common;

use abcd_ir::Op;
use abcd_taint::names::callee_name_candidates;

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn callee_name_frequency() {
    let root = common::corpus_root();
    let paths = common::runtime_passed_paths(&root);
    assert_eq!(
        paths.len(),
        1149,
        "expected the 1149 runtime-passed fixtures"
    );

    let mut freq: std::collections::BTreeMap<String, usize> = Default::default();
    let mut sites = 0usize;
    let mut named = 0usize;
    for relative in &paths {
        let module = common::lift_fixture(&root, relative);
        for f in &module.functions {
            for &b in &f.blocks {
                for &iid in &module.blocks[b.index()].insts {
                    let inst = &module.insts[iid.index()];
                    let Op::Call { callee, .. } = &inst.op else {
                        continue;
                    };
                    sites += 1;
                    let candidates = callee_name_candidates(&module, *callee);
                    if let Some(top) = candidates.first() {
                        named += 1;
                        *freq.entry(top.clone()).or_insert(0) += 1;
                    }
                }
            }
        }
    }

    let mut ranked: Vec<(String, usize)> = freq.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    eprintln!("NAME-FREQ sites={sites} named={named}");
    for (i, (name, count)) in ranked.iter().take(200).enumerate() {
        eprintln!("NAME-FREQ #{:02} {count:>6} {name}", i + 1);
    }
}
