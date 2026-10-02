//! Corpus measurement (opt-in): the deepest region-tree nesting across
//! the exported corpus — the depth the old recursive structurer had to
//! keep on the native stack (the ASan stack-overflow driver), now the
//! depth of the explicit-stack driver's heap stack.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-analysis --test corpus_region_depth --release -- --ignored --nocapture
//! ```

mod common;

use abcd_analysis::control::{RegionId, RegionNode, RegionTree, structure_regions};
use abcd_ir::FuncId;

/// The region tree's nesting depth (root = 1), computed iteratively.
fn tree_depth(tree: &RegionTree) -> usize {
    let mut depth = 0usize;
    let mut stack: Vec<(RegionId, usize)> = Vec::new();
    if let Some(root) = tree.root {
        stack.push((root, 1));
    }
    while let Some((id, d)) = stack.pop() {
        depth = depth.max(d);
        match tree.node(id) {
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                for &c in children {
                    stack.push((c, d + 1));
                }
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                stack.push((*body, d + 1));
            }
            RegionNode::If {
                then, otherwise, ..
            } => {
                for c in [then, otherwise].into_iter().flatten() {
                    stack.push((*c, d + 1));
                }
            }
            RegionNode::Block(_) | RegionNode::Irreducible { .. } => {}
        }
    }
    depth
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_region_depth_report() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 5517, "expected the full 5517-fixture corpus");

    let mut functions = 0usize;
    // (depth, fixture, func index, blocks)
    let mut deepest: (usize, String, u32, usize) = (0, String::new(), 0, 0);
    let mut top: Vec<(usize, String, u32, usize)> = Vec::new();
    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = abcd_lift::lift_file(&file).expect("lift fixture");
        for fi in 0..module.functions.len() {
            let func = FuncId::new(fi as u32);
            let fi = fi as u32;
            let blocks = module.func(func).expect("func").blocks.len();
            let tree = structure_regions(&module, func);
            functions += 1;
            let d = tree_depth(&tree);
            if d > deepest.0 {
                deepest = (d, relative.clone(), fi, blocks);
            }
            top.push((d, relative.clone(), fi, blocks));
        }
    }
    top.sort_by_key(|a| std::cmp::Reverse(a.0));
    eprintln!("DEPTH-GATE functions={functions}");
    eprintln!(
        "DEPTH-GATE deepest depth={} fixture={} func={} blocks={}",
        deepest.0, deepest.1, deepest.2, deepest.3
    );
    for (d, rel, fi, blocks) in top.iter().take(10) {
        eprintln!("DEPTH-GATE top depth={d} fixture={rel} func={fi} blocks={blocks}");
    }
}
