//! Corpus agreement check: `abcd_analysis::control::Dominators` must agree
//! with `abcd_ir::verify`'s private iterative dominator computation on every
//! corpus function.

use crate::common;
use abcd_ir::{FuncId, Module};

#[derive(Default, Clone, Copy)]
pub(crate) struct DomCounts {
    pub functions: usize,
    pub blocks_compared: usize,
    pub blocks_skipped: usize,
    pub blocks_total: usize,
}

impl DomCounts {
    pub fn merge(&mut self, other: Self) {
        self.functions += other.functions;
        self.blocks_compared += other.blocks_compared;
        self.blocks_skipped += other.blocks_skipped;
        self.blocks_total += other.blocks_total;
    }
}

pub(crate) fn check_fixture(module: &Module, relative: &str) -> DomCounts {
    let mut out = DomCounts::default();
    for fi in 0..module.functions.len() {
        let (c, s, t) = common::check_function(module, FuncId::new(fi as u32), relative);
        out.functions += 1;
        out.blocks_compared += c;
        out.blocks_skipped += s;
        out.blocks_total += t;
    }
    out
}

pub(crate) fn report_and_assert(fixtures: usize, counts: DomCounts) {
    eprintln!(
        "DOM-AGREEMENT fixtures={fixtures} functions={} \
         blocks_compared={} blocks_skipped={} blocks_total={}",
        counts.functions, counts.blocks_compared, counts.blocks_skipped, counts.blocks_total
    );
    assert!(counts.blocks_compared > 0);
}
