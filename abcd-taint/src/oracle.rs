//! The taint problem's alias-oracle switch (analysis-strategy §5.2, §4.4):
//! rung 0 ([`Rung0AliasOracle`], the trivial baseline), rung 1
//! ([`Rung1AliasOracle`], the demand-driven backward points-to engine),
//! or rung 2 ([`Rung2AliasOracle`], the whole-module context-sensitive
//! PTA), selected by [`crate::driver::TaintConfig::alias_rung`].
//!
//! ## What the refined arms change for the flow functions
//!
//! - [`Oracle::site_info_at`] — the point-aware resolution used by the
//!   store/load rules and summary endpoints. Rung 0: the local def-chain
//!   walk. Rung 1: the engine's memoized interprocedural query WHEN it is
//!   complete and balanced, else the rung-0 answer (the sound floor —
//!   the engine can only ever make keying *more* precise, never less
//!   sound; see `abcd_analysis::dataflow::alias` module docs). Rung 2:
//!   the PTA's fixed-point answer under the same completeness rule.
//! - [`Oracle::aliases_of_store`] — the client-side `computeAliases`
//!   analogue (soot-infoflow.md §4.2): a taint written to the heap at a
//!   store is re-keyed by the REFINED sites of the store's base. This
//!   lives here and not inside the trait impl because re-keying needs
//!   the fact algebra (`TaintFact`), which the `F`-generic
//!   `AliasOracle<F>` seam deliberately cannot express — the trait
//!   method stays for key-level oracles (rung 0: empty) and later
//!   value-level rebasing.
//! - [`Oracle::lex_env_at`] — the rung-2-only environment-identity
//!   channel: `None` on rungs 0/1 (the legacy `(level, slot)` keying
//!   stands); `Some(answer)` on rung 2, consumed by the lexical-slot
//!   rules in `problem.rs` (b2).

use abcd_analysis::dataflow::alias::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::{
    self, AliasOracle, AllocSiteSet, FieldChain, FieldKey, HeapRef, Rung0AliasOracle, SiteInfo,
    Tribool,
};
use abcd_analysis::dataflow::pta::{EnvAnswer, Rung2AliasOracle};
use abcd_ir::{FuncId, InstId, ValueId};

use crate::fact::{Fact, TaintBase, TaintFact};

/// The oracle the [`crate::problem::TaintProblem`] runs against.
pub enum Oracle<'m> {
    /// Rung 0: local def chains only.
    Rung0(Rung0AliasOracle<'m>),
    /// Rung 1: the demand-driven engine + rung-0 fallback.
    Rung1(Rung1AliasOracle<'m>),
    /// Rung 2: the whole-module PTA + rung-0 fallback.
    Rung2(Rung2AliasOracle<'m>),
}

impl<'m> Oracle<'m> {
    /// The rung-0 local def-chain resolution (identical on all arms —
    /// the floor every refined answer is checked against).
    pub fn resolve(&self, value: ValueId) -> SiteInfo {
        match self {
            Oracle::Rung0(o) => o.resolve(value),
            Oracle::Rung1(o) => heap::resolve_alloc_sites(o.module(), value),
            Oracle::Rung2(o) => heap::resolve_alloc_sites(o.module(), value),
        }
    }

    /// The point-aware resolution: the refined arms answer through
    /// their engines when the answer is complete; rung 0 (and any
    /// imprecise query) answers with the local def chain.
    pub fn site_info_at(&self, value: ValueId, at: InstId) -> SiteInfo {
        match self {
            Oracle::Rung0(o) => o.resolve(value),
            Oracle::Rung1(o) => o.site_info_at(value, at),
            Oracle::Rung2(o) => o.site_info_at(value, at),
        }
    }

    /// The refined capability probe (§5.2): allocation sites of a base
    /// value at a program point. Call-graph resolution consumes the same
    /// answer through the engine directly (one engine, two consumers).
    pub fn points_to(&self, value: ValueId, at: InstId) -> AllocSiteSet {
        match self {
            Oracle::Rung0(o) => AliasOracle::<Fact>::points_to(o, value, at),
            Oracle::Rung1(o) => AliasOracle::<Fact>::points_to(o, value, at),
            Oracle::Rung2(o) => AliasOracle::<Fact>::points_to(o, value, at),
        }
    }

    /// The MAY-direction site query (t-P4; the
    /// `CallGraph::refine_with_points_to` consumer discipline): the
    /// refined arms return the engine's answer when it is complete
    /// modulo the recorded call graph (`complete_for_resolution` —
    /// may-direction consumers accept what negative decisions must
    /// not); anything incomplete, and rung 0, falls back to the local
    /// def-chain walk (the sound floor, partial sites included).
    pub fn may_sites_at(&self, value: ValueId, at: InstId) -> AllocSiteSet {
        match self {
            Oracle::Rung0(o) => o.resolve(value).sites,
            Oracle::Rung1(o) => {
                let ans = o.query(value, at);
                if ans.complete_for_resolution() {
                    ans.sites
                } else {
                    self.resolve(value).sites
                }
            }
            Oracle::Rung2(o) => {
                let ans = o.query(value, at);
                if ans.complete_for_resolution() {
                    ans.sites
                } else {
                    self.resolve(value).sites
                }
            }
        }
    }

    /// The rung-2 environment-identity channel: the lexical environment
    /// a `GetLexVar`/`PutLexVar` at `at` with scope-chain `level`
    /// denotes. `None` on rungs 0/1 — the legacy `(level, slot)` keying
    /// stands there.
    pub fn lex_env_at(&self, at: InstId, level: u16) -> Option<EnvAnswer> {
        match self {
            Oracle::Rung2(o) => Some(o.lex_env_at(at, level)),
            _ => None,
        }
    }

    /// Whether `site` is a lexical-environment allocation (the
    /// may-direction env fallback's fact filter; `false` on rungs 0/1).
    pub fn is_env_site(&self, site: InstId) -> bool {
        match self {
            Oracle::Rung2(o) => o.is_env_site(site),
            _ => false,
        }
    }

    /// The computeAliases analogue: a taint on the store's VALUE, written
    /// through `object.key` at `store`. The refined arms return the taint
    /// re-keyed by the REFINED site set of `object` when the engine's
    /// answer is precise; the caller skips its baseline (rung-0) re-key
    /// then. Rung 0 injects nothing (aliasing is resolved at the fact key).
    pub fn aliases_of_store(
        &self,
        taint: &TaintFact,
        object: ValueId,
        key: FieldKey,
        store: InstId,
        cap: usize,
    ) -> Vec<TaintFact> {
        let ans = match self {
            Oracle::Rung0(_) => return Vec::new(),
            Oracle::Rung1(o) => o.query(object, store),
            Oracle::Rung2(o) => o.query(object, store),
        };
        if !ans.precise_for_keying() {
            return Vec::new();
        }
        let mut chain = FieldChain::new().pushed(key, cap);
        for &k in taint.fields.elements() {
            chain = chain.pushed(k, cap);
        }
        vec![TaintFact {
            base: TaintBase::Heap(ans.sites),
            fields: chain,
        }]
    }
}

/// Delegate the §5.2 seam so the problem's call sites stay
/// oracle-agnostic (the refined engines' docs apply; rung 0 is the
/// baseline behavior).
impl<F> AliasOracle<F> for Oracle<'_> {
    fn may_alias(&self, a: &HeapRef, b: &HeapRef) -> Tribool {
        heap::key_may_alias(a, b)
    }

    fn must_alias(&self, base_a: ValueId, base_b: ValueId, at: InstId) -> bool {
        match self {
            Oracle::Rung0(o) => AliasOracle::<F>::must_alias(o, base_a, base_b, at),
            Oracle::Rung1(o) => AliasOracle::<F>::must_alias(o, base_a, base_b, at),
            Oracle::Rung2(o) => AliasOracle::<F>::must_alias(o, base_a, base_b, at),
        }
    }

    fn aliases_of_store(&mut self, taint: &F, store: InstId, func: FuncId) -> Vec<F> {
        match self {
            Oracle::Rung0(o) => AliasOracle::<F>::aliases_of_store(o, taint, store, func),
            Oracle::Rung1(o) => AliasOracle::<F>::aliases_of_store(o, taint, store, func),
            Oracle::Rung2(o) => AliasOracle::<F>::aliases_of_store(o, taint, store, func),
        }
    }

    fn inject_calling_context(&mut self, call: InstId, callee: FuncId, fact: &F) {
        match self {
            Oracle::Rung0(o) => AliasOracle::<F>::inject_calling_context(o, call, callee, fact),
            Oracle::Rung1(o) => AliasOracle::<F>::inject_calling_context(o, call, callee, fact),
            Oracle::Rung2(o) => AliasOracle::<F>::inject_calling_context(o, call, callee, fact),
        }
    }

    fn needs_requery_on_return(&self) -> bool {
        false
    }

    fn points_to(&self, base: ValueId, at: InstId) -> AllocSiteSet {
        match self {
            Oracle::Rung0(o) => AliasOracle::<F>::points_to(o, base, at),
            Oracle::Rung1(o) => AliasOracle::<F>::points_to(o, base, at),
            Oracle::Rung2(o) => AliasOracle::<F>::points_to(o, base, at),
        }
    }
}
