//! The taint problem's alias-oracle switch (`design/analysis.md`):
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
//! - [`Oracle::aliases_of_store`] — client-side store-base alias
//!   resolution: a taint written to the heap at a
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

use std::cell::RefCell;
use std::collections::HashMap;

use abcd_analysis::dataflow::alias::Rung1AliasOracle;
use abcd_analysis::dataflow::heap::{
    self, AliasOracle, AllocSiteSet, FieldChain, FieldKey, Rung0AliasOracle,
    SingletonSiteClassifier, SiteInfo,
};
use abcd_analysis::dataflow::pta::{EnvAnswer, Rung2AliasOracle};
use abcd_ir::{InstId, Module, ValueId};

use crate::fact::{TaintBase, TaintFact};

/// Memoized local def-chain resolution cache (`ValueId -> SiteInfo`) shared by
/// refined oracle arms (`Rung1`, `Rung2`) so fallback floor queries run in `O(1)`
/// amortized instead of re-walking `Phi`/`Mov` def chains (`#78`, `#84`).
#[derive(Default)]
pub struct ResolveMemo(RefCell<HashMap<ValueId, SiteInfo>>);

impl ResolveMemo {
    #[inline]
    fn resolve_with(&self, module: &Module, value: ValueId) -> SiteInfo {
        if let Some(hit) = self.0.borrow().get(&value) {
            return hit.clone();
        }
        let info = heap::resolve_alloc_sites(module, value);
        self.0.borrow_mut().insert(value, info.clone());
        info
    }
}

/// The oracle the [`crate::problem::TaintProblem`] runs against.
#[expect(
    clippy::large_enum_variant,
    reason = "Oracle is instantiated once per TaintProblem and never stored in collections"
)]
pub enum Oracle<'m> {
    /// Rung 0: local def chains only.
    Rung0(Rung0AliasOracle<'m>),
    /// Rung 1: the demand-driven engine + memoized rung-0 fallback.
    Rung1(Rung1AliasOracle<'m>, ResolveMemo),
    /// Rung 2: the whole-module PTA + memoized rung-0 fallback.
    Rung2(Rung2AliasOracle<'m>, ResolveMemo),
}

impl<'m> Oracle<'m> {
    /// Construct a [`Self::Rung1`] oracle with an empty fallback memo.
    #[must_use]
    pub fn rung1(engine: Rung1AliasOracle<'m>) -> Self {
        Self::Rung1(engine, ResolveMemo::default())
    }

    /// Construct a [`Self::Rung2`] oracle with an empty fallback memo.
    #[must_use]
    pub fn rung2(pta: Rung2AliasOracle<'m>) -> Self {
        Self::Rung2(pta, ResolveMemo::default())
    }

    /// The rung-0 local def-chain resolution (identical on all arms —
    /// the floor every refined answer is checked against), memoized per `ValueId`.
    pub fn resolve(&self, value: ValueId) -> SiteInfo {
        match self {
            Oracle::Rung0(o) => o.resolve(value),
            Oracle::Rung1(o, memo) => memo.resolve_with(o.module(), value),
            Oracle::Rung2(o, memo) => memo.resolve_with(o.module(), value),
        }
    }

    /// The point-aware resolution: the refined arms answer through
    /// their engines when the answer is complete; rung 0 (and any
    /// imprecise query) answers with the memoized local def chain, gated by
    /// [`SingletonSiteClassifier`] (`D5`).
    pub fn site_info_at(&self, value: ValueId, at: InstId) -> SiteInfo {
        match self {
            Oracle::Rung0(o) => o.site_info_at(value, at),
            Oracle::Rung1(o, memo) => {
                let ans = o.query(value, at);
                let raw = if ans.precise_for_keying() {
                    SiteInfo {
                        sites: ans.sites,
                        has_phi: ans.has_phi,
                        has_unknown: false,
                    }
                } else {
                    memo.resolve_with(o.module(), value)
                };
                o.singletons().gate_site_info(raw)
            }
            Oracle::Rung2(o, memo) => {
                let ans = o.query(value, at);
                let raw = if ans.precise_for_keying() {
                    SiteInfo {
                        sites: ans.sites,
                        has_phi: ans.has_phi,
                        has_unknown: false,
                    }
                } else {
                    memo.resolve_with(o.module(), value)
                };
                o.singletons().gate_site_info(raw)
            }
        }
    }

    /// Borrow the active [`SingletonSiteClassifier`] (`D5`).
    #[must_use]
    pub fn singletons(&self) -> &SingletonSiteClassifier {
        match self {
            Oracle::Rung0(o) => o.singletons(),
            Oracle::Rung1(o, _) => o.singletons(),
            Oracle::Rung2(o, _) => o.singletons(),
        }
    }

    /// Whether `site` executes at most once in a concrete program run (`D5`).
    #[must_use]
    pub fn is_concrete_singleton_site(&self, site: InstId) -> bool {
        match self {
            Oracle::Rung0(o) => o.is_concrete_singleton_site(site),
            Oracle::Rung1(o, _) => o.is_concrete_singleton_site(site),
            Oracle::Rung2(o, _) => o.is_concrete_singleton_site(site),
        }
    }

    /// The MAY-direction site query (`CallGraph::refine_with_points_to`
    /// consumer discipline): the
    /// refined arms return the engine's answer when it is complete
    /// modulo the recorded call graph (`complete_for_resolution` —
    /// may-direction consumers accept what negative decisions must
    /// not); anything incomplete, and rung 0, falls back to the local
    /// def-chain walk (the sound floor, partial sites included).
    pub fn may_sites_at(&self, value: ValueId, at: InstId) -> AllocSiteSet {
        match self {
            Oracle::Rung0(o) => o.resolve(value).sites,
            Oracle::Rung1(o, _) => {
                let ans = o.query(value, at);
                if ans.complete_for_resolution() {
                    ans.sites
                } else {
                    self.resolve(value).sites
                }
            }
            Oracle::Rung2(o, _) => {
                let ans = o.query(value, at);
                if ans.complete_for_resolution() {
                    ans.sites
                } else {
                    self.resolve(value).sites
                }
            }
        }
    }

    /// Union of local def-chain allocation sites and any engine-recorded
    /// allocation sites for `value` (retaining known sites even when
    /// `has_unknown` is `true`).
    pub fn known_sites_at(&self, value: ValueId, at: InstId) -> AllocSiteSet {
        let mut out = self.resolve(value).sites;
        match self {
            Oracle::Rung0(_) => {}
            Oracle::Rung1(o, _) => out.union_with(&o.query(value, at).sites),
            Oracle::Rung2(o, _) => out.union_with(&o.query(value, at).sites),
        }
        out
    }

    /// The rung-2 environment-identity channel: the lexical environment
    /// a `GetLexVar`/`PutLexVar` at `at` with scope-chain `level`
    /// denotes. `None` on rungs 0/1 — the legacy `(level, slot)` keying
    /// stands there.
    pub fn lex_env_at(&self, at: InstId, level: u16) -> Option<EnvAnswer> {
        match self {
            Oracle::Rung2(o, _) => Some(o.lex_env_at(at, level)),
            _ => None,
        }
    }

    /// Whether `site` (`result`) was analyzed inside Rung-2 PTA (`#78`, `#84`).
    #[must_use]
    pub fn is_analyzed_alloc_site(&self, site: InstId, result: ValueId) -> bool {
        match self {
            Oracle::Rung2(o, _) => !o.query(result, site).sites.is_empty(),
            Oracle::Rung0(_) | Oracle::Rung1(..) => false,
        }
    }

    /// Return the Rung-2 points-to site set of `value` at `at` only when the
    /// Rung-2 PTA answer is complete and free of unknown aliases (`precise_for_keying`).
    #[must_use]
    pub(crate) fn rung2_precise_sites_at(
        &self,
        value: ValueId,
        at: InstId,
    ) -> Option<AllocSiteSet> {
        match self {
            Oracle::Rung2(o, _) => {
                let ans = o.query(value, at);
                ans.precise_for_keying().then_some(ans.sites)
            }
            Oracle::Rung0(_) | Oracle::Rung1(..) => None,
        }
    }

    /// Whether `site` is a lexical-environment allocation (the
    /// may-direction env fallback's fact filter; `false` on rungs 0/1).
    pub fn is_env_site(&self, site: InstId) -> bool {
        match self {
            Oracle::Rung2(o, _) => o.is_env_site(site),
            // unreachable: the only caller (problem.rs GetLexVar fallback)
            // is guarded by lex_env_at(...) -> Some, which fires only on
            // Oracle::Rung2, so `self` here always dispatches above.
            _ => false,
        }
    }

    /// Store-base alias re-keying: a taint on the store's VALUE, written
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
            Oracle::Rung1(o, _) => o.query(object, store),
            Oracle::Rung2(o, _) => o.query(object, store),
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

/// Implement the [`AliasOracle`] policy marker seam (`design/analysis.md`) across
/// all precision-ladder arms (`Rung0`, `Rung1`, `Rung2`).
impl<F> AliasOracle<F> for Oracle<'_> {}
