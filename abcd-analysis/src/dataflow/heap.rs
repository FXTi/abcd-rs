//! Heap v0 — alloc-site-keyed heap facts, strong/weak updates, and the
//! [`AliasOracle`] trait seam (design/analysis-strategy.md §4.4 rung 0 and
//! §5.2, which is the spec for the trait surface).
//!
//! ## The rung-0 model
//!
//! A heap location is keyed by `(AllocSite, FieldChain)` where the
//! allocation site is the [`InstId`] of the `AllocObject` / `AllocArray` /
//! `AllocClosure` / `AllocRegExp` instruction (T7) — unique, stable, and
//! already in the IR, so rung 0 costs no additional analysis. Two SSA
//! values alias when their def chains reach the same site
//! ([`resolve_alloc_sites`]); phi merges take the union of sites.
//!
//! **Strong update** is legal iff the store's base resolves to exactly one
//! site with no phi in between ([`update_kind`]) — the SSA substitute for
//! a must-alias analysis (infoflow.md §9 item 3); everything else is a
//! weak update.
//!
//! Because facts are keyed by site rather than by local, aliasing is
//! resolved *at the key*: a store through `x.f` and a load through `y.f`
//! meet iff `x` and `y` share a site. That is why
//! [`Rung0AliasOracle::aliases_of_store`] injects nothing — the
//! `computeAliases` trigger of infoflow.md §4.2 is subsumed by key
//! matching at rung 0. Rung 1 (a Boomerang-shaped demand-driven query
//! engine) replaces that with memoized backward queries *without changing
//! the key shape* — climbing the ladder only makes [`AllocSiteSet`]s more
//! precise, never re-keys facts (analysis-strategy §5.2).

use std::collections::{BTreeSet, HashMap, HashSet};

use abcd_ir::{FuncId, InstId, Module, Op, Sym, ValueDef, ValueId};

/// Default k-limit for field chains (access-path cutoff), FlowDroid's
/// conventional bound: a chain that grows past this is truncated back to
/// the prefix, merging everything below the cutoff into one abstract
/// location (conservative, and what keeps the fact domain finite).
pub const DEFAULT_MAX_FIELD_CHAIN: usize = 5;

/// One field-chain element (T2/T9: named / index / dynamic access are
/// always distinguishable).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldKey {
    /// A statically known property name.
    Named(Sym),
    /// An integer-index access (the index value is deliberately not part
    /// of the key — constant-index refinement is a later rung).
    AnyIndex,
    /// A computed-key access (over-approximates every property).
    AnyDynamic,
}

/// A k-capped chain of field accesses — the access-path tail of a heap
/// fact key.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldChain(Vec<FieldKey>);

impl FieldChain {
    /// The empty chain (the base object itself).
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// `chain.key`, k-capped: at the cap the extension collapses back onto
    /// the prefix (k-limiting), so chains are bounded and merging at the
    /// cutoff is automatic.
    pub fn pushed(&self, key: FieldKey, cap: usize) -> Self {
        let mut chain = self.0.clone();
        if chain.len() < cap {
            chain.push(key);
        }
        Self(chain)
    }

    /// Chain length.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the chain is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The elements, base-first.
    pub fn elements(&self) -> &[FieldKey] {
        &self.0
    }

    /// Whether the two chains could denote the same property chain:
    /// pointwise-compatible on the shared prefix (`AnyIndex`/`AnyDynamic`
    /// are wildcards; two different names are not).
    pub fn compatible_with(&self, other: &FieldChain) -> bool {
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match (a, b) {
                (FieldKey::Named(x), FieldKey::Named(y)) if x != y => return false,
                _ => {}
            }
        }
        true
    }
}

/// A set of allocation sites (the `InstId`s of the four keyed `Alloc*`
/// ops). A B-tree: iteration order is part of determinism.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AllocSiteSet(BTreeSet<InstId>);

impl AllocSiteSet {
    /// The empty set (no known sites).
    pub fn new() -> Self {
        Self::default()
    }

    /// A singleton set.
    pub fn one(site: InstId) -> Self {
        Self(BTreeSet::from([site]))
    }

    /// The sites, in [`InstId`] order.
    pub fn iter(&self) -> impl Iterator<Item = InstId> + '_ {
        self.0.iter().copied()
    }

    /// Number of sites.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Whether the sets share at least one site.
    pub fn intersects(&self, other: &AllocSiteSet) -> bool {
        self.0.intersection(&other.0).next().is_some()
    }

    /// Union in place.
    pub fn union_with(&mut self, other: &AllocSiteSet) {
        self.0.extend(other.0.iter().copied());
    }
}

/// The rung-0 heap fact key: `(AllocSiteSet, FieldChain)`
/// (analysis-strategy §5.2 — this shape is stable across the whole
/// precision ladder; climbing only refines the site set).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HeapRef {
    /// The objects (by allocation site) this reference may denote.
    pub sites: AllocSiteSet,
    /// The field chain below the object.
    pub fields: FieldChain,
}

/// A three-valued answer for cheap oracle queries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tribool {
    /// Definitely.
    True,
    /// Definitely not.
    False,
    /// Cannot decide at this rung.
    Unknown,
}

/// The resolution of an SSA value to allocation sites along its def
/// chain (rung 0: intraprocedural, flow-insensitive along the chain).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SiteInfo {
    /// The sites found.
    pub sites: AllocSiteSet,
    /// A phi was traversed (sites are a merge of incoming values).
    pub has_phi: bool,
    /// The chain passed through something that is not a keyed allocation
    /// (parameters, loads, call results, non-keyed allocations, …), so
    /// the set is a lower bound, not the whole truth.
    pub has_unknown: bool,
}

impl SiteInfo {
    /// Whether the value is provably a single site with no phi in between
    /// — the strong-update condition (analysis-strategy §4.4 rung 0).
    pub fn is_single_precise(&self) -> bool {
        self.sites.len() == 1 && !self.has_phi && !self.has_unknown
    }
}

/// Store update strength.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UpdateKind {
    /// The old value at the location is dead after the store (base is
    /// provably one site, no phi in between).
    Strong,
    /// The old value may survive (merge).
    Weak,
}

/// The update kind for a store whose base resolved to `info`.
pub fn update_kind(info: &SiteInfo) -> UpdateKind {
    if info.is_single_precise() {
        UpdateKind::Strong
    } else {
        UpdateKind::Weak
    }
}

/// Whether `op` allocates one of the four rung-0 keyed sites (T7;
/// analysis-strategy §4.4 rung 0 names exactly these four — other
/// allocating ops (`CreateIterResultObj`, `GetUnmappedArgs`, …) are
/// *unkeyed* and conservatively count as unknown).
pub fn is_keyed_alloc(op: &Op) -> bool {
    matches!(
        op,
        Op::AllocObject { .. }
            | Op::AllocArray { .. }
            | Op::AllocClosure { .. }
            | Op::AllocRegExp { .. }
    )
}

/// Resolve an SSA value to allocation sites by walking its def chain:
/// `Mov` passes through, `Phi` merges (marking `has_phi`), the four keyed
/// `Alloc*` ops contribute their [`InstId`], and everything else
/// (parameters, loads, call results, non-keyed allocations, exception
/// params) marks `has_unknown`. Chains are cycle-guarded; a phi cycle
/// terminates as a phi.
pub fn resolve_alloc_sites(module: &Module, value: ValueId) -> SiteInfo {
    let mut info = SiteInfo::default();
    let mut visiting = HashSet::new();
    resolve_into(module, value, &mut info, &mut visiting);
    info
}

fn resolve_into(
    module: &Module,
    value: ValueId,
    info: &mut SiteInfo,
    visiting: &mut HashSet<ValueId>,
) {
    if !visiting.insert(value) {
        // A def-chain cycle (only possible through phis): treat as a phi
        // merge and stop.
        info.has_phi = true;
        return;
    }
    let Some(v) = module.value(value) else {
        info.has_unknown = true;
        return;
    };
    match v.def {
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => {
            info.has_unknown = true;
        }
        ValueDef::Const(_) => {
            // Constants are not heap allocations: they contribute no site
            // and are not "unknown heap" either.
        }
        ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => resolve_into(module, *src, info, visiting),
            Some(Op::Phi { entries }) => {
                info.has_phi = true;
                for (_, v) in entries {
                    resolve_into(module, *v, info, visiting);
                }
            }
            Some(op) if is_keyed_alloc(op) => {
                info.sites.union_with(&AllocSiteSet::one(iid));
            }
            Some(_) => {
                info.has_unknown = true;
            }
            None => {
                info.has_unknown = true;
            }
        },
    }
}

/// Key-level may-alias tri-state over two heap refs, engine-independent
/// (shared by the rung-0 and rung-1 oracles — climbing the ladder refines
/// the site sets IN the keys, never this rule): equal refs alias;
/// incompatible field chains or disjoint non-empty site sets do not
/// (an empty set means "no keyed site found", not "no object"); anything
/// else is undecidable.
pub fn key_may_alias(a: &HeapRef, b: &HeapRef) -> Tribool {
    if a == b {
        return Tribool::True;
    }
    if !a.fields.compatible_with(&b.fields) {
        return Tribool::False;
    }
    if !a.sites.is_empty() && !b.sites.is_empty() && !a.sites.intersects(&b.sites) {
        return Tribool::False;
    }
    Tribool::Unknown
}

/// Oracle for heap aliasing, implemented by heap-v0 (rung 0) initially
/// and by a demand-driven query engine (rung 1) later WITHOUT call-site
/// changes in the taint engine (analysis-strategy.md §5.2 — this trait's
/// method set is that section's spec, generalized over the client's fact
/// type `F` so `abcd-analysis` never depends on `abcd-taint`; modeled on
/// FlowDroid's `IAliasingStrategy` policy interface, infoflow.md §9).
pub trait AliasOracle<F> {
    /// Cheap, must-not-block queries used inside flow functions.
    /// Tri-state over alloc-site sets; heap-v0 answers from def chains
    /// only.
    fn may_alias(&self, a: &HeapRef, b: &HeapRef) -> Tribool;

    /// Must-alias on SSA bases at a program point: rung 0 answers "same
    /// single site along both def chains, no phi in between".
    fn must_alias(&self, base_a: ValueId, base_b: ValueId, at: InstId) -> bool;

    /// The expensive trigger: a taint was written to the heap at `store`.
    /// Returns additional (heap-keyed) taint facts to inject into the
    /// forward analysis — the analogue of infoflow.md §4.2's
    /// `computeAliases` triggers. heap-v0 answers locally (key-level
    /// merging makes this empty); rung 1 runs a memoized backward query
    /// here.
    fn aliases_of_store(&mut self, taint: &F, store: InstId, func: FuncId) -> Vec<F>;

    /// Interprocedural discipline, mirroring infoflow.md §4.3: the oracle
    /// learns calling contexts so alias queries started in a callee
    /// return to the right callers.
    fn inject_calling_context(&mut self, call: InstId, callee: FuncId, fact: &F);

    /// Whether the oracle needs to be re-queried on return edges
    /// (FlowDroid's `PtsBased` said yes, `FlowSensitive` said no; rung 1
    /// will say no). heap-v0 answers everything from def chains, so no.
    fn needs_requery_on_return(&self) -> bool;

    /// Rung-1 capability probe: resolve a base value to allocation sites
    /// at a program point. heap-v0 implements it as the local def-chain
    /// walk ([`resolve_alloc_sites`]); the rung-1 engine overrides with
    /// the memoized interprocedural query. Call-graph resolution
    /// (analysis-strategy §5.4) may consume this too — one mechanism
    /// serves both the alias ladder and dispatch precision.
    fn points_to(&self, base: ValueId, at: InstId) -> AllocSiteSet;
}

/// The rung-0 oracle: def-chain answers only
/// (analysis-strategy.md §4.4 rung 0). Cheap, total, and conservative;
/// every "cannot decide" degrades to `Unknown`/weak.
pub struct Rung0AliasOracle<'m> {
    module: &'m Module,
    memo: std::cell::RefCell<HashMap<ValueId, SiteInfo>>,
}

impl<'m> Rung0AliasOracle<'m> {
    /// An oracle over `module` with an empty memo table.
    pub fn new(module: &'m Module) -> Self {
        Self {
            module,
            memo: std::cell::RefCell::new(HashMap::new()),
        }
    }

    /// The (memoized) site resolution of `value`.
    pub fn resolve(&self, value: ValueId) -> SiteInfo {
        if let Some(hit) = self.memo.borrow().get(&value) {
            return hit.clone();
        }
        let info = resolve_alloc_sites(self.module, value);
        self.memo.borrow_mut().insert(value, info.clone());
        info
    }

    /// The store-update kind for a base value.
    pub fn update_kind_of(&self, base: ValueId) -> UpdateKind {
        update_kind(&self.resolve(base))
    }
}

impl<F> AliasOracle<F> for Rung0AliasOracle<'_> {
    fn may_alias(&self, a: &HeapRef, b: &HeapRef) -> Tribool {
        key_may_alias(a, b)
    }

    fn must_alias(&self, base_a: ValueId, base_b: ValueId, _at: InstId) -> bool {
        let a = self.resolve(base_a);
        let b = self.resolve(base_b);
        a.is_single_precise() && b.is_single_precise() && a.sites == b.sites
    }

    fn aliases_of_store(&mut self, _taint: &F, _store: InstId, _func: FuncId) -> Vec<F> {
        // Rung 0 resolves aliasing at the fact KEY (site-keyed heap facts
        // merge at the key), so there is nothing to inject — see the
        // module docs. Rung 1 overrides this with a backward query.
        Vec::new()
    }

    fn inject_calling_context(&mut self, _call: InstId, _callee: FuncId, _fact: &F) {
        // Rung 0 is context-insensitive by construction (def chains carry
        // no calling context); nothing to record.
    }

    fn needs_requery_on_return(&self) -> bool {
        false
    }

    fn points_to(&self, base: ValueId, _at: InstId) -> AllocSiteSet {
        // Rung 0 is flow-insensitive along the def chain: `at` does not
        // refine the answer (documented imprecision; the parameter exists
        // so rung 1's point-aware query drops in unchanged).
        self.resolve(base).sites
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::{EdgeKind, Op};

    #[test]
    fn straight_line_alloc_is_single_precise() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let obj = alloc_object(&mut m, entry);
        let alias = emit(&mut m, entry, Op::Mov { src: obj });
        emit_void(&mut m, entry, Op::Return { value: None });

        let info = resolve_alloc_sites(&m, alias);
        assert_eq!(info.sites.len(), 1);
        assert!(info.is_single_precise());
        assert_eq!(update_kind(&info), UpdateKind::Strong);

        let oracle = Rung0AliasOracle::new(&m);
        assert!(AliasOracle::<()>::must_alias(
            &oracle,
            obj,
            alias,
            InstId::new(0)
        ));
        assert_eq!(
            AliasOracle::<()>::points_to(&oracle, alias, InstId::new(0)).len(),
            1
        );
    }

    #[test]
    fn phi_merge_is_weak() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let join = add_block(&mut m, f);

        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: t,
                false_dest: e,
            },
        );
        let a = alloc_object(&mut m, t);
        emit_void(&mut m, t, Op::Branch { dest: join });
        let b = alloc_object(&mut m, e);
        emit_void(&mut m, e, Op::Branch { dest: join });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
        link(&mut m, t, join);
        link(&mut m, e, join);
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        abcd_ir::Edge {
                            from: t,
                            kind: EdgeKind::Normal,
                        },
                        a,
                    ),
                    (
                        abcd_ir::Edge {
                            from: e,
                            kind: EdgeKind::Normal,
                        },
                        b,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: None });

        let info = resolve_alloc_sites(&m, phi);
        assert_eq!(info.sites.len(), 2, "phi merges sites");
        assert!(info.has_phi);
        assert_eq!(update_kind(&info), UpdateKind::Weak);

        let oracle = Rung0AliasOracle::new(&m);
        assert!(!AliasOracle::<()>::must_alias(
            &oracle,
            phi,
            a,
            InstId::new(0)
        ));
        assert_eq!(
            AliasOracle::<()>::points_to(&oracle, phi, InstId::new(0)).len(),
            2
        );
    }

    #[test]
    fn array_alloc_site_and_consts() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let arr = alloc_array(&mut m, entry);
        let undef = const_undefined(&mut m);
        emit_void(&mut m, entry, Op::Return { value: None });

        // An array allocation is a keyed site (T7).
        let info = resolve_alloc_sites(&m, arr);
        assert!(info.is_single_precise());
        assert_eq!(update_kind(&info), UpdateKind::Strong);

        // Constants contribute no site and no unknown — they are not heap
        // objects at all.
        let info = resolve_alloc_sites(&m, undef);
        assert!(info.sites.is_empty());
        assert!(!info.has_unknown && !info.has_phi);

        // Different sites of different kinds do not alias.
        let obj = alloc_object(&mut m, entry);
        let oracle = Rung0AliasOracle::new(&m);
        assert!(!AliasOracle::<()>::must_alias(
            &oracle,
            arr,
            obj,
            InstId::new(0)
        ));
    }

    #[test]
    fn unknown_sources_are_weak_and_never_must_alias() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p = add_param(&mut m, f, 1);
        let name = intern(&mut m, "x");
        let loaded = emit(&mut m, entry, Op::LoadProp { object: p, name });
        emit_void(&mut m, entry, Op::Return { value: None });

        let info = resolve_alloc_sites(&m, loaded);
        assert!(info.sites.is_empty());
        assert!(info.has_unknown);
        assert_eq!(update_kind(&info), UpdateKind::Weak);

        let oracle = Rung0AliasOracle::new(&m);
        assert!(!AliasOracle::<()>::must_alias(
            &oracle,
            loaded,
            loaded,
            InstId::new(0)
        ));
    }

    #[test]
    fn access_path_cutoff_at_k() {
        let cap = 3usize;
        let s = Sym::new(7);
        let mut chain = FieldChain::new();
        for _ in 0..5 {
            chain = chain.pushed(FieldKey::Named(s), cap);
        }
        assert_eq!(chain.len(), cap, "chain is capped at k");

        // Two chains that differ ONLY below the cutoff collapse to the
        // same key (k-limiting merges them).
        let other = Sym::new(8);
        let mut a = FieldChain::new();
        let mut b = FieldChain::new();
        for _ in 0..cap {
            a = a.pushed(FieldKey::Named(s), cap);
            b = b.pushed(FieldKey::Named(s), cap);
        }
        a = a.pushed(FieldKey::Named(s), cap);
        b = b.pushed(FieldKey::Named(other), cap);
        assert_eq!(a, b, "beyond-k extensions collapse onto the prefix");
    }

    #[test]
    fn may_alias_tri_state() {
        let f1 = FieldChain::new().pushed(FieldKey::Named(Sym::new(1)), DEFAULT_MAX_FIELD_CHAIN);
        let f2 = FieldChain::new().pushed(FieldKey::Named(Sym::new(2)), DEFAULT_MAX_FIELD_CHAIN);
        let s1 = AllocSiteSet::one(InstId::new(1));
        let s2 = AllocSiteSet::one(InstId::new(2));

        let m = Module::new();
        let oracle = Rung0AliasOracle::new(&m);
        let same = HeapRef {
            sites: s1.clone(),
            fields: f1.clone(),
        };
        assert_eq!(
            AliasOracle::<()>::may_alias(&oracle, &same, &same.clone()),
            Tribool::True
        );
        // Different named fields: never the same location.
        let other_field = HeapRef {
            sites: s1.clone(),
            fields: f2,
        };
        assert_eq!(
            AliasOracle::<()>::may_alias(&oracle, &same, &other_field),
            Tribool::False
        );
        // Same field, disjoint sites: different objects.
        let other_obj = HeapRef {
            sites: s2,
            fields: f1.clone(),
        };
        assert_eq!(
            AliasOracle::<()>::may_alias(&oracle, &same, &other_obj),
            Tribool::False
        );
        // Same field, unknown sites on one side: undecidable.
        let unknown = HeapRef {
            sites: AllocSiteSet::new(),
            fields: f1,
        };
        assert_eq!(
            AliasOracle::<()>::may_alias(&oracle, &same, &unknown),
            Tribool::Unknown
        );
    }
}
