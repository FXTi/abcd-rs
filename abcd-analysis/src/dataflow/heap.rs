//! Rung 0 — allocation-site-keyed heap facts, strong/weak updates, and the
//! [`AliasOracle`] trait seam (`design/analysis.md`, `design/ir.md`).
//!
//! ## The rung-0 model
//!
//! A heap location is keyed by `(AllocSite, FieldChain)` where the
//! allocation site is the [`InstId`] of the `AllocObject` / `AllocArray` /
//! `AllocClosure` / `AllocRegExp` instruction — unique, stable, and
//! already in the IR, so rung 0 costs no additional whole-program pass. Two
//! SSA values alias when their def chains reach the same site
//! ([`resolve_alloc_sites`]); phi merges take the union of sites.
//!
//! **Strong update** is legal iff the store's base resolves to exactly one
//! site with no phi in between ([`update_kind`]) — the local SSA condition
//! for must-alias; everything else is a weak update.
//!
//! Because facts are keyed by allocation site rather than by local variable,
//! aliasing is resolved *at the fact key*: a store through `x.f` and a load
//! through `y.f` meet iff `x` and `y` share a site, without requiring a
//! separate backward alias-injection solver at heap writes. Rung 1
//! ([`super::alias`]) and Rung 2 ([`super::pta`]) refine those site sets
//! *without changing the key shape* — climbing the precision ladder only
//! makes [`AllocSiteSet`]s sharper, never re-keys facts (`design/analysis.md`).

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::OnceLock;

use abcd_ir::cfg::{ExceptionHandlerMap, augmented_succs_with_map};
use abcd_ir::{
    BlockId, Const, ConstId, FuncId, FunctionKind, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use crate::callgraph::{CallGraph, CallTargets};
use crate::dataflow::ifds::CallGraphOracle;
use crate::module_link::ModuleLinkTable;

/// Default k-limit for field chains (access-path cutoff): a chain that grows
/// past `k` is truncated back to its prefix, merging deeper accesses into one
/// abstract location so the fact domain stays finite.
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
/// (`design/analysis.md` — this shape is stable across the whole
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
    /// — the local SSA precision condition (`design/analysis.md`).
    pub fn is_single_precise(&self) -> bool {
        self.sites.len() == 1 && !self.has_phi && !self.has_unknown
    }

    /// Return the unique allocation site when [`Self::is_single_precise`] holds.
    #[must_use]
    pub fn as_singleton(&self) -> Option<InstId> {
        self.is_single_precise()
            .then(|| self.sites.iter().next())
            .flatten()
    }

    /// Return the unique allocation site ONLY when [`Self::is_single_precise`]
    /// holds AND `classifier` proves that site executes at most once at runtime
    /// (`D5`, `#94`).
    #[must_use]
    pub fn as_concrete_singleton(&self, classifier: &SingletonSiteClassifier) -> Option<InstId> {
        let site = self.as_singleton()?;
        classifier.site_is_concrete(site).then_some(site)
    }
}

/// Store update strength.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UpdateKind {
    /// The old value at the location is dead after the store (base is
    /// provably one concrete runtime singleton site, no phi in between).
    Strong,
    /// The old value may survive (merge).
    Weak,
}

/// The update kind for a store whose base resolved to `info` (assumes `info`'s
/// `has_phi` already reflects any non-singleton summary site, as enforced by
/// [`Rung0AliasOracle::site_info_at`], [`super::alias::Rung1AliasOracle::site_info_at`],
/// and [`super::pta::Rung2AliasOracle::site_info_at`]).
pub fn update_kind(info: &SiteInfo) -> UpdateKind {
    if info.is_single_precise() {
        UpdateKind::Strong
    } else {
        UpdateKind::Weak
    }
}

/// Concrete-singleton-gated store update strength (`D5`, `#94`): returns
/// [`UpdateKind::Strong`] iff `info.as_concrete_singleton(classifier)` is `Some`.
#[must_use]
pub fn update_kind_for(info: &SiteInfo, classifier: &SingletonSiteClassifier) -> UpdateKind {
    if info.as_concrete_singleton(classifier).is_some() {
        UpdateKind::Strong
    } else {
        UpdateKind::Weak
    }
}

/// Precomputed `O(1)` concrete-runtime-singleton classifier over a [`Module`]
/// (`D5`, `#94`).
///
/// An abstract allocation site (`InstId`) is a concrete runtime singleton iff:
/// 1. Its owning basic block does **not** belong to any natural or irreducible
///    loop in its owning function (computed via iterative Tarjan SCC over the
///    function's exception-augmented CFG: `scc.len() >= 2` or self-edge `b -> b`), AND
/// 2. Its owning [`FuncId`] is a **single-execution function** (a non-escaped
///    top-level initializer / single-run entry root, or a non-escaped function
///    with at most one resolved non-loop call site from another single-execution
///    function — never a multi-call helper, constructor, method, closure
///    callback, generator, or steady-state lifecycle hook).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SingletonSiteClassifier {
    inst_block: Vec<Option<BlockId>>,
    block_func: Vec<Option<FuncId>>,
    loop_blocks: Vec<bool>,
    single_exec_funcs: Vec<bool>,
}

impl SingletonSiteClassifier {
    /// Precompute loop-block and single-execution-function bitsets over `module`
    /// and `callgraph`.
    #[must_use]
    pub fn build(module: &Module, callgraph: &CallGraph) -> Self {
        Self::build_with_harness(module, callgraph, None)
    }

    /// Precompute loop-block and single-execution-function bitsets with an
    /// explicit optional lifecycle `harness_func`.
    #[must_use]
    pub fn build_with_harness(
        module: &Module,
        callgraph: &CallGraph,
        harness_func: Option<FuncId>,
    ) -> Self {
        let links = ModuleLinkTable::build(module);
        Self::build_with_links(module, &links, callgraph, harness_func)
    }

    /// Precompute loop-block and single-execution-function bitsets reusing a
    /// prebuilt [`ModuleLinkTable`].
    #[must_use]
    pub fn build_with_links(
        module: &Module,
        links: &ModuleLinkTable,
        callgraph: &CallGraph,
        harness_func: Option<FuncId>,
    ) -> Self {
        let num_funcs = module.functions.len();
        let num_blocks = module.blocks.len();
        let num_insts = module.insts.len();

        let mut inst_block = vec![None; num_insts];
        let mut block_func = vec![None; num_blocks];
        let mut loop_blocks = vec![false; num_blocks];

        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            for &b in &fd.blocks {
                if let Some(slot) = block_func.get_mut(b.index()) {
                    *slot = Some(fid);
                }
                if let Some(bb) = module.block(b) {
                    for &iid in &bb.insts {
                        if let Some(slot) = inst_block.get_mut(iid.index()) {
                            *slot = Some(b);
                        }
                    }
                }
            }
            if !fd.is_external && !fd.blocks.is_empty() {
                mark_function_loop_blocks(module, fid, &fd.blocks, &mut loop_blocks);
            }
        }

        let ClosureCallability {
            escaped,
            val_funcs,
            effective_callers,
        } = analyze_closure_callability(module, links, callgraph, &loop_blocks);
        let mut single_exec_funcs = vec![false; num_funcs];

        // Determine whether `module` carries canonical top-level entry roots
        // (`func_main_0`, `<cctor>`, or the lifecycle harness). Synthetic unit
        // test modules with none of those names treat unescaped 0-caller
        // `FunctionKind::Function` roots as single-execution entries.
        let has_named_init_root = harness_func.is_some()
            || module.functions.iter().any(|fd| {
                !fd.is_external
                    && !fd.blocks.is_empty()
                    && matches!(
                        module.sym.resolve(fd.name),
                        Some("func_main_0" | "<cctor>" | crate::ohos_lifecycle::OHOS_HARNESS_FUNC)
                    )
            });

        let mut queue = VecDeque::new();
        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if fd.is_external || fd.blocks.is_empty() || escaped[fi] {
                continue;
            }
            if !effective_callers[fi].is_empty() {
                continue;
            }
            let is_root = if has_named_init_root {
                Some(fid) == harness_func
                    || matches!(
                        module.sym.resolve(fd.name),
                        Some("func_main_0" | "<cctor>" | crate::ohos_lifecycle::OHOS_HARNESS_FUNC)
                    )
            } else {
                fd.kind == FunctionKind::Function
            };
            if is_root {
                single_exec_funcs[fi] = true;
                queue.push_back(fid);
            }
        }

        // Propagate single-execution status downward across single non-loop
        // call sites (`<= 1` caller total across both `CallGraph` and closed
        // top-level global function bindings, `0` loop/escaped callers).
        while let Some(caller) = queue.pop_front() {
            let Some(cfd) = module.func(caller) else {
                continue;
            };
            for &b in &cfd.blocks {
                if loop_blocks.get(b.index()).copied().unwrap_or(false) {
                    continue;
                }
                let Some(bb) = module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let Op::Call { callee: cal_v, .. } = &inst.op else {
                        continue;
                    };
                    let mut targets: BTreeSet<FuncId> = BTreeSet::new();
                    if let Some(edge) = callgraph.edge_at(iid)
                        && let CallTargets::Resolved(ts) = &edge.targets
                    {
                        targets.extend(ts.iter().copied());
                    }
                    if let Some(vf) = val_funcs.get(cal_v.index()) {
                        targets.extend(vf.iter().copied());
                    }
                    for callee in targets {
                        let ci = callee.index();
                        if ci >= num_funcs || single_exec_funcs[ci] || escaped[ci] {
                            continue;
                        }
                        let Some(callee_fd) = module.func(callee) else {
                            continue;
                        };
                        if callee_fd.is_external || callee_fd.blocks.is_empty() {
                            continue;
                        }
                        if effective_callers[ci].as_slice() == [iid] {
                            single_exec_funcs[ci] = true;
                            queue.push_back(callee);
                        }
                    }
                }
            }
        }

        Self {
            inst_block,
            block_func,
            loop_blocks,
            single_exec_funcs,
        }
    }

    /// Build a classifier directly from `module` (computing [`CallGraph::build`]).
    #[must_use]
    pub fn from_module(module: &Module) -> Self {
        let links = ModuleLinkTable::build(module);
        let cg = CallGraph::build_with_links(module, &links);
        Self::build_with_links(module, &links, &cg, None)
    }

    #[inline]
    pub(crate) fn site_is_concrete(&self, site: InstId) -> bool {
        let Some(block) = self.inst_block.get(site.index()).copied().flatten() else {
            return false;
        };
        if self.is_loop_block(block) {
            return false;
        }
        let Some(func) = self.block_func.get(block.index()).copied().flatten() else {
            return false;
        };
        self.is_single_execution_func(func)
    }

    /// `O(1)` query: whether `site` executes at most once in a concrete program run.
    #[must_use]
    #[inline]
    pub fn is_concrete_singleton_site(&self, site: InstId) -> bool {
        self.site_is_concrete(site)
    }

    /// `O(1)` query: whether `block` belongs to any natural or irreducible loop.
    #[must_use]
    #[inline]
    pub fn is_loop_block(&self, block: BlockId) -> bool {
        self.loop_blocks
            .get(block.index())
            .copied()
            .unwrap_or(false)
    }

    /// `O(1)` query: whether `func` executes at most once per program run.
    #[must_use]
    #[inline]
    pub fn is_single_execution_func(&self, func: FuncId) -> bool {
        self.single_exec_funcs
            .get(func.index())
            .copied()
            .unwrap_or(false)
    }

    /// Concrete-singleton-gated store update kind for `info`.
    #[must_use]
    #[inline]
    pub fn update_kind(&self, info: &SiteInfo) -> UpdateKind {
        update_kind_for(info, self)
    }

    /// Normalize a [`SiteInfo`] so single-site summaries that are NOT concrete
    /// runtime singletons mark `has_phi = true` (forcing weak updates downstream
    /// while preserving `sites` for heap fact keying).
    #[must_use]
    #[inline]
    pub fn gate_site_info(&self, mut info: SiteInfo) -> SiteInfo {
        if info.sites.len() == 1
            && !info.has_phi
            && let Some(site) = info.sites.iter().next()
            && !self.site_is_concrete(site)
        {
            info.has_phi = true;
        }
        info
    }
}

/// Convenience helper checking whether `site` is a concrete runtime singleton in `module`.
///
/// Hot callers querying multiple sites should construct [`SingletonSiteClassifier`]
/// once and call [`SingletonSiteClassifier::is_concrete_singleton_site`] (`O(1)`).
#[must_use]
pub fn is_concrete_singleton_site(module: &Module, site: InstId) -> bool {
    let classifier = SingletonSiteClassifier::from_module(module);
    classifier.site_is_concrete(site)
}

/// Mark every block in `blocks` belonging to a loop (an SCC of size `>= 2` or
/// a self-edge `b -> b` under exception-augmented CFG edges) via iterative Tarjan SCC.
fn mark_function_loop_blocks(
    module: &Module,
    func_id: FuncId,
    blocks: &[BlockId],
    loop_blocks: &mut [bool],
) {
    let n = blocks.len();
    if n == 0 {
        return;
    }
    let Some(exc_map) = ExceptionHandlerMap::build(module, func_id) else {
        return;
    };

    let mut adj: Vec<Vec<usize>> = Vec::with_capacity(n);
    let mut has_self_edge = vec![false; n];
    for (u_idx, &bb) in blocks.iter().enumerate() {
        let mut succ_indices = Vec::new();
        for succ_bb in augmented_succs_with_map(module, &exc_map, bb) {
            if let Some(v_idx) = exc_map.block_index(succ_bb) {
                if v_idx == u_idx {
                    has_self_edge[u_idx] = true;
                }
                succ_indices.push(v_idx);
            }
        }
        adj.push(succ_indices);
    }

    let mut index_of = vec![u32::MAX; n];
    let mut lowlink = vec![u32::MAX; n];
    let mut on_stack = vec![false; n];
    let mut scc_stack: Vec<usize> = Vec::with_capacity(n);
    let mut dfs_stack: Vec<(usize, usize)> = Vec::with_capacity(n);
    let mut next_index = 0u32;

    for root in 0..n {
        if index_of[root] != u32::MAX {
            continue;
        }
        index_of[root] = next_index;
        lowlink[root] = next_index;
        next_index += 1;
        on_stack[root] = true;
        scc_stack.push(root);
        dfs_stack.push((root, 0));

        while let Some((u_ref, edge_idx)) = dfs_stack.last_mut() {
            let u = *u_ref;
            if *edge_idx < adj[u].len() {
                let w = adj[u][*edge_idx];
                *edge_idx += 1;
                if index_of[w] == u32::MAX {
                    index_of[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    on_stack[w] = true;
                    scc_stack.push(w);
                    dfs_stack.push((w, 0));
                } else if on_stack[w] && index_of[w] < lowlink[u] {
                    lowlink[u] = index_of[w];
                }
            } else {
                dfs_stack.pop();
                if let Some(&(parent, _)) = dfs_stack.last()
                    && lowlink[u] < lowlink[parent]
                {
                    lowlink[parent] = lowlink[u];
                }
                if lowlink[u] == index_of[u] {
                    let mut scc = Vec::new();
                    while let Some(w) = scc_stack.pop() {
                        on_stack[w] = false;
                        scc.push(w);
                        if w == u {
                            break;
                        }
                    }
                    if scc.len() >= 2 || (scc.len() == 1 && has_self_edge[u]) {
                        for member_idx in scc {
                            if let Some(slot) = loop_blocks.get_mut(blocks[member_idx].index()) {
                                *slot = true;
                            }
                        }
                    }
                }
            }
        }
    }
}

struct ClosureCallability {
    escaped: Vec<bool>,
    val_funcs: Vec<BTreeSet<FuncId>>,
    effective_callers: Vec<Vec<InstId>>,
}

fn is_global_obj_val(module: &Module, v: ValueId) -> bool {
    let peeled = peel_movs(module, v);
    matches!(
        module.value(peeled).map(|val| val.def),
        Some(ValueDef::Inst(iid)) if matches!(module.inst(iid).map(|i| &i.op), Some(Op::LoadGlobalObject))
    )
}

fn is_benign_undef_init(module: &Module, v: ValueId) -> bool {
    let peeled = peel_movs(module, v);
    match module.value(peeled).map(|val| val.def) {
        Some(ValueDef::Const(cid)) => matches!(module.consts.get(cid), Some(Const::Undefined)),
        Some(ValueDef::Inst(iid)) => matches!(
            module.inst(iid).map(|i| &i.op),
            Some(Op::LoadConst(cid)) if matches!(module.consts.get(*cid), Some(Const::Undefined))
        ),
        _ => false,
    }
}

fn is_direct_func_def_val(module: &Module, v: ValueId) -> Option<FuncId> {
    let mut cur = v;
    for _ in 0..16 {
        let val = module.value(cur)?;
        match val.def {
            ValueDef::Const(cid) => match module.consts.get(cid)? {
                Const::MethodRef { func, .. } => return Some(*func),
                _ => return None,
            },
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src } | Op::AllocClosure { func: src } => cur = *src,
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(cid) => match module.consts.get(*cid)? {
                    Const::MethodRef { func, .. } => return Some(*func),
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        }
    }
    None
}

/// Conservatively classify functions that may be invoked as constructors,
/// methods, getters/setters, generators, OHOS lifecycle components, or escaped
/// first-class closures (any use other than closed global function bindings or
/// the `callee` operand of a resolved / closed-global [`Op::Call`]).
fn analyze_closure_callability(
    module: &Module,
    links: &ModuleLinkTable,
    callgraph: &CallGraph,
    loop_blocks: &[bool],
) -> ClosureCallability {
    let n_funcs = module.functions.len();
    let mut escaped = vec![false; n_funcs];

    for (fi, fd) in module.functions.iter().enumerate() {
        if fd.is_external
            || fd.blocks.is_empty()
            || matches!(
                fd.kind,
                FunctionKind::Constructor
                    | FunctionKind::Getter
                    | FunctionKind::Setter
                    | FunctionKind::Generator
                    | FunctionKind::AsyncGenerator
            )
        {
            escaped[fi] = true;
        }
    }

    // Static ArkTS class methods may be dispatched virtually or externally.
    if module.dialect == abcd_ir::Dialect::StaticArkTS {
        for cls in &module.classes {
            let desc = module.sym.resolve(cls.descriptor).unwrap_or("");
            if desc != "L_GLOBAL;"
                && desc != "LETSGLOBAL;"
                && !desc.ends_with("/ETSGLOBAL;")
                && cls.es_module.is_none()
            {
                for &mfid in &cls.methods {
                    let mname = module
                        .func(mfid)
                        .and_then(|f| module.sym.resolve(f.name))
                        .unwrap_or("");
                    if mname != "func_main_0"
                        && mname != "<cctor>"
                        && mname != crate::ohos_lifecycle::OHOS_HARNESS_FUNC
                        && let Some(slot) = escaped.get_mut(mfid.index())
                    {
                        *slot = true;
                    }
                }
            }
        }
    }

    // OHOS discovered components (Ability / ExtensionAbility / ArkUI View methods).
    for comp in crate::ohos_lifecycle::discover_components(module, links, None) {
        if let Some(slot) = escaped.get_mut(comp.ctor.index()) {
            *slot = true;
        }
        for fids in comp.methods.values() {
            for &mfid in fids {
                if let Some(slot) = escaped.get_mut(mfid.index()) {
                    *slot = true;
                }
            }
        }
    }

    // Identify closed top-level global function bindings (`function foo() {}`
    // compiled by `es2abc` as `[stglobalvar "foo" = undefined;] definefunc foo;
    // stglobalvar "foo"`): safe iff `globalThis` is not dynamically mutated and
    // every store to `"foo"` is either `undefined` or the same single `FuncId`
    // at a single non-loop store site.
    let mut global_obj_tampered = false;
    let mut global_store_state: std::collections::BTreeMap<abcd_ir::Sym, Option<(FuncId, usize)>> =
        std::collections::BTreeMap::new();
    let mut global_loads: std::collections::BTreeMap<abcd_ir::Sym, Vec<ValueId>> =
        std::collections::BTreeMap::new();

    for fd in &module.functions {
        for &b in &fd.blocks {
            let in_loop = loop_blocks.get(b.index()).copied().unwrap_or(false);
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::StoreGlobal { name, value } | Op::StoreGlobalRecord { name, value, .. } => {
                        if is_benign_undef_init(module, *value) {
                            continue;
                        }
                        if !in_loop && let Some(fn_id) = is_direct_func_def_val(module, *value) {
                            let entry = global_store_state.entry(*name).or_insert(Some((fn_id, 0)));
                            match entry {
                                Some((prev_fn, cnt)) if *prev_fn == fn_id && *cnt == 0 => {
                                    *cnt = 1;
                                }
                                _ => *entry = None,
                            }
                        } else {
                            global_store_state.insert(*name, None);
                        }
                    }
                    Op::StoreProp {
                        object,
                        name,
                        value,
                    } if is_global_obj_val(module, *object) => {
                        if is_benign_undef_init(module, *value) {
                            continue;
                        }
                        if !in_loop && let Some(fn_id) = is_direct_func_def_val(module, *value) {
                            let entry = global_store_state.entry(*name).or_insert(Some((fn_id, 0)));
                            match entry {
                                Some((prev_fn, cnt)) if *prev_fn == fn_id && *cnt == 0 => {
                                    *cnt = 1;
                                }
                                _ => *entry = None,
                            }
                        } else {
                            global_store_state.insert(*name, None);
                        }
                    }
                    Op::StorePropIdx { object, .. }
                    | Op::StorePropDyn { object, .. }
                    | Op::DeleteProp { object, .. }
                        if is_global_obj_val(module, *object) =>
                    {
                        global_obj_tampered = true;
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if let Some(res) = inst.result {
                            global_loads.entry(*name).or_default().push(res);
                        }
                    }
                    Op::LoadProp { object, name } if is_global_obj_val(module, *object) => {
                        if let Some(res) = inst.result {
                            global_loads.entry(*name).or_default().push(res);
                        }
                    }
                    other => {
                        if !matches!(other, Op::LoadGlobalObject | Op::Mov { .. }) {
                            other.for_each_operand(|op_val| {
                                if is_global_obj_val(module, op_val) {
                                    global_obj_tampered = true;
                                }
                            });
                        }
                    }
                }
            }
        }
    }

    let mut closed_globals: std::collections::BTreeMap<abcd_ir::Sym, FuncId> =
        std::collections::BTreeMap::new();
    if !global_obj_tampered {
        for (sym, state) in global_store_state {
            if let Some((fn_id, 1)) = state {
                closed_globals.insert(sym, fn_id);
            }
        }
    }

    // Seed SSA values carrying callable `FuncId`s and propagate through
    // `Mov` / `AllocClosure` / `Phi` + closed single-function globals.
    let mut val_funcs: Vec<BTreeSet<FuncId>> = vec![BTreeSet::new(); module.values.len()];
    let mut val_closed_only: Vec<bool> = vec![true; module.values.len()];
    let mut copy_edges: Vec<Vec<ValueId>> = vec![Vec::new(); module.values.len()];
    let mut queue: VecDeque<ValueId> = VecDeque::new();

    for (&sym, &fn_id) in &closed_globals {
        if let Some(loads) = global_loads.get(&sym) {
            for &res in loads {
                if let Some(set) = val_funcs.get_mut(res.index())
                    && set.insert(fn_id)
                {
                    queue.push_back(res);
                }
            }
        }
    }

    for (vi, val) in module.values.iter().enumerate() {
        if let ValueDef::Const(cid) = val.def
            && let Some(Const::MethodRef { func, .. }) = module.consts.get(cid)
        {
            let vid = ValueId::new(vi as u32);
            val_funcs[vi].insert(*func);
            queue.push_back(vid);
        } else if !matches!(val.def, ValueDef::Inst(_)) {
            val_closed_only[vi] = false;
        }
    }

    for (fi, fd) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if let Some(slot) = escaped.get_mut(cls.ctor.index()) {
                            *slot = true;
                        }
                        mark_const_pool_funcs(module, cls.members, &mut escaped);
                        if let Some(res) = inst.result {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    Op::AllocObject { shape } => {
                        mark_const_pool_funcs(module, *shape, &mut escaped);
                        if let Some(res) = inst.result {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    Op::AllocArray { shape: Some(shape) } => {
                        mark_const_pool_funcs(module, *shape, &mut escaped);
                        if let Some(res) = inst.result {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        if let Some(res) = inst.result
                            && let Some(set) = val_funcs.get_mut(res.index())
                            && set.insert(*body)
                        {
                            queue.push_back(res);
                        }
                    }
                    Op::LoadConst(cid) => {
                        if let Some(Const::MethodRef { func, .. }) = module.consts.get(*cid) {
                            if let Some(res) = inst.result
                                && let Some(set) = val_funcs.get_mut(res.index())
                                && set.insert(*func)
                            {
                                queue.push_back(res);
                            }
                        } else if let Some(res) = inst.result {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    Op::LoadFunction => {
                        if let Some(res) = inst.result
                            && let Some(set) = val_funcs.get_mut(res.index())
                            && set.insert(fid)
                        {
                            queue.push_back(res);
                        }
                    }
                    Op::Mov { src } | Op::AllocClosure { func: src } => {
                        if let Some(res) = inst.result
                            && let Some(outs) = copy_edges.get_mut(src.index())
                        {
                            outs.push(res);
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(res) = inst.result {
                            for (_, incoming) in entries {
                                if let Some(outs) = copy_edges.get_mut(incoming.index()) {
                                    outs.push(res);
                                }
                            }
                        }
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if !closed_globals.contains_key(name)
                            && let Some(res) = inst.result
                        {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    Op::LoadProp { object, name } if is_global_obj_val(module, *object) => {
                        if !closed_globals.contains_key(name)
                            && let Some(res) = inst.result
                        {
                            val_closed_only[res.index()] = false;
                        }
                    }
                    _ => {
                        if let Some(res) = inst.result {
                            val_closed_only[res.index()] = false;
                        }
                    }
                }
            }
        }
    }

    for (vi, &closed) in val_closed_only.iter().enumerate() {
        if !closed {
            queue.push_back(ValueId::new(vi as u32));
        }
    }

    while let Some(v) = queue.pop_front() {
        let cur = val_funcs.get(v.index()).cloned().unwrap_or_default();
        let closed = val_closed_only.get(v.index()).copied().unwrap_or(false);
        let outs = copy_edges.get(v.index()).cloned().unwrap_or_default();
        for dst in outs {
            let mut changed = false;
            if !closed && val_closed_only[dst.index()] {
                val_closed_only[dst.index()] = false;
                changed = true;
            }
            if !cur.is_empty()
                && let Some(dst_set) = val_funcs.get_mut(dst.index())
            {
                let before = dst_set.len();
                dst_set.extend(cur.iter().copied());
                if dst_set.len() > before {
                    changed = true;
                }
            }
            if changed {
                queue.push_back(dst);
            }
        }
    }

    let mut effective_callers_sets: Vec<BTreeSet<InstId>> = vec![BTreeSet::new(); n_funcs];
    for (fi, cset) in effective_callers_sets.iter_mut().enumerate() {
        for &cid in callgraph.callers_of(FuncId::new(fi as u32)) {
            cset.insert(cid);
        }
    }

    // Any callable value appearing outside a pure propagation op (`Mov`,
    // `AllocClosure`, `Phi`), outside a closed single-function global store, or
    // outside the `callee` slot of a resolved / closed-only `Call` marks its
    // `FuncId`s escaped.
    for fd in &module.functions {
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Mov { .. } | Op::AllocClosure { .. } | Op::Phi { .. } => {}
                    Op::StoreGlobal { name, .. } | Op::StoreGlobalRecord { name, .. }
                        if closed_globals.contains_key(name) => {}
                    Op::StoreProp { object, name, .. }
                        if is_global_obj_val(module, *object)
                            && closed_globals.contains_key(name) => {}
                    Op::Call {
                        callee, this, args, ..
                    } => {
                        let closed_callee = val_closed_only
                            .get(callee.index())
                            .copied()
                            .unwrap_or(false)
                            && val_funcs.get(callee.index()).is_some_and(|s| s.len() == 1);
                        let complete = callgraph
                            .edge_at(iid)
                            .is_some_and(|e| e.resolution_complete)
                            || closed_callee;
                        if let Some(fset) = val_funcs.get(callee.index()) {
                            for &f in fset {
                                if let Some(cset) = effective_callers_sets.get_mut(f.index()) {
                                    cset.insert(iid);
                                }
                            }
                        }
                        if !complete {
                            mark_value_funcs_escaped(*callee, &val_funcs, &mut escaped);
                        }
                        if let Some(t) = this {
                            mark_value_funcs_escaped(*t, &val_funcs, &mut escaped);
                        }
                        for &a in args {
                            mark_value_funcs_escaped(a, &val_funcs, &mut escaped);
                        }
                    }
                    other => {
                        other.for_each_operand(|op_val| {
                            mark_value_funcs_escaped(op_val, &val_funcs, &mut escaped);
                        });
                    }
                }
            }
        }
    }

    let effective_callers = effective_callers_sets
        .into_iter()
        .map(|s| s.into_iter().collect())
        .collect();

    ClosureCallability {
        escaped,
        val_funcs,
        effective_callers,
    }
}

fn mark_value_funcs_escaped(v: ValueId, val_funcs: &[BTreeSet<FuncId>], escaped: &mut [bool]) {
    if let Some(fset) = val_funcs.get(v.index()) {
        for &f in fset {
            if let Some(slot) = escaped.get_mut(f.index()) {
                *slot = true;
            }
        }
    }
}

fn mark_const_pool_funcs(module: &Module, root: ConstId, escaped: &mut [bool]) {
    let mut visited = HashSet::new();
    let mut stack = vec![root];
    while let Some(cid) = stack.pop() {
        if !visited.insert(cid) {
            continue;
        }
        match module.consts.get(cid) {
            Some(Const::MethodRef { func, .. }) => {
                if let Some(slot) = escaped.get_mut(func.index()) {
                    *slot = true;
                }
            }
            Some(Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. }) => {
                for &ch in items {
                    stack.push(ch);
                }
            }
            Some(Const::ObjectLiteral { keys, values }) => {
                for &ch in keys.iter().chain(values.iter()) {
                    stack.push(ch);
                }
            }
            Some(Const::LiteralBufferRef(inner)) => stack.push(*inner),
            _ => {}
        }
    }
}

/// Whether `op` allocates one of the four rung-0 keyed sites
/// (`design/ir.md`, `design/analysis.md` — other allocating ops such as
/// `CreateIterResultObj` or `GetUnmappedArgs` are *unkeyed* and
/// conservatively count as unknown).
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
    // Explicit work stack: the def-chain depth is input-driven, so this
    // must not recurse. All side effects are set unions / monotone flags,
    // so the visit order is unobservable.
    let mut stack = vec![value];
    while let Some(value) = stack.pop() {
        if !visiting.insert(value) {
            // A def-chain cycle (only possible through phis): treat as a
            // phi merge and stop.
            info.has_phi = true;
            continue;
        }
        let Some(v) = module.value(value) else {
            info.has_unknown = true;
            continue;
        };
        match v.def {
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => {
                info.has_unknown = true;
            }
            ValueDef::Const(_) => {
                // Constants are not heap allocations: they contribute no
                // site and are not "unknown heap" either.
            }
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => stack.push(*src),
                Some(Op::Phi { entries }) => {
                    info.has_phi = true;
                    for (_, v) in entries {
                        stack.push(*v);
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

/// Peel `Op::Mov` copies backward to the underlying non-`Mov` SSA definition,
/// cycle-guarded via a `HashSet<ValueId>` with no hop cap (`#82`).
#[must_use]
pub fn peel_movs(module: &Module, mut val: ValueId) -> ValueId {
    let mut visited = HashSet::new();
    while visited.insert(val) {
        let Some(ValueDef::Inst(iid)) = module.value(val).map(|v| v.def) else {
            break;
        };
        let Some(Op::Mov { src }) = module.inst(iid).map(|i| &i.op) else {
            break;
        };
        val = *src;
    }
    val
}

/// Policy marker seam for heap aliasing across the precision ladder
/// (`design/analysis.md`), generalized over the client's fact type `F` so
/// `abcd-analysis` never depends on `abcd-taint`.
///
/// Downstream clients key facts directly by [`AllocSiteSet`] and invoke the
/// inherent oracle queries (`resolve`, `site_info_at`, `lex_env_at`).
pub trait AliasOracle<F> {}

/// The rung-0 oracle: local SSA def-chain answers only (`design/analysis.md`).
/// Cheap, total, and conservative; every undecidable case degrades to
/// `Unknown`/weak.
pub struct Rung0AliasOracle<'m> {
    module: &'m Module,
    memo: std::cell::RefCell<HashMap<ValueId, SiteInfo>>,
    singletons: OnceLock<SingletonSiteClassifier>,
}

impl<'m> Rung0AliasOracle<'m> {
    /// An oracle over `module` with an empty memo table.
    pub fn new(module: &'m Module) -> Self {
        Self {
            module,
            memo: std::cell::RefCell::new(HashMap::new()),
            singletons: OnceLock::new(),
        }
    }

    /// Lazily built [`SingletonSiteClassifier`] for `module`.
    pub fn singletons(&self) -> &SingletonSiteClassifier {
        self.singletons
            .get_or_init(|| SingletonSiteClassifier::from_module(self.module))
    }

    /// `O(1)` query (after first build): whether `site` is a concrete runtime singleton.
    pub fn is_concrete_singleton_site(&self, site: InstId) -> bool {
        self.singletons().site_is_concrete(site)
    }

    /// The (memoized) local SSA site resolution of `value`.
    pub fn resolve(&self, value: ValueId) -> SiteInfo {
        if let Some(hit) = self.memo.borrow().get(&value) {
            return hit.clone();
        }
        let info = resolve_alloc_sites(self.module, value);
        self.memo.borrow_mut().insert(value, info.clone());
        info
    }

    /// Concrete-singleton-gated site resolution at `at` (uniform with Rung 1/2).
    pub fn site_info_at(&self, base: ValueId, _at: InstId) -> SiteInfo {
        self.singletons().gate_site_info(self.resolve(base))
    }

    /// The store-update kind for a base value (`Strong` iff concrete runtime singleton).
    pub fn update_kind_of(&self, base: ValueId) -> UpdateKind {
        self.singletons().update_kind(&self.resolve(base))
    }
}

impl<F> AliasOracle<F> for Rung0AliasOracle<'_> {}

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

        // The oracle seam's must-alias/points-to delegates were deleted
        // as dead surface; the same answers come from `resolve`:
        // must-alias = both sides single-precise with equal sites,
        // points-to = the resolved site set.
        let oracle = Rung0AliasOracle::new(&m);
        let (a, b) = (oracle.resolve(obj), oracle.resolve(alias));
        assert!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites);
        assert_eq!(oracle.resolve(alias).sites.len(), 1);
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
        // Not must-alias: the phi side is not single-precise.
        let (pa, pb) = (oracle.resolve(phi), oracle.resolve(a));
        assert!(!(pa.is_single_precise() && pb.is_single_precise() && pa.sites == pb.sites));
        assert_eq!(oracle.resolve(phi).sites.len(), 2);
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
        let (a, b) = (oracle.resolve(arr), oracle.resolve(obj));
        assert!(!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites));
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
        // Not must-alias: an unknown-source value is not single-precise.
        let (a, b) = (oracle.resolve(loaded), oracle.resolve(loaded));
        assert!(!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites));
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

        // The oracle seam's may-alias delegate was deleted as dead
        // surface; it was a pure forward to `key_may_alias`.
        let same = HeapRef {
            sites: s1.clone(),
            fields: f1.clone(),
        };
        assert_eq!(key_may_alias(&same, &same.clone()), Tribool::True);
        // Different named fields: never the same location.
        let other_field = HeapRef {
            sites: s1.clone(),
            fields: f2,
        };
        assert_eq!(key_may_alias(&same, &other_field), Tribool::False);
        // Same field, disjoint sites: different objects.
        let other_obj = HeapRef {
            sites: s2,
            fields: f1.clone(),
        };
        assert_eq!(key_may_alias(&same, &other_obj), Tribool::False);
        // Same field, unknown sites on one side: undecidable.
        let unknown = HeapRef {
            sites: AllocSiteSet::new(),
            fields: f1,
        };
        assert_eq!(key_may_alias(&same, &unknown), Tribool::Unknown);
    }

    #[test]
    fn concrete_singleton_classifier_gates_loops_multi_call_helpers_and_escaped_closures() {
        let mut m = mk_module();

        // 1. `single_helper`: called ONCE from `func_main_0` outside any loop -> singleton!
        let single_helper = add_func_named(&mut m, "single_helper");
        let b_sh = entry_of(&m, single_helper);
        let obj_single_helper = alloc_object(&mut m, b_sh);
        let site_single_helper = m.blocks[b_sh.index()].insts[0];
        emit_void(
            &mut m,
            b_sh,
            Op::Return {
                value: Some(obj_single_helper),
            },
        );

        // 2. `multi_helper`: called TWICE from `func_main_0` -> NOT singleton!
        let multi_helper = add_func_named(&mut m, "multi_helper");
        let b_mh = entry_of(&m, multi_helper);
        let obj_multi_helper = alloc_object(&mut m, b_mh);
        let site_multi_helper = m.blocks[b_mh.index()].insts[0];
        emit_void(
            &mut m,
            b_mh,
            Op::Return {
                value: Some(obj_multi_helper),
            },
        );

        // 3. `escaped_cb`: stored onto an object -> NOT singleton!
        let escaped_cb = add_func_named(&mut m, "escaped_cb");
        let b_cb = entry_of(&m, escaped_cb);
        let obj_escaped = alloc_object(&mut m, b_cb);
        let site_escaped = m.blocks[b_cb.index()].insts[0];
        emit_void(
            &mut m,
            b_cb,
            Op::Return {
                value: Some(obj_escaped),
            },
        );

        // 4. `func_main_0`: top-level alloc, natural `while` loop alloc, and
        //    irreducible 2-entry loop (`ir1 <-> ir2`) alloc.
        let main_fn = add_func_named(&mut m, "func_main_0");
        let b_entry = entry_of(&m, main_fn);
        let b_while_head = add_block(&mut m, main_fn);
        let b_while_body = add_block(&mut m, main_fn);
        let b_ir1 = add_block(&mut m, main_fn);
        let b_ir2 = add_block(&mut m, main_fn);
        let b_exit = add_block(&mut m, main_fn);

        let obj_top = alloc_object(&mut m, b_entry);
        let site_top = m.blocks[b_entry.index()].insts[0];

        let sh_ref = load_method_ref(&mut m, b_entry, single_helper);
        let _ = emit(
            &mut m,
            b_entry,
            Op::Call {
                callee: sh_ref,
                this: None,
                args: Vec::new(),
                kind: abcd_ir::CallKind::Direct,
            },
        );
        let mh_ref = load_method_ref(&mut m, b_entry, multi_helper);
        for _ in 0..2 {
            let _ = emit(
                &mut m,
                b_entry,
                Op::Call {
                    callee: mh_ref,
                    this: None,
                    args: Vec::new(),
                    kind: abcd_ir::CallKind::Direct,
                },
            );
        }
        let df_cb = emit(
            &mut m,
            b_entry,
            Op::DefineFunc {
                body: escaped_cb,
                captures: Vec::new(),
                length: 0,
            },
        );
        let cl_cb = emit(&mut m, b_entry, Op::AllocClosure { func: df_cb });
        let s_fn = intern(&mut m, "fn");
        emit_void(
            &mut m,
            b_entry,
            Op::StoreProp {
                object: obj_top,
                name: s_fn,
                value: cl_cb,
            },
        );
        emit_void(&mut m, b_entry, Op::Branch { dest: b_while_head });
        link(&mut m, b_entry, b_while_head);

        let cond = load_number(&mut m, b_while_head, 1.0);
        emit_void(
            &mut m,
            b_while_head,
            Op::CondBranch {
                cond,
                true_dest: b_while_body,
                false_dest: b_ir1,
            },
        );
        link(&mut m, b_while_head, b_while_body);
        link(&mut m, b_while_head, b_ir1);

        let obj_while = alloc_object(&mut m, b_while_body);
        let site_while = m.blocks[b_while_body.index()].insts[0];
        emit_void(
            &mut m,
            b_while_body,
            Op::CondBranch {
                cond,
                true_dest: b_while_head,
                false_dest: b_ir2,
            },
        );
        link(&mut m, b_while_body, b_while_head);
        link(&mut m, b_while_body, b_ir2);

        // Irreducible cycle `b_ir1 <-> b_ir2` entered from both `b_while_head` and `b_while_body`.
        let _ = alloc_object(&mut m, b_ir1);
        let site_ir1 = m.blocks[b_ir1.index()].insts[0];
        emit_void(
            &mut m,
            b_ir1,
            Op::CondBranch {
                cond,
                true_dest: b_ir2,
                false_dest: b_exit,
            },
        );
        link(&mut m, b_ir1, b_ir2);
        link(&mut m, b_ir1, b_exit);

        emit_void(&mut m, b_ir2, Op::Branch { dest: b_ir1 });
        link(&mut m, b_ir2, b_ir1);

        let ret_iid = emit_void(&mut m, b_exit, Op::Return { value: None });

        let cls = SingletonSiteClassifier::from_module(&m);
        assert!(cls.is_single_execution_func(main_fn));
        assert!(cls.is_single_execution_func(single_helper));
        assert!(!cls.is_single_execution_func(multi_helper));
        assert!(!cls.is_single_execution_func(escaped_cb));

        assert!(!cls.is_loop_block(b_entry));
        assert!(cls.is_loop_block(b_while_head));
        assert!(cls.is_loop_block(b_while_body));
        assert!(cls.is_loop_block(b_ir1));
        assert!(cls.is_loop_block(b_ir2));
        assert!(!cls.is_loop_block(b_exit));

        assert!(cls.is_concrete_singleton_site(site_top));
        assert!(cls.is_concrete_singleton_site(site_single_helper));
        assert!(!cls.is_concrete_singleton_site(site_while));
        assert!(!cls.is_concrete_singleton_site(site_ir1));
        assert!(!cls.is_concrete_singleton_site(site_multi_helper));
        assert!(!cls.is_concrete_singleton_site(site_escaped));
        assert!(is_concrete_singleton_site(&m, site_top));
        assert!(!is_concrete_singleton_site(&m, site_while));

        let r0 = Rung0AliasOracle::new(&m);
        assert_eq!(r0.update_kind_of(obj_top), UpdateKind::Strong);
        assert_eq!(r0.update_kind_of(obj_single_helper), UpdateKind::Strong);
        assert_eq!(r0.update_kind_of(obj_while), UpdateKind::Weak);
        assert_eq!(r0.update_kind_of(obj_multi_helper), UpdateKind::Weak);
        assert_eq!(r0.update_kind_of(obj_escaped), UpdateKind::Weak);
        assert!(!r0.site_info_at(obj_top, ret_iid).has_phi);
        assert!(r0.site_info_at(obj_while, ret_iid).has_phi);
        assert!(r0.site_info_at(obj_multi_helper, ret_iid).has_phi);
    }
}
