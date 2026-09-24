//! The taint IFDS problem: the four flow functions of
//! [`abcd_analysis::dataflow::ifds::IfdsProblem`] specialized to
//! [`Fact`].
//!
//! ## Design rule (task / analysis-strategy §5.1)
//!
//! Flow functions are driven by `Op::operands()` + `Op::has_result()` —
//! the generic rule "a tainted operand taints the result" covers
//! `Mov`/binops/unops/compares/coercions/iterators — with explicit
//! per-family rules ONLY where semantics demand:
//!
//! - **LoadProp family** (`LoadProp`/`LoadPropIdx`/`LoadPropDyn`):
//!   access-path push/cut at the field key (soot-infoflow §2.2's
//!   `cutFirstField` algebra), matching heap facts by alloc-site
//!   intersection and local facts by positive-alias evidence.
//! - **StoreProp family** (incl. the `StoreOwnProp*` own-stores): the
//!   stored value's taint is re-keyed to a heap fact
//!   `(sites(object), key ++ fields)`; strong kills only under the
//!   rung-0 must-alias proof (`update_kind == Strong`), weak otherwise.
//! - **Calls** ([`IfdsProblem::call_flow`] /
//!   [`IfdsProblem::call_to_return_flow`]): the §5.3 binding table for
//!   arg→param mapping, the summary wrapper on the call-to-return edge
//!   (summaries.md §2.1 — the interception point), exclusive-kill of the
//!   call edge into the callee, and the fallback ladder.
//! - **Return wiring** ([`IfdsProblem::return_flow`]): return value →
//!   call result on the normal continuation; thrown value → the catch
//!   handler's `ExceptionParam` binding on handler return sites (T5).
//! - **Exception edges**: intraprocedural `Throw` → handler entry maps
//!   the thrown value's taint onto the catch binding
//!   ([`ValueDef::ExceptionParam`]) — "ExceptionParam taints the catch
//!   binding".
//!
//! Everything else is pass-through (facts survive) plus the generic
//! operand→result rule.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::{AllocSiteSet, UpdateKind};
use abcd_analysis::dataflow::heap::{FieldChain, FieldKey, update_kind};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, IfdsProblem};
use abcd_ir::{CallKind, FuncId, InstId, Module, Op, Sym, ValueId};

use crate::driver::{SourceSpec, TaintConfig};
use crate::fact::{Fact, TaintBase, TaintFact};
use crate::gap;
use crate::names::{call_base_value, call_method_leaf, callee_name_candidates};
use crate::oracle::Oracle;
use crate::prototype::{FamilyAnswer, PrototypeResolver};
use crate::summary::{CallbackGap, Endpoint, FallbackStep, SummaryRegistry};

/// How a call site is handled — the fallback ladder, memoized per site.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SiteClass {
    /// A summary applies (registry hit).
    Summary { name: String, exclusive: bool },
    /// No summary; at least one resolved callee has a body — normal
    /// IFDS steps into it.
    BodyStep,
    /// No summary; callees are external or the callee is unknown but
    /// named (a global we have not summarized) — conservative keep.
    NativeKeep,
    /// No summary and no resolvable name — conservative keep.
    UnknownKeep,
}

/// How caller operands bind to callee params (N66; the frame-slot model
/// itself lives in `abcd_analysis::frame` — the alias engine's
/// interprocedural hops consume the same model).
///
/// When the annotation is ABSENT on a `<static>` callee the vendored
/// default is `callType = 0xF` — all three implicit slots — which is
/// exactly the es2abc corpus shape (every corpus function declares
/// `num_args = 3 + formals` and reads its first formal from `a3`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParamBinding {
    /// The frame-slot model resolved: `this` → `this_slot`, args[i] →
    /// `params[formal_base + i]` (left-aligned formals).
    Precise {
        /// Index of the this slot, when the callee has one.
        this_slot: Option<usize>,
        /// First formal's index in `params` (= implicit slot count).
        formal_base: usize,
    },
    /// No reliable slot model (NON-STATIC callee without a callType
    /// annotation — inline REFUSES these, but taint must never silently
    /// drop a flow — or a callee with fewer params than its implicit
    /// slots, e.g. hand-built test modules): conservative
    /// over-approximation — a tainted `this`/arg taints EVERY param.
    OverApproxAll,
}

/// Resolve the param binding for `callee`.
fn param_binding(module: &Module, callee: FuncId) -> ParamBinding {
    let Some(fd) = module.func(callee) else {
        return ParamBinding::OverApproxAll;
    };
    let Some(slots) = abcd_analysis::frame::frame_slots_of(module, callee) else {
        return ParamBinding::OverApproxAll;
    };
    if fd.params.len() < slots.implicit_count() {
        return ParamBinding::OverApproxAll;
    }
    ParamBinding::Precise {
        this_slot: slots.this_index(),
        formal_base: slots.implicit_count(),
    }
}

/// The taint problem over a module + call graph + the rung-selected
/// alias oracle ([`Oracle`]: rung-0 baseline or the rung-1 demand-driven
/// engine) + summary registry + source/sink config.
pub struct TaintProblem<'m> {
    module: &'m Module,
    callgraph: &'m CallGraph,
    oracle: RefCell<Oracle<'m>>,
    registry: &'m SummaryRegistry,
    config: &'m TaintConfig,
    /// `(func, param indices)` seeds, resolved from the config's
    /// function-name source specs at construction.
    param_seeds: Vec<(FuncId, Vec<ValueId>)>,
    /// Module-interned names whose `TryGetGlobal` results are sources.
    global_sources: HashSet<Sym>,
    /// Per-site fallback-ladder classification (memo).
    site_class: RefCell<HashMap<InstId, SiteClass>>,
    /// Sites already counted (counters are per-site, not per-fact).
    counted: RefCell<HashSet<InstId>>,
    /// The applied-summary log: `(call site, summary name)` in
    /// application order — reported by the driver.
    applied: RefCell<Vec<(InstId, String)>>,
    /// The t-P3 receiver-family memo (one entry per queried receiver
    /// value; engine answers are point-independent at rung 1).
    proto_memo: RefCell<HashMap<ValueId, FamilyAnswer>>,
    /// The t-P4 gap edges (eager scan, [`crate::gap`]): summary call
    /// site → resolved callback bodies. The driver layers them onto
    /// the solver's call graph (`GapCallGraph`); the flow functions
    /// consult them to recognize gap edges.
    gap_edges: BTreeMap<InstId, Vec<FuncId>>,
    /// The e13 fresh-result memo (rung 2; [`TaintProblem::fresh_result_site`]).
    fresh_memo: RefCell<HashMap<ValueId, Option<InstId>>>,
    /// Gap-wrapper counters (FlowDroid's gap-hit/miss analogue): call
    /// sites whose callback summary applied AND the callback value
    /// resolved to at least one user body.
    gap_resolved: usize,
    /// Callback-summary sites whose callback value did NOT resolve —
    /// the honest fallback (mini-gap tag only; gap.rs module docs).
    gap_unresolved: usize,
}

impl<'m> TaintProblem<'m> {
    /// Build the problem over `module`. Source specs that name functions
    /// are resolved against [`abcd_ir::FunctionData::name`]; global-load
    /// source names are interned into the module's symbol table copy —
    /// interning is by string equality, so a spec for a name the module
    /// never mentions simply never fires (the local table internment is
    /// keyed on the same strings via a side table below).
    pub fn new(
        module: &'m Module,
        callgraph: &'m CallGraph,
        oracle: Oracle<'m>,
        registry: &'m SummaryRegistry,
        config: &'m TaintConfig,
    ) -> Self {
        let mut param_seeds = Vec::new();
        let mut global_sources = HashSet::new();
        // The module's symbol table is behind a shared reference; source
        // name matching is done by STRING comparison against resolved
        // syms, so no mutation of the module is needed: we collect the
        // set of module syms whose string equals a global-source name.
        let global_names: HashSet<&str> = config
            .sources
            .iter()
            .filter_map(|s| match s {
                SourceSpec::GlobalLoad { name } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        if !global_names.is_empty() {
            for i in 0..module.sym.len() {
                let sym = Sym::new(i as u32);
                if let Some(s) = module.sym.resolve(sym) {
                    if global_names.contains(s) {
                        global_sources.insert(sym);
                    }
                }
            }
        }
        for spec in &config.sources {
            if let SourceSpec::FunctionParams { name, params } = spec {
                for (fi, f) in module.functions.iter().enumerate() {
                    // `"*"` is the sensitivity-analysis wildcard (every
                    // function's params are sources).
                    if name == "*" || module.sym.resolve(f.name) == Some(name.as_str()) {
                        let values: Vec<ValueId> = match params {
                            Some(indices) => indices
                                .iter()
                                .filter_map(|&i| f.params.get(i as usize).copied())
                                .collect(),
                            None => f.params.clone(),
                        };
                        if !values.is_empty() {
                            param_seeds.push((FuncId::new(fi as u32), values));
                        }
                    }
                }
            }
        }
        let mut problem = TaintProblem {
            module,
            callgraph,
            oracle: RefCell::new(oracle),
            registry,
            config,
            param_seeds,
            global_sources,
            site_class: RefCell::new(HashMap::new()),
            counted: RefCell::new(HashSet::new()),
            applied: RefCell::new(Vec::new()),
            proto_memo: RefCell::new(HashMap::new()),
            gap_edges: BTreeMap::new(),
            fresh_memo: RefCell::new(HashMap::new()),
            gap_resolved: 0,
            gap_unresolved: 0,
        };
        // The eager gap scan (t-P4, gap.rs): static edges, counter-free.
        let (edges, resolved, unresolved) = problem.scan_gap_edges();
        problem.gap_edges = edges;
        problem.gap_resolved = resolved;
        problem.gap_unresolved = unresolved;
        problem
    }

    /// The gap edges (t-P4 eager scan) — the driver layers them onto
    /// the solver's call graph via [`crate::gap::GapCallGraph`].
    pub fn gap_edges(&self) -> &BTreeMap<InstId, Vec<FuncId>> {
        &self.gap_edges
    }

    /// The gap-wrapper counters: `(sites with resolved callbacks, sites
    /// with unresolved callbacks)` (the honest fallback count).
    pub fn gap_counts(&self) -> (usize, usize) {
        (self.gap_resolved, self.gap_unresolved)
    }

    /// The eager gap scan (gap.rs §1): for every call site whose
    /// winning summary declares a full callback gap, resolve the
    /// callback argument to user bodies. COUNTER-FREE by construction —
    /// classification peeks (`compute_class(call, true)`), so the
    /// fallback-ladder counters keep classifying only solver-processed
    /// sites.
    fn scan_gap_edges(&self) -> (BTreeMap<InstId, Vec<FuncId>>, usize, usize) {
        let mut edges = BTreeMap::new();
        let mut resolved = 0usize;
        let mut unresolved = 0usize;
        for (call, _) in self.callgraph.sites() {
            let Some(inst) = self.module.inst(call) else {
                continue;
            };
            let Op::Call { args, .. } = &inst.op else {
                continue;
            };
            let SiteClass::Summary { name, .. } = self.compute_class(call, true).0 else {
                continue;
            };
            let Some(summary) = self.registry.peek(&name, args.len()) else {
                continue;
            };
            let Some(cb_gap) = &summary.callback else {
                continue;
            };
            if cb_gap.enter.is_empty() {
                continue; // mini-gap only — nothing to spawn
            }
            let Some(&cbv) = args.get(cb_gap.param as usize) else {
                unresolved += 1; // the callback argument is absent entirely
                continue;
            };
            let funcs = gap::resolve_callback_funcs(self.module, &self.oracle.borrow(), cbv, call);
            if funcs.is_empty() {
                // The not-a-callback refinement (t-P5): a slot filled
                // with a provably non-callable constant (the dual-form
                // `String.prototype.replace`'s string replacement) is
                // not a gap site at all — counting it as unresolved
                // would dilute the honest-fallback counter with sites
                // that have no user code to spawn into.
                if !gap::definitely_not_callable(self.module, cbv) {
                    unresolved += 1;
                }
            } else {
                resolved += 1;
                edges.insert(call, funcs);
            }
        }
        (edges, resolved, unresolved)
    }

    /// The gap spec when `(call, callee)` is a gap edge: the eager
    /// scan's map carries the edge; the site's winning summary carries
    /// the spec. Returns an owned copy (the registry borrow must not
    /// outlive the caller's flow-function borrows).
    fn gap_at(&self, call: InstId, callee: FuncId) -> Option<CallbackGap> {
        let funcs = self.gap_edges.get(&call)?;
        if !funcs.contains(&callee) {
            return None;
        }
        let SiteClass::Summary { name, .. } = self.classify(call) else {
            return None;
        };
        let argc = match self.module.inst(call).map(|i| &i.op) {
            Some(Op::Call { args, .. }) => args.len(),
            _ => return None,
        };
        self.registry
            .peek(&name, argc)
            .and_then(|s| s.callback.clone())
    }

    /// The applied-summary log (application order).
    pub fn applied_summaries(&self) -> Vec<(InstId, String)> {
        self.applied.borrow().clone()
    }

    /// The k-limit for field chains.
    fn cap(&self) -> usize {
        self.config.max_field_chain
    }

    /// Classify a call site on the fallback ladder (memoized; counters
    /// fire exactly once per site).
    ///
    /// The lookup precedence (t-P3; documented in the README):
    ///
    /// 1. **direct name match** — a summary registered under one of
    ///    the callee's def-chain name candidates wins (exclusive
    ///    summaries also win over resolved bodies — never merged);
    /// 2. **resolved user body** — a callee the call graph resolved to
    ///    a function with a body is stepped into (USER CODE beats the
    ///    builtin assumption of the prototype path — the receiver
    ///    type is a may-answer, the body is evidence);
    /// 3. **prototype-resolution path** — the receiver's alloc-kind /
    ///    constant / global-provenance family qualifies the method
    ///    leaf (`a.pop` + Array ⇒ `Array.prototype.pop`);
    ///    prototype-applied summaries are ALWAYS applied
    ///    non-exclusively (additive: flows are added, incoming taint
    ///    is retained — a may-typed receiver must never kill);
    /// 4. **native keep** (named) / **unknown keep** (no name).
    fn classify(&self, call: InstId) -> SiteClass {
        if let Some(c) = self.site_class.borrow().get(&call) {
            return c.clone();
        }
        // Non-call instructions keep the pre-refactor early-return
        // semantics: never memoized, never counted.
        let is_call = self
            .module
            .inst(call)
            .is_some_and(|i| matches!(i.op, Op::Call { .. }));
        if !is_call {
            return SiteClass::UnknownKeep;
        }
        let (class, tried) = self.compute_class(call, false);
        // Counters fire once per site.
        if self.counted.borrow_mut().insert(call) {
            match &class {
                SiteClass::Summary { name, .. } => self.registry.record_hit(name),
                SiteClass::BodyStep => self.registry.record_fallback(FallbackStep::BodyStep),
                SiteClass::NativeKeep => self.registry.record_fallback(FallbackStep::NativeKeep),
                SiteClass::UnknownKeep => self.registry.record_fallback(FallbackStep::Unknown),
            }
            if !matches!(&class, SiteClass::Summary { .. }) {
                for n in &tried {
                    self.registry.record_miss(n);
                }
            }
        }
        self.site_class.borrow_mut().insert(call, class.clone());
        class
    }

    /// The classification computation (the precedence table of
    /// [`TaintProblem::classify`]) without memoization or counters.
    /// `peek = true` routes registry queries through
    /// [`SummaryRegistry::peek`] — the eager gap scan's discipline, so
    /// the scan never perturbs the per-site counters. Returns the class
    /// plus the candidate names that missed (the backlog log's input
    /// when nothing rescues the site).
    fn compute_class(&self, call: InstId, peek: bool) -> (SiteClass, Vec<String>) {
        let Some(inst) = self.module.inst(call) else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let Op::Call { callee, args, .. } = &inst.op else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let argc = args.len();
        let mut names = callee_name_candidates(self.module, *callee);
        // Resolved callees contribute their FunctionData names (directly
        // resolved internal functions named like a builtin match too).
        let callees = self.callgraph.callees_of_call_at(call);
        for f in callees {
            if let Some(fd) = self.module.func(*f) {
                if let Some(n) = self.module.sym.resolve(fd.name) {
                    if !names.iter().any(|x| x == n) {
                        names.push(n.to_owned());
                    }
                }
            }
        }
        // Candidate names that missed — the backlog log counts them
        // when NO candidate rescues the site (a rescued name is not
        // backlog: `a.pop` resolved through the Array family must not
        // stay in the miss log).
        let mut tried: Vec<String> = Vec::new();
        let mut found = None;
        for n in &names {
            let hit = if peek {
                self.registry.peek(n, argc)
            } else {
                self.registry.lookup(n, argc)
            };
            if let Some(s) = hit {
                found = Some((n.clone(), s.exclusive));
                break;
            }
            tried.push(n.clone());
        }
        let class = match found {
            Some((name, exclusive)) => SiteClass::Summary { name, exclusive },
            None => {
                let has_body = callees.iter().any(|f| {
                    self.module
                        .func(*f)
                        .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
                });
                if has_body {
                    SiteClass::BodyStep
                } else if let Some(name) =
                    self.prototype_summary(inst, call, argc, &mut tried, peek)
                {
                    // Prototype-path applications are additive-only
                    // (exclusive: false) — see the precedence table.
                    SiteClass::Summary {
                        name,
                        exclusive: false,
                    }
                } else if names.is_empty() {
                    SiteClass::UnknownKeep
                } else {
                    SiteClass::NativeKeep
                }
            }
        };
        (class, tried)
    }

    /// The t-P3 prototype-resolution path: `recv.m(...)` → the
    /// receiver's prototype families ([`crate::prototype`]) →
    /// `Family.prototype.m` candidates, in family order. Returns the
    /// first registered summary key; every miss appends its
    /// synthesized key to `tried` (counted into the backlog log by the
    /// caller when nothing rescues the site). An empty/unknown
    /// receiver typing produces NO candidate at all — the site falls
    /// through to the fallback ladder unchanged (never invent).
    fn prototype_summary(
        &self,
        call_inst: &abcd_ir::Inst,
        call: InstId,
        argc: usize,
        tried: &mut Vec<String>,
        peek: bool,
    ) -> Option<String> {
        let leaf = call_method_leaf(self.module, call_inst)?;
        let leaf = self.module.sym.resolve(leaf)?.to_owned();
        let base = call_base_value(self.module, call_inst)?;
        let oracle = self.oracle.borrow();
        let resolver = PrototypeResolver::new(self.module, &oracle, &self.proto_memo);
        let answer = resolver.families_of(base, call);
        drop(oracle);
        let mut hit = None;
        for family in &answer.families {
            let key = format!("{}.{leaf}", family.key());
            let found = if peek {
                self.registry.peek(&key, argc).is_some()
            } else {
                self.registry.lookup(&key, argc).is_some()
            };
            if found {
                hit = Some(key);
                break;
            }
            tried.push(key);
        }
        hit
    }

    /// All `ValueId` operands of a call that taint can ride on:
    /// callee, `this`, args.
    fn call_operands(call_op: &Op) -> Vec<ValueId> {
        call_op.operands()
    }

    /// Whether `return_site` is the entry instruction of a catch handler
    /// of the calling function (then the callee's RETURN value does not
    /// flow there — only thrown values do). Returns the handler's
    /// exception binding when it is one.
    fn handler_exception_at(&self, return_site: InstId) -> Option<ValueId> {
        let rs_inst = self.module.inst(return_site)?;
        for f in &self.module.functions {
            for region in &f.try_regions {
                for catch in &region.catches {
                    if catch.handler == rs_inst.block {
                        return Some(catch.exception);
                    }
                }
            }
        }
        None
    }

    /// The catch binding of the handler whose entry block is
    /// `succ_block`, restricted to try regions of the function owning
    /// `from_block` (intraprocedural throw dispatch).
    fn handler_exception_for(
        &self,
        from_block: abcd_ir::BlockId,
        succ_block: abcd_ir::BlockId,
    ) -> Option<ValueId> {
        let func = self
            .module
            .functions
            .iter()
            .find(|f| f.blocks.contains(&from_block))?;
        for region in &func.try_regions {
            for catch in &region.catches {
                if catch.handler == succ_block {
                    return Some(catch.exception);
                }
            }
        }
        None
    }

    /// Whether a load through `object` may pick up a heap fact keyed by
    /// `sites` (positive intersection, or either side unknown — the
    /// conservative may-alias answer for unknown bases; the refined
    /// rungs sharpen `object`'s sites through their engines).
    ///
    /// Rung 2 addition (t-P6, the e13 mechanism): when `object`'s sites
    /// are unknown BUT it is the result of a summary call whose result
    /// no static flow reaches (a FRESH container — [`TaintProblem`]'s
    /// `fresh_result_site`), the load base keys by the call site: a
    /// VM-allocated `map` result no longer may-aliases the source
    /// array's heap fact through the wildcard.
    fn heap_may_reach(&self, sites: &AllocSiteSet, object: ValueId, at: InstId) -> bool {
        if sites.is_empty() {
            return true;
        }
        let obj = self.oracle.borrow().site_info_at(object, at);
        if !obj.sites.is_empty() {
            return sites.intersects(&obj.sites);
        }
        match self.fresh_result_site(object) {
            Some(site) => sites.iter().any(|s| s == site),
            None => true, // the unknown-base wildcard
        }
    }

    /// The e13 mechanism (t-P4's registered rung-2 idea, "summary
    /// results as call-site-keyed allocations" — landed here,
    /// taint-side): the call instruction of a summary-application whose
    /// result NO static flow reaches (`Param/Base/Field → Return*`
    /// would mean the result derives from — may alias — an input, and
    /// gap return channels key their facts precisely on the local
    /// result, so they do not count as aliasing either). Rung-2-gated:
    /// the wildcard discipline of rungs 0/1 is unchanged. Memoized;
    /// classification is peeked (counter-free).
    fn fresh_result_site(&self, value: ValueId) -> Option<InstId> {
        if self.config.alias_rung < 2 {
            return None;
        }
        if let Some(hit) = self.fresh_memo.borrow().get(&value) {
            return *hit;
        }
        let site = self.fresh_result_site_uncached(value);
        self.fresh_memo.borrow_mut().insert(value, site);
        site
    }

    /// The uncached worker of [`TaintProblem::fresh_result_site`].
    fn fresh_result_site_uncached(&self, value: ValueId) -> Option<InstId> {
        let abcd_ir::ValueDef::Inst(iid) = self.module.value(value)?.def else {
            return None;
        };
        let inst = self.module.inst(iid)?;
        if inst.result != Some(value) {
            return None;
        }
        let Op::Call { args, .. } = &inst.op else {
            return None;
        };
        let SiteClass::Summary { name, .. } = self.compute_class(iid, true).0 else {
            return None;
        };
        let summary = self.registry.peek(&name, args.len())?;
        let result_inflow = summary
            .flows
            .iter()
            .any(|f| matches!(f.to, Endpoint::Return | Endpoint::ReturnField(_)));
        if result_inflow { None } else { Some(iid) }
    }

    /// Whether local fact base `v` has positive-alias evidence with
    /// `object` (same value, or non-empty intersecting site sets).
    /// Unknown-on-either-side is deliberately NOT evidence for locals:
    /// params/globals would alias every load (documented rung-0 choice,
    /// kept under rung 1 — the engine only sharpens the site sets).
    fn local_alias_evidence(&self, v: ValueId, object: ValueId, at: InstId) -> bool {
        if v == object {
            return true;
        }
        let oracle = self.oracle.borrow();
        let a = oracle.site_info_at(v, at);
        let b = oracle.site_info_at(object, at);
        !a.sites.is_empty() && a.sites.intersects(&b.sites)
    }

    /// The access-path cut (`cutFirstField`, soot-infoflow §2.2): what
    /// remains of `fields` after reading `key`. An empty chain means the
    /// base itself was tainted — any property read is tainted one step.
    fn cut_first(&self, fields: &FieldChain, key: FieldKey) -> Option<FieldChain> {
        if fields.is_empty() {
            return Some(FieldChain::new().pushed(key, self.cap()));
        }
        let first = fields.elements()[0];
        let compatible = match (first, key) {
            (FieldKey::Named(a), FieldKey::Named(b)) => a == b,
            // AnyIndex/AnyDynamic are wildcards (heap.rs discipline).
            _ => true,
        };
        if compatible {
            let mut rest = FieldChain::new();
            for &k in &fields.elements()[1..] {
                rest = rest.pushed(k, self.cap());
            }
            Some(rest)
        } else {
            None
        }
    }

    /// Access-path load rule: `result = object.key` at instruction `at`.
    fn load_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        at: InstId,
        out: &mut Vec<Fact>,
    ) {
        let Some(result) = self.module.inst(at).and_then(|i| i.result) else {
            return;
        };
        let try_cut = |fields: &FieldChain| self.cut_first(fields, key);
        match &fact.base {
            TaintBase::Local(v) if self.local_alias_evidence(*v, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.push(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            TaintBase::Heap(sites) if self.heap_may_reach(sites, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.push(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            _ => {}
        }
    }

    /// Access-path store rule: `object.key = value` at instruction `at`.
    /// Returns whether the incoming fact survives (strong kills return
    /// false for the killed fact).
    ///
    /// Rung 1 changes BOTH decisions through the engine's memoized query
    /// ([`Oracle::site_info_at`] / [`Oracle::aliases_of_store`]): the
    /// strong-kill proof may come from an interprocedural def chain (the
    /// a5 case — a sanitizing store through a call-result alias), and the
    /// stored taint's heap key may be refined from an unknown base to
    /// precise sites (the a4 case). Any imprecise answer falls back to
    /// the rung-0 local walk — never silently wrong.
    fn store_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        value: ValueId,
        at: InstId,
        out: &mut Vec<Fact>,
    ) -> bool {
        let mut survive = true;
        // Strong kill: the old value at exactly this location is dead.
        let obj_info = self.oracle.borrow().site_info_at(object, at);
        if update_kind(&obj_info) == UpdateKind::Strong {
            let site = obj_info.sites;
            let at_location = match &fact.base {
                TaintBase::Heap(sites) => *sites == site,
                TaintBase::Local(v) => *v == object,
                _ => false,
            };
            if at_location && !fact.fields.is_empty() {
                let first = fact.fields.elements()[0];
                let same_key = match (first, key) {
                    (FieldKey::Named(a), FieldKey::Named(b)) => a == b,
                    _ => true,
                };
                if same_key {
                    survive = false;
                }
            }
        }
        // The stored value's taint is re-keyed into the heap: the
        // computeAliases analogue (soot-infoflow §4.2) — rung 1 injects
        // the REFINED key and the baseline is skipped; otherwise the
        // rung-0 keying stands (empty-site unknown-base wildcard
        // included — sound by construction).
        if fact.base == TaintBase::Local(value) {
            let injected = {
                let oracle = self.oracle.borrow();
                oracle.aliases_of_store(fact, object, key, at, self.cap())
            };
            if !injected.is_empty() {
                out.extend(injected.into_iter().map(Fact::of));
            } else {
                let sites = self.oracle.borrow().resolve(object).sites;
                let mut chain = FieldChain::new().pushed(key, self.cap());
                for &k in fact.fields.elements() {
                    chain = chain.pushed(k, self.cap());
                }
                out.push(Fact::of(TaintFact {
                    base: TaintBase::Heap(sites),
                    fields: chain,
                }));
            }
        }
        survive
    }

    /// The generic operand→result rule (Mov/binop/unop/compare/
    /// coercion/iterator families — everything with a result that is not
    /// in an explicitly handled family).
    fn generic_propagate(&self, inst: &abcd_ir::Inst, fact: &TaintFact, out: &mut Vec<Fact>) {
        let Some(result) = inst.result else { return };
        let Some(v) = fact.local_base() else { return };
        if inst.op.operands().contains(&v) {
            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
        }
    }

    /// Match an incoming fact against a summary endpoint at a call site.
    /// Returns the leftover field chain below the endpoint path.
    fn match_endpoint(
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
    ) -> Option<FieldChain> {
        let local = fact.local_base()?;
        let (value, path) = match endpoint {
            Endpoint::Param(i) => (*args.get(*i as usize)?, None),
            Endpoint::Base => (base?, None),
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
            Endpoint::Field(path) => (base?, Some(path)),
        };
        if local != value {
            return None;
        }
        match path {
            None => Some(fact.fields.clone()),
            Some(path) => {
                let elems = fact.fields.elements();
                let p = path.elements();
                if elems.len() < p.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(p.iter()) {
                    if let (FieldKey::Named(x), FieldKey::Named(y)) = (a, b) {
                        if x != y {
                            return None;
                        }
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[p.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                Some(rest)
            }
        }
    }

    /// Match a summary FLOW's source endpoint against an incoming fact
    /// at call site `at`: the static local match first; otherwise the
    /// rung-1 heap-fact match — a fact `Heap(sites).chain` where `sites`
    /// positively intersects the points-to set of the endpoint's value
    /// (the e5 case: a field-tainted literal passed to `Object.assign`).
    /// Positive intersection is required on both sides (an unknown side
    /// is not evidence — the same discipline as
    /// [`TaintProblem::local_alias_evidence`]), so this adds flows over
    /// rung 0 without re-keying any existing match. `Field(path)`
    /// endpoints additionally require the fact's chain to start with
    /// `path` (the leftover below the path flows on — the t-P3 case:
    /// an `[AnyIndex]`-tagged array element read by
    /// `Array.prototype.pop` / `Iterator.prototype.next`). Returns the
    /// leftover chain and whether the match was heap-sourced (the
    /// substitute then re-keys to `Heap`, keeping the fact
    /// function-global instead of dying on a local). `may = true` (the
    /// gap enter) reads the endpoint value's sites through the
    /// MAY-direction query ([`Oracle::may_sites_at`] — the engine's
    /// resolution-complete caller fan-out is accepted, the
    /// `refine_with_points_to` discipline); `may = false` keeps the
    /// keying-precise `site_info_at` answer.
    fn match_flow_endpoint(
        &self,
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        at: InstId,
        may: bool,
    ) -> Option<(FieldChain, bool)> {
        if let Some(leftover) = Self::match_endpoint(endpoint, fact, args, base) {
            return Some((leftover, false));
        }
        let TaintBase::Heap(sites) = &fact.base else {
            return None;
        };
        if sites.is_empty() {
            return None;
        }
        let (value, path) = match endpoint {
            Endpoint::Param(i) => (*args.get(*i as usize)?, None),
            Endpoint::Base => (base?, None),
            Endpoint::Field(path) => (base?, Some(path)),
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
        };
        let pts = if may {
            self.oracle.borrow().may_sites_at(value, at)
        } else {
            self.oracle.borrow().site_info_at(value, at).sites
        };
        if pts.is_empty() || !pts.intersects(sites) {
            return None;
        }
        let leftover = match path {
            None => fact.fields.clone(),
            Some(p) => {
                let elems = fact.fields.elements();
                let want = p.elements();
                if elems.len() < want.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(want.iter()) {
                    if let (FieldKey::Named(x), FieldKey::Named(y)) = (a, b) {
                        if x != y {
                            return None;
                        }
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[want.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                rest
            }
        };
        Some((leftover, true))
    }

    /// Substitute a sink endpoint at the call site.
    fn substitute(
        &self,
        endpoint: &Endpoint,
        leftover: &FieldChain,
        args: &[ValueId],
        base: Option<ValueId>,
        result: Option<ValueId>,
        is_handler_site: bool,
        from_heap: bool,
        at: InstId,
        out: &mut Vec<Fact>,
    ) {
        let append = |path: &FieldChain| {
            let mut chain = path.clone();
            for &k in leftover.elements() {
                chain = chain.pushed(k, self.cap());
            }
            chain
        };
        // The target key for a value endpoint: a heap-sourced match
        // re-keys onto the target's site set (function-global state);
        // unknown-site targets stay local (rung-0 behavior).
        let value_key = |v: ValueId| {
            if from_heap {
                let sites = self.oracle.borrow().site_info_at(v, at).sites;
                if !sites.is_empty() {
                    return TaintBase::Heap(sites);
                }
            }
            TaintBase::Local(v)
        };
        match endpoint {
            Endpoint::Param(i) => {
                if let Some(&v) = args.get(*i as usize) {
                    out.push(Fact::of(TaintFact {
                        base: value_key(v),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::Base => {
                if let Some(b) = base {
                    out.push(Fact::of(TaintFact {
                        base: value_key(b),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::Return => {
                // A return value exists only on the normal continuation.
                if !is_handler_site {
                    if let Some(r) = result {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(r),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
            Endpoint::ReturnField(path) => {
                // A result-field sink (filter's base-elements →
                // result-elements flow): the result value with the
                // declared path ++ leftover.
                if !is_handler_site {
                    if let Some(r) = result {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(r),
                            fields: append(path),
                        }));
                    }
                }
            }
            Endpoint::Field(path) => {
                if let Some(b) = base {
                    let sites = self.oracle.borrow().site_info_at(b, at).sites;
                    let chain = append(path);
                    let base_key = if sites.is_empty() {
                        TaintBase::Local(b)
                    } else {
                        TaintBase::Heap(sites)
                    };
                    out.push(Fact::of(TaintFact {
                        base: base_key,
                        fields: chain,
                    }));
                }
            }
        }
    }

    /// The gap enter mapping (t-P4; [`crate::gap`] §3): at a gap edge
    /// `(call → cb_func)`, each of the gap's `enter` rules whose source
    /// endpoint matches the incoming fact seeds the callback's formal
    /// (the N66 frame-slot binding — formal 0 of an es2abc closure is
    /// `params[formal_base]`, not `params[1]`). A heap-sourced match
    /// seeds a LOCAL formal fact: the element VALUE rides the formal —
    /// the heap key was about the receiver's storage, not the
    /// extracted element. `OverApproxAll` binding taints every formal
    /// (never silently drop a flow).
    fn gap_enter(
        &self,
        call: InstId,
        cb_func: FuncId,
        gap: &CallbackGap,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        out: &mut Vec<Fact>,
    ) {
        let Some(fd) = self.module.func(cb_func) else {
            return;
        };
        let binding = param_binding(self.module, cb_func);
        for enter in &gap.enter {
            let Some((leftover, _from_heap)) =
                self.match_flow_endpoint(&enter.from, fact, args, base, call, true)
            else {
                continue;
            };
            match binding {
                ParamBinding::OverApproxAll => {
                    for &p in &fd.params {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
                ParamBinding::Precise { formal_base, .. } => {
                    if let Some(&p) = fd.params.get(formal_base + enter.formal as usize) {
                        out.push(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
        }
    }
}

impl IfdsProblem for TaintProblem<'_> {
    type Fact = Fact;

    fn zero(&self) -> Fact {
        Fact::Zero
    }

    fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
        let mut seeds = Vec::new();
        if self.config.seed_all_functions {
            for (fi, f) in self.module.functions.iter().enumerate() {
                if !f.blocks.is_empty() {
                    seeds.push((FuncId::new(fi as u32), Fact::Zero));
                }
            }
        }
        for (func, params) in &self.param_seeds {
            for &p in params {
                seeds.push((*func, Fact::of(TaintFact::local(p))));
            }
        }
        seeds
    }

    fn normal_flow(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Some(curr_inst) = module.inst(curr) else {
            return;
        };
        let Some(succ_inst) = module.inst(succ) else {
            return;
        };

        // ── Source generation fires on EVERY incoming edge, including
        // the zero fact's (FlowDroid's SourcePropagationRule: a source
        // statement produces taint from Λ).
        if let Op::TryGetGlobal { name, .. } = &curr_inst.op {
            if self.global_sources.contains(name) {
                if let Some(result) = curr_inst.result {
                    out.push(Fact::of(TaintFact::local(result)));
                }
            }
        }

        let Fact::Taint(fact) = source else { return };

        // ── Phi-entry edges: an incoming value listed for THIS edge
        // additionally maps to the phi result (phi merges union sites via
        // the heap oracle; the SSA value mapping is exact per edge).
        // Non-matching locals PASS THROUGH — a phi edge is a block
        // boundary, not a kill: the value's taint is path-insensitively
        // true wherever the value is in scope.
        if let Op::Phi { entries } = &succ_inst.op {
            if let Some(v) = fact.local_base() {
                for (edge, val) in entries {
                    if *val == v && edge.from == curr_inst.block {
                        if let Some(result) = succ_inst.result {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    }
                }
            }
            out.push(source.clone());
            return;
        }

        // ── Exception dispatch: `throw v` taints the catch binding (T5).
        if let Op::Throw { value } = &curr_inst.op {
            out.push(source.clone());
            if fact.base == TaintBase::Local(*value) {
                if let Some(exc) = self.handler_exception_for(curr_inst.block, succ_inst.block) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            return;
        }

        match &curr_inst.op {
            // ── Global bindings ──────────────────────────────────────
            Op::TryGetGlobal { name, .. } => {
                // Pick up a previously stored global taint.
                if fact.base == TaintBase::Global(*name) {
                    if let Some(result) = curr_inst.result {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                self.generic_propagate(curr_inst, fact, out); // the `default` operand
                out.push(source.clone());
            }
            Op::StoreGlobal { name, value } | Op::TryStoreGlobal { name, value } => {
                if fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::Global(*name))));
                }
                out.push(source.clone());
            }
            // ── Module variables ─────────────────────────────────────
            Op::LoadModuleVar { index } => {
                if fact.base == TaintBase::ModuleVar(*index) {
                    if let Some(result) = curr_inst.result {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                out.push(source.clone());
            }
            Op::StoreModuleVar { index, value } => {
                if fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::ModuleVar(*index))));
                }
                out.push(source.clone());
            }
            // ── Lexical environment slots ────────────────────────────
            Op::GetLexVar { level, slot } => {
                if fact.base == TaintBase::LexVar(*level, *slot) {
                    if let Some(result) = curr_inst.result {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                // The rung-2 environment-identity channel (b2): a
                // PRECISE writer keys the slot by its NewLexEnv site's
                // abstract object (`Heap(env).[AnyIndex]`), so two
                // functions' colliding (level, slot) captures no longer
                // merge. A precise reader matches by env-site
                // intersection; an imprecise reader (env unknown) falls
                // back to matching ANY env-keyed fact — the
                // may-direction rule that keeps the channel sound when
                // the env analysis gives up (the rung-1 unbalanced
                // discipline's analogue).
                if let Some(env) = self.oracle.borrow().lex_env_at(curr, *level) {
                    if let TaintBase::Heap(sites) = &fact.base {
                        let precise = !env.has_unknown && !env.sites.is_empty();
                        let hits = if precise {
                            env.sites.intersects(sites)
                        } else {
                            let oracle = self.oracle.borrow();
                            sites.iter().any(|s| oracle.is_env_site(s))
                        };
                        if hits {
                            if let Some(rest) =
                                self.cut_first(&fact.fields, FieldKey::AnyIndex)
                            {
                                if let Some(result) = curr_inst.result {
                                    out.push(Fact::of(
                                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                                    ));
                                }
                            }
                        }
                    }
                }
                out.push(source.clone());
            }
            Op::PutLexVar { level, slot, value } => {
                if fact.base == TaintBase::Local(*value) {
                    // Rung 2 keys the slot by the environment's
                    // abstract object when the env analysis is precise
                    // (b2 — see the GetLexVar arm); the legacy
                    // function-agnostic `(level, slot)` keying stands
                    // otherwise and on rungs 0/1. Slots within one
                    // environment merge under `AnyIndex` (the b2
                    // collision is ACROSS environments — documented).
                    let keyed_env = self
                        .oracle
                        .borrow()
                        .lex_env_at(curr, *level)
                        .and_then(|env| {
                            (!env.has_unknown && !env.sites.is_empty()).then_some(env.sites)
                        });
                    match keyed_env {
                        Some(sites) => {
                            let mut chain = FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                            for &k in fact.fields.elements() {
                                chain = chain.pushed(k, self.cap());
                            }
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: chain,
                            }));
                        }
                        None => {
                            out.push(Fact::of(fact.rebased(TaintBase::LexVar(*level, *slot))))
                        }
                    }
                }
                out.push(source.clone());
            }
            // ── Iterator protocol objects (t-P3) ───────────────────
            Op::GetIterator { obj } => {
                // `it = getiterator(obj)`: the iterator yields obj's
                // elements, so obj's taint state transfers to it.
                // LOCAL facts ride the generic rule below with their
                // chain intact (empty = whole-source taint;
                // `[AnyIndex]` = the "elements of" tag the
                // `Iterator.prototype.next` summary consumes). HEAP
                // facts re-key onto the result by positive site
                // intersection (heap reads are otherwise opaque —
                // this is the one builtin op whose element channel is
                // static): `Heap(site(a)).[AnyIndex]` ⇒
                // `Local(it).[AnyIndex]`.
                if let Some(result) = curr_inst.result {
                    if let TaintBase::Heap(sites) = &fact.base {
                        if self.heap_may_reach(sites, *obj, curr) {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    }
                }
                self.generic_propagate(curr_inst, fact, out);
                out.push(source.clone());
            }
            // ── Loads (access-path cut) ──────────────────────────────
            Op::LoadProp { object, name } => {
                self.load_rule(fact, *object, FieldKey::Named(*name), curr, out);
                out.push(source.clone());
            }
            Op::LoadPropIdx { object, .. } => {
                self.load_rule(fact, *object, FieldKey::AnyIndex, curr, out);
                out.push(source.clone());
            }
            Op::LoadPropDyn { object, .. } => {
                self.load_rule(fact, *object, FieldKey::AnyDynamic, curr, out);
                out.push(source.clone());
            }
            // ── Stores (heap re-keying + strong/weak kills) ──────────
            Op::StoreProp {
                object,
                name,
                value,
            }
            | Op::StoreOwnPropName {
                object,
                name,
                value,
            } => {
                if self.store_rule(fact, *object, FieldKey::Named(*name), *value, curr, out) {
                    out.push(source.clone());
                }
            }
            Op::StorePropIdx { object, value, .. } | Op::StoreOwnPropIdx { object, value, .. } => {
                if self.store_rule(fact, *object, FieldKey::AnyIndex, *value, curr, out) {
                    out.push(source.clone());
                }
            }
            Op::StorePropDyn { object, value, .. } | Op::StoreOwnPropDyn { object, value, .. } => {
                if self.store_rule(fact, *object, FieldKey::AnyDynamic, *value, curr, out) {
                    out.push(source.clone());
                }
            }
            // ── Object-family ops with bespoke taint semantics ───────
            Op::CopyDataProps { dst, src } => {
                // Object spread: src's taint (object + fields) copies to dst.
                if fact.base == TaintBase::Local(*src) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(*dst))));
                }
                out.push(source.clone());
            }
            Op::SetObjectWithProto { proto, obj } => {
                // obj's prototype chain now reads through proto.
                if fact.base == TaintBase::Local(*proto) {
                    out.push(Fact::of(
                        TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                out.push(source.clone());
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                // No FieldKey for private names at rung 0: record "some
                // property of obj is tainted".
                if fact.base == TaintBase::Local(*value) {
                    let sites = self.oracle.borrow().resolve(*obj).sites;
                    if sites.is_empty() {
                        out.push(Fact::of(
                            TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    } else {
                        out.push(Fact::of(
                            TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: FieldChain::new(),
                            }
                            .pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    }
                }
                out.push(source.clone());
            }
            Op::DefineMethod { object, func, .. } => {
                if fact.base == TaintBase::Local(*func) {
                    let sites = self.oracle.borrow().resolve(*object).sites;
                    out.push(Fact::of(
                        TaintFact {
                            base: TaintBase::Heap(sites),
                            fields: FieldChain::new(),
                        }
                        .pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                out.push(source.clone());
            }
            Op::DefineFunc { .. } => {
                // Captured taint marks the closure value with an EMPTY
                // chain ("this function closes over tainted data").
                // Rung 0 does NOT propagate capture taint into the body
                // (known FN, ladder pointer in the README).
                let is_capture = curr_inst
                    .op
                    .operands()
                    .iter()
                    .any(|&v| fact.base == TaintBase::Local(v));
                if is_capture {
                    if let Some(result) = curr_inst.result {
                        out.push(Fact::of(TaintFact::local(result)));
                    }
                }
                out.push(source.clone());
            }
            // ── Everything else: the generic operand→result rule ─────
            _ => {
                self.generic_propagate(curr_inst, fact, out);
                out.push(source.clone());
            }
        }
    }

    fn call_flow(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let gap = self.gap_at(call, callee);
        // Exclusive summaries kill the call edge into the callee body —
        // never merged (summaries.md §2.1). The GAP edge into the user
        // callback is NOT killed (gap.rs §"Interaction with exclusive":
        // exclusive-with-callback still runs the callback).
        if gap.is_none()
            && matches!(
                self.classify(call),
                SiteClass::Summary {
                    exclusive: true,
                    ..
                }
            )
        {
            return;
        }
        let Fact::Taint(fact) = source else { return };
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        } = &call_inst.op
        else {
            return;
        };
        let Some(fd) = module.func(callee) else {
            return;
        };

        // ── The gap edge (t-P4) ──────────────────────────────────────
        // The summary call site virtually invokes the callback with
        // (element, index, array) — the summary call's operands are NOT
        // the callback's arguments, so the normal arg→param binding does
        // not run here; only the gap's `enter` rules bind. Function-
        // global state crosses unchanged (same as a normal edge). The
        // oracle's calling-context injection is deliberately skipped:
        // the rung-1 engine reads the BASE call graph, which has no gap
        // edges — a query inside the callback that tries to hop through
        // the gap call finds no recorded caller and falls back to the
        // rung-0 floor (sound; documented in gap.rs).
        if let Some(gap) = &gap {
            if fact.is_state_base() {
                out.push(source.clone());
            }
            let base = call_base_value(module, call_inst);
            self.gap_enter(call, callee, gap, fact, args, base, out);
            return;
        }

        // The oracle learns the calling context (rung 0: no-op; the seam
        // discipline of analysis-strategy §5.2 / infoflow.md §4.3).
        abcd_analysis::dataflow::heap::AliasOracle::inject_calling_context(
            &mut *self.oracle.borrow_mut(),
            call,
            callee,
            fact,
        );

        match &fact.base {
            TaintBase::Local(v) => {
                // N66: bind through the vendored frame-slot model
                // ([func][newTarget][this][formals…], per the callee's
                // callType annotation or the 0xF static default) —
                // args[i] → params[formal_base + i], NOT params[i + 1]
                // (the pre-N66 table was written for a normalized ABI
                // the lift never produced).
                let binding = param_binding(module, callee);
                if binding == ParamBinding::OverApproxAll {
                    // Conservative: a tainted this/arg taints EVERY
                    // param (never silently drop a flow).
                    let on_operands = this.is_some_and(|t| t == *v) || args.contains(v);
                    if on_operands {
                        for &p in &fd.params {
                            out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                        }
                    }
                } else {
                    // `this` → the this slot (T4 binding convention).
                    if let ParamBinding::Precise {
                        this_slot: Some(slot),
                        ..
                    } = binding
                    {
                        if this.is_some_and(|t| t == *v) {
                            if let Some(&p) = fd.params.get(slot) {
                                out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                            }
                        }
                    }
                    let formal_base = match binding {
                        ParamBinding::Precise { formal_base, .. } => formal_base,
                        ParamBinding::OverApproxAll => unreachable!(),
                    };
                    match kind {
                        CallKind::Direct | CallKind::Dynamic | CallKind::New | CallKind::Super => {
                            for (i, &a) in args.iter().enumerate() {
                                if a == *v {
                                    if let Some(&p) = fd.params.get(formal_base + i) {
                                        out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                                    }
                                }
                            }
                        }
                        CallKind::Apply | CallKind::SuperSpread => {
                            // args[0] is an ARRAY spread over the formals: a
                            // tainted array taints every formal (the
                            // reflective-call mapper case of soot-infoflow).
                            if args.first() == Some(v) {
                                for &p in fd.params.iter().skip(formal_base) {
                                    out.push(Fact::of(fact.rebased(TaintBase::Local(p))));
                                }
                            }
                        }
                        CallKind::SuperForwardAllArgs => {
                            // The forwarded arguments are the caller's own
                            // formals — not operands of this call. Rung 0
                            // models nothing here (documented gap).
                        }
                    }
                }
                // The mini-gap channel: a callback value tagged
                // `[AnyIndex, ...]` by a summary (forEach-style) seeds
                // its first formal when user code calls it directly.
                // N66: the first FORMAL is `params[formal_base]` (the
                // implicit frame slots lead), not `params[1]`;
                // OverApproxAll taints every formal (never silently
                // drop).
                if *v == *callee_val && !fact.fields.is_empty() {
                    if fact.fields.elements()[0] == FieldKey::AnyIndex {
                        let mut rest = FieldChain::new();
                        for &k in &fact.fields.elements()[1..] {
                            rest = rest.pushed(k, self.cap());
                        }
                        match param_binding(module, callee) {
                            ParamBinding::Precise { formal_base, .. } => {
                                if let Some(&p1) = fd.params.get(formal_base) {
                                    out.push(Fact::of(
                                        fact.with_fields(rest).rebased(TaintBase::Local(p1)),
                                    ));
                                }
                            }
                            ParamBinding::OverApproxAll => {
                                for &p in &fd.params {
                                    out.push(Fact::of(
                                        fact.with_fields(rest.clone()).rebased(TaintBase::Local(p)),
                                    ));
                                }
                            }
                        }
                    }
                }
                // A tainted callee value with an EMPTY chain (function-
                // object taint, e.g. a closure over tainted captures) is
                // dropped at the boundary — function-object taint is not
                // data taint (documented rung-0 gap).
            }
            // Heap/global/module/lexical state flows into the callee.
            _ => out.push(source.clone()),
        }
    }

    fn return_flow(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        let Some(exit_inst) = module.inst(exit) else {
            return;
        };

        // State bases are function-global: they cross returns unchanged
        // (also for unbalanced returns with `None` endpoints — and
        // across gap edges: the callback's side effects on heap/global
        // state persist at the summary call's continuation).
        if fact.is_state_base() {
            out.push(source.clone());
            return;
        }
        let Some(v) = fact.local_base() else { return };
        // The gap return channel (t-P4; gap.rs §4): at a gap edge the
        // callback's RETURN value maps per the summary's
        // `return_to_result` instead of the normal value→result
        // rebasing (map: the result array's `[AnyIndex]` elements;
        // forEach: `None` — the callback return dies with the undefined
        // result).
        let gap = call_site.and_then(|c| self.gap_at(c, callee));

        match &exit_inst.op {
            Op::Return { value } => {
                if value != &Some(v) {
                    return; // callee-local taint that is not returned dies here
                }
                let (Some(call), Some(rs)) = (call_site, return_site) else {
                    return; // unbalanced: no result value to rebase onto
                };
                // The return VALUE flows only to the normal continuation,
                // never to handler entries.
                if self.handler_exception_at(rs).is_some() {
                    return;
                }
                if let Some(gap) = &gap {
                    if let Some(chain) = &gap.return_to_result {
                        if let Some(Some(result)) = module.inst(call).map(|i| i.result) {
                            let mut fields = FieldChain::new();
                            for &k in chain.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            for &k in fact.fields.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            out.push(Fact::of(TaintFact {
                                base: TaintBase::Local(result),
                                fields,
                            }));
                        }
                    }
                    return;
                }
                if let Some(Some(result)) = module.inst(call).map(|i| i.result) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
            }
            Op::Throw { value } => {
                if value != &v {
                    return;
                }
                let Some(rs) = return_site else { return };
                // Thrown taint lands on the catch binding of whichever
                // handler entry this return site is (T5/T10).
                if let Some(exc) = self.handler_exception_at(rs) {
                    out.push(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            _ => {}
        }
    }

    fn call_to_return_flow(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Op::Call { args, .. } = &call_inst.op else {
            return;
        };
        let operands = Self::call_operands(&call_inst.op);
        let on_operand = fact.local_base().is_some_and(|v| operands.contains(&v));
        let is_handler_site = self.handler_exception_at(return_site).is_some();

        match self.classify(call) {
            SiteClass::Summary { name, exclusive } => {
                let base = call_base_value(module, call_inst);
                let result = call_inst.result;
                let summary = self
                    .registry
                    .lookup(&name, args.len())
                    .expect("classified sites have a summary");
                // Clears first (summaries.md §2.2 step 3).
                let cleared = summary
                    .clears
                    .iter()
                    .any(|c| Self::match_endpoint(c, fact, args, base).is_some());
                if !cleared {
                    for flow in &summary.flows {
                        if let Some((leftover, from_heap)) =
                            self.match_flow_endpoint(&flow.from, fact, args, base, call, false)
                        {
                            self.substitute(
                                &flow.to,
                                &leftover,
                                args,
                                base,
                                result,
                                is_handler_site,
                                from_heap,
                                call,
                                out,
                            );
                        }
                    }
                    // Mini-gap: tag the callback value with `[AnyIndex]`
                    // (the may-call-user-code marker). The FULL gap
                    // propagator's enter/return channels live on the
                    // gap call/return edges (gap.rs); this tag remains
                    // the channel for DIRECT user calls of the callback
                    // value and the unresolved-callback fallback.
                    if let Some(cb_gap) = &summary.callback {
                        if Self::match_endpoint(&Endpoint::Base, fact, args, base).is_some() {
                            if let Some(&cbv) = args.get(cb_gap.param as usize) {
                                out.push(Fact::of(
                                    TaintFact::local(cbv).pushed(FieldKey::AnyIndex, self.cap()),
                                ));
                            }
                        }
                    }
                }
                // The incoming taint is RETAINED unless cleared
                // (summaries.md §2.2:813-820); exclusive summaries
                // additionally kill incoming operand taints the flows
                // did not re-add (WrapperPropagationRule's killSource).
                let retain = if cleared {
                    false
                } else if exclusive && on_operand {
                    false // the summary is the complete model of the operands' fate
                } else {
                    true
                };
                if retain {
                    out.push(source.clone());
                }
                // Log once per (site, fact-free) application.
                let mut applied = self.applied.borrow_mut();
                if !applied.iter().any(|(i, n)| *i == call && *n == name) {
                    applied.push((call, name));
                }
            }
            SiteClass::BodyStep => {
                // The callee body carries operand taints through the
                // call/return edges (FlowDroid's killIncomingTaint =
                // hasActiveBody); everything else bypasses.
                if !on_operand {
                    out.push(source.clone());
                }
            }
            SiteClass::NativeKeep | SiteClass::UnknownKeep => {
                // Conservative keep: taint passes through untouched —
                // never sanitizes. Plus the identity heuristic (reader D
                // ladder rung 3): tainted operand ⇒ tainted return.
                out.push(source.clone());
                if self.config.native_identity && on_operand && !is_handler_site {
                    if let Some(result) = call_inst.result {
                        out.push(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
            }
        }
    }
}
