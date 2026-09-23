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
use std::collections::{HashMap, HashSet};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::{AllocSiteSet, UpdateKind};
use abcd_analysis::dataflow::heap::{FieldChain, FieldKey, update_kind};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, IfdsProblem};
use abcd_ir::{CallKind, FuncId, InstId, Module, Op, Sym, ValueId};

use crate::driver::{SourceSpec, TaintConfig};
use crate::fact::{Fact, TaintBase, TaintFact};
use crate::names::{call_base_value, callee_name_candidates};
use crate::oracle::Oracle;
use crate::summary::{Endpoint, FallbackStep, SummaryRegistry};

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
        TaintProblem {
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
        }
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
    fn classify(&self, call: InstId) -> SiteClass {
        if let Some(c) = self.site_class.borrow().get(&call) {
            return c.clone();
        }
        let Some(inst) = self.module.inst(call) else {
            return SiteClass::UnknownKeep;
        };
        let Op::Call { callee, args, .. } = &inst.op else {
            return SiteClass::UnknownKeep;
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
        let class = {
            let mut found = None;
            for n in &names {
                if let Some(s) = self.registry.lookup(n, argc) {
                    found = Some((n.clone(), s.exclusive));
                    break;
                }
            }
            match found {
                Some((name, exclusive)) => SiteClass::Summary { name, exclusive },
                None => {
                    let has_body = callees.iter().any(|f| {
                        self.module
                            .func(*f)
                            .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
                    });
                    if has_body {
                        SiteClass::BodyStep
                    } else if names.is_empty() {
                        SiteClass::UnknownKeep
                    } else {
                        SiteClass::NativeKeep
                    }
                }
            }
        };
        // Counters fire once per site.
        if self.counted.borrow_mut().insert(call) {
            match &class {
                SiteClass::Summary { name, .. } => self.registry.record_hit(name),
                SiteClass::BodyStep => self.registry.record_fallback(FallbackStep::BodyStep),
                SiteClass::NativeKeep => self.registry.record_fallback(FallbackStep::NativeKeep),
                SiteClass::UnknownKeep => self.registry.record_fallback(FallbackStep::Unknown),
            }
        }
        self.site_class.borrow_mut().insert(call, class.clone());
        class
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
    /// conservative may-alias answer for unknown bases; rung 1 refines
    /// `object`'s sites through the on-demand query, rung 0 through the
    /// local def chain).
    fn heap_may_reach(&self, sites: &AllocSiteSet, object: ValueId, at: InstId) -> bool {
        let obj = self.oracle.borrow().site_info_at(object, at);
        sites.is_empty() || obj.sites.is_empty() || sites.intersects(&obj.sites)
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
        let try_cut = |fields: &FieldChain| -> Option<FieldChain> {
            if fields.is_empty() {
                // Base tainted: any property read is tainted (one step).
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
        };
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
            Endpoint::Return => return None,
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
    /// rung 0 without re-keying any existing match. Returns the leftover
    /// chain and whether the match was heap-sourced (the substitute then
    /// re-keys to `Heap`, keeping the fact function-global instead of
    /// dying on a local).
    fn match_flow_endpoint(
        &self,
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        at: InstId,
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
        let value = match endpoint {
            Endpoint::Param(i) => *args.get(*i as usize)?,
            Endpoint::Base => base?,
            _ => return None,
        };
        let pts = self.oracle.borrow().site_info_at(value, at).sites;
        if pts.is_empty() || !pts.intersects(sites) {
            return None;
        }
        Some((fact.fields.clone(), true))
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
                out.push(source.clone());
            }
            Op::PutLexVar { level, slot, value } => {
                if fact.base == TaintBase::Local(*value) {
                    out.push(Fact::of(fact.rebased(TaintBase::LexVar(*level, *slot))));
                }
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
        // Exclusive summaries kill the call edge into the callee body —
        // never merged (summaries.md §2.1).
        if matches!(
            self.classify(call),
            SiteClass::Summary {
                exclusive: true,
                ..
            }
        ) {
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
                if *v == *callee_val && !fact.fields.is_empty() {
                    if fact.fields.elements()[0] == FieldKey::AnyIndex {
                        let mut rest = FieldChain::new();
                        for &k in &fact.fields.elements()[1..] {
                            rest = rest.pushed(k, self.cap());
                        }
                        if let Some(&p1) = fd.params.get(1) {
                            out.push(Fact::of(
                                fact.with_fields(rest).rebased(TaintBase::Local(p1)),
                            ));
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
        _callee: FuncId,
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
        // (also for unbalanced returns with `None` endpoints).
        if fact.is_state_base() {
            out.push(source.clone());
            return;
        }
        let Some(v) = fact.local_base() else { return };

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
                            self.match_flow_endpoint(&flow.from, fact, args, base, call)
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
                    // (the may-call-user-code marker).
                    if let Some(cb) = summary.callback {
                        if Self::match_endpoint(&Endpoint::Base, fact, args, base).is_some() {
                            if let Some(&cbv) = args.get(cb as usize) {
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
