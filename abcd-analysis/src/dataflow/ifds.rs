//! The IFDS tabulation solver (`design/analysis.md`, `design/decisions.md`
//! N20): Reps–Horwitz–Sagiv interprocedural finite distributive subset
//! tabulation (POPL'95) with Naeem–Lhoták–Rodriguez practical extensions
//! (CC'10), specialized to the binary reachability lattice.
//!
//! ## Core tabulation design
//!
//! - **Start-anchored path-edge triples** `(source fact, target node, target fact)`:
//!   the source statement is omitted because it is always the entry
//!   instruction of the anchor function. Every tuple element is a compact
//!   integer/newtype, so standard tuple hashing and equality run directly
//!   without cached hash fields.
//! - **The `incoming`/`end_summary` pair** keyed by `(start point, fact)`
//!   with second-arriver replay: whichever of call-site entry or callee exit
//!   arrives second replays the other's table. Context sensitivity
//!   (same-level-realizable interprocedural paths) falls out of summary
//!   tabulation directly without maintaining per-edge call stacks.
//! - **TOP-as-absent / sparse-by-default**: the jump-function table IS
//!   the path-edge set; an edge that was never propagated is absent.
//!   Over the binary lattice the edge function is degenerate, so edge
//!   existence carries the entire lattice value.
//! - **The worklist + dedup chokepoint** (`IfdsSolver::propagate`):
//!   an edge is (re-)processed iff it is new — idempotency, scheduling,
//!   and summary storage come from one mechanism.
//! - **Dispatch rule**: a call node gets `process_call` only
//!   (call-to-return edges carry caller-local bypass flow); an exit node
//!   gets `process_exit` AND, when it has intraprocedural successors, normal
//!   flow too — an `Op::Throw` in a protected block is both a function exit
//!   and an intraprocedural exceptional-dispatch source.
//!
//! ## SSA IR supergraph representation (`design/ir.md`)
//!
//! - Nodes are [`InstId`]s; function identity is recovered via a
//!   block→function index. Facts are client-defined and should be
//!   newtypes over interned ids (`ValueId`-keyed) so path-edge hashing and
//!   equality reduce to integer comparisons.
//! - Exceptional flow is first-class: every may-throw instruction in
//!   a protected block has an exceptional successor (the handler entry), and
//!   a call's return sites form a COLLECTION (normal continuation +
//!   handler entries) so callee-thrown values flow to caller catch handlers
//!   via return-flow edges. Function exits are `Return` terminators and
//!   `Op::Throw` instructions; conditional runtime throws in unprotected
//!   blocks construct engine errors carrying no user SSA values, so they are
//!   not modeled as value-carrying exits (handlers still observe them via
//!   `ExceptionParam` when protected).
//! - Determinism (N20): FIFO worklist + insertion-ordered compact sets
//!   (`CompactU32Set`, `CompactPairSet`) everywhere the solver iterates;
//!   `HashMap`s are lookup-only and never iterated.
//!
//! ## The client contract ([`IfdsProblem`])
//!
//! Downstream clients (`abcd-taint`) plug in their fact type + the flow
//! functions + seeds without touching solver internals. The solver owns the
//! worklist, start-point anchoring, unconditional zero-fact (`Λ`)
//! preservation (whenever the source is `zero()`, `zero()` is automatically
//! retained among the targets), summary wiring, and deterministic ordering.
//! Flow functions receive the [`Module`] and push results into a
//! caller-provided `Vec`; they must be deterministic and tolerate `None`
//! call/return-site arguments under unbalanced returns.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{BuildHasher, Hash, RandomState};
use std::sync::OnceLock;

use abcd_ir::cfg::ExceptionHandlerMap;
use abcd_ir::{BlockId, FuncId, InstId, Module, Op};
use hashbrown::HashTable;

/// The call-graph seam the solver consumes (`design/analysis.md`:
/// consuming call edges strictly through query methods keeps batch vs
/// on-the-fly call graphs swappable). Implemented by
/// [`crate::callgraph::CallGraph`].
pub trait CallGraphOracle {
    /// The resolved callees of a call instruction; empty when the site is
    /// unresolved ([`crate::callgraph::CallTargets::UnknownCallees`]).
    fn callees_of_call_at(&self, call: InstId) -> &[FuncId];

    /// The call sites that may call `func` (for unbalanced returns).
    fn callers_of(&self, func: FuncId) -> &[InstId];
}

const FLAG_IS_CALL: u8 = 1 << 0;
const FLAG_CALL_MAY_THROW_UNCAUGHT: u8 = 1 << 1;
const FLAG_IS_EXIT: u8 = 1 << 2;

/// Compact per-function supergraph slice materialized lazily on first visit (`#78`).
#[derive(Default)]
struct FuncSupergraph {
    /// Entry instruction of `func.entry()`, if present.
    start_point: Option<InstId>,
    /// Minimum instruction ID when `inst_ids` is empty (dense arithmetic indexing).
    base_iid: u32,
    /// Empty in dense mode (`off = iid.raw() - base_iid`); sorted raw `InstId`s
    /// when a function's instruction IDs span a wide range.
    inst_ids: Box<[u32]>,
    /// Bitflags (`FLAG_*`) per local instruction slot.
    flags: Box<[u8]>,
    /// CSR offsets (`len == flags.len() + 1` when `!flags.is_empty()`, else empty)
    /// into `succ_targets`.
    succ_offsets: Box<[u32]>,
    /// Flattened intraprocedural (normal + exceptional) successor `InstId`s.
    succ_targets: Box<[InstId]>,
}

impl FuncSupergraph {
    fn build(module: &Module, func_id: FuncId) -> Self {
        let Some(f) = module.func(func_id) else {
            return Self::default();
        };
        let first_inst = |b: BlockId| -> Option<InstId> {
            module.block(b).and_then(|bb| bb.insts.first().copied())
        };
        let start_point = f.entry().and_then(first_inst);

        let exc_map = (!f.try_regions.is_empty())
            .then(|| ExceptionHandlerMap::build(module, func_id))
            .flatten();
        let mut block_has_catch_all = vec![false; f.blocks.len()];
        if let Some(map) = &exc_map {
            for region in &f.try_regions {
                let region_catch_all = region
                    .catches
                    .iter()
                    .any(|c| c.type_class.is_none() && map.block_index(c.handler).is_some());
                if region_catch_all {
                    for &prot_block in &region.protected {
                        if let Some(bi) = map.block_index(prot_block) {
                            block_has_catch_all[bi] = true;
                        }
                    }
                }
            }
        }

        // Collect `(raw_iid, flags, succ_start, succ_end)` in block order.
        let mut raw_entries: Vec<(u32, u8, u32, u32)> = Vec::new();
        let mut all_succs: Vec<InstId> = Vec::new();
        let mut succs_buf: Vec<InstId> = Vec::new();
        let mut min_iid = u32::MAX;
        let mut max_iid = 0u32;

        for (bi, &b) in f.blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else {
                continue;
            };
            let has_catch_all = block_has_catch_all.get(bi).copied().unwrap_or(false);
            let exc_handlers = exc_map
                .as_ref()
                .map_or(&[][..], |map| map.handlers_of_index(bi));
            for (pos, &iid) in bb.insts.iter().enumerate() {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                succs_buf.clear();
                if pos + 1 < bb.insts.len() {
                    succs_buf.push(bb.insts[pos + 1]);
                } else {
                    for s in crate::control::block_succs(module, b) {
                        if let Some(first) = first_inst(s) {
                            succs_buf.push(first);
                        }
                    }
                }
                if !exc_handlers.is_empty() && inst.op.effects_in(module).may_throw {
                    for &h in exc_handlers {
                        if let Some(first) = first_inst(h)
                            && !succs_buf.contains(&first)
                        {
                            succs_buf.push(first);
                        }
                    }
                }

                let mut fl = 0u8;
                match &inst.op {
                    Op::Call { .. } => {
                        fl |= FLAG_IS_CALL;
                        if !has_catch_all {
                            fl |= FLAG_CALL_MAY_THROW_UNCAUGHT;
                        }
                    }
                    Op::Return { .. } => {
                        fl |= FLAG_IS_EXIT;
                    }
                    Op::Throw { .. } if !has_catch_all => {
                        fl |= FLAG_IS_EXIT;
                    }
                    _ => {}
                }

                let s_start = all_succs.len() as u32;
                all_succs.extend_from_slice(&succs_buf);
                let s_end = all_succs.len() as u32;
                let raw = iid.raw();
                if raw < min_iid {
                    min_iid = raw;
                }
                if raw > max_iid {
                    max_iid = raw;
                }
                raw_entries.push((raw, fl, s_start, s_end));
            }
        }

        if raw_entries.is_empty() {
            return Self {
                start_point,
                ..Self::default()
            };
        }

        raw_entries.sort_unstable_by_key(|e| e.0);
        raw_entries.dedup_by_key(|e| e.0);

        let n_insts = raw_entries.len();
        let span = (max_iid - min_iid) as usize + 1;
        let use_dense = span <= n_insts.saturating_mul(4).saturating_add(16);

        if use_dense {
            let mut flags = vec![0u8; span];
            let mut succ_offsets = Vec::with_capacity(span + 1);
            let mut succ_targets = Vec::with_capacity(all_succs.len());
            let mut cur = 0usize;
            for (off, flag_slot) in flags.iter_mut().enumerate() {
                succ_offsets.push(succ_targets.len() as u32);
                let want_raw = min_iid + off as u32;
                if let Some(&(raw, fl, s_start, s_end)) = raw_entries.get(cur)
                    && raw == want_raw
                {
                    *flag_slot = fl;
                    succ_targets.extend_from_slice(&all_succs[s_start as usize..s_end as usize]);
                    cur += 1;
                }
            }
            succ_offsets.push(succ_targets.len() as u32);
            Self {
                start_point,
                base_iid: min_iid,
                inst_ids: Box::new([]),
                flags: flags.into_boxed_slice(),
                succ_offsets: succ_offsets.into_boxed_slice(),
                succ_targets: succ_targets.into_boxed_slice(),
            }
        } else {
            let mut inst_ids = Vec::with_capacity(n_insts);
            let mut flags = Vec::with_capacity(n_insts);
            let mut succ_offsets = Vec::with_capacity(n_insts + 1);
            let mut succ_targets = Vec::with_capacity(all_succs.len());
            for &(raw, fl, s_start, s_end) in &raw_entries {
                inst_ids.push(raw);
                flags.push(fl);
                succ_offsets.push(succ_targets.len() as u32);
                succ_targets.extend_from_slice(&all_succs[s_start as usize..s_end as usize]);
            }
            succ_offsets.push(succ_targets.len() as u32);
            Self {
                start_point,
                base_iid: 0,
                inst_ids: inst_ids.into_boxed_slice(),
                flags: flags.into_boxed_slice(),
                succ_offsets: succ_offsets.into_boxed_slice(),
                succ_targets: succ_targets.into_boxed_slice(),
            }
        }
    }

    #[inline]
    fn local_slot(&self, inst: InstId) -> Option<usize> {
        if self.flags.is_empty() {
            return None;
        }
        if self.inst_ids.is_empty() {
            let off = inst.raw().checked_sub(self.base_iid)? as usize;
            (off < self.flags.len()).then_some(off)
        } else {
            self.inst_ids.binary_search(&inst.raw()).ok()
        }
    }

    #[inline]
    fn flag(&self, inst: InstId, mask: u8) -> bool {
        self.local_slot(inst)
            .is_some_and(|slot| (self.flags[slot] & mask) != 0)
    }

    #[inline]
    fn succs(&self, inst: InstId) -> &[InstId] {
        let Some(slot) = self.local_slot(inst) else {
            return &[];
        };
        let start = self.succ_offsets[slot] as usize;
        let end = self.succ_offsets[slot + 1] as usize;
        &self.succ_targets[start..end]
    }
}

enum BlockFuncMap<'b> {
    Borrowed(&'b [Option<FuncId>]),
    Owned(Vec<Option<FuncId>>),
}

impl BlockFuncMap<'_> {
    #[inline]
    fn as_slice(&self) -> &[Option<FuncId>] {
        match self {
            Self::Borrowed(s) => s,
            Self::Owned(v) => v,
        }
    }
}

/// Lazy per-visited-function supergraph view (`#78`): avoids pre-building
/// `inst_succs` / `is_call` / `call_may_throw_uncaught` / `is_exit` across
/// hundreds of thousands of unvisited functions.
struct Supergraph<'m, 'b> {
    module: &'m Module,
    /// Block arena index → owning function (shared from `ModuleLinkTable` when available).
    block_func: BlockFuncMap<'b>,
    /// Function arena index → lazily materialized per-function supergraph.
    funcs: Vec<Option<Box<FuncSupergraph>>>,
}

impl<'m, 'b> Supergraph<'m, 'b> {
    fn new(module: &'m Module, shared_block_func: Option<&'b [Option<FuncId>]>) -> Self {
        let block_func = match shared_block_func {
            Some(bf) if bf.len() >= module.blocks.len() => BlockFuncMap::Borrowed(bf),
            _ => {
                let mut owned = vec![None; module.blocks.len()];
                for (fi, f) in module.functions.iter().enumerate() {
                    let func = FuncId::new(fi as u32);
                    for &b in &f.blocks {
                        if let Some(slot) = owned.get_mut(b.index()) {
                            *slot = Some(func);
                        }
                    }
                }
                BlockFuncMap::Owned(owned)
            }
        };
        let mut funcs = Vec::with_capacity(module.functions.len());
        funcs.resize_with(module.functions.len(), || None);
        Supergraph {
            module,
            block_func,
            funcs,
        }
    }

    #[inline]
    fn func_of(&self, inst: InstId) -> Option<FuncId> {
        let inst = self.module.inst(inst)?;
        self.block_func
            .as_slice()
            .get(inst.block.index())
            .copied()
            .flatten()
    }

    #[inline]
    fn ensure_func(&mut self, func: FuncId) -> Option<&FuncSupergraph> {
        let slot = self.funcs.get_mut(func.index())?;
        let fg = slot.get_or_insert_with(|| Box::new(FuncSupergraph::build(self.module, func)));
        Some(fg)
    }

    #[inline]
    fn ensure_for_inst(&mut self, inst: InstId) -> Option<&FuncSupergraph> {
        let func = self.func_of(inst)?;
        self.ensure_func(func)
    }

    fn start_point(&mut self, func: FuncId) -> Option<InstId> {
        self.ensure_func(func).and_then(|fg| fg.start_point)
    }

    fn is_call(&mut self, inst: InstId) -> bool {
        self.ensure_for_inst(inst)
            .is_some_and(|fg| fg.flag(inst, FLAG_IS_CALL))
    }

    fn call_may_throw_uncaught(&mut self, call: InstId) -> bool {
        self.ensure_for_inst(call)
            .is_some_and(|fg| fg.flag(call, FLAG_CALL_MAY_THROW_UNCAUGHT))
    }

    fn is_exit(&mut self, inst: InstId) -> bool {
        self.ensure_for_inst(inst)
            .is_some_and(|fg| fg.flag(inst, FLAG_IS_EXIT))
    }

    /// Number of intraprocedural (normal + exceptional) instruction successors.
    fn normal_succ_len(&mut self, inst: InstId) -> usize {
        self.ensure_for_inst(inst)
            .map_or(0, |fg| fg.succs(inst).len())
    }

    /// `idx`-th intraprocedural (normal + exceptional) instruction successor.
    fn normal_succ_at(&mut self, inst: InstId, idx: usize) -> InstId {
        self.ensure_for_inst(inst)
            .and_then(|fg| fg.succs(inst).get(idx).copied())
            .unwrap_or(inst)
    }

    /// Number of return sites (normal continuation + exceptional handler entries) of `call`.
    fn return_site_len(&mut self, call: InstId) -> usize {
        self.normal_succ_len(call)
    }

    /// `idx`-th return site of `call`.
    fn return_site_at(&mut self, call: InstId, idx: usize) -> InstId {
        self.normal_succ_at(call, idx)
    }
}

/// Interned solver fact identifier (`0` is always [`IfdsProblem::zero`]; `D6`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FactId(pub u32);

/// One transfer-function emission: either an allocation-free identity
/// passthrough of the input fact (`PassThrough`) or a newly constructed fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlowOut<F> {
    /// Reuse the incoming [`FactId`] directly without cloning or hashing `F`.
    PassThrough,
    /// Intern and emit `F`.
    Fact(F),
}

/// Zero-allocation transfer-function output buffer (`D6`, `#94`).
///
/// Calling [`Self::pass_through`] records an `O(1)` boolean flag so
/// [`IfdsSolver`] propagates the incoming [`FactId`] directly with **zero**
/// `Fact` clones, **zero** `Vec` allocations, and **zero** `HashMap` lookups.
#[derive(Debug)]
pub struct FlowSink<F> {
    pass_through: bool,
    extra_ids: Vec<FactId>,
    facts: Vec<F>,
}

impl<F> Default for FlowSink<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F> FlowSink<F> {
    /// Construct an empty sink.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pass_through: false,
            extra_ids: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// Clear all recorded emissions while retaining allocated buffer capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.pass_through = false;
        self.extra_ids.clear();
        self.facts.clear();
    }

    /// Propagate the incoming fact unchanged (`d2 -> d2`) without cloning or
    /// hashing `F`.
    #[inline]
    pub fn pass_through(&mut self) {
        self.pass_through = true;
    }

    /// Whether [`Self::pass_through`] was requested on this step.
    #[must_use]
    #[inline]
    pub const fn has_pass_through(&self) -> bool {
        self.pass_through
    }

    /// Emit a newly constructed or transformed fact.
    #[inline]
    pub fn emit(&mut self, fact: F) {
        self.facts.push(fact);
    }

    /// Emit a known [`FactId`] directly without cloning or hashing `F`.
    #[inline]
    pub fn emit_id(&mut self, id: FactId) {
        self.extra_ids.push(id);
    }

    /// Emit a [`FlowOut`] item.
    #[inline]
    pub fn emit_flow(&mut self, out: FlowOut<F>) {
        match out {
            FlowOut::PassThrough => self.pass_through(),
            FlowOut::Fact(fact) => self.emit(fact),
        }
    }

    /// Emit every fact from `iter`.
    #[inline]
    pub fn extend<I: IntoIterator<Item = F>>(&mut self, iter: I) {
        self.facts.extend(iter);
    }

    /// Mutable access to the materialized-fact buffer (used by default
    /// backward-compatible `*_out` adapters).
    #[inline]
    pub fn facts_mut(&mut self) -> &mut Vec<F> {
        &mut self.facts
    }
}

/// The client problem: fact type + the flow functions + seeds.
///
/// Clients may implement either the classic `Vec`-emitting methods
/// (`normal_flow`, `call_flow`, `return_flow`, `call_to_return_flow`,
/// `call_uncaught_exit_flow`) OR the zero-copy [`FlowSink`] methods
/// (`normal_flow_out`, `call_flow_out`, `return_flow_out`,
/// `call_to_return_flow_out`, `call_uncaught_exit_flow_out`), which default to
/// delegating to their `Vec`-based counterparts (`D6`).
pub trait IfdsProblem {
    /// The data-flow fact.
    type Fact: Clone + Eq + Hash + std::fmt::Debug;

    /// The zero (Λ) fact — the tautological fact from which new facts can be generated.
    fn zero(&self) -> Self::Fact;

    /// Initial seeds: `(function, fact)` pairs, planted at the function's
    /// start point (anchoring at function entry points keeps the callee
    /// self-loop summary discipline uniform).
    fn initial_seeds(&self) -> Vec<(FuncId, Self::Fact)>;

    /// Intraprocedural edge, including exceptional edges and phi-entry
    /// edges (`succ` may be a phi instruction; the incoming edge is
    /// recoverable from `curr`'s block). `succ` is passed so
    /// branch-sensitive analyses can split on the outgoing edge.
    fn normal_flow(
        &self,
        _module: &Module,
        _curr: InstId,
        _succ: InstId,
        _source: &Self::Fact,
        _out: &mut Vec<Self::Fact>,
    ) {
    }

    /// Zero-copy intraprocedural transfer (`D6`): defaults to [`Self::normal_flow`].
    fn normal_flow_out(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        _source_id: FactId,
        source: &Self::Fact,
        out: &mut FlowSink<Self::Fact>,
    ) {
        self.normal_flow(module, curr, succ, source, out.facts_mut());
    }

    /// Call edge into one concrete callee (call-graph resolution is the
    /// oracle's job, not the flow function's).
    fn call_flow(
        &self,
        _module: &Module,
        _call: InstId,
        _callee: FuncId,
        _source: &Self::Fact,
        _out: &mut Vec<Self::Fact>,
    ) {
    }

    /// Zero-copy call transfer (`D6`): defaults to [`Self::call_flow`].
    fn call_flow_out(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        _source_id: FactId,
        source: &Self::Fact,
        out: &mut FlowSink<Self::Fact>,
    ) {
        self.call_flow(module, call, callee, source, out.facts_mut());
    }

    /// Return edge out of `callee`'s `exit` instruction back to the call
    /// site. `call_site`/`return_site` are `None` under unbalanced
    /// returns of caller-less functions (the flow function is still invoked
    /// — it may record an external-return sink — and must tolerate `None`
    /// call/return sites).
    #[expect(
        clippy::too_many_arguments,
        reason = "distinct IFDS return-flow inputs"
    )]
    fn return_flow(
        &self,
        _module: &Module,
        _call_site: Option<InstId>,
        _callee: FuncId,
        _exit: InstId,
        _return_site: Option<InstId>,
        _source: &Self::Fact,
        _out: &mut Vec<Self::Fact>,
    ) {
    }

    /// Zero-copy return transfer (`D6`): defaults to [`Self::return_flow`].
    #[expect(
        clippy::too_many_arguments,
        reason = "distinct IFDS return-flow inputs"
    )]
    fn return_flow_out(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        _source_id: FactId,
        source: &Self::Fact,
        out: &mut FlowSink<Self::Fact>,
    ) {
        self.return_flow(
            module,
            call_site,
            callee,
            exit,
            return_site,
            source,
            out.facts_mut(),
        );
    }

    /// The call-to-return bypass edge: facts the callee cannot affect
    /// (locals not passed in, zero propagation) skip the call along it.
    fn call_to_return_flow(
        &self,
        _module: &Module,
        _call: InstId,
        _return_site: InstId,
        _source: &Self::Fact,
        _out: &mut Vec<Self::Fact>,
    ) {
    }

    /// Zero-copy call-to-return transfer (`D6`): defaults to [`Self::call_to_return_flow`].
    fn call_to_return_flow_out(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        _source_id: FactId,
        source: &Self::Fact,
        out: &mut FlowSink<Self::Fact>,
    ) {
        self.call_to_return_flow(module, call, return_site, source, out.facts_mut());
    }

    /// Uncaught-exception propagation out of `callee`'s `callee_exit` when
    /// `call_site` is not covered by a catch-all handler in its caller
    /// (`#79` `R4-D3`).
    fn call_uncaught_exit_flow(
        &self,
        _module: &Module,
        _call_site: InstId,
        _callee: FuncId,
        _callee_exit: InstId,
        _source: &Self::Fact,
        _out: &mut Vec<Self::Fact>,
    ) {
    }

    /// Zero-copy uncaught-exception exit transfer (`D6`): defaults to
    /// [`Self::call_uncaught_exit_flow`].
    #[expect(
        clippy::too_many_arguments,
        reason = "distinct IFDS uncaught-exit flow inputs"
    )]
    fn call_uncaught_exit_flow_out(
        &self,
        module: &Module,
        call_site: InstId,
        callee: FuncId,
        callee_exit: InstId,
        _source_id: FactId,
        source: &Self::Fact,
        out: &mut FlowSink<Self::Fact>,
    ) {
        self.call_uncaught_exit_flow(
            module,
            call_site,
            callee,
            callee_exit,
            source,
            out.facts_mut(),
        );
    }

    /// Whether the tautological zero fact (`Λ`) should propagate as `Λ -> Λ`
    /// across `call` into `callee`. Defaults to `true`.
    fn propagate_zero_to_callee(&self, _call: InstId, _callee: FuncId) -> bool {
        true
    }
}

/// Solver configuration.
#[derive(Clone, Copy, Debug, Default)]
pub struct IfdsConfig {
    /// Follow returns past seeds: when a callee was entered only via an
    /// initial seed (`Λ`), its exit facts return to ALL call sites the call
    /// graph knows — and when it has no callers at all, the return flow
    /// function is still invoked once with `None` call/return sites.
    pub follow_returns_past_seeds: bool,
}

/// A path edge: `(source fact, target node, target fact)`. The source
/// statement is omitted by design — it is always the start point of the
/// fact's anchor function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PathEdge<D> {
    /// The fact at the anchor function's start point.
    pub source_fact: D,
    /// The instruction the edge reaches.
    pub target_node: InstId,
    /// The fact at the target.
    pub target_fact: D,
}

/// Insertion-ordered compact set of interned fact IDs (`u32`), avoiding heap
/// `HashSet` allocation until membership exceeds 8 elements.
#[derive(Clone, Debug, Default)]
struct CompactU32Set {
    items: Vec<u32>,
    overflow: Option<HashSet<u32>>,
}

impl CompactU32Set {
    fn insert(&mut self, item: u32) -> bool {
        if let Some(set) = &mut self.overflow {
            if !set.insert(item) {
                return false;
            }
            self.items.push(item);
            return true;
        }
        if self.items.contains(&item) {
            return false;
        }
        self.items.push(item);
        if self.items.len() > 8 {
            self.overflow = Some(self.items.iter().copied().collect());
        }
        true
    }

    fn items(&self) -> &[u32] {
        &self.items
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

/// Insertion-ordered compact set of `(InstId, u32)` pairs for `incoming` and
/// `end_summary` tables, promoting to `HashSet` only when `items.len() > 8`.
#[derive(Clone, Debug, Default)]
struct CompactPairSet {
    items: Vec<(InstId, u32)>,
    overflow: Option<HashSet<(InstId, u32)>>,
}

impl CompactPairSet {
    fn insert(&mut self, item: (InstId, u32)) -> bool {
        if let Some(set) = &mut self.overflow {
            if !set.insert(item) {
                return false;
            }
            self.items.push(item);
            return true;
        }
        if self.items.contains(&item) {
            return false;
        }
        self.items.push(item);
        if self.items.len() > 8 {
            self.overflow = Some(self.items.iter().copied().collect());
        }
        true
    }

    fn items(&self) -> &[(InstId, u32)] {
        &self.items
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

/// Lazy node-indexed Compressed Sparse Row (CSR) index over `ordered_edges` (`#78`).
///
/// `offsets` has length `max_target_idx + 2` (or `0` when `ordered_edges` is
/// empty — never `module.insts.len() + 1` when only a subset of instructions
/// have propagated edges) and preserves exact first-arrival `ordered_edges`
/// order per target node (`N20`).
#[derive(Clone, Debug, Default)]
struct EdgeCsr {
    offsets: Vec<u32>,
    edge_indices: Vec<u32>,
}

impl EdgeCsr {
    fn build(ordered_edges: &[(u32, InstId, u32)]) -> Self {
        let Some(max_target_idx) = ordered_edges.iter().map(|e| e.1.index()).max() else {
            return Self::default();
        };
        let mut offsets = vec![0u32; max_target_idx + 2];
        for &(_, target, _) in ordered_edges {
            offsets[target.index()] += 1;
        }
        let mut acc = 0u32;
        for slot in &mut offsets {
            let cnt = *slot;
            *slot = acc;
            acc += cnt;
        }
        let mut edge_indices = vec![0u32; ordered_edges.len()];
        for (ei, &(_, target, _)) in ordered_edges.iter().enumerate() {
            let write_pos = &mut offsets[target.index()];
            edge_indices[*write_pos as usize] = ei as u32;
            *write_pos += 1;
        }
        offsets.copy_within(0..=max_target_idx, 1);
        offsets[0] = 0;
        Self {
            offsets,
            edge_indices,
        }
    }

    #[inline]
    fn indices_at(&self, node: InstId) -> &[u32] {
        let idx = node.index();
        let Some(end_idx) = idx.checked_add(1) else {
            return &[];
        };
        let Some(&end) = self.offsets.get(end_idx) else {
            return &[];
        };
        let start = self.offsets[idx];
        &self.edge_indices[start as usize..end as usize]
    }
}

/// The solver's result: everything phase-I computed, queryable.
#[derive(Debug)]
pub struct IfdsResult<D> {
    /// Interned fact ID → client fact.
    facts: Vec<D>,
    /// Client fact → interned fact ID.
    fact_ids: HashMap<D, u32>,
    /// Propagated path edges as compact interned triples `(source_id, target_node, target_id)`.
    ordered_edges: Vec<(u32, InstId, u32)>,
    /// Shared lazy target-node CSR index over `ordered_edges` (`#78`).
    csr: OnceLock<EdgeCsr>,
    /// Lazily materialized `PathEdge<D>` slice, in propagation order.
    path_edges: OnceLock<Vec<PathEdge<D>>>,
}

impl<D: Clone> Clone for IfdsResult<D> {
    fn clone(&self) -> Self {
        let csr = match self.csr.get() {
            Some(c) => OnceLock::from(c.clone()),
            None => OnceLock::new(),
        };
        let path_edges = match self.path_edges.get() {
            Some(edges) => OnceLock::from(edges.clone()),
            None => OnceLock::new(),
        };
        Self {
            facts: self.facts.clone(),
            fact_ids: self.fact_ids.clone(),
            ordered_edges: self.ordered_edges.clone(),
            csr,
            path_edges,
        }
    }
}

impl<D> IfdsResult<D> {
    #[inline]
    fn ensure_csr(&self) -> &EdgeCsr {
        self.csr.get_or_init(|| EdgeCsr::build(&self.ordered_edges))
    }

    /// Total number of propagated path edges, without materializing [`PathEdge`] clones.
    #[must_use]
    pub fn path_edge_count(&self) -> usize {
        self.ordered_edges.len()
    }

    /// Compact propagated path-edge triples `(source_fact_id, target_node, target_fact_id)`
    /// in propagation order.
    #[must_use]
    pub fn raw_path_edges(&self) -> &[(u32, InstId, u32)] {
        &self.ordered_edges
    }

    /// Look up the raw `(source_fact_id, target_node, target_fact_id)` triple at `edge_idx`.
    #[must_use]
    #[inline]
    pub fn raw_edge_at(&self, edge_idx: u32) -> Option<(u32, InstId, u32)> {
        self.ordered_edges.get(edge_idx as usize).copied()
    }

    /// Borrow `(source_fact, target_node, target_fact)` for `edge_idx` directly
    /// without cloning `D` (`#78`).
    #[must_use]
    #[inline]
    pub fn edge_at(&self, edge_idx: u32) -> Option<(&D, InstId, &D)> {
        let &(src_id, target_inst, dst_id) = self.ordered_edges.get(edge_idx as usize)?;
        Some((
            self.facts.get(src_id as usize)?,
            target_inst,
            self.facts.get(dst_id as usize)?,
        ))
    }

    /// Indices into [`Self::raw_path_edges`] / [`Self::edge_at`] targeting `node`
    /// in exact first-arrival propagation order (`N20`, `#78`).
    #[must_use]
    #[inline]
    pub fn edge_indices_at(&self, node: InstId) -> &[u32] {
        self.ensure_csr().indices_at(node)
    }

    /// Whether any path edge (including `zero`) reached `node` (`#78`).
    #[must_use]
    #[inline]
    pub fn has_any_fact_at(&self, node: InstId) -> bool {
        !self.edge_indices_at(node).is_empty()
    }

    /// Look up a client fact by its interned `u32` ID.
    #[must_use]
    pub fn fact_by_id(&self, id: u32) -> Option<&D> {
        self.facts.get(id as usize)
    }
}

impl<D: Clone + Eq + Hash> IfdsResult<D> {
    /// Look up the interned `u32` ID of `fact`, if `fact` was interned during tabulation.
    #[must_use]
    pub fn id_of_fact(&self, fact: &D) -> Option<u32> {
        self.fact_ids.get(fact).copied()
    }

    /// Whether at least one non-`zero` fact reached `node` (`#78`).
    #[must_use]
    pub fn has_non_zero_fact_at(&self, node: InstId, zero: &D) -> bool {
        let eidxs = self.edge_indices_at(node);
        if eidxs.is_empty() {
            return false;
        }
        let zero_id = self.fact_ids.get(zero).copied();
        eidxs
            .iter()
            .any(|&ei| Some(self.ordered_edges[ei as usize].2) != zero_id)
    }

    /// The facts holding at `node` (zero excluded), in propagation order.
    #[must_use]
    pub fn facts_at(&self, node: InstId, zero: &D) -> Vec<D> {
        let eidxs = self.edge_indices_at(node);
        if eidxs.is_empty() {
            return Vec::new();
        }
        let zero_id = self.fact_ids.get(zero).copied();
        let mut seen = CompactU32Set::default();
        let mut out = Vec::new();
        for &ei in eidxs {
            let dst_id = self.ordered_edges[ei as usize].2;
            if Some(dst_id) != zero_id
                && seen.insert(dst_id)
                && let Some(fact) = self.facts.get(dst_id as usize)
            {
                out.push(fact.clone());
            }
        }
        out
    }

    /// Whether `fact` was propagated to `node` (zero included).
    #[must_use]
    pub fn is_reached(&self, node: InstId, fact: &D) -> bool {
        let Some(&id) = self.fact_ids.get(fact) else {
            return false;
        };
        self.edge_indices_at(node)
            .iter()
            .any(|&ei| self.ordered_edges[ei as usize].2 == id)
    }

    /// Every propagated path edge, in propagation order.
    pub fn path_edges(&self) -> &[PathEdge<D>] {
        self.path_edges.get_or_init(|| {
            self.ordered_edges
                .iter()
                .map(|&(src, target_node, dst)| PathEdge {
                    source_fact: self.facts[src as usize].clone(),
                    target_node,
                    target_fact: self.facts[dst as usize].clone(),
                })
                .collect()
        })
    }
}

/// The solver. Construct over a module + problem + call-graph oracle,
/// then [`IfdsSolver::solve`] or [`IfdsSolver::solve_with_block_func`].
pub struct IfdsSolver<'m, 'p, P: IfdsProblem, C: CallGraphOracle> {
    module: &'m Module,
    problem: &'p P,
    callgraph: &'p C,
    config: IfdsConfig,
    shared_block_func: Option<&'m [Option<FuncId>]>,
    /// Interned facts table (`u32` id → `P::Fact`).
    facts: Vec<P::Fact>,
    /// Reverse interning map (`P::Fact` → `u32` id; lookup-only).
    fact_ids: HashMap<P::Fact, u32>,
    /// Interned ID of `problem.zero()` (always `0`).
    zero_id: u32,
}

struct TabulationState<'m, 'b, 'p, P: IfdsProblem, C: CallGraphOracle> {
    module: &'m Module,
    problem: &'p P,
    callgraph: &'p C,
    config: IfdsConfig,
    graph: Supergraph<'m, 'b>,
    facts: Vec<P::Fact>,
    fact_ids: HashMap<P::Fact, u32>,
    zero_id: u32,
    edge_hasher: RandomState,
    /// Index-only deduplication table over `ordered_edges` (`4 B` per slot; `#78`).
    edge_table: HashTable<u32>,
    /// Separate deduplication table for uncaught-exception exits at call sites
    /// (`D6`, `#94`) indexing `ordered_edges`.
    uncaught_edge_table: HashTable<u32>,
    /// Indices in `ordered_edges` initially inserted by `propagate_uncaught_exit`
    /// so `work_cursor` does not run normal `process_call` on uncaught-only exits.
    uncaught_first_indices: HashSet<u32>,
    /// Rare `D6` overlap queue: normal arrivals whose `(d1, call_site, d2)` triple
    /// was previously inserted into `ordered_edges` by `propagate_uncaught_exit`,
    /// tagged with the `ordered_edges.len()` position at enqueue time to preserve
    /// 100% exact FIFO scheduling order (`N20`).
    requeued_normal: VecDeque<(usize, (u32, InstId, u32))>,
    /// Reverse index: `(target node, target fact id)` → source fact ids.
    by_target: HashMap<(InstId, u32), CompactU32Set>,
    /// `(callee start point, callee entry fact id)` → `(call site, fact id at the call)`.
    incoming: HashMap<(InstId, u32), CompactPairSet>,
    /// `(callee start point, anchor fact id)` → `(exit node, exit fact id)`.
    end_summary: HashMap<(InstId, u32), CompactPairSet>,
    /// Monotonic cursor into `ordered_edges` driving the main FIFO worklist (`#78`).
    work_cursor: usize,
    /// Iterative queue of uncaught-throw call-site exits awaiting `process_exit`.
    exit_worklist: VecDeque<(u32, InstId, u32)>,
    /// Reusable zero-copy transfer sink avoiding per-edge heap allocations.
    scratch_sink: FlowSink<P::Fact>,
    /// Reusable interned target-ID scratch buffer for leaf flow evaluations (`#84.3a`).
    scratch_ids: Vec<u32>,
    /// Reusable interned target-ID scratch buffer for outer `call_flow_out` loops (`#84.3a`).
    scratch_call_ids: Vec<u32>,
    /// Propagation order record (the result).
    ordered_edges: Vec<(u32, InstId, u32)>,
}

impl<'m, 'p, P: IfdsProblem, C: CallGraphOracle> IfdsSolver<'m, 'p, P, C> {
    /// Construct a solver over `module`; supergraph slices materialize lazily
    /// per visited function during [`Self::solve`] / [`Self::solve_with_block_func`].
    pub fn new(module: &'m Module, problem: &'p P, callgraph: &'p C, config: IfdsConfig) -> Self {
        let zero = problem.zero();
        let mut facts = Vec::new();
        let mut fact_ids = HashMap::new();
        facts.push(zero.clone());
        fact_ids.insert(zero, 0);
        IfdsSolver {
            module,
            problem,
            callgraph,
            config,
            shared_block_func: None,
            facts,
            fact_ids,
            zero_id: 0,
        }
    }

    /// Attach a prebuilt `BlockId::index() -> Option<FuncId>` slice (such as
    /// [`crate::module_link::ModuleLinkTable::block_func_slice`]) to avoid
    /// rebuilding `block_func` (`#78`).
    #[must_use]
    pub fn with_block_func(mut self, block_func: &'m [Option<FuncId>]) -> Self {
        self.shared_block_func = Some(block_func);
        self
    }

    /// Run tabulation to the fixed point and return the reachability result.
    pub fn solve(self) -> IfdsResult<P::Fact> {
        let shared = self.shared_block_func;
        self.solve_with_block_func(shared)
    }

    /// Run tabulation sharing an optional prebuilt `block_func` slice (`#78`).
    pub fn solve_with_block_func(
        self,
        block_func: Option<&[Option<FuncId>]>,
    ) -> IfdsResult<P::Fact> {
        let chosen_bf = block_func.or(self.shared_block_func);
        let state = TabulationState {
            module: self.module,
            problem: self.problem,
            callgraph: self.callgraph,
            config: self.config,
            graph: Supergraph::new(self.module, chosen_bf),
            facts: self.facts,
            fact_ids: self.fact_ids,
            zero_id: self.zero_id,
            edge_hasher: RandomState::new(),
            edge_table: HashTable::new(),
            uncaught_edge_table: HashTable::new(),
            uncaught_first_indices: HashSet::new(),
            requeued_normal: VecDeque::new(),
            by_target: HashMap::new(),
            incoming: HashMap::new(),
            end_summary: HashMap::new(),
            work_cursor: 0,
            exit_worklist: VecDeque::new(),
            scratch_sink: FlowSink::new(),
            scratch_ids: Vec::new(),
            scratch_call_ids: Vec::new(),
            ordered_edges: Vec::new(),
        };
        state.run()
    }
}

impl<'m, 'b, 'p, P: IfdsProblem, C: CallGraphOracle> TabulationState<'m, 'b, 'p, P, C> {
    fn intern_fact(&mut self, fact: P::Fact) -> u32 {
        if let Some(&id) = self.fact_ids.get(&fact) {
            return id;
        }
        let id = self.facts.len() as u32;
        self.fact_ids.insert(fact.clone(), id);
        self.facts.push(fact);
        id
    }

    /// The single chokepoint for the join and the worklist: an edge is
    /// processed iff it is new in `edge_table`.
    fn propagate(&mut self, source: u32, target_node: InstId, target_fact: u32) {
        let key = (source, target_node, target_fact);
        let hash = self.edge_hasher.hash_one(key);
        let ordered_ref = &self.ordered_edges;
        if self
            .edge_table
            .find(hash, |&idx| ordered_ref[idx as usize] == key)
            .is_some()
        {
            return;
        }
        let existing_uncaught = self
            .uncaught_edge_table
            .find(hash, |&idx| ordered_ref[idx as usize] == key)
            .copied();

        let edge_idx = match existing_uncaught {
            Some(idx) => {
                self.requeued_normal
                    .push_back((self.ordered_edges.len(), key));
                idx
            }
            None => {
                let idx = self.ordered_edges.len() as u32;
                self.ordered_edges.push(key);
                idx
            }
        };

        let ordered_ref = &self.ordered_edges;
        let hasher = &self.edge_hasher;
        self.edge_table.insert_unique(hash, edge_idx, |&existing| {
            hasher.hash_one(ordered_ref[existing as usize])
        });

        if self.graph.is_call(target_node)
            && !self.callgraph.callees_of_call_at(target_node).is_empty()
        {
            self.by_target
                .entry((target_node, target_fact))
                .or_default()
                .insert(source);
        }
    }

    /// Record an uncaught-exception exit `(caller_entry, call_site, uncaught_fact)`
    /// in `uncaught_edge_table` (separate from normal `edge_table` so normal arrival
    /// and uncaught exit at `call_site` never mask each other, `D6`).
    fn propagate_uncaught_exit(
        &mut self,
        caller_entry: u32,
        call_site: InstId,
        uncaught_fact: u32,
    ) {
        let key = (caller_entry, call_site, uncaught_fact);
        let hash = self.edge_hasher.hash_one(key);
        let ordered_ref = &self.ordered_edges;
        if self
            .uncaught_edge_table
            .find(hash, |&idx| ordered_ref[idx as usize] == key)
            .is_some()
        {
            return;
        }
        let existing_normal = self
            .edge_table
            .find(hash, |&idx| ordered_ref[idx as usize] == key)
            .copied();

        let edge_idx = match existing_normal {
            Some(idx) => idx,
            None => {
                let idx = self.ordered_edges.len() as u32;
                self.ordered_edges.push(key);
                self.uncaught_first_indices.insert(idx);
                idx
            }
        };

        let ordered_ref = &self.ordered_edges;
        let hasher = &self.edge_hasher;
        self.uncaught_edge_table
            .insert_unique(hash, edge_idx, |&existing| {
                hasher.hash_one(ordered_ref[existing as usize])
            });
        self.exit_worklist.push_back(key);
    }

    /// Drain `sink` into caller-provided `ids` scratch buffer without allocating
    /// a fresh `Vec` per edge (`#84` Part 3a).
    fn drain_sink_into(
        &mut self,
        source: u32,
        keep_zero: bool,
        mut sink: FlowSink<P::Fact>,
        ids: &mut Vec<u32>,
    ) {
        ids.clear();
        let extra_cap = usize::from(sink.pass_through) + usize::from(keep_zero);
        ids.reserve(sink.extra_ids.len() + sink.facts.len() + extra_cap);
        let mut saw_zero = false;
        if sink.pass_through {
            if source == self.zero_id {
                saw_zero = true;
            }
            ids.push(source);
        }
        for raw_id in sink.extra_ids.drain(..) {
            if (raw_id.0 as usize) < self.facts.len() {
                if raw_id.0 == self.zero_id {
                    saw_zero = true;
                }
                ids.push(raw_id.0);
            }
        }
        for fact in sink.facts.drain(..) {
            let id = self.intern_fact(fact);
            if id == self.zero_id {
                saw_zero = true;
            }
            ids.push(id);
        }
        self.scratch_sink = sink;
        if keep_zero && !saw_zero {
            ids.push(self.zero_id);
        }
    }

    /// Compute a leaf flow function's interned target fact IDs into `scratch_ids`.
    fn compute_targets(
        &mut self,
        source: u32,
        f: impl FnOnce(&P, &Module, FactId, &P::Fact, &mut FlowSink<P::Fact>),
    ) -> Vec<u32> {
        let keep_zero = source == self.zero_id;
        self.compute_targets_with_zero(source, keep_zero, f)
    }

    /// Compute a leaf flow function's interned target fact IDs into `scratch_ids`,
    /// auto-injecting `Λ` only when `keep_zero` is `true`.
    fn compute_targets_with_zero(
        &mut self,
        source: u32,
        keep_zero: bool,
        f: impl FnOnce(&P, &Module, FactId, &P::Fact, &mut FlowSink<P::Fact>),
    ) -> Vec<u32> {
        let mut sink = std::mem::take(&mut self.scratch_sink);
        sink.clear();
        f(
            self.problem,
            self.module,
            FactId(source),
            &self.facts[source as usize],
            &mut sink,
        );
        let mut ids = std::mem::take(&mut self.scratch_ids);
        self.drain_sink_into(source, keep_zero, sink, &mut ids);
        ids
    }

    /// Compute `call_uncaught_exit_flow_out` target fact IDs into `scratch_ids`
    /// without injecting `Λ`.
    fn compute_uncaught_targets(
        &mut self,
        call_site: InstId,
        callee: FuncId,
        callee_exit: InstId,
        source: u32,
    ) -> Vec<u32> {
        let mut sink = std::mem::take(&mut self.scratch_sink);
        sink.clear();
        self.problem.call_uncaught_exit_flow_out(
            self.module,
            call_site,
            callee,
            callee_exit,
            FactId(source),
            &self.facts[source as usize],
            &mut sink,
        );
        let mut ids = std::mem::take(&mut self.scratch_ids);
        self.drain_sink_into(source, false, sink, &mut ids);
        ids
    }

    /// Compute `call_flow_out` target fact IDs into `scratch_call_ids`.
    fn compute_call_targets(&mut self, call: InstId, callee: FuncId, source: u32) -> Vec<u32> {
        let mut sink = std::mem::take(&mut self.scratch_sink);
        sink.clear();
        self.problem.call_flow_out(
            self.module,
            call,
            callee,
            FactId(source),
            &self.facts[source as usize],
            &mut sink,
        );
        let keep_zero =
            source == self.zero_id && self.problem.propagate_zero_to_callee(call, callee);
        let mut ids = std::mem::take(&mut self.scratch_call_ids);
        self.drain_sink_into(source, keep_zero, sink, &mut ids);
        ids
    }

    fn drain_exit_worklist(&mut self) {
        while let Some(exit_edge) = self.exit_worklist.pop_front() {
            self.process_exit(exit_edge);
        }
    }

    fn pop_next_normal_edge(&mut self) -> Option<(u32, InstId, u32)> {
        loop {
            if let Some(&(at_cursor, edge)) = self.requeued_normal.front()
                && at_cursor <= self.work_cursor
            {
                self.requeued_normal.pop_front();
                return Some(edge);
            }
            if self.work_cursor >= self.ordered_edges.len() {
                return self.requeued_normal.pop_front().map(|(_, edge)| edge);
            }
            let idx = self.work_cursor;
            self.work_cursor += 1;
            if !self.uncaught_first_indices.is_empty()
                && self.uncaught_first_indices.contains(&(idx as u32))
            {
                continue;
            }
            return Some(self.ordered_edges[idx]);
        }
    }

    fn run(mut self) -> IfdsResult<P::Fact> {
        let zero_id = self.zero_id;
        for (func, fact) in self.problem.initial_seeds() {
            let Some(sp) = self.graph.start_point(func) else {
                continue;
            };
            let fact_id = self.intern_fact(fact);
            self.propagate(zero_id, sp, zero_id);
            self.propagate(zero_id, sp, fact_id);
        }

        loop {
            self.drain_exit_worklist();
            let Some(edge) = self.pop_next_normal_edge() else {
                break;
            };
            let n = edge.1;
            if self.graph.is_call(n) {
                self.process_call(edge);
            } else {
                if self.graph.is_exit(n) {
                    self.process_exit(edge);
                }
                if self.graph.normal_succ_len(n) > 0 {
                    self.process_normal(edge);
                }
            }
        }

        IfdsResult {
            facts: self.facts,
            fact_ids: self.fact_ids,
            ordered_edges: self.ordered_edges,
            csr: OnceLock::new(),
            path_edges: OnceLock::new(),
        }
    }

    /// Normal flow over intraprocedural successors (including first-class
    /// exceptional edges).
    fn process_normal(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let succ_len = self.graph.normal_succ_len(n);
        for i in 0..succ_len {
            let succ = self.graph.normal_succ_at(n, i);
            let targets = self.compute_targets(d2, |p, m, src_id, src, out| {
                p.normal_flow_out(m, n, succ, src_id, src, out);
            });
            for &t in &targets {
                self.propagate(d1, succ, t);
            }
            self.scratch_ids = targets;
        }
    }

    /// Caller-side tabulation: callee entry self-loops + summary replay +
    /// call-to-return bypass.
    fn process_call(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let callgraph = self.callgraph;
        let callees = callgraph.callees_of_call_at(n);
        for &callee in callees {
            let Some(sp) = self.graph.start_point(callee) else {
                continue;
            };
            let d3s = self.compute_call_targets(n, callee, d2);
            for &d3 in &d3s {
                self.propagate(d3, sp, d3);
                self.incoming.entry((sp, d3)).or_default().insert((n, d2));
                let summary_len = self
                    .end_summary
                    .get(&(sp, d3))
                    .map_or(0, CompactPairSet::len);
                for si in 0..summary_len {
                    let Some(&(ep, d4)) = self
                        .end_summary
                        .get(&(sp, d3))
                        .and_then(|s| s.items().get(si))
                    else {
                        break;
                    };
                    let ret_len = self.graph.return_site_len(n);
                    for ri in 0..ret_len {
                        let ret_site = self.graph.return_site_at(n, ri);
                        let d5s = self.compute_targets(d4, |p, m, src_id, src, out| {
                            p.return_flow_out(
                                m,
                                Some(n),
                                callee,
                                ep,
                                Some(ret_site),
                                src_id,
                                src,
                                out,
                            );
                        });
                        for &d5 in &d5s {
                            self.propagate(d1, ret_site, d5);
                        }
                        self.scratch_ids = d5s;
                    }
                    if self.graph.call_may_throw_uncaught(n) {
                        let d_uncaughts = self.compute_uncaught_targets(n, callee, ep, d4);
                        for &d_unc in &d_uncaughts {
                            self.propagate_uncaught_exit(d1, n, d_unc);
                        }
                        self.scratch_ids = d_uncaughts;
                    }
                }
            }
            self.scratch_call_ids = d3s;
        }
        self.drain_exit_worklist();

        // Call-to-return flow: facts the callee cannot affect bypass the
        // call. This also covers UNKNOWN callees — caller-side facts always
        // survive across the call site.
        let ret_len = self.graph.return_site_len(n);
        for ri in 0..ret_len {
            let ret_site = self.graph.return_site_at(n, ri);
            let d6s = self.compute_targets(d2, |p, m, src_id, src, out| {
                p.call_to_return_flow_out(m, n, ret_site, src_id, src, out);
            });
            for &d6 in &d6s {
                self.propagate(d1, ret_site, d6);
            }
            self.scratch_ids = d6s;
        }
    }

    /// Callee-side tabulation: record the summary edge, then apply return
    /// flow (and uncaught-throw propagation) to every recorded caller.
    fn process_exit(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let Some(func) = self.graph.func_of(n) else {
            return;
        };
        let Some(sp) = self.graph.start_point(func) else {
            return;
        };

        if !self
            .end_summary
            .entry((sp, d1))
            .or_default()
            .insert((n, d2))
        {
            return;
        }

        let inc_len = self.incoming.get(&(sp, d1)).map_or(0, CompactPairSet::len);

        for ii in 0..inc_len {
            let Some(&(call_site, d4)) =
                self.incoming.get(&(sp, d1)).and_then(|s| s.items().get(ii))
            else {
                break;
            };
            let ret_len = self.graph.return_site_len(call_site);
            for ri in 0..ret_len {
                let ret_site = self.graph.return_site_at(call_site, ri);
                let d5s = self.compute_targets(d2, |p, m, src_id, src, out| {
                    p.return_flow_out(
                        m,
                        Some(call_site),
                        func,
                        n,
                        Some(ret_site),
                        src_id,
                        src,
                        out,
                    );
                });
                for &d5 in &d5s {
                    let callers_len = self
                        .by_target
                        .get(&(call_site, d4))
                        .map_or(0, CompactU32Set::len);
                    for ci in 0..callers_len {
                        let Some(&d3) = self
                            .by_target
                            .get(&(call_site, d4))
                            .and_then(|s| s.items().get(ci))
                        else {
                            break;
                        };
                        self.propagate(d3, ret_site, d5);
                    }
                }
                self.scratch_ids = d5s;
            }
            if self.graph.call_may_throw_uncaught(call_site) {
                let d_uncaughts = self.compute_uncaught_targets(call_site, func, n, d2);
                for &d_unc in &d_uncaughts {
                    let callers_len = self
                        .by_target
                        .get(&(call_site, d4))
                        .map_or(0, CompactU32Set::len);
                    for ci in 0..callers_len {
                        let Some(&d3) = self
                            .by_target
                            .get(&(call_site, d4))
                            .and_then(|s| s.items().get(ci))
                        else {
                            break;
                        };
                        self.propagate_uncaught_exit(d3, call_site, d_unc);
                    }
                }
                self.scratch_ids = d_uncaughts;
            }
        }

        // Unbalanced returns (`follow_returns_past_seeds`): seeded-but-never-called
        // functions return to every known call site; caller-less
        // functions still get one return-flow invocation with `None`s.
        if self.config.follow_returns_past_seeds && d1 == self.zero_id && inc_len == 0 {
            let callgraph = self.callgraph;
            let callers = callgraph.callers_of(func);
            if callers.is_empty() {
                let ignored =
                    self.compute_targets_with_zero(d2, false, |p, m, src_id, src, out| {
                        p.return_flow_out(m, None, func, n, None, src_id, src, out);
                    });
                self.scratch_ids = ignored;
            } else {
                for &call_site in callers {
                    let ret_len = self.graph.return_site_len(call_site);
                    for ri in 0..ret_len {
                        let ret_site = self.graph.return_site_at(call_site, ri);
                        let d5s =
                            self.compute_targets_with_zero(d2, false, |p, m, src_id, src, out| {
                                p.return_flow_out(
                                    m,
                                    Some(call_site),
                                    func,
                                    n,
                                    Some(ret_site),
                                    src_id,
                                    src,
                                    out,
                                );
                            });
                        for &d5 in &d5s {
                            self.propagate(self.zero_id, ret_site, d5);
                        }
                        self.scratch_ids = d5s;
                    }
                    if self.graph.call_may_throw_uncaught(call_site) {
                        let d_uncaughts = self.compute_uncaught_targets(call_site, func, n, d2);
                        for &d_unc in &d_uncaughts {
                            self.propagate_uncaught_exit(self.zero_id, call_site, d_unc);
                        }
                        self.scratch_ids = d_uncaughts;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
