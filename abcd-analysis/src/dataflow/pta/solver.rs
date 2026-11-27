//! Andersen `k=1` delta-worklist pointer-analysis solver state, statement-handler
//! firing cascade, N66 call/prototype/super wiring, and fixed-point `pump` loop.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use abcd_ir::{CallKind, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId};

use crate::callgraph::CallGraph;
use crate::dataflow::ifds::CallGraphOracle;
use crate::frame::frame_slots_of;
use crate::module_link::ModuleLinkTable;

use super::env::EnvState;
use super::scan::{SliceInit, class_named_methods, is_super_call_kind};
use super::{
    Handler, MAX_SLICED_DYN_HOP, Obj, ObjLoc, PackedCtx, PackedFunc, PtaConfig, PtaStats, Ptr,
    Read, Slot,
};

/// Deferred step on the iterative handler-firing stack.
pub(super) enum FireStep {
    Fire(u32, Obj),
    AddEdge(Ptr, Ptr),
}

/// The engine state.
pub(super) struct Pta<'m> {
    pub(super) module: &'m Module,
    pub(super) links: &'m ModuleLinkTable,
    pub(super) base: &'m CallGraph,
    pub(super) config: &'m PtaConfig,
    pub(super) env_stack_at: &'m [Arc<EnvState>],
    /// Root set when running in demand-driven / root-sliced mode (`None` =
    /// whole-module mode).
    pub(super) root_keep: Option<BTreeSet<FuncId>>,
    /// Bounded static forward-slice allowlist (`Some` iff `roots.is_some()`).
    pub(super) slice_allow: Option<Vec<bool>>,
    /// Per-function hop distance from roots in sliced mode (`u8::MAX` if unreached).
    pub(super) func_hop: Vec<u8>,
    /// Maximum dynamic closure / module-init / lex-owner hop distance in sliced mode.
    pub(super) max_dyn_hop: u8,
    /// Points-to sets.
    pub(super) pts: BTreeMap<Ptr, BTreeSet<Obj>>,
    /// Subset edges `s → t`.
    pub(super) edges: BTreeMap<Ptr, BTreeSet<Ptr>>,
    /// Pending `(pointer, object)` facts (the delta worklist — pop min).
    pub(super) worklist: BTreeSet<(Ptr, Obj)>,
    /// Activations requested so far.
    pub(super) activated: BTreeSet<(FuncId, PackedCtx)>,
    /// Activations requested but not yet scanned (pop min).
    pub(super) pending_activations: BTreeSet<(FuncId, PackedCtx)>,
    /// Activations already scanned.
    pub(super) scanned: BTreeSet<(FuncId, PackedCtx)>,
    /// Handlers in registration (scan) order — the id is the index.
    pub(super) handlers: Vec<(Ptr, Handler)>,
    /// Handler ids registered per base pointer (lookup-only map).
    pub(super) handlers_by_base: HashMap<Ptr, Vec<u32>>,
    /// `(handler, object)` pairs already fired.
    pub(super) fired: BTreeSet<(u32, Obj)>,
    /// Explicit LIFO workstack for iterative handler firing and re-arm cascades.
    pub(super) fire_stack: Vec<FireStep>,
    /// Dynamic-read / copy-src `(handler id, object)` pairs indexed by `ObjLoc`
    /// (lookup-only map; `BTreeSet` values preserve deterministic `(id, o)` order).
    pub(super) dyn_loads_by_obj: HashMap<ObjLoc, BTreeSet<(u32, Obj)>>,
    /// Buckets known per `ObjLoc` — a NEW bucket re-arms the dynamic reads /
    /// property copies / prototype delegations that already fired on the object.
    pub(super) buckets: BTreeMap<ObjLoc, BTreeSet<Slot>>,
    /// Excluded constant string keys per `CopyProps` / `CopyFromSrc` handler.
    pub(super) copy_excluded: Vec<BTreeSet<Sym>>,
    /// Own named methods declared directly on `(ObjLoc, Slot)` so inherited
    /// superclass prototype/static methods do not overwrite subclass overrides.
    pub(super) own_class_members: HashSet<(ObjLoc, Slot)>,
    /// `DefineClass` / `DefineSendableClass` instruction sites.
    pub(super) class_sites: HashSet<InstId>,
    /// Active `(class_site, class_ctx)` pairs per constructor `FuncId`.
    pub(super) ctor_class_activations: HashMap<FuncId, BTreeSet<(InstId, PackedCtx)>>,
    /// Interned `Sym`s equal to `"prototype"` in `module.sym`.
    pub(super) proto_syms: Vec<Sym>,
    /// Interned `Sym`s equal to `"value"` in `module.sym` (for `CreateIterResultObj`).
    pub(super) value_syms: Vec<Sym>,
    /// Variadic argument sinks `(var_iid, skip_formals)` (`GetUnmappedArgs` /
    /// `CopyRestArgs`) per function `FuncId`.
    pub(super) variadic_sinks: HashMap<FuncId, Vec<(InstId, usize)>>,
    /// Writer functions per `(NewLexEnv InstId, slot)` pair, plus non-owner writers.
    pub(super) lex_writers: BTreeMap<(InstId, u16), BTreeSet<FuncId>>,
    /// `(NewLexEnv InstId, slot)` pairs written by at least one child closure (`func != owner_fn`).
    pub(super) lex_captured_mutated: HashSet<(InstId, u16)>,
    /// Instance methods `(method_sym, mfid)` per constructor `FuncId`.
    pub(super) ctor_inst_methods: HashMap<FuncId, Vec<(Sym, FuncId)>>,
    /// Wired internal call edges `(call, caller ctx, callee)`.
    pub(super) wired: BTreeSet<(InstId, PackedCtx, FuncId)>,
    /// PTA-resolved call targets `(call, caller ctx)` → bodies.
    pub(super) call_targets: BTreeMap<(InstId, PackedCtx), BTreeSet<FuncId>>,
    /// Call-site activations whose callee set contained `Unknown`.
    pub(super) call_unknown: BTreeSet<(InstId, PackedCtx)>,
    /// Call sites where root-slicing / dynamic-hop caps skipped wiring a target.
    pub(super) hop_cut_calls: BTreeSet<InstId>,
    /// Scanned call activations `(call, caller ctx)` for completeness checking.
    pub(super) scanned_calls: Vec<(InstId, PackedCtx)>,
    /// Scanned call activations already tainted for incomplete/external escape.
    pub(super) tainted_calls: BTreeSet<(InstId, PackedCtx)>,
    /// Load-result pointers (the empty-bucket post-pass).
    pub(super) load_results: Vec<Ptr>,
    /// Lazily populated `FuncId` → returned values (block/inst order).
    pub(super) returns_of: HashMap<FuncId, Vec<ValueId>>,
    pub(super) stats: PtaStats,
}

impl<'m> Pta<'m> {
    pub(super) fn new(
        module: &'m Module,
        links: &'m ModuleLinkTable,
        base: &'m CallGraph,
        config: &'m PtaConfig,
        env_stack_at: &'m [Arc<EnvState>],
        slice_init: Option<SliceInit>,
    ) -> Self {
        let (root_keep, slice_allow, func_hop, max_dyn_hop) = match slice_init {
            Some(s) => (
                Some(s.root_keep),
                Some(s.slice_allow),
                s.func_hop,
                s.max_dyn_hop,
            ),
            None => (None, None, Vec::new(), MAX_SLICED_DYN_HOP),
        };
        let mut proto_syms = Vec::new();
        let mut value_syms = Vec::new();
        for si in 0..module.sym.len() {
            let sym = Sym::new(si as u32);
            match module.sym.resolve(sym) {
                Some("prototype") => proto_syms.push(sym),
                Some("value") => value_syms.push(sym),
                _ => {}
            }
        }
        let mut ctor_inst_methods: HashMap<FuncId, Vec<(Sym, FuncId)>> = HashMap::new();
        let mut class_sites: HashSet<InstId> = HashSet::new();
        let mut variadic_sinks: HashMap<FuncId, Vec<(InstId, usize)>> = HashMap::new();
        let mut lex_captured_mutated: HashSet<(InstId, u16)> = HashSet::new();

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
                            class_sites.insert(iid);
                            let entry = ctor_inst_methods.entry(cls.ctor).or_default();
                            for (sym, mfid, is_static) in class_named_methods(module, cls) {
                                if !is_static && !entry.contains(&(sym, mfid)) {
                                    entry.push((sym, mfid));
                                }
                            }
                        }
                        Op::GetUnmappedArgs => {
                            variadic_sinks.entry(fid).or_default().push((iid, 0));
                        }
                        Op::CopyRestArgs { start_index } => {
                            variadic_sinks
                                .entry(fid)
                                .or_default()
                                .push((iid, *start_index as usize));
                        }
                        Op::PutLexVar {
                            level, slot, kind, ..
                        } => {
                            if let Some(entry) = env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(*kind))
                                .and_then(|ch| ch.at_level(*level))
                            {
                                for &env_site in &entry.sites {
                                    if links.inst_func(module, env_site) != Some(fid) {
                                        lex_captured_mutated.insert((env_site, *slot));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        Pta {
            module,
            links,
            base,
            config,
            env_stack_at,
            root_keep,
            slice_allow,
            func_hop,
            max_dyn_hop,
            pts: BTreeMap::new(),
            edges: BTreeMap::new(),
            worklist: BTreeSet::new(),
            activated: BTreeSet::new(),
            pending_activations: BTreeSet::new(),
            scanned: BTreeSet::new(),
            handlers: Vec::new(),
            handlers_by_base: HashMap::new(),
            fired: BTreeSet::new(),
            fire_stack: Vec::new(),
            dyn_loads_by_obj: HashMap::new(),
            buckets: BTreeMap::new(),
            copy_excluded: vec![BTreeSet::new()],
            own_class_members: HashSet::new(),
            class_sites,
            ctor_class_activations: HashMap::new(),
            proto_syms,
            value_syms,
            variadic_sinks,
            lex_writers: BTreeMap::new(),
            lex_captured_mutated,
            ctor_inst_methods,
            wired: BTreeSet::new(),
            call_targets: BTreeMap::new(),
            call_unknown: BTreeSet::new(),
            hop_cut_calls: BTreeSet::new(),
            scanned_calls: Vec::new(),
            tainted_calls: BTreeSet::new(),
            load_results: Vec::new(),
            returns_of: HashMap::new(),
            stats: PtaStats::default(),
        }
    }

    pub(super) fn is_base_slice_allowed(&self, callee: FuncId) -> bool {
        self.slice_allow
            .as_ref()
            .is_none_or(|allow| allow.get(callee.index()).copied().unwrap_or(false))
    }

    pub(super) fn try_record_dyn_hop(&mut self, callee: FuncId, next_hop: u8) -> bool {
        if self.slice_allow.is_none() {
            return true;
        }
        let Some(slot) = self.func_hop.get_mut(callee.index()) else {
            return false;
        };
        let updated = (*slot).min(next_hop);
        if updated > self.max_dyn_hop {
            return false;
        }
        *slot = updated;
        true
    }

    /// Returned SSA values of `callee` in deterministic block/inst order,
    /// populated lazily on first `wire_call` into `callee`.
    fn returns_of_func(&mut self, callee: FuncId) -> Vec<ValueId> {
        if let Some(cached) = self.returns_of.get(&callee) {
            return cached.clone();
        }
        let mut returns = Vec::new();
        if let Some(f) = self.module.func(callee) {
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    if let Op::Return { value: Some(v) } = &inst.op {
                        returns.push(*v);
                    }
                }
            }
        }
        self.returns_of.insert(callee, returns.clone());
        returns
    }

    /// Queue fact `o ∈ pts(p)`.
    pub(super) fn add_fact(&mut self, p: Ptr, o: Obj) {
        if self.pts.get(&p).is_some_and(|s| s.contains(&o)) {
            return;
        }
        self.worklist.insert((p, o));
    }

    /// Add subset edge `s → t` (delta half two: a new edge catches up
    /// with everything already in `s`).
    pub(super) fn add_edge(&mut self, s: Ptr, t: Ptr) {
        if s == t {
            return;
        }
        if !self.edges.entry(s).or_default().insert(t) {
            return;
        }
        self.stats.flow_edges += 1;
        let Pta { pts, worklist, .. } = self;
        if let Some(objs) = pts.get(&s) {
            for &o in objs {
                worklist.insert((t, o));
            }
        }
    }

    /// Push one `(handler_id, obj)` firing onto the deferred workstack.
    fn enqueue_fire(&mut self, id: u32, o: Obj) {
        self.fire_stack.push(FireStep::Fire(id, o));
    }

    /// Register a handler and enqueue immediate catch-up firings onto
    /// `self.fire_stack` without re-entering `drain_fires`.
    fn register_deferred(&mut self, base: Ptr, handler: Handler) {
        let id = self.handlers.len() as u32;
        self.handlers.push((base, handler));
        self.handlers_by_base.entry(base).or_default().push(id);
        if let Some(objs) = self.pts.get(&base).cloned() {
            for o in objs.into_iter().rev() {
                self.enqueue_fire(id, o);
            }
        }
    }

    /// Register a statement handler on a base pointer. Handlers
    /// register during activation scans, but an aliased base pointer
    /// may already carry facts — fire on those immediately (the
    /// statement-level delta discipline).
    pub(super) fn register(&mut self, base: Ptr, handler: Handler) {
        self.register_deferred(base, handler);
        self.drain_fires();
    }

    /// Fire one handler on one object (once per pair), driving any bucket
    /// re-arm or call-wiring cascade over `self.fire_stack`.
    fn fire(&mut self, first_id: u32, first_o: Obj) {
        self.enqueue_fire(first_id, first_o);
        self.drain_fires();
    }

    /// Iteratively drain all pending `FireStep`s on `self.fire_stack` without
    /// direct or mutual call-stack recursion.
    pub(super) fn drain_fires(&mut self) {
        while let Some(step) = self.fire_stack.pop() {
            match step {
                FireStep::AddEdge(s, t) => self.add_edge(s, t),
                FireStep::Fire(id, o) => {
                    if !self.fired.insert((id, o)) {
                        continue;
                    }
                    let (_, handler) = self.handlers[id as usize];
                    match handler {
                        Handler::Store { value, slot } => match o.loc() {
                            Some(loc) => {
                                self.fire_stack
                                    .push(FireStep::AddEdge(value, Ptr::Field(loc, slot)));
                                let rearm = self.note_bucket_rearms(loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                            None => match o {
                                Obj::GlobalThis => match slot {
                                    Slot::Named(name) => {
                                        self.fire_stack
                                            .push(FireStep::AddEdge(value, Ptr::Global(name)));
                                    }
                                    Slot::Index | Slot::Dynamic => {
                                        self.fire_stack
                                            .push(FireStep::AddEdge(value, Ptr::GlobalDynamic));
                                    }
                                    Slot::Private(_) => {}
                                },
                                Obj::Unknown | Obj::Site { .. } | Obj::Proto(_) => {}
                            },
                        },
                        Handler::Load { result, read } => match o.loc() {
                            Some(loc) => {
                                let slots: Vec<Slot> = match read {
                                    Read::Named(n) => vec![Slot::Named(n), Slot::Dynamic],
                                    Read::Index => vec![Slot::Index, Slot::Dynamic],
                                    Read::Private(pslot) => vec![Slot::Private(pslot)],
                                    Read::All => {
                                        self.dyn_loads_by_obj
                                            .entry(loc)
                                            .or_default()
                                            .insert((id, o));
                                        self.buckets
                                            .get(&loc)
                                            .map(|b| {
                                                b.iter()
                                                    .copied()
                                                    .filter(|s| !matches!(s, Slot::Private(_)))
                                                    .collect()
                                            })
                                            .unwrap_or_default()
                                    }
                                };
                                for slot in slots {
                                    self.add_edge(Ptr::Field(loc, slot), result);
                                }
                            }
                            None => match o {
                                Obj::GlobalThis => match read {
                                    Read::Named(name) => {
                                        self.add_edge(Ptr::Global(name), result);
                                        self.add_edge(Ptr::GlobalDynamic, result);
                                    }
                                    Read::Index | Read::All => {
                                        self.add_edge(Ptr::GlobalDynamic, result);
                                        self.add_fact(result, Obj::Unknown);
                                    }
                                    Read::Private(_) => {
                                        self.add_fact(result, Obj::Unknown);
                                    }
                                },
                                Obj::Unknown | Obj::Site { .. } | Obj::Proto(_) => {
                                    self.add_fact(result, Obj::Unknown);
                                }
                            },
                        },
                        Handler::Call { call, caller_ctx } => {
                            self.resolve_call(call, caller_ctx, o);
                        }
                        Handler::CopyProps { dst_base, excl_idx } => match o.loc() {
                            Some(src_loc) => {
                                let sub_id = self.handlers.len() as u32;
                                let sub_h = Handler::CopyFromSrc {
                                    src_loc,
                                    excl_idx,
                                    respect_own_methods: false,
                                };
                                self.handlers.push((dst_base, sub_h));
                                self.handlers_by_base
                                    .entry(dst_base)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(dst_objs) = self.pts.get(&dst_base).cloned() {
                                    for dst_o in dst_objs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(sub_id, dst_o));
                                    }
                                }
                            }
                            None => {
                                let sub_id = self.handlers.len() as u32;
                                self.handlers.push((dst_base, Handler::TaintEscape));
                                self.handlers_by_base
                                    .entry(dst_base)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(dst_objs) = self.pts.get(&dst_base).cloned() {
                                    for dst_o in dst_objs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(sub_id, dst_o));
                                    }
                                }
                            }
                        },
                        Handler::CopyFromSrc {
                            src_loc,
                            excl_idx,
                            respect_own_methods,
                        } => {
                            let Some(dst_loc) = o.loc() else {
                                continue;
                            };
                            if src_loc == dst_loc {
                                continue;
                            }
                            self.dyn_loads_by_obj
                                .entry(src_loc)
                                .or_default()
                                .insert((id, o));
                            let src_slots: Vec<Slot> = self
                                .buckets
                                .get(&src_loc)
                                .map(|b| {
                                    b.iter()
                                        .copied()
                                        .filter(|s| !matches!(s, Slot::Private(_)))
                                        .collect()
                                })
                                .unwrap_or_default();
                            for slot in src_slots {
                                if let Slot::Named(sym) = slot
                                    && self
                                        .copy_excluded
                                        .get(excl_idx as usize)
                                        .is_some_and(|ex| ex.contains(&sym))
                                {
                                    continue;
                                }
                                if respect_own_methods
                                    && self.own_class_members.contains(&(dst_loc, slot))
                                {
                                    continue;
                                }
                                self.fire_stack.push(FireStep::AddEdge(
                                    Ptr::Field(src_loc, slot),
                                    Ptr::Field(dst_loc, slot),
                                ));
                                let rearm = self.note_bucket_rearms(dst_loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                        }
                        Handler::InheritClass { sub_site, sub_ctx } => {
                            let sub_cls_loc = ObjLoc::Site(sub_site, sub_ctx);
                            let sub_proto_loc = ObjLoc::ClassProto(sub_site, sub_ctx);
                            let sub_super_proto = ObjLoc::SuperProto(sub_site, sub_ctx);
                            let sub_super_static = ObjLoc::SuperStatic(sub_site, sub_ctx);
                            match o {
                                Obj::Site {
                                    site: base_site,
                                    ctx: base_ctx,
                                    callable,
                                    ..
                                } => {
                                    let base_cls_loc = ObjLoc::Site(base_site, base_ctx);
                                    // 1. Dynamic super constructor target (`super(...)`).
                                    if callable.is_some() {
                                        self.add_fact(Ptr::SuperCtor(sub_site, sub_ctx), o);
                                    }
                                    // 2. Static constructor chain (`Sub.__proto__ = Base`) and
                                    //    static `super.prop` view.
                                    let st_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: base_cls_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(st_id, Obj::Proto(sub_cls_loc)));

                                    let sst_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: base_cls_loc,
                                            excl_idx: 0,
                                            respect_own_methods: false,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(sst_id, Obj::Proto(sub_super_static)));

                                    // 3. Instance prototype chain (`Sub.prototype.__proto__ = Base.prototype`)
                                    //    and instance `super.prop` view.
                                    if self.class_sites.contains(&base_site) {
                                        let base_proto_loc =
                                            ObjLoc::ClassProto(base_site, base_ctx);
                                        let pr_id = self.handlers.len() as u32;
                                        self.handlers.push((
                                            Ptr::SuperCtor(sub_site, sub_ctx),
                                            Handler::CopyFromSrc {
                                                src_loc: base_proto_loc,
                                                excl_idx: 0,
                                                respect_own_methods: true,
                                            },
                                        ));
                                        self.fire_stack
                                            .push(FireStep::Fire(pr_id, Obj::Proto(sub_proto_loc)));

                                        let spr_id = self.handlers.len() as u32;
                                        self.handlers.push((
                                            Ptr::SuperCtor(sub_site, sub_ctx),
                                            Handler::CopyFromSrc {
                                                src_loc: base_proto_loc,
                                                excl_idx: 0,
                                                respect_own_methods: false,
                                            },
                                        ));
                                        self.fire_stack.push(FireStep::Fire(
                                            spr_id,
                                            Obj::Proto(sub_super_proto),
                                        ));
                                    } else {
                                        let ps_list = self.proto_syms.clone();
                                        for psym in ps_list {
                                            let base_proto_ptr =
                                                Ptr::Field(base_cls_loc, Slot::Named(psym));
                                            for target_loc in [sub_proto_loc, sub_super_proto] {
                                                let lp_id = self.handlers.len() as u32;
                                                self.handlers.push((
                                                    base_proto_ptr,
                                                    Handler::LinkProtoFromBase {
                                                        child_loc: target_loc,
                                                    },
                                                ));
                                                self.handlers_by_base
                                                    .entry(base_proto_ptr)
                                                    .or_default()
                                                    .push(lp_id);
                                                if let Some(pobjs) =
                                                    self.pts.get(&base_proto_ptr).cloned()
                                                {
                                                    for po in pobjs.into_iter().rev() {
                                                        self.fire_stack
                                                            .push(FireStep::Fire(lp_id, po));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                Obj::Proto(parent_loc) => {
                                    let pr_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: parent_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(pr_id, Obj::Proto(sub_proto_loc)));
                                }
                                Obj::Unknown | Obj::GlobalThis => {
                                    self.add_fact(Ptr::SuperCtor(sub_site, sub_ctx), Obj::Unknown);
                                    for loc in [
                                        sub_cls_loc,
                                        sub_proto_loc,
                                        sub_super_proto,
                                        sub_super_static,
                                    ] {
                                        self.add_fact(Ptr::Field(loc, Slot::Dynamic), Obj::Unknown);
                                        let rearm = self.note_bucket_rearms(loc, Slot::Dynamic);
                                        for (rid, ro) in rearm.into_iter().rev() {
                                            self.fire_stack.push(FireStep::Fire(rid, ro));
                                        }
                                    }
                                }
                            }
                        }
                        Handler::LinkProtoFromBase { child_loc } => match o.loc() {
                            Some(parent_loc) => {
                                if parent_loc != child_loc {
                                    let cp_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::Field(child_loc, Slot::Dynamic),
                                        Handler::CopyFromSrc {
                                            src_loc: parent_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(cp_id, Obj::Proto(child_loc)));
                                }
                            }
                            None => {
                                if matches!(o, Obj::Unknown | Obj::GlobalThis) {
                                    self.add_fact(
                                        Ptr::Field(child_loc, Slot::Dynamic),
                                        Obj::Unknown,
                                    );
                                    let rearm = self.note_bucket_rearms(child_loc, Slot::Dynamic);
                                    for (rid, ro) in rearm.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(rid, ro));
                                    }
                                }
                            }
                        },
                        Handler::SetObjProto { proto_ptr } => {
                            if let Some(child_loc) = o.loc() {
                                let lp_id = self.handlers.len() as u32;
                                self.handlers
                                    .push((proto_ptr, Handler::LinkProtoFromBase { child_loc }));
                                self.handlers_by_base
                                    .entry(proto_ptr)
                                    .or_default()
                                    .push(lp_id);
                                if let Some(pobjs) = self.pts.get(&proto_ptr).cloned() {
                                    for po in pobjs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(lp_id, po));
                                    }
                                }
                            }
                        }
                        Handler::TaintEscape | Handler::TaintEscapeIndex => {
                            let Some(loc) = o.loc() else {
                                continue;
                            };
                            let slots: &[Slot] = if matches!(handler, Handler::TaintEscapeIndex) {
                                &[Slot::Index]
                            } else {
                                &[Slot::Index, Slot::Dynamic]
                            };
                            for &slot in slots {
                                self.add_fact(Ptr::Field(loc, slot), Obj::Unknown);
                                let rearm = self.note_bucket_rearms(loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Record a bucket on `loc` and return any `(handler_id, obj)` dynamic
    /// reads / copies that need to re-fire (already cleared from `self.fired`).
    fn note_bucket_rearms(&mut self, loc: ObjLoc, slot: Slot) -> Vec<(u32, Obj)> {
        if !self.buckets.entry(loc).or_default().insert(slot) {
            return Vec::new();
        }
        let Some(loads) = self.dyn_loads_by_obj.get(&loc) else {
            return Vec::new();
        };
        let rearm: Vec<(u32, Obj)> = loads.iter().copied().collect();
        for &(id, o) in &rearm {
            self.fired.remove(&(id, o));
        }
        rearm
    }

    /// Note a bucket on `loc` and enqueue re-arms onto `self.fire_stack`
    /// without re-entering `drain_fires`.
    fn note_bucket_deferred(&mut self, loc: ObjLoc, slot: Slot) {
        let rearm = self.note_bucket_rearms(loc, slot);
        for (id, o) in rearm.into_iter().rev() {
            self.enqueue_fire(id, o);
        }
    }

    /// Note a bucket on `loc`; a NEW bucket re-arms the dynamic reads / copies
    /// that already fired on it.
    pub(super) fn note_bucket(&mut self, loc: ObjLoc, slot: Slot) {
        self.note_bucket_deferred(loc, slot);
        self.drain_fires();
    }

    /// Link `child_loc` to `parent_loc` and enqueue the initial firing onto
    /// `self.fire_stack` without re-entering `drain_fires`.
    fn link_proto_locs_deferred(&mut self, child_loc: ObjLoc, parent_loc: ObjLoc) {
        if child_loc == parent_loc {
            return;
        }
        let id = self.handlers.len() as u32;
        self.handlers.push((
            Ptr::Field(child_loc, Slot::Dynamic),
            Handler::CopyFromSrc {
                src_loc: parent_loc,
                excl_idx: 0,
                respect_own_methods: true,
            },
        ));
        self.enqueue_fire(id, Obj::Proto(child_loc));
    }

    /// Link `child_loc` so it inherits public buckets from `parent_loc`
    /// (respecting `own_class_members` on `child_loc`).
    pub(super) fn link_proto_locs(&mut self, child_loc: ObjLoc, parent_loc: ObjLoc) {
        self.link_proto_locs_deferred(child_loc, parent_loc);
        self.drain_fires();
    }

    /// An object reached a callee pointer: `Unknown` marks the site
    /// partial and poisons the result; a callable object wires the
    /// edge; a non-callable object is a TypeError path (no edge, no
    /// unknown — the base trace's discipline).
    fn resolve_call(&mut self, call: InstId, caller_ctx: PackedCtx, o: Obj) {
        match o {
            Obj::Unknown => {
                if self.call_unknown.insert((call, caller_ctx)) {
                    self.stats.call_sites_partial += 1;
                }
                if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                    self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                }
            }
            Obj::Site { site, callable, .. } if callable.is_some() => {
                let Some(body) = callable.to_opt() else {
                    return;
                };
                let is_super = matches!(
                    self.module.inst(call).map(|i| &i.op),
                    Some(Op::Call { kind, .. }) if is_super_call_kind(*kind)
                );
                let caller_fn = self
                    .base
                    .edge_at(call)
                    .map(|e| e.caller)
                    .or_else(|| self.links.inst_func(self.module, call));
                let is_derived_self = is_super
                    && (caller_fn == Some(body)
                        || matches!(
                            self.module.inst(site).map(|i| &i.op),
                            Some(Op::LoadFunction)
                        ));
                if is_derived_self {
                    let super_targets: Vec<FuncId> = self
                        .base
                        .callees_of_call_at(call)
                        .iter()
                        .copied()
                        .filter(|&t| t != body && Some(t) != caller_fn)
                        .collect();
                    if super_targets.is_empty() {
                        // Also consult dynamic `Ptr::SuperCtor(cls_site, cls_ctx)`
                        // when the derived class has a dynamic `heritage` expression!
                        if let Some(cls_acts) = self
                            .ctor_class_activations
                            .get(&body)
                            .cloned()
                            .filter(|s| !s.is_empty())
                        {
                            for (cls_site, cls_ctx) in cls_acts {
                                let sup_ptr = Ptr::SuperCtor(cls_site, cls_ctx);
                                let sub_id = self.handlers.len() as u32;
                                self.handlers
                                    .push((sup_ptr, Handler::Call { call, caller_ctx }));
                                self.handlers_by_base
                                    .entry(sup_ptr)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(sobjs) = self.pts.get(&sup_ptr).cloned() {
                                    for so in sobjs {
                                        if !matches!(
                                            so,
                                            Obj::Site { callable, .. }
                                                if callable.to_opt().is_some_and(|f| f == body || Some(f) == caller_fn)
                                        ) {
                                            self.resolve_call_direct(call, caller_ctx, so);
                                        }
                                    }
                                }
                            }
                        } else {
                            if self.call_unknown.insert((call, caller_ctx)) {
                                self.stats.call_sites_partial += 1;
                            }
                            if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                                self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                            }
                        }
                    } else {
                        let next_hop = caller_fn
                            .and_then(|f| self.func_hop.get(f.index()).copied())
                            .unwrap_or(u8::MAX)
                            .saturating_add(1);
                        for super_ctor in super_targets {
                            if self
                                .call_targets
                                .entry((call, caller_ctx))
                                .or_default()
                                .insert(super_ctor)
                            {
                                self.stats.call_edges_resolved += 1;
                            }
                            if self.try_record_dyn_hop(super_ctor, next_hop) {
                                self.wire_call(call, caller_ctx, super_ctor);
                            } else {
                                self.hop_cut_calls.insert(call);
                            }
                        }
                    }
                    return;
                }
                if self
                    .call_targets
                    .entry((call, caller_ctx))
                    .or_default()
                    .insert(body)
                {
                    self.stats.call_edges_resolved += 1;
                }
                let next_hop = caller_fn
                    .and_then(|f| self.func_hop.get(f.index()).copied())
                    .unwrap_or(u8::MAX)
                    .saturating_add(1);
                if self.try_record_dyn_hop(body, next_hop) {
                    self.wire_call(call, caller_ctx, body);
                } else {
                    self.hop_cut_calls.insert(call);
                }
            }
            Obj::Site { .. } | Obj::Proto(_) | Obj::GlobalThis => {}
        }
    }

    fn resolve_call_direct(&mut self, call: InstId, caller_ctx: PackedCtx, o: Obj) {
        match o {
            Obj::Unknown => {
                if self.call_unknown.insert((call, caller_ctx)) {
                    self.stats.call_sites_partial += 1;
                }
                if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                    self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                }
            }
            Obj::Site { callable, .. } if callable.is_some() => {
                let Some(body) = callable.to_opt() else {
                    return;
                };
                if self
                    .call_targets
                    .entry((call, caller_ctx))
                    .or_default()
                    .insert(body)
                {
                    self.stats.call_edges_resolved += 1;
                }
                let caller_fn = self
                    .base
                    .edge_at(call)
                    .map(|e| e.caller)
                    .or_else(|| self.links.inst_func(self.module, call));
                let next_hop = caller_fn
                    .and_then(|f| self.func_hop.get(f.index()).copied())
                    .unwrap_or(u8::MAX)
                    .saturating_add(1);
                if self.try_record_dyn_hop(body, next_hop) {
                    self.wire_call(call, caller_ctx, body);
                } else {
                    self.hop_cut_calls.insert(call);
                }
            }
            _ => {}
        }
    }

    /// Wire call `call` (in `caller_ctx`) into `callee`: activation +
    /// argument/return edges. Idempotent per internal callee triple.
    pub(super) fn wire_call(&mut self, call: InstId, caller_ctx: PackedCtx, callee: FuncId) {
        let Some(fd) = self.module.func(callee) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if !self.wired.insert((call, caller_ctx, callee)) {
            return;
        }
        let callee_ctx = PackedCtx::some(call);
        self.activate(callee, callee_ctx);
        let Some(Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        }) = self.module.inst(call).map(|i| &i.op)
        else {
            return;
        };
        let (callee_val, this, args, kind) = (*callee_val, *this, args.clone(), *kind);
        let local = |v: ValueId| Ptr::Local(v, caller_ctx);
        let constructed_instance =
            matches!(kind, CallKind::New | CallKind::NewSpread).then_some(Obj::Site {
                site: call,
                ctx: caller_ctx,
                callable: PackedFunc::NONE,
                keyed: true,
            });
        if constructed_instance.is_some() {
            let inst_loc = ObjLoc::Site(call, caller_ctx);
            if let Some(methods) = self.ctor_inst_methods.get(&callee).cloned() {
                for (msym, mfid) in methods {
                    let slot = Slot::Named(msym);
                    self.own_class_members.insert((inst_loc, slot));
                    self.add_fact(
                        Ptr::Field(inst_loc, slot),
                        Obj::Site {
                            site: call,
                            ctx: PackedCtx::NONE,
                            callable: PackedFunc::some(mfid),
                            keyed: false,
                        },
                    );
                    self.note_bucket_deferred(inst_loc, slot);
                }
            }
            // Link constructed instance to `Cls.prototype` (`DefineClass` prototype
            // chain AND legacy constructor function `Fn.prototype` stores!).
            if let Some(cls_acts) = self.ctor_class_activations.get(&callee).cloned() {
                for (cls_site, cls_ctx) in cls_acts {
                    self.link_proto_locs_deferred(inst_loc, ObjLoc::ClassProto(cls_site, cls_ctx));
                }
            }
            let ps_list = self.proto_syms.clone();
            if !ps_list.is_empty()
                && let Some(callee_objs) = self.pts.get(&local(callee_val)).cloned()
            {
                for co in callee_objs {
                    if let Obj::Site {
                        site: fn_site,
                        ctx: fn_ctx,
                        ..
                    } = co
                        && !self.class_sites.contains(&fn_site)
                    {
                        for &psym in &ps_list {
                            self.register_deferred(
                                Ptr::Field(ObjLoc::Site(fn_site, fn_ctx), Slot::Named(psym)),
                                Handler::LinkProtoFromBase {
                                    child_loc: inst_loc,
                                },
                            );
                        }
                    }
                }
            }
        }
        let caller_fn = self
            .base
            .edge_at(call)
            .map(|e| e.caller)
            .or_else(|| self.links.inst_func(self.module, call));
        let inherited_this = (this.is_none()
            && matches!(
                kind,
                CallKind::Super
                    | CallKind::SuperArrow
                    | CallKind::SuperSpread
                    | CallKind::SuperForwardAllArgs
            ))
        .then(|| {
            if kind == CallKind::SuperForwardAllArgs
                && let Some(&explicit_this) = args.first()
            {
                return Some(explicit_this);
            }
            let caller = caller_fn?;
            let c_slots = frame_slots_of(self.module, caller)?;
            let c_this_idx = c_slots.this_index()?;
            self.module.func(caller)?.params.get(c_this_idx).copied()
        })
        .flatten();
        let callee_variadics = self
            .variadic_sinks
            .get(&callee)
            .cloned()
            .unwrap_or_default();
        let callee_params = fd.params.clone();
        match frame_slots_of(self.module, callee) {
            Some(slots) if callee_params.len() >= slots.implicit_count() => {
                if slots.func && !is_super_call_kind(kind) {
                    self.add_edge(local(callee_val), Ptr::Local(callee_params[0], callee_ctx));
                }
                if let Some(this_idx) = slots.this_index() {
                    if let Some(t) = this.or(inherited_this) {
                        self.add_edge(local(t), Ptr::Local(callee_params[this_idx], callee_ctx));
                    } else if let Some(inst_obj) = constructed_instance {
                        self.add_fact(Ptr::Local(callee_params[this_idx], callee_ctx), inst_obj);
                    }
                }
                let formal_base = slots.implicit_count();
                match kind {
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread => {
                        if !args.is_empty() {
                            let spread_ptr = Ptr::SpreadElem(call, caller_ctx);
                            for &p in callee_params.iter().skip(formal_base) {
                                self.add_edge(spread_ptr, Ptr::Local(p, callee_ctx));
                            }
                            for &(var_iid, _) in &callee_variadics {
                                let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                                self.note_bucket_deferred(var_loc, Slot::Index);
                                self.add_edge(spread_ptr, Ptr::Field(var_loc, Slot::Index));
                            }
                        }
                    }
                    CallKind::SuperForwardAllArgs => {
                        let caller_formals: Vec<ValueId> = caller_fn
                            .and_then(|cf| {
                                let cfd = self.module.func(cf)?;
                                let c_base = frame_slots_of(self.module, cf)
                                    .map_or(0, |cs| cs.implicit_count());
                                Some(cfd.params.iter().skip(c_base).copied().collect())
                            })
                            .unwrap_or_default();
                        for (i, &callee_p) in callee_params.iter().skip(formal_base).enumerate() {
                            if let Some(&caller_p) = caller_formals.get(i) {
                                self.add_edge(local(caller_p), Ptr::Local(callee_p, callee_ctx));
                            } else if caller_ctx.is_none() {
                                self.add_fact(Ptr::Local(callee_p, callee_ctx), Obj::Unknown);
                            }
                        }
                        for &(var_iid, skip) in &callee_variadics {
                            let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                            let elem_ptr = Ptr::Field(var_loc, Slot::Index);
                            self.note_bucket_deferred(var_loc, Slot::Index);
                            for &caller_p in caller_formals.iter().skip(skip) {
                                self.add_edge(local(caller_p), elem_ptr);
                            }
                            if caller_ctx.is_none() {
                                self.add_fact(elem_ptr, Obj::Unknown);
                            } else if let Some(cf) = caller_fn
                                && let Some(c_vars) = self.variadic_sinks.get(&cf).cloned()
                            {
                                for (c_var_iid, _) in c_vars {
                                    self.add_edge(
                                        Ptr::Field(
                                            ObjLoc::Site(c_var_iid, caller_ctx),
                                            Slot::Index,
                                        ),
                                        elem_ptr,
                                    );
                                }
                            }
                        }
                    }
                    _ => {
                        for (i, a) in args.iter().enumerate() {
                            if let Some(&p) = callee_params.get(formal_base + i) {
                                self.add_edge(local(*a), Ptr::Local(p, callee_ctx));
                            }
                            // Propagate ALL actual arguments (including excess args
                            // beyond `callee_params.len()`) into `GetUnmappedArgs`
                            // and `CopyRestArgs` (`#94`)!
                            for &(var_iid, skip) in &callee_variadics {
                                if i >= skip {
                                    let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                                    self.note_bucket_deferred(var_loc, Slot::Index);
                                    self.add_edge(local(*a), Ptr::Field(var_loc, Slot::Index));
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                if matches!(
                    kind,
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                ) && !args.is_empty()
                {
                    let spread_ptr = Ptr::SpreadElem(call, caller_ctx);
                    for &p in &callee_params {
                        self.add_edge(spread_ptr, Ptr::Local(p, callee_ctx));
                    }
                    for &(var_iid, _) in &callee_variadics {
                        let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                        self.note_bucket_deferred(var_loc, Slot::Index);
                        self.add_edge(spread_ptr, Ptr::Field(var_loc, Slot::Index));
                    }
                }
                let mut operands = args.clone();
                if let Some(t) = this.or(inherited_this) {
                    operands.push(t);
                }
                for a in operands {
                    for &p in &callee_params {
                        self.add_edge(local(a), Ptr::Local(p, callee_ctx));
                    }
                    for &(var_iid, _) in &callee_variadics {
                        let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                        self.note_bucket_deferred(var_loc, Slot::Index);
                        self.add_edge(local(a), Ptr::Field(var_loc, Slot::Index));
                    }
                }
            }
        }
        // Returns → the call result, in the caller's context.
        if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
            if let Some(inst_obj) = constructed_instance {
                self.add_fact(Ptr::Local(result, caller_ctx), inst_obj);
            }
            if let Some(inh_t) = inherited_this {
                self.add_edge(local(inh_t), Ptr::Local(result, caller_ctx));
            }
            let returns = self.returns_of_func(callee);
            for v in returns {
                self.add_edge(Ptr::Local(v, callee_ctx), Ptr::Local(result, caller_ctx));
            }
        }
    }

    /// Queue an activation for scanning (idempotent; external/bodyless
    /// functions are ignored).
    pub(super) fn activate(&mut self, func: FuncId, ctx: PackedCtx) {
        let Some(fd) = self.module.func(func) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        };
        if self.activated.insert((func, ctx)) {
            self.pending_activations.insert((func, ctx));
        }
    }

    /// Whether a scanned call activation `(call, caller_ctx)` is unresolved,
    /// partial (`resolution_complete == false`), external, or excluded by
    /// root-slicing.
    fn is_call_incomplete(&self, call: InstId, caller_ctx: PackedCtx) -> bool {
        if self.call_unknown.contains(&(call, caller_ctx)) {
            return true;
        }
        let is_super = matches!(
            self.module.inst(call).map(|i| &i.op),
            Some(Op::Call { kind, .. }) if is_super_call_kind(*kind)
        );
        let caller_fn = self
            .base
            .edge_at(call)
            .map(|e| e.caller)
            .or_else(|| self.links.inst_func(self.module, call));
        let pta_set = self.call_targets.get(&(call, caller_ctx));
        let mut all_targets: BTreeSet<FuncId> = pta_set.cloned().unwrap_or_default();
        for &bc in self.base.callees_of_call_at(call) {
            if !(is_super && Some(bc) == caller_fn) {
                all_targets.insert(bc);
            }
        }
        if all_targets.is_empty() {
            return true;
        }
        if pta_set.is_none_or(BTreeSet::is_empty)
            && self
                .base
                .edge_at(call)
                .is_none_or(|e| !e.resolution_complete)
        {
            return true;
        }
        all_targets
            .iter()
            .any(|&callee| !self.wired.contains(&(call, caller_ctx, callee)))
    }

    /// The main loop: activations (in `(FuncId, ctx)` order) and facts
    /// (pop-min) through one deterministic worklist, followed by empty-bucket
    /// and incomplete-call escape post-passes until quiescence or `step_budget`.
    fn pump(&mut self, steps: &mut usize) {
        loop {
            loop {
                if let Some((func, ctx)) = self.pending_activations.pop_first() {
                    self.scanned.insert((func, ctx));
                    self.scan(func, ctx);
                    continue;
                }
                let Some((p, o)) = self.worklist.pop_first() else {
                    break;
                };
                *steps += 1;
                if *steps > self.config.step_budget {
                    self.stats.capped = true;
                    return;
                }
                if !self.pts.entry(p).or_default().insert(o) {
                    continue;
                }
                self.stats.facts += 1;
                let Pta {
                    edges, worklist, ..
                } = self;
                if let Some(targets) = edges.get(&p) {
                    for &t in targets {
                        worklist.insert((t, o));
                    }
                }
                let handler_len = self.handlers_by_base.get(&p).map_or(0, Vec::len);
                for hi in 0..handler_len {
                    let Some(&id) = self.handlers_by_base.get(&p).and_then(|ids| ids.get(hi))
                    else {
                        break;
                    };
                    self.fire(id, o);
                }
            }
            let mut added = false;
            let results = self.load_results.clone();
            for result in results {
                if self.pts.get(&result).is_none_or(|s| s.is_empty()) {
                    self.add_fact(result, Obj::Unknown);
                    added = true;
                }
            }
            if added {
                continue;
            }
            let calls = self.scanned_calls.clone();
            for (call, caller_ctx) in calls {
                if !self.tainted_calls.contains(&(call, caller_ctx))
                    && self.is_call_incomplete(call, caller_ctx)
                {
                    self.tainted_calls.insert((call, caller_ctx));
                    added = true;
                    if let Some(inst) = self.module.inst(call) {
                        if let Some(r) = inst.result {
                            self.add_fact(Ptr::Local(r, caller_ctx), Obj::Unknown);
                        }
                        if let Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } = &inst.op
                        {
                            let (callee, this, kind, args) = (*callee, *this, *kind, args.clone());
                            if let Some((recv, stores_args)) =
                                self.inherited_array_proto_call(callee, this, kind, caller_ctx)
                            {
                                let recv_ptr = Ptr::Local(recv, caller_ctx);
                                self.register(recv_ptr, Handler::TaintEscapeIndex);
                                if stores_args {
                                    if kind == CallKind::Apply {
                                        self.register(
                                            recv_ptr,
                                            Handler::Store {
                                                value: Ptr::SpreadElem(call, caller_ctx),
                                                slot: Slot::Index,
                                            },
                                        );
                                    } else {
                                        for a in args {
                                            self.register(
                                                recv_ptr,
                                                Handler::Store {
                                                    value: Ptr::Local(a, caller_ctx),
                                                    slot: Slot::Index,
                                                },
                                            );
                                        }
                                    }
                                }
                            } else {
                                let mut escape_vals = args;
                                if let Some(t) = this {
                                    escape_vals.push(t);
                                }
                                for ev in escape_vals {
                                    self.register(Ptr::Local(ev, caller_ctx), Handler::TaintEscape);
                                }
                            }
                        }
                    }
                }
            }
            if !added {
                break;
            }
        }
    }

    /// Detect an inherited non-callback `Array.prototype` method call on a
    /// proven `AllocArray` receiver with no own/dynamic shadow on that method,
    /// returning `(recv, stores_args)`.
    fn inherited_array_proto_call(
        &self,
        callee: ValueId,
        this: Option<ValueId>,
        kind: CallKind,
        caller_ctx: PackedCtx,
    ) -> Option<(ValueId, bool)> {
        if !matches!(kind, CallKind::Direct | CallKind::Dynamic | CallKind::Apply) {
            return None;
        }
        let callee_root = crate::dataflow::heap::peel_movs(self.module, callee);
        let ValueDef::Inst(load_iid) = self.module.value(callee_root)?.def else {
            return None;
        };
        let Op::LoadProp {
            object: recv,
            name: method_sym,
        } = &self.module.inst(load_iid)?.op
        else {
            return None;
        };
        if !this.is_some_and(|t| {
            crate::dataflow::heap::peel_movs(self.module, t)
                == crate::dataflow::heap::peel_movs(self.module, *recv)
        }) {
            return None;
        }
        let stores_args = match self.module.sym.resolve(*method_sym)? {
            "push" | "unshift" | "splice" | "fill" => true,
            "pop" | "shift" | "slice" | "concat" | "copyWithin" | "reverse" | "join"
            | "indexOf" | "lastIndexOf" | "includes" | "at" => false,
            _ => return None,
        };
        let objs = self.pts.get(&Ptr::Local(*recv, caller_ctx))?;
        (!objs.is_empty()
            && objs.iter().all(|o| {
                matches!(
                    o,
                    Obj::Site { site, ctx, .. }
                        if matches!(
                            self.module.inst(*site).map(|i| &i.op),
                            Some(Op::AllocArray { .. })
                        ) && !self
                            .buckets
                            .get(&ObjLoc::Site(*site, *ctx))
                            .is_some_and(|b| {
                                b.contains(&Slot::Named(*method_sym)) || b.contains(&Slot::Dynamic)
                            })
                )
            }))
        .then_some((*recv, stores_args))
    }

    pub(super) fn run(&mut self, roots: Option<&[FuncId]>, steps: &mut usize) {
        match roots {
            None => {
                for fi in 0..self.module.functions.len() {
                    self.activate(FuncId::new(fi as u32), PackedCtx::NONE);
                }
            }
            Some(root_funcs) => {
                for &func in root_funcs {
                    self.activate(func, PackedCtx::NONE);
                }
            }
        }
        self.pump(steps);
    }
}
