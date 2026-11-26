//! Bounded class, prototype, object-literal, field-provenance, and lexical-slot
//! call-resolution index (`Issue #34` Step 1B).
//!
//! Complements `CallGraph`'s backward SSA def-chain trace when a callee flows
//! through class method tables (`this.m()`, `super.m()`, `super()`, `Cls.m()`),
//! prototype/static property attachments, object-literal methods, bounded
//! constructor/method field provenance (`this.service.doWork()`,
//! `Repo.getInstance().fetch()`), lexical-environment slots (ArkTS `stlexvar`
//! class self-bindings and arrow-captured `this`), or cross-module ES imports.
//!
//! ## Engineering invariants
//! - **Zero input-depth recursion**: every value, CFG, capture, and class
//!   hierarchy traversal uses an explicit heap workstack with visited guards
//!   and hard step caps (`<= 64`).
//! - **Bit-exact determinism (`N20`)**: `ClassDefId`s are assigned in arena
//!   `(FuncId, BlockId, InstId)` scan order; provenance sets and resolved
//!   target lists use `BTreeSet` ordering; `HashMap`s are lookup-only and never
//!   iterated to emit output order.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use abcd_ir::cfg::ExceptionHandlerMap;
use abcd_ir::op::{LexEnvKind, MemberAttrs, ModuleVarKind, SuperKey};
use abcd_ir::ty::{StaticTy, Ty};
use abcd_ir::{
    BlockId, CallKind, ClassId, Const, ConstId, FuncId, FunctionKind, InstId, Modifiers, Module,
    Op, SourceLang, Sym, ValueDef, ValueId,
};

use crate::control::{augmented_succs_with_map, awaited_values_for_resume};
use crate::dataflow::heap::peel_movs;
use crate::frame::frame_slots_of;
use crate::module_link::{ModuleLinkTable, ModuleSlotRef};

/// Maximum worklist/hierarchy steps per provenance or ancestor query.
const MAX_STEPS: usize = 64;

/// Maximum abstract provenance items retained in any `BTreeSet<Prov>`.
const MAX_PROV_SET: usize = 16;

/// Maximum lexical-environment nesting depth tracked per instruction.
const MAX_ENV_DEPTH: usize = 8;

/// Maximum alternative `NewLexEnv` sites retained at a single lexical level.
const MAX_ENV_SITES_PER_SLOT: usize = 4;

/// Number of closure-capture propagation rounds for the fast lexical-slot index.
const LEX_CAPTURE_ROUNDS: usize = 2;

/// Number of monotone field/return provenance rounds.
const PROV_ROUNDS: usize = 3;

/// Deterministic identifier of an indexed `DefineClass` / `DefineSendableClass` site.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ClassDefId(u32);

impl ClassDefId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Bounded value-provenance fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Prov {
    /// Class constructor / static receiver object.
    ClassObj(ClassDefId),
    /// Constructed instance of a class.
    ClassInst(ClassDefId),
    /// Object literal allocated at `InstId` (`Op::AllocObject`).
    ObjLit(InstId),
    /// Direct callable function body.
    Callable(FuncId),
    /// ES module namespace object for internal record `ClassId`.
    ModuleNs(ClassId),
}

/// Indexed class metadata from `Op::DefineClass` / `Op::DefineSendableClass`,
/// static `ClassData` records, and same-function prototype/static attachments.
#[derive(Clone, Debug)]
struct ClassDef {
    ctor: Option<FuncId>,
    enclosing_func: Option<FuncId>,
    static_record: Option<ClassId>,
    heritage: Option<ValueId>,
    is_sendable: bool,
    super_classes: Vec<ClassDefId>,
    sub_classes: Vec<ClassDefId>,
    instance_methods: BTreeMap<Sym, Vec<FuncId>>,
    static_methods: BTreeMap<Sym, Vec<FuncId>>,
    instance_getters: BTreeMap<Sym, Vec<FuncId>>,
    static_getters: BTreeMap<Sym, Vec<FuncId>>,
}

/// Indexed property entries on an `Op::AllocObject` literal.
#[derive(Clone, Debug, Default)]
struct ObjLitProp {
    /// Methods declared directly in `Const::ObjectLiteral`.
    methods: Vec<FuncId>,
    /// Values stored via `StoreProp` / `StoreOwnPropName` / `DefineMethod`.
    stores: Vec<(FuncId, ValueId)>,
}

type EnvStack = Vec<Vec<InstId>>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct DualEnvStack {
    plain: EnvStack,
    sendable: EnvStack,
}

/// Whole-module class hierarchy, lexical-slot, and bounded field/return index.
pub(crate) struct ClassHierarchyIndex<'m> {
    module: &'m Module,
    links: &'m ModuleLinkTable,
    classes: Vec<ClassDef>,
    class_by_inst: Vec<Option<ClassDefId>>,
    record_to_class_def: Vec<Option<ClassDefId>>,
    ctor_to_classes: Vec<Vec<ClassDefId>>,
    method_owner: Vec<Option<(ClassDefId, bool)>>,
    super_owner: Vec<Option<(ClassDefId, bool)>>,
    this_param_of: Vec<Option<ValueId>>,
    func_obj_param_of: Vec<Option<ValueId>>,
    enclosing_sendable_class: Vec<Option<ClassDefId>>,
    obj_lits: BTreeMap<(InstId, Sym), ObjLitProp>,
    get_lex_sites: HashMap<InstId, Vec<InstId>>,
    lex_stores: HashMap<(InstId, u16), Vec<(FuncId, ValueId)>>,
    instance_fields: HashMap<(ClassDefId, Sym), BTreeSet<Prov>>,
    static_fields: HashMap<(ClassDefId, Sym), BTreeSet<Prov>>,
    func_returns: Vec<BTreeSet<Prov>>,
}

enum LexAccessKind {
    Put {
        func: FuncId,
        level: u16,
        slot: u16,
        value: ValueId,
        sendable: bool,
    },
    Get {
        level: u16,
        sendable: bool,
    },
}

enum FrameCont {
    Root,
    LoadProp { name: Sym },
    Call { kind: CallKind },
}

struct EvalFrame {
    origin: Option<(FuncId, ValueId)>,
    work: Vec<(FuncId, ValueId)>,
    visited: HashSet<(FuncId, ValueId)>,
    out: BTreeSet<Prov>,
    cont: FrameCont,
}

impl<'m> ClassHierarchyIndex<'m> {
    /// Construct the class/prototype/field/lexical-slot index over `module`.
    pub(crate) fn build(module: &'m Module, links: &'m ModuleLinkTable) -> Self {
        let num_funcs = module.functions.len();
        let num_insts = module.insts.len();

        let mut this_param_of = vec![None; num_funcs];
        let mut func_obj_param_of = vec![None; num_funcs];
        for fi in 0..num_funcs {
            let fid = FuncId::new(fi as u32);
            if let (Some(fd), Some(slots)) = (module.func(fid), frame_slots_of(module, fid)) {
                if let Some(idx) = slots.this_index() {
                    this_param_of[fi] = fd.params.get(idx).copied();
                }
                if slots.func {
                    func_obj_param_of[fi] = fd.params.first().copied();
                }
            }
        }

        let mut classes: Vec<ClassDef> = Vec::new();
        let mut class_by_inst: Vec<Option<ClassDefId>> = vec![None; num_insts];
        let mut record_to_class_def: Vec<Option<ClassDefId>> = vec![None; module.classes.len()];
        let mut ctor_to_classes: Vec<Vec<ClassDefId>> = vec![Vec::new(); num_funcs];
        let mut method_owner: Vec<Option<(ClassDefId, bool)>> = vec![None; num_funcs];
        let mut enclosing_sendable_class: Vec<Option<ClassDefId>> = vec![None; num_funcs];
        let mut obj_lits: BTreeMap<(InstId, Sym), ObjLitProp> = BTreeMap::new();

        // Index static `ClassData` records (`super_class`, `interfaces`, static ArkTS classes).
        let referenced_static = collect_referenced_static_classes(module);
        for (ci, cls_data) in module.classes.iter().enumerate() {
            let rcid = ClassId::new(ci as u32);
            if should_index_static_class(module, cls_data, referenced_static[ci]) {
                let cdef_id = index_static_class_data(
                    module,
                    rcid,
                    cls_data,
                    &mut classes,
                    &mut ctor_to_classes,
                    &mut method_owner,
                );
                record_to_class_def[ci] = Some(cdef_id);
            }
        }

        // Collected during the single Pass-1 scan for Pass 1B, 1C, and Pass 2.
        let mut prop_stores: Vec<(FuncId, ValueId, Sym, ValueId)> = Vec::new();
        let mut define_methods: Vec<(FuncId, ValueId, Sym, ValueId)> = Vec::new();
        let mut return_values: Vec<(FuncId, ValueId)> = Vec::new();
        let mut capture_sites: Vec<(InstId, FuncId)> = Vec::new();
        let mut child_funcs_of: Vec<Vec<FuncId>> = vec![Vec::new(); num_funcs];
        let mut has_env_mut_ops = vec![false; num_funcs];
        let mut is_lex_or_cap = vec![false; num_insts];
        let mut func_lex_or_cap_insts: Vec<Vec<InstId>> = vec![Vec::new(); num_funcs];
        let mut lex_accesses: Vec<(InstId, LexAccessKind)> = Vec::new();

        // ── Pass 1A: Linear `(FuncId, BlockId, InstId)` scan ─────────────
        for (fi, f) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let mut mark_lex_or_cap = false;
                    match &inst.op {
                        Op::DefineClass(cls) => {
                            mark_lex_or_cap = true;
                            let cid = index_class_def(
                                module,
                                fid,
                                cls.ctor,
                                cls.heritage,
                                cls.members,
                                &cls.member_attrs,
                                false,
                                &mut classes,
                                &mut ctor_to_classes,
                                &mut method_owner,
                                &mut enclosing_sendable_class,
                                &mut capture_sites,
                                &mut child_funcs_of[fi],
                                iid,
                            );
                            if let Some(slot) = class_by_inst.get_mut(iid.index()) {
                                *slot = Some(cid);
                            }
                        }
                        Op::DefineSendableClass(cls) => {
                            mark_lex_or_cap = true;
                            let cid = index_class_def(
                                module,
                                fid,
                                cls.ctor,
                                cls.heritage,
                                cls.members,
                                &cls.member_attrs,
                                true,
                                &mut classes,
                                &mut ctor_to_classes,
                                &mut method_owner,
                                &mut enclosing_sendable_class,
                                &mut capture_sites,
                                &mut child_funcs_of[fi],
                                iid,
                            );
                            if let Some(slot) = class_by_inst.get_mut(iid.index()) {
                                *slot = Some(cid);
                            }
                        }
                        Op::AllocObject { shape } => {
                            if let Some(Const::ObjectLiteral { keys, values }) =
                                module.consts.get(*shape)
                            {
                                for (&k_cid, &v_cid) in keys.iter().zip(values.iter()) {
                                    if let (
                                        Some(Const::String(k_sym)),
                                        Some(Const::MethodRef { func: mfid, .. }),
                                    ) = (module.consts.get(k_cid), module.consts.get(v_cid))
                                    {
                                        obj_lits
                                            .entry((iid, *k_sym))
                                            .or_default()
                                            .methods
                                            .push(*mfid);
                                    }
                                }
                            }
                        }
                        Op::StoreProp {
                            object,
                            name,
                            value,
                        }
                        | Op::StoreOwnPropName {
                            object,
                            name,
                            value,
                            ..
                        } => {
                            prop_stores.push((fid, *object, *name, *value));
                        }
                        Op::DefineMethod {
                            object, name, func, ..
                        } => {
                            define_methods.push((fid, *object, *name, *func));
                            if let Some(body) = peel_closure_func(module, *func) {
                                mark_lex_or_cap = true;
                                capture_sites.push((iid, body));
                                push_unique_func(&mut child_funcs_of[fi], body);
                            }
                        }
                        Op::DefineGetterSetterByValue { getter, setter, .. } => {
                            for &inner in [getter, setter] {
                                if let Some(body) = peel_closure_func(module, inner) {
                                    mark_lex_or_cap = true;
                                    capture_sites.push((iid, body));
                                    push_unique_func(&mut child_funcs_of[fi], body);
                                }
                            }
                        }
                        Op::DefineFunc { body, .. } => {
                            mark_lex_or_cap = true;
                            capture_sites.push((iid, *body));
                            push_unique_func(&mut child_funcs_of[fi], *body);
                        }
                        Op::AllocClosure { func }
                        | Op::CreateGenerator { func }
                        | Op::CreateAsyncGenerator { func } => {
                            if let Some(body) = peel_closure_func(module, *func) {
                                mark_lex_or_cap = true;
                                capture_sites.push((iid, body));
                                push_unique_func(&mut child_funcs_of[fi], body);
                            }
                        }
                        Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } | Op::PopLexEnv => {
                            has_env_mut_ops[fi] = true;
                        }
                        Op::PutLexVar {
                            level,
                            slot,
                            value,
                            kind,
                        } if *kind != LexEnvKind::Patch => {
                            mark_lex_or_cap = true;
                            lex_accesses.push((
                                iid,
                                LexAccessKind::Put {
                                    func: fid,
                                    level: *level,
                                    slot: *slot,
                                    value: *value,
                                    sendable: *kind == LexEnvKind::Sendable,
                                },
                            ));
                        }
                        Op::GetLexVar { level, kind, .. } if *kind != LexEnvKind::Patch => {
                            mark_lex_or_cap = true;
                            lex_accesses.push((
                                iid,
                                LexAccessKind::Get {
                                    level: *level,
                                    sendable: *kind == LexEnvKind::Sendable,
                                },
                            ));
                        }
                        Op::Return { value: Some(v) } | Op::AsyncResolve { value: v, .. } => {
                            return_values.push((fid, *v));
                        }
                        _ => {}
                    }
                    if mark_lex_or_cap {
                        if let Some(slot) = is_lex_or_cap.get_mut(iid.index()) {
                            *slot = true;
                        }
                        func_lex_or_cap_insts[fi].push(iid);
                    }
                }
            }
        }

        // ── Pass 1B: Prototype/static attachments & object-literal stores ─
        for &(func, object, name, val_or_func) in prop_stores.iter().chain(define_methods.iter()) {
            let root_obj = peel_movs(module, object);
            let Some(ValueDef::Inst(obj_iid)) = module.value(root_obj).map(|v| v.def) else {
                continue;
            };
            if let Some(cid) = class_by_inst.get(obj_iid.index()).copied().flatten() {
                if let Some(mfid) = peel_closure_func(module, val_or_func) {
                    attach_class_member(
                        module,
                        &mut classes[cid.index()],
                        cid,
                        name,
                        mfid,
                        true,
                        &mut method_owner,
                        &mut enclosing_sendable_class,
                    );
                }
                continue;
            }
            match module.inst(obj_iid).map(|i| &i.op) {
                Some(Op::LoadProp {
                    object: proto_base,
                    name: prop_name,
                }) if module.sym.resolve(*prop_name) == Some("prototype") => {
                    let cls_root = peel_movs(module, *proto_base);
                    if let Some(ValueDef::Inst(cls_iid)) = module.value(cls_root).map(|v| v.def)
                        && let Some(cid) = class_by_inst.get(cls_iid.index()).copied().flatten()
                        && let Some(mfid) = peel_closure_func(module, val_or_func)
                    {
                        attach_class_member(
                            module,
                            &mut classes[cid.index()],
                            cid,
                            name,
                            mfid,
                            false,
                            &mut method_owner,
                            &mut enclosing_sendable_class,
                        );
                    }
                }
                Some(Op::AllocObject { .. }) => {
                    obj_lits
                        .entry((obj_iid, name))
                        .or_default()
                        .stores
                        .push((func, val_or_func));
                }
                _ => {}
            }
        }

        for cls in &mut classes {
            sort_dedup_method_map(&mut cls.instance_methods);
            sort_dedup_method_map(&mut cls.static_methods);
            sort_dedup_method_map(&mut cls.instance_getters);
            sort_dedup_method_map(&mut cls.static_getters);
        }
        for prop in obj_lits.values_mut() {
            prop.methods.sort();
            prop.methods.dedup();
        }

        // Propagate `enclosing_sendable_class` and arrow `super_owner` with explicit stacks.
        let mut sendable_wl: Vec<FuncId> = enclosing_sendable_class
            .iter()
            .enumerate()
            .filter_map(|(fi, s)| s.map(|_| FuncId::new(fi as u32)))
            .collect();
        while let Some(parent) = sendable_wl.pop() {
            let Some(scid) = enclosing_sendable_class
                .get(parent.index())
                .copied()
                .flatten()
            else {
                continue;
            };
            if let Some(children) = child_funcs_of.get(parent.index()) {
                for &child in children {
                    if let Some(slot) = enclosing_sendable_class.get_mut(child.index())
                        && slot.is_none()
                    {
                        *slot = Some(scid);
                        sendable_wl.push(child);
                    }
                }
            }
        }

        let mut super_owner = method_owner.clone();
        let mut super_wl: Vec<FuncId> = super_owner
            .iter()
            .enumerate()
            .filter_map(|(fi, s)| s.map(|_| FuncId::new(fi as u32)))
            .collect();
        while let Some(parent) = super_wl.pop() {
            let Some(owner) = super_owner.get(parent.index()).copied().flatten() else {
                continue;
            };
            if let Some(children) = child_funcs_of.get(parent.index()) {
                for &child in children {
                    let is_arrow = module.func(child).is_some_and(|fd| {
                        matches!(fd.kind, FunctionKind::Arrow | FunctionKind::AsyncArrow)
                    });
                    if is_arrow
                        && let Some(slot) = super_owner.get_mut(child.index())
                        && slot.is_none()
                    {
                        *slot = Some(owner);
                        super_wl.push(child);
                    }
                }
            }
        }

        // ── Pass 1C: Fast lexical-slot index (monotonic RPO worklist + 2 capture rounds) ────
        let mut rpo_by_func: Vec<Option<(Vec<BlockId>, ExceptionHandlerMap)>> =
            Vec::with_capacity(num_funcs);
        for (fi, &has_mut) in has_env_mut_ops.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if has_mut && let Some(exc_map) = ExceptionHandlerMap::build(module, fid) {
                let rpo = compute_augmented_rpo(module, fid, &exc_map);
                rpo_by_func.push(Some((rpo, exc_map)));
            } else {
                rpo_by_func.push(None);
            }
        }

        let mut captured_entry: Vec<DualEnvStack> = vec![DualEnvStack::default(); num_funcs];
        let mut stack_at: HashMap<InstId, DualEnvStack> = HashMap::new();

        for (fi, rpo_entry) in rpo_by_func.iter().enumerate() {
            if let Some((rpo, exc_map)) = rpo_entry {
                compute_func_env_stacks(
                    module,
                    rpo,
                    exc_map,
                    &captured_entry[fi],
                    &is_lex_or_cap,
                    &mut stack_at,
                );
            }
        }

        for _ in 0..LEX_CAPTURE_ROUNDS {
            let mut dirty = vec![false; num_funcs];
            for &(cap_iid, child_fn) in &capture_sites {
                if let Some(cap_stack) = stack_at.get(&cap_iid).cloned()
                    && let Some(dst) = captured_entry.get_mut(child_fn.index())
                    && merge_dual_env_stacks(dst, &cap_stack)
                    && let Some(d) = dirty.get_mut(child_fn.index())
                {
                    *d = true;
                }
            }
            if !dirty.iter().any(|&d| d) {
                break;
            }
            for (fi, &is_dirty) in dirty.iter().enumerate() {
                if !is_dirty {
                    continue;
                }
                if let Some((rpo, exc_map)) = &rpo_by_func[fi] {
                    compute_func_env_stacks(
                        module,
                        rpo,
                        exc_map,
                        &captured_entry[fi],
                        &is_lex_or_cap,
                        &mut stack_at,
                    );
                } else {
                    let entry_stack = &captured_entry[fi];
                    for &iid in &func_lex_or_cap_insts[fi] {
                        match stack_at.get_mut(&iid) {
                            Some(existing) => {
                                merge_dual_env_stacks(existing, entry_stack);
                            }
                            None => {
                                stack_at.insert(iid, entry_stack.clone());
                            }
                        }
                    }
                }
            }
        }

        let mut get_lex_sites: HashMap<InstId, Vec<InstId>> = HashMap::new();
        let mut lex_stores: HashMap<(InstId, u16), Vec<(FuncId, ValueId)>> = HashMap::new();
        for (iid, access) in lex_accesses {
            let Some(dual) = stack_at.get(&iid) else {
                continue;
            };
            match access {
                LexAccessKind::Put {
                    func,
                    level,
                    slot,
                    value,
                    sendable,
                } => {
                    let stack = if sendable {
                        &dual.sendable
                    } else {
                        &dual.plain
                    };
                    let lvl = level as usize;
                    if lvl < stack.len() {
                        for &env_site in &stack[stack.len() - 1 - lvl] {
                            lex_stores
                                .entry((env_site, slot))
                                .or_default()
                                .push((func, value));
                        }
                    }
                }
                LexAccessKind::Get { level, sendable } => {
                    let stack = if sendable {
                        &dual.sendable
                    } else {
                        &dual.plain
                    };
                    let lvl = level as usize;
                    if lvl < stack.len() {
                        let sites = &stack[stack.len() - 1 - lvl];
                        if !sites.is_empty() {
                            get_lex_sites.insert(iid, sites.clone());
                        }
                    }
                }
            }
        }

        let mut index = ClassHierarchyIndex {
            module,
            links,
            classes,
            class_by_inst,
            record_to_class_def,
            ctor_to_classes,
            method_owner,
            super_owner,
            this_param_of,
            func_obj_param_of,
            enclosing_sendable_class,
            obj_lits,
            get_lex_sites,
            lex_stores,
            instance_fields: HashMap::new(),
            static_fields: HashMap::new(),
            func_returns: vec![BTreeSet::new(); num_funcs],
        };

        // ── Pass 2A: Resolve `super_classes` & `sub_classes` ─────────────
        for ci in 0..index.classes.len() {
            let self_cid = ClassDefId(ci as u32);
            let mut supers = BTreeSet::new();
            if let Some(rcid) = index.classes[ci].static_record
                && let Some(cls_data) = module.class(rcid)
            {
                if let Some(sup_rcid) = cls_data.super_class
                    && let Some(sc) = index
                        .record_to_class_def
                        .get(sup_rcid.index())
                        .copied()
                        .flatten()
                    && sc != self_cid
                {
                    supers.insert(sc);
                }
                for &iface_rcid in &cls_data.interfaces {
                    if let Some(ic) = index
                        .record_to_class_def
                        .get(iface_rcid.index())
                        .copied()
                        .flatten()
                        && ic != self_cid
                    {
                        supers.insert(ic);
                    }
                }
            }
            if let (Some(enclosing), Some(h)) =
                (index.classes[ci].enclosing_func, index.classes[ci].heritage)
            {
                for p in index.infer_prov(enclosing, h) {
                    if let Prov::ClassObj(sc) = p
                        && sc != self_cid
                    {
                        supers.insert(sc);
                    }
                }
            }
            index.classes[ci].super_classes = supers.into_iter().collect();
        }
        let mut subs_by_class = vec![BTreeSet::new(); index.classes.len()];
        for (ci, cls) in index.classes.iter().enumerate() {
            let sub_id = ClassDefId(ci as u32);
            for &sup_id in &cls.super_classes {
                if let Some(set) = subs_by_class.get_mut(sup_id.index()) {
                    set.insert(sub_id);
                }
            }
        }
        for (ci, subs) in subs_by_class.into_iter().enumerate() {
            index.classes[ci].sub_classes = subs.into_iter().collect();
        }

        // ── Pass 2B: 3 bounded monotone rounds of field/return provenance ─
        for _ in 0..PROV_ROUNDS {
            let mut changed = false;
            for &(func, object, name, value) in &prop_stores {
                let obj_provs = index.infer_prov(func, object);
                if !obj_provs
                    .iter()
                    .any(|p| matches!(p, Prov::ClassInst(_) | Prov::ClassObj(_)))
                {
                    continue;
                }
                let val_provs = index.infer_prov(func, value);
                if val_provs.is_empty() {
                    continue;
                }
                for p in obj_provs {
                    match p {
                        Prov::ClassInst(c) => {
                            let set = index.instance_fields.entry((c, name)).or_default();
                            changed |= union_prov_set(set, &val_provs);
                        }
                        Prov::ClassObj(c) => {
                            let set = index.static_fields.entry((c, name)).or_default();
                            changed |= union_prov_set(set, &val_provs);
                        }
                        _ => {}
                    }
                }
            }
            for &(func, ret_val) in &return_values {
                let ret_provs = index.infer_prov(func, ret_val);
                if ret_provs.is_empty() {
                    continue;
                }
                if let Some(set) = index.func_returns.get_mut(func.index()) {
                    changed |= union_prov_set(set, &ret_provs);
                }
            }
            if !changed {
                break;
            }
        }

        index
    }

    /// Resolve a call site that the base SSA def-chain trace could not resolve.
    /// Returns a sorted, deduplicated list of target [`FuncId`]s.
    pub(crate) fn resolve_call(
        &self,
        caller: FuncId,
        callee: ValueId,
        kind: CallKind,
    ) -> Vec<FuncId> {
        let mut targets = BTreeSet::new();
        match kind {
            CallKind::Super
            | CallKind::SuperArrow
            | CallKind::SuperSpread
            | CallKind::SuperForwardAllArgs => {
                let owned_ctors = self
                    .ctor_to_classes
                    .get(caller.index())
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                if !owned_ctors.is_empty() {
                    for &cid in owned_ctors {
                        if let Some(cls) = self.classes.get(cid.index()) {
                            for &sc in &cls.super_classes {
                                if let Some(ctor) =
                                    self.classes.get(sc.index()).and_then(|scls| scls.ctor)
                                {
                                    targets.insert(ctor);
                                }
                            }
                        }
                    }
                } else {
                    for p in self.infer_prov(caller, callee) {
                        match p {
                            Prov::Callable(f) if f != caller => {
                                let f_ctors = self
                                    .ctor_to_classes
                                    .get(f.index())
                                    .map(Vec::as_slice)
                                    .unwrap_or(&[]);
                                if !f_ctors.is_empty() {
                                    for &cid in f_ctors {
                                        if let Some(cls) = self.classes.get(cid.index()) {
                                            for &sc in &cls.super_classes {
                                                if let Some(ctor) = self
                                                    .classes
                                                    .get(sc.index())
                                                    .and_then(|scls| scls.ctor)
                                                    && ctor != caller
                                                {
                                                    targets.insert(ctor);
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    targets.insert(f);
                                }
                            }
                            Prov::ClassObj(sc) => {
                                let caller_cls = self
                                    .super_owner
                                    .get(caller.index())
                                    .copied()
                                    .flatten()
                                    .map(|(c, _)| c);
                                if caller_cls == Some(sc) {
                                    if let Some(cls) = self.classes.get(sc.index()) {
                                        for &sup in &cls.super_classes {
                                            if let Some(ctor) =
                                                self.classes.get(sup.index()).and_then(|s| s.ctor)
                                                && ctor != caller
                                            {
                                                targets.insert(ctor);
                                            }
                                        }
                                    }
                                } else if let Some(ctor) =
                                    self.classes.get(sc.index()).and_then(|scls| scls.ctor)
                                    && ctor != caller
                                {
                                    targets.insert(ctor);
                                }
                            }
                            _ => {}
                        }
                    }
                    if targets.is_empty()
                        && let Some((cid, _)) =
                            self.super_owner.get(caller.index()).copied().flatten()
                        && let Some(cls) = self.classes.get(cid.index())
                    {
                        for &sc in &cls.super_classes {
                            if let Some(ctor) =
                                self.classes.get(sc.index()).and_then(|scls| scls.ctor)
                                && ctor != caller
                            {
                                targets.insert(ctor);
                            }
                        }
                    }
                }
            }
            CallKind::New | CallKind::NewSpread => {
                for p in self.infer_prov(caller, callee) {
                    match p {
                        Prov::ClassObj(c) => {
                            if let Some(ctor) = self.classes.get(c.index()).and_then(|cls| cls.ctor)
                            {
                                targets.insert(ctor);
                            }
                        }
                        Prov::Callable(f) => {
                            targets.insert(f);
                        }
                        _ => {}
                    }
                }
            }
            _ => {
                for p in self.infer_prov(caller, callee) {
                    if let Prov::Callable(f) = p {
                        targets.insert(f);
                    }
                }
            }
        }
        targets.into_iter().collect()
    }

    /// Iterative bounded provenance inference (`<= 64` pops, zero call-stack recursion).
    pub(crate) fn infer_prov(&self, root_func: FuncId, root_val: ValueId) -> BTreeSet<Prov> {
        let mut frames = vec![EvalFrame {
            origin: Some((root_func, root_val)),
            work: vec![(root_func, root_val)],
            visited: HashSet::new(),
            out: BTreeSet::new(),
            cont: FrameCont::Root,
        }];
        let mut memo: HashMap<(FuncId, ValueId), BTreeSet<Prov>> = HashMap::new();
        let mut steps = 0usize;

        while let Some(top_idx) = frames.len().checked_sub(1) {
            if let Some((func, val)) = frames[top_idx].work.pop() {
                if !frames[top_idx].visited.insert((func, val)) {
                    continue;
                }
                if frames[top_idx].out.len() >= MAX_PROV_SET || steps >= MAX_STEPS {
                    frames[top_idx].work.clear();
                    continue;
                }
                if let Some(cached) = memo.get(&(func, val)) {
                    union_prov_set(&mut frames[top_idx].out, cached);
                    continue;
                }
                steps += 1;

                let Some(v) = self.module.value(val) else {
                    continue;
                };
                if let Ty::Static(StaticTy::Reference(rcid)) = &v.ty
                    && let Some(cid) = self
                        .record_to_class_def
                        .get(rcid.index())
                        .copied()
                        .flatten()
                {
                    insert_prov(&mut frames[top_idx].out, Prov::ClassInst(cid));
                }
                match v.def {
                    ValueDef::Param(_) => {
                        if self.this_param_of.get(func.index()).copied().flatten() == Some(val) {
                            if let Some((cid, is_static)) =
                                self.method_owner.get(func.index()).copied().flatten()
                            {
                                let p = if is_static {
                                    Prov::ClassObj(cid)
                                } else {
                                    Prov::ClassInst(cid)
                                };
                                insert_prov(&mut frames[top_idx].out, p);
                            }
                        } else if self.func_obj_param_of.get(func.index()).copied().flatten()
                            == Some(val)
                        {
                            insert_prov(&mut frames[top_idx].out, Prov::Callable(func));
                        }
                    }
                    ValueDef::ExceptionParam(_) => {}
                    ValueDef::Const(c) => {
                        if let Some(Const::MethodRef { func: f, .. }) = self.module.consts.get(c) {
                            insert_prov(&mut frames[top_idx].out, Prov::Callable(*f));
                        }
                    }
                    ValueDef::Inst(iid) => {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::LoadFunction => {
                                insert_prov(&mut frames[top_idx].out, Prov::Callable(func));
                            }
                            Op::LoadConst(c) => {
                                if let Some(Const::MethodRef { func: f, .. }) =
                                    self.module.consts.get(*c)
                                {
                                    insert_prov(&mut frames[top_idx].out, Prov::Callable(*f));
                                }
                            }
                            Op::Mov { src }
                            | Op::ThrowUndefinedIfHole { value: src, .. }
                            | Op::ThrowUndefinedIfHoleWithName { value: src, .. }
                            | Op::ThrowIfNotObject { value: src, .. }
                            | Op::ThrowIfSuperNotCalled { value: src, .. }
                            | Op::Await { value: src, .. }
                            | Op::AwaitUncaught { value: src, .. } => {
                                frames[top_idx].work.push((func, *src));
                            }
                            Op::ResumeGenerator { genobj } => {
                                for awaited in
                                    awaited_values_for_resume(self.module, func, iid, *genobj)
                                {
                                    frames[top_idx].work.push((func, awaited));
                                }
                            }
                            Op::Phi { entries } => {
                                for (_, incoming) in entries {
                                    frames[top_idx].work.push((func, *incoming));
                                }
                            }
                            Op::AllocClosure { func: inner }
                            | Op::CreateGenerator { func: inner }
                            | Op::CreateAsyncGenerator { func: inner }
                            | Op::DefineMethod { func: inner, .. } => {
                                frames[top_idx].work.push((func, *inner));
                            }
                            Op::DefineFunc { body, .. } => {
                                insert_prov(&mut frames[top_idx].out, Prov::Callable(*body));
                            }
                            Op::DefineClass(_) | Op::DefineSendableClass(_) => {
                                if let Some(cid) =
                                    self.class_by_inst.get(iid.index()).copied().flatten()
                                {
                                    insert_prov(&mut frames[top_idx].out, Prov::ClassObj(cid));
                                }
                            }
                            Op::AllocObject { .. } => {
                                insert_prov(&mut frames[top_idx].out, Prov::ObjLit(iid));
                            }
                            Op::LoadModuleVar { index, kind } => {
                                if *kind == ModuleVarKind::SendableClass {
                                    if let Some(cid) = self
                                        .enclosing_sendable_class
                                        .get(func.index())
                                        .copied()
                                        .flatten()
                                    {
                                        insert_prov(&mut frames[top_idx].out, Prov::ClassObj(cid));
                                    } else if self.links.has_multi_record_esm()
                                        && let Some(record_cid) = self.links.func_class(func)
                                    {
                                        let sr = ModuleSlotRef {
                                            class_id: record_cid,
                                            slot: *index,
                                        };
                                        for &(def_fn, def_val) in self.links.stored_values(sr) {
                                            frames[top_idx].work.push((def_fn, def_val));
                                        }
                                    }
                                } else if kind.is_local() {
                                    if self.links.has_multi_record_esm()
                                        && let Some(record_cid) = self.links.func_class(func)
                                    {
                                        let sr = ModuleSlotRef {
                                            class_id: record_cid,
                                            slot: *index,
                                        };
                                        for &(def_fn, def_val) in self.links.stored_values(sr) {
                                            frames[top_idx].work.push((def_fn, def_val));
                                        }
                                    }
                                } else if let Some(record_cid) = self.links.func_class(func)
                                    && let Some(target) =
                                        self.links.external_load(record_cid, *index)
                                {
                                    for &slot_ref in &target.slots {
                                        for &(def_fn, def_val) in self.links.stored_values(slot_ref)
                                        {
                                            frames[top_idx].work.push((def_fn, def_val));
                                        }
                                    }
                                    for &ns_cid in &target.namespace_classes {
                                        insert_prov(
                                            &mut frames[top_idx].out,
                                            Prov::ModuleNs(ns_cid),
                                        );
                                    }
                                }
                            }
                            Op::GetModuleNamespace { index } => {
                                if let Some(record_cid) = self.links.func_class(func)
                                    && let Some(target_cid) =
                                        self.links.namespace_target(record_cid, *index)
                                {
                                    insert_prov(
                                        &mut frames[top_idx].out,
                                        Prov::ModuleNs(target_cid),
                                    );
                                }
                            }
                            Op::GetLexVar { slot, .. } => {
                                if let Some(env_sites) = self.get_lex_sites.get(&iid) {
                                    for &env_site in env_sites {
                                        if let Some(stores) =
                                            self.lex_stores.get(&(env_site, *slot))
                                        {
                                            for &(def_fn, def_val) in stores {
                                                frames[top_idx].work.push((def_fn, def_val));
                                            }
                                        }
                                    }
                                }
                            }
                            Op::LoadSuper {
                                key: SuperKey::Name(name),
                                ..
                            } => {
                                if let Some((cid, is_static)) =
                                    self.super_owner.get(func.index()).copied().flatten()
                                {
                                    self.lookup_super_member(
                                        cid,
                                        is_static,
                                        *name,
                                        &mut frames[top_idx].out,
                                    );
                                }
                            }
                            Op::LoadProp { object, name } => {
                                let sub = (func, *object);
                                if let Some(cached) = memo.get(&sub).cloned() {
                                    self.apply_load_prop(&cached, *name, &mut frames[top_idx]);
                                } else if !frames.iter().any(|fr| fr.origin == Some(sub)) {
                                    frames.push(EvalFrame {
                                        origin: Some(sub),
                                        work: vec![sub],
                                        visited: HashSet::new(),
                                        out: BTreeSet::new(),
                                        cont: FrameCont::LoadProp { name: *name },
                                    });
                                }
                            }
                            Op::Call { callee, kind, .. } => {
                                let sub = (func, *callee);
                                if let Some(cached) = memo.get(&sub).cloned() {
                                    self.apply_call_result(
                                        &cached,
                                        *kind,
                                        &mut frames[top_idx].out,
                                    );
                                } else if !frames.iter().any(|fr| fr.origin == Some(sub)) {
                                    frames.push(EvalFrame {
                                        origin: Some(sub),
                                        work: vec![sub],
                                        visited: HashSet::new(),
                                        out: BTreeSet::new(),
                                        cont: FrameCont::Call { kind: *kind },
                                    });
                                }
                            }
                            _ => {}
                        }
                    }
                }
            } else {
                let Some(finished) = frames.pop() else {
                    break;
                };
                if steps < MAX_STEPS
                    && let Some(origin) = finished.origin
                {
                    memo.insert(origin, finished.out.clone());
                }
                match finished.cont {
                    FrameCont::Root => return finished.out,
                    FrameCont::LoadProp { name } => {
                        if let Some(parent) = frames.last_mut() {
                            self.apply_load_prop(&finished.out, name, parent);
                        }
                    }
                    FrameCont::Call { kind } => {
                        if let Some(parent) = frames.last_mut() {
                            self.apply_call_result(&finished.out, kind, &mut parent.out);
                        }
                    }
                }
            }
        }

        BTreeSet::new()
    }

    fn apply_load_prop(&self, obj_provs: &BTreeSet<Prov>, name: Sym, frame: &mut EvalFrame) {
        for &p in obj_provs {
            if frame.out.len() >= MAX_PROV_SET {
                break;
            }
            match p {
                Prov::ClassInst(c) => {
                    self.lookup_class_member(c, false, name, &mut frame.out);
                }
                Prov::ClassObj(c) => {
                    self.lookup_class_member(c, true, name, &mut frame.out);
                }
                Prov::ObjLit(alloc_iid) => {
                    if let Some(prop) = self.obj_lits.get(&(alloc_iid, name)) {
                        for &mfid in &prop.methods {
                            insert_prov(&mut frame.out, Prov::Callable(mfid));
                        }
                        for &(def_fn, def_val) in &prop.stores {
                            frame.work.push((def_fn, def_val));
                        }
                    }
                }
                Prov::ModuleNs(target_cid) => {
                    if let Some(exports) = self.links.namespace_exports(target_cid)
                        && let Some(slots) = exports.get(&name)
                    {
                        for &sr in slots {
                            for &(def_fn, def_val) in self.links.stored_values(sr) {
                                frame.work.push((def_fn, def_val));
                            }
                        }
                    }
                    if let Some(subs) = self.links.namespace_submodules(target_cid)
                        && let Some(sub_cids) = subs.get(&name)
                    {
                        for &scid in sub_cids {
                            insert_prov(&mut frame.out, Prov::ModuleNs(scid));
                        }
                    }
                }
                Prov::Callable(_) => {}
            }
        }
    }

    fn apply_call_result(
        &self,
        callee_provs: &BTreeSet<Prov>,
        kind: CallKind,
        out: &mut BTreeSet<Prov>,
    ) {
        if matches!(kind, CallKind::New | CallKind::NewSpread) {
            for &p in callee_provs {
                if let Prov::ClassObj(c) = p {
                    insert_prov(out, Prov::ClassInst(c));
                }
            }
        } else {
            for &p in callee_provs {
                if let Prov::Callable(f) = p
                    && let Some(rets) = self.func_returns.get(f.index())
                {
                    union_prov_set(out, rets);
                }
            }
        }
    }

    /// Lookup `name` on `start_cid` (and `super_classes` ancestors — plus
    /// static-hierarchy `sub_classes` overrides/implementors — with cycle guard
    /// and `<= 64` step cap) for instance (`!is_static`) or static
    /// (`is_static`) methods, fields, and getters.
    fn lookup_class_member(
        &self,
        start_cid: ClassDefId,
        is_static: bool,
        name: Sym,
        out: &mut BTreeSet<Prov>,
    ) {
        let mut concrete_methods = BTreeSet::new();
        let mut abstract_methods = BTreeSet::new();
        let record_method =
            |mfid: FuncId, concrete: &mut BTreeSet<FuncId>, abs: &mut BTreeSet<FuncId>| {
                let is_bodyless_abstract = self.module.func(mfid).is_some_and(|fd| {
                    fd.modifiers.contains(Modifiers::ABSTRACT)
                        && fd.blocks.is_empty()
                        && !fd.is_external
                });
                if is_bodyless_abstract {
                    abs.insert(mfid);
                } else {
                    concrete.insert(mfid);
                }
            };

        // 1a. Upward lookup on `start_cid`, falling back to `super_classes` on miss.
        let mut method_q = VecDeque::from([start_cid]);
        let mut visited_m = HashSet::from([start_cid]);
        let mut steps = 0usize;
        while let Some(cur) = method_q.pop_front() {
            if steps >= MAX_STEPS || concrete_methods.len() >= MAX_PROV_SET {
                break;
            }
            steps += 1;
            let Some(cls) = self.classes.get(cur.index()) else {
                continue;
            };
            let methods = if is_static {
                &cls.static_methods
            } else {
                &cls.instance_methods
            };
            if let Some(found) = methods.get(&name)
                && !found.is_empty()
            {
                for &m in found {
                    record_method(m, &mut concrete_methods, &mut abstract_methods);
                }
            } else {
                for &sc in &cls.super_classes {
                    if visited_m.insert(sc) {
                        method_q.push_back(sc);
                    }
                }
            }
        }

        // 1b. Static `ClassData` hierarchy CHA: collect subtype overrides/implementations.
        if !is_static
            && self
                .classes
                .get(start_cid.index())
                .is_some_and(|c| c.static_record.is_some())
        {
            let mut sub_q = VecDeque::new();
            let mut visited_sub = HashSet::from([start_cid]);
            if let Some(start_cls) = self.classes.get(start_cid.index()) {
                for &sub in &start_cls.sub_classes {
                    if visited_sub.insert(sub) {
                        sub_q.push_back(sub);
                    }
                }
            }
            let mut sub_steps = 0usize;
            while let Some(cur) = sub_q.pop_front() {
                if sub_steps >= MAX_STEPS || concrete_methods.len() >= MAX_PROV_SET {
                    break;
                }
                sub_steps += 1;
                let Some(cls) = self.classes.get(cur.index()) else {
                    continue;
                };
                if let Some(found) = cls.instance_methods.get(&name) {
                    for &m in found {
                        record_method(m, &mut concrete_methods, &mut abstract_methods);
                    }
                }
                for &sub in &cls.sub_classes {
                    if visited_sub.insert(sub) {
                        sub_q.push_back(sub);
                    }
                }
            }
        }

        let chosen = if !concrete_methods.is_empty() {
            &concrete_methods
        } else {
            &abstract_methods
        };
        for &m in chosen {
            insert_prov(out, Prov::Callable(m));
        }

        // 2. Fields & getters across `c` and ancestors (`c_or_anc`).
        let mut anc_q = VecDeque::from([start_cid]);
        let mut visited_a = HashSet::from([start_cid]);
        let mut anc_steps = 0usize;
        let mut getter_resolved_on_branch = false;
        while let Some(cur) = anc_q.pop_front() {
            if anc_steps >= MAX_STEPS || out.len() >= MAX_PROV_SET {
                break;
            }
            anc_steps += 1;
            let fields_map = if is_static {
                &self.static_fields
            } else {
                &self.instance_fields
            };
            if let Some(fset) = fields_map.get(&(cur, name)) {
                union_prov_set(out, fset);
            }
            let Some(cls) = self.classes.get(cur.index()) else {
                continue;
            };
            let getters = if is_static {
                &cls.static_getters
            } else {
                &cls.instance_getters
            };
            if !getter_resolved_on_branch
                && let Some(gs) = getters.get(&name)
                && !gs.is_empty()
            {
                getter_resolved_on_branch = true;
                for &g in gs {
                    if let Some(rets) = self.func_returns.get(g.index()) {
                        union_prov_set(out, rets);
                    }
                }
            }
            for &sc in &cls.super_classes {
                if visited_a.insert(sc) {
                    anc_q.push_back(sc);
                }
            }
        }
    }

    /// Lookup `super.name` across `super_classes` of `cid` (BFS with cycle guard & `<= 64` cap).
    fn lookup_super_member(
        &self,
        cid: ClassDefId,
        is_static: bool,
        name: Sym,
        out: &mut BTreeSet<Prov>,
    ) {
        let Some(start_cls) = self.classes.get(cid.index()) else {
            return;
        };
        let mut q = VecDeque::new();
        let mut visited = HashSet::from([cid]);
        for &sc in &start_cls.super_classes {
            if visited.insert(sc) {
                q.push_back(sc);
            }
        }
        let mut steps = 0usize;
        while let Some(cur) = q.pop_front() {
            if steps >= MAX_STEPS || out.len() >= MAX_PROV_SET {
                break;
            }
            steps += 1;
            let Some(cls) = self.classes.get(cur.index()) else {
                continue;
            };
            let methods = if is_static {
                &cls.static_methods
            } else {
                &cls.instance_methods
            };
            let getters = if is_static {
                &cls.static_getters
            } else {
                &cls.instance_getters
            };
            let mut hit = false;
            if let Some(found) = methods.get(&name)
                && !found.is_empty()
            {
                hit = true;
                for &m in found {
                    insert_prov(out, Prov::Callable(m));
                }
            }
            if let Some(gs) = getters.get(&name)
                && !gs.is_empty()
            {
                hit = true;
                for &g in gs {
                    if let Some(rets) = self.func_returns.get(g.index()) {
                        union_prov_set(out, rets);
                    }
                }
            }
            let fields_map = if is_static {
                &self.static_fields
            } else {
                &self.instance_fields
            };
            if let Some(fset) = fields_map.get(&(cur, name)) {
                union_prov_set(out, fset);
            }
            if !hit {
                for &sc in &cls.super_classes {
                    if visited.insert(sc) {
                        q.push_back(sc);
                    }
                }
            }
        }
    }
}

fn collect_referenced_static_classes(module: &Module) -> Vec<bool> {
    let n = module.classes.len();
    let mut referenced = vec![false; n];
    for cls in &module.classes {
        if let Some(sup) = cls.super_class
            && let Some(slot) = referenced.get_mut(sup.index())
        {
            *slot = true;
        }
        for &iface in &cls.interfaces {
            if let Some(slot) = referenced.get_mut(iface.index()) {
                *slot = true;
            }
        }
    }
    for val in &module.values {
        if let Ty::Static(StaticTy::Reference(rcid)) = &val.ty
            && let Some(slot) = referenced.get_mut(rcid.index())
        {
            *slot = true;
        }
    }
    referenced
}

fn should_index_static_class(
    module: &Module,
    cls_data: &abcd_ir::ClassData,
    is_referenced: bool,
) -> bool {
    if cls_data.modifiers.contains(Modifiers::ANNOTATION) {
        return false;
    }
    let desc = module.sym.resolve(cls_data.descriptor).unwrap_or("");
    if matches!(
        desc,
        "L_ESModuleRecord;"
            | "L_ESScopeNamesRecord;"
            | "L_ModuleRequestPhaseRecord;"
            | "L_ESSlotNumberAnnotation;"
            | "L_ESConcurrentModuleRequestsAnnotation;"
            | "L_ESCallTypeAnnotation;"
    ) {
        return false;
    }
    if cls_data.super_class.is_some() || !cls_data.interfaces.is_empty() || is_referenced {
        return true;
    }
    cls_data.es_module.is_none()
        && desc != "L_GLOBAL;"
        && desc != "LETSGLOBAL;"
        && !desc.ends_with("/ETSGLOBAL;")
        && (cls_data.source_lang == SourceLang::ArkTS
            || cls_data.modifiers.contains(Modifiers::INTERFACE))
}

fn index_static_class_data(
    module: &Module,
    rcid: ClassId,
    cls_data: &abcd_ir::ClassData,
    classes: &mut Vec<ClassDef>,
    ctor_to_classes: &mut [Vec<ClassDefId>],
    method_owner: &mut [Option<(ClassDefId, bool)>],
) -> ClassDefId {
    let cid = ClassDefId(classes.len() as u32);
    let mut ctor: Option<FuncId> = None;
    let mut instance_methods: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut static_methods: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut instance_getters: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut static_getters: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();

    for &mfid in &cls_data.methods {
        let Some(fd) = module.func(mfid) else {
            continue;
        };
        let mname = module.sym.resolve(fd.name).unwrap_or("");
        if fd.kind == FunctionKind::Constructor || mname == "<ctor>" {
            if ctor.is_none() {
                ctor = Some(mfid);
            }
            if let Some(list) = ctor_to_classes.get_mut(mfid.index()) {
                list.push(cid);
            }
            if let Some(slot) = method_owner.get_mut(mfid.index())
                && slot.is_none()
            {
                *slot = Some((cid, false));
            }
            continue;
        }
        if mname == "func_main_0" || mname == "<cctor>" {
            continue;
        }
        let is_static = fd.modifiers.contains(Modifiers::STATIC);
        if let Some(slot) = method_owner.get_mut(mfid.index())
            && slot.is_none()
        {
            *slot = Some((cid, is_static));
        }
        match fd.kind {
            FunctionKind::Setter => {}
            FunctionKind::Getter => {
                let map = if is_static {
                    &mut static_getters
                } else {
                    &mut instance_getters
                };
                map.entry(fd.name).or_default().push(mfid);
            }
            _ => {
                let map = if is_static {
                    &mut static_methods
                } else {
                    &mut instance_methods
                };
                map.entry(fd.name).or_default().push(mfid);
            }
        }
    }

    classes.push(ClassDef {
        ctor,
        enclosing_func: None,
        static_record: Some(rcid),
        heritage: None,
        is_sendable: false,
        super_classes: Vec::new(),
        sub_classes: Vec::new(),
        instance_methods,
        static_methods,
        instance_getters,
        static_getters,
    });
    cid
}

#[expect(
    clippy::too_many_arguments,
    reason = "flat arena index tables passed directly during single-pass class scan"
)]
fn index_class_def(
    module: &Module,
    enclosing_func: FuncId,
    ctor: FuncId,
    heritage: Option<ValueId>,
    members: ConstId,
    member_attrs: &[MemberAttrs],
    is_sendable: bool,
    classes: &mut Vec<ClassDef>,
    ctor_to_classes: &mut [Vec<ClassDefId>],
    method_owner: &mut [Option<(ClassDefId, bool)>],
    enclosing_sendable_class: &mut [Option<ClassDefId>],
    capture_sites: &mut Vec<(InstId, FuncId)>,
    parent_children: &mut Vec<FuncId>,
    def_iid: InstId,
) -> ClassDefId {
    let cid = ClassDefId(classes.len() as u32);
    if let Some(list) = ctor_to_classes.get_mut(ctor.index()) {
        list.push(cid);
    }
    if let Some(slot) = method_owner.get_mut(ctor.index()) {
        *slot = Some((cid, false));
    }
    if is_sendable && let Some(slot) = enclosing_sendable_class.get_mut(ctor.index()) {
        *slot = Some(cid);
    }
    capture_sites.push((def_iid, ctor));
    push_unique_func(parent_children, ctor);

    let mut instance_methods: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut static_methods: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut instance_getters: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();
    let mut static_getters: BTreeMap<Sym, Vec<FuncId>> = BTreeMap::new();

    if let Some(Const::ArrayLiteral(items)) = module.consts.get(members) {
        let tail_count = items
            .last()
            .and_then(|&tail_cid| match module.consts.get(tail_cid) {
                Some(Const::Int8(v)) => Some(*v as usize),
                Some(Const::Int32(v)) => ((*v as i32) >= 0).then_some(*v as usize),
                Some(Const::Number(bits)) => {
                    let v = f64::from_bits(*bits);
                    (v.is_finite() && v >= 0.0).then_some(v as usize)
                }
                Some(Const::Int64(v)) => (*v >= 0).then_some(*v as usize),
                Some(Const::UInt64(v)) => usize::try_from(*v).ok(),
                _ => None,
            });
        let mut idx = 0usize;
        let mut pair_idx = 0usize;
        while idx + 1 < items.len() {
            if let (
                Some(Const::String(name_sym)),
                Some(Const::MethodRef {
                    func: mfid,
                    kind: lit_kind,
                }),
            ) = (
                module.consts.get(items[idx]),
                module.consts.get(items[idx + 1]),
            ) {
                let fallback_kind = || match lit_kind {
                    abcd_ir::LitMethodKind::Getter => Some(FunctionKind::Getter),
                    abcd_ir::LitMethodKind::Setter => Some(FunctionKind::Setter),
                    _ => module.func(*mfid).map(|f| f.kind),
                };
                let (is_static, kind_opt) = if let Some(attr) = member_attrs.get(pair_idx) {
                    (attr.is_static, Some(attr.kind))
                } else if member_attrs.is_empty() {
                    let static_by_tail = tail_count.is_some_and(|n| pair_idx >= n);
                    (static_by_tail, fallback_kind())
                } else {
                    (false, fallback_kind())
                };

                if let Some(slot) = method_owner.get_mut(mfid.index()) {
                    *slot = Some((cid, is_static));
                }
                if is_sendable && let Some(slot) = enclosing_sendable_class.get_mut(mfid.index()) {
                    *slot = Some(cid);
                }
                capture_sites.push((def_iid, *mfid));
                push_unique_func(parent_children, *mfid);

                match kind_opt {
                    Some(FunctionKind::Setter) => {}
                    Some(FunctionKind::Getter) => {
                        let map = if is_static {
                            &mut static_getters
                        } else {
                            &mut instance_getters
                        };
                        map.entry(*name_sym).or_default().push(*mfid);
                    }
                    _ => {
                        let map = if is_static {
                            &mut static_methods
                        } else {
                            &mut instance_methods
                        };
                        map.entry(*name_sym).or_default().push(*mfid);
                    }
                }
                pair_idx += 1;
                idx += 2;
            } else {
                if let Some(Const::MethodRef { func: mfid, .. }) = module.consts.get(items[idx]) {
                    capture_sites.push((def_iid, *mfid));
                    push_unique_func(parent_children, *mfid);
                }
                idx += 1;
            }
        }
        if idx < items.len()
            && let Some(Const::MethodRef { func: mfid, .. }) = module.consts.get(items[idx])
        {
            capture_sites.push((def_iid, *mfid));
            push_unique_func(parent_children, *mfid);
        }
    }

    classes.push(ClassDef {
        ctor: Some(ctor),
        enclosing_func: Some(enclosing_func),
        static_record: None,
        heritage,
        is_sendable,
        super_classes: Vec::new(),
        sub_classes: Vec::new(),
        instance_methods,
        static_methods,
        instance_getters,
        static_getters,
    });
    cid
}

#[expect(
    clippy::too_many_arguments,
    reason = "flat arena index tables passed directly during prototype/static attachment"
)]
fn attach_class_member(
    module: &Module,
    cls: &mut ClassDef,
    cid: ClassDefId,
    name: Sym,
    mfid: FuncId,
    is_static: bool,
    method_owner: &mut [Option<(ClassDefId, bool)>],
    enclosing_sendable_class: &mut [Option<ClassDefId>],
) {
    if let Some(slot) = method_owner.get_mut(mfid.index())
        && slot.is_none()
    {
        *slot = Some((cid, is_static));
    }
    if cls.is_sendable
        && let Some(slot) = enclosing_sendable_class.get_mut(mfid.index())
        && slot.is_none()
    {
        *slot = Some(cid);
    }
    match module.func(mfid).map(|f| f.kind) {
        Some(FunctionKind::Setter) => {}
        Some(FunctionKind::Getter) => {
            let map = if is_static {
                &mut cls.static_getters
            } else {
                &mut cls.instance_getters
            };
            map.entry(name).or_default().push(mfid);
        }
        _ => {
            let map = if is_static {
                &mut cls.static_methods
            } else {
                &mut cls.instance_methods
            };
            map.entry(name).or_default().push(mfid);
        }
    }
}

fn sort_dedup_method_map(map: &mut BTreeMap<Sym, Vec<FuncId>>) {
    for list in map.values_mut() {
        list.sort();
        list.dedup();
    }
}

fn push_unique_func(list: &mut Vec<FuncId>, f: FuncId) {
    if !list.contains(&f) {
        list.push(f);
    }
}

fn peel_closure_func(module: &Module, mut v: ValueId) -> Option<FuncId> {
    let mut visited = HashSet::new();
    while visited.insert(v) {
        let val = module.value(v)?;
        match val.def {
            ValueDef::Const(c) => {
                return match module.consts.get(c) {
                    Some(Const::MethodRef { func: f, .. }) => Some(*f),
                    _ => None,
                };
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src } => {
                    v = peel_movs(module, *src);
                }
                Op::AllocClosure { func: src }
                | Op::CreateGenerator { func: src }
                | Op::CreateAsyncGenerator { func: src }
                | Op::DefineMethod { func: src, .. } => {
                    v = *src;
                }
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(c) => {
                    return match module.consts.get(*c) {
                        Some(Const::MethodRef { func: f, .. }) => Some(*f),
                        _ => None,
                    };
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
    None
}

fn compute_augmented_rpo(
    module: &Module,
    func_id: FuncId,
    exc_map: &ExceptionHandlerMap,
) -> Vec<BlockId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let Some(entry) = func.entry() else {
        return Vec::new();
    };
    let mut visited = HashSet::new();
    let mut post_order = Vec::new();
    visited.insert(entry);
    let mut stack: Vec<(BlockId, std::vec::IntoIter<BlockId>)> = vec![(
        entry,
        augmented_succs_with_map(module, exc_map, entry).into_iter(),
    )];
    while let Some((node, succs)) = stack.last_mut() {
        let node = *node;
        match succs.next() {
            Some(succ) => {
                if visited.insert(succ) {
                    stack.push((
                        succ,
                        augmented_succs_with_map(module, exc_map, succ).into_iter(),
                    ));
                }
            }
            None => {
                post_order.push(node);
                stack.pop();
            }
        }
    }
    post_order.reverse();
    for &bb in &func.blocks {
        if visited.insert(bb) {
            post_order.push(bb);
        }
    }
    post_order
}

fn compute_func_env_stacks(
    module: &Module,
    rpo: &[BlockId],
    exc_map: &ExceptionHandlerMap,
    entry_stack: &DualEnvStack,
    is_lex_or_cap: &[bool],
    stack_at: &mut HashMap<InstId, DualEnvStack>,
) {
    if rpo.is_empty() {
        return;
    }
    let mut block_to_rpo: HashMap<BlockId, usize> = HashMap::with_capacity(rpo.len());
    for (idx, &b) in rpo.iter().enumerate() {
        block_to_rpo.entry(b).or_insert(idx);
    }

    let mut in_stacks: Vec<Option<DualEnvStack>> = vec![None; rpo.len()];
    let mut wl: BTreeSet<usize> = BTreeSet::new();
    let mut next_seed = 0usize;

    loop {
        while next_seed < rpo.len() && in_stacks[next_seed].is_some() {
            next_seed += 1;
        }
        if next_seed >= rpo.len() {
            break;
        }
        in_stacks[next_seed] = Some(entry_stack.clone());
        wl.insert(next_seed);

        while let Some(rpo_idx) = wl.pop_first() {
            let b = rpo[rpo_idx];
            let Some(bb) = module.block(b) else {
                continue;
            };
            let mut cur = in_stacks[rpo_idx]
                .clone()
                .unwrap_or_else(|| entry_stack.clone());
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if is_lex_or_cap.get(iid.index()).copied().unwrap_or(false) {
                    match stack_at.get_mut(&iid) {
                        Some(existing) => {
                            merge_dual_env_stacks(existing, &cur);
                        }
                        None => {
                            stack_at.insert(iid, cur.clone());
                        }
                    }
                }
                match &inst.op {
                    Op::NewLexEnv {
                        kind: LexEnvKind::Sendable,
                        ..
                    } => {
                        push_env_site(&mut cur.sendable, iid);
                    }
                    Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                        push_env_site(&mut cur.plain, iid);
                    }
                    Op::PopLexEnv => {
                        // `PopLexEnv` (`poplexenv`) pops only `Plain` lexical environments;
                        // `Sendable` environments are NOT popped by `PopLexEnv`.
                        cur.plain.pop();
                    }
                    _ => {}
                }
            }
            for succ in augmented_succs_with_map(module, exc_map, b) {
                let Some(&succ_idx) = block_to_rpo.get(&succ) else {
                    continue;
                };
                let changed = match &mut in_stacks[succ_idx] {
                    Some(dst) => merge_dual_env_stacks(dst, &cur),
                    slot @ None => {
                        *slot = Some(cur.clone());
                        true
                    }
                };
                if changed {
                    wl.insert(succ_idx);
                }
            }
        }
    }
}

fn push_env_site(stack: &mut EnvStack, site: InstId) {
    stack.push(vec![site]);
    if stack.len() > MAX_ENV_DEPTH {
        let overflow = stack.len() - MAX_ENV_DEPTH;
        stack.drain(0..overflow);
    }
}

fn merge_dual_env_stacks(dst: &mut DualEnvStack, src: &DualEnvStack) -> bool {
    let c_plain = merge_env_stacks(&mut dst.plain, &src.plain);
    let c_sendable = merge_env_stacks(&mut dst.sendable, &src.sendable);
    c_plain || c_sendable
}

fn merge_env_stacks(dst: &mut EnvStack, src: &[Vec<InstId>]) -> bool {
    let src = &src[src.len().saturating_sub(MAX_ENV_DEPTH)..];
    if src.is_empty() {
        return false;
    }
    let mut changed = false;
    if src.len() > dst.len() {
        let extra = src.len() - dst.len();
        let mut expanded = Vec::with_capacity(src.len());
        for slot in &src[..extra] {
            expanded.push(slot.clone());
        }
        expanded.append(dst);
        *dst = expanded;
        changed = true;
    }
    let d_len = dst.len();
    let s_len = src.len();
    for off in 0..s_len {
        let d_slot = &mut dst[d_len - 1 - off];
        let s_slot = &src[s_len - 1 - off];
        for &site in s_slot {
            if !d_slot.contains(&site) && d_slot.len() < MAX_ENV_SITES_PER_SLOT {
                d_slot.push(site);
                d_slot.sort();
                changed = true;
            }
        }
    }
    changed
}

fn insert_prov(set: &mut BTreeSet<Prov>, p: Prov) -> bool {
    if set.contains(&p) || set.len() >= MAX_PROV_SET {
        return false;
    }
    set.insert(p)
}

fn union_prov_set(dst: &mut BTreeSet<Prov>, src: &BTreeSet<Prov>) -> bool {
    let mut changed = false;
    for &p in src {
        if dst.len() >= MAX_PROV_SET {
            break;
        }
        if dst.insert(p) {
            changed = true;
        }
    }
    changed
}
