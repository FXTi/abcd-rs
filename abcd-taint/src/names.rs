//! Callee-name resolution through the global-load def chain — the
//! matcher that makes summaries and sinks work when the call graph says
//! `UnknownCallees` (corpus reality: ~97% of call sites load their
//! callee via `TryGetGlobal`, mutable across scripts, so the edge is
//! never resolved — but the NAME is static).
//!
//! A call `print(x)` lifts to `%f = TryGetGlobal("print"); call %f`.
//! The callee value's def chain statically carries the global's name, so
//! name-keyed summaries/sinks fire independently of call-graph
//! resolution. Qualified names are built through property loads:
//! `console.log(x)` lifts to `%g = TryGetGlobal("console"); %f =
//! LoadProp(%g, "log"); call %f` → candidate `"console.log"`.
//!
//! Candidates are returned most-qualified first. Bare property names
//! (`"log"` alone) are deliberately NOT emitted: a bare-method registry
//! key would collide across every object with a same-named method.
//! Resolved-callee [`abcd_ir::FunctionData`] names are matched by the driver on
//! top of these candidates (directly-resolved internal functions).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;

use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_analysis::ohos_lifecycle::OHOS_CONTEXT_GLOBAL;
use abcd_analysis::{OhmUrl, OhmUrlKind};
use abcd_ir::module::ExportDecl;
use abcd_ir::{CallKind, ClassId, Const, FuncId, Module, Op, Sym, ValueDef, ValueId};

/// Per-root safety step cap on `resolve_iterative` and `resolve_namespace_classes`
/// so cyclic cross-module `StoreModuleVar` / `Phi` webs where `had_cycle`
/// suppresses memoization always terminate in bounded `O(1)` work (`#78`, `#84`).
const MAX_RESOLVE_STEPS: usize = 8_192;

type CalleeMemoMap = HashMap<(FuncId, ValueId), Rc<[String]>>;
type NsMemoMap = HashMap<(FuncId, ValueId), Rc<[ClassId]>>;

/// Allocation-free slice view over resolved internal ES module namespace [`ClassId`]s.
pub(crate) enum NsClasses {
    Empty,
    Shared(Rc<[ClassId]>),
    Owned(Vec<ClassId>),
}

impl Deref for NsClasses {
    type Target = [ClassId];

    #[inline]
    fn deref(&self) -> &[ClassId] {
        match self {
            Self::Empty => &[],
            Self::Shared(rc) => rc,
            Self::Owned(v) => v,
        }
    }
}

/// Pre-indexed `(ClassId, prop_name)` -> `(method FuncId, stored ValueId)` table
/// plus shared single-threaded `(FuncId, ValueId)` callee-name and namespace-class
/// memoization tables across `compute_pta_roots`, `TaintProblem`, and `collect_hits`
/// (`#78`, `#84`).
pub(crate) struct ClassPropStores {
    by_class_prop: HashMap<(ClassId, Sym), Vec<(FuncId, ValueId)>>,
    callee_memo: RefCell<CalleeMemoMap>,
    ns_memo: RefCell<NsMemoMap>,
    empty_strings: Rc<[String]>,
    empty_classes: Rc<[ClassId]>,
}

impl Default for ClassPropStores {
    fn default() -> Self {
        Self {
            by_class_prop: HashMap::new(),
            callee_memo: RefCell::new(HashMap::new()),
            ns_memo: RefCell::new(HashMap::new()),
            empty_strings: Rc::from(&[][..]),
            empty_classes: Rc::from(&[][..]),
        }
    }
}

impl Clone for ClassPropStores {
    fn clone(&self) -> Self {
        Self {
            by_class_prop: self.by_class_prop.clone(),
            callee_memo: RefCell::new(self.callee_memo.borrow().clone()),
            ns_memo: RefCell::new(self.ns_memo.borrow().clone()),
            empty_strings: Rc::clone(&self.empty_strings),
            empty_classes: Rc::clone(&self.empty_classes),
        }
    }
}

impl fmt::Debug for ClassPropStores {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClassPropStores")
            .field("class_props", &self.by_class_prop.len())
            .field("callee_memo_len", &self.callee_memo.borrow().len())
            .field("ns_memo_len", &self.ns_memo.borrow().len())
            .finish()
    }
}

impl ClassPropStores {
    /// Build the `(ClassId, prop_name)` property-store index over `module`.
    pub(crate) fn build(module: &Module) -> Self {
        let mut by_class_prop: HashMap<(ClassId, Sym), Vec<(FuncId, ValueId)>> = HashMap::new();
        for (ci, cls) in module.classes.iter().enumerate() {
            let cid = ClassId::new(ci as u32);
            for &mfid in &cls.methods {
                let Some(fd) = module.func(mfid) else {
                    continue;
                };
                for &b in &fd.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    for &iid in &bb.insts {
                        let Some(inst) = module.inst(iid) else {
                            continue;
                        };
                        if let Op::StoreProp { name, value, .. }
                        | Op::StoreOwnPropName { name, value, .. } = &inst.op
                        {
                            by_class_prop
                                .entry((cid, *name))
                                .or_default()
                                .push((mfid, *value));
                        }
                    }
                }
            }
        }
        Self {
            by_class_prop,
            ..Self::default()
        }
    }

    fn get(&self, cid: ClassId, prop_name: Sym) -> &[(FuncId, ValueId)] {
        self.by_class_prop
            .get(&(cid, prop_name))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

/// All candidate names for a callee value, most-qualified first, in
/// deterministic def-chain order. Iterative workstack with cycle guard.
pub fn callee_name_candidates(module: &Module, callee: ValueId) -> Vec<String> {
    let links = ModuleLinkTable::build(module);
    let caller = owner_func_of_value(module, &links, callee).unwrap_or(FuncId::new(0));
    callee_name_candidates_with_links(module, &links, caller, callee)
}

/// All candidate names for `callee` inside `caller`, resolving cross-module
/// ES `import`/`export` bindings, `@ohos.*` / `@kit.*` SDK specifiers,
/// two-step factory/constructor receivers (`http.createHttp().request`,
/// `new webview.WebviewController().loadUrl`, `await relationalStore.getRdbStore()`),
/// and `UIAbilityContext` (`this.context.*` / `getContext().*`).
pub fn callee_name_candidates_with_links(
    module: &Module,
    links: &ModuleLinkTable,
    caller: FuncId,
    callee: ValueId,
) -> Vec<String> {
    callee_name_candidates_indexed(module, links, None, caller, callee)
}

/// Indexed variant of [`callee_name_candidates_with_links`] reusing a prebuilt
/// [`ClassPropStores`] table across call sites.
pub(crate) fn callee_name_candidates_indexed(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: Option<&ClassPropStores>,
    caller: FuncId,
    callee: ValueId,
) -> Vec<String> {
    resolve_iterative(module, Some(links), prop_stores, caller, callee)
}

/// Fast `O(1)` pre-check returning `Some(sym)` when every candidate name
/// produced by [`callee_name_candidates_indexed`] (and [`call_method_leaf`])
/// for `callee` inside `caller` is guaranteed to end with `sym`'s final
/// `.`-segment. Returns `None` when full resolution is required.
pub(crate) fn quick_callee_leaf_sym(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: &ClassPropStores,
    caller: FuncId,
    mut callee: ValueId,
) -> Option<Sym> {
    let mut seen = [ValueId::new(u32::MAX); 8];
    for step in 0..8 {
        let val = module.value(callee)?;
        match val.def {
            ValueDef::Const(c) => {
                let Const::MethodRef { func: body, .. } = module.consts.get(c)? else {
                    return None;
                };
                return Some(module.func(*body)?.name);
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src } => {
                    if seen[..step].contains(&callee) {
                        return None;
                    }
                    seen[step] = callee;
                    callee = *src;
                }
                Op::DefineFunc { body, .. } => {
                    return Some(module.func(*body)?.name);
                }
                Op::LoadConst(c) => {
                    let Const::MethodRef { func: body, .. } = module.consts.get(*c)? else {
                        return None;
                    };
                    return Some(module.func(*body)?.name);
                }
                Op::TryGetGlobal { name, .. } => {
                    if module.sym.resolve(*name) == Some(OHOS_CONTEXT_GLOBAL) {
                        return None;
                    }
                    return Some(*name);
                }
                Op::LoadProp { object, name } => {
                    let leaf = module.sym.resolve(*name)?;
                    if matches!(
                        leaf,
                        "context" | "fileIo" | "identifier" | "dataPreferences"
                    ) {
                        return None;
                    }
                    if may_be_module_namespace_object(module, links, prop_stores, caller, *object) {
                        return None;
                    }
                    let cid = links
                        .func_class(caller)
                        .or_else(|| module.func(caller).map(|f| f.class_id))?;
                    if !prop_stores.get(cid, *name).is_empty() {
                        return None;
                    }
                    return Some(*name);
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
    None
}

enum ResolveStep {
    Enter {
        func: FuncId,
        value: ValueId,
    },
    Leave {
        func: FuncId,
        value: ValueId,
    },
    StartObjectPrefix {
        func: FuncId,
        object: ValueId,
        name: Sym,
    },
    FinishObjectPrefix {
        func: FuncId,
        object: ValueId,
        name: Sym,
    },
    StartSdkStore {
        func: FuncId,
        value: ValueId,
    },
    FinishSdkStore,
    FinishCall {
        kind: CallKind,
    },
}

/// Iterative def-chain name resolver (zero call-stack recursion), separating
/// active-path cycle detection (`visiting`) from shared DAG memoization
/// (`ClassPropStores::callee_memo` / `local_memo`) so diamond `Phi`/`LoadProp`
/// sharing runs in `O(1)` amortized across call sites while bounding cyclic
/// cross-module graphs via [`MAX_RESOLVE_STEPS`].
fn resolve_iterative(
    module: &Module,
    links: Option<&ModuleLinkTable>,
    prop_stores: Option<&ClassPropStores>,
    root_func: FuncId,
    root_value: ValueId,
) -> Vec<String> {
    let share_memo = links.is_some();
    if share_memo
        && let Some(ps) = prop_stores
        && let Some(cached) = ps.callee_memo.borrow().get(&(root_func, root_value))
    {
        return if cached.is_empty() {
            Vec::new()
        } else {
            cached.to_vec()
        };
    }

    let mut visiting: HashSet<(FuncId, ValueId)> = HashSet::new();
    let mut local_memo: CalleeMemoMap = HashMap::new();
    let mut bufs: Vec<Vec<String>> = vec![Vec::new()];
    let mut had_cycle: Vec<bool> = vec![false];
    let mut steps = 0usize;
    let mut stack: Vec<ResolveStep> = vec![ResolveStep::Enter {
        func: root_func,
        value: root_value,
    }];

    while let Some(step) = stack.pop() {
        steps += 1;
        match step {
            ResolveStep::Enter { func, value } => {
                if share_memo
                    && let Some(ps) = prop_stores
                    && let Some(cached) = ps.callee_memo.borrow().get(&(func, value)).cloned()
                {
                    if let Some(out) = bufs.last_mut() {
                        for cand in cached.iter() {
                            push_unique(out, cand.clone());
                        }
                    }
                    continue;
                }
                if (!share_memo || prop_stores.is_none())
                    && let Some(cached) = local_memo.get(&(func, value))
                {
                    if let Some(out) = bufs.last_mut() {
                        for cand in cached.iter() {
                            push_unique(out, cand.clone());
                        }
                    }
                    continue;
                }
                if steps > MAX_RESOLVE_STEPS || !visiting.insert((func, value)) {
                    if let Some(hc) = had_cycle.last_mut() {
                        *hc = true;
                    }
                    continue;
                }
                bufs.push(Vec::new());
                had_cycle.push(false);
                stack.push(ResolveStep::Leave { func, value });

                let Some(v) = module.value(value) else {
                    continue;
                };
                let ValueDef::Inst(iid) = v.def else {
                    if let ValueDef::Const(c) = v.def
                        && let Some(Const::MethodRef { func: f, .. }) = module.consts.get(c)
                        && let Some(fd) = module.func(*f)
                        && let Some(s) = module.sym.resolve(fd.name)
                        && let Some(out) = bufs.last_mut()
                    {
                        push_unique(out, s.to_owned());
                    }
                    continue;
                };
                match module.inst(iid).map(|i| &i.op) {
                    Some(Op::Mov { src })
                    | Some(Op::Await { value: src })
                    | Some(Op::AwaitUncaught { value: src, .. }) => {
                        stack.push(ResolveStep::Enter { func, value: *src });
                    }
                    Some(Op::ResumeGenerator { genobj }) => {
                        // Pair async-machine `AwaitUncaught` / `SuspendGenerator` ->
                        // `ResumeGenerator` across predecessor blocks so
                        // `const rdb = await relationalStore.getRdbStore(...); rdb.executeSql(...)`
                        // preserves receiver provenance across multi-block `await`s.
                        let owner = links.and_then(|l| l.inst_func(module, iid)).unwrap_or(func);
                        let awaited_vals = abcd_analysis::control::awaited_values_for_resume(
                            module, owner, iid, *genobj,
                        );
                        for val in awaited_vals.into_iter().rev() {
                            stack.push(ResolveStep::Enter {
                                func: owner,
                                value: val,
                            });
                        }
                    }
                    Some(Op::Phi { entries }) => {
                        for (_, incoming) in entries.iter().rev() {
                            stack.push(ResolveStep::Enter {
                                func,
                                value: *incoming,
                            });
                        }
                    }
                    Some(Op::TryGetGlobal { name, .. }) => {
                        if let Some(s) = module.sym.resolve(*name)
                            && let Some(out) = bufs.last_mut()
                        {
                            if s == OHOS_CONTEXT_GLOBAL {
                                push_unique(out, "UIAbilityContext".to_owned());
                            } else {
                                push_unique(out, s.to_owned());
                            }
                        }
                    }
                    Some(Op::LoadModuleVar { index, kind }) => {
                        if let Some(links) = links
                            && let Some(cid) = links.func_class(func)
                        {
                            if kind.is_local() {
                                if links.has_multi_record_esm() {
                                    let stored = links.stored_values(ModuleSlotRef {
                                        class_id: cid,
                                        slot: *index,
                                    });
                                    for &(def_fn, def_val) in stored.iter().rev() {
                                        stack.push(ResolveStep::Enter {
                                            func: def_fn,
                                            value: def_val,
                                        });
                                    }
                                }
                            } else if let Some(target) = links.external_load(cid, *index) {
                                if let Some(out) = bufs.last_mut() {
                                    for &(spec_sym, imp_sym) in &target.external_imports {
                                        let raw_spec = module.sym.resolve(spec_sym).unwrap_or("");
                                        let imp = module.sym.resolve(imp_sym).unwrap_or("");
                                        emit_external_import_names(raw_spec, imp, out);
                                    }
                                }
                                let mut pending = Vec::new();
                                for &slot_ref in &target.slots {
                                    for &(def_fn, def_val) in links.stored_values(slot_ref) {
                                        pending.push((def_fn, def_val));
                                    }
                                }
                                for (def_fn, def_val) in pending.into_iter().rev() {
                                    stack.push(ResolveStep::Enter {
                                        func: def_fn,
                                        value: def_val,
                                    });
                                }
                            }
                        }
                    }
                    Some(Op::GetModuleNamespace { index }) => {
                        if let Some(links) = links
                            && let Some(cid) = links.func_class(func)
                            && let Some(ext_sym) = links.namespace_external(cid, *index)
                            && let Some(out) = bufs.last_mut()
                        {
                            let raw_spec = module.sym.resolve(ext_sym).unwrap_or("");
                            let norm = normalize_sdk_specifier(raw_spec);
                            push_unique(out, norm);
                        }
                    }
                    Some(Op::LoadProp { object, name }) => {
                        // Qualified names through the receiver chain:
                        // `TryGetGlobal("console").log` -> `"console.log"`,
                        // `LoadModuleVar("@ohos.net.http").createHttp` -> `"@ohos.net.http.createHttp"`.
                        if let Some(leaf) = module.sym.resolve(*name) {
                            if is_viewpu_intrinsic(leaf)
                                && let Some(out) = bufs.last_mut()
                            {
                                push_unique(out, format!("ViewPU.{leaf}"));
                            }
                            stack.push(ResolveStep::StartObjectPrefix {
                                func,
                                object: *object,
                                name: *name,
                            });
                            // Internal namespace member (`import * as ns`, `export * as ns`,
                            // and nested `ns.sub.foo()` chains).
                            if let Some(links) = links {
                                let ns_classes = resolve_namespace_classes_cached(
                                    module,
                                    links,
                                    prop_stores,
                                    func,
                                    *object,
                                );
                                let mut ns_defs = Vec::new();
                                for &ns_cid in ns_classes.iter() {
                                    if let Some(slots) =
                                        links.namespace_exports(ns_cid).and_then(|m| m.get(name))
                                    {
                                        for &sr in slots {
                                            for &(def_fn, def_val) in links.stored_values(sr) {
                                                ns_defs.push((def_fn, def_val));
                                            }
                                        }
                                    }
                                    if let Some(out) = bufs.last_mut() {
                                        emit_namespace_external_reexports(
                                            module, ns_cid, *name, leaf, out,
                                        );
                                    }
                                }
                                for (def_fn, def_val) in ns_defs.into_iter().rev() {
                                    stack.push(ResolveStep::Enter {
                                        func: def_fn,
                                        value: def_val,
                                    });
                                }
                            }
                        }
                    }
                    Some(Op::Call { callee, kind, .. }) => {
                        if steps > MAX_RESOLVE_STEPS {
                            if let Some(hc) = had_cycle.last_mut() {
                                *hc = true;
                            }
                        } else {
                            bufs.push(Vec::new());
                            had_cycle.push(false);
                            stack.push(ResolveStep::FinishCall { kind: *kind });
                            stack.push(ResolveStep::Enter {
                                func,
                                value: *callee,
                            });
                        }
                    }
                    Some(Op::LoadConst(c)) => {
                        if let Some(Const::MethodRef { func: f, .. }) = module.consts.get(*c)
                            && let Some(fd) = module.func(*f)
                            && let Some(s) = module.sym.resolve(fd.name)
                            && let Some(out) = bufs.last_mut()
                        {
                            push_unique(out, s.to_owned());
                        }
                    }
                    Some(Op::DefineFunc { body, .. }) => {
                        if let Some(fd) = module.func(*body)
                            && let Some(s) = module.sym.resolve(fd.name)
                            && let Some(out) = bufs.last_mut()
                        {
                            push_unique(out, s.to_owned());
                        }
                    }
                    Some(Op::AllocClosure { func: inner })
                    | Some(Op::CreateGenerator { func: inner })
                    | Some(Op::CreateAsyncGenerator { func: inner })
                    | Some(Op::DefineMethod { func: inner, .. }) => {
                        stack.push(ResolveStep::Enter {
                            func,
                            value: *inner,
                        });
                    }
                    _ => {}
                }
            }
            ResolveStep::Leave { func, value } => {
                visiting.remove(&(func, value));
                let node_cands = bufs.pop().unwrap_or_default();
                let node_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && node_cycled
                {
                    *parent_hc = true;
                }
                if !node_cycled {
                    if share_memo && let Some(ps) = prop_stores {
                        let rc = if node_cands.is_empty() {
                            Rc::clone(&ps.empty_strings)
                        } else {
                            Rc::<[String]>::from(node_cands.as_slice())
                        };
                        ps.callee_memo.borrow_mut().insert((func, value), rc);
                    } else {
                        let rc = Rc::<[String]>::from(node_cands.as_slice());
                        local_memo.insert((func, value), rc);
                    }
                }
                if let Some(out) = bufs.last_mut() {
                    for cand in node_cands {
                        push_unique(out, cand);
                    }
                }
            }
            ResolveStep::StartObjectPrefix { func, object, name } => {
                if steps > MAX_RESOLVE_STEPS {
                    if let Some(hc) = had_cycle.last_mut() {
                        *hc = true;
                    }
                    continue;
                }
                bufs.push(Vec::new());
                had_cycle.push(false);
                stack.push(ResolveStep::FinishObjectPrefix { func, object, name });
                stack.push(ResolveStep::Enter {
                    func,
                    value: object,
                });
            }
            ResolveStep::FinishObjectPrefix { func, object, name } => {
                let prefix = bufs.pop().unwrap_or_default();
                let sub_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && sub_cycled
                {
                    *parent_hc = true;
                }
                let Some(leaf) = module.sym.resolve(name) else {
                    continue;
                };
                if prefix.is_empty() {
                    if leaf == "context" && is_this_or_lex_receiver(module, object) {
                        if let Some(out) = bufs.last_mut() {
                            push_unique(out, "UIAbilityContext".to_owned());
                        }
                    } else if let Some(cid) = links
                        .and_then(|l| l.func_class(func))
                        .or_else(|| module.func(func).map(|f| f.class_id))
                    {
                        let stores: Vec<(FuncId, ValueId)> = match prop_stores {
                            Some(ps) => ps.get(cid, name).to_vec(),
                            None => scan_class_prop_stores(module, cid, name),
                        };
                        for (mfid, val) in stores.into_iter().rev() {
                            stack.push(ResolveStep::StartSdkStore {
                                func: mfid,
                                value: val,
                            });
                        }
                    }
                } else if let Some(out) = bufs.last_mut() {
                    for base in &prefix {
                        if let Some(canon) = kit_canonical_alias(base, leaf) {
                            push_unique(out, canon.to_owned());
                        }
                        push_unique(out, format!("{base}.{leaf}"));
                    }
                }
            }
            ResolveStep::StartSdkStore { func, value } => {
                if steps > MAX_RESOLVE_STEPS {
                    if let Some(hc) = had_cycle.last_mut() {
                        *hc = true;
                    }
                    continue;
                }
                bufs.push(Vec::new());
                had_cycle.push(false);
                stack.push(ResolveStep::FinishSdkStore);
                stack.push(ResolveStep::Enter { func, value });
            }
            ResolveStep::FinishSdkStore => {
                let sub = bufs.pop().unwrap_or_default();
                let sub_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && sub_cycled
                {
                    *parent_hc = true;
                }
                if let Some(out) = bufs.last_mut() {
                    for cand in sub {
                        if cand.starts_with("@ohos.")
                            || cand.starts_with("@kit.")
                            || cand == "UIAbilityContext"
                        {
                            push_unique(out, cand);
                        }
                    }
                }
            }
            ResolveStep::FinishCall { kind } => {
                let callee_names = bufs.pop().unwrap_or_default();
                let sub_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && sub_cycled
                {
                    *parent_hc = true;
                }
                if let Some(out) = bufs.last_mut() {
                    if matches!(kind, CallKind::New | CallKind::NewSpread) {
                        for cn in callee_names {
                            if cn.starts_with("@ohos.") || cn.starts_with("@kit.") {
                                push_unique(out, cn);
                            }
                        }
                    } else {
                        for cn in &callee_names {
                            if let Some(ret_ty) = sdk_factory_return_type(cn) {
                                push_unique(out, ret_ty.to_owned());
                            }
                        }
                    }
                }
            }
        }
    }

    bufs.pop().unwrap_or_default()
}

fn owner_func_of_value(module: &Module, links: &ModuleLinkTable, val: ValueId) -> Option<FuncId> {
    match module.value(val)?.def {
        ValueDef::Inst(iid) => links.inst_func(module, iid),
        ValueDef::ExceptionParam(b) => module
            .block(b)
            .and_then(|bb| bb.insts.first())
            .and_then(|&iid| links.inst_func(module, iid))
            .or_else(|| {
                module
                    .functions
                    .iter()
                    .position(|f| f.blocks.contains(&b))
                    .map(|i| FuncId::new(i as u32))
            }),
        ValueDef::Param(_) | ValueDef::Const(_) => module
            .functions
            .iter()
            .position(|f| f.params.contains(&val))
            .map(|i| FuncId::new(i as u32)),
    }
}

fn scan_class_prop_stores(module: &Module, cid: ClassId, prop_name: Sym) -> Vec<(FuncId, ValueId)> {
    let mut stores = Vec::new();
    let Some(cls) = module.classes.get(cid.index()) else {
        return stores;
    };
    for &mfid in &cls.methods {
        let Some(fd) = module.func(mfid) else {
            continue;
        };
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::StoreProp { name, value, .. } | Op::StoreOwnPropName { name, value, .. } =
                    &inst.op
                    && *name == prop_name
                {
                    stores.push((mfid, *value));
                }
            }
        }
    }
    stores
}

fn may_be_module_namespace_object(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: &ClassPropStores,
    caller: FuncId,
    v: ValueId,
) -> bool {
    let v = abcd_analysis::dataflow::heap::peel_movs(module, v);
    let Some(ValueDef::Inst(iid)) = module.value(v).map(|val| val.def) else {
        return false;
    };
    let Some(op) = module.inst(iid).map(|i| &i.op) else {
        return false;
    };
    match op {
        Op::GetModuleNamespace { index } => links
            .func_class(caller)
            .and_then(|cid| links.namespace_target(cid, *index))
            .is_some(),
        Op::LoadModuleVar { index, kind } => {
            if !links.has_multi_record_esm() {
                return false;
            }
            let Some(cid) = links.func_class(caller) else {
                return false;
            };
            if !kind.is_local() {
                let Some(t) = links.external_load(cid, *index) else {
                    return false;
                };
                if t.namespace_classes.is_empty() && t.slots.is_empty() {
                    return false;
                }
            }
            let (classes, hit_cap) =
                resolve_namespace_classes_inner(module, links, Some(prop_stores), caller, v);
            !classes.is_empty() || hit_cap
        }
        Op::LoadProp { .. } | Op::Phi { .. } => {
            if !links.has_multi_record_esm() {
                return false;
            }
            let (classes, hit_cap) =
                resolve_namespace_classes_inner(module, links, Some(prop_stores), caller, v);
            !classes.is_empty() || hit_cap
        }
        _ => false,
    }
}

enum NsEvalStep {
    Enter { func: FuncId, value: ValueId },
    Leave { func: FuncId, value: ValueId },
    FinishSubProp { name: Sym },
}

/// Resolve all internal record [`ClassId`]s whose ES module namespace `value`
/// (in `func`) may denote via `GetModuleNamespace`, `export * as ns` external
/// imports (`ExternalSlotTarget::namespace_classes`), local module-slot copies,
/// or chained sub-namespace `LoadProp` reads (`ModuleLinkTable::namespace_submodules`),
/// sharing [`ClassPropStores::ns_memo`] across call sites (`#78`, `#84`).
pub(crate) fn resolve_namespace_classes_cached(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: Option<&ClassPropStores>,
    root_func: FuncId,
    root_value: ValueId,
) -> NsClasses {
    resolve_namespace_classes_inner(module, links, prop_stores, root_func, root_value).0
}

fn resolve_namespace_classes_inner(
    module: &Module,
    links: &ModuleLinkTable,
    prop_stores: Option<&ClassPropStores>,
    root_func: FuncId,
    root_value: ValueId,
) -> (NsClasses, bool) {
    let peeled = peel_movs_fast(module, root_value);
    if let Some(ps) = prop_stores
        && let Some(cached) = ps.ns_memo.borrow().get(&(root_func, peeled)).cloned()
    {
        return if cached.is_empty() {
            (NsClasses::Empty, false)
        } else {
            (NsClasses::Shared(cached), false)
        };
    }
    let Some(ValueDef::Inst(root_iid)) = module.value(peeled).map(|v| v.def) else {
        return (NsClasses::Empty, false);
    };
    let Some(root_op) = module.inst(root_iid).map(|i| &i.op) else {
        return (NsClasses::Empty, false);
    };
    if !matches!(
        root_op,
        Op::GetModuleNamespace { .. }
            | Op::LoadModuleVar { .. }
            | Op::LoadProp { .. }
            | Op::Phi { .. }
    ) {
        return (NsClasses::Empty, false);
    }

    let mut visiting: HashSet<(FuncId, ValueId)> = HashSet::new();
    let mut local_memo: NsMemoMap = HashMap::new();
    let mut frames: Vec<Vec<ClassId>> = vec![Vec::new()];
    let mut had_cycle: Vec<bool> = vec![false];
    let mut steps = 0usize;
    let mut hit_step_cap = false;
    let mut stack: Vec<NsEvalStep> = vec![NsEvalStep::Enter {
        func: root_func,
        value: peeled,
    }];

    let push_cid = |out: &mut Vec<ClassId>, cid: ClassId| {
        if !out.contains(&cid) {
            out.push(cid);
        }
    };

    while let Some(step) = stack.pop() {
        steps += 1;
        match step {
            NsEvalStep::Enter { func, value } => {
                if let Some(ps) = prop_stores
                    && let Some(cached) = ps.ns_memo.borrow().get(&(func, value)).cloned()
                {
                    if let Some(out) = frames.last_mut() {
                        for &cid in cached.iter() {
                            push_cid(out, cid);
                        }
                    }
                    continue;
                }
                if prop_stores.is_none()
                    && let Some(cached) = local_memo.get(&(func, value))
                {
                    if let Some(out) = frames.last_mut() {
                        for &cid in cached.iter() {
                            push_cid(out, cid);
                        }
                    }
                    continue;
                }
                let Some(ValueDef::Inst(iid)) = module.value(value).map(|v| v.def) else {
                    continue;
                };
                let Some(op) = module.inst(iid).map(|i| &i.op) else {
                    continue;
                };
                if !matches!(
                    op,
                    Op::Mov { .. }
                        | Op::Phi { .. }
                        | Op::GetModuleNamespace { .. }
                        | Op::LoadModuleVar { .. }
                        | Op::LoadProp { .. }
                ) {
                    continue;
                }
                if steps > MAX_RESOLVE_STEPS {
                    hit_step_cap = true;
                    if let Some(hc) = had_cycle.last_mut() {
                        *hc = true;
                    }
                    continue;
                }
                if !visiting.insert((func, value)) {
                    if let Some(hc) = had_cycle.last_mut() {
                        *hc = true;
                    }
                    continue;
                }
                frames.push(Vec::new());
                had_cycle.push(false);
                stack.push(NsEvalStep::Leave { func, value });

                match op {
                    Op::Mov { src } => stack.push(NsEvalStep::Enter { func, value: *src }),
                    Op::Phi { entries } => {
                        for (_, incoming) in entries.iter().rev() {
                            stack.push(NsEvalStep::Enter {
                                func,
                                value: *incoming,
                            });
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(cid) = links.func_class(func)
                            && let Some(target_cid) = links.namespace_target(cid, *index)
                            && let Some(out) = frames.last_mut()
                        {
                            push_cid(out, target_cid);
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        let Some(cid) = links.func_class(func) else {
                            continue;
                        };
                        if kind.is_local() {
                            let stored = links.stored_values(ModuleSlotRef {
                                class_id: cid,
                                slot: *index,
                            });
                            for &(def_fn, def_val) in stored.iter().rev() {
                                stack.push(NsEvalStep::Enter {
                                    func: def_fn,
                                    value: def_val,
                                });
                            }
                        } else if let Some(target) = links.external_load(cid, *index) {
                            if let Some(out) = frames.last_mut() {
                                for &ns_cid in &target.namespace_classes {
                                    push_cid(out, ns_cid);
                                }
                            }
                            let mut defs = Vec::new();
                            for &sr in &target.slots {
                                for &(def_fn, def_val) in links.stored_values(sr) {
                                    defs.push((def_fn, def_val));
                                }
                            }
                            for (def_fn, def_val) in defs.into_iter().rev() {
                                stack.push(NsEvalStep::Enter {
                                    func: def_fn,
                                    value: def_val,
                                });
                            }
                        }
                    }
                    Op::LoadProp { object, name } => {
                        if steps > MAX_RESOLVE_STEPS {
                            hit_step_cap = true;
                            if let Some(hc) = had_cycle.last_mut() {
                                *hc = true;
                            }
                        } else {
                            frames.push(Vec::new());
                            had_cycle.push(false);
                            stack.push(NsEvalStep::FinishSubProp { name: *name });
                            stack.push(NsEvalStep::Enter {
                                func,
                                value: *object,
                            });
                        }
                    }
                    _ => {}
                }
            }
            NsEvalStep::FinishSubProp { name } => {
                let parent_ns = frames.pop().unwrap_or_default();
                let sub_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && sub_cycled
                {
                    *parent_hc = true;
                }
                let mut defs = Vec::new();
                for p_cid in parent_ns {
                    if let Some(sub_cids) =
                        links.namespace_submodules(p_cid).and_then(|m| m.get(&name))
                        && let Some(out) = frames.last_mut()
                    {
                        for &scid in sub_cids {
                            push_cid(out, scid);
                        }
                    }
                    if let Some(slots) = links.namespace_exports(p_cid).and_then(|m| m.get(&name)) {
                        for &sr in slots {
                            for &(def_fn, def_val) in links.stored_values(sr) {
                                defs.push((def_fn, def_val));
                            }
                        }
                    }
                }
                for (def_fn, def_val) in defs.into_iter().rev() {
                    stack.push(NsEvalStep::Enter {
                        func: def_fn,
                        value: def_val,
                    });
                }
            }
            NsEvalStep::Leave { func, value } => {
                visiting.remove(&(func, value));
                let node_cids = frames.pop().unwrap_or_default();
                let node_cycled = had_cycle.pop().unwrap_or(false);
                if let Some(parent_hc) = had_cycle.last_mut()
                    && node_cycled
                {
                    *parent_hc = true;
                }
                // Monotone fixed-point property: when `visiting.is_empty()` and
                // `!hit_step_cap` with `node_cids.is_empty()`, zero namespace
                // generators are reachable anywhere in this closed SCC, so `[]`
                // is exact even across cyclic non-namespace loop `Phi`s.
                let exact = !hit_step_cap
                    && (!node_cycled || (visiting.is_empty() && node_cids.is_empty()));
                if exact {
                    if let Some(ps) = prop_stores {
                        let rc = if node_cids.is_empty() {
                            Rc::clone(&ps.empty_classes)
                        } else {
                            Rc::<[ClassId]>::from(node_cids.as_slice())
                        };
                        ps.ns_memo.borrow_mut().insert((func, value), rc);
                    } else {
                        let rc = Rc::<[ClassId]>::from(node_cids.as_slice());
                        local_memo.insert((func, value), rc);
                    }
                }
                if let Some(out) = frames.last_mut() {
                    for cid in node_cids {
                        push_cid(out, cid);
                    }
                }
            }
        }
    }

    let root_out = frames.pop().unwrap_or_default();
    if root_out.is_empty() {
        (NsClasses::Empty, hit_step_cap)
    } else {
        (NsClasses::Owned(root_out), hit_step_cap)
    }
}

/// Emit external SDK candidate names when an internal barrel namespace `ns_cid`
/// re-exports an external SDK binding via `export { ... } from '@ohos.*'` or
/// `export * from '@ohos.*'` (`R8`).
fn emit_namespace_external_reexports(
    module: &Module,
    ns_cid: ClassId,
    prop_sym: Sym,
    prop_str: &str,
    out: &mut Vec<String>,
) {
    let mut visited = HashSet::new();
    let mut stack = vec![ns_cid];
    while let Some(cur_cid) = stack.pop() {
        if !visited.insert(cur_cid) {
            continue;
        }
        let Some(cls) = module.classes.get(cur_cid.index()) else {
            continue;
        };
        let Some(esm) = &cls.es_module else {
            continue;
        };
        for exp in &esm.exports {
            match exp {
                ExportDecl::Indirect {
                    export_name,
                    import_name,
                    module_request,
                } if *export_name == prop_sym => {
                    let raw_spec = module.sym.resolve(*module_request).unwrap_or("");
                    if OhmUrl::is_sdk_specifier(raw_spec) {
                        let imp = module.sym.resolve(*import_name).unwrap_or("");
                        emit_external_import_names(raw_spec, imp, out);
                    }
                }
                ExportDecl::Star { module_request } => {
                    let raw_spec = module.sym.resolve(*module_request).unwrap_or("");
                    if OhmUrl::is_sdk_specifier(raw_spec) {
                        emit_external_import_names(raw_spec, prop_str, out);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Allocation-free `Op::Mov` def-chain peeler using Floyd's tortoise-and-hare
/// cycle guard (`O(steps)`, zero heap allocation).
#[inline]
pub(crate) fn peel_movs_fast(module: &Module, v: ValueId) -> ValueId {
    let step_mov = |cur: ValueId| -> Option<ValueId> {
        let ValueDef::Inst(iid) = module.value(cur)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::Mov { src } => Some(*src),
            _ => None,
        }
    };
    let Some(mut cur) = step_mov(v) else {
        return v;
    };
    if cur == v {
        return v;
    }
    let mut slow = v;
    let mut advance_slow = false;
    while let Some(next) = step_mov(cur) {
        if next == cur || next == slow {
            return cur;
        }
        cur = next;
        if advance_slow && let Some(s_next) = step_mov(slow) {
            slow = s_next;
        }
        advance_slow = !advance_slow;
    }
    cur
}

fn is_this_or_lex_receiver(module: &Module, v: ValueId) -> bool {
    let v = peel_movs_fast(module, v);
    let Some(val) = module.value(v) else {
        return false;
    };
    match val.def {
        ValueDef::Param(_) => true,
        ValueDef::Inst(iid) => {
            matches!(module.inst(iid).map(|i| &i.op), Some(Op::GetLexVar { .. }))
        }
        _ => false,
    }
}

fn is_viewpu_intrinsic(leaf: &str) -> bool {
    matches!(
        leaf,
        "observeComponentCreation2"
            | "observeComponentCreation"
            | "observeRecycleComponentCreation"
            | "ifElseBranchUpdateFunction"
            | "forEachUpdateFunction"
    )
}

/// Normalize OpenHarmony SDK / OHM URL specifiers (`@ohos:foo` -> `@ohos.foo`,
/// `@hms:foo` -> `@hms.foo`, `@kit:foo` -> `@kit.foo`, `@arkts:foo` -> `@arkts.foo`,
/// `@system:foo` -> `@system.foo`, `@normalized:...` -> logical `import_path`)
/// via [`abcd_analysis::OhmUrl`].
pub fn normalize_sdk_specifier(raw: &str) -> String {
    if let Some(ohm) = OhmUrl::parse(raw) {
        return match ohm.kind {
            OhmUrlKind::OhosSdk => format!("@ohos.{}", ohm.import_path),
            OhmUrlKind::HmsSdk => format!("@hms.{}", ohm.import_path),
            OhmUrlKind::KitSdk => format!("@kit.{}", ohm.import_path),
            OhmUrlKind::ArktsSdk => format!("@arkts.{}", ohm.import_path),
            OhmUrlKind::SystemSdk => format!("@system.{}", ohm.import_path),
            OhmUrlKind::Native => format!("@native:{}", ohm.import_path),
            OhmUrlKind::Normalized { .. }
            | OhmUrlKind::Bundle
            | OhmUrlKind::Package
            | OhmUrlKind::App => ohm.import_path.to_owned(),
        };
    }
    raw.to_owned()
}

fn emit_external_import_names(raw_spec: &str, imp: &str, out: &mut Vec<String>) {
    if raw_spec.is_empty() {
        return;
    }
    let spec = normalize_sdk_specifier(raw_spec);
    if imp.is_empty() || imp == "default" || imp == "*" {
        push_unique(out, spec);
    } else {
        if let Some(canon) = kit_canonical_alias(&spec, imp) {
            push_unique(out, canon.to_owned());
        }
        push_unique(out, format!("{spec}.{imp}"));
    }
}

/// Map HarmonyOS NEXT `@kit.*` named bindings onto canonical `@ohos.*`
/// module prefixes so a single rule pack covers both import styles.
pub fn kit_canonical_alias(spec: &str, binding: &str) -> Option<&'static str> {
    match (spec, binding) {
        ("@kit.NetworkKit", "http") => Some("@ohos.net.http"),
        ("@kit.NetworkKit", "socket") => Some("@ohos.net.socket"),
        ("@kit.NetworkKit", "webSocket") => Some("@ohos.net.webSocket"),
        ("@kit.NetworkKit", "connection") => Some("@ohos.net.connection"),
        ("@kit.PerformanceAnalysisKit", "hilog") => Some("@ohos.hilog"),
        ("@kit.BasicServicesKit", "pasteboard") => Some("@ohos.pasteboard"),
        ("@kit.BasicServicesKit", "deviceInfo") => Some("@ohos.deviceInfo"),
        ("@kit.BasicServicesKit", "commonEventManager") => Some("@ohos.commonEventManager"),
        ("@kit.BasicServicesKit", "request") => Some("@ohos.request"),
        ("@kit.LocationKit", "geoLocationManager") => Some("@ohos.geoLocationManager"),
        ("@kit.ArkWeb", "webview") => Some("@ohos.web.webview"),
        ("@kit.ArkData", "preferences") | ("@kit.ArkData", "dataPreferences") => {
            Some("@ohos.data.preferences")
        }
        ("@kit.ArkData", "relationalStore") => Some("@ohos.data.relationalStore"),
        ("@kit.ArkData", "distributedKVStore") => Some("@ohos.data.distributedKVStore"),
        ("@kit.CoreFileKit", "fileIo") | ("@kit.CoreFileKit", "fs") => Some("@ohos.file.fs"),
        ("@kit.AdsKit", "identifier") => Some("@ohos.identifier.oaid"),
        ("@kit.ContactsKit", "contact") => Some("@ohos.contact"),
        ("@kit.TelephonyKit", "call") => Some("@ohos.telephony.call"),
        ("@kit.TelephonyKit", "radio") => Some("@ohos.telephony.radio"),
        ("@kit.TelephonyKit", "sim") => Some("@ohos.telephony.sim"),
        ("@kit.TelephonyKit", "sms") => Some("@ohos.telephony.sms"),
        ("@kit.AbilityKit", "UIAbility") => Some("@ohos.app.ability.UIAbility"),
        ("@kit.AbilityKit", "Want") => Some("@ohos.app.ability.Want"),
        ("@kit.AbilityKit", "common") => Some("@ohos.app.ability.common"),
        ("@kit.CryptoArchitectureKit", "cryptoFramework") => Some("@ohos.security.cryptoFramework"),
        ("@kit.ArkUI", "router") => Some("@ohos.router"),
        _ => None,
    }
}

/// Map two-step OpenHarmony SDK factory calls to their canonical receiver prefix.
fn sdk_factory_return_type(callee_name: &str) -> Option<&'static str> {
    match callee_name {
        "@ohos.net.http.createHttp" => Some("@ohos.net.http.HttpRequest"),
        "@ohos.net.socket.constructTCPSocketInstance" => Some("@ohos.net.socket.TCPSocket"),
        "@ohos.net.socket.constructUDPSocketInstance" => Some("@ohos.net.socket.UDPSocket"),
        "@ohos.net.socket.constructTLSSocketInstance" => Some("@ohos.net.socket.TLSSocket"),
        "@ohos.pasteboard.getSystemPasteboard" => Some("@ohos.pasteboard.SystemPasteboard"),
        "@ohos.pasteboard.SystemPasteboard.getData"
        | "@ohos.pasteboard.SystemPasteboard.getDataSync"
        | "@ohos.pasteboard.createData" => Some("@ohos.pasteboard.PasteData"),
        "@ohos.data.preferences.getPreferences" | "@ohos.data.preferences.getPreferencesSync" => {
            Some("@ohos.data.preferences.Preferences")
        }
        "@ohos.data.relationalStore.getRdbStore" => Some("@ohos.data.relationalStore.RdbStore"),
        "@ohos.file.fs.open" | "@ohos.file.fs.openSync" => Some("@ohos.file.fs.File"),
        "getContext" | "@ohos.app.ability.common.getContext" => Some("UIAbilityContext"),
        _ => None,
    }
}

fn push_unique(out: &mut Vec<String>, s: String) {
    if !s.is_empty() && !out.contains(&s) {
        out.push(s);
    }
}

/// The base (receiver) value of a call: the explicit `this` (peeled through
/// `Op::Mov` chains), or — for the `obj.m()` shape where `Dynamic` calls carry
/// no `this` — the receiver object of the `LoadProp` / `LoadPropDyn` /
/// `LoadPropIdx` / `LoadPrivate` / `LoadSuper` that produced `callee` (also
/// peeled through `Op::Mov` chains).
pub fn call_base_value(module: &Module, call: &abcd_ir::Inst) -> Option<ValueId> {
    let Op::Call { callee, this, .. } = &call.op else {
        return None;
    };
    if let Some(t) = this {
        return Some(abcd_analysis::dataflow::heap::peel_movs(module, *t));
    }
    base_through_movs(module, *callee)
        .map(|obj| abcd_analysis::dataflow::heap::peel_movs(module, obj))
}

fn receiver_of_member_load(op: &Op) -> Option<ValueId> {
    match op {
        Op::LoadProp { object, .. }
        | Op::LoadPropDyn { object, .. }
        | Op::LoadPropIdx { object, .. } => Some(*object),
        Op::LoadPrivate { obj, .. } => Some(*obj),
        Op::LoadSuper { this_value, .. } => Some(*this_value),
        _ => None,
    }
}

fn base_through_movs(module: &Module, value: ValueId) -> Option<ValueId> {
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    let op = module.inst(iid).map(|i| &i.op)?;
    if let Some(obj) = receiver_of_member_load(op) {
        return Some(obj);
    }
    if !matches!(op, Op::Mov { .. } | Op::Phi { .. }) {
        return None;
    }
    let mut visiting = HashSet::new();
    let mut stack = vec![value];
    while let Some(cur) = stack.pop() {
        if !visiting.insert(cur) {
            continue;
        }
        let Some(cv) = module.value(cur) else {
            continue;
        };
        let ValueDef::Inst(ciid) = cv.def else {
            continue;
        };
        let Some(op) = module.inst(ciid).map(|i| &i.op) else {
            continue;
        };
        if let Some(obj) = receiver_of_member_load(op) {
            return Some(obj);
        }
        match op {
            Op::Mov { src } => stack.push(*src),
            // Loop rotation: the callee phi merges the pre-loop LoadProp
            // with the phi itself; every entry reaches the same LoadProp
            // in that shape (first-found is exact there, may otherwise).
            Op::Phi { entries } => {
                for (_, incoming) in entries.iter().rev() {
                    stack.push(*incoming);
                }
            }
            _ => {}
        }
    }
    None
}

/// The method leaf of a call whose callee came through a `LoadProp`
/// chain: `a.pop(...)` → `"pop"`. This is the key the prototype
/// resolution path (`crate::prototype`) qualifies with the
/// receiver's family — `TryGetGlobal("a").pop` + receiver family
/// `Array` ⇒ candidate `Array.prototype.pop`. Returns `None` when the
/// callee is not a property load (bare global calls, direct calls).
pub fn call_method_leaf(module: &Module, call: &abcd_ir::Inst) -> Option<Sym> {
    let Op::Call { callee, .. } = &call.op else {
        return None;
    };
    leaf_through_movs(module, *callee)
}

fn leaf_through_movs(module: &Module, value: ValueId) -> Option<Sym> {
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::LoadProp { name, .. } => return Some(*name),
        Op::Mov { .. } | Op::Phi { .. } => {}
        _ => return None,
    }
    let mut visiting = HashSet::new();
    let mut stack = vec![value];
    while let Some(cur) = stack.pop() {
        if !visiting.insert(cur) {
            continue;
        }
        let Some(cv) = module.value(cur) else {
            continue;
        };
        let ValueDef::Inst(ciid) = cv.def else {
            continue;
        };
        let Some(op) = module.inst(ciid).map(|i| &i.op) else {
            continue;
        };
        match op {
            Op::Mov { src } => stack.push(*src),
            // Loop-rotated method calls: the callee phi merges the
            // pre-loop LoadProp with the phi itself (for-of's `next`).
            Op::Phi { entries } => {
                for (_, incoming) in entries.iter().rev() {
                    stack.push(*incoming);
                }
            }
            Op::LoadProp { name, .. } => return Some(*name),
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::BlockId;
    use abcd_ir::function::{Block, Edge, EdgeKind, FunctionData, Inst, Value};
    use abcd_ir::module::{
        ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, Modifiers, ModuleRequest,
    };
    use abcd_ir::op::ModuleVarKind;
    use abcd_ir::ty::Ty;

    fn emit_val(m: &mut Module, block: BlockId, op: Op) -> ValueId {
        let iid = abcd_ir::InstId::new(m.insts.len() as u32);
        let vid = ValueId::new(m.values.len() as u32);
        m.insts.push(Inst {
            op,
            result: Some(vid),
            block,
            loc: None,
        });
        m.values.push(Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        m.blocks[block.index()].insts.push(iid);
        vid
    }

    fn emit_void(m: &mut Module, block: BlockId, op: Op) {
        let iid = abcd_ir::InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block,
            loc: None,
        });
        m.blocks[block.index()].insts.push(iid);
    }

    #[test]
    fn quick_callee_leaf_and_shared_memos_handle_multi_record_esm_and_aliased_namespaces() {
        let mut m = Module::new();

        // Class 0 (`./lib`): exports `realSecretFn` as `aliasedFn`.
        let d0 = m.sym.intern("L@bundle:app/entry/ets/lib;");
        let n0 = m.sym.intern("@bundle:app/entry/ets/lib");
        let s_real = m.sym.intern("realSecretFn");
        let s_alias = m.sym.intern("aliasedFn");
        let mut c0 = ClassData::new(d0, n0);
        c0.es_module = Some(EsModule {
            imports: Vec::new(),
            exports: vec![ExportDecl::Local {
                export_name: s_alias,
                local_name: s_real,
            }],
            module_requests: Vec::new(),
        });
        m.classes.push(c0);

        // Class 1 (`./entry`): `import * as libNs from './lib'` AND `import http from '@ohos.net.http'`.
        let d1 = m.sym.intern("L@bundle:app/entry/ets/entry;");
        let n1 = m.sym.intern("@bundle:app/entry/ets/entry");
        let s_req_lib = m.sym.intern("./lib");
        let s_req_http = m.sym.intern("@ohos.net.http");
        let s_default = m.sym.intern("default");
        let s_http_local = m.sym.intern("http");
        let mut c1 = ClassData::new(d1, n1);
        c1.es_module = Some(EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: s_http_local,
                import_name: s_default,
                module_request: s_req_http,
            }],
            exports: Vec::new(),
            module_requests: vec![
                ModuleRequest {
                    specifier: s_req_lib,
                    lazy: false,
                },
                ModuleRequest {
                    specifier: s_req_http,
                    lazy: false,
                },
            ],
        });
        m.classes.push(c1);

        // `lib.realSecretFn` + `lib.func_main_0` storing `realSecretFn` into slot 0.
        let b_real = abcd_ir::BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        let f_real = FuncId::new(m.functions.len() as u32);
        let mut fd_real = FunctionData::new(ClassId::new(0), s_real, FunctionKind::Function);
        fd_real.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        fd_real.blocks.push(b_real);
        m.functions.push(fd_real);
        m.classes[0].methods.push(f_real);
        emit_void(&mut m, b_real, Op::Return { value: None });

        let s_main = m.sym.intern("func_main_0");
        let b_m0 = abcd_ir::BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        let f_m0 = FuncId::new(m.functions.len() as u32);
        let mut fd_m0 = FunctionData::new(ClassId::new(0), s_main, FunctionKind::Function);
        fd_m0.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        fd_m0.blocks.push(b_m0);
        m.functions.push(fd_m0);
        m.classes[0].methods.push(f_m0);
        let df_real = emit_val(
            &mut m,
            b_m0,
            Op::DefineFunc {
                body: f_real,
                captures: Vec::new(),
                length: 0,
            },
        );
        emit_void(
            &mut m,
            b_m0,
            Op::StoreModuleVar {
                index: 0,
                value: df_real,
            },
        );
        emit_void(&mut m, b_m0, Op::Return { value: None });

        // `entry.func_main_0`
        let b_m1 = abcd_ir::BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        let f_m1 = FuncId::new(m.functions.len() as u32);
        let mut fd_m1 = FunctionData::new(ClassId::new(1), s_main, FunctionKind::Function);
        fd_m1.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        fd_m1.blocks.push(b_m1);
        let p_this = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(2),
            ty: Ty::Any,
        });
        fd_m1.params.push(p_this);
        m.functions.push(fd_m1);
        m.classes[1].methods.push(f_m1);

        // 1) `this.helper.doWork`: chained `LoadProp` on non-namespace receiver in multi-record ESM!
        let s_helper = m.sym.intern("helper");
        let s_do_work = m.sym.intern("doWork");
        let v_helper = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: p_this,
                name: s_helper,
            },
        );
        let v_do_work = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: v_helper,
                name: s_do_work,
            },
        );

        // 2) `http.createHttp`: external SDK `LoadModuleVar` in multi-record ESM!
        let s_create_http = m.sym.intern("createHttp");
        let v_http = emit_val(
            &mut m,
            b_m1,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let v_create_http = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: v_http,
                name: s_create_http,
            },
        );

        // 3) Cyclic non-namespace loop `Phi` (`phi = Phi(v_helper, LoadProp(phi, "next"))`)!
        let s_next = m.sym.intern("next");
        let phi_iid = abcd_ir::InstId::new(m.insts.len() as u32);
        let phi_vid = ValueId::new(m.values.len() as u32);
        m.insts.push(Inst {
            op: Op::Phi {
                entries: Vec::new(),
            },
            result: Some(phi_vid),
            block: b_m1,
            loc: None,
        });
        m.values.push(Value {
            def: ValueDef::Inst(phi_iid),
            ty: Ty::Any,
        });
        m.blocks[b_m1.index()].insts.push(phi_iid);
        let v_phi_next = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: phi_vid,
                name: s_next,
            },
        );
        m.insts[phi_iid.index()].op = Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_m1,
                        kind: EdgeKind::Normal,
                    },
                    v_helper,
                ),
                (
                    Edge {
                        from: b_m1,
                        kind: EdgeKind::Normal,
                    },
                    v_phi_next,
                ),
            ],
        };
        let v_phi_method = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: phi_vid,
                name: s_do_work,
            },
        );

        // 4) Genuine internal namespace `libNs.aliasedFn` (where exported name != `realSecretFn`)!
        let v_lib_ns = emit_val(&mut m, b_m1, Op::GetModuleNamespace { index: 0 });
        let v_aliased_call = emit_val(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: v_lib_ns,
                name: s_alias,
            },
        );
        emit_void(&mut m, b_m1, Op::Return { value: None });

        let links = ModuleLinkTable::build(&m);
        assert!(links.has_multi_record_esm());
        let ps = ClassPropStores::build(&m);

        // Fast `quick_callee_leaf_sym` succeeds on `this.helper.doWork`, `http.createHttp`,
        // AND cyclic non-namespace `phi.doWork`, while soundly returning `None` on `libNs.aliasedFn`!
        assert_eq!(
            quick_callee_leaf_sym(&m, &links, &ps, f_m1, v_do_work),
            Some(s_do_work)
        );
        assert_eq!(
            quick_callee_leaf_sym(&m, &links, &ps, f_m1, v_create_http),
            Some(s_create_http)
        );
        assert_eq!(
            quick_callee_leaf_sym(&m, &links, &ps, f_m1, v_phi_method),
            Some(s_do_work)
        );
        assert!(ps.ns_memo.borrow().contains_key(&(f_m1, phi_vid)));
        assert_eq!(
            quick_callee_leaf_sym(&m, &links, &ps, f_m1, v_aliased_call),
            None,
            "internal namespace member must defer to full resolution because aliasedFn -> realSecretFn"
        );

        let cands = callee_name_candidates_indexed(&m, &links, Some(&ps), f_m1, v_aliased_call);
        assert!(
            cands.iter().any(|c| c == "realSecretFn"),
            "cands: {cands:?}"
        );
        assert!(
            ps.callee_memo
                .borrow()
                .contains_key(&(f_m1, v_aliased_call))
        );
        let cands_cached =
            callee_name_candidates_indexed(&m, &links, Some(&ps), f_m1, v_aliased_call);
        assert_eq!(cands, cands_cached);
    }
}
