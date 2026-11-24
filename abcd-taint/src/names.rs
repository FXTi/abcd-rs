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

use std::collections::{HashMap, HashSet};

use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_analysis::ohos_lifecycle::OHOS_CONTEXT_GLOBAL;
use abcd_ir::{CallKind, ClassId, Const, FuncId, Module, Op, Sym, ValueDef, ValueId};

/// Pre-indexed `(ClassId, prop_name)` -> `(method FuncId, stored ValueId)` table
/// so SDK receiver field lookups (`this.controller = new WebviewController()`)
/// run in `O(1)` per property access instead of rescanning class bodies.
#[derive(Clone, Debug, Default)]
pub(crate) struct ClassPropStores {
    by_class_prop: HashMap<(ClassId, Sym), Vec<(FuncId, ValueId)>>,
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
        Self { by_class_prop }
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
                let Const::MethodRef(body) = module.consts.get(c)? else {
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
                    let Const::MethodRef(body) = module.consts.get(*c)? else {
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
                    if peel_namespace_index(module, *object).is_some() {
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

/// Iterative def-chain name resolver (zero call-stack recursion).
fn resolve_iterative(
    module: &Module,
    links: Option<&ModuleLinkTable>,
    prop_stores: Option<&ClassPropStores>,
    root_func: FuncId,
    root_value: ValueId,
) -> Vec<String> {
    let mut visiting: HashSet<(FuncId, ValueId)> = HashSet::new();
    let mut bufs: Vec<Vec<String>> = vec![Vec::new()];
    let mut stack: Vec<ResolveStep> = vec![ResolveStep::Enter {
        func: root_func,
        value: root_value,
    }];

    while let Some(step) = stack.pop() {
        match step {
            ResolveStep::Enter { func, value } => {
                if !visiting.insert((func, value)) {
                    continue;
                }
                let Some(v) = module.value(value) else {
                    continue;
                };
                let ValueDef::Inst(iid) = v.def else {
                    continue;
                };
                match module.inst(iid).map(|i| &i.op) {
                    Some(Op::Mov { src })
                    | Some(Op::Await { value: src })
                    | Some(Op::AwaitUncaught { value: src, .. }) => {
                        stack.push(ResolveStep::Enter { func, value: *src });
                    }
                    Some(Op::ResumeGenerator { genobj }) => {
                        // Pair async-machine `AwaitUncaught(funcobj, awaited)` -> `ResumeGenerator(funcobj)`
                        // so `const rdb = await relationalStore.getRdbStore(...); rdb.executeSql(...)`
                        // preserves receiver provenance across `await`.
                        if let Some(inst) = module.inst(iid)
                            && let Some(bb) = module.block(inst.block)
                        {
                            let mut awaited_vals = Vec::new();
                            for &prev_iid in &bb.insts {
                                if prev_iid == iid {
                                    break;
                                }
                                if let Some(Op::AwaitUncaught { funcobj, value }) =
                                    module.inst(prev_iid).map(|i| &i.op)
                                    && funcobj == genobj
                                {
                                    awaited_vals.push(*value);
                                }
                            }
                            for val in awaited_vals.into_iter().rev() {
                                stack.push(ResolveStep::Enter { func, value: val });
                            }
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
                            // Internal namespace member: `import * as ns from "./lib"; ns.foo()`.
                            if let Some(links) = links
                                && let Some(cid) = links.func_class(func)
                                && let Some(req_idx) = peel_namespace_index(module, *object)
                                && let Some(slots) =
                                    links.resolve_namespace_member(cid, req_idx, *name)
                            {
                                let mut ns_defs = Vec::new();
                                for &sr in slots {
                                    for &(def_fn, def_val) in links.stored_values(sr) {
                                        ns_defs.push((def_fn, def_val));
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
                        bufs.push(Vec::new());
                        stack.push(ResolveStep::FinishCall { kind: *kind });
                        stack.push(ResolveStep::Enter {
                            func,
                            value: *callee,
                        });
                    }
                    Some(Op::LoadConst(c)) => {
                        if let Some(Const::MethodRef(f)) = module.consts.get(*c)
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
                    | Some(Op::CreateGenerator { func: inner }) => {
                        stack.push(ResolveStep::Enter {
                            func,
                            value: *inner,
                        });
                    }
                    _ => {}
                }
            }
            ResolveStep::StartObjectPrefix { func, object, name } => {
                bufs.push(Vec::new());
                stack.push(ResolveStep::FinishObjectPrefix { func, object, name });
                stack.push(ResolveStep::Enter {
                    func,
                    value: object,
                });
            }
            ResolveStep::FinishObjectPrefix { func, object, name } => {
                let prefix = bufs.pop().unwrap_or_default();
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
                bufs.push(Vec::new());
                stack.push(ResolveStep::FinishSdkStore);
                stack.push(ResolveStep::Enter { func, value });
            }
            ResolveStep::FinishSdkStore => {
                let sub = bufs.pop().unwrap_or_default();
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
                if let Some(out) = bufs.last_mut() {
                    if kind == CallKind::New {
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

fn peel_namespace_index(module: &Module, mut v: ValueId) -> Option<u32> {
    for _ in 0..8 {
        let ValueDef::Inst(iid) = module.value(v)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::Mov { src } => v = *src,
            Op::GetModuleNamespace { index } => return Some(*index),
            _ => return None,
        }
    }
    None
}

fn is_this_or_lex_receiver(module: &Module, mut v: ValueId) -> bool {
    for _ in 0..8 {
        let Some(val) = module.value(v) else {
            return false;
        };
        match val.def {
            ValueDef::Param(_) => return true,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => v = *src,
                Some(Op::GetLexVar { .. }) => return true,
                _ => return false,
            },
            _ => return false,
        }
    }
    false
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

/// Normalize `@ohos:foo` -> `@ohos.foo` and `@system:foo` -> `@system.foo`.
pub fn normalize_sdk_specifier(raw: &str) -> String {
    if let Some(rest) = raw.strip_prefix("@ohos:") {
        return format!("@ohos.{rest}");
    }
    if let Some(rest) = raw.strip_prefix("@system:") {
        return format!("@system.{rest}");
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

/// The base (receiver) value of a call: the explicit `this`, or — for
/// the `obj.m()` shape where `Dynamic` calls carry no `this` — the
/// object of the `LoadProp` that produced the callee value.
pub fn call_base_value(module: &Module, call: &abcd_ir::Inst) -> Option<ValueId> {
    let Op::Call { callee, this, .. } = &call.op else {
        return None;
    };
    if let Some(t) = this {
        return Some(*t);
    }
    base_through_movs(module, *callee)
}

fn base_through_movs(module: &Module, value: ValueId) -> Option<ValueId> {
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::LoadProp { object, .. } => return Some(*object),
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
            // Loop rotation: the callee phi merges the pre-loop LoadProp
            // with the phi itself; every entry reaches the same LoadProp
            // in that shape (first-found is exact there, may otherwise).
            Op::Phi { entries } => {
                for (_, incoming) in entries.iter().rev() {
                    stack.push(*incoming);
                }
            }
            Op::LoadProp { object, .. } => return Some(*object),
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
