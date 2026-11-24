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

use std::collections::HashSet;

use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_analysis::ohos_lifecycle::OHOS_CONTEXT_GLOBAL;
use abcd_ir::{CallKind, ClassId, Const, FuncId, Module, Op, Sym, ValueDef, ValueId};

/// All candidate names for a callee value, most-qualified first, in
/// deterministic def-chain order. Recursion is cycle-guarded.
pub fn callee_name_candidates(module: &Module, callee: ValueId) -> Vec<String> {
    let links = ModuleLinkTable::build(module);
    let caller = owner_func_of_value(module, callee).unwrap_or(FuncId::new(0));
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
    let mut out = Vec::new();
    let mut visiting = HashSet::new();
    resolve_into(module, Some(links), caller, callee, &mut visiting, &mut out);
    out
}

/// The recursive worker.
fn resolve_into(
    module: &Module,
    links: Option<&ModuleLinkTable>,
    func: FuncId,
    value: ValueId,
    visiting: &mut HashSet<(FuncId, ValueId)>,
    out: &mut Vec<String>,
) {
    if !visiting.insert((func, value)) {
        return;
    }
    let Some(v) = module.value(value) else {
        return;
    };
    if let ValueDef::Inst(iid) = v.def {
        match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src })
            | Some(Op::Await { value: src })
            | Some(Op::AwaitUncaught { value: src, .. }) => {
                resolve_into(module, links, func, *src, visiting, out);
            }
            Some(Op::ResumeGenerator { genobj }) => {
                // Pair async-machine `AwaitUncaught(funcobj, awaited)` -> `ResumeGenerator(funcobj)`
                // so `const rdb = await relationalStore.getRdbStore(...); rdb.executeSql(...)`
                // preserves receiver provenance across `await`.
                if let Some(inst) = module.inst(iid)
                    && let Some(bb) = module.block(inst.block)
                {
                    for &prev_iid in &bb.insts {
                        if prev_iid == iid {
                            break;
                        }
                        if let Some(Op::AwaitUncaught { funcobj, value }) =
                            module.inst(prev_iid).map(|i| &i.op)
                            && funcobj == genobj
                        {
                            resolve_into(module, links, func, *value, visiting, out);
                        }
                    }
                }
            }
            Some(Op::Phi { entries }) => {
                for (_, incoming) in entries {
                    resolve_into(module, links, func, *incoming, visiting, out);
                }
            }
            Some(Op::TryGetGlobal { name, .. }) => {
                if let Some(s) = module.sym.resolve(*name) {
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
                            for &(def_fn, def_val) in links.stored_values(ModuleSlotRef {
                                class_id: cid,
                                slot: *index,
                            }) {
                                resolve_into(module, Some(links), def_fn, def_val, visiting, out);
                            }
                        }
                    } else if let Some(target) = links.external_load(cid, *index) {
                        for &(spec_sym, imp_sym) in &target.external_imports {
                            let raw_spec = module.sym.resolve(spec_sym).unwrap_or("");
                            let imp = module.sym.resolve(imp_sym).unwrap_or("");
                            emit_external_import_names(raw_spec, imp, out);
                        }
                        for &slot_ref in &target.slots {
                            for &(def_fn, def_val) in links.stored_values(slot_ref) {
                                resolve_into(module, Some(links), def_fn, def_val, visiting, out);
                            }
                        }
                    }
                }
            }
            Some(Op::GetModuleNamespace { index }) => {
                if let Some(links) = links
                    && let Some(cid) = links.func_class(func)
                    && let Some(ext_sym) = links.namespace_external(cid, *index)
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
                    if is_viewpu_intrinsic(leaf) {
                        push_unique(out, format!("ViewPU.{leaf}"));
                    }
                    // Internal namespace member: `import * as ns from "./lib"; ns.foo()`.
                    if let Some(links) = links
                        && let Some(cid) = links.func_class(func)
                        && let Some(req_idx) = peel_namespace_index(module, *object)
                        && let Some(slots) = links.resolve_namespace_member(cid, req_idx, *name)
                    {
                        for &sr in slots {
                            for &(def_fn, def_val) in links.stored_values(sr) {
                                resolve_into(module, Some(links), def_fn, def_val, visiting, out);
                            }
                        }
                    }

                    let mut prefix = Vec::new();
                    resolve_into(module, links, func, *object, visiting, &mut prefix);

                    // `this.context` on Ability/Extension instances or SDK receivers
                    // stored into component instance fields (`this.controller = new webview.WebviewController()`):
                    // these already include `leaf`, so push directly into `out`.
                    if prefix.is_empty() {
                        if leaf == "context" && is_this_or_lex_receiver(module, *object) {
                            push_unique(out, "UIAbilityContext".to_owned());
                        } else if let Some(cid) = links
                            .and_then(|l| l.func_class(func))
                            .or_else(|| module.func(func).map(|f| f.class_id))
                        {
                            collect_sdk_field_prefixes(module, links, cid, *name, visiting, out);
                        }
                    }

                    for base in &prefix {
                        if let Some(canon) = kit_canonical_alias(base, leaf) {
                            push_unique(out, canon.to_owned());
                        }
                        push_unique(out, format!("{base}.{leaf}"));
                    }
                }
            }
            Some(Op::Call { callee, kind, .. }) => {
                let mut callee_names = Vec::new();
                resolve_into(module, links, func, *callee, visiting, &mut callee_names);
                if *kind == CallKind::New {
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
            Some(Op::LoadConst(c)) => {
                if let Some(Const::MethodRef(f)) = module.consts.get(*c)
                    && let Some(fd) = module.func(*f)
                    && let Some(s) = module.sym.resolve(fd.name)
                {
                    push_unique(out, s.to_owned());
                }
            }
            Some(Op::DefineFunc { body, .. }) => {
                if let Some(fd) = module.func(*body)
                    && let Some(s) = module.sym.resolve(fd.name)
                {
                    push_unique(out, s.to_owned());
                }
            }
            Some(Op::AllocClosure { func: inner }) | Some(Op::CreateGenerator { func: inner }) => {
                resolve_into(module, links, func, *inner, visiting, out);
            }
            _ => {}
        }
    }
}

fn owner_func_of_value(module: &Module, val: ValueId) -> Option<FuncId> {
    let block = match module.value(val)?.def {
        ValueDef::Inst(iid) => module.inst(iid)?.block,
        ValueDef::ExceptionParam(b) => b,
        ValueDef::Param(_) | ValueDef::Const(_) => {
            return module
                .functions
                .iter()
                .position(|f| f.params.contains(&val))
                .map(|i| FuncId::new(i as u32));
        }
    };
    module
        .functions
        .iter()
        .position(|f| f.blocks.contains(&block))
        .map(|i| FuncId::new(i as u32))
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

/// Scan property writes to `prop_name` within `cid` for SDK-typed receiver
/// instances (e.g. `this.controller = new webview.WebviewController()`).
/// Strictly gated to `@ohos.*` / `@kit.*` / `UIAbilityContext` prefixes so
/// ordinary JS objects are never affected.
fn collect_sdk_field_prefixes(
    module: &Module,
    links: Option<&ModuleLinkTable>,
    cid: ClassId,
    prop_name: Sym,
    visiting: &mut HashSet<(FuncId, ValueId)>,
    out: &mut Vec<String>,
) {
    let Some(cls) = module.classes.get(cid.index()) else {
        return;
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
                    let mut sub = Vec::new();
                    resolve_into(module, links, mfid, *value, visiting, &mut sub);
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
        }
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
    let mut visiting = std::collections::HashSet::new();
    base_through_movs(module, *callee, &mut visiting)
}

fn base_through_movs(
    module: &Module,
    value: ValueId,
    visiting: &mut std::collections::HashSet<ValueId>,
) -> Option<ValueId> {
    if !visiting.insert(value) {
        return None;
    }
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::Mov { src } => base_through_movs(module, *src, visiting),
        // Loop rotation: the callee phi merges the pre-loop LoadProp
        // with the phi itself; every entry reaches the same LoadProp
        // in that shape (first-found is exact there, may otherwise).
        Op::Phi { entries } => entries
            .iter()
            .find_map(|(_, incoming)| base_through_movs(module, *incoming, visiting)),
        Op::LoadProp { object, .. } => Some(*object),
        _ => None,
    }
}

/// The method leaf of a call whose callee came through a `LoadProp`
/// chain: `a.pop(...)` → `"pop"`. This is the key the prototype
/// resolution path (t-P3, `crate::prototype`) qualifies with the
/// receiver's family — `TryGetGlobal("a").pop` + receiver family
/// `Array` ⇒ candidate `Array.prototype.pop`. Returns `None` when the
/// callee is not a property load (bare global calls, direct calls).
pub fn call_method_leaf(module: &Module, call: &abcd_ir::Inst) -> Option<Sym> {
    let Op::Call { callee, .. } = &call.op else {
        return None;
    };
    let mut visiting = std::collections::HashSet::new();
    leaf_through_movs(module, *callee, &mut visiting)
}

fn leaf_through_movs(
    module: &Module,
    value: ValueId,
    visiting: &mut std::collections::HashSet<ValueId>,
) -> Option<Sym> {
    if !visiting.insert(value) {
        return None;
    }
    let v = module.value(value)?;
    let ValueDef::Inst(iid) = v.def else {
        return None;
    };
    match module.inst(iid).map(|i| &i.op)? {
        Op::Mov { src } => leaf_through_movs(module, *src, visiting),
        // Loop-rotated method calls: the callee phi merges the
        // pre-loop LoadProp with the phi itself (for-of's `next`).
        Op::Phi { entries } => entries
            .iter()
            .find_map(|(_, incoming)| leaf_through_movs(module, *incoming, visiting)),
        Op::LoadProp { name, .. } => Some(*name),
        _ => None,
    }
}
