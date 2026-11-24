//! OpenHarmony Stage/FA lifecycle and entry-point harness synthesis (#27 Phase 2).
//!
//! Models implicit framework entry points (`UIAbility`, `Ability`,
//! `*ExtensionAbility`, `AbilityStage`, and ArkUI `ViewPU` / `View` components)
//! as well as multi-record ES module initialization order (`func_main_0`) by
//! synthesizing a deterministic SSA harness function (`__abcd_ohos_harness__`)
//! on a cloned [`Module`]:
//!
//! 1. **Per-component concrete receiver allocation**: each discovered component
//!    class gets its own `Op::AllocObject` instance site (`this` is bound to a
//!    concrete abstract object rather than `Obj::Unknown`), with an initialized
//!    `this.context` object on Ability/Extension instances so `this.context.*`
//!    calls (`startAbility`, `startAbilityForResult`, etc.) resolve cleanly.
//! 2. **Framework-supplied parameters**: Ability/Extension lifecycle hooks
//!    (`onCreate(want, launchParam)`, `onNewWant(want, launchParam)`,
//!    `onShare(wantParam)`, `onContinue(wantParam)`, `onRequest`, `onConnect`,
//!    `onAddForm`, `onWorkStart`) receive concrete `Want` / parameter objects
//!    loaded from the synthetic `"__ohos_want__"` global marker so `@ohos`
//!    taint presets can seed `want` (and `want.parameters` / `want.uri`) without
//!    affecting unrelated user functions.
//! 3. **Zero single-module perturbation**: plain single-record JS modules with
//!    no multi-record ES imports and no OpenHarmony component classes return
//!    `None`, leaving existing single-module call-graph and taint runs
//!    untouched.

use std::collections::{BTreeMap, BTreeSet};

use abcd_ir::ValueDef;
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, ConstId, FuncId, InstId, Sym, ValueId};
use abcd_ir::module::{FunctionKind, Modifiers, Module};
use abcd_ir::op::{CallKind, Op};
use abcd_ir::ty::Ty;

use crate::module_link::ModuleLinkTable;

/// Synthetic global marker loaded to represent framework-supplied `Want`
/// objects passed into Ability / ExtensionAbility lifecycle callbacks.
pub const OHOS_WANT_GLOBAL: &str = "__ohos_want__";

/// Synthetic global marker loaded to represent `UIAbilityContext` /
/// `ExtensionContext` attached to `this.context` on Ability instances.
pub const OHOS_CONTEXT_GLOBAL: &str = "__ohos_ability_context__";

/// Synthetic harness function name appended to augmented modules.
pub const OHOS_HARNESS_FUNC: &str = "__abcd_ohos_harness__";

/// Classification of an OpenHarmony framework component class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OhosComponentKind {
    /// `UIAbility` / `Ability` / `AbilityStage`.
    Ability,
    /// `*ExtensionAbility` (`FormExtensionAbility`, `WorkSchedulerExtensionAbility`,
    /// `ServiceExtensionAbility`, `UIExtensionAbility`, `BackupExtensionAbility`, …).
    ExtensionAbility,
    /// Declarative ArkUI component (`ViewPU` / `View`).
    ArkUiView,
}

/// Discovered OpenHarmony component class and its lifecycle/member methods.
#[derive(Clone, Debug)]
pub struct DiscoveredComponent {
    /// Owning record `ClassId`.
    pub class_id: ClassId,
    /// Constructor `FuncId`.
    pub ctor: FuncId,
    /// Component kind.
    pub kind: OhosComponentKind,
    /// Method name → `FuncId`s (from `DefineClass.members` and prototype stores).
    pub methods: BTreeMap<String, Vec<FuncId>>,
}

/// Lifecycle methods invoked in deterministic order on `UIAbility` / `Ability` /
/// `AbilityStage` instances, paired with whether the first parameter is a `Want`.
const ABILITY_LIFECYCLE: &[(&str, bool, usize)] = &[
    ("onCreate", true, 2),
    ("onAcceptWant", true, 1),
    ("onWindowStageCreate", false, 1),
    ("onWindowStageRestore", false, 1),
    ("onForeground", false, 0),
    ("onNewWant", true, 2),
    ("onShare", true, 1),
    ("onContinue", true, 1),
    ("onSaveState", true, 2),
    ("onBackground", false, 0),
    ("onWindowStageDestroy", false, 0),
    ("onDestroy", false, 0),
];

/// Lifecycle callbacks invoked on `*ExtensionAbility` instances.
const EXTENSION_LIFECYCLE: &[(&str, bool, usize)] = &[
    ("onCreate", true, 1),
    ("onRequest", true, 2),
    ("onConnect", true, 1),
    ("onAddForm", true, 1),
    ("onCastToNormalForm", false, 1),
    ("onUpdateForm", false, 1),
    ("onFormEvent", false, 2),
    ("onWorkStart", true, 1),
    ("onWorkStop", true, 1),
    ("onReceive", true, 1),
    ("onSessionCreate", true, 2),
    ("onBackup", false, 0),
    ("onRestore", false, 1),
    ("onDisconnect", true, 1),
    ("onDestroy", false, 0),
];

/// Lifecycle and render methods invoked on ArkUI `ViewPU` / `View` instances.
const ARKUI_LIFECYCLE: &[&str] = &[
    "aboutToAppear",
    "onPageShow",
    "initialRender",
    "onBackPress",
    "onPageHide",
    "aboutToDisappear",
];

/// Extract `srcEntry` record hints from a Stage-model `module.json` or FA-model
/// `config.json` text payload (`"srcEntry": "./ets/entryability/EntryAbility.ets"`).
pub fn parse_manifest_src_entries(manifest_json: &str) -> BTreeSet<String> {
    let mut entries = BTreeSet::new();
    for key in ["\"srcEntry\"", "\"srcPath\""] {
        let mut rest = manifest_json;
        while let Some(pos) = rest.find(key) {
            rest = &rest[pos + key.len()..];
            let trimmed = rest.trim_start();
            let Some(after_colon) = trimmed.strip_prefix(':') else {
                continue;
            };
            let after_colon = after_colon.trim_start();
            let Some(after_quote) = after_colon.strip_prefix('"') else {
                continue;
            };
            if let Some(end_q) = after_quote.find('"') {
                let raw = &after_quote[..end_q];
                let clean = raw
                    .trim_start_matches("./")
                    .trim_start_matches('/')
                    .trim_end_matches(".ets")
                    .trim_end_matches(".ts")
                    .trim_end_matches(".js");
                if !clean.is_empty() {
                    entries.insert(clean.to_owned());
                }
                rest = &after_quote[end_q + 1..];
            }
        }
    }
    entries
}

/// Discover all OpenHarmony Ability, ExtensionAbility, and ArkUI `ViewPU`/`View`
/// component classes inside `module`.
pub fn discover_components(
    module: &Module,
    links: &ModuleLinkTable,
    manifest_json: Option<&str>,
) -> Vec<DiscoveredComponent> {
    let manifest_entries = manifest_json
        .map(parse_manifest_src_entries)
        .unwrap_or_default();

    let mut out = Vec::new();
    let mut seen_ctors = BTreeSet::new();

    for (fi, f) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        let cid = f.class_id;

        // Track `<cls_val>.prototype` in this function so prototype-overflow
        // methods (`proto.onCreate = ...`, `proto.initialRender = ...`) join
        // the component's method table.
        let mut class_defs: Vec<(ValueId, FuncId, Option<ValueId>, ConstId)> = Vec::new();
        let mut proto_to_cls: BTreeMap<ValueId, ValueId> = BTreeMap::new();
        let mut extra_methods: BTreeMap<ValueId, Vec<(String, FuncId)>> = BTreeMap::new();

        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::DefineClass {
                        ctor,
                        heritage,
                        members,
                        ..
                    }
                    | Op::DefineSendableClass {
                        ctor,
                        heritage,
                        members,
                        ..
                    } => {
                        if let Some(res) = inst.result {
                            class_defs.push((res, *ctor, *heritage, *members));
                        }
                    }
                    Op::LoadProp { object, name } if sym_str(module, *name) == "prototype" => {
                        let root = peel_mov(module, *object);
                        if class_defs.iter().any(|(cv, _, _, _)| *cv == root)
                            && let Some(res) = inst.result
                        {
                            proto_to_cls.insert(res, root);
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
                    } => {
                        let root_obj = peel_mov(module, *object);
                        if let Some(&cls_val) = proto_to_cls.get(&root_obj)
                            && let Some(mfid) = peel_closure_func(module, *value)
                        {
                            let mname = sym_str(module, *name);
                            if !mname.is_empty() && !mname.starts_with("#~@") {
                                extra_methods
                                    .entry(cls_val)
                                    .or_default()
                                    .push((mname.to_owned(), mfid));
                            }
                        }
                    }
                    Op::DefineMethod {
                        object, name, func, ..
                    } => {
                        let root_obj = peel_mov(module, *object);
                        if let Some(&cls_val) = proto_to_cls.get(&root_obj)
                            && let Some(mfid) = peel_closure_func(module, *func)
                        {
                            let mname = sym_str(module, *name);
                            if !mname.is_empty() && !mname.starts_with("#~@") {
                                extra_methods
                                    .entry(cls_val)
                                    .or_default()
                                    .push((mname.to_owned(), mfid));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let record_desc = sym_str(module, module.classes[cid.index()].descriptor);
        let in_manifest = manifest_entries
            .iter()
            .any(|e| record_desc.contains(e.as_str()));

        for (cls_val, ctor, heritage, members) in class_defs {
            if !seen_ctors.insert(ctor) {
                continue;
            }
            let mut methods = collect_member_methods(module, members);
            if let Some(extras) = extra_methods.get(&cls_val) {
                for (mname, mfid) in extras {
                    let list = methods.entry(mname.clone()).or_default();
                    if !list.contains(mfid) {
                        list.push(*mfid);
                    }
                }
            }

            let heritage_kind = heritage.and_then(|h| classify_heritage(module, links, fid, h));
            let inferred_kind =
                heritage_kind.or_else(|| infer_kind_from_methods(&methods, in_manifest));
            if let Some(kind) = inferred_kind {
                out.push(DiscoveredComponent {
                    class_id: cid,
                    ctor,
                    kind,
                    methods,
                });
            }
        }
    }

    out
}

/// Synthesize a deterministic entry-point & lifecycle harness function onto a
/// cloned [`Module`] when `module` contains either:
/// - `>= 2` `func_main_0` module initializers (cross-record `--merge-abc` /
///   merged multi-`.abc` containers), or
/// - `>= 1` OpenHarmony Ability, ExtensionAbility, or ArkUI `ViewPU` / `View`
///   component class.
///
/// Returns `None` for ordinary single-module JS inputs so single-module
/// analyses incur zero cloning or call-site changes.
pub fn synthesize_ohos_harness(
    module: &Module,
    manifest_json: Option<&str>,
) -> Option<(Module, FuncId)> {
    let links = ModuleLinkTable::build(module);
    let components = discover_components(module, &links, manifest_json);
    let init_funcs = links.init_order();
    if components.is_empty() && init_funcs.len() <= 1 {
        return None;
    }

    let mut m = module.clone();
    if m.classes.is_empty() {
        return None;
    }
    let host_cid = ClassId::new(0);
    let harness_sym = m.sym.intern(OHOS_HARNESS_FUNC);
    let harness_fid = FuncId::new(m.functions.len() as u32);
    let mut hfd = FunctionData::new(host_cid, harness_sym, FunctionKind::Function);
    hfd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    m.functions.push(hfd);
    m.classes[host_cid.index()].methods.push(harness_fid);

    let b = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    if let Some(fd) = m.func_mut(harness_fid) {
        fd.blocks.push(b);
    }
    for idx in 0..3u16 {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(idx),
            ty: Ty::Any,
        });
        if let Some(fd) = m.func_mut(harness_fid) {
            fd.params.push(vid);
        }
    }

    let undef_cid = m.consts.push(Const::Undefined);
    let undef_val = emit_inst_val(&mut m, b, Op::LoadConst(undef_cid));
    let empty_shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });

    // 1. Run top-level `func_main_0` initializers in topological order so
    //    cross-module `StoreModuleVar` exports and prototype methods initialize
    //    before importers and lifecycle hooks execute.
    for &init_fid in init_funcs {
        let mref = m.consts.push(Const::MethodRef(init_fid));
        let callee = emit_inst_val(&mut m, b, Op::LoadConst(mref));
        let _ = emit_inst_val(
            &mut m,
            b,
            Op::Call {
                callee,
                this: Some(undef_val),
                args: Vec::new(),
                kind: CallKind::Direct,
            },
        );
    }

    // 2. Materialize framework-supplied `Want` and `UIAbilityContext` values
    //    when any Ability or ExtensionAbility component exists.
    let has_ability = components.iter().any(|c| {
        matches!(
            c.kind,
            OhosComponentKind::Ability | OhosComponentKind::ExtensionAbility
        )
    });
    let (want_val, misc_param_val, ctx_sym) = if has_ability {
        let want_sym = m.sym.intern(OHOS_WANT_GLOBAL);
        let w = emit_inst_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: want_sym,
                default: Some(undef_val),
            },
        );
        let p = emit_inst_val(&mut m, b, Op::AllocObject { shape: empty_shape });
        let c_sym = m.sym.intern("context");
        (Some(w), Some(p), Some(c_sym))
    } else {
        (None, None, None)
    };

    // 3. Instantiate each component with a dedicated concrete `AllocObject`
    //    receiver (`this`) and invoke its lifecycle methods in order.
    for comp in &components {
        let inst_obj = emit_inst_val(&mut m, b, Op::AllocObject { shape: empty_shape });

        if matches!(
            comp.kind,
            OhosComponentKind::Ability | OhosComponentKind::ExtensionAbility
        ) && let Some(context_prop) = ctx_sym
        {
            let ctx_marker_sym = m.sym.intern(OHOS_CONTEXT_GLOBAL);
            let ctx_obj = emit_inst_val(
                &mut m,
                b,
                Op::TryGetGlobal {
                    name: ctx_marker_sym,
                    default: Some(undef_val),
                },
            );
            emit_inst_void(
                &mut m,
                b,
                Op::StoreProp {
                    object: inst_obj,
                    name: context_prop,
                    value: ctx_obj,
                },
            );
        }

        // Constructor invocation on `inst_obj`.
        invoke_method(&mut m, b, comp.ctor, inst_obj, &[]);

        match comp.kind {
            OhosComponentKind::Ability => {
                let w = want_val.unwrap_or(undef_val);
                let p = misc_param_val.unwrap_or(undef_val);
                for &(mname, first_is_want, arity) in ABILITY_LIFECYCLE {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            invoke_method(&mut m, b, mfid, inst_obj, &args);
                        }
                    }
                }
            }
            OhosComponentKind::ExtensionAbility => {
                let w = want_val.unwrap_or(undef_val);
                let p = misc_param_val.unwrap_or(undef_val);
                for &(mname, first_is_want, arity) in EXTENSION_LIFECYCLE {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            invoke_method(&mut m, b, mfid, inst_obj, &args);
                        }
                    }
                }
            }
            OhosComponentKind::ArkUiView => {
                for &mname in ARKUI_LIFECYCLE {
                    if let Some(fids) = comp.methods.get(mname) {
                        for &mfid in fids {
                            invoke_method(&mut m, b, mfid, inst_obj, &[]);
                        }
                    }
                }
                // Also invoke custom `@Builder` methods (any non-synthetic method
                // calling `observeComponentCreation*`) with `this = inst_obj`.
                for (mname, fids) in &comp.methods {
                    if ARKUI_LIFECYCLE.contains(&mname.as_str()) {
                        continue;
                    }
                    for &mfid in fids {
                        if func_calls_observe(&m, mfid) {
                            invoke_method(&mut m, b, mfid, inst_obj, &[]);
                        }
                    }
                }
            }
        }
    }

    emit_inst_void(&mut m, b, Op::Return { value: None });
    Some((m, harness_fid))
}

fn build_lifecycle_args(
    arity: usize,
    first_is_want: bool,
    want: ValueId,
    other: ValueId,
) -> Vec<ValueId> {
    let mut args = Vec::with_capacity(arity);
    for i in 0..arity {
        if i == 0 && first_is_want {
            args.push(want);
        } else {
            args.push(other);
        }
    }
    args
}

fn invoke_method(m: &mut Module, b: BlockId, target: FuncId, this_val: ValueId, args: &[ValueId]) {
    let Some(fd) = m.func(target) else { return };
    if fd.is_external || fd.blocks.is_empty() {
        return;
    }
    let mref = m.consts.push(Const::MethodRef(target));
    let callee = emit_inst_val(m, b, Op::LoadConst(mref));
    let _ = emit_inst_val(
        m,
        b,
        Op::Call {
            callee,
            this: Some(this_val),
            args: args.to_vec(),
            kind: CallKind::Direct,
        },
    );
}

fn emit_inst_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    let iid = InstId::new(m.insts.len() as u32);
    let vid = ValueId::new(m.values.len() as u32);
    m.insts.push(Inst {
        op,
        result: Some(vid),
        block: b,
        loc: None,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid),
        ty: Ty::Any,
    });
    if let Some(bb) = m.block_mut(b) {
        bb.insts.push(iid);
    }
    vid
}

fn emit_inst_void(m: &mut Module, b: BlockId, op: Op) {
    let iid = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    if let Some(bb) = m.block_mut(b) {
        bb.insts.push(iid);
    }
}

fn collect_member_methods(module: &Module, members: ConstId) -> BTreeMap<String, Vec<FuncId>> {
    let mut map: BTreeMap<String, Vec<FuncId>> = BTreeMap::new();
    let Some(Const::ArrayLiteral(items)) = module.consts.get(members) else {
        return map;
    };
    let mut pending_name: Option<String> = None;
    for item in items {
        match item {
            Const::String(s) => {
                pending_name = Some(sym_str(module, *s).to_owned());
            }
            Const::MethodRef(fid) => {
                if let Some(name) = pending_name.take()
                    && !name.is_empty()
                {
                    let list = map.entry(name).or_default();
                    if !list.contains(fid) {
                        list.push(*fid);
                    }
                }
            }
            _ => {}
        }
    }
    map
}

fn classify_heritage(
    module: &Module,
    links: &ModuleLinkTable,
    in_func: FuncId,
    heritage: ValueId,
) -> Option<OhosComponentKind> {
    let base_name = resolve_heritage_name(module, links, in_func, heritage)?;
    classify_base_class_name(&base_name)
}

fn classify_base_class_name(name: &str) -> Option<OhosComponentKind> {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    if matches!(leaf, "ViewPU" | "View" | "BaseCustomDialog") {
        return Some(OhosComponentKind::ArkUiView);
    }
    if matches!(leaf, "UIAbility" | "Ability" | "AbilityStage") {
        return Some(OhosComponentKind::Ability);
    }
    if leaf.ends_with("ExtensionAbility") {
        return Some(OhosComponentKind::ExtensionAbility);
    }
    None
}

fn resolve_heritage_name(
    module: &Module,
    links: &ModuleLinkTable,
    in_func: FuncId,
    val: ValueId,
) -> Option<String> {
    let root = peel_mov(module, val);
    let ValueDef::Inst(iid) = module.value(root)?.def else {
        return None;
    };
    match &module.inst(iid)?.op {
        Op::TryGetGlobal { name, .. } => Some(sym_str(module, *name).to_owned()),
        Op::LoadProp { object, name } => {
            let leaf = sym_str(module, *name);
            if classify_base_class_name(leaf).is_some() {
                return Some(leaf.to_owned());
            }
            let prefix = resolve_heritage_name(module, links, in_func, *object)?;
            Some(format!("{prefix}.{leaf}"))
        }
        Op::LoadModuleVar { index, kind } if !kind.is_local() => {
            let cid = links.func_class(in_func)?;
            let target = links.external_load(cid, *index)?;
            for &(spec, imp) in &target.external_imports {
                let imp_s = sym_str(module, imp);
                let spec_s = sym_str(module, spec);
                if imp_s != "default" && classify_base_class_name(imp_s).is_some() {
                    return Some(imp_s.to_owned());
                }
                if let Some(tail) = spec_s.rsplit(['.', ':']).next()
                    && classify_base_class_name(tail).is_some()
                {
                    return Some(tail.to_owned());
                }
            }
            None
        }
        _ => None,
    }
}

fn infer_kind_from_methods(
    methods: &BTreeMap<String, Vec<FuncId>>,
    in_manifest: bool,
) -> Option<OhosComponentKind> {
    if methods.contains_key("initialRender")
        && (methods.contains_key("rerender")
            || methods.contains_key("updateStateVars")
            || methods.contains_key("purgeVariableDependenciesOnElmtId"))
    {
        return Some(OhosComponentKind::ArkUiView);
    }
    if methods.contains_key("onWindowStageCreate") {
        return Some(OhosComponentKind::Ability);
    }
    if in_manifest {
        if methods.contains_key("onAddForm")
            || methods.contains_key("onWorkStart")
            || methods.contains_key("onConnect")
            || methods.contains_key("onRequest")
        {
            return Some(OhosComponentKind::ExtensionAbility);
        }
        if methods.contains_key("onCreate") || methods.contains_key("onForeground") {
            return Some(OhosComponentKind::Ability);
        }
    }
    None
}

fn func_calls_observe(module: &Module, fid: FuncId) -> bool {
    let Some(fd) = module.func(fid) else {
        return false;
    };
    for &b in &fd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            if let Some(Inst {
                op: Op::LoadProp { name, .. },
                ..
            }) = module.inst(iid)
            {
                let s = sym_str(module, *name);
                if s == "observeComponentCreation2" || s == "observeComponentCreation" {
                    return true;
                }
            }
        }
    }
    false
}

fn peel_mov(module: &Module, mut v: ValueId) -> ValueId {
    for _ in 0..16 {
        let Some(ValueDef::Inst(iid)) = module.value(v).map(|val| val.def) else {
            break;
        };
        let Some(Op::Mov { src }) = module.inst(iid).map(|i| &i.op) else {
            break;
        };
        v = *src;
    }
    v
}

fn peel_closure_func(module: &Module, mut v: ValueId) -> Option<FuncId> {
    for _ in 0..16 {
        let ValueDef::Inst(iid) = module.value(v)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::Mov { src }
            | Op::AllocClosure { func: src }
            | Op::DefineMethod { func: src, .. } => {
                v = *src;
            }
            Op::DefineFunc { body, .. } => return Some(*body),
            _ => return None,
        }
    }
    None
}

fn sym_str(module: &Module, sym: Sym) -> &str {
    module.sym.resolve(sym).unwrap_or("")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::CallGraph;
    use crate::dataflow::ifds::CallGraphOracle;
    use crate::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
    use abcd_ir::module::ClassData;
    use abcd_ir::verify::verify_module;

    fn add_fn(
        m: &mut Module,
        cid: ClassId,
        name: &str,
        kind: FunctionKind,
        total_params: u16,
    ) -> (FuncId, BlockId, Vec<ValueId>) {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        let bid = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        fd.blocks.push(bid);
        let mut params = Vec::new();
        for i in 0..total_params {
            let vid = ValueId::new(m.values.len() as u32);
            m.values.push(Value {
                def: ValueDef::Param(i),
                ty: Ty::Any,
            });
            fd.params.push(vid);
            params.push(vid);
        }
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        (fid, bid, params)
    }

    #[test]
    fn plain_single_module_returns_none() {
        let mut m = Module::new();
        let d = m.sym.intern("L_GLOBAL;");
        let n = m.sym.intern("_GLOBAL");
        m.classes.push(ClassData::new(d, n));
        let (_, b, _) = add_fn(
            &mut m,
            ClassId::new(0),
            "func_main_0",
            FunctionKind::Function,
            3,
        );
        emit_inst_void(&mut m, b, Op::Return { value: None });
        assert!(synthesize_ohos_harness(&m, None).is_none());
    }

    #[test]
    fn synthesize_harness_wires_ability_extension_and_viewpu_with_distinct_receivers() {
        let mut m = Module::new();
        let d = m
            .sym
            .intern("L@bundle:com.app/entry/ets/entryability/EntryAbility;");
        let n = m
            .sym
            .intern("@bundle:com.app/entry/ets/entryability/EntryAbility");
        let cid = ClassId::new(0);
        m.classes.push(ClassData::new(d, n));

        // Ability 1: EntryAbility (`ctor`, `onCreate`, `onForeground`)
        let (ctor1, b_c1, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_c1, Op::Return { value: None });
        let (on_create1, b_oc1, p_oc1) = add_fn(&mut m, cid, "onCreate", FunctionKind::Function, 5);
        let s_saved = m.sym.intern("savedWant");
        emit_inst_void(
            &mut m,
            b_oc1,
            Op::StoreProp {
                object: p_oc1[2],
                name: s_saved,
                value: p_oc1[3],
            },
        );
        emit_inst_void(&mut m, b_oc1, Op::Return { value: None });
        let (on_fg1, b_fg1, p_fg1) = add_fn(&mut m, cid, "onForeground", FunctionKind::Function, 3);
        emit_inst_void(&mut m, b_fg1, Op::Return { value: None });
        let fg1_last = m.blocks[b_fg1.index()].insts[0];

        // Ability 2: SecondAbility (`ctor`, `onForeground`) — distinct receiver check!
        let (ctor2, b_c2, _) = add_fn(&mut m, cid, "SecondAbility", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_c2, Op::Return { value: None });
        let (on_fg2, b_fg2, p_fg2) =
            add_fn(&mut m, cid, "onForeground2", FunctionKind::Function, 3);
        emit_inst_void(&mut m, b_fg2, Op::Return { value: None });
        let fg2_last = m.blocks[b_fg2.index()].insts[0];

        // ExtensionAbility: CardExt (`ctor`, `onAddForm`)
        let (ctor3, b_c3, _) = add_fn(&mut m, cid, "CardExt", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_c3, Op::Return { value: None });
        let (on_add, b_add, _) = add_fn(&mut m, cid, "onAddForm", FunctionKind::Function, 4);
        emit_inst_void(&mut m, b_add, Op::Return { value: None });

        // ArkUI ViewPU: HomePage (`ctor`, `aboutToAppear`, `initialRender`, overflow `@Builder`)
        let (ctor4, b_c4, _) = add_fn(&mut m, cid, "HomePage", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_c4, Op::Return { value: None });
        let (about, b_ab, _) = add_fn(&mut m, cid, "aboutToAppear", FunctionKind::Function, 3);
        emit_inst_void(&mut m, b_ab, Op::Return { value: None });
        let (render, b_rn, _) = add_fn(&mut m, cid, "initialRender", FunctionKind::Function, 3);
        emit_inst_void(&mut m, b_rn, Op::Return { value: None });
        let (builder, b_bd, p_bd) = add_fn(&mut m, cid, "HeaderBuilder", FunctionKind::Function, 3);
        let s_obs = m.sym.intern("observeComponentCreation2");
        let _ = emit_inst_val(
            &mut m,
            b_bd,
            Op::LoadProp {
                object: p_bd[2],
                name: s_obs,
            },
        );
        emit_inst_void(&mut m, b_bd, Op::Return { value: None });

        // `func_main_0` defines all 4 classes + attaches `HeaderBuilder` on `HomePage.prototype`.
        let (_, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
        let s_uiab = m.sym.intern("UIAbility");
        let s_form = m.sym.intern("FormExtensionAbility");
        let s_viewpu = m.sym.intern("ViewPU");
        let u_undef = m.consts.push(Const::Undefined);
        let undef = emit_inst_val(&mut m, b_main, Op::LoadConst(u_undef));
        let h_uiab = emit_inst_val(
            &mut m,
            b_main,
            Op::TryGetGlobal {
                name: s_uiab,
                default: Some(undef),
            },
        );
        let h_form = emit_inst_val(
            &mut m,
            b_main,
            Op::TryGetGlobal {
                name: s_form,
                default: Some(undef),
            },
        );
        let h_view = emit_inst_val(
            &mut m,
            b_main,
            Op::TryGetGlobal {
                name: s_viewpu,
                default: Some(undef),
            },
        );

        let s_oc = m.sym.intern("onCreate");
        let s_fg = m.sym.intern("onForeground");
        let s_af = m.sym.intern("onAddForm");
        let s_ata = m.sym.intern("aboutToAppear");
        let s_ir = m.sym.intern("initialRender");
        let s_proto = m.sym.intern("prototype");
        let s_hb = m.sym.intern("HeaderBuilder");

        let mem1 = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(s_oc),
            Const::MethodRef(on_create1),
            Const::String(s_fg),
            Const::MethodRef(on_fg1),
        ]));
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass {
                ctor: ctor1,
                heritage: Some(h_uiab),
                members: mem1,
                member_attrs: Vec::new(),
                count: 0,
            },
        );

        let mem2 = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(s_fg),
            Const::MethodRef(on_fg2),
        ]));
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass {
                ctor: ctor2,
                heritage: Some(h_uiab),
                members: mem2,
                member_attrs: Vec::new(),
                count: 0,
            },
        );

        let mem3 = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(s_af),
            Const::MethodRef(on_add),
        ]));
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass {
                ctor: ctor3,
                heritage: Some(h_form),
                members: mem3,
                member_attrs: Vec::new(),
                count: 0,
            },
        );

        let mem4 = m.consts.push(Const::ArrayLiteral(vec![
            Const::String(s_ata),
            Const::MethodRef(about),
            Const::String(s_ir),
            Const::MethodRef(render),
        ]));
        let home_cls = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass {
                ctor: ctor4,
                heritage: Some(h_view),
                members: mem4,
                member_attrs: Vec::new(),
                count: 0,
            },
        );
        let home_proto = emit_inst_val(
            &mut m,
            b_main,
            Op::LoadProp {
                object: home_cls,
                name: s_proto,
            },
        );
        let df_bd = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: builder,
                captures: Vec::new(),
                length: 0,
            },
        );
        let cl_bd = emit_inst_val(&mut m, b_main, Op::AllocClosure { func: df_bd });
        emit_inst_void(
            &mut m,
            b_main,
            Op::StoreProp {
                object: home_proto,
                name: s_hb,
                value: cl_bd,
            },
        );
        emit_inst_void(&mut m, b_main, Op::Return { value: None });

        let manifest =
            r#"{"module":{"abilities":[{"srcEntry":"./ets/entryability/EntryAbility.ets"}]}}"#;
        let entries = parse_manifest_src_entries(manifest);
        assert!(entries.contains("ets/entryability/EntryAbility"));

        let (aug, _harness_fid) = synthesize_ohos_harness(&m, Some(manifest)).expect("harness");
        let rep = verify_module(&aug);
        assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

        let cg = CallGraph::build(&aug);
        for target in [on_create1, on_fg1, on_fg2, on_add, about, render, builder] {
            assert!(
                !cg.callers_of(target).is_empty(),
                "expected harness to call {target:?}"
            );
        }

        // Verify Rung 2 PTA assigns non-overlapping concrete `AllocObject` sites
        // to `EntryAbility.this` vs `SecondAbility.this`.
        let outcome = analyze(&aug, &cg, &PtaConfig::default());
        let (_, tables, stats) = outcome.into_parts();
        let r2 = Rung2AliasOracle::new(&aug, tables, stats);
        let this1 = r2.site_info_at(p_fg1[2], fg1_last);
        let this2 = r2.site_info_at(p_fg2[2], fg2_last);
        assert!(!this1.has_unknown && this1.sites.len() == 1);
        assert!(!this2.has_unknown && this2.sites.len() == 1);
        assert!(!this1.sites.intersects(&this2.sites));
    }
}
