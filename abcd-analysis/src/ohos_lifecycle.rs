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
use abcd_ir::function::{Block, Edge, EdgeKind, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, ConstId, FuncId, InstId, Sym, ValueId};
use abcd_ir::module::{FunctionKind, Modifiers, Module};
use abcd_ir::op::{CallKind, Op};
use abcd_ir::ty::Ty;

use crate::dataflow::heap::peel_movs;
use crate::module_link::ModuleLinkTable;

/// Synthetic global marker loaded to represent framework-supplied `Want`
/// objects passed into Ability / ExtensionAbility lifecycle callbacks.
pub const OHOS_WANT_GLOBAL: &str = "__ohos_want__";

/// Synthetic global marker loaded to represent `UIAbilityContext` /
/// `ExtensionContext` attached to `this.context` on Ability instances.
pub const OHOS_CONTEXT_GLOBAL: &str = "__ohos_ability_context__";

/// Synthetic global condition marker driving non-deterministic dispatch in
/// [`OHOS_HARNESS_FUNC`]'s steady-state lifecycle loop.
pub const OHOS_LIFECYCLE_COND_GLOBAL: &str = "__ohos_lifecycle_cond__";

/// Synthetic harness function name appended to augmented modules.
pub const OHOS_HARNESS_FUNC: &str = "__abcd_ohos_harness__";

/// Explicit OpenHarmony and multi-record entry-point model (`D3`, `#94`).
///
/// Exposes [`Self::harness_func`] and [`Self::entry_funcs`] directly so
/// downstream call-graph, PTA, and taint drivers never need to string-match
/// [`OHOS_HARNESS_FUNC`].
#[derive(Clone, Debug)]
pub struct EntryModel {
    /// Cloned module augmented with [`Self::harness_func`] when multi-record
    /// initializers (`> 1`) or OpenHarmony components exist; `None` for plain
    /// single-record modules.
    pub augmented_module: Option<Module>,
    /// Synthesized lifecycle harness `FuncId` inside [`Self::augmented_module`],
    /// when synthesized.
    pub harness_func: Option<FuncId>,
    /// Topological `func_main_0` module initializer sequence.
    pub init_funcs: Vec<FuncId>,
    /// Discovered OpenHarmony Ability, ExtensionAbility, and ArkUI components.
    pub components: Vec<DiscoveredComponent>,
    /// Effective root entry functions (`[harness_func]` when synthesized, else
    /// top-level initializers / entry functions in `module`).
    pub entry_funcs: Vec<FuncId>,
}

impl EntryModel {
    /// Discover module initializers and OpenHarmony components in `module` and
    /// synthesize the lifecycle harness (with creation, steady-state `while (*)`
    /// callback dispatch loop, and teardown phases) when needed.
    #[must_use]
    pub fn build(module: &Module, manifest_json: Option<&str>) -> Self {
        build_entry_model(module, manifest_json)
    }

    /// Borrow [`Self::augmented_module`] when present, or fall back to `original`.
    #[must_use]
    pub fn active_module<'a>(&'a self, original: &'a Module) -> &'a Module {
        self.augmented_module.as_ref().unwrap_or(original)
    }
}

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

/// Creation-phase callbacks on `UIAbility` / `Ability` / `AbilityStage`
/// instances, paired with `(first_is_want, arity)`.
const ABILITY_CREATE: &[(&str, bool, usize)] = &[
    ("onCreate", true, 2),
    ("onAcceptWant", true, 1),
    ("onWindowStageCreate", false, 1),
    ("onWindowStageRestore", false, 1),
];

/// Steady-state re-entrant callbacks dispatched inside `while (*)` on
/// `UIAbility` / `Ability` / `AbilityStage` instances (`D3`, `#94`).
const ABILITY_STEADY: &[(&str, bool, usize)] = &[
    ("onForeground", false, 0),
    ("onNewWant", true, 2),
    ("onShare", true, 1),
    ("onContinue", true, 1),
    ("onSaveState", true, 2),
    ("onBackground", false, 0),
];

/// Teardown-phase callbacks on `UIAbility` / `Ability` / `AbilityStage`.
const ABILITY_TEARDOWN: &[(&str, bool, usize)] =
    &[("onWindowStageDestroy", false, 0), ("onDestroy", false, 0)];

/// Creation-phase callbacks on `*ExtensionAbility` instances.
const EXTENSION_CREATE: &[(&str, bool, usize)] = &[("onCreate", true, 1)];

/// Steady-state re-entrant callbacks dispatched inside `while (*)` on
/// `*ExtensionAbility` instances (`D3`, `#94`).
const EXTENSION_STEADY: &[(&str, bool, usize)] = &[
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
];

/// Teardown-phase callbacks on `*ExtensionAbility` instances.
const EXTENSION_TEARDOWN: &[(&str, bool, usize)] = &[("onDestroy", false, 0)];

/// Creation-phase hooks on ArkUI `ViewPU` / `View` instances.
const ARKUI_CREATE: &[&str] = &["aboutToAppear"];

/// Steady-state render/page hooks dispatched inside `while (*)` on ArkUI
/// `ViewPU` / `View` instances (`D3`, `#94`).
const ARKUI_STEADY: &[&str] = &[
    "onPageShow",
    "initialRender",
    "build",
    "rerender",
    "updateStateVars",
    "onBackPress",
    "onPageHide",
];

/// Teardown-phase hooks on ArkUI `ViewPU` / `View` instances.
const ARKUI_TEARDOWN: &[&str] = &["aboutToDisappear"];

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
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if let Some(res) = inst.result {
                            class_defs.push((res, cls.ctor, cls.heritage, cls.members));
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
                        ..
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

        let record_desc = module
            .class(cid)
            .map_or("", |cls_data| sym_str(module, cls_data.descriptor));
        let in_manifest = manifest_entries
            .iter()
            .any(|e| record_desc.contains(e.as_str()));

        for (cls_val, ctor, heritage, members) in class_defs {
            if module.func(ctor).is_none() || !seen_ctors.insert(ctor) {
                continue;
            }
            let mut methods = collect_member_methods(module, members);
            if let Some(extras) = extra_methods.get(&cls_val) {
                for (mname, mfid) in extras {
                    if module.func(*mfid).is_none() {
                        continue;
                    }
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
///
/// Prefer [`EntryModel::build`] when the caller also needs structured
/// [`EntryModel::harness_func`] / [`EntryModel::entry_funcs`] metadata.
pub fn synthesize_ohos_harness(
    module: &Module,
    manifest_json: Option<&str>,
) -> Option<(Module, FuncId)> {
    let model = EntryModel::build(module, manifest_json);
    model.augmented_module.zip(model.harness_func)
}

fn build_entry_model(module: &Module, manifest_json: Option<&str>) -> EntryModel {
    let links = ModuleLinkTable::build(module);
    let components = discover_components(module, &links, manifest_json);
    let init_funcs = links.init_order().to_vec();
    if components.is_empty() && init_funcs.len() <= 1 {
        let entry_funcs = if init_funcs.is_empty() {
            default_single_module_entries(module)
        } else {
            init_funcs.clone()
        };
        return EntryModel {
            augmented_module: None,
            harness_func: None,
            init_funcs,
            components,
            entry_funcs,
        };
    }

    if module.classes.is_empty() {
        return EntryModel {
            augmented_module: None,
            harness_func: None,
            entry_funcs: init_funcs.clone(),
            init_funcs,
            components,
        };
    }

    let mut m = module.clone();
    let host_cid = m
        .classes
        .iter()
        .position(|c| sym_str(&m, c.descriptor) == "L_GLOBAL;")
        .map_or(ClassId::new(0), |idx| ClassId::new(idx as u32));
    let harness_sym = m.sym.intern(OHOS_HARNESS_FUNC);
    let harness_fid = FuncId::new(m.functions.len() as u32);
    let mut hfd = FunctionData::new(host_cid, harness_sym, FunctionKind::Function);
    hfd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    m.functions.push(hfd);
    if let Some(cls) = m.classes.get_mut(host_cid.index()) {
        cls.methods.push(harness_fid);
    }

    let b_entry = alloc_harness_block(&mut m, harness_fid);
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
    let undef_val = emit_inst_val(&mut m, b_entry, Op::LoadConst(undef_cid));
    let empty_shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });

    // 1. Run top-level `func_main_0` initializers in topological order so
    //    cross-module `StoreModuleVar` exports and prototype methods initialize
    //    before importers and lifecycle hooks execute.
    for &init_fid in &init_funcs {
        if m.func(init_fid)
            .is_none_or(|fd| fd.is_external || fd.blocks.is_empty())
        {
            continue;
        }
        let callee = const_method_ref_val(&mut m, init_fid);
        let _ = emit_inst_val(
            &mut m,
            b_entry,
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
            b_entry,
            Op::TryGetGlobal {
                name: want_sym,
                default: Some(undef_val),
            },
        );
        let p = emit_inst_val(&mut m, b_entry, Op::AllocObject { shape: empty_shape });
        let c_sym = m.sym.intern("context");
        (Some(w), Some(p), Some(c_sym))
    } else {
        (None, None, None)
    };

    // 3. Creation phase: instantiate each component once in `b_entry` with a
    //    dedicated concrete singleton `AllocObject` receiver (`this`), run its
    //    constructor + creation hooks, and collect its steady-state & teardown
    //    callbacks for the loop and teardown blocks.
    let mut steady_calls: Vec<(FuncId, ValueId, Vec<ValueId>)> = Vec::new();
    let mut teardown_calls: Vec<(FuncId, ValueId, Vec<ValueId>)> = Vec::new();

    for comp in &components {
        let inst_obj = emit_inst_val(&mut m, b_entry, Op::AllocObject { shape: empty_shape });

        if matches!(
            comp.kind,
            OhosComponentKind::Ability | OhosComponentKind::ExtensionAbility
        ) && let Some(context_prop) = ctx_sym
        {
            let ctx_marker_sym = m.sym.intern(OHOS_CONTEXT_GLOBAL);
            let ctx_obj = emit_inst_val(
                &mut m,
                b_entry,
                Op::TryGetGlobal {
                    name: ctx_marker_sym,
                    default: Some(undef_val),
                },
            );
            emit_inst_void(
                &mut m,
                b_entry,
                Op::StoreProp {
                    object: inst_obj,
                    name: context_prop,
                    value: ctx_obj,
                },
            );
        }

        // Constructor invocation on `inst_obj`.
        invoke_method(&mut m, b_entry, comp.ctor, inst_obj, &[]);

        match comp.kind {
            OhosComponentKind::Ability => {
                let w = want_val.unwrap_or(undef_val);
                let p = misc_param_val.unwrap_or(undef_val);
                for &(mname, first_is_want, arity) in ABILITY_CREATE {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            invoke_method(&mut m, b_entry, mfid, inst_obj, &args);
                        }
                    }
                }
                for &(mname, first_is_want, arity) in ABILITY_STEADY {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                steady_calls.push((mfid, inst_obj, args.clone()));
                            }
                        }
                    }
                }
                for &(mname, first_is_want, arity) in ABILITY_TEARDOWN {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                teardown_calls.push((mfid, inst_obj, args.clone()));
                            }
                        }
                    }
                }
            }
            OhosComponentKind::ExtensionAbility => {
                let w = want_val.unwrap_or(undef_val);
                let p = misc_param_val.unwrap_or(undef_val);
                for &(mname, first_is_want, arity) in EXTENSION_CREATE {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            invoke_method(&mut m, b_entry, mfid, inst_obj, &args);
                        }
                    }
                }
                for &(mname, first_is_want, arity) in EXTENSION_STEADY {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                steady_calls.push((mfid, inst_obj, args.clone()));
                            }
                        }
                    }
                }
                for &(mname, first_is_want, arity) in EXTENSION_TEARDOWN {
                    if let Some(fids) = comp.methods.get(mname) {
                        let args = build_lifecycle_args(arity, first_is_want, w, p);
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                teardown_calls.push((mfid, inst_obj, args.clone()));
                            }
                        }
                    }
                }
            }
            OhosComponentKind::ArkUiView => {
                for &mname in ARKUI_CREATE {
                    if let Some(fids) = comp.methods.get(mname) {
                        for &mfid in fids {
                            invoke_method(&mut m, b_entry, mfid, inst_obj, &[]);
                        }
                    }
                }
                for &mname in ARKUI_STEADY {
                    if let Some(fids) = comp.methods.get(mname) {
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                steady_calls.push((mfid, inst_obj, Vec::new()));
                            }
                        }
                    }
                }
                // Also dispatch custom `@Builder` methods (any non-lifecycle
                // method calling `observeComponentCreation*`) inside steady-state.
                for (mname, fids) in &comp.methods {
                    let s = mname.as_str();
                    if ARKUI_CREATE.contains(&s)
                        || ARKUI_STEADY.contains(&s)
                        || ARKUI_TEARDOWN.contains(&s)
                    {
                        continue;
                    }
                    for &mfid in fids {
                        if is_invocable_internal(&m, mfid) && func_calls_observe(&m, mfid) {
                            steady_calls.push((mfid, inst_obj, Vec::new()));
                        }
                    }
                }
                for &mname in ARKUI_TEARDOWN {
                    if let Some(fids) = comp.methods.get(mname) {
                        for &mfid in fids {
                            if is_invocable_internal(&m, mfid) {
                                teardown_calls.push((mfid, inst_obj, Vec::new()));
                            }
                        }
                    }
                }
            }
        }
    }

    // 4. Steady-state `while (*)` dispatch loop + teardown phase (`D3`).
    if steady_calls.is_empty() {
        for (mfid, recv, args) in teardown_calls {
            invoke_method(&mut m, b_entry, mfid, recv, &args);
        }
        emit_inst_void(&mut m, b_entry, Op::Return { value: None });
    } else {
        let cond_sym = m.sym.intern(OHOS_LIFECYCLE_COND_GLOBAL);
        let b_loop_head = alloc_harness_block(&mut m, harness_fid);
        let b_teardown = alloc_harness_block(&mut m, harness_fid);

        emit_inst_void(&mut m, b_entry, Op::Branch { dest: b_loop_head });
        link_normal_edge(&mut m, b_entry, b_loop_head);

        if steady_calls.len() == 1 {
            let (mfid, recv, args) = &steady_calls[0];
            let b_call = alloc_harness_block(&mut m, harness_fid);
            let cond = emit_inst_val(
                &mut m,
                b_loop_head,
                Op::TryGetGlobal {
                    name: cond_sym,
                    default: Some(undef_val),
                },
            );
            emit_inst_void(
                &mut m,
                b_loop_head,
                Op::CondBranch {
                    cond,
                    true_dest: b_call,
                    false_dest: b_teardown,
                },
            );
            link_normal_edge(&mut m, b_loop_head, b_call);
            link_normal_edge(&mut m, b_loop_head, b_teardown);

            invoke_method(&mut m, b_call, *mfid, *recv, args);
            emit_inst_void(&mut m, b_call, Op::Branch { dest: b_loop_head });
            link_normal_edge(&mut m, b_call, b_loop_head);
        } else {
            let mut choice_blocks = Vec::with_capacity(steady_calls.len());
            let mut call_blocks = Vec::with_capacity(steady_calls.len());
            for _ in 0..steady_calls.len() {
                choice_blocks.push(alloc_harness_block(&mut m, harness_fid));
                call_blocks.push(alloc_harness_block(&mut m, harness_fid));
            }
            let cond = emit_inst_val(
                &mut m,
                b_loop_head,
                Op::TryGetGlobal {
                    name: cond_sym,
                    default: Some(undef_val),
                },
            );
            emit_inst_void(
                &mut m,
                b_loop_head,
                Op::CondBranch {
                    cond,
                    true_dest: choice_blocks[0],
                    false_dest: b_teardown,
                },
            );
            link_normal_edge(&mut m, b_loop_head, choice_blocks[0]);
            link_normal_edge(&mut m, b_loop_head, b_teardown);

            for (idx, (mfid, recv, args)) in steady_calls.iter().enumerate() {
                let b_choice = choice_blocks[idx];
                let b_call = call_blocks[idx];
                let b_next = choice_blocks.get(idx + 1).copied().unwrap_or(b_loop_head);

                let c_val = emit_inst_val(
                    &mut m,
                    b_choice,
                    Op::TryGetGlobal {
                        name: cond_sym,
                        default: Some(undef_val),
                    },
                );
                emit_inst_void(
                    &mut m,
                    b_choice,
                    Op::CondBranch {
                        cond: c_val,
                        true_dest: b_call,
                        false_dest: b_next,
                    },
                );
                link_normal_edge(&mut m, b_choice, b_call);
                link_normal_edge(&mut m, b_choice, b_next);

                invoke_method(&mut m, b_call, *mfid, *recv, args);
                emit_inst_void(&mut m, b_call, Op::Branch { dest: b_next });
                link_normal_edge(&mut m, b_call, b_next);
            }
        }

        for (mfid, recv, args) in teardown_calls {
            invoke_method(&mut m, b_teardown, mfid, recv, &args);
        }
        emit_inst_void(&mut m, b_teardown, Op::Return { value: None });
    }

    EntryModel {
        augmented_module: Some(m),
        harness_func: Some(harness_fid),
        init_funcs,
        components,
        entry_funcs: vec![harness_fid],
    }
}

fn default_single_module_entries(module: &Module) -> Vec<FuncId> {
    let mut mains = Vec::new();
    for (fi, fd) in module.functions.iter().enumerate() {
        if !fd.is_external && !fd.blocks.is_empty() && sym_str(module, fd.name) == "func_main_0" {
            mains.push(FuncId::new(fi as u32));
        }
    }
    if !mains.is_empty() {
        return mains;
    }
    module
        .functions
        .iter()
        .enumerate()
        .filter_map(|(fi, fd)| {
            (!fd.is_external && !fd.blocks.is_empty()).then_some(FuncId::new(fi as u32))
        })
        .collect()
}

fn alloc_harness_block(m: &mut Module, harness_fid: FuncId) -> BlockId {
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    if let Some(fd) = m.func_mut(harness_fid) {
        fd.blocks.push(bid);
    }
    bid
}

fn link_normal_edge(m: &mut Module, from: BlockId, to: BlockId) {
    if let Some(bb) = m.block_mut(to) {
        bb.preds.push(Edge {
            from,
            kind: EdgeKind::Normal,
        });
    }
}

fn is_invocable_internal(m: &Module, target: FuncId) -> bool {
    m.func(target)
        .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
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

fn const_method_ref_val(m: &mut Module, target: FuncId) -> ValueId {
    let mref = m.consts.push(Const::method_ref(target));
    let vid = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(mref),
        ty: Ty::Any,
    });
    vid
}

fn invoke_method(m: &mut Module, b: BlockId, target: FuncId, this_val: ValueId, args: &[ValueId]) {
    let Some(fd) = m.func(target) else { return };
    if fd.is_external || fd.blocks.is_empty() {
        return;
    }
    let callee = const_method_ref_val(m, target);
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
    for &item_cid in items {
        match module.consts.get(item_cid) {
            Some(Const::String(s)) => {
                pending_name = Some(sym_str(module, *s).to_owned());
            }
            Some(Const::MethodRef { func: fid, .. }) => {
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
    let mut cur = val;
    let mut suffixes: Vec<&str> = Vec::new();
    let mut visited: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
    let mut acc = loop {
        let root = peel_mov(module, cur);
        if !visited.insert(root) {
            return None;
        }
        let ValueDef::Inst(iid) = module.value(root)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::TryGetGlobal { name, .. } => break sym_str(module, *name).to_owned(),
            Op::LoadProp { object, name } => {
                let leaf = sym_str(module, *name);
                if classify_base_class_name(leaf).is_some() {
                    break leaf.to_owned();
                }
                suffixes.push(leaf);
                cur = *object;
            }
            Op::LoadModuleVar { index, kind } if !kind.is_local() => {
                let cid = links.func_class(in_func)?;
                let target = links.external_load(cid, *index)?;
                let mut resolved: Option<String> = None;
                for &(spec, imp) in &target.external_imports {
                    let imp_s = sym_str(module, imp);
                    let spec_s = sym_str(module, spec);
                    if imp_s != "default" && classify_base_class_name(imp_s).is_some() {
                        resolved = Some(imp_s.to_owned());
                        break;
                    }
                    if let Some(tail) = spec_s.rsplit(['.', ':']).next()
                        && classify_base_class_name(tail).is_some()
                    {
                        resolved = Some(tail.to_owned());
                        break;
                    }
                }
                break resolved?;
            }
            _ => return None,
        }
    };
    for suf in suffixes.into_iter().rev() {
        acc.push('.');
        acc.push_str(suf);
    }
    Some(acc)
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

fn peel_mov(module: &Module, v: ValueId) -> ValueId {
    peel_movs(module, v)
}

fn peel_closure_func(module: &Module, mut v: ValueId) -> Option<FuncId> {
    let mut visited = std::collections::HashSet::new();
    while visited.insert(v) {
        let ValueDef::Inst(iid) = module.value(v)?.def else {
            return None;
        };
        match &module.inst(iid)?.op {
            Op::Mov { src }
            | Op::AllocClosure { func: src }
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

        let c_s_oc = m.consts.intern(Const::String(s_oc));
        let c_oc1 = m.consts.intern(Const::method_ref(on_create1));
        let c_s_fg = m.consts.intern(Const::String(s_fg));
        let c_fg1 = m.consts.intern(Const::method_ref(on_fg1));
        let mem1 = m.consts.push_array(vec![c_s_oc, c_oc1, c_s_fg, c_fg1]);
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor1,
                heritage: Some(h_uiab),
                members: mem1,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );

        let c_fg2 = m.consts.intern(Const::method_ref(on_fg2));
        let mem2 = m.consts.push_array(vec![c_s_fg, c_fg2]);
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor2,
                heritage: Some(h_uiab),
                members: mem2,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );

        let c_s_af = m.consts.intern(Const::String(s_af));
        let c_on_add = m.consts.intern(Const::method_ref(on_add));
        let mem3 = m.consts.push_array(vec![c_s_af, c_on_add]);
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor3,
                heritage: Some(h_form),
                members: mem3,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );

        let c_s_ata = m.consts.intern(Const::String(s_ata));
        let c_about = m.consts.intern(Const::method_ref(about));
        let c_s_ir = m.consts.intern(Const::String(s_ir));
        let c_render = m.consts.intern(Const::method_ref(render));
        let mem4 = m
            .consts
            .push_array(vec![c_s_ata, c_about, c_s_ir, c_render]);
        let home_cls = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctor4,
                heritage: Some(h_view),
                members: mem4,
                member_attrs: Vec::new(),
                count: 0,
            })),
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

    #[test]
    fn deep_and_cyclic_heritage_loadprop_runs_on_small_stack() {
        const DEPTH: usize = 500;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut m = Module::new();
                let d = m.sym.intern("L@bundle:com.app/entry/ets/Deep;");
                let n = m.sym.intern("@bundle:com.app/entry/ets/Deep");
                let cid = ClassId::new(0);
                m.classes.push(ClassData::new(d, n));

                let (ctor_deep, b_cd, _) =
                    add_fn(&mut m, cid, "DeepComp", FunctionKind::Constructor, 3);
                emit_inst_void(&mut m, b_cd, Op::Return { value: None });
                let (ctor_cyc, b_cc, _) =
                    add_fn(&mut m, cid, "CyclicComp", FunctionKind::Constructor, 3);
                emit_inst_void(&mut m, b_cc, Op::Return { value: None });

                let (main_fid, b_main, _) =
                    add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
                let s_uiab = m.sym.intern("UIAbility");
                let mut cur = emit_inst_val(
                    &mut m,
                    b_main,
                    Op::TryGetGlobal {
                        name: s_uiab,
                        default: None,
                    },
                );
                let s_seg = m.sym.intern("sub");
                for _ in 0..DEPTH {
                    cur = emit_inst_val(
                        &mut m,
                        b_main,
                        Op::LoadProp {
                            object: cur,
                            name: s_seg,
                        },
                    );
                }
                let deep_chain = cur;
                let deep_heritage = emit_inst_val(
                    &mut m,
                    b_main,
                    Op::LoadProp {
                        object: cur,
                        name: s_uiab,
                    },
                );
                let empty_mem = m.consts.push_array(Vec::new());
                let _ = emit_inst_val(
                    &mut m,
                    b_main,
                    Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                        ctor: ctor_deep,
                        heritage: Some(deep_heritage),
                        members: empty_mem,
                        member_attrs: Vec::new(),
                        count: 0,
                    })),
                );

                // Cyclic `LoadProp` chain (`v_cyc = LoadProp(v_cyc, "sub")`):
                // must terminate cleanly as `None` via the cycle guard.
                let cyc_iid = InstId::new(m.insts.len() as u32);
                let cyc_vid = ValueId::new(m.values.len() as u32);
                m.insts.push(Inst {
                    op: Op::LoadProp {
                        object: cyc_vid,
                        name: s_seg,
                    },
                    result: Some(cyc_vid),
                    block: b_main,
                    loc: None,
                });
                m.values.push(Value {
                    def: ValueDef::Inst(cyc_iid),
                    ty: Ty::Any,
                });
                m.blocks[b_main.index()].insts.push(cyc_iid);
                let _ = emit_inst_val(
                    &mut m,
                    b_main,
                    Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                        ctor: ctor_cyc,
                        heritage: Some(cyc_vid),
                        members: empty_mem,
                        member_attrs: Vec::new(),
                        count: 0,
                    })),
                );
                emit_inst_void(&mut m, b_main, Op::Return { value: None });

                let links = ModuleLinkTable::build(&m);
                let full_name =
                    resolve_heritage_name(&m, &links, main_fid, deep_chain).expect("deep chain");
                assert!(full_name.starts_with("UIAbility.sub."));
                assert_eq!(full_name.matches(".sub").count(), DEPTH);
                assert!(resolve_heritage_name(&m, &links, main_fid, cyc_vid).is_none());

                let comps = discover_components(&m, &links, None);
                assert_eq!(comps.len(), 1);
                assert_eq!(comps[0].ctor, ctor_deep);
                assert_eq!(comps[0].kind, OhosComponentKind::Ability);
            })
            .expect("spawn");
        handle.join().expect("small stack must not overflow");
    }

    #[test]
    fn standalone_global_at_class1_with_stub_class0_preserves_esm_after_harness() {
        use abcd_ir::module::{ImportDecl, ModuleRequest};
        use abcd_ir::op::ModuleVarKind;

        let mut m = Module::new();
        // ClassId(0): empty stub class `"LA;"`
        let d_stub = m.sym.intern("LA;");
        let n_stub = m.sym.intern("A");
        m.classes.push(ClassData::new(d_stub, n_stub));

        // ClassId(1): standalone `"L_GLOBAL;"` with module-level SDK import
        let d_glob = m.sym.intern("L_GLOBAL;");
        let n_glob = m.sym.intern("_GLOBAL");
        let cid_glob = ClassId::new(1);
        m.classes.push(ClassData::new(d_glob, n_glob));

        let s_uiab = m.sym.intern("UIAbility");
        let s_kit = m.sym.intern("@kit.AbilityKit");
        m.imports.push(ImportDecl::Regular {
            local_name: s_uiab,
            import_name: s_uiab,
            module_request: s_kit,
        });
        m.module_requests.push(ModuleRequest {
            specifier: s_kit,
            lazy: false,
        });

        let (ctor, b_ctor, _) = add_fn(&mut m, cid_glob, "MyAbility", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_ctor, Op::Return { value: None });
        let (on_create, b_oc, _) = add_fn(&mut m, cid_glob, "onCreate", FunctionKind::Function, 5);
        emit_inst_void(&mut m, b_oc, Op::Return { value: None });

        let (_, b_main, _) = add_fn(&mut m, cid_glob, "func_main_0", FunctionKind::Function, 3);
        let h_uiab = emit_inst_val(
            &mut m,
            b_main,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let s_oc = m.sym.intern("onCreate");
        let c_s_oc = m.consts.intern(Const::String(s_oc));
        let c_oc = m.consts.intern(Const::method_ref(on_create));
        let mem = m.consts.push_array(vec![c_s_oc, c_oc]);
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor,
                heritage: Some(h_uiab),
                members: mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        emit_inst_void(&mut m, b_main, Op::Return { value: None });

        let links_before = ModuleLinkTable::build(&m);
        assert!(links_before.external_load(cid_glob, 0).is_some());

        let (aug, harness_fid) = synthesize_ohos_harness(&m, None).expect("harness synthesized");
        assert_eq!(aug.func(harness_fid).unwrap().class_id, cid_glob);
        assert!(aug.classes[0].methods.is_empty());

        let links_after = ModuleLinkTable::build(&aug);
        let ext = links_after
            .external_load(cid_glob, 0)
            .expect("standalone ESM preserved on L_GLOBAL; after harness synthesis");
        assert_eq!(ext.external_imports, vec![(s_kit, s_uiab)]);
    }

    #[test]
    fn steady_state_lifecycle_loop_propagates_on_background_write_to_next_on_foreground_read() {
        use crate::dataflow::ifds::{IfdsConfig, IfdsProblem, IfdsSolver};

        let mut m = Module::new();
        let d = m
            .sym
            .intern("L@bundle:com.app/entry/ets/entryability/EntryAbility;");
        let n = m
            .sym
            .intern("@bundle:com.app/entry/ets/entryability/EntryAbility");
        let cid = ClassId::new(0);
        m.classes.push(ClassData::new(d, n));

        let s_cached = m.sym.intern("cachedSecret");
        let s_uiab = m.sym.intern("UIAbility");
        let s_bg = m.sym.intern("onBackground");
        let s_fg = m.sym.intern("onForeground");
        let s_destroy = m.sym.intern("onDestroy");

        let (ctor, b_c, _) = add_fn(&mut m, cid, "EntryAbility", FunctionKind::Constructor, 3);
        emit_inst_void(&mut m, b_c, Op::Return { value: None });

        // `onBackground`: `this.cachedSecret = "secret"`
        let (on_bg, b_bg, p_bg) = add_fn(&mut m, cid, "onBackground", FunctionKind::Function, 3);
        let s_secret = m.sym.intern("secret");
        let c_secret = m.consts.intern(Const::String(s_secret));
        let v_secret = emit_inst_val(&mut m, b_bg, Op::LoadConst(c_secret));
        let bg_store_iid = InstId::new(m.insts.len() as u32);
        emit_inst_void(
            &mut m,
            b_bg,
            Op::StoreProp {
                object: p_bg[2],
                name: s_cached,
                value: v_secret,
            },
        );
        emit_inst_void(&mut m, b_bg, Op::Return { value: None });

        // `onForeground`: `let x = this.cachedSecret; sink(x)`
        // In a single linear pass (`onForeground -> onBackground -> onDestroy`),
        // `onForeground` ran ONLY BEFORE `onBackground` and missed `this.cachedSecret`!
        let sink_sym = m.sym.intern("sink");
        let sink_fid = FuncId::new(m.functions.len() as u32);
        let mut sink_fd = FunctionData::new(cid, sink_sym, FunctionKind::Function);
        sink_fd.is_external = true;
        m.functions.push(sink_fd);
        m.classes[cid.index()].methods.push(sink_fid);

        let (on_fg, b_fg, p_fg) = add_fn(&mut m, cid, "onForeground", FunctionKind::Function, 3);
        let fg_load_iid = InstId::new(m.insts.len() as u32);
        let loaded = emit_inst_val(
            &mut m,
            b_fg,
            Op::LoadProp {
                object: p_fg[2],
                name: s_cached,
            },
        );
        let callee_sink = const_method_ref_val(&mut m, sink_fid);
        let sink_call = InstId::new(m.insts.len() as u32);
        let _ = emit_inst_val(
            &mut m,
            b_fg,
            Op::Call {
                callee: callee_sink,
                this: None,
                args: vec![loaded],
                kind: CallKind::Direct,
            },
        );
        emit_inst_void(&mut m, b_fg, Op::Return { value: None });

        // `onDestroy` teardown hook.
        let (on_destroy, b_dt, _) = add_fn(&mut m, cid, "onDestroy", FunctionKind::Function, 3);
        let dt_ret = InstId::new(m.insts.len() as u32);
        emit_inst_void(&mut m, b_dt, Op::Return { value: None });

        let (_, b_main, _) = add_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 3);
        let h_uiab = emit_inst_val(
            &mut m,
            b_main,
            Op::TryGetGlobal {
                name: s_uiab,
                default: None,
            },
        );
        let c_s_bg = m.consts.intern(Const::String(s_bg));
        let c_bg = m.consts.intern(Const::method_ref(on_bg));
        let c_s_fg = m.consts.intern(Const::String(s_fg));
        let c_fg = m.consts.intern(Const::method_ref(on_fg));
        let c_s_dt = m.consts.intern(Const::String(s_destroy));
        let c_dt = m.consts.intern(Const::method_ref(on_destroy));
        let mem = m
            .consts
            .push_array(vec![c_s_fg, c_fg, c_s_bg, c_bg, c_s_dt, c_dt]);
        let _ = emit_inst_val(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor,
                heritage: Some(h_uiab),
                members: mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        emit_inst_void(&mut m, b_main, Op::Return { value: None });

        let model = EntryModel::build(&m, None);
        let harness_fid = model.harness_func.expect("harness synthesized");
        assert_eq!(model.entry_funcs, vec![harness_fid]);
        let aug = model.augmented_module.as_ref().expect("augmented module");
        let rep = verify_module(aug);
        assert!(rep.errors.is_empty(), "verify errors: {:?}", rep.errors);

        let base_cg = CallGraph::build(aug);
        let (cg, tables, stats) = analyze(
            aug,
            &base_cg,
            &PtaConfig {
                harness_func: Some(harness_fid),
                ..PtaConfig::default()
            },
        )
        .into_parts();
        let r2 = Rung2AliasOracle::new(aug, tables, stats);
        let bg_sites = r2.query(p_bg[2], bg_store_iid).sites;
        let fg_sites = r2.query(p_fg[2], fg_load_iid).sites;
        assert_eq!(bg_sites.len(), 1);
        assert_eq!(bg_sites, fg_sites);
        let recv_site = bg_sites.iter().next().unwrap();

        // Run IFDS over the synthesized harness: `onBackground` taints
        // `(recv_site, cachedSecret)`, which loops around `while (*)` into the
        // next `onForeground` (`sink_call`) AND reaches `onDestroy` (`dt_ret`)!
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        enum LfFact {
            Zero,
            Val(ValueId),
            HeapCached(InstId),
        }

        struct LfProblem {
            harness: FuncId,
            bg_store: InstId,
            fg_load: InstId,
            loaded_val: ValueId,
            recv_site: InstId,
        }

        impl IfdsProblem for LfProblem {
            type Fact = LfFact;

            fn zero(&self) -> LfFact {
                LfFact::Zero
            }

            fn initial_seeds(&self) -> Vec<(FuncId, LfFact)> {
                vec![(self.harness, LfFact::Zero)]
            }

            fn normal_flow(
                &self,
                _module: &Module,
                curr: InstId,
                _succ: InstId,
                source: &LfFact,
                out: &mut Vec<LfFact>,
            ) {
                match *source {
                    LfFact::Zero => {
                        if curr == self.bg_store {
                            out.push(LfFact::HeapCached(self.recv_site));
                        }
                    }
                    LfFact::HeapCached(site) => {
                        out.push(LfFact::HeapCached(site));
                        if curr == self.fg_load && site == self.recv_site {
                            out.push(LfFact::Val(self.loaded_val));
                        }
                    }
                    LfFact::Val(v) => out.push(LfFact::Val(v)),
                }
            }

            fn call_flow(
                &self,
                _module: &Module,
                _call: InstId,
                _callee: FuncId,
                source: &LfFact,
                out: &mut Vec<LfFact>,
            ) {
                if let LfFact::HeapCached(s) = *source {
                    out.push(LfFact::HeapCached(s));
                }
            }

            fn return_flow(
                &self,
                _module: &Module,
                _call_site: Option<InstId>,
                _callee: FuncId,
                _exit: InstId,
                _return_site: Option<InstId>,
                source: &LfFact,
                out: &mut Vec<LfFact>,
            ) {
                if let LfFact::HeapCached(s) = *source {
                    out.push(LfFact::HeapCached(s));
                }
            }

            fn call_to_return_flow(
                &self,
                module: &Module,
                call: InstId,
                _return_site: InstId,
                source: &LfFact,
                out: &mut Vec<LfFact>,
            ) {
                match *source {
                    LfFact::Zero => {}
                    LfFact::Val(v) => out.push(LfFact::Val(v)),
                    LfFact::HeapCached(s) => {
                        // Resolved internal calls propagate heap facts through callee;
                        // external `sink` bypasses.
                        let is_ext_call =
                            matches!(module.inst(call).map(|i| &i.op), Some(Op::Call { .. }))
                                && module
                                    .inst(call)
                                    .is_some_and(|_| call == InstId::new(999_999));
                        let _ = is_ext_call;
                        out.push(LfFact::HeapCached(s));
                    }
                }
            }
        }

        let prob = LfProblem {
            harness: harness_fid,
            bg_store: bg_store_iid,
            fg_load: fg_load_iid,
            loaded_val: loaded,
            recv_site,
        };
        let res = IfdsSolver::new(aug, &prob, &cg, IfdsConfig::default()).solve();
        assert!(
            res.is_reached(sink_call, &LfFact::Val(loaded)),
            "state written in onBackground must flow around steady-state loop to next onForeground"
        );
        assert!(
            res.is_reached(dt_ret, &LfFact::HeapCached(recv_site)),
            "steady-state loop exit must reach teardown onDestroy"
        );
    }

    #[test]
    fn out_of_bounds_class_and_func_ids_do_not_panic() {
        let mut m = Module::new();
        let d = m.sym.intern("L_GLOBAL;");
        let n = m.sym.intern("_GLOBAL");
        m.classes.push(ClassData::new(d, n));

        // Function with out-of-bounds `class_id = ClassId(999)` and `DefineClass`
        // referencing out-of-bounds `ctor = FuncId(999)`.
        let sym = m.sym.intern("func_main_0");
        let mut fd = FunctionData::new(ClassId::new(999), sym, FunctionKind::Function);
        let b = BlockId::new(0);
        m.blocks.push(Block::default());
        fd.blocks.push(b);
        m.functions.push(fd);

        let s_uiab = m.sym.intern("UIAbility");
        let h = emit_inst_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: s_uiab,
                default: None,
            },
        );
        let empty_mem = m.consts.push_array(Vec::new());
        let _ = emit_inst_val(
            &mut m,
            b,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: FuncId::new(999),
                heritage: Some(h),
                members: empty_mem,
                member_attrs: Vec::new(),
                count: 0,
            })),
        );
        emit_inst_void(&mut m, b, Op::Return { value: None });

        let model = EntryModel::build(&m, Some(r#"{"srcEntry":"./ets/EntryAbility.ets"}"#));
        assert!(model.components.is_empty());
        assert!(synthesize_ohos_harness(&m, None).is_none());
    }
}
