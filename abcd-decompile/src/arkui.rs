//! OpenHarmony ArkUI declarative UI sugar recovery (`--arkui`, #26 Phase 3).
//!
//! Reconstructs `ets_loader` / `ui2abc`-lowered imperative `ViewPU` / `View`
//! classes back into readable ArkTS declarative `@Entry` / `@Component struct`
//! definitions:
//!
//! - **State & storage decorators** (`@State`, `@Prop`, `@Link`, `@ObjectLink`,
//!   `@Provide`, `@Consume`, `@LocalStorageLink`, `@LocalStorageProp`,
//!   `@StorageLink`, `@StorageProp`) recovered from constructor property
//!   wrappers (`ObservedProperty*PU`, `SynchedProperty*PU`, `addProvidedVar`,
//!   `initializeConsume`, `createLocalStorage*`).
//! - **Declarative `build() { ... }` & `@Builder` methods** recovered from
//!   `initialRender` (and helper methods invoking `observeComponentCreation*`),
//!   matching `Comp.create(...)` + chained attribute calls + `Comp.pop()` stacks,
//!   custom child component instantiations (`ViewPU.create(new Child(...))` /
//!   `updateStateVarsOfChildByElmtId`), `If` branches
//!   (`ifElseBranchUpdateFunction` / `If.branchId`), and `ForEach` /
//!   `LazyForEach` generators.
//! - **Boilerplate elision**: drops synthetic `ets_loader` plumbing methods
//!   (`setInitiallyProvidedValue`, `updateStateVars`,
//!   `purgeVariableDependenciesOnElmtId`, `aboutToBeDeleted`, `rerender`,
//!   `updateRecycleElmtId`, `getEntryName`, and `__prop` getter/setter pairs)
//!   while preserving every user lifecycle hook (`aboutToAppear`,
//!   `aboutToDisappear`, `onPageShow`, `onPageHide`, `onBackPress`) and custom
//!   method, and emitting any unrecognized statements verbatim inside `build()`
//!   so nothing is ever silently lost.

use std::collections::{BTreeMap, BTreeSet};

use abcd_ir::id::{ConstId, FuncId};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{CallKind, MemberAttrs};

use crate::consts::lit_of;
use crate::emit::{Emitter, lex_decls};
use crate::expr::{Expr, Lit, ObjEntry};
use crate::legalize::{is_legal_ident, sanitize};
use crate::recover::Stmt;
use crate::structure::{Leaf, SNode};

/// Decorated or plain property recovered from a `ViewPU` / `View` constructor.
#[derive(Clone, Debug)]
enum ArkField {
    State {
        name: String,
        init: Option<String>,
    },
    Prop {
        name: String,
    },
    Link {
        name: String,
    },
    ObjectLink {
        name: String,
    },
    Provide {
        alias: String,
        name: String,
        init: Option<String>,
    },
    Consume {
        alias: String,
        name: String,
    },
    LocalStorageLink {
        key: String,
        name: String,
        init: String,
    },
    LocalStorageProp {
        key: String,
        name: String,
        init: String,
    },
    StorageLink {
        key: String,
        name: String,
        init: String,
    },
    StorageProp {
        key: String,
        name: String,
        init: String,
    },
    Plain {
        name: String,
        init: String,
    },
}

/// Reconstructed declarative UI node inside `build()` or `@Builder`.
#[derive(Clone, Debug)]
enum UiNode {
    Component {
        name: String,
        args: String,
        attrs: Vec<(String, String)>,
        children: Vec<UiNode>,
    },
    CustomChild {
        name: String,
        props: Option<String>,
    },
    If {
        cond: String,
        then_body: Vec<UiNode>,
        else_body: Vec<UiNode>,
    },
    ForEach {
        is_lazy: bool,
        arr: String,
        item_param: String,
        idx_param: Option<String>,
        body: Vec<UiNode>,
        key_gen: Option<String>,
    },
    RawStmt(String),
}

const SYNTHETIC_VIEWPU_METHODS: &[&str] = &[
    "setInitiallyProvidedValue",
    "updateStateVars",
    "purgeVariableDependenciesOnElmtId",
    "aboutToBeDeleted",
    "aboutToBeDeletedInternal",
    "rerender",
    "updateRecycleElmtId",
    "getEntryName",
    "finalizeConstruction",
    "setController",
];

/// Leaf built-in ArkUI components that do not emit a matching `.pop()` call in
/// `ets_loader` output (or close immediately at the next sibling).
const SELF_CLOSING_COMPONENTS: &[&str] = &[
    "Blank",
    "Divider",
    "Image",
    "ImageAnimator",
    "LoadingProgress",
    "Marquee",
    "Progress",
    "QRCode",
    "Rating",
    "RichText",
    "Search",
    "Slider",
    "Span",
    "SymbolGlyph",
    "SymbolSpan",
    "TextArea",
    "TextClock",
    "TextInput",
    "TextPicker",
    "TextTimer",
    "TimePicker",
    "Toggle",
    "Video",
    "Web",
    "XComponent",
];

#[derive(Default)]
struct MainArkUiPlan {
    has_view_class: bool,
    view_classes: BTreeSet<String>,
    struct_names: BTreeSet<String>,
    proto_to_class: BTreeMap<String, String>,
    extra_methods: BTreeMap<String, Vec<(String, FuncId)>>,
    dead_temps: BTreeSet<String>,
    polyfill_phis: BTreeSet<String>,
    entry_targets: BTreeSet<String>,
}

/// Return the top-level ArkUI `struct` names that [`try_emit_arkui_main`] will
/// emit for `func`, so module-level `let <StructName>;` predeclarations can be
/// suppressed in `--split-modules --arkui` output.
pub(crate) fn arkui_main_struct_names(pre: &crate::emit::PreparedFunc) -> BTreeSet<String> {
    let env = collect_const_bindings(&pre.body);
    let mut plan = MainArkUiPlan::default();
    scan_main_body(&pre.body, &env, &mut plan);
    if plan.has_view_class {
        plan.struct_names
    } else {
        BTreeSet::new()
    }
}

/// Attempt to emit `func_main_0` at module top-level under `--arkui` by
/// unwrapping `ets_loader`'s `finalizeConstruction` polyfill and
/// `registerNamedRoute` / `loadDocument` registration calls around `@Component`
/// classes. Returns `true` if handled.
pub(crate) fn try_emit_arkui_main(em: &mut Emitter<'_>, func: FuncId, out: &mut String) -> bool {
    if em.module.func(func).is_none() {
        return false;
    }
    let (env, plan) = {
        let pre = em.peek_prepared(func, true);
        let env = collect_const_bindings(&pre.body);
        let mut plan = MainArkUiPlan::default();
        scan_main_body(&pre.body, &env, &mut plan);
        if !plan.has_view_class {
            return false;
        }
        (env, plan)
    };

    let (rf, body) = em.func_nodes(func, true);
    em.stats.functions += 1;
    em.current_fn_has_fallback = false;
    em.current_kind = rf.kind;

    for n in &body {
        emit_arkui_main_node(em, n, &env, &plan, out);
    }

    if em.current_fn_has_fallback {
        em.stats.functions_with_fallbacks += 1;
    }
    true
}

fn scan_main_body(nodes: &[SNode], env: &BTreeMap<String, Expr>, plan: &mut MainArkUiPlan) {
    // Pass 1: discover ViewPU/View classes, prototype aliases, and polyfill phis.
    for n in nodes {
        match n {
            SNode::If {
                cond,
                then,
                otherwise,
            } if is_finalize_construction_polyfill(cond, then, otherwise, env) => {
                collect_phi_targets(then, &mut plan.polyfill_phis);
                collect_phi_targets(otherwise, &mut plan.polyfill_phis);
            }
            SNode::Stmts(leaves) => {
                for l in leaves {
                    let Leaf::Raw(stmt) = l else { continue };
                    match stmt {
                        Stmt::Declare { name, value, .. } => {
                            if let Expr::Class { heritage, .. } = value
                                && is_view_heritage(heritage.as_deref(), env)
                            {
                                plan.has_view_class = true;
                                plan.view_classes.insert(name.clone());
                                plan.struct_names.insert(clean_component_name(name));
                            }
                            if let Expr::PropName {
                                object,
                                name: prop_name,
                                ..
                            } = value
                                && prop_name == "prototype"
                                && let Some(cls_var) = raw_ident_of(object)
                                && plan.view_classes.contains(&cls_var)
                            {
                                plan.proto_to_class.insert(name.clone(), cls_var);
                            }
                            if let Some(t) = extract_entry_registration(value, env) {
                                plan.entry_targets.insert(t);
                            }
                        }
                        Stmt::Expr(e) | Stmt::LexStore { value: e, .. } => {
                            if let Expr::Class { heritage, .. } = e
                                && is_view_heritage(heritage.as_deref(), env)
                            {
                                plan.has_view_class = true;
                            }
                            if let Some(t) = extract_entry_registration(e, env) {
                                plan.entry_targets.insert(t);
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    // Pass 2: collect prototype-overflow methods and accessor-descriptor temps
    // attached to `<ViewClass>.prototype` after `DefineClass`.
    for n in nodes {
        let SNode::Stmts(leaves) = n else { continue };
        for l in leaves {
            let Leaf::Raw(stmt) = l else { continue };
            match stmt {
                Stmt::DefineMethod {
                    object, name, func, ..
                }
                | Stmt::StoreProp {
                    object,
                    name,
                    value: func,
                    ..
                } => {
                    if let Some(pvar) = raw_ident_of(object)
                        && let Some(cls_var) = plan.proto_to_class.get(&pvar).cloned()
                        && let Expr::Closure { body: mfid, .. } = resolve_expr(func, env)
                        && !name.starts_with("#~@")
                    {
                        let list = plan.extra_methods.entry(cls_var).or_default();
                        if !list.iter().any(|(m, f)| m == name || f == mfid) {
                            list.push((name.clone(), *mfid));
                        }
                    }
                }
                Stmt::Expr(Expr::DefineGetterSetter {
                    obj,
                    key,
                    getter,
                    setter,
                }) => {
                    if let Some(pvar) = raw_ident_of(obj)
                        && plan.proto_to_class.contains_key(&pvar)
                    {
                        for operand in [key.as_ref(), getter.as_ref(), setter.as_ref()] {
                            if let Some(id) = raw_ident_of(operand) {
                                plan.dead_temps.insert(id);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

fn collect_phi_targets(nodes: &[SNode], out: &mut BTreeSet<String>) {
    for n in nodes {
        if let SNode::Stmts(leaves) = n {
            for l in leaves {
                if let Leaf::Raw(Stmt::PhiAssign { target, .. }) = l {
                    out.insert(target.clone());
                }
            }
        }
    }
}

fn raw_ident_of(e: &Expr) -> Option<String> {
    match e {
        Expr::Ident(s) | Expr::Temp { name: s, .. } => Some(s.clone()),
        _ => None,
    }
}

fn emit_arkui_main_node(
    em: &mut Emitter<'_>,
    n: &SNode,
    env: &BTreeMap<String, Expr>,
    plan: &MainArkUiPlan,
    out: &mut String,
) {
    match n {
        SNode::If {
            cond,
            then,
            otherwise,
        } if is_finalize_construction_polyfill(cond, then, otherwise, env) => {}
        SNode::Stmts(leaves) => {
            for l in leaves {
                let Leaf::Raw(s) = l else {
                    em.emit_leaf(l, 0, out);
                    continue;
                };
                match s {
                    Stmt::Declare {
                        name,
                        value:
                            Expr::Class {
                                ctor,
                                heritage,
                                members,
                                member_attrs,
                                ..
                            },
                        ..
                    } if is_view_heritage(heritage.as_deref(), env) => {
                        let is_entry = plan.entry_targets.contains("*")
                            || plan.entry_targets.contains(name)
                            || plan
                                .entry_targets
                                .iter()
                                .any(|t| clean_component_name(t) == clean_component_name(name));
                        let extra = plan
                            .extra_methods
                            .get(name)
                            .map(Vec::as_slice)
                            .unwrap_or(&[]);
                        let _ = emit_arkui_struct(
                            em,
                            "",
                            0,
                            name,
                            *ctor,
                            *members,
                            member_attrs,
                            extra,
                            is_entry,
                            out,
                        );
                    }
                    Stmt::Declare { name, value, .. }
                        if plan.proto_to_class.contains_key(name)
                            || plan.dead_temps.contains(name)
                            || is_pure_arkui_main_setup(value, env) => {}
                    Stmt::PhiDecl { name, .. } if plan.polyfill_phis.contains(name) => {}
                    Stmt::DefineMethod { object, func, .. }
                    | Stmt::StoreProp {
                        object,
                        value: func,
                        ..
                    } if raw_ident_of(object)
                        .is_some_and(|p| plan.proto_to_class.contains_key(&p))
                        && matches!(resolve_expr(func, env), Expr::Closure { .. }) => {}
                    Stmt::StoreDyn {
                        object, key, value, ..
                    } if raw_ident_of(object)
                        .is_some_and(|p| plan.proto_to_class.contains_key(&p))
                        && string_lit(Some(key), env).is_some_and(|k| k.starts_with("#~@"))
                        && matches!(resolve_expr(value, env), Expr::Closure { .. }) => {}
                    Stmt::Expr(Expr::DefineGetterSetter { obj, .. })
                        if raw_ident_of(obj)
                            .is_some_and(|p| plan.proto_to_class.contains_key(&p)) => {}
                    Stmt::ModuleStore {
                        name: slot_name,
                        value,
                        ..
                    } if raw_ident_of(value).is_some_and(|v| plan.view_classes.contains(&v)) => {
                        if let Some(cls_var) = raw_ident_of(value) {
                            let sname = clean_component_name(&cls_var);
                            if slot_name != &sname {
                                out.push_str(&format!("{slot_name} = {sname};\n"));
                            }
                        }
                    }
                    Stmt::LexStore { value, .. }
                        if is_class_alias_store(value, env)
                            || raw_ident_of(value)
                                .is_some_and(|v| plan.view_classes.contains(&v)) => {}
                    Stmt::Expr(e)
                        if is_prototype_touch(e)
                            || extract_entry_registration(e, env).is_some() => {}
                    Stmt::Return(None) | Stmt::Elided { .. } => {}
                    _ => em.emit_leaf(l, 0, out),
                }
            }
        }
        SNode::Honest(_) => {}
        _ => em.emit_node(n, 0, out),
    }
}

/// Attempt to emit a `Class` as an `@Component struct` when `opts.arkui`
/// is enabled and `heritage` resolves to `ViewPU` or `View`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_emit_arkui_component(
    em: &mut Emitter<'_>,
    pad: &str,
    indent: usize,
    name: &str,
    ctor: FuncId,
    heritage: Option<&Expr>,
    members: ConstId,
    member_attrs: &[MemberAttrs],
    out: &mut String,
) -> bool {
    let empty_env = BTreeMap::new();
    if !is_view_heritage(heritage, &empty_env) && !heritage_mentions_view(heritage) {
        return false;
    }
    emit_arkui_struct(
        em,
        pad,
        indent,
        name,
        ctor,
        members,
        member_attrs,
        &[],
        false,
        out,
    )
}

#[allow(clippy::too_many_arguments)]
fn emit_arkui_struct(
    em: &mut Emitter<'_>,
    pad: &str,
    indent: usize,
    raw_name: &str,
    ctor: FuncId,
    members: ConstId,
    member_attrs: &[MemberAttrs],
    extra_methods: &[(String, FuncId)],
    mut is_entry: bool,
    out: &mut String,
) -> bool {
    let Some(Lit::Array(items)) = lit_of(em.module, members) else {
        return false;
    };

    let mut method_entries: Vec<(String, FuncId, Option<&MemberAttrs>)> = Vec::new();
    let mut seen_fids = BTreeSet::new();
    let mut is_custom_dialog = false;
    let mut pending_name: Option<String> = None;
    let mut midx = 0usize;
    for item in &items {
        match item {
            Lit::String(s) => pending_name = Some(s.clone()),
            Lit::MethodRef(f) => {
                let mname = pending_name
                    .take()
                    .unwrap_or_else(|| format!("m${}", f.index()));
                let attrs = member_attrs.get(midx);
                midx += 1;
                if mname == "getEntryName" {
                    is_entry = true;
                }
                if mname == "setController" {
                    is_custom_dialog = true;
                }
                seen_fids.insert(*f);
                method_entries.push((mname, *f, attrs));
            }
            _ => {}
        }
    }
    for (mname, mfid) in extra_methods {
        if mname == "getEntryName" {
            is_entry = true;
        }
        if mname == "setController" {
            is_custom_dialog = true;
        }
        if seen_fids.insert(*mfid) {
            method_entries.push((mname.clone(), *mfid, None));
        }
    }

    em.stats.classes += 1;
    let struct_name = clean_component_name(raw_name);
    if is_entry {
        out.push_str(&format!("{pad}@Entry\n"));
    }
    if is_custom_dialog {
        out.push_str(&format!("{pad}@CustomDialog\n"));
    }
    out.push_str(&format!("{pad}@Component\n"));
    out.push_str(&format!("{pad}struct {struct_name} {{\n"));

    let (_ctor_rf, ctor_body) = em.func_nodes(ctor, false);
    let fields = extract_arkui_fields(em, &ctor_body);
    let mut decorated_names = BTreeSet::new();
    let mut link_names = BTreeSet::new();
    for field in &fields {
        match field {
            ArkField::State { name, init } => {
                decorated_names.insert(name.clone());
                match init {
                    Some(v) => out.push_str(&format!("{pad}  @State {name}: any = {v};\n")),
                    None => out.push_str(&format!("{pad}  @State {name}: any;\n")),
                }
            }
            ArkField::Prop { name } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!("{pad}  @Prop {name}: any;\n"));
            }
            ArkField::Link { name } => {
                decorated_names.insert(name.clone());
                link_names.insert(name.clone());
                out.push_str(&format!("{pad}  @Link {name}: any;\n"));
            }
            ArkField::ObjectLink { name } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!("{pad}  @ObjectLink {name}: any;\n"));
            }
            ArkField::Provide { alias, name, init } => {
                decorated_names.insert(name.clone());
                let dec = if alias == name {
                    "@Provide".to_string()
                } else {
                    format!("@Provide({alias:?})")
                };
                match init {
                    Some(v) => out.push_str(&format!("{pad}  {dec} {name}: any = {v};\n")),
                    None => out.push_str(&format!("{pad}  {dec} {name}: any;\n")),
                }
            }
            ArkField::Consume { alias, name } => {
                decorated_names.insert(name.clone());
                if alias == name {
                    out.push_str(&format!("{pad}  @Consume {name}: any;\n"));
                } else {
                    out.push_str(&format!("{pad}  @Consume({alias:?}) {name}: any;\n"));
                }
            }
            ArkField::LocalStorageLink { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @LocalStorageLink({key:?}) {name}: any = {init};\n"
                ));
            }
            ArkField::LocalStorageProp { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @LocalStorageProp({key:?}) {name}: any = {init};\n"
                ));
            }
            ArkField::StorageLink { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @StorageLink({key:?}) {name}: any = {init};\n"
                ));
            }
            ArkField::StorageProp { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @StorageProp({key:?}) {name}: any = {init};\n"
                ));
            }
            ArkField::Plain { name, init } => {
                out.push_str(&format!("{pad}  {name} = {init};\n"));
            }
        }
    }

    em.class_depth += 1;
    for (mname, mfid, attrs) in method_entries {
        if SYNTHETIC_VIEWPU_METHODS.contains(&mname.as_str()) {
            continue;
        }
        let kind = attrs
            .map(|a| a.kind)
            .unwrap_or_else(|| crate::recover::effective_kind(em.module, mfid));
        if matches!(kind, FunctionKind::Getter | FunctionKind::Setter)
            && decorated_names.contains(&mname)
        {
            continue;
        }

        if mname == "initialRender" {
            em.stats.class_methods += 1;
            let (_rf, mbody) = em.func_nodes(mfid, false);
            let ui_nodes = reconstruct_ui_body(em, &mbody, &link_names);
            out.push_str(&format!("{pad}  build() {{\n"));
            render_ui_nodes(&ui_nodes, indent + 2, out);
            out.push_str(&format!("{pad}  }}\n"));
            continue;
        }

        let is_builder = em.module.func(mfid).is_some()
            && body_has_observe_creation(&em.peek_prepared(mfid, false).body);
        if is_builder {
            em.stats.class_methods += 1;
            let (rf, mbody) = em.func_nodes(mfid, false);
            let visible = &rf.params[rf.hidden_params.min(rf.params.len())..];
            let clean_m = sanitize(&mname);
            let ui_nodes = reconstruct_ui_body(em, &mbody, &link_names);
            out.push_str(&format!(
                "{pad}  @Builder\n{pad}  {clean_m}({}) {{\n",
                visible.join(", ")
            ));
            for d in lex_decls(&mbody, &rf.params) {
                if !d.starts_with("v1_") {
                    out.push_str(&format!("{pad}    let {d};\n"));
                }
            }
            render_ui_nodes(&ui_nodes, indent + 2, out);
            out.push_str(&format!("{pad}  }}\n"));
            continue;
        }

        em.emit_class_method(pad, indent, &mname, mfid, attrs, out);
    }
    em.class_depth -= 1;

    out.push_str(&format!("{pad}}}\n"));
    true
}

fn clean_component_name(raw: &str) -> String {
    if let Some(pos) = raw.rfind('#')
        && pos + 1 < raw.len()
    {
        let cand = sanitize(&raw[pos + 1..]);
        if is_legal_ident(&cand) {
            return cand;
        }
    }
    let mut s = raw;
    if let Some(rest) = s.strip_prefix("___") {
        let digits_trimmed = rest.trim_start_matches(|c: char| c.is_ascii_digit());
        if let Some(after) = digits_trimmed.strip_prefix("__")
            && !after.is_empty()
            && is_legal_ident(after)
        {
            s = after;
        }
    }
    sanitize(s)
}

fn collect_const_bindings(nodes: &[SNode]) -> BTreeMap<String, Expr> {
    let mut map = BTreeMap::new();
    let mut stack: Vec<std::slice::Iter<'_, SNode>> = vec![nodes.iter()];
    while let Some(iter) = stack.last_mut() {
        let Some(n) = iter.next() else {
            stack.pop();
            continue;
        };
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    match l {
                        Leaf::Raw(Stmt::Declare { name, value, .. }) => {
                            map.insert(name.clone(), value.clone());
                        }
                        Leaf::Raw(Stmt::LexStore { name, value, .. }) => {
                            map.entry(name.clone()).or_insert_with(|| value.clone());
                        }
                        _ => {}
                    }
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                stack.push(otherwise.iter());
                stack.push(then.iter());
            }
            _ => {}
        }
    }
    map
}

fn resolve_expr<'a>(mut e: &'a Expr, env: &'a BTreeMap<String, Expr>) -> &'a Expr {
    for _ in 0..8 {
        match e {
            Expr::Temp { name, .. } | Expr::Ident(name) => match env.get(name) {
                Some(next) => e = next,
                None => break,
            },
            _ => break,
        }
    }
    e
}

fn ident_of(e: &Expr, env: &BTreeMap<String, Expr>) -> Option<String> {
    match resolve_expr(e, env) {
        Expr::Ident(s) | Expr::Temp { name: s, .. } => Some(base_ident(s).to_string()),
        _ => None,
    }
}

fn base_ident(s: &str) -> &str {
    match s.split_once('$') {
        Some((prefix, suffix)) if suffix.chars().all(|c: char| c.is_ascii_digit()) => prefix,
        _ => s,
    }
}

fn is_view_heritage(heritage: Option<&Expr>, env: &BTreeMap<String, Expr>) -> bool {
    let Some(h) = heritage else { return false };
    matches!(ident_of(h, env).as_deref(), Some("ViewPU" | "View"))
}

fn heritage_mentions_view(heritage: Option<&Expr>) -> bool {
    match heritage {
        Some(Expr::Ident(s) | Expr::Temp { name: s, .. }) => {
            matches!(base_ident(s), "ViewPU" | "View")
        }
        _ => false,
    }
}

fn is_finalize_construction_polyfill(
    cond: &Expr,
    then: &[SNode],
    otherwise: &[SNode],
    env: &BTreeMap<String, Expr>,
) -> bool {
    if expr_mentions_finalize_str(cond, env) {
        return true;
    }
    for branch in [then, otherwise] {
        for n in branch {
            if let SNode::Stmts(leaves) = n {
                for l in leaves {
                    if let Leaf::Raw(Stmt::Expr(e)) = l
                        && expr_mentions_finalize_str(e, env)
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn expr_mentions_finalize_str(root: &Expr, env: &BTreeMap<String, Expr>) -> bool {
    let mut stack: Vec<&Expr> = vec![root];
    let mut budget = 4096usize;
    while let Some(e) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget -= 1;
        match resolve_expr(e, env) {
            Expr::Lit(Lit::String(s)) if s == "finalizeConstruction" => return true,
            Expr::Unary { operand, .. } => stack.push(operand),
            Expr::Binary { left, right, .. } | Expr::Compare { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            Expr::Call { args, .. } => {
                for a in args.iter().rev() {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    false
}

fn is_pure_arkui_main_setup(value: &Expr, env: &BTreeMap<String, Expr>) -> bool {
    match value {
        Expr::Lit(Lit::Undefined) => true,
        Expr::Lit(Lit::String(s)) if s == "finalizeConstruction" => true,
        Expr::Ident(s) | Expr::Temp { name: s, .. } => matches!(
            base_ident(s),
            "ViewPU" | "View" | "Reflect" | "registerNamedRoute" | "loadDocument"
        ),
        Expr::PropName { object, name, .. }
            if matches!(name.as_str(), "prototype" | "set")
                && matches!(
                    ident_of(object, env).as_deref(),
                    Some("ViewPU" | "View" | "Reflect")
                ) =>
        {
            true
        }
        _ => false,
    }
}

fn is_class_alias_store(value: &Expr, env: &BTreeMap<String, Expr>) -> bool {
    matches!(resolve_expr(value, env), Expr::Class { heritage, .. } if is_view_heritage(heritage.as_deref(), env))
}

fn is_prototype_touch(e: &Expr) -> bool {
    matches!(e, Expr::PropName { name, .. } if name == "prototype")
}

fn extract_entry_registration(e: &Expr, env: &BTreeMap<String, Expr>) -> Option<String> {
    let Expr::Call { callee, args, .. } = e else {
        return None;
    };
    let cname = ident_of(callee, env)?;
    if cname == "registerNamedRoute" {
        return Some("*".to_string());
    }
    if cname == "loadDocument"
        && let Some(first) = args.first()
        && let Expr::Call {
            callee: new_callee,
            kind: CallKind::New,
            ..
        } = resolve_expr(first, env)
    {
        return ident_of(new_callee, env);
    }
    None
}

// ── Constructor field extraction ──────────────────────────────────────────

fn extract_arkui_fields(em: &mut Emitter<'_>, ctor_body: &[SNode]) -> Vec<ArkField> {
    let env = collect_const_bindings(ctor_body);
    let mut fields: Vec<ArkField> = Vec::new();
    let mut provided_aliases: BTreeMap<String, String> = BTreeMap::new();

    walk_ctor_stmts(ctor_body, &mut |stmt| {
        if let Stmt::Expr(Expr::Call { callee, args, .. }) = stmt
            && is_method_named(callee, "addProvidedVar", &env)
            && args.len() >= 2
            && let Some(alias) = string_lit(args.first(), &env)
            && let Some(prop) = backing_prop_name(&args[1], &env)
        {
            provided_aliases.insert(prop, alias);
        }
    });

    let mut seen = BTreeSet::new();
    walk_ctor_stmts(ctor_body, &mut |stmt| {
        let Stmt::StoreProp {
            name: raw_prop,
            value,
            ..
        } = stmt
        else {
            return;
        };
        if raw_prop == "paramsGenerator_" {
            return;
        }
        let val = resolve_expr(value, &env);
        if let Some(prop) = raw_prop.strip_prefix("__") {
            if prop.is_empty() || !seen.insert(prop.to_string()) {
                return;
            }
            let prop_name = prop.to_string();
            match val {
                Expr::Call {
                    callee,
                    args,
                    kind: CallKind::New,
                    ..
                } => {
                    let wrapper = ident_of(callee, &env).unwrap_or_default();
                    let init_str = args
                        .first()
                        .map(|a| render_clean_expr(em, resolve_expr(a, &env)))
                        .filter(|s| s != "undefined");
                    match wrapper.as_str() {
                        "ObservedPropertySimplePU"
                        | "ObservedPropertyObjectPU"
                        | "ObservedPropertySimple"
                        | "ObservedPropertyObject" => {
                            if let Some(alias) = provided_aliases.get(&prop_name) {
                                fields.push(ArkField::Provide {
                                    alias: alias.clone(),
                                    name: prop_name,
                                    init: init_str,
                                });
                            } else {
                                fields.push(ArkField::State {
                                    name: prop_name,
                                    init: init_str,
                                });
                            }
                        }
                        "SynchedPropertySimpleOneWayPU"
                        | "SynchedPropertyObjectOneWayPU"
                        | "SynchedPropertySimpleOneWay"
                        | "SynchedPropertyObjectOneWay" => {
                            fields.push(ArkField::Prop { name: prop_name });
                        }
                        "SynchedPropertySimpleTwoWayPU"
                        | "SynchedPropertyObjectTwoWayPU"
                        | "SynchedPropertySimpleTwoWay"
                        | "SynchedPropertyObjectTwoWay" => {
                            fields.push(ArkField::Link { name: prop_name });
                        }
                        "SynchedPropertyNesedObjectPU" | "SynchedPropertyNestedObjectPU" => {
                            fields.push(ArkField::ObjectLink { name: prop_name });
                        }
                        _ => {}
                    }
                }
                Expr::Call { callee, args, .. } => {
                    if is_method_named(callee, "initializeConsume", &env) {
                        let alias =
                            string_lit(args.first(), &env).unwrap_or_else(|| prop_name.clone());
                        fields.push(ArkField::Consume {
                            alias,
                            name: prop_name,
                        });
                    } else if is_method_named(callee, "createLocalStorageLink", &env) {
                        let key =
                            string_lit(args.first(), &env).unwrap_or_else(|| prop_name.clone());
                        let init = args
                            .get(1)
                            .map(|a| render_clean_expr(em, resolve_expr(a, &env)))
                            .unwrap_or_else(|| "undefined".to_string());
                        fields.push(ArkField::LocalStorageLink {
                            key,
                            name: prop_name,
                            init,
                        });
                    } else if is_method_named(callee, "createLocalStorageProp", &env) {
                        let key =
                            string_lit(args.first(), &env).unwrap_or_else(|| prop_name.clone());
                        let init = args
                            .get(1)
                            .map(|a| render_clean_expr(em, resolve_expr(a, &env)))
                            .unwrap_or_else(|| "undefined".to_string());
                        fields.push(ArkField::LocalStorageProp {
                            key,
                            name: prop_name,
                            init,
                        });
                    } else if is_method_named(callee, "setAndLink", &env)
                        || is_method_named(callee, "createStorageLink", &env)
                    {
                        let key =
                            string_lit(args.first(), &env).unwrap_or_else(|| prop_name.clone());
                        let init = args
                            .get(1)
                            .map(|a| render_clean_expr(em, resolve_expr(a, &env)))
                            .unwrap_or_else(|| "undefined".to_string());
                        fields.push(ArkField::StorageLink {
                            key,
                            name: prop_name,
                            init,
                        });
                    } else if is_method_named(callee, "setAndProp", &env)
                        || is_method_named(callee, "createStorageProp", &env)
                    {
                        let key =
                            string_lit(args.first(), &env).unwrap_or_else(|| prop_name.clone());
                        let init = args
                            .get(1)
                            .map(|a| render_clean_expr(em, resolve_expr(a, &env)))
                            .unwrap_or_else(|| "undefined".to_string());
                        fields.push(ArkField::StorageProp {
                            key,
                            name: prop_name,
                            init,
                        });
                    }
                }
                _ => {}
            }
        } else if is_legal_ident(raw_prop) && seen.insert(raw_prop.clone()) {
            let init = render_clean_expr(em, val);
            fields.push(ArkField::Plain {
                name: raw_prop.clone(),
                init,
            });
        }
    });

    fields
}

fn walk_ctor_stmts(nodes: &[SNode], f: &mut impl FnMut(&Stmt)) {
    let mut stack: Vec<std::slice::Iter<'_, SNode>> = vec![nodes.iter()];
    while let Some(iter) = stack.last_mut() {
        let Some(n) = iter.next() else {
            stack.pop();
            continue;
        };
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    if let Leaf::Raw(s) = l {
                        f(s);
                    }
                }
            }
            SNode::If {
                then, otherwise, ..
            } => {
                stack.push(otherwise.iter());
                stack.push(then.iter());
            }
            _ => {}
        }
    }
}

fn is_method_named(callee: &Expr, target: &str, env: &BTreeMap<String, Expr>) -> bool {
    match resolve_expr(callee, env) {
        Expr::PropName { name, .. } => name == target,
        Expr::Ident(s) | Expr::Temp { name: s, .. } => base_ident(s) == target,
        _ => false,
    }
}

fn string_lit(e: Option<&Expr>, env: &BTreeMap<String, Expr>) -> Option<String> {
    match resolve_expr(e?, env) {
        Expr::Lit(Lit::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn backing_prop_name(e: &Expr, env: &BTreeMap<String, Expr>) -> Option<String> {
    match resolve_expr(e, env) {
        Expr::PropName { name, .. } => name.strip_prefix("__").map(str::to_string),
        Expr::Ident(s) | Expr::Temp { name: s, .. } => {
            base_ident(s).strip_prefix("__").map(str::to_string)
        }
        _ => None,
    }
}

// ── Declarative UI tree (`build()` / `@Builder`) reconstruction ───────────

struct OpenComp {
    name: String,
    args: String,
    attrs: Vec<(String, String)>,
    children: Vec<UiNode>,
}

fn body_has_observe_creation(nodes: &[SNode]) -> bool {
    let env = collect_const_bindings(nodes);
    let mut found = false;
    walk_ctor_stmts(nodes, &mut |s| {
        if let Stmt::Expr(Expr::Call { callee, .. }) = s
            && (is_method_named(callee, "observeComponentCreation2", &env)
                || is_method_named(callee, "observeComponentCreation", &env))
        {
            found = true;
        }
    });
    found
}

fn reconstruct_ui_body(
    em: &mut Emitter<'_>,
    nodes: &[SNode],
    link_names: &BTreeSet<String>,
) -> Vec<UiNode> {
    let env = collect_const_bindings(nodes);
    let mut stack: Vec<OpenComp> = Vec::new();
    let mut root: Vec<UiNode> = Vec::new();

    process_ui_snodes(em, nodes, &env, link_names, &mut stack, &mut root);

    while let Some(open) = stack.pop() {
        let finished = UiNode::Component {
            name: open.name,
            args: open.args,
            attrs: open.attrs,
            children: open.children,
        };
        push_ui_node(&mut stack, &mut root, finished);
    }
    root
}

fn push_ui_node(stack: &mut [OpenComp], root: &mut Vec<UiNode>, node: UiNode) {
    if let Some(top) = stack.last_mut() {
        top.children.push(node);
    } else {
        root.push(node);
    }
}

fn flush_self_closing_top(stack: &mut Vec<OpenComp>, root: &mut Vec<UiNode>) {
    if stack
        .last()
        .is_some_and(|c| SELF_CLOSING_COMPONENTS.contains(&c.name.as_str()))
        && let Some(open) = stack.pop()
    {
        push_ui_node(
            stack,
            root,
            UiNode::Component {
                name: open.name,
                args: open.args,
                attrs: open.attrs,
                children: open.children,
            },
        );
    }
}

fn process_ui_snodes(
    em: &mut Emitter<'_>,
    nodes: &[SNode],
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
    stack: &mut Vec<OpenComp>,
    root: &mut Vec<UiNode>,
) {
    for n in nodes {
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    let Leaf::Raw(s) = l else { continue };
                    match s {
                        Stmt::Declare { .. }
                        | Stmt::LexStore { .. }
                        | Stmt::Return(None)
                        | Stmt::Elided { .. } => {}
                        Stmt::Expr(e) => {
                            process_ui_expr(em, e, env, link_names, stack, root);
                        }
                        other => {
                            let mut buf = String::new();
                            em.emit_stmt(other, 0, &mut buf);
                            let trimmed = buf.trim().to_string();
                            if !trimmed.is_empty() {
                                push_ui_node(stack, root, UiNode::RawStmt(trimmed));
                            }
                        }
                    }
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                if then.is_empty() && otherwise.is_empty() {
                    continue;
                }
                let cond_s = render_clean_expr(em, cond);
                let mut then_nodes = Vec::new();
                let mut then_stack = Vec::new();
                process_ui_snodes(em, then, env, link_names, &mut then_stack, &mut then_nodes);
                while let Some(o) = then_stack.pop() {
                    push_ui_node(
                        &mut then_stack,
                        &mut then_nodes,
                        UiNode::Component {
                            name: o.name,
                            args: o.args,
                            attrs: o.attrs,
                            children: o.children,
                        },
                    );
                }
                let mut else_nodes = Vec::new();
                let mut else_stack = Vec::new();
                process_ui_snodes(
                    em,
                    otherwise,
                    env,
                    link_names,
                    &mut else_stack,
                    &mut else_nodes,
                );
                while let Some(o) = else_stack.pop() {
                    push_ui_node(
                        &mut else_stack,
                        &mut else_nodes,
                        UiNode::Component {
                            name: o.name,
                            args: o.args,
                            attrs: o.attrs,
                            children: o.children,
                        },
                    );
                }
                push_ui_node(
                    stack,
                    root,
                    UiNode::If {
                        cond: cond_s,
                        then_body: then_nodes,
                        else_body: else_nodes,
                    },
                );
            }
            other => {
                let mut buf = String::new();
                em.emit_node(other, 0, &mut buf);
                let trimmed = buf.trim().to_string();
                if !trimmed.is_empty() {
                    push_ui_node(stack, root, UiNode::RawStmt(trimmed));
                }
            }
        }
    }
}

fn process_ui_expr(
    em: &mut Emitter<'_>,
    e: &Expr,
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
    stack: &mut Vec<OpenComp>,
    root: &mut Vec<UiNode>,
) {
    let Expr::Call { callee, args, .. } = e else {
        return;
    };

    if is_method_named(callee, "observeComponentCreation2", env)
        || is_method_named(callee, "observeComponentCreation", env)
    {
        flush_self_closing_top(stack, root);
        if let Some(first) = args.first()
            && let Expr::Closure { body: fn_id, .. } = resolve_expr(first, env)
        {
            let fn_id = *fn_id;
            let second_meta = args.get(1).map(|a| resolve_expr(a, env));
            handle_observe_closure(em, fn_id, second_meta, link_names, stack, root);
            return;
        }
    }

    if is_method_named(callee, "pop", env) {
        let comp_name = receiver_component_name(callee, e, env);
        if matches!(comp_name.as_deref(), Some("If" | "ForEach" | "LazyForEach")) {
            return;
        }
        flush_self_closing_top(stack, root);
        if let Some(target) = &comp_name
            && let Some(pos) = stack.iter().rposition(|c| &c.name == target)
        {
            while stack.len() > pos + 1 {
                if let Some(inner) = stack.pop() {
                    push_ui_node(
                        stack,
                        root,
                        UiNode::Component {
                            name: inner.name,
                            args: inner.args,
                            attrs: inner.attrs,
                            children: inner.children,
                        },
                    );
                }
            }
            if let Some(open) = stack.pop() {
                push_ui_node(
                    stack,
                    root,
                    UiNode::Component {
                        name: open.name,
                        args: open.args,
                        attrs: open.attrs,
                        children: open.children,
                    },
                );
            }
            return;
        }
    }

    if is_method_named(callee, "create", env)
        && let Some(comp) = receiver_component_name(callee, e, env)
        && (comp == "LazyForEach" || comp == "ForEach")
        && args.len() >= 4
    {
        flush_self_closing_top(stack, root);
        let arr_s = render_clean_expr(em, resolve_expr(&args[2], env));
        if let Some((item_p, idx_p, item_body)) = extract_foreach_gen(em, &args[3], env, link_names)
        {
            let key_s = args
                .get(4)
                .map(|k| render_clean_expr(em, resolve_expr(k, env)));
            push_ui_node(
                stack,
                root,
                UiNode::ForEach {
                    is_lazy: comp == "LazyForEach",
                    arr: arr_s,
                    item_param: item_p,
                    idx_param: idx_p,
                    body: item_body,
                    key_gen: key_s,
                },
            );
            return;
        }
    }

    if is_method_named(callee, "forEachUpdateFunction", env) && args.len() >= 3 {
        let arr_s = render_clean_expr(em, resolve_expr(&args[1], env));
        let item_arg = unwrap_foreach_item_gen(&args[2], env).unwrap_or(&args[2]);
        if let Some((item_p, idx_p, item_body)) = extract_foreach_gen(em, item_arg, env, link_names)
        {
            let key_s = args
                .get(3)
                .map(|k| render_clean_expr(em, resolve_expr(k, env)));
            push_ui_node(
                stack,
                root,
                UiNode::ForEach {
                    is_lazy: false,
                    arr: arr_s,
                    item_param: item_p,
                    idx_param: idx_p,
                    body: item_body,
                    key_gen: key_s,
                },
            );
            return;
        }
    }

    if is_method_named(callee, "ifElseBranchUpdateFunction", env)
        && args.len() >= 2
        && let Expr::Closure { body: br_fn, .. } = resolve_expr(&args[1], env)
    {
        let br_fn = *br_fn;
        let (_rf, br_body) = em.func_nodes(br_fn, false);
        let children = reconstruct_ui_body(em, &br_body, link_names);
        for c in children {
            push_ui_node(stack, root, c);
        }
        return;
    }

    let rendered = render_clean_expr(em, e);
    if !rendered.is_empty() {
        push_ui_node(stack, root, UiNode::RawStmt(format!("{rendered};")));
    }
}

fn handle_observe_closure(
    em: &mut Emitter<'_>,
    closure_fn: FuncId,
    second_meta: Option<&Expr>,
    link_names: &BTreeSet<String>,
    stack: &mut Vec<OpenComp>,
    root: &mut Vec<UiNode>,
) {
    let (_rf, body) = em.func_nodes(closure_fn, false);
    let env = collect_const_bindings(&body);

    if let Some(meta_name) = custom_child_meta_name(second_meta, &env) {
        let props = extract_custom_child_props(em, &body, &env, link_names);
        push_ui_node(
            stack,
            root,
            UiNode::CustomChild {
                name: meta_name,
                props,
            },
        );
        return;
    }
    if let Some((child_name, props)) = extract_viewpu_child_from_body(em, &body, &env, link_names) {
        push_ui_node(
            stack,
            root,
            UiNode::CustomChild {
                name: child_name,
                props,
            },
        );
        return;
    }

    let meta_ident = second_meta.and_then(|m| ident_of(m, &env));
    if meta_ident.as_deref() == Some("If") || body_calls_comp_create(&body, &env, "If") {
        for n in &body {
            if let SNode::If { .. } = n {
                process_ui_snodes(em, std::slice::from_ref(n), &env, link_names, stack, root);
            }
        }
        return;
    }

    let mut comp_name: Option<String> = meta_ident;
    let mut create_args = String::new();
    let mut attrs: Vec<(String, String)> = Vec::new();
    let mut saw_pop = false;

    walk_ctor_stmts(&body, &mut |s| {
        let Stmt::Expr(call_expr @ Expr::Call { callee, args, .. }) = s else {
            return;
        };
        let Some(mname) = method_name_of(callee, &env) else {
            return;
        };
        let recv = receiver_component_name(callee, call_expr, &env);
        if comp_name.is_none() {
            comp_name = recv.clone();
        }
        if recv.is_some() && recv == comp_name {
            match mname.as_str() {
                "create" | "createWithLabel" | "createWithChild" => {
                    create_args = render_call_args_clean(em, args, &env, link_names, true);
                }
                "pop" => {
                    saw_pop = true;
                }
                attr => {
                    let attr_args = render_call_args_clean(em, args, &env, link_names, false);
                    attrs.push((attr.to_string(), attr_args));
                }
            }
        }
    });

    if let Some(name) = comp_name {
        if name == "ForEach" {
            process_ui_snodes(em, &body, &env, link_names, stack, root);
            return;
        }
        let open = OpenComp {
            name,
            args: create_args,
            attrs,
            children: Vec::new(),
        };
        if saw_pop {
            push_ui_node(
                stack,
                root,
                UiNode::Component {
                    name: open.name,
                    args: open.args,
                    attrs: open.attrs,
                    children: Vec::new(),
                },
            );
        } else {
            stack.push(open);
        }
    }
}

fn method_name_of(callee: &Expr, env: &BTreeMap<String, Expr>) -> Option<String> {
    match resolve_expr(callee, env) {
        Expr::PropName { name, .. } => Some(name.clone()),
        Expr::Ident(s) | Expr::Temp { name: s, .. } => Some(base_ident(s).to_string()),
        _ => None,
    }
}

fn receiver_component_name(
    callee: &Expr,
    whole_call: &Expr,
    env: &BTreeMap<String, Expr>,
) -> Option<String> {
    if let Expr::PropName { object, .. } = resolve_expr(callee, env)
        && let Some(id) = ident_of(object, env)
    {
        return Some(id);
    }
    if let Expr::Call { this: Some(t), .. } = whole_call
        && let Some(id) = ident_of(t, env)
    {
        return Some(id);
    }
    None
}

fn body_calls_comp_create(nodes: &[SNode], env: &BTreeMap<String, Expr>, comp: &str) -> bool {
    let mut hit = false;
    walk_ctor_stmts(nodes, &mut |s| {
        if let Stmt::Expr(call @ Expr::Call { callee, .. }) = s
            && is_method_named(callee, "create", env)
            && receiver_component_name(callee, call, env).as_deref() == Some(comp)
        {
            hit = true;
        }
    });
    hit
}

fn custom_child_meta_name(meta: Option<&Expr>, env: &BTreeMap<String, Expr>) -> Option<String> {
    match resolve_expr(meta?, env) {
        Expr::ObjectBuild { entries } => {
            for e in entries {
                if let ObjEntry::KeyValue(Lit::String(k), v) = e
                    && k == "name"
                    && let Expr::Lit(Lit::String(s)) = resolve_expr(v, env)
                {
                    return Some(s.clone());
                }
            }
            None
        }
        Expr::ObjectLit { entries } => {
            for (k, v) in entries {
                if let (Lit::String(ks), Lit::String(vs)) = (k, v)
                    && ks == "name"
                {
                    return Some(vs.clone());
                }
            }
            None
        }
        _ => None,
    }
}

fn collect_obj_prop_stores(nodes: &[SNode]) -> BTreeMap<String, Vec<(String, Expr)>> {
    let mut map: BTreeMap<String, Vec<(String, Expr)>> = BTreeMap::new();
    walk_ctor_stmts(nodes, &mut |s| {
        if let Stmt::StoreProp {
            object,
            name,
            value,
            ..
        } = s
            && let Some(ovar) = raw_ident_of(object)
        {
            map.entry(ovar)
                .or_default()
                .push((name.clone(), value.clone()));
        }
    });
    map
}

fn extract_custom_child_props(
    em: &mut Emitter<'_>,
    body: &[SNode],
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
) -> Option<String> {
    let obj_stores = collect_obj_prop_stores(body);
    let mut new_props: Option<String> = None;
    let mut update_props: Option<String> = None;
    walk_ctor_stmts(body, &mut |s| {
        if let Stmt::Declare {
            value:
                Expr::Call {
                    args,
                    kind: CallKind::New,
                    ..
                },
            ..
        } = s
            && new_props.is_none()
            && let Some(arg1) = args.get(1)
        {
            new_props =
                render_props_object(em, arg1, &obj_stores, env, link_names).filter(|p| p != "{}");
        }
        if let Stmt::Expr(Expr::Call { callee, args, .. }) = s {
            if new_props.is_none()
                && is_method_named(callee, "create", env)
                && let Some(first) = args.first()
                && let Expr::Call {
                    args: new_args,
                    kind: CallKind::New,
                    ..
                } = resolve_expr(first, env)
                && let Some(arg1) = new_args.get(1)
            {
                new_props = render_props_object(em, arg1, &obj_stores, env, link_names)
                    .filter(|p| p != "{}");
            }
            if update_props.is_none()
                && is_method_named(callee, "updateStateVarsOfChildByElmtId", env)
                && let Some(arg1) = args.get(1)
            {
                update_props = render_props_object(em, arg1, &obj_stores, env, link_names)
                    .filter(|p| p != "{}");
            }
        }
    });
    new_props.or(update_props)
}

fn extract_viewpu_child_from_body(
    em: &mut Emitter<'_>,
    body: &[SNode],
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
) -> Option<(String, Option<String>)> {
    let obj_stores = collect_obj_prop_stores(body);
    let mut found: Option<(String, Option<String>)> = None;
    let mut saw_view_create = false;
    walk_ctor_stmts(body, &mut |s| {
        if let Stmt::Expr(call @ Expr::Call { callee, args, .. }) = s
            && is_method_named(callee, "create", env)
            && matches!(
                receiver_component_name(callee, call, env).as_deref(),
                Some("ViewPU" | "View")
            )
        {
            saw_view_create = true;
            if found.is_none()
                && let Some(first) = args.first()
                && let Expr::Call {
                    callee: new_callee,
                    args: new_args,
                    kind: CallKind::New,
                    ..
                } = resolve_expr(first, env)
                && let Some(cname) = ident_of(new_callee, env)
            {
                let props = new_args
                    .get(1)
                    .and_then(|a| render_props_object(em, a, &obj_stores, env, link_names))
                    .filter(|p| p != "{}");
                found = Some((clean_component_name(&cname), props));
            }
        }
        if let Stmt::Declare {
            value:
                Expr::Call {
                    callee,
                    args,
                    kind: CallKind::New,
                    ..
                },
            ..
        } = s
            && let Some(cname) = ident_of(callee, env)
            && !cname.starts_with("ObservedProperty")
            && !cname.starts_with("SynchedProperty")
        {
            let props = args
                .get(1)
                .and_then(|a| render_props_object(em, a, &obj_stores, env, link_names))
                .filter(|p| p != "{}");
            found = Some((clean_component_name(&cname), props));
        }
    });
    if saw_view_create { found } else { None }
}

fn render_props_object(
    em: &mut Emitter<'_>,
    raw_e: &Expr,
    obj_stores: &BTreeMap<String, Vec<(String, Expr)>>,
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
) -> Option<String> {
    let extra = raw_ident_of(raw_e).and_then(|id| obj_stores.get(&id));
    let e = resolve_expr(raw_e, env);
    match e {
        Expr::ObjectBuild { entries } => {
            let mut ordered_keys: Vec<String> = Vec::new();
            let mut values: BTreeMap<String, String> = BTreeMap::new();
            for entry in entries {
                if let ObjEntry::KeyValue(Lit::String(k), value) = entry {
                    let rv = resolve_expr(value, env);
                    let vs = render_prop_val(em, rv, obj_stores, env, link_names);
                    if !values.contains_key(k) {
                        ordered_keys.push(k.clone());
                    }
                    values.insert(k.clone(), vs);
                }
            }
            if let Some(stores) = extra {
                for (k, value) in stores {
                    let vs = render_prop_val(em, value, obj_stores, env, link_names);
                    if !values.contains_key(k) {
                        ordered_keys.push(k.clone());
                    }
                    values.insert(k.clone(), vs);
                }
            }
            Some(format_kv_map(ordered_keys, values))
        }
        Expr::ObjectLit { entries } => {
            let mut ordered_keys: Vec<String> = Vec::new();
            let mut values: BTreeMap<String, String> = BTreeMap::new();
            for (k, v) in entries {
                if let Lit::String(ks) = k {
                    let vs = em.render_lit_js(v);
                    if !values.contains_key(ks) {
                        ordered_keys.push(ks.clone());
                    }
                    values.insert(ks.clone(), vs);
                }
            }
            if let Some(stores) = extra {
                for (k, value) in stores {
                    let vs = render_prop_val(em, value, obj_stores, env, link_names);
                    if !values.contains_key(k) {
                        ordered_keys.push(k.clone());
                    }
                    values.insert(k.clone(), vs);
                }
            }
            Some(format_kv_map(ordered_keys, values))
        }
        _ => Some(render_clean_expr(em, e)),
    }
}

fn render_prop_val(
    em: &mut Emitter<'_>,
    raw_rv: &Expr,
    obj_stores: &BTreeMap<String, Vec<(String, Expr)>>,
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
) -> String {
    let rv = resolve_expr(raw_rv, env);
    if matches!(rv, Expr::ObjectBuild { .. } | Expr::ObjectLit { .. })
        && let Some(nested) = render_props_object(em, raw_rv, obj_stores, env, link_names)
    {
        return nested;
    }
    if let Some(prop) = backing_prop_name(rv, env) {
        return format!("${prop}");
    }
    let raw_s = em.estr(rv);
    for alias in ["v1_1$2.__", "v1_1$1.__", "v1_1.__", "v1_2.__", "this.__"] {
        if let Some(prop) = raw_s.strip_prefix(alias) {
            return format!("${prop}");
        }
    }
    let cleaned = clean_this_aliases(&raw_s);
    if let Some(prop) = cleaned.strip_prefix("this.")
        && link_names.contains(prop)
    {
        return format!("${prop}");
    }
    cleaned
}

fn format_kv_map(ordered_keys: Vec<String>, mut values: BTreeMap<String, String>) -> String {
    if ordered_keys.is_empty() {
        return "{}".to_string();
    }
    let parts: Vec<String> = ordered_keys
        .into_iter()
        .filter_map(|k| {
            let v = values.remove(&k)?;
            if is_legal_ident(&k) {
                Some(format!("{k}: {v}"))
            } else {
                Some(format!("{k:?}: {v}"))
            }
        })
        .collect();
    format!("{{ {} }}", parts.join(", "))
}

fn unwrap_foreach_item_gen<'a>(e: &'a Expr, env: &'a BTreeMap<String, Expr>) -> Option<&'a Expr> {
    let resolved = resolve_expr(e, env);
    if let Expr::Closure { .. } = resolved {
        return Some(resolved);
    }
    if let Expr::ObjectBuild { entries } = resolved {
        for entry in entries {
            if let ObjEntry::KeyValue(_, value) = entry
                && matches!(resolve_expr(value, env), Expr::Closure { .. })
            {
                return Some(resolve_expr(value, env));
            }
        }
    }
    None
}

fn extract_foreach_gen(
    em: &mut Emitter<'_>,
    gen_expr: &Expr,
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
) -> Option<(String, Option<String>, Vec<UiNode>)> {
    let Expr::Closure { body: fn_id, .. } = resolve_expr(gen_expr, env) else {
        return None;
    };
    let (rf, body) = em.func_nodes(*fn_id, false);
    let visible = &rf.params[rf.hidden_params.min(rf.params.len())..];
    let item_p = visible
        .first()
        .cloned()
        .unwrap_or_else(|| "item".to_string());
    let idx_p = visible.get(1).cloned();
    let ui = reconstruct_ui_body(em, &body, link_names);
    Some((item_p, idx_p, ui))
}

fn render_call_args_clean(
    em: &mut Emitter<'_>,
    args: &[Expr],
    env: &BTreeMap<String, Expr>,
    link_names: &BTreeSet<String>,
    strip_nav_meta: bool,
) -> String {
    let mut rendered = Vec::new();
    for (idx, a) in args.iter().enumerate() {
        let ra = resolve_expr(a, env);
        if strip_nav_meta && idx == 1 && is_navigation_meta_obj(ra) {
            continue;
        }
        if matches!(ra, Expr::ObjectBuild { .. } | Expr::ObjectLit { .. })
            && let Some(obj_s) = render_props_object(em, a, &BTreeMap::new(), env, link_names)
        {
            rendered.push(obj_s);
            continue;
        }
        rendered.push(render_clean_expr(em, ra));
    }
    rendered.join(", ")
}

fn is_navigation_meta_obj(e: &Expr) -> bool {
    match e {
        Expr::ObjectBuild { entries } => entries.iter().any(|entry| {
            matches!(
                entry,
                ObjEntry::KeyValue(Lit::String(k), _) if k == "isUserCreateStack" || k == "pagePath"
            )
        }),
        Expr::ObjectLit { entries } => entries.iter().any(
            |(k, _)| matches!(k, Lit::String(ks) if ks == "isUserCreateStack" || ks == "pagePath"),
        ),
        _ => false,
    }
}

fn render_clean_expr(em: &mut Emitter<'_>, e: &Expr) -> String {
    let raw = em.estr(e);
    clean_this_aliases(&raw)
}

fn clean_this_aliases(raw: &str) -> String {
    let mut s = raw.to_string();
    for alias in ["v1_1$2.", "v1_1$1.", "v1_1.", "v1_2$1.", "v1_2."] {
        s = s.replace(alias, "this.");
    }
    s = s.replace("this.__", "this.");
    s
}

fn render_ui_nodes(nodes: &[UiNode], indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    for node in nodes {
        match node {
            UiNode::Component {
                name,
                args,
                attrs,
                children,
            } => {
                if children.is_empty() {
                    out.push_str(&format!("{pad}{name}({args})"));
                    for (aname, aargs) in attrs {
                        out.push_str(&format!("\n{pad}  .{aname}({aargs})"));
                    }
                    out.push('\n');
                } else {
                    out.push_str(&format!("{pad}{name}({args}) {{\n"));
                    render_ui_nodes(children, indent + 1, out);
                    out.push_str(&format!("{pad}}}"));
                    for (aname, aargs) in attrs {
                        out.push_str(&format!("\n{pad}  .{aname}({aargs})"));
                    }
                    out.push('\n');
                }
            }
            UiNode::CustomChild { name, props } => match props {
                Some(p) => out.push_str(&format!("{pad}{name}({p})\n")),
                None => out.push_str(&format!("{pad}{name}()\n")),
            },
            UiNode::If {
                cond,
                then_body,
                else_body,
            } => {
                out.push_str(&format!("{pad}if ({cond}) {{\n"));
                render_ui_nodes(then_body, indent + 1, out);
                if else_body.is_empty() {
                    out.push_str(&format!("{pad}}}\n"));
                } else {
                    out.push_str(&format!("{pad}}} else {{\n"));
                    render_ui_nodes(else_body, indent + 1, out);
                    out.push_str(&format!("{pad}}}\n"));
                }
            }
            UiNode::ForEach {
                is_lazy,
                arr,
                item_param,
                idx_param,
                body,
                key_gen,
            } => {
                let kw = if *is_lazy { "LazyForEach" } else { "ForEach" };
                let params = match idx_param {
                    Some(ix) => format!("({item_param}, {ix})"),
                    None => format!("({item_param})"),
                };
                out.push_str(&format!("{pad}{kw}({arr}, {params} => {{\n"));
                render_ui_nodes(body, indent + 1, out);
                match key_gen {
                    Some(k) => out.push_str(&format!("{pad}}}, {k})\n")),
                    None => out.push_str(&format!("{pad}}})\n")),
                }
            }
            UiNode::RawStmt(text) => {
                for line in text.lines() {
                    out.push_str(&format!("{pad}{line}\n"));
                }
            }
        }
    }
}
