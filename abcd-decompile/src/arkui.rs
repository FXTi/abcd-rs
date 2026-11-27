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
pub(crate) enum UiNode {
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

impl Clone for UiNode {
    fn clone(&self) -> Self {
        enum Step<'a> {
            Eval(&'a UiNode),
            FinishComp {
                name: String,
                args: String,
                attrs: Vec<(String, String)>,
                len: usize,
            },
            FinishIf {
                cond: String,
                then_len: usize,
                else_len: usize,
            },
            FinishForEach {
                is_lazy: bool,
                arr: String,
                item_param: String,
                idx_param: Option<String>,
                key_gen: Option<String>,
                len: usize,
            },
        }
        match self {
            UiNode::CustomChild { name, props } => {
                return UiNode::CustomChild {
                    name: name.clone(),
                    props: props.clone(),
                };
            }
            UiNode::RawStmt(s) => return UiNode::RawStmt(s.clone()),
            _ => {}
        }
        let mut steps = vec![Step::Eval(self)];
        let mut vals: Vec<UiNode> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Eval(node) => match node {
                    UiNode::CustomChild { name, props } => vals.push(UiNode::CustomChild {
                        name: name.clone(),
                        props: props.clone(),
                    }),
                    UiNode::RawStmt(s) => vals.push(UiNode::RawStmt(s.clone())),
                    UiNode::Component {
                        name,
                        args,
                        attrs,
                        children,
                    } => {
                        steps.push(Step::FinishComp {
                            name: name.clone(),
                            args: args.clone(),
                            attrs: attrs.clone(),
                            len: children.len(),
                        });
                        for c in children.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                    UiNode::If {
                        cond,
                        then_body,
                        else_body,
                    } => {
                        steps.push(Step::FinishIf {
                            cond: cond.clone(),
                            then_len: then_body.len(),
                            else_len: else_body.len(),
                        });
                        for c in else_body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                        for c in then_body.iter().rev() {
                            steps.push(Step::Eval(c));
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
                        steps.push(Step::FinishForEach {
                            is_lazy: *is_lazy,
                            arr: arr.clone(),
                            item_param: item_param.clone(),
                            idx_param: idx_param.clone(),
                            key_gen: key_gen.clone(),
                            len: body.len(),
                        });
                        for c in body.iter().rev() {
                            steps.push(Step::Eval(c));
                        }
                    }
                },
                Step::FinishComp {
                    name,
                    args,
                    attrs,
                    len,
                } => {
                    let children = vals.split_off(vals.len() - len);
                    vals.push(UiNode::Component {
                        name,
                        args,
                        attrs,
                        children,
                    });
                }
                Step::FinishIf {
                    cond,
                    then_len,
                    else_len,
                } => {
                    let else_body = vals.split_off(vals.len() - else_len);
                    let then_body = vals.split_off(vals.len() - then_len);
                    vals.push(UiNode::If {
                        cond,
                        then_body,
                        else_body,
                    });
                }
                Step::FinishForEach {
                    is_lazy,
                    arr,
                    item_param,
                    idx_param,
                    key_gen,
                    len,
                } => {
                    let body = vals.split_off(vals.len() - len);
                    vals.push(UiNode::ForEach {
                        is_lazy,
                        arr,
                        item_param,
                        idx_param,
                        body,
                        key_gen,
                    });
                }
            }
        }
        vals.pop().unwrap_or_else(|| UiNode::RawStmt(String::new()))
    }
}

impl PartialEq for UiNode {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (
                    UiNode::Component {
                        name: n1,
                        args: a1,
                        attrs: at1,
                        children: c1,
                    },
                    UiNode::Component {
                        name: n2,
                        args: a2,
                        attrs: at2,
                        children: c2,
                    },
                ) => {
                    if n1 != n2 || a1 != a2 || at1 != at2 || c1.len() != c2.len() {
                        return false;
                    }
                    stack.extend(c1.iter().zip(c2.iter()));
                }
                (
                    UiNode::CustomChild {
                        name: n1,
                        props: p1,
                    },
                    UiNode::CustomChild {
                        name: n2,
                        props: p2,
                    },
                ) => {
                    if n1 != n2 || p1 != p2 {
                        return false;
                    }
                }
                (
                    UiNode::If {
                        cond: c1,
                        then_body: t1,
                        else_body: e1,
                    },
                    UiNode::If {
                        cond: c2,
                        then_body: t2,
                        else_body: e2,
                    },
                ) => {
                    if c1 != c2 || t1.len() != t2.len() || e1.len() != e2.len() {
                        return false;
                    }
                    stack.extend(e1.iter().zip(e2.iter()));
                    stack.extend(t1.iter().zip(t2.iter()));
                }
                (
                    UiNode::ForEach {
                        is_lazy: l1,
                        arr: ar1,
                        item_param: ip1,
                        idx_param: ix1,
                        body: b1,
                        key_gen: k1,
                    },
                    UiNode::ForEach {
                        is_lazy: l2,
                        arr: ar2,
                        item_param: ip2,
                        idx_param: ix2,
                        body: b2,
                        key_gen: k2,
                    },
                ) => {
                    if l1 != l2
                        || ar1 != ar2
                        || ip1 != ip2
                        || ix1 != ix2
                        || k1 != k2
                        || b1.len() != b2.len()
                    {
                        return false;
                    }
                    stack.extend(b1.iter().zip(b2.iter()));
                }
                (UiNode::RawStmt(s1), UiNode::RawStmt(s2)) => {
                    if s1 != s2 {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for UiNode {}

impl std::fmt::Debug for UiNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Node(&'a UiNode),
            Nodes(&'a [UiNode]),
            Raw(&'static str),
            Owned(String),
        }
        fn push_list<'a>(tasks: &mut Vec<Task<'a>>, slice: &'a [UiNode]) {
            tasks.push(Task::Raw("]"));
            if !slice.is_empty() {
                tasks.push(Task::Nodes(slice));
            }
            tasks.push(Task::Raw("["));
        }
        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Raw(s) => f.write_str(s)?,
                Task::Owned(s) => f.write_str(&s)?,
                Task::Nodes(slice) => {
                    if let Some((first, rest)) = slice.split_first() {
                        if !rest.is_empty() {
                            tasks.push(Task::Nodes(rest));
                            tasks.push(Task::Raw(", "));
                        }
                        tasks.push(Task::Node(first));
                    }
                }
                Task::Node(node) => match node {
                    UiNode::CustomChild { name, props } => {
                        write!(f, "CustomChild {{ name: {name:?}, props: {props:?} }}")?;
                    }
                    UiNode::RawStmt(s) => write!(f, "RawStmt({s:?})")?,
                    UiNode::Component {
                        name,
                        args,
                        attrs,
                        children,
                    } => {
                        write!(
                            f,
                            "Component {{ name: {name:?}, args: {args:?}, attrs: {attrs:?}, children: "
                        )?;
                        tasks.push(Task::Raw(" }"));
                        push_list(&mut tasks, children);
                    }
                    UiNode::If {
                        cond,
                        then_body,
                        else_body,
                    } => {
                        write!(f, "If {{ cond: {cond:?}, then_body: ")?;
                        tasks.push(Task::Raw(" }"));
                        push_list(&mut tasks, else_body);
                        tasks.push(Task::Raw(", else_body: "));
                        push_list(&mut tasks, then_body);
                    }
                    UiNode::ForEach {
                        is_lazy,
                        arr,
                        item_param,
                        idx_param,
                        body,
                        key_gen,
                    } => {
                        write!(
                            f,
                            "ForEach {{ is_lazy: {is_lazy:?}, arr: {arr:?}, item_param: {item_param:?}, idx_param: {idx_param:?}, body: "
                        )?;
                        tasks.push(Task::Owned(format!(", key_gen: {key_gen:?} }}")));
                        push_list(&mut tasks, body);
                    }
                },
            }
        }
        Ok(())
    }
}

impl Drop for UiNode {
    fn drop(&mut self) {
        let mut stack: Vec<UiNode> = Vec::new();
        match self {
            UiNode::Component { children, .. } => stack.extend(std::mem::take(children)),
            UiNode::If {
                then_body,
                else_body,
                ..
            } => {
                stack.extend(std::mem::take(then_body));
                stack.extend(std::mem::take(else_body));
            }
            UiNode::ForEach { body, .. } => stack.extend(std::mem::take(body)),
            UiNode::CustomChild { .. } | UiNode::RawStmt(_) => return,
        }
        while let Some(mut cur) = stack.pop() {
            match &mut cur {
                UiNode::Component { children, .. } => stack.extend(std::mem::take(children)),
                UiNode::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    stack.extend(std::mem::take(then_body));
                    stack.extend(std::mem::take(else_body));
                }
                UiNode::ForEach { body, .. } => stack.extend(std::mem::take(body)),
                UiNode::CustomChild { .. } | UiNode::RawStmt(_) => {}
            }
        }
    }
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
    live_idents: BTreeSet<String>,
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

    // Pass 3: collect identifier/temp references across all SURVIVING statements
    // and control-flow headers of `func_main_0` so live `const t = undefined;`
    // or pure-setup declarations are never stripped while still referenced.
    collect_surviving_main_uses(nodes, env, plan);
}

fn collect_expr_raw_idents(root: &Expr, out: &mut BTreeSet<String>) {
    let mut stack = vec![root];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Ident(s) | Expr::Temp { name: s, .. } => {
                out.insert(s.clone());
            }
            _ => {}
        }
        stack.extend(crate::folds::expr_children(cur));
    }
}

fn collect_surviving_main_uses(
    nodes: &[SNode],
    env: &BTreeMap<String, Expr>,
    plan: &mut MainArkUiPlan,
) {
    let mut candidate_deps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut nstack: Vec<(&[SNode], bool)> = vec![(nodes, true)];
    while let Some((slice, at_root)) = nstack.pop() {
        for n in slice {
            match n {
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    if at_root && is_finalize_construction_polyfill(cond, then, otherwise, env) {
                        continue;
                    }
                    collect_expr_raw_idents(cond, &mut plan.live_idents);
                    nstack.push((otherwise, false));
                    nstack.push((then, false));
                }
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        let Leaf::Raw(s) = l else {
                            for e in crate::folds::leaf_exprs(l) {
                                collect_expr_raw_idents(e, &mut plan.live_idents);
                            }
                            continue;
                        };
                        if at_root {
                            match s {
                                Stmt::Declare {
                                    value: Expr::Class { heritage, .. },
                                    ..
                                } if is_view_heritage(heritage.as_deref(), env) => {
                                    continue;
                                }
                                Stmt::Declare { name, value, .. }
                                    if plan.proto_to_class.contains_key(name)
                                        || plan.dead_temps.contains(name)
                                        || is_pure_arkui_main_setup(value, env) =>
                                {
                                    let mut deps = BTreeSet::new();
                                    collect_expr_raw_idents(value, &mut deps);
                                    candidate_deps.insert(name.clone(), deps);
                                    continue;
                                }
                                Stmt::PhiDecl { name, .. } if plan.polyfill_phis.contains(name) => {
                                    continue;
                                }
                                Stmt::DefineMethod { object, func, .. }
                                | Stmt::StoreProp {
                                    object,
                                    value: func,
                                    ..
                                } if raw_ident_of(object)
                                    .is_some_and(|p| plan.proto_to_class.contains_key(&p))
                                    && matches!(resolve_expr(func, env), Expr::Closure { .. }) =>
                                {
                                    continue;
                                }
                                Stmt::StoreDyn {
                                    object, key, value, ..
                                } if raw_ident_of(object)
                                    .is_some_and(|p| plan.proto_to_class.contains_key(&p))
                                    && string_lit(Some(key), env)
                                        .is_some_and(|k| k.starts_with("#~@"))
                                    && matches!(resolve_expr(value, env), Expr::Closure { .. }) =>
                                {
                                    continue;
                                }
                                Stmt::Expr(Expr::DefineGetterSetter { obj, .. })
                                    if raw_ident_of(obj)
                                        .is_some_and(|p| plan.proto_to_class.contains_key(&p)) =>
                                {
                                    continue;
                                }
                                Stmt::ModuleStore { value, .. }
                                    if raw_ident_of(value)
                                        .is_some_and(|v| plan.view_classes.contains(&v)) =>
                                {
                                    continue;
                                }
                                Stmt::LexStore { value, .. }
                                    if is_class_alias_store(value, env)
                                        || raw_ident_of(value)
                                            .is_some_and(|v| plan.view_classes.contains(&v)) =>
                                {
                                    continue;
                                }
                                Stmt::Expr(e)
                                    if is_prototype_touch(e)
                                        || extract_entry_registration(e, env).is_some() =>
                                {
                                    continue;
                                }
                                Stmt::Return(None) | Stmt::Elided { .. } => continue,
                                _ => {}
                            }
                        }
                        for e in crate::emit::stmt_exprs(s) {
                            collect_expr_raw_idents(e, &mut plan.live_idents);
                        }
                    }
                }
                SNode::Block(body) | SNode::Labeled { body, .. } => nstack.push((body, false)),
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        collect_expr_raw_idents(c, &mut plan.live_idents);
                    }
                    nstack.push((body, false));
                }
                SNode::DoWhile { body, cond, .. } => {
                    collect_expr_raw_idents(cond, &mut plan.live_idents);
                    nstack.push((body, false));
                }
                SNode::ForOf { iter, body, .. } => {
                    collect_expr_raw_idents(iter, &mut plan.live_idents);
                    nstack.push((body, false));
                }
                SNode::ForIn { obj, body, .. } => {
                    collect_expr_raw_idents(obj, &mut plan.live_idents);
                    nstack.push((body, false));
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        nstack.push((fin, false));
                    }
                    for c in catches.iter().rev() {
                        nstack.push((&c.body, false));
                    }
                    nstack.push((body, false));
                }
                SNode::Switch { disc, cases } => {
                    collect_expr_raw_idents(disc, &mut plan.live_idents);
                    for c in cases.iter().rev() {
                        for t in &c.tests {
                            collect_expr_raw_idents(t, &mut plan.live_idents);
                        }
                        nstack.push((&c.body, false));
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }

    // Transitively mark pure-setup candidates referenced by live candidates.
    let mut work: Vec<String> = plan.live_idents.iter().cloned().collect();
    while let Some(live) = work.pop() {
        if let Some(deps) = candidate_deps.get(&live) {
            for dep in deps {
                if plan.live_idents.insert(dep.clone()) {
                    work.push(dep.clone());
                }
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
                        if !plan.live_idents.contains(name)
                            && (plan.proto_to_class.contains_key(name)
                                || plan.dead_temps.contains(name)
                                || is_pure_arkui_main_setup(value, env)) => {}
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
        SNode::Honest(note) => {
            out.push_str(&format!("/* {note} */\n"));
        }
        _ => em.emit_node(n, 0, out),
    }
}

/// Iteratively precompute nested `@Component struct` renderings for all
/// `ViewPU` / `View` classes reachable from `root_func` in post-order so
/// [`Emitter::step_start_class`] can splice them without calling back into
/// `crate::arkui` (zero mutual call-graph cycles).
pub(crate) fn precompute_arkui_components(em: &mut Emitter<'_>, root_func: FuncId) {
    struct ClassCand {
        name: String,
        ctor: FuncId,
        members: ConstId,
        member_attrs: Vec<MemberAttrs>,
    }

    let mut visited_funcs: BTreeSet<FuncId> = BTreeSet::new();
    let mut fstack: Vec<(FuncId, bool)> = vec![(root_func, true)];
    let mut candidates: Vec<ClassCand> = Vec::new();
    let empty_env = BTreeMap::new();

    while let Some((fid, is_top)) = fstack.pop() {
        if !visited_funcs.insert(fid) || em.module.func(fid).is_none() {
            continue;
        }
        let body = em.peek_prepared(fid, is_top).body.clone();
        let mut nstack: Vec<&[SNode]> = vec![body.as_slice()];
        while let Some(slice) = nstack.pop() {
            for n in slice {
                match n {
                    SNode::Stmts(leaves) => {
                        for l in leaves {
                            if let Leaf::Raw(Stmt::Declare {
                                name,
                                value:
                                    Expr::Class {
                                        ctor,
                                        heritage,
                                        members,
                                        member_attrs,
                                        sendable: false,
                                        ..
                                    },
                                ..
                            }) = l
                                && (is_view_heritage(heritage.as_deref(), &empty_env)
                                    || heritage_mentions_view(heritage.as_deref()))
                            {
                                candidates.push(ClassCand {
                                    name: name.clone(),
                                    ctor: *ctor,
                                    members: *members,
                                    member_attrs: member_attrs.clone(),
                                });
                            }
                            for e in crate::folds::leaf_exprs(l) {
                                collect_inline_funcs_from_expr(em.module, e, &mut fstack);
                            }
                        }
                    }
                    SNode::Block(b) | SNode::Labeled { body: b, .. } => nstack.push(b),
                    SNode::If {
                        cond,
                        then,
                        otherwise,
                    } => {
                        collect_inline_funcs_from_expr(em.module, cond, &mut fstack);
                        nstack.push(otherwise);
                        nstack.push(then);
                    }
                    SNode::While { cond, body: b, .. } => {
                        if let Some(c) = cond {
                            collect_inline_funcs_from_expr(em.module, c, &mut fstack);
                        }
                        nstack.push(b);
                    }
                    SNode::DoWhile { body: b, cond, .. } => {
                        collect_inline_funcs_from_expr(em.module, cond, &mut fstack);
                        nstack.push(b);
                    }
                    SNode::ForOf { iter, body: b, .. } => {
                        collect_inline_funcs_from_expr(em.module, iter, &mut fstack);
                        nstack.push(b);
                    }
                    SNode::ForIn { obj, body: b, .. } => {
                        collect_inline_funcs_from_expr(em.module, obj, &mut fstack);
                        nstack.push(b);
                    }
                    SNode::Try {
                        body: b,
                        catches,
                        finally,
                        ..
                    } => {
                        if let Some(fin) = finally {
                            nstack.push(fin);
                        }
                        for c in catches.iter().rev() {
                            nstack.push(&c.body);
                        }
                        nstack.push(b);
                    }
                    SNode::Switch { disc, cases } => {
                        collect_inline_funcs_from_expr(em.module, disc, &mut fstack);
                        for c in cases.iter().rev() {
                            for t in &c.tests {
                                collect_inline_funcs_from_expr(em.module, t, &mut fstack);
                            }
                            nstack.push(&c.body);
                        }
                    }
                    SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
                }
            }
        }
    }

    // Render inner components before outer components so nested `@Component`
    // classes inside methods find their precomputed output in `em.arkui_components`.
    for cand in candidates.into_iter().rev() {
        let key = (cand.ctor, cand.name.clone());
        if em.arkui_components.contains_key(&key) {
            continue;
        }
        let saved_stats = std::mem::take(&mut em.stats);
        let saved_fn_fb = em.current_fn_has_fallback;
        let saved_kind = em.current_kind;
        let saved_depth = em.class_depth;
        let saved_hoisted = std::mem::take(&mut em.hoisted);

        let mut rendered = String::new();
        let ok = emit_arkui_struct(
            em,
            "",
            0,
            &cand.name,
            cand.ctor,
            cand.members,
            &cand.member_attrs,
            &[],
            false,
            &mut rendered,
        );

        let delta_stats = std::mem::replace(&mut em.stats, saved_stats);
        let had_fb = em.current_fn_has_fallback;
        em.current_fn_has_fallback = saved_fn_fb;
        em.current_kind = saved_kind;
        em.class_depth = saved_depth;
        em.hoisted = saved_hoisted;

        if ok {
            em.arkui_components
                .insert(key, (rendered, delta_stats, had_fb));
        }
    }
}

fn collect_inline_funcs_from_expr(
    module: &abcd_ir::Module,
    root: &Expr,
    out: &mut Vec<(FuncId, bool)>,
) {
    let mut estack = vec![root];
    let mut mrefs = BTreeSet::new();
    while let Some(cur) = estack.pop() {
        match cur {
            Expr::Closure { body, .. } => out.push((*body, false)),
            Expr::Class { ctor, members, .. } => {
                out.push((*ctor, false));
                mrefs.clear();
                crate::emit::collect_method_refs(module, *members, &mut mrefs);
                for &m in &mrefs {
                    out.push((m, false));
                }
            }
            _ => {}
        }
        estack.extend(crate::folds::expr_children(cur));
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "struct emitter threads indentation, ctor, member buffers, overflow methods, and entry flag"
)]
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
    let Some(items) = lit_of(em.module, members).and_then(Lit::into_array) else {
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

    let (ctor_rf, ctor_body) = em.func_nodes(ctor, false);
    let mut base_this_aliases = BTreeSet::from(["this".to_string()]);
    for p in &ctor_rf.params {
        if p == "this" {
            base_this_aliases.insert(p.clone());
        }
    }
    collect_this_aliases(&ctor_body, &mut base_this_aliases);
    let fields = extract_arkui_fields(em, &ctor_body, &base_this_aliases);
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
                    format!("@Provide({})", crate::consts::render_string(alias))
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
                    out.push_str(&format!(
                        "{pad}  @Consume({}) {name}: any;\n",
                        crate::consts::render_string(alias)
                    ));
                }
            }
            ArkField::LocalStorageLink { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @LocalStorageLink({}) {name}: any = {init};\n",
                    crate::consts::render_string(key)
                ));
            }
            ArkField::LocalStorageProp { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @LocalStorageProp({}) {name}: any = {init};\n",
                    crate::consts::render_string(key)
                ));
            }
            ArkField::StorageLink { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @StorageLink({}) {name}: any = {init};\n",
                    crate::consts::render_string(key)
                ));
            }
            ArkField::StorageProp { key, name, init } => {
                decorated_names.insert(name.clone());
                out.push_str(&format!(
                    "{pad}  @StorageProp({}) {name}: any = {init};\n",
                    crate::consts::render_string(key)
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
            let mut method_this = base_this_aliases.clone();
            collect_this_aliases(&mbody, &mut method_this);
            let ui_ctx = ArkUiExprCtx {
                this_aliases: method_this,
                decorated_names: decorated_names.clone(),
                link_names: link_names.clone(),
            };
            let ui_nodes = reconstruct_ui_body(em, &mbody, &ui_ctx);
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
            let mut method_this = base_this_aliases.clone();
            collect_this_aliases(&mbody, &mut method_this);
            let ui_ctx = ArkUiExprCtx {
                this_aliases: method_this,
                decorated_names: decorated_names.clone(),
                link_names: link_names.clone(),
            };
            let ui_nodes = reconstruct_ui_body(em, &mbody, &ui_ctx);
            out.push_str(&format!(
                "{pad}  @Builder\n{pad}  {clean_m}({}) {{\n",
                visible.join(", ")
            ));
            for d in lex_decls(&mbody, &rf.params) {
                if !ui_ctx.this_aliases.contains(&d) {
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
            SNode::Block(body) | SNode::Labeled { body, .. } => {
                stack.push(body.iter());
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

/// Match ONLY `ets_loader`'s synthetic constructor guard
/// `if (!("finalizeConstruction" in ViewPU.prototype)) { Reflect.set(...); }`
/// (or its positive-condition empty-`then` mirror), never arbitrary user `if` blocks.
fn is_finalize_construction_polyfill(
    cond: &Expr,
    then: &[SNode],
    otherwise: &[SNode],
    env: &BTreeMap<String, Expr>,
) -> bool {
    let mut cur = resolve_expr(cond, env);
    let mut negated = false;
    for _ in 0..8 {
        match cur {
            Expr::Unary {
                op:
                    abcd_ir::op::UnOp::LogicalNot
                    | abcd_ir::op::UnOp::IsFalse
                    | abcd_ir::op::UnOp::JumpEqz,
                operand,
            } => {
                negated = !negated;
                cur = resolve_expr(operand, env);
            }
            Expr::Unary {
                op: abcd_ir::op::UnOp::IsTrue | abcd_ir::op::UnOp::JumpNez,
                operand,
            } => {
                cur = resolve_expr(operand, env);
            }
            _ => break,
        }
    }
    let Expr::Compare {
        op: abcd_ir::op::CmpOp::In,
        left,
        right,
    } = cur
    else {
        return false;
    };
    let is_view_proto = |e: &Expr| -> bool {
        matches!(
            resolve_expr(e, env),
            Expr::PropName { object, name, .. }
                if name == "prototype"
                    && matches!(ident_of(object, env).as_deref(), Some("ViewPU" | "View"))
        )
    };
    let is_fc_str =
        |e: &Expr| -> bool { string_lit(Some(e), env).as_deref() == Some("finalizeConstruction") };
    let matches_in_guard =
        (is_fc_str(left) && is_view_proto(right)) || (is_view_proto(left) && is_fc_str(right));
    if !matches_in_guard {
        return false;
    }
    if negated {
        otherwise.is_empty() && !then.is_empty()
    } else {
        then.is_empty() && !otherwise.is_empty()
    }
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

#[derive(Clone)]
struct ArkUiExprCtx {
    this_aliases: BTreeSet<String>,
    decorated_names: BTreeSet<String>,
    link_names: BTreeSet<String>,
}

fn collect_this_aliases(nodes: &[SNode], aliases: &mut BTreeSet<String>) {
    let mut grew = true;
    while grew {
        grew = false;
        walk_ctor_stmts(nodes, &mut |stmt| {
            if let Stmt::Declare { name, value, .. } | Stmt::LexStore { name, value, .. } = stmt
                && let Expr::Ident(src) | Expr::Temp { name: src, .. } = value
                && aliases.contains(src)
            {
                if aliases.insert(name.clone()) {
                    grew = true;
                }
                let san = sanitize(name);
                if aliases.insert(san) {
                    grew = true;
                }
            }
        });
    }
}

fn extract_arkui_fields(
    em: &mut Emitter<'_>,
    ctor_body: &[SNode],
    this_aliases: &BTreeSet<String>,
) -> Vec<ArkField> {
    let env = collect_const_bindings(ctor_body);
    let empty_dec = BTreeSet::new();
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
                        .map(|a| {
                            render_clean_expr(
                                em,
                                resolve_expr(a, &env),
                                &env,
                                this_aliases,
                                &empty_dec,
                            )
                        })
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
                            .map(|a| {
                                render_clean_expr(
                                    em,
                                    resolve_expr(a, &env),
                                    &env,
                                    this_aliases,
                                    &empty_dec,
                                )
                            })
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
                            .map(|a| {
                                render_clean_expr(
                                    em,
                                    resolve_expr(a, &env),
                                    &env,
                                    this_aliases,
                                    &empty_dec,
                                )
                            })
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
                            .map(|a| {
                                render_clean_expr(
                                    em,
                                    resolve_expr(a, &env),
                                    &env,
                                    this_aliases,
                                    &empty_dec,
                                )
                            })
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
                            .map(|a| {
                                render_clean_expr(
                                    em,
                                    resolve_expr(a, &env),
                                    &env,
                                    this_aliases,
                                    &empty_dec,
                                )
                            })
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
            let init = render_clean_expr(em, val, &env, this_aliases, &empty_dec);
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
            SNode::Block(body) | SNode::Labeled { body, .. } => {
                stack.push(body.iter());
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

enum UiFinishKind {
    Root,
    IfThen {
        cond: String,
        otherwise: Vec<SNode>,
    },
    IfElse {
        cond: String,
        then_body: Vec<UiNode>,
    },
    ForEach {
        func_id: FuncId,
        is_lazy: bool,
        arr: String,
        item_param: String,
        idx_param: Option<String>,
        key_gen: Option<String>,
    },
    BranchClosure {
        func_id: FuncId,
    },
    ObserveSubbody {
        func_id: FuncId,
    },
}

struct UiBuildFrame {
    nodes: std::vec::IntoIter<SNode>,
    pending_leaves: std::vec::IntoIter<Leaf>,
    env: BTreeMap<String, Expr>,
    ctx: ArkUiExprCtx,
    stack: Vec<OpenComp>,
    root: Vec<UiNode>,
    finish: UiFinishKind,
}

fn close_open_comps(stack: &mut Vec<OpenComp>, root: &mut Vec<UiNode>) {
    while let Some(open) = stack.pop() {
        let finished = UiNode::Component {
            name: open.name,
            args: open.args,
            attrs: open.attrs,
            children: open.children,
        };
        push_ui_node(stack, root, finished);
    }
}

fn reconstruct_ui_body(em: &mut Emitter<'_>, nodes: &[SNode], ctx: &ArkUiExprCtx) -> Vec<UiNode> {
    let env = collect_const_bindings(nodes);
    let mut local_ctx = ctx.clone();
    collect_this_aliases(nodes, &mut local_ctx.this_aliases);

    let root_nodes = nodes.to_vec();
    let mut active_funcs: BTreeSet<FuncId> = BTreeSet::new();
    let mut frames = vec![UiBuildFrame {
        nodes: root_nodes.into_iter(),
        pending_leaves: Vec::new().into_iter(),
        env,
        ctx: local_ctx,
        stack: Vec::new(),
        root: Vec::new(),
        finish: UiFinishKind::Root,
    }];

    while let Some(top) = frames.last_mut() {
        if let Some(leaf) = top.pending_leaves.next() {
            let Leaf::Raw(s) = leaf else { continue };
            match s {
                Stmt::Declare { .. }
                | Stmt::LexStore { .. }
                | Stmt::Return(None)
                | Stmt::Elided { .. } => {}
                Stmt::Expr(e) => {
                    if let Some(next_frame) = step_ui_expr(em, &e, top, &mut active_funcs) {
                        frames.push(next_frame);
                    }
                }
                other => {
                    let mut buf = String::new();
                    em.emit_stmt(&other, 0, &mut buf);
                    let trimmed = buf.trim().to_string();
                    if !trimmed.is_empty() {
                        push_ui_node(&mut top.stack, &mut top.root, UiNode::RawStmt(trimmed));
                    }
                }
            }
            continue;
        }

        if let Some(mut node) = top.nodes.next() {
            match &mut node {
                SNode::Stmts(leaves) => {
                    top.pending_leaves = std::mem::take(leaves).into_iter();
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    if then.is_empty() && otherwise.is_empty() {
                        continue;
                    }
                    let cond_s = render_clean_expr(
                        em,
                        cond,
                        &top.env,
                        &top.ctx.this_aliases,
                        &top.ctx.decorated_names,
                    );
                    let child_env = top.env.clone();
                    let child_ctx = top.ctx.clone();
                    let then_vec = std::mem::take(then);
                    let else_vec = std::mem::take(otherwise);
                    frames.push(UiBuildFrame {
                        nodes: then_vec.into_iter(),
                        pending_leaves: Vec::new().into_iter(),
                        env: child_env,
                        ctx: child_ctx,
                        stack: Vec::new(),
                        root: Vec::new(),
                        finish: UiFinishKind::IfThen {
                            cond: cond_s,
                            otherwise: else_vec,
                        },
                    });
                }
                other => {
                    let mut buf = String::new();
                    em.emit_node(other, 0, &mut buf);
                    let trimmed = buf.trim().to_string();
                    if !trimmed.is_empty() {
                        push_ui_node(&mut top.stack, &mut top.root, UiNode::RawStmt(trimmed));
                    }
                }
            }
            continue;
        }

        let Some(mut done) = frames.pop() else {
            break;
        };
        match done.finish {
            UiFinishKind::Root => {
                close_open_comps(&mut done.stack, &mut done.root);
                return done.root;
            }
            UiFinishKind::IfThen { cond, otherwise } => {
                close_open_comps(&mut done.stack, &mut done.root);
                frames.push(UiBuildFrame {
                    nodes: otherwise.into_iter(),
                    pending_leaves: Vec::new().into_iter(),
                    env: done.env,
                    ctx: done.ctx,
                    stack: Vec::new(),
                    root: Vec::new(),
                    finish: UiFinishKind::IfElse {
                        cond,
                        then_body: done.root,
                    },
                });
            }
            UiFinishKind::IfElse { cond, then_body } => {
                close_open_comps(&mut done.stack, &mut done.root);
                if let Some(parent) = frames.last_mut() {
                    push_ui_node(
                        &mut parent.stack,
                        &mut parent.root,
                        UiNode::If {
                            cond,
                            then_body,
                            else_body: done.root,
                        },
                    );
                }
            }
            UiFinishKind::ForEach {
                func_id,
                is_lazy,
                arr,
                item_param,
                idx_param,
                key_gen,
            } => {
                active_funcs.remove(&func_id);
                close_open_comps(&mut done.stack, &mut done.root);
                if let Some(parent) = frames.last_mut() {
                    push_ui_node(
                        &mut parent.stack,
                        &mut parent.root,
                        UiNode::ForEach {
                            is_lazy,
                            arr,
                            item_param,
                            idx_param,
                            body: done.root,
                            key_gen,
                        },
                    );
                }
            }
            UiFinishKind::BranchClosure { func_id } => {
                active_funcs.remove(&func_id);
                close_open_comps(&mut done.stack, &mut done.root);
                if let Some(parent) = frames.last_mut() {
                    for c in done.root {
                        push_ui_node(&mut parent.stack, &mut parent.root, c);
                    }
                }
            }
            UiFinishKind::ObserveSubbody { func_id } => {
                active_funcs.remove(&func_id);
                if let Some(parent) = frames.last_mut() {
                    parent.stack = done.stack;
                    parent.root = done.root;
                }
            }
        }
    }
    Vec::new()
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

#[allow(
    clippy::too_many_arguments,
    reason = "ForEach frame builder threads emitter, generator closure, bindings, context, and cycle set"
)]
fn prepare_foreach_frame(
    em: &mut Emitter<'_>,
    gen_expr: &Expr,
    env: &BTreeMap<String, Expr>,
    ctx: &ArkUiExprCtx,
    is_lazy: bool,
    arr_s: String,
    key_s: Option<String>,
    active_funcs: &mut BTreeSet<FuncId>,
) -> Option<UiBuildFrame> {
    let Expr::Closure { body: fn_id, .. } = resolve_expr(gen_expr, env) else {
        return None;
    };
    let fn_id = *fn_id;
    if !active_funcs.insert(fn_id) {
        return None;
    }
    let (rf, body) = em.func_nodes(fn_id, false);
    let visible = &rf.params[rf.hidden_params.min(rf.params.len())..];
    let item_p = visible
        .first()
        .cloned()
        .unwrap_or_else(|| "item".to_string());
    let idx_p = visible.get(1).cloned();
    let sub_env = collect_const_bindings(&body);
    let mut sub_ctx = ctx.clone();
    collect_this_aliases(&body, &mut sub_ctx.this_aliases);
    Some(UiBuildFrame {
        nodes: body.into_iter(),
        pending_leaves: Vec::new().into_iter(),
        env: sub_env,
        ctx: sub_ctx,
        stack: Vec::new(),
        root: Vec::new(),
        finish: UiFinishKind::ForEach {
            func_id: fn_id,
            is_lazy,
            arr: arr_s,
            item_param: item_p,
            idx_param: idx_p,
            key_gen: key_s,
        },
    })
}

fn step_ui_expr(
    em: &mut Emitter<'_>,
    e: &Expr,
    frame: &mut UiBuildFrame,
    active_funcs: &mut BTreeSet<FuncId>,
) -> Option<UiBuildFrame> {
    let Expr::Call { callee, args, .. } = e else {
        return None;
    };
    let env = &frame.env;
    let ctx = &frame.ctx;

    if is_method_named(callee, "observeComponentCreation2", env)
        || is_method_named(callee, "observeComponentCreation", env)
    {
        flush_self_closing_top(&mut frame.stack, &mut frame.root);
        if let Some(first) = args.first()
            && let Expr::Closure { body: fn_id, .. } = resolve_expr(first, env)
        {
            let fn_id = *fn_id;
            let second_meta = args.get(1).map(|a| resolve_expr(a, env).clone());
            return step_observe_closure(em, fn_id, second_meta.as_ref(), frame, active_funcs);
        }
    }

    if is_method_named(callee, "pop", env) {
        let comp_name = receiver_component_name(callee, e, env);
        if matches!(comp_name.as_deref(), Some("If" | "ForEach" | "LazyForEach")) {
            return None;
        }
        flush_self_closing_top(&mut frame.stack, &mut frame.root);
        if let Some(target) = &comp_name
            && let Some(pos) = frame.stack.iter().rposition(|c| &c.name == target)
        {
            while frame.stack.len() > pos + 1 {
                if let Some(inner) = frame.stack.pop() {
                    push_ui_node(
                        &mut frame.stack,
                        &mut frame.root,
                        UiNode::Component {
                            name: inner.name,
                            args: inner.args,
                            attrs: inner.attrs,
                            children: inner.children,
                        },
                    );
                }
            }
            if let Some(open) = frame.stack.pop() {
                push_ui_node(
                    &mut frame.stack,
                    &mut frame.root,
                    UiNode::Component {
                        name: open.name,
                        args: open.args,
                        attrs: open.attrs,
                        children: open.children,
                    },
                );
            }
            return None;
        }
    }

    if is_method_named(callee, "create", env)
        && let Some(comp) = receiver_component_name(callee, e, env)
        && (comp == "LazyForEach" || comp == "ForEach")
        && args.len() >= 4
    {
        flush_self_closing_top(&mut frame.stack, &mut frame.root);
        let arr_s = render_clean_expr(
            em,
            resolve_expr(&args[2], env),
            env,
            &ctx.this_aliases,
            &ctx.decorated_names,
        );
        let key_s = args.get(4).map(|k| {
            render_clean_expr(
                em,
                resolve_expr(k, env),
                env,
                &ctx.this_aliases,
                &ctx.decorated_names,
            )
        });
        if let Some(next_frame) = prepare_foreach_frame(
            em,
            &args[3],
            env,
            ctx,
            comp == "LazyForEach",
            arr_s,
            key_s,
            active_funcs,
        ) {
            return Some(next_frame);
        }
    }

    if is_method_named(callee, "forEachUpdateFunction", env) && args.len() >= 3 {
        let arr_s = render_clean_expr(
            em,
            resolve_expr(&args[1], env),
            env,
            &ctx.this_aliases,
            &ctx.decorated_names,
        );
        let item_arg = unwrap_foreach_item_gen(&args[2], env).unwrap_or(&args[2]);
        let key_s = args.get(3).map(|k| {
            render_clean_expr(
                em,
                resolve_expr(k, env),
                env,
                &ctx.this_aliases,
                &ctx.decorated_names,
            )
        });
        if let Some(next_frame) =
            prepare_foreach_frame(em, item_arg, env, ctx, false, arr_s, key_s, active_funcs)
        {
            return Some(next_frame);
        }
    }

    if is_method_named(callee, "ifElseBranchUpdateFunction", env)
        && args.len() >= 2
        && let Expr::Closure { body: br_fn, .. } = resolve_expr(&args[1], env)
    {
        let br_fn = *br_fn;
        if active_funcs.insert(br_fn) {
            let (_rf, br_body) = em.func_nodes(br_fn, false);
            let sub_env = collect_const_bindings(&br_body);
            let mut sub_ctx = ctx.clone();
            collect_this_aliases(&br_body, &mut sub_ctx.this_aliases);
            return Some(UiBuildFrame {
                nodes: br_body.into_iter(),
                pending_leaves: Vec::new().into_iter(),
                env: sub_env,
                ctx: sub_ctx,
                stack: Vec::new(),
                root: Vec::new(),
                finish: UiFinishKind::BranchClosure { func_id: br_fn },
            });
        }
        return None;
    }

    let rendered = render_clean_expr(em, e, env, &ctx.this_aliases, &ctx.decorated_names);
    if !rendered.is_empty() {
        push_ui_node(
            &mut frame.stack,
            &mut frame.root,
            UiNode::RawStmt(format!("{rendered};")),
        );
    }
    None
}

fn step_observe_closure(
    em: &mut Emitter<'_>,
    closure_fn: FuncId,
    second_meta: Option<&Expr>,
    parent: &mut UiBuildFrame,
    active_funcs: &mut BTreeSet<FuncId>,
) -> Option<UiBuildFrame> {
    if !active_funcs.insert(closure_fn) {
        return None;
    }
    let (_rf, body) = em.func_nodes(closure_fn, false);
    let env = collect_const_bindings(&body);
    let mut ctx = parent.ctx.clone();
    collect_this_aliases(&body, &mut ctx.this_aliases);

    if let Some(meta_name) = custom_child_meta_name(second_meta, &env) {
        let props = extract_custom_child_props(em, &body, &env, &ctx);
        push_ui_node(
            &mut parent.stack,
            &mut parent.root,
            UiNode::CustomChild {
                name: meta_name,
                props,
            },
        );
        active_funcs.remove(&closure_fn);
        return None;
    }
    if let Some((child_name, props)) = extract_viewpu_child_from_body(em, &body, &env, &ctx) {
        push_ui_node(
            &mut parent.stack,
            &mut parent.root,
            UiNode::CustomChild {
                name: child_name,
                props,
            },
        );
        active_funcs.remove(&closure_fn);
        return None;
    }

    let meta_ident = second_meta.and_then(|m| ident_of(m, &env));
    if meta_ident.as_deref() == Some("If") || body_calls_comp_create(&body, &env, "If") {
        let if_nodes: Vec<SNode> = body
            .into_iter()
            .filter(|n| matches!(n, SNode::If { .. }))
            .collect();
        return Some(UiBuildFrame {
            nodes: if_nodes.into_iter(),
            pending_leaves: Vec::new().into_iter(),
            env,
            ctx,
            stack: std::mem::take(&mut parent.stack),
            root: std::mem::take(&mut parent.root),
            finish: UiFinishKind::ObserveSubbody {
                func_id: closure_fn,
            },
        });
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
                    create_args = render_call_args_clean(em, args, &env, &ctx, true);
                }
                "pop" => {
                    saw_pop = true;
                }
                attr => {
                    let attr_args = render_call_args_clean(em, args, &env, &ctx, false);
                    attrs.push((attr.to_string(), attr_args));
                }
            }
        }
    });

    if let Some(name) = comp_name {
        if name == "ForEach" {
            return Some(UiBuildFrame {
                nodes: body.into_iter(),
                pending_leaves: Vec::new().into_iter(),
                env,
                ctx,
                stack: std::mem::take(&mut parent.stack),
                root: std::mem::take(&mut parent.root),
                finish: UiFinishKind::ObserveSubbody {
                    func_id: closure_fn,
                },
            });
        }
        let open = OpenComp {
            name,
            args: create_args,
            attrs,
            children: Vec::new(),
        };
        if saw_pop {
            push_ui_node(
                &mut parent.stack,
                &mut parent.root,
                UiNode::Component {
                    name: open.name,
                    args: open.args,
                    attrs: open.attrs,
                    children: Vec::new(),
                },
            );
        } else {
            parent.stack.push(open);
        }
    }
    active_funcs.remove(&closure_fn);
    None
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
    ctx: &ArkUiExprCtx,
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
            new_props = render_props_object(em, arg1, &obj_stores, env, ctx).filter(|p| p != "{}");
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
                new_props =
                    render_props_object(em, arg1, &obj_stores, env, ctx).filter(|p| p != "{}");
            }
            if update_props.is_none()
                && is_method_named(callee, "updateStateVarsOfChildByElmtId", env)
                && let Some(arg1) = args.get(1)
            {
                update_props =
                    render_props_object(em, arg1, &obj_stores, env, ctx).filter(|p| p != "{}");
            }
        }
    });
    new_props.or(update_props)
}

fn extract_viewpu_child_from_body(
    em: &mut Emitter<'_>,
    body: &[SNode],
    env: &BTreeMap<String, Expr>,
    ctx: &ArkUiExprCtx,
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
                    .and_then(|a| render_props_object(em, a, &obj_stores, env, ctx))
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
                .and_then(|a| render_props_object(em, a, &obj_stores, env, ctx))
                .filter(|p| p != "{}");
            found = Some((clean_component_name(&cname), props));
        }
    });
    if saw_view_create { found } else { None }
}

enum PropValSrc<'a> {
    Lit(&'a Lit),
    Expr(&'a Expr),
}

struct PropFrame<'a> {
    pending: std::vec::IntoIter<(String, PropValSrc<'a>)>,
    ordered_keys: Vec<String>,
    values: BTreeMap<String, String>,
    pop_ident: Option<String>,
    parent_key: Option<String>,
}

fn try_make_prop_frame<'a>(
    raw_e: &'a Expr,
    obj_stores: &'a BTreeMap<String, Vec<(String, Expr)>>,
    env: &'a BTreeMap<String, Expr>,
    active_objs: &mut BTreeSet<String>,
    parent_key: Option<String>,
) -> Option<PropFrame<'a>> {
    let raw_id = raw_ident_of(raw_e);
    if let Some(id) = &raw_id
        && active_objs.contains(id)
    {
        return None;
    }
    let e = resolve_expr(raw_e, env);
    let extra = raw_id.as_ref().and_then(|id| obj_stores.get(id));
    match e {
        Expr::ObjectBuild { entries } => {
            let pop_ident = raw_id.filter(|id| obj_stores.contains_key(id));
            if let Some(id) = &pop_ident {
                active_objs.insert(id.clone());
            }
            let mut items: Vec<(String, PropValSrc<'a>)> = Vec::new();
            for entry in entries {
                if let ObjEntry::KeyValue(Lit::String(k), value) = entry {
                    items.push((k.clone(), PropValSrc::Expr(resolve_expr(value, env))));
                }
            }
            if let Some(stores) = extra {
                for (k, value) in stores {
                    items.push((k.clone(), PropValSrc::Expr(value)));
                }
            }
            Some(PropFrame {
                pending: items.into_iter(),
                ordered_keys: Vec::new(),
                values: BTreeMap::new(),
                pop_ident,
                parent_key,
            })
        }
        Expr::ObjectLit { entries } => {
            let pop_ident = raw_id.filter(|id| obj_stores.contains_key(id));
            if let Some(id) = &pop_ident {
                active_objs.insert(id.clone());
            }
            let mut items: Vec<(String, PropValSrc<'a>)> = Vec::new();
            for (k, v) in entries {
                if let Lit::String(ks) = k {
                    items.push((ks.clone(), PropValSrc::Lit(v)));
                }
            }
            if let Some(stores) = extra {
                for (k, value) in stores {
                    items.push((k.clone(), PropValSrc::Expr(value)));
                }
            }
            Some(PropFrame {
                pending: items.into_iter(),
                ordered_keys: Vec::new(),
                values: BTreeMap::new(),
                pop_ident,
                parent_key,
            })
        }
        _ => None,
    }
}

fn render_leaf_prop_val(
    em: &mut Emitter<'_>,
    rv: &Expr,
    env: &BTreeMap<String, Expr>,
    ctx: &ArkUiExprCtx,
) -> String {
    if let Expr::PropName { object, name, .. } = rv
        && is_this_alias_expr(object, env, &ctx.this_aliases)
    {
        if let Some(prop) = name.strip_prefix("__")
            && !prop.is_empty()
        {
            return format!("${prop}");
        }
        if ctx.link_names.contains(name) {
            return format!("${name}");
        }
    }
    render_clean_expr(em, rv, env, &ctx.this_aliases, &ctx.decorated_names)
}

fn render_props_object(
    em: &mut Emitter<'_>,
    raw_e: &Expr,
    obj_stores: &BTreeMap<String, Vec<(String, Expr)>>,
    env: &BTreeMap<String, Expr>,
    ctx: &ArkUiExprCtx,
) -> Option<String> {
    let mut active_objs = BTreeSet::new();
    let Some(root_frame) = try_make_prop_frame(raw_e, obj_stores, env, &mut active_objs, None)
    else {
        let e = resolve_expr(raw_e, env);
        return Some(render_clean_expr(
            em,
            e,
            env,
            &ctx.this_aliases,
            &ctx.decorated_names,
        ));
    };

    let mut frames = vec![root_frame];
    let mut completed: Option<(String, String)> = None;

    while let Some(top) = frames.last_mut() {
        if let Some((k, v_str)) = completed.take() {
            if !top.values.contains_key(&k) {
                top.ordered_keys.push(k.clone());
            }
            top.values.insert(k, v_str);
        }
        if let Some((k, src)) = top.pending.next() {
            match src {
                PropValSrc::Lit(lit) => {
                    let vs = em.render_lit_js(lit);
                    if !top.values.contains_key(&k) {
                        top.ordered_keys.push(k.clone());
                    }
                    top.values.insert(k, vs);
                }
                PropValSrc::Expr(raw_rv) => {
                    let rv = resolve_expr(raw_rv, env);
                    if matches!(rv, Expr::ObjectBuild { .. } | Expr::ObjectLit { .. })
                        && let Some(child_frame) = try_make_prop_frame(
                            raw_rv,
                            obj_stores,
                            env,
                            &mut active_objs,
                            Some(k.clone()),
                        )
                    {
                        frames.push(child_frame);
                    } else {
                        let vs = render_leaf_prop_val(em, rv, env, ctx);
                        if !top.values.contains_key(&k) {
                            top.ordered_keys.push(k.clone());
                        }
                        top.values.insert(k, vs);
                    }
                }
            }
            continue;
        }

        let Some(done) = frames.pop() else {
            break;
        };
        if let Some(id) = done.pop_ident {
            active_objs.remove(&id);
        }
        let formatted = format_kv_map(done.ordered_keys, done.values);
        match done.parent_key {
            None => return Some(formatted),
            Some(pk) => completed = Some((pk, formatted)),
        }
    }
    None
}

fn is_this_alias_expr(
    e: &Expr,
    env: &BTreeMap<String, Expr>,
    this_aliases: &BTreeSet<String>,
) -> bool {
    match e {
        Expr::Ident(s) | Expr::Temp { name: s, .. } if this_aliases.contains(s) => true,
        _ => match resolve_expr(e, env) {
            Expr::Ident(s) | Expr::Temp { name: s, .. } => this_aliases.contains(s),
            _ => false,
        },
    }
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
                Some(format!("{}: {v}", crate::consts::render_string(&k)))
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

fn render_call_args_clean(
    em: &mut Emitter<'_>,
    args: &[Expr],
    env: &BTreeMap<String, Expr>,
    ctx: &ArkUiExprCtx,
    strip_nav_meta: bool,
) -> String {
    let mut rendered = Vec::new();
    for (idx, a) in args.iter().enumerate() {
        let ra = resolve_expr(a, env);
        if strip_nav_meta && idx == 1 && is_navigation_meta_obj(ra) {
            continue;
        }
        if matches!(ra, Expr::ObjectBuild { .. } | Expr::ObjectLit { .. })
            && let Some(obj_s) = render_props_object(em, a, &BTreeMap::new(), env, ctx)
        {
            rendered.push(obj_s);
            continue;
        }
        rendered.push(render_clean_expr(
            em,
            ra,
            env,
            &ctx.this_aliases,
            &ctx.decorated_names,
        ));
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

/// AST-level rewrite of ArkUI `this` capture aliases and observed `__prop`
/// backing accesses BEFORE printing (`#87.6`): string literals and `new.target`
/// are never modified.
fn rewrite_arkui_expr(
    root: &Expr,
    env: &BTreeMap<String, Expr>,
    this_aliases: &BTreeSet<String>,
    decorated_names: &BTreeSet<String>,
) -> Expr {
    let mut cloned = root.clone();
    // Iterative heap workstack over mutable `Expr` nodes (`(ptr, expanded)` is
    // avoided via `#![forbid(unsafe_code)]`; instead we rewrite top-down on
    // `Ident`/`Temp`/`PropName` using a safe mutable borrow stack!).
    let mut stack: Vec<&mut Expr> = vec![&mut cloned];
    while let Some(cur) = stack.pop() {
        if is_this_alias_expr(cur, env, this_aliases) {
            *cur = Expr::Ident("this".to_string());
            continue;
        }
        if let Expr::PropName {
            object,
            name,
            dot_legal,
        } = cur
            && is_this_alias_expr(object, env, this_aliases)
        {
            **object = Expr::Ident("this".to_string());
            if let Some(stripped) = name.strip_prefix("__")
                && !stripped.is_empty()
                && (decorated_names.is_empty() || decorated_names.contains(stripped))
            {
                let clean = stripped.to_string();
                *dot_legal = is_legal_ident(&clean);
                *name = clean;
            }
            continue;
        }
        stack.extend(crate::folds::expr_children_mut(cur));
    }
    cloned
}

fn render_clean_expr(
    em: &mut Emitter<'_>,
    e: &Expr,
    env: &BTreeMap<String, Expr>,
    this_aliases: &BTreeSet<String>,
    decorated_names: &BTreeSet<String>,
) -> String {
    let rewritten = rewrite_arkui_expr(e, env, this_aliases, decorated_names);
    em.estr(&rewritten)
}

fn render_ui_nodes(nodes: &[UiNode], indent: usize, out: &mut String) {
    enum RenderTask<'a> {
        Nodes { slice: &'a [UiNode], indent: usize },
        Raw(String),
    }

    let mut stack = vec![RenderTask::Nodes {
        slice: nodes,
        indent,
    }];
    while let Some(task) = stack.pop() {
        match task {
            RenderTask::Raw(s) => out.push_str(&s),
            RenderTask::Nodes { slice, indent } => {
                let Some((node, rest)) = slice.split_first() else {
                    continue;
                };
                if !rest.is_empty() {
                    stack.push(RenderTask::Nodes {
                        slice: rest,
                        indent,
                    });
                }
                let pad = "  ".repeat(indent);
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
                            let mut close = format!("{pad}}}");
                            for (aname, aargs) in attrs {
                                close.push_str(&format!("\n{pad}  .{aname}({aargs})"));
                            }
                            close.push('\n');
                            stack.push(RenderTask::Raw(close));
                            stack.push(RenderTask::Nodes {
                                slice: children,
                                indent: indent + 1,
                            });
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
                        if else_body.is_empty() {
                            stack.push(RenderTask::Raw(format!("{pad}}}\n")));
                            stack.push(RenderTask::Nodes {
                                slice: then_body,
                                indent: indent + 1,
                            });
                        } else {
                            stack.push(RenderTask::Raw(format!("{pad}}}\n")));
                            stack.push(RenderTask::Nodes {
                                slice: else_body,
                                indent: indent + 1,
                            });
                            stack.push(RenderTask::Raw(format!("{pad}}} else {{\n")));
                            stack.push(RenderTask::Nodes {
                                slice: then_body,
                                indent: indent + 1,
                            });
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
                        let close = match key_gen {
                            Some(k) => format!("{pad}}}, {k})\n"),
                            None => format!("{pad}}})\n"),
                        };
                        stack.push(RenderTask::Raw(close));
                        stack.push(RenderTask::Nodes {
                            slice: body,
                            indent: indent + 1,
                        });
                    }
                    UiNode::RawStmt(text) => {
                        for line in text.lines() {
                            out.push_str(&format!("{pad}{line}\n"));
                        }
                    }
                }
            }
        }
    }
}
