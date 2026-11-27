//! Declarative `build()` / `@Builder` UI tree reconstruction and rendering.

use super::*;

// ── Declarative UI tree (`build()` / `@Builder`) reconstruction ───────────

struct OpenComp {
    name: String,
    args: String,
    attrs: Vec<(String, String)>,
    children: Vec<UiNode>,
}

pub(super) fn body_has_observe_creation(nodes: &[SNode]) -> bool {
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

pub(super) fn reconstruct_ui_body(
    em: &mut Emitter<'_>,
    nodes: &[SNode],
    ctx: &ArkUiExprCtx,
) -> Vec<UiNode> {
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

pub(super) fn render_clean_expr(
    em: &mut Emitter<'_>,
    e: &Expr,
    env: &BTreeMap<String, Expr>,
    this_aliases: &BTreeSet<String>,
    decorated_names: &BTreeSet<String>,
) -> String {
    let rewritten = rewrite_arkui_expr(e, env, this_aliases, decorated_names);
    em.estr(&rewritten)
}

pub(super) fn render_ui_nodes(nodes: &[UiNode], indent: usize, out: &mut String) {
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
