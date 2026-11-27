//! Function, class, method, and TypeScript signature emission.

use super::*;

impl<'m> Emitter<'m> {
    /// Returns the (legalized, minted) emitted name and the raw name.
    pub(crate) fn emit_top_level_function(
        &mut self,
        func: FuncId,
        out: &mut String,
    ) -> (String, String) {
        let (rf, body) = self.func_nodes(func, true);
        self.stats.functions += 1;
        self.current_fn_has_fallback = false;
        self.current_kind = rf.kind;
        let raw = rf.name.clone();
        let name = self.fn_names.mint(&raw);
        let (params, ret) = self.params_ret(&rf);
        let keyword = fn_decl_keyword(rf.kind);
        if rf.kind == FunctionKind::Constructor {
            out.push_str("/* constructor outside a class context (data shape) */\n");
        }
        self.hoisted = escaped_temps(&body);
        out.push_str(&format!("{keyword} {name}({params}){ret} {{\n"));
        for d in lex_decls(&body, &rf.params) {
            out.push_str(&format!("  let {d};\n"));
        }
        for h in self.hoisted.clone() {
            out.push_str(&format!(
                "  var {h}; /* hoisted temp: used outside its def's block */\n"
            ));
        }
        self.emitting_funcs.insert(func);
        self.emit_nodes(&body, 1, out);
        self.emitting_funcs.remove(&func);
        out.push_str("}\n");
        if self.current_fn_has_fallback {
            self.stats.functions_with_fallbacks += 1;
        }
        (name, raw)
    }

    pub(in crate::emit) fn step_enter_inline_func<'b>(
        &mut self,
        func: FuncId,
        indent: usize,
        style: InlineHeaderStyle,
        inline_pool: &'b BTreeMap<FuncId, PreparedFunc>,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        let body_pad = "  ".repeat(indent);
        if !self.emitting_funcs.insert(func) {
            *self
                .stats
                .fallback_comments
                .entry("DefineFunc(cycle)")
                .or_insert(0) += 1;
            self.current_fn_has_fallback = true;
            let rf = crate::recover::recover_func(self.module, func);
            let (params, mut ret) = self.params_ret(&rf);
            if style.drop_ret_ty {
                ret.clear();
            }
            if style.open_paren {
                out.push('(');
            }
            out.push_str(&params);
            out.push(')');
            out.push_str(&ret);
            out.push_str(if style.arrow { " => {\n" } else { " {\n" });
            out.push_str(&format!(
                "{body_pad}/* fallback DefineFunc(cycle): cyclic inline function reference fn#{} */\n",
                func.index()
            ));
            out.push_str(&style.closing);
            return;
        }

        let Some(p) = inline_pool.get(&func) else {
            self.emitting_funcs.remove(&func);
            return;
        };
        self.stats.function_bodies += 1;
        self.stats.structure =
            merge_struct_stats(std::mem::take(&mut self.stats.structure), &p.struct_stats);
        self.stats.folds = merge_fold_stats(std::mem::take(&mut self.stats.folds), &p.fold_stats);

        let (params, mut ret) = self.params_ret(&p.rf);
        if style.drop_ret_ty {
            ret.clear();
        }
        if style.open_paren {
            out.push('(');
        }
        out.push_str(&params);
        out.push(')');
        out.push_str(&ret);
        out.push_str(if style.arrow { " => {\n" } else { " {\n" });

        let prev_kind = std::mem::replace(&mut self.current_kind, p.rf.kind);
        let prev_hoisted = std::mem::replace(&mut self.hoisted, escaped_temps(&p.body));
        for d in lex_decls(&p.body, &p.rf.params) {
            out.push_str(&format!("{body_pad}let {d};\n"));
        }
        for h in &self.hoisted {
            out.push_str(&format!(
                "{body_pad}var {h}; /* hoisted temp: used outside its def's block */\n"
            ));
        }
        tasks.push(PrintTask::ExitInlineFunc {
            func,
            prev_kind,
            prev_hoisted,
            closing: style.closing,
        });
        tasks.push(PrintTask::Nodes {
            slice: &p.body,
            indent,
        });
    }

    // ── Classes & closures ───────────────────────────────────────────

    #[allow(
        clippy::too_many_arguments,
        reason = "class emission threads indent, name, ctor, heritage, members, attrs, and task stack"
    )]
    pub(in crate::emit) fn step_start_class<'b>(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        ctor: FuncId,
        heritage: Option<&'b Expr>,
        members: abcd_ir::ConstId,
        member_attrs: &'b [abcd_ir::op::MemberAttrs],
        sendable: bool,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        if self.opts.arkui
            && !sendable
            && !self.hoisted.contains(name)
            && let Some((rendered, delta_stats, had_fb)) = self
                .arkui_components
                .get(&(ctor, name.to_string()))
                .cloned()
        {
            super::accumulate_decompile_stats(&mut self.stats, &delta_stats);
            if had_fb {
                self.current_fn_has_fallback = true;
            }
            for line in rendered.lines() {
                if line.is_empty() {
                    out.push('\n');
                } else {
                    out.push_str(pad);
                    out.push_str(line);
                    out.push('\n');
                }
            }
            return;
        }
        self.stats.classes += 1;
        if sendable {
            out.push_str(&format!(
                "{pad}/* sendable class (DefineSendableClass — no JS surface syntax) */\n"
            ));
        }
        if self.hoisted.contains(name) {
            out.push_str(&format!("{pad}{name} = class {name}"));
        } else {
            out.push_str(&format!("{pad}class {name}"));
        }
        tasks.push(PrintTask::StartClassBody {
            pad: pad.to_string(),
            indent,
            ctor,
            members,
            member_attrs,
        });
        match heritage {
            Some(Expr::Lit(Lit::Hole)) | None => {
                tasks.push(PrintTask::Raw(" {\n"));
            }
            Some(h) => {
                out.push_str(" extends ");
                tasks.push(PrintTask::Raw(" {\n"));
                tasks.push(PrintTask::Expr { expr: h, prec: 0 });
            }
        }
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "class body step emits constructor, private fields, and member methods iteratively"
    )]
    pub(in crate::emit) fn step_start_class_body<'b>(
        &mut self,
        pad: String,
        indent: usize,
        ctor: FuncId,
        members: abcd_ir::ConstId,
        member_attrs: &'b [abcd_ir::op::MemberAttrs],
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        self.class_depth += 1;
        out.push_str(&format!("{pad}  constructor("));

        let mut priv_names: BTreeSet<String> = BTreeSet::new();
        collect_private_names_with_index(self.module, self.index, ctor, &mut priv_names);
        let member_items = lit_of(self.module, members).and_then(Lit::into_array);
        if let Some(items) = &member_items {
            for item in items {
                if let Lit::MethodRef(f) = item {
                    collect_private_names_with_index(self.module, self.index, *f, &mut priv_names);
                }
            }
        }
        let fold = crate::classfold::plan_with_index(self.module, ctor, self.index);
        let folded_names: BTreeSet<&str> = fold
            .iter()
            .flat_map(|f| f.fields.iter().map(|(n, _)| n.as_str()))
            .collect();
        let mut priv_text = String::new();
        for pname in &priv_names {
            if folded_names.contains(pname.as_str()) {
                continue;
            }
            priv_text.push_str(&format!(
                "{pad}  #{};\n",
                super::expr::format_private_ident(pname)
            ));
        }
        if let Some(fold) = &fold {
            for (fname, cid) in &fold.fields {
                let value = lit_of(self.module, *cid)
                    .map(|l| self.render_lit_js(&l))
                    .unwrap_or_else(|| "undefined /* non-literal field value */".to_string());
                priv_text.push_str(&format!(
                    "{pad}  #{} = {}; /* es2abc instance-initializer fold */\n",
                    super::expr::format_private_ident(fname),
                    value
                ));
            }
        }

        tasks.push(PrintTask::CloseClass { pad: pad.clone() });

        if let Some(items) = member_items {
            let mut methods: Vec<(String, FuncId, Option<&'b abcd_ir::op::MemberAttrs>)> =
                Vec::new();
            let mut pending: Option<String> = None;
            let mut skipped = 0usize;
            let mut member_idx = 0usize;
            for mut item in items {
                match &mut item {
                    Lit::String(s) => pending = Some(std::mem::take(s)),
                    Lit::MethodRef(f) => {
                        let mname = pending.take().unwrap_or_else(|| format!("m${}", f.index()));
                        let attrs = member_attrs.get(member_idx);
                        member_idx += 1;
                        methods.push((mname, *f, attrs));
                    }
                    _ => skipped += 1,
                }
            }
            tasks.push(PrintTask::ClassMethods {
                pad: pad.clone(),
                indent,
                methods: methods.into_iter(),
                skipped,
            });
        } else {
            tasks.push(PrintTask::RawOwned(format!(
                "{pad}  /* member buffer is not a literal array (data shape) */\n"
            )));
        }

        if !priv_text.is_empty() {
            tasks.push(PrintTask::RawOwned(priv_text));
        }

        tasks.push(PrintTask::EnterInlineFunc {
            func: ctor,
            indent: indent + 2,
            style: InlineHeaderStyle {
                open_paren: false,
                drop_ret_ty: true,
                arrow: false,
                closing: format!("{pad}  }}\n"),
            },
        });
    }

    pub(crate) fn emit_class_method(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        f: FuncId,
        attrs: Option<&abcd_ir::op::MemberAttrs>,
        out: &mut String,
    ) {
        self.run_print_tasks(
            PrintRoot::ClassMethod {
                pad,
                indent,
                name,
                func: f,
                attrs,
            },
            out,
        );
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "class method emission threads indentation, name, func, attrs, and task stack"
    )]
    pub(in crate::emit) fn step_emit_class_method<'b>(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        f: FuncId,
        attrs: Option<&'b abcd_ir::op::MemberAttrs>,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        self.stats.class_methods += 1;
        let kind = attrs
            .map(|a| a.kind)
            .unwrap_or_else(|| crate::recover::effective_kind(self.module, f));
        let kind = if matches!(kind, FunctionKind::Function) {
            match crate::recover::effective_kind(self.module, f) {
                k @ (FunctionKind::Generator
                | FunctionKind::AsyncGenerator
                | FunctionKind::Async) => k,
                _ => kind,
            }
        } else {
            kind
        };
        let placement = if attrs.is_some_and(|a| a.is_static) {
            "static "
        } else {
            ""
        };
        let prefix = method_prefix(kind);
        let key = if is_legal_ident(name) {
            name.to_string()
        } else {
            render_pool_string(self.module, name)
        };
        out.push_str(&format!("{pad}  {placement}{prefix}{key}("));
        tasks.push(PrintTask::EnterInlineFunc {
            func: f,
            indent: indent + 2,
            style: InlineHeaderStyle {
                open_paren: false,
                drop_ret_ty: false,
                arrow: false,
                closing: format!("{pad}  }}\n"),
            },
        });
    }
}

/// Whether a function's own instructions reference `super`
/// (`LoadSuper`/`StoreSuper`/`super(...)` calls). Nested closures are
/// NOT descended into — their super binds to their own home object.
/// (N74-W4: drives the concise-method choice for object literals —
/// only concise methods carry a [[HomeObject]].)
pub(in crate::emit) fn fn_uses_super(module: &Module, func: FuncId) -> bool {
    let Some(f) = module.func(func) else {
        return false;
    };
    for &b in &f.blocks {
        let Some(block) = module.block(b) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::LoadSuper { .. } | Op::StoreSuper { .. } => return true,
                Op::Call {
                    kind:
                        CallKind::Super
                        | CallKind::SuperArrow
                        | CallKind::SuperSpread
                        | CallKind::SuperForwardAllArgs,
                    ..
                } => {
                    return true;
                }
                _ => {}
            }
        }
    }
    false
}

/// Collect private names referenced by a function's private-name ops
/// (the names are level/slot fallbacks when unresolvable — IR gap,
/// documented; the set makes declarations duplicate-safe).
#[cfg(test)]
pub(in crate::emit) fn collect_private_names(
    module: &Module,
    func: FuncId,
    out: &mut BTreeSet<String>,
) {
    collect_private_names_with_index(module, None, func, out);
}

pub(in crate::emit) fn collect_private_names_with_index(
    module: &Module,
    index: Option<&DecompileIndex>,
    func: FuncId,
    out: &mut BTreeSet<String>,
) {
    let owned_cache;
    let method_refs = match index {
        Some(idx) => &idx.const_method_refs,
        None => {
            owned_cache = crate::consts::ConstMethodRefCache::build(module);
            &owned_cache
        }
    };
    let mut visited: HashSet<FuncId> = HashSet::new();
    let mut stack: Vec<FuncId> = vec![func];

    while let Some(fid) = stack.pop() {
        if !visited.insert(fid) {
            continue;
        }
        let Some(f) = module.func(fid) else {
            continue;
        };
        let scopes = crate::names::NameScopes::build_with_index(module, fid, index);
        for &b in &f.blocks {
            let Some(block) = module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::LoadPrivate { level, slot, .. }
                    | Op::StorePrivate { level, slot, .. }
                    | Op::DefinePrivate { level, slot, .. }
                    | Op::TestPrivate { level, slot, .. } => {
                        let name = scopes
                            .name_of(iid)
                            .map(str::to_string)
                            .unwrap_or_else(|| format!("p{level}_{slot}"));
                        out.insert(name);
                    }
                    Op::CreatePrivateNames { names, .. } => {
                        if let Some(items) = lit_of(module, *names).and_then(Lit::into_array) {
                            for item in items {
                                if let Some(n) = item.into_string() {
                                    out.insert(n);
                                }
                            }
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        stack.push(*body);
                    }
                    Op::AllocObject { shape } => {
                        stack.extend_from_slice(method_refs.get(*shape));
                    }
                    _ => {}
                }
            }
        }
    }
}

/// The declaration keyword for a top-level function or closure.
pub(in crate::emit) fn fn_decl_keyword(kind: FunctionKind) -> &'static str {
    match kind {
        FunctionKind::Async => "async function",
        FunctionKind::Generator => "function*",
        FunctionKind::AsyncGenerator => "async function*",
        _ => "function",
    }
}

/// The declaration keyword for a closure expression.
pub(in crate::emit) fn closure_prefix(kind: FunctionKind) -> &'static str {
    fn_decl_keyword(kind)
}

/// A class-member prefix for [`FunctionKind`].
pub(in crate::emit) fn method_prefix(kind: FunctionKind) -> &'static str {
    match kind {
        FunctionKind::Constructor => "",
        FunctionKind::Getter => "get ",
        FunctionKind::Setter => "set ",
        FunctionKind::Async => "async ",
        FunctionKind::Generator => "*",
        FunctionKind::AsyncGenerator => "async *",
        // Arrows never appear in member position (concise methods are
        // `None` at the file level, not NC); degrade to plain syntax.
        FunctionKind::Function | FunctionKind::Arrow | FunctionKind::AsyncArrow => "",
    }
}

/// Render an IR type as a TypeScript annotation (the `--ts` flag).
/// `Reference` types resolve through the module's own class table; `Union`
/// slices walk iteratively over an explicit heap stack.
pub(in crate::emit) fn ty_ts(module: &Module, ty: &Ty) -> String {
    fn leaf_ty_ts(module: &Module, ty: &Ty) -> Option<String> {
        Some(match ty {
            Ty::Any => "any".to_string(),
            Ty::Unknown => "unknown".to_string(),
            Ty::Never => "never".to_string(),
            Ty::DynPrim(p) => match p {
                DynPrim::Undefined => "undefined".to_string(),
                DynPrim::Null => "null".to_string(),
                DynPrim::Bool => "boolean".to_string(),
                DynPrim::Number => "number".to_string(),
                DynPrim::String => "string".to_string(),
                DynPrim::Symbol => "symbol".to_string(),
                DynPrim::BigInt => "bigint".to_string(),
                DynPrim::Object => "object".to_string(),
            },
            Ty::Static(s) => match s {
                StaticTy::Void => "void".to_string(),
                StaticTy::Reference(cid) => {
                    let raw = module
                        .class(*cid)
                        .map(|c| sym_str(module, c.name))
                        .unwrap_or_default();
                    // A descriptor `Lfoo/Bar;` unwraps to its simple name.
                    let simple = raw
                        .strip_prefix('L')
                        .and_then(|r| r.strip_suffix(';'))
                        .and_then(|r| r.rsplit('/').next().map(str::to_string))
                        .unwrap_or(raw);
                    let name = sanitize(&simple);
                    if is_legal_ident(&name) {
                        name
                    } else {
                        "object".to_string()
                    }
                }
                // The ArkTS numeric statics all surface as TS `number`.
                _ => "number".to_string(),
            },
            Ty::Union(_) => return None,
        })
    }
    if let Some(s) = leaf_ty_ts(module, ty) {
        return s;
    }
    let Ty::Union(root) = ty else {
        return "any".to_string();
    };
    let mut stack: Vec<(&[Ty], usize, Vec<String>)> =
        vec![(root, 0, Vec::with_capacity(root.len()))];
    let mut completed: Option<String> = None;
    while let Some((slice, idx, parts)) = stack.last_mut() {
        if let Some(done) = completed.take() {
            parts.push(done);
        }
        if *idx < slice.len() {
            let item = &slice[*idx];
            *idx += 1;
            if let Some(s) = leaf_ty_ts(module, item) {
                parts.push(s);
            } else if let Ty::Union(sub) = item {
                stack.push((sub, 0, Vec::with_capacity(sub.len())));
            }
        } else {
            let joined = parts.join(" | ");
            stack.pop();
            if stack.is_empty() {
                return joined;
            }
            completed = Some(joined);
        }
    }
    String::new()
}

/// The `(params)` text and the TS return annotation for one function.
/// Bare (no annotation) when the flag is off, the function carries no
/// signature (12+/24 files — format fact #A7), or the signature does
/// not align with the IR parameter list (never fabricate).
impl<'m> Emitter<'m> {
    pub(in crate::emit) fn params_ret(&self, rf: &RecoveredFunc) -> (String, String) {
        let visible = &rf.params[rf.hidden_params.min(rf.params.len())..];
        if !self.opts.ts {
            return (visible.join(", "), String::new());
        }
        let sig: Option<&Signature> = self.module.func(rf.func).and_then(|f| f.sig.as_ref());
        let Some(sig) = sig else {
            return (visible.join(", "), String::new());
        };
        if sig.param_tys.len() != rf.params.len() {
            // Misaligned declaration — annotate nothing (honest skip).
            return (visible.join(", "), String::new());
        }
        let params = visible
            .iter()
            .enumerate()
            .map(|(i, p)| {
                format!(
                    "{p}: {}",
                    ty_ts(self.module, &sig.param_tys[rf.hidden_params + i])
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        let ret = match (&sig.return_ty, rf.kind) {
            // TS forbids a return annotation on constructors.
            (Some(t), FunctionKind::Constructor) => {
                let _ = t;
                String::new()
            }
            (Some(t), _) => format!(": {}", ty_ts(self.module, t)),
            (None, _) => String::new(),
        };
        (params, ret)
    }
}
