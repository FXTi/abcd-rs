//! Function, class, method, and TypeScript signature emission.

use super::*;

impl<'m> Emitter<'m> {
    /// Returns the (legalized, minted) emitted name and the raw name.
    pub(in crate::emit) fn emit_top_level_function(
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
        self.emit_nodes(&body, 1, out);
        out.push_str("}\n");
        if self.current_fn_has_fallback {
            self.stats.functions_with_fallbacks += 1;
        }
        (name, raw)
    }

    /// A closure/class-member body at a given indent.
    pub(in crate::emit) fn emit_function_body(
        &mut self,
        func: FuncId,
        indent: usize,
        out: &mut String,
    ) -> RecoveredFunc {
        let (rf, body) = self.func_nodes(func, false);
        let prev = self.current_kind;
        self.current_kind = rf.kind;
        let prev_hoisted = std::mem::replace(&mut self.hoisted, escaped_temps(&body));
        let pad = "  ".repeat(indent);
        for d in lex_decls(&body, &rf.params) {
            out.push_str(&format!("{pad}let {d};\n"));
        }
        for h in self.hoisted.clone() {
            out.push_str(&format!(
                "{pad}var {h}; /* hoisted temp: used outside its def's block */\n"
            ));
        }
        self.emit_nodes(&body, indent, out);
        self.current_kind = prev;
        self.hoisted = prev_hoisted;
        rf
    }

    // ── Classes & closures ───────────────────────────────────────────

    /// Assignment form of a hoisted class (`name = class …`); the
    /// hoisted check in [`Emitter::emit_class`] does the work.
    // Signature mirrors `emit_class` (it is a thin forwarder): every
    // parameter is a distinct facet of the class IR node.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::emit) fn emit_class_assign(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        ctor: FuncId,
        heritage: Option<Box<Expr>>,
        members: abcd_ir::ConstId,
        member_attrs: &[abcd_ir::op::MemberAttrs],
        sendable: bool,
        out: &mut String,
    ) {
        self.emit_class(
            pad,
            indent,
            name,
            ctor,
            heritage,
            members,
            member_attrs,
            sendable,
            out,
        );
    }

    /// `class Name extends H { constructor(…) {…} …methods… }`.
    // Every parameter is a distinct facet of the class IR node; a
    // bundling struct would only rename the plumbing.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::emit) fn emit_class(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        ctor: FuncId,
        heritage: Option<Box<Expr>>,
        members: abcd_ir::ConstId,
        member_attrs: &[abcd_ir::op::MemberAttrs],
        sendable: bool,
        out: &mut String,
    ) {
        self.stats.classes += 1;
        if sendable {
            out.push_str(&format!(
                "{pad}/* sendable class (DefineSendableClass — no JS surface syntax) */\n"
            ));
        }
        let ext = match heritage.as_deref() {
            // The hole is es2abc's "no extends" marker (suppressed
            // upstream at recover — belt here for direct Lit heritage).
            // An explicit `extends undefined` (Lit::Undefined) is real
            // source semantics and must survive (N74-W4).
            Some(Expr::Lit(Lit::Hole)) | None => String::new(),
            Some(h) => {
                let mut s = String::new();
                self.expr(h, 0, &mut s);
                format!(" extends {s}")
            }
        };
        if self.hoisted.contains(name) {
            // Hoisted escapee: `name = class name …` (the `var` is at
            // the function top; a block-scoped `class` declaration
            // would not escape this structured block).
            out.push_str(&format!("{pad}{name} = class {name}{ext} {{\n"));
        } else {
            out.push_str(&format!("{pad}class {name}{ext} {{\n"));
        }
        self.class_depth += 1;
        // The constructor.
        out.push_str(&format!("{pad}  constructor("));
        let rf = {
            // Emit the ctor body into a scratch buffer to interleave
            // the signature.
            let mut body = String::new();
            let rf = self.emit_function_body(ctor, indent + 2, &mut body);
            // TS forbids a return annotation on a class constructor —
            // drop it here regardless of the ctor's recorded kind (the
            // class table's ctor slot is authoritative, not the kind).
            let (params, _) = self.params_ret(&rf);
            out.push_str(&format!("{params}) {{\n{body}"));
            rf
        };
        let _ = rf;
        out.push_str(&format!("{pad}  }}\n"));
        // Private-name declarations (`#x;`) used by the ctor/members —
        // node requires them declared in the class body (the IR gap:
        // CreatePrivateNames buffers carry numeric slots, not strings,
        // so names are the resolved/fallback ones — documented).
        let mut priv_names: BTreeSet<String> = BTreeSet::new();
        collect_private_names_with_index(self.module, self.index, ctor, &mut priv_names);
        if let Some(Lit::Array(items)) = lit_of(self.module, members) {
            for item in &items {
                if let Lit::MethodRef(f) = item {
                    collect_private_names_with_index(self.module, self.index, *f, &mut priv_names);
                }
            }
        }
        // B2 class-field fold: the instance initializer's constant
        // private definitions print as `#name = <const>;` declarations
        // (the ctor's initializer call is elided at recover). Folded
        // names are EXCLUDED from the bare `#name;` set — a duplicate
        // private declaration would be a SyntaxError.
        let fold = crate::classfold::plan_with_index(self.module, ctor, self.index);
        let folded_names: BTreeSet<&str> = fold
            .iter()
            .flat_map(|f| f.fields.iter().map(|(n, _)| n.as_str()))
            .collect();
        for name in &priv_names {
            if folded_names.contains(name.as_str()) {
                continue;
            }
            out.push_str(&format!("{pad}  #{};\n", sanitize(name)));
        }
        if let Some(fold) = &fold {
            for (fname, cid) in &fold.fields {
                let value = lit_of(self.module, *cid)
                    .map(|l| self.render_lit_js(&l))
                    .unwrap_or_else(|| "undefined /* non-literal field value */".to_string());
                out.push_str(&format!(
                    "{pad}  #{} = {}; /* es2abc instance-initializer fold */\n",
                    sanitize(fname),
                    value
                ));
            }
        }
        // The member buffer: flat [name, MethodRef, …metadata…]; the
        // B2 member_attrs projection (parallel to the MethodRef
        // sequence) carries placement (static/instance) and the
        // buffer-tag kind — empty = unknown (conservative instance
        // placement, FunctionData kind).
        if let Some(Lit::Array(items)) = lit_of(self.module, members) {
            let mut pending: Option<String> = None;
            let mut skipped = 0usize;
            let mut member_idx = 0usize;
            for item in &items {
                match item {
                    Lit::String(s) => pending = Some(s.clone()),
                    Lit::MethodRef(f) => {
                        let mname = pending.take().unwrap_or_else(|| format!("m${}", f.index()));
                        let attrs = member_attrs.get(member_idx);
                        member_idx += 1;
                        self.emit_class_method(pad, indent, &mname, *f, attrs, out);
                    }
                    _ => skipped += 1,
                }
            }
            if skipped > 0 {
                out.push_str(&format!(
                    "{pad}  /* {skipped} member-buffer metadata entries skipped (name/method pairs consumed; numeric payloads are runtime metadata) */\n"
                ));
            }
        } else {
            out.push_str(&format!(
                "{pad}  /* member buffer is not a literal array (data shape) */\n"
            ));
        }
        self.class_depth -= 1;
        out.push_str(&format!("{pad}}}\n"));
    }

    fn emit_class_method(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        f: FuncId,
        attrs: Option<&abcd_ir::op::MemberAttrs>,
        out: &mut String,
    ) {
        self.stats.class_methods += 1;
        // B2: the buffer's own attribute payloads win when known —
        // placement (static vs prototype) is ONLY carried by the
        // buffer's trailing nonStaticNum count, and the callable kind
        // by the entry's method-kind tag; the conservative fallback
        // (attrs unknown) is instance placement + the lifted
        // FunctionData kind (the pre-B2 behavior).
        let kind = attrs
            .map(|a| a.kind)
            .unwrap_or_else(|| crate::recover::effective_kind(self.module, f));
        // N74-W4: the 24.0.0.0 member buffer tags generator and async
        // methods as plain `method` (probe: methods-gen-yield-as-statement's
        // buffer reads `method:#~A>#g1` while the function body carries
        // `creategeneratorobj`), so a buffer `Function` kind must yield to
        // the member function's own lifted kind when that is more specific
        // — otherwise the `*`/`async` marker is lost (`yield` outside a
        // generator is an es2abc SyntaxError; a plain method returns
        // undefined where the source returned an iterator). Getter/Setter
        // are accessor kinds the FUNCTION metadata does not carry — the
        // buffer tag stays authoritative for them. The lifted kind here is
        // the EVIDENCE kind (Bug A: 3.2-era files do not tag async
        // functions in the metadata; the body's `AsyncFunctionEnter` is
        // decisive — an `await` in a non-async body is the es2abc
        // SyntaxError the wild smoke hit).
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
        let mut body = String::new();
        let rf = self.emit_function_body(f, indent + 2, &mut body);
        let (params, ret) = self.params_ret(&rf);
        out.push_str(&format!(
            "{pad}  {placement}{prefix}{key}({params}){ret} {{\n{body}"
        ));
        out.push_str(&format!("{pad}  }}\n"));
    }
}

impl<'m> Emitter<'m> {
    /// A concise object-literal member: `get [k]() {…}` / `*name() {…}`
    /// (N74-W4). The ONLY member form carrying a [[HomeObject]] (super)
    /// — and the only legal spelling for generator members.
    pub(in crate::emit) fn concise_method(
        &mut self,
        prefix: &str,
        key: &crate::expr::ObjKey,
        body: FuncId,
    ) -> String {
        let mut s = String::from(prefix);
        match key {
            crate::expr::ObjKey::Name(n) => {
                if is_legal_ident(n) {
                    s.push_str(n);
                } else {
                    s.push_str(&render_pool_string(self.module, n));
                }
            }
            crate::expr::ObjKey::Computed(e) => {
                s.push('[');
                let mut k = String::new();
                self.expr(e, 0, &mut k);
                s.push_str(&k);
                s.push(']');
            }
        }
        let mut text = String::new();
        let rf = self.emit_function_body(body, 1, &mut text);
        let (params, ret) = self.params_ret(&rf);
        s.push_str(&format!("({params}){ret} {{\n{text}}}"));
        s
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
                    kind: CallKind::Super | CallKind::SuperSpread | CallKind::SuperForwardAllArgs,
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
    let Some(f) = module.func(func) else {
        return;
    };
    let scopes = crate::names::NameScopes::build_with_index(module, func, index);
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
                    if let Some(Lit::Array(items)) = lit_of(module, *names) {
                        for item in items {
                            if let Lit::String(n) = item {
                                out.insert(n.clone());
                            }
                        }
                    }
                }
                _ => {}
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
/// `Reference` types resolve through the module's own class table.
pub(in crate::emit) fn ty_ts(module: &Module, ty: &Ty) -> String {
    match ty {
        Ty::Any => "any".to_string(),
        Ty::Unknown => "unknown".to_string(),
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
        Ty::Union(ts) => ts
            .iter()
            .map(|t| ty_ts(module, t))
            .collect::<Vec<_>>()
            .join(" | "),
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
    }
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
