//! Precedence-exact expression, call, unary, and literal emission.

use super::decl::{closure_prefix, fn_uses_super, method_prefix};
use super::*;

impl<'m> Emitter<'m> {
    // ── Expressions (precedence-correct) ─────────────────────────────

    /// Print an expression; parenthesize when its precedence is below
    /// `prec`.
    pub(in crate::emit) fn expr(&mut self, e: &Expr, prec: u8, out: &mut String) {
        if e.precedence() < prec {
            out.push('(');
            self.expr_inner(e, out);
            out.push(')');
        } else {
            self.expr_inner(e, out);
        }
    }

    /// A sub-expression at context precedence `prec`.
    pub(in crate::emit) fn sub(&mut self, e: &Expr, prec: u8, out: &mut String) {
        self.expr(e, prec, out);
    }

    #[allow(clippy::too_many_lines)]
    pub(in crate::emit) fn expr_inner(&mut self, e: &Expr, out: &mut String) {
        match e {
            Expr::Lit(lit) => out.push_str(&self.render_lit_js(lit)),
            Expr::Ident(name) => out.push_str(name),
            Expr::Temp { name, .. } => out.push_str(name),
            Expr::PropName {
                object,
                name,
                dot_legal,
            } => {
                self.sub(object, 19, out);
                if *dot_legal {
                    out.push_str(&format!(".{name}"));
                } else {
                    out.push_str(&format!("[{}]", render_pool_string(self.module, name)));
                }
            }
            Expr::PropIndex { object, index } | Expr::PropDyn { object, key: index } => {
                self.sub(object, 19, out);
                out.push('[');
                self.sub(index, 0, out);
                out.push(']');
            }
            Expr::PrivateLoad { object, name } => {
                if self.class_depth > 0 {
                    self.sub(object, 19, out);
                    out.push_str(&format!(".#{name}"));
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("LoadPrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    self.sub(object, 19, out);
                    out.push_str(&format!(
                        "[{}] /*private #{name} — out-of-class*/",
                        render_pool_string(self.module, name)
                    ));
                }
            }
            Expr::PrivateTest { object, name } => {
                if self.class_depth > 0 {
                    out.push_str(&format!("#{name} in "));
                    self.sub(object, 12, out);
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("TestPrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    out.push_str(&format!("({} in ", render_pool_string(self.module, name)));
                    self.sub(object, 0, out);
                    out.push_str(") /*private test — out-of-class*/");
                }
            }
            Expr::SuperProp { name, key } => match (name, key) {
                (Some(n), None) => out.push_str(&format!("super.{n}")),
                (None, Some(k)) => {
                    out.push_str("super[");
                    self.sub(k, 0, out);
                    out.push(']');
                }
                _ => out.push_str("super[?]"),
            },
            Expr::Call {
                callee,
                this,
                args,
                kind,
            } => self.emit_call(callee, this.as_deref(), args, *kind, out),
            Expr::SuperMarker => out.push_str("super"),
            Expr::DynamicImport { specifier } => {
                out.push_str("import(");
                self.sub(specifier, 0, out);
                out.push(')');
            }
            Expr::Unary { op, operand } => self.emit_unary(*op, operand, out),
            Expr::Delete { target } => {
                out.push_str("delete ");
                self.sub(target, 17, out);
            }
            Expr::Binary { op, left, right } => {
                let prec = e.precedence();
                // `**` is right-associative; a unary left operand of
                // `**` is a JS syntax error (always parenthesized).
                let left_prec = if *op == BinOp::Exp { 17 } else { prec };
                let right_prec = if *op == BinOp::Exp { prec } else { prec + 1 };
                let force_left_parens =
                    *op == BinOp::Exp && matches!(left.as_ref(), Expr::Unary { .. });
                if force_left_parens {
                    out.push('(');
                    self.expr_inner(left, out);
                    out.push(')');
                } else {
                    self.sub(left, left_prec, out);
                }
                out.push_str(&format!(" {} ", binop_sym(*op)));
                self.sub(right, right_prec, out);
            }
            Expr::Compare { op, left, right } => {
                let prec = e.precedence();
                self.sub(left, prec, out);
                out.push_str(&format!(" {} ", cmpop_sym(*op)));
                self.sub(right, prec + 1, out);
            }
            Expr::RegExp { pattern, flags } => {
                let body = pattern.replace('/', "\\/");
                out.push_str(&format!("/{body}/{flags}"));
            }
            Expr::ObjectLit { entries } => {
                out.push_str(&render_lit_m(self.module, &Lit::Object(entries.clone())));
            }
            Expr::ArrayLit { elements } => {
                out.push_str(&render_lit_m(self.module, &Lit::Array(elements.clone())));
            }
            Expr::ObjectBuild { entries } => {
                out.push('{');
                let parts: Vec<String> = entries
                    .iter()
                    .map(|en| {
                        let mut s = String::new();
                        match en {
                            ObjEntry::KeyValue(k, v) => {
                                s.push_str(&render_lit_key_pub(self.module, k));
                                s.push_str(": ");
                                self.expr(v, 0, &mut s);
                            }
                            ObjEntry::Computed(k, v) => {
                                s.push('[');
                                self.expr(k, 0, &mut s);
                                s.push_str("]: ");
                                self.expr(v, 0, &mut s);
                            }
                            ObjEntry::Spread(x) => {
                                s.push_str("...");
                                self.expr(x, 0, &mut s);
                            }
                            ObjEntry::Proto(x) => {
                                s.push_str("__proto__: ");
                                self.expr(x, 0, &mut s);
                            }
                            ObjEntry::Method(n, f) => {
                                // N74-W4: a `key: function` property
                                // value has NO [[HomeObject]] — a body
                                // referencing `super` is a SyntaxError
                                // there (es2abc: "Unexpected super
                                // keyword"), and a generator body loses
                                // its `yield` legality the same way.
                                // Both MUST print as the concise method
                                // form (`key() {…}` / `*key() {…}`),
                                // which carries both.
                                let concise = match f {
                                    Expr::Closure { body, kind, .. } => {
                                        matches!(
                                            kind,
                                            FunctionKind::Generator | FunctionKind::AsyncGenerator
                                        ) || fn_uses_super(self.module, *body)
                                    }
                                    _ => false,
                                };
                                if concise {
                                    let Expr::Closure { body, kind, .. } = f else {
                                        unreachable!()
                                    };
                                    s.push_str(&self.concise_method(
                                        method_prefix(*kind),
                                        &crate::expr::ObjKey::Name(n.clone()),
                                        *body,
                                    ));
                                } else {
                                    if is_legal_ident(n) {
                                        s.push_str(n);
                                    } else {
                                        s.push_str(&render_pool_string(self.module, n));
                                    }
                                    s.push_str(": ");
                                    self.expr(f, 0, &mut s);
                                }
                            }
                            // N74-W4: accessors folded from
                            // `DefineGetterSetterByValue` (folds.rs) —
                            // always the concise form (HomeObject,
                            // enumerability).
                            ObjEntry::Getter(k, f) => {
                                if let Expr::Closure { body, .. } = f {
                                    s.push_str(&self.concise_method("get ", k, *body));
                                } else {
                                    s.push_str("/* getter: non-closure (data shape) */");
                                }
                            }
                            ObjEntry::Setter(k, f) => {
                                if let Expr::Closure { body, .. } = f {
                                    s.push_str(&self.concise_method("set ", k, *body));
                                } else {
                                    s.push_str("/* setter: non-closure (data shape) */");
                                }
                            }
                        }
                        s
                    })
                    .collect();
                out.push_str(&parts.join(", "));
                out.push('}');
            }
            Expr::ArrayBuild { elements } => {
                let parts: Vec<String> = elements
                    .iter()
                    .map(|el| {
                        let mut s = String::new();
                        match el {
                            ArrayElem::Item(x) => self.expr(x, 0, &mut s),
                            ArrayElem::Spread(x) => {
                                s.push_str("...");
                                self.expr(x, 0, &mut s);
                            }
                        }
                        s
                    })
                    .collect();
                out.push_str(&format!("[{}]", parts.join(", ")));
            }
            Expr::Closure {
                body, name, kind, ..
            } => {
                self.stats.closures += 1;
                let body = *body;
                let kind = *kind;
                let display = sanitize(name);
                let named = !display.is_empty() && display != "_" && is_legal_ident(&display);
                let arrow = matches!(kind, FunctionKind::Arrow | FunctionKind::AsyncArrow);
                if arrow {
                    // The arrow signal IS recoverable (the file's
                    // NC_FUNCTION kind — d-P8); arrows are anonymous,
                    // the binding name comes from the context.
                    let prefix = if kind == FunctionKind::AsyncArrow {
                        "async ("
                    } else {
                        "("
                    };
                    out.push_str(prefix);
                } else {
                    let keyword = closure_prefix(kind);
                    if named {
                        out.push_str(&format!("{keyword} {display}("));
                    } else {
                        out.push_str(&format!("{keyword} ("));
                    }
                }
                let mut text = String::new();
                let rf = self.emit_function_body(body, 1, &mut text);
                let (params, ret) = self.params_ret(&rf);
                if arrow {
                    out.push_str(&format!("{params}){ret} => {{\n{text}}}"));
                } else {
                    // `FunctionKind::Function` closures ARE function
                    // expressions (the file marks arrows NC — d-P8), so
                    // no arrow/function caveat applies.
                    out.push_str(&format!("{params}){ret} {{\n{text}}}"));
                }
            }
            Expr::Class {
                ctor,
                name,
                heritage,
                members,
                member_attrs,
                sendable,
            } => {
                // Class expression form.
                let (ctor, name, heritage, members, member_attrs, sendable) = (
                    *ctor,
                    name.clone(),
                    heritage.clone(),
                    *members,
                    member_attrs.clone(),
                    *sendable,
                );
                let mut s = String::new();
                self.emit_class(
                    "",
                    0,
                    &sanitize(&name),
                    ctor,
                    heritage,
                    members,
                    &member_attrs,
                    sendable,
                    &mut s,
                );
                out.push_str(s.trim_end());
            }
            Expr::Yield { value } => {
                if matches!(
                    self.current_kind,
                    FunctionKind::Generator | FunctionKind::AsyncGenerator
                ) {
                    out.push_str("yield ");
                    self.sub(value, 0, out);
                } else {
                    // `SuspendGenerator` inside a plain-async function is
                    // the async suspension machinery (R4), not a source
                    // `yield` — `yield` would not parse here.
                    *self
                        .stats
                        .fallback_comments
                        .entry("SuspendGenerator(async-machinery)")
                        .or_insert(0) += 1;
                    out.push_str("/*async-machinery suspend (R4; not a source yield)*/ ");
                    self.sub(value, 0, out);
                }
            }
            Expr::YieldStar { value } => {
                // Produced only by the YieldStar fold (d-P15), which is
                // kind-gated to Generator/AsyncGenerator — `yield*`
                // always parses here.
                out.push_str("yield* ");
                self.sub(value, 0, out);
            }
            Expr::Await { value, .. } => {
                if matches!(
                    self.current_kind,
                    FunctionKind::Async | FunctionKind::AsyncArrow | FunctionKind::AsyncGenerator
                ) {
                    out.push_str("await ");
                    self.sub(value, 17, out);
                } else {
                    // Defensive (Bug A residual): `await` parses only in
                    // an async body. The effective-kind evidence upgrade
                    // makes this unreachable for the vendor shape
                    // (`AwaitUncaught` always pairs with
                    // `AsyncFunctionEnter`); a stray await in a
                    // metadata-plain body degrades LOUDLY to its operand
                    // instead of emitting unparseable text (mirrors the
                    // `SuspendGenerator` arm above).
                    *self
                        .stats
                        .fallback_comments
                        .entry("Await(non-async context)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    out.push_str("/*await outside async context (operand kept)*/ ");
                    self.sub(value, 0, out);
                }
            }
            Expr::NewTarget => out.push_str("new.target"),
            Expr::GlobalThis => out.push_str("globalThis"),
            Expr::SelfFunction(name) => out.push_str(&sanitize(name)),
            Expr::Arguments => out.push_str("arguments"),
            Expr::RestArgs { start_index } => {
                out.push_str(&format!(
                    "[...arguments].slice({start_index}) /*CopyRestArgs*/"
                ));
            }
            Expr::TemplateObject { raw, cooked } => {
                // G4 RESOLVED (d-P10): with the raw strings recovered the
                // node emits as a real backtick literal carrying the raw
                // text verbatim — an identity tag `(_=>_)` reconstructs
                // the (frozen, `.raw`-bearing) template object the
                // runtime would build, and es2abc re-derives the cooked
                // strings from the raw source text per spec. Multi-quasi
                // templates get inert `${0}` separators (a no-substitution
                // template has exactly one quasi; the tag ignores the
                // dummy values). The junction is safe: appending `${0}`
                // after any valid raw text cannot create a spurious
                // interpolation (only an exact `${` opens one, and raw
                // ending in `$` yields `…$` + `${0}` = `…$${0}` which
                // still terminates the quasi at the appended marker).
                let raw_strings: Option<Vec<&str>> = raw.as_ref().and_then(|lits| {
                    lits.iter()
                        .map(|l| match l {
                            Lit::String(s) => Some(s.as_str()),
                            _ => None,
                        })
                        .collect::<Option<Vec<&str>>>()
                });
                match raw_strings {
                    Some(parts) if !parts.is_empty() => {
                        out.push_str("((_=>_)`");
                        out.push_str(&parts.join("${0}"));
                        out.push_str("`)");
                    }
                    _ => {
                        // Cooked-only fallback — documented per case: raw
                        // is genuinely absent (unresolved literal operand
                        // or non-string quasi). The cooked text is
                        // emitted as a plain string (its raw form is
                        // unrecoverable from cooked text).
                        *self
                            .stats
                            .fallback_comments
                            .entry("GetTemplateObject")
                            .or_insert(0) += 1;
                        self.current_fn_has_fallback = true;
                        match cooked {
                            Some(lits) => {
                                let joined: Vec<String> = lits
                                    .iter()
                                    .map(|l| match l {
                                        Lit::String(s) => s.clone(),
                                        other => render_lit_m(self.module, other),
                                    })
                                    .collect();
                                out.push_str(&format!(
                                    "{} /*template: raw absent, cooked-only*/",
                                    render_pool_string(self.module, &joined.join(""))
                                ));
                            }
                            None => {
                                out.push_str("\"\" /*template unresolved (raw+cooked absent)*/")
                            }
                        }
                    }
                }
            }
            Expr::TaggedTemplate { tag, quasis, exprs } => {
                self.sub(tag, 19, out);
                out.push('`');
                for (i, q) in quasis.iter().enumerate() {
                    out.push_str(q);
                    if let Some(arg) = exprs.get(i) {
                        out.push_str("${");
                        self.expr(arg, 0, out);
                        out.push('}');
                    }
                }
                out.push('`');
            }
            Expr::IterResultObj { value, done } => {
                out.push_str("{ value: ");
                self.sub(value, 0, out);
                out.push_str(", done: ");
                self.sub(done, 0, out);
                out.push_str(" } /*iter-result*/");
            }
            Expr::Iter {
                op: IterOp::GetIterator,
                obj,
                ..
            } => {
                // The real protocol call (dream gate: the passthrough
                // left arrays without `.next` — destructuring failed
                // with "undefined is not callable"). The for-of fold
                // consumes the AST node pre-print, so only direct
                // protocol uses (destructuring, spread) land here.
                self.sub(obj, 19, out);
                out.push_str("[Symbol.iterator]()");
            }
            Expr::Iter {
                op: IterOp::GetAsyncIterator,
                obj,
                ..
            } => {
                // Vendor falls back to Symbol.iterator when no async
                // iterator exists — elided here (comment); corpus
                // coverage for for-await is via the fold anyway.
                self.sub(obj, 19, out);
                out.push_str("[Symbol.asyncIterator]() /*sync-fallback elided*/");
            }
            Expr::Iter { op, obj, status } => {
                let name = iter_op_name(*op);
                match status {
                    NodeStatus::Fallback => {
                        *self.stats.fallback_comments.entry(name).or_insert(0) += 1;
                        self.current_fn_has_fallback = true;
                        out.push_str(&format!("/*hard-fallback {name}*/ "));
                    }
                    NodeStatus::Plumbing => {
                        out.push_str(&format!("/*{name} plumbing*/ "));
                    }
                    NodeStatus::Expressed => {}
                }
                self.sub(obj, 0, out);
            }
            Expr::CreateGenerator { func } => {
                out.push_str("/*CreateGenerator plumbing*/ ");
                self.sub(func, 0, out);
            }
            Expr::GeneratorDriver { resume, genobj } => {
                let name = if *resume {
                    "ResumeGenerator"
                } else {
                    "GetResumeMode"
                };
                *self.stats.fallback_comments.entry(name).or_insert(0) += 1;
                self.current_fn_has_fallback = true;
                out.push_str(&format!("/*hard-fallback {name} (generator driver, R4)*/ "));
                self.sub(genobj, 0, out);
            }
            Expr::AsyncDriver { resolve, value } => {
                let name = if *resolve {
                    "AsyncResolve"
                } else {
                    "AsyncReject"
                };
                *self.stats.fallback_comments.entry(name).or_insert(0) += 1;
                self.current_fn_has_fallback = true;
                out.push_str(&format!("/*hard-fallback {name} (async driver, R4)*/ "));
                self.sub(value, 0, out);
            }
            Expr::CopyDataProps { dst, src } => {
                out.push_str("Object.assign(");
                self.sub(dst, 0, out);
                out.push_str(", ");
                self.sub(src, 0, out);
                out.push_str(") /*CopyDataProps: approximate outside a literal*/");
            }
            Expr::SetObjectWithProto { obj, proto } => {
                out.push_str("Object.setPrototypeOf(");
                self.sub(obj, 0, out);
                out.push_str(", ");
                self.sub(proto, 0, out);
                out.push_str(") /*NOT identical: no-setter semantics*/");
            }
            Expr::ArraySpread { dst, src, .. } => {
                self.sub(dst, 19, out);
                out.push_str(".push(...");
                self.sub(src, 0, out);
                out.push_str(") /*ArraySpread: result=new-index*/");
            }
            Expr::RestObject { obj, .. } => {
                out.push_str("/*CreateObjectWithExcludedKeys plumbing*/ ");
                self.sub(obj, 0, out);
            }
            Expr::DefineGetterSetter {
                obj,
                key,
                getter,
                setter,
            } => {
                // defineProperty with only the PRESENT accessor: an
                // explicit `get: undefined` would clobber an existing
                // getter (dream gate: local/class-accessors' setter
                // definition wiped the getter → NaN).
                let g = matches!(getter.as_ref(), Expr::Lit(Lit::Undefined));
                let s = matches!(setter.as_ref(), Expr::Lit(Lit::Undefined));
                out.push_str("Object.defineProperty(");
                self.sub(obj, 0, out);
                out.push_str(", ");
                self.sub(key, 0, out);
                out.push_str(", {");
                if !g {
                    out.push_str(" get: ");
                    self.sub(getter, 0, out);
                }
                if !s {
                    if !g {
                        out.push(',');
                    }
                    out.push_str(" set: ");
                    self.sub(setter, 0, out);
                }
                // Class accessors are configurable — without it the
                // getter/setter pair can't be defined in two steps
                // (dream gate: class-accessors on 12.x, "Cannot define
                // property").
                out.push_str(", configurable: true }) /*DefineGetterSetterByValue: approximate*/");
            }
            Expr::ModuleNamespace { index } => {
                out.push_str(&crate::names::namespace_fallback(*index));
            }
            Expr::Fallback { op, note, .. } => {
                *self.stats.fallback_comments.entry(op).or_insert(0) += 1;
                self.current_fn_has_fallback = true;
                out.push_str(&format!("undefined /*fallback {op}: {note}*/"));
            }
        }
    }

    fn emit_call(
        &mut self,
        callee: &Expr,
        this: Option<&Expr>,
        args: &[Expr],
        kind: CallKind,
        out: &mut String,
    ) {
        match kind {
            CallKind::Direct | CallKind::Dynamic => {
                // `callthis*`: the receiver matters. Method form when
                // the callee is a property load of the SAME receiver
                // (`obj.m(…)`); otherwise `.call(this, …)` — dropping
                // the receiver silently is a bug (dream gate:
                // destructuring's `iterator.next()` became `next()` —
                // "undefined is not callable"/wrong this).
                let mut done = false;
                if let Some(t) = this {
                    // Reachability note (coverage audit): at HEAD no
                    // producer can place a `PropName`/`PropIndex`/
                    // `PropDyn` in `callee` with `object == this` —
                    // recover builds call callees only via `expr_of`, and
                    // the receiver-load ops (`LoadProp`/`LoadPropIdx`/
                    // `LoadPropDyn`) are observable (effects: may_throw +
                    // may_call), so `compute_inline` never inlines them
                    // and the callee always arrives as a `Temp`/`Ident`/
                    // `Lit`; neither folds nor structure rewrites
                    // `Call.callee`. The three reunification arms below
                    // are kept as defense-in-depth for future producers.
                    match callee {
                        Expr::PropName {
                            object,
                            name,
                            dot_legal: true,
                        } if object.as_ref() == t => {
                            self.sub(t, 19, out);
                            out.push_str(&format!(".{name}"));
                            self.emit_args(args, out);
                            done = true;
                        }
                        Expr::PropIndex { object, index } if object.as_ref() == t => {
                            self.sub(t, 19, out);
                            out.push('[');
                            self.sub(index, 0, out);
                            out.push(']');
                            self.emit_args(args, out);
                            done = true;
                        }
                        Expr::PropDyn { object, key } if object.as_ref() == t => {
                            self.sub(t, 19, out);
                            out.push('[');
                            self.sub(key, 0, out);
                            out.push(']');
                            self.emit_args(args, out);
                            done = true;
                        }
                        _ => {
                            self.sub(callee, 19, out);
                            out.push_str(".call(");
                            self.sub(t, 0, out);
                            for a in args {
                                out.push_str(", ");
                                self.sub(a, 0, out);
                            }
                            out.push(')');
                            done = true;
                        }
                    }
                }
                if !done {
                    self.sub(callee, 19, out);
                    self.emit_args(args, out);
                }
            }
            CallKind::New => {
                out.push_str("new ");
                self.sub(callee, 19, out);
                self.emit_args(args, out);
            }
            CallKind::Apply => {
                self.sub(callee, 19, out);
                out.push_str(".apply(");
                match this {
                    Some(t) => self.sub(t, 0, out),
                    None => out.push_str("undefined"),
                }
                for a in args {
                    out.push_str(", ");
                    self.sub(a, 0, out);
                }
                out.push(')');
            }
            CallKind::Super => {
                out.push_str("super");
                self.emit_args(args, out);
            }
            CallKind::SuperSpread => {
                out.push_str("super(...");
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.sub(a, 0, out);
                }
                out.push(')');
            }
            CallKind::SuperForwardAllArgs => {
                // `args` is not a real binding — the op forwards the
                // actual arguments object (dream gate: super-properties
                // hit "args is not defined").
                out.push_str(
                    "super(...arguments) /*forward-all: default derived ctor elision pending*/",
                );
            }
        }
    }

    fn emit_args(&mut self, args: &[Expr], out: &mut String) {
        out.push('(');
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.sub(a, 0, out);
        }
        out.push(')');
    }

    fn emit_unary(&mut self, op: UnOp, operand: &Expr, out: &mut String) {
        match op {
            UnOp::IsTrue => {
                // Truthiness coercion feeding a condition: the bare
                // operand is equivalent in boolean contexts (printed
                // at context precedence — no coercion node remains).
                self.sub(operand, 0, out);
            }
            UnOp::IsFalse => {
                out.push('!');
                self.sub(operand, 17, out);
            }
            UnOp::LogicalNot => {
                out.push('!');
                self.sub(operand, 17, out);
            }
            UnOp::TypeOf => {
                out.push_str("typeof ");
                self.sub(operand, 17, out);
            }
            UnOp::Void => {
                out.push_str("void ");
                self.sub(operand, 17, out);
            }
            UnOp::BitNot => {
                out.push('~');
                self.sub(operand, 17, out);
            }
            UnOp::ToNumber => {
                out.push('+');
                // `++x`-style ambiguity (N74-W4: `+(+1)` printed as
                // `++1.0` — an invalid pre-increment LHS): parenthesize
                // unary operands, the same rule as `Minus` below.
                if matches!(operand, Expr::Unary { .. }) {
                    out.push('(');
                    self.expr_inner(operand, out);
                    out.push(')');
                } else {
                    self.sub(operand, 17, out);
                }
            }
            UnOp::ToNumeric => {
                out.push('+');
                if matches!(operand, Expr::Unary { .. }) {
                    out.push('(');
                    self.expr_inner(operand, out);
                    out.push(')');
                } else {
                    self.sub(operand, 17, out);
                }
                out.push_str(" /*ToNumeric*/");
            }
            UnOp::Minus => {
                out.push('-');
                // `--x`-style ambiguity: parenthesize unary operands.
                if matches!(operand, Expr::Unary { .. }) {
                    out.push('(');
                    self.expr_inner(operand, out);
                    out.push(')');
                } else {
                    self.sub(operand, 17, out);
                }
            }
            UnOp::Inc | UnOp::Dec => {
                // The vendored inc/dec are VALUE-pure (`acc ± 1` — the
                // store-back is a separate op); JS `--x` would mutate a
                // const temporary (dream gate: "Assignment to const
                // variable") and double-fire property setters. Emit the
                // pure arithmetic form, keeping the ToNumber coercion:
                // N74-W4 — a bare `x + 1` STRING-concatenates a
                // non-number operand (test262 S8.6_A3_T1: `++{foo:'bar'}
                // .foo` must be NaN, never "bar1"); the unary `+` first
                // restores the vendor's ToNumber. Corner: vendor bigint
                // inc/dec polymorphism (`5n--` → `4n`) is not expressible
                // purely (`+5n` throws) — no corpus fixture exercises it
                // (registered).
                out.push('(');
                out.push('+');
                // Same `++x` ambiguity rule as `ToNumber` above.
                if matches!(operand, Expr::Unary { .. }) {
                    out.push('(');
                    self.expr_inner(operand, out);
                    out.push(')');
                } else {
                    self.sub(operand, 17, out);
                }
                out.push_str(if matches!(op, UnOp::Inc) {
                    " + 1"
                } else {
                    " - 1"
                });
                out.push(')');
            }
        }
    }

    /// A literal with JS-valid MethodRef rendering.
    pub(in crate::emit) fn render_lit_js(&self, lit: &Lit) -> String {
        match lit {
            Lit::MethodRef(f) => format!("undefined /*method fn#{}*/", f.index()),
            Lit::Array(items) => {
                let inner: Vec<String> = items.iter().map(|i| self.render_lit_js(i)).collect();
                format!("[{}]", inner.join(", "))
            }
            Lit::Object(entries) => {
                let inner: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{}: {}",
                            render_lit_key_pub(self.module, k),
                            self.render_lit_js(v)
                        )
                    })
                    .collect();
                format!("{{{}}}", inner.join(", "))
            }
            other => render_lit_m(self.module, other),
        }
    }
}

pub(in crate::emit) fn iter_op_name(op: IterOp) -> &'static str {
    match op {
        IterOp::GetIterator => "GetIterator",
        IterOp::GetAsyncIterator => "GetAsyncIterator",
        IterOp::Next => "IteratorNext",
        IterOp::Return => "IteratorReturn",
        IterOp::Throw => "IteratorThrow",
        IterOp::GetPropIterator => "GetPropIterator",
        IterOp::NextPropName => "NextPropName",
    }
}

/// Object-literal key rendering (identifier form when legal).
pub(in crate::emit) fn render_lit_key_pub(module: &Module, lit: &Lit) -> String {
    if let Lit::String(s) = lit
        && is_legal_ident(s)
    {
        return s.clone();
    }
    render_lit_m(module, lit)
}

pub(in crate::emit) fn fmt_loc(loc: Option<Loc>) -> String {
    match loc {
        Some(l) => match l.column {
            Some(c) => format!(" @{}:{}", l.line, c),
            None => format!(" @{}", l.line),
        },
        None => String::new(),
    }
}

pub(in crate::emit) fn binop_sym(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Exp => "**",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>>",
        BinOp::Ashr => ">>",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
    }
}

pub(in crate::emit) fn cmpop_sym(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Eq => "==",
        CmpOp::NotEq => "!=",
        CmpOp::StrictEq => "===",
        CmpOp::StrictNotEq => "!==",
        CmpOp::Less => "<",
        CmpOp::LessEq => "<=",
        CmpOp::Greater => ">",
        CmpOp::GreaterEq => ">=",
        CmpOp::In => "in",
        CmpOp::InstanceOf => "instanceof",
    }
}
