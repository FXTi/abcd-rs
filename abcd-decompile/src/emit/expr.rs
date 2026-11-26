//! Precedence-exact expression, call, unary, and literal emission.

use super::decl::{closure_prefix, fn_uses_super, method_prefix};
use super::*;

impl<'m> Emitter<'m> {
    // ── Expressions (precedence-correct, iterative) ──────────────────

    /// Print an expression; parenthesize when its precedence is below `prec`.
    pub(in crate::emit) fn expr(&mut self, e: &Expr, prec: u8, out: &mut String) {
        self.run_print_tasks(PrintRoot::Expr(e, prec), out);
    }

    #[allow(
        clippy::too_many_lines,
        reason = "central expression pretty-printer dispatches across all Stage-A/B Expr variants"
    )]
    pub(in crate::emit) fn step_print_expr_inner<'b>(
        &mut self,
        e: &'b Expr,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        match e {
            Expr::Lit(lit) => out.push_str(&self.render_lit_js(lit)),
            Expr::Ident(name) => out.push_str(name),
            Expr::Temp { name, .. } => out.push_str(name),
            Expr::PropName {
                object,
                name,
                dot_legal,
            } => {
                let suffix = if *dot_legal {
                    format!(".{name}")
                } else {
                    format!("[{}]", render_pool_string(self.module, name))
                };
                tasks.push(PrintTask::RawOwned(suffix));
                tasks.push(PrintTask::Expr {
                    expr: object,
                    prec: 19,
                });
            }
            Expr::PropIndex { object, index } | Expr::PropDyn { object, key: index } => {
                tasks.push(PrintTask::Raw("]"));
                tasks.push(PrintTask::Expr {
                    expr: index,
                    prec: 0,
                });
                tasks.push(PrintTask::Raw("["));
                tasks.push(PrintTask::Expr {
                    expr: object,
                    prec: 19,
                });
            }
            Expr::PrivateLoad { object, name } => {
                if self.class_depth > 0 {
                    tasks.push(PrintTask::RawOwned(format!(".#{name}")));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 19,
                    });
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("LoadPrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    tasks.push(PrintTask::RawOwned(format!(
                        "[{}] /*private #{name} — out-of-class*/",
                        render_pool_string(self.module, name)
                    )));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 19,
                    });
                }
            }
            Expr::PrivateTest { object, name } => {
                if self.class_depth > 0 {
                    out.push_str(&format!("#{name} in "));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 12,
                    });
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("TestPrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    out.push_str(&format!("({} in ", render_pool_string(self.module, name)));
                    tasks.push(PrintTask::Raw(") /*private test — out-of-class*/"));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 0,
                    });
                }
            }
            Expr::SuperProp { name, key } => match (name, key) {
                (Some(n), None) => out.push_str(&format!("super.{n}")),
                (None, Some(k)) => {
                    out.push_str("super[");
                    tasks.push(PrintTask::Raw("]"));
                    tasks.push(PrintTask::Expr { expr: k, prec: 0 });
                }
                _ => out.push_str("super[?]"),
            },
            Expr::Call {
                callee,
                this,
                args,
                kind,
            } => self.step_print_call(callee, this.as_deref(), args, *kind, tasks, out),
            Expr::SuperMarker => out.push_str("super"),
            Expr::DynamicImport { specifier } => {
                out.push_str("import(");
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::Expr {
                    expr: specifier,
                    prec: 0,
                });
            }
            Expr::Unary { op, operand } => self.step_print_unary(*op, operand, tasks, out),
            Expr::Delete { target } => {
                out.push_str("delete ");
                tasks.push(PrintTask::Expr {
                    expr: target,
                    prec: 17,
                });
            }
            Expr::Binary { op, left, right } => {
                let prec = e.precedence();
                let left_prec = if *op == BinOp::Exp { 17 } else { prec };
                let right_prec = if *op == BinOp::Exp { prec } else { prec + 1 };
                let force_left_parens = *op == BinOp::Exp && is_emitted_unary_lhs(left);
                tasks.push(PrintTask::Expr {
                    expr: right,
                    prec: right_prec,
                });
                tasks.push(PrintTask::RawOwned(format!(" {} ", binop_sym(*op))));
                if force_left_parens {
                    tasks.push(PrintTask::Raw(")"));
                    tasks.push(PrintTask::ExprInner(left));
                    tasks.push(PrintTask::Raw("("));
                } else {
                    tasks.push(PrintTask::Expr {
                        expr: left,
                        prec: left_prec,
                    });
                }
            }
            Expr::Compare { op, left, right } => {
                let prec = e.precedence();
                tasks.push(PrintTask::Expr {
                    expr: right,
                    prec: prec + 1,
                });
                tasks.push(PrintTask::RawOwned(format!(" {} ", cmpop_sym(*op))));
                tasks.push(PrintTask::Expr { expr: left, prec });
            }
            Expr::RegExp { pattern, flags } => {
                let body = crate::consts::escape_regexp_body(pattern);
                out.push_str(&format!("/{body}/{flags}"));
            }
            Expr::ObjectLit { entries } => {
                out.push_str(&self.render_lit_js(&Lit::Object(entries.clone())));
            }
            Expr::ArrayLit { elements } => {
                out.push_str(&self.render_lit_js(&Lit::Array(elements.clone())));
            }
            Expr::ObjectBuild { entries } => {
                out.push('{');
                tasks.push(PrintTask::Raw("}"));
                if !entries.is_empty() {
                    tasks.push(PrintTask::ObjEntries {
                        slice: entries,
                        first: true,
                    });
                }
            }
            Expr::ArrayBuild { elements } => {
                out.push('[');
                tasks.push(PrintTask::Raw("]"));
                if !elements.is_empty() {
                    tasks.push(PrintTask::ArrElems {
                        slice: elements,
                        first: true,
                    });
                }
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
                tasks.push(PrintTask::EnterInlineFunc {
                    func: body,
                    indent: 1,
                    style: InlineHeaderStyle {
                        open_paren: false,
                        drop_ret_ty: false,
                        arrow,
                        closing: "}".to_string(),
                    },
                });
            }
            Expr::Class {
                ctor,
                name,
                heritage,
                members,
                member_attrs,
                sendable,
            } => {
                let start = out.len();
                tasks.push(PrintTask::TrimEndSince(start));
                self.step_start_class(
                    "",
                    0,
                    &sanitize(name),
                    *ctor,
                    heritage.as_deref(),
                    *members,
                    member_attrs,
                    *sendable,
                    tasks,
                    out,
                );
            }
            Expr::Yield { value } => {
                if matches!(
                    self.current_kind,
                    FunctionKind::Generator | FunctionKind::AsyncGenerator
                ) {
                    out.push_str("yield ");
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("SuspendGenerator(async-machinery)")
                        .or_insert(0) += 1;
                    out.push_str("/*async-machinery suspend (R4; not a source yield)*/ ");
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                }
            }
            Expr::YieldStar { value } => {
                out.push_str("yield* ");
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Expr::Await { value, .. } => {
                if matches!(
                    self.current_kind,
                    FunctionKind::Async | FunctionKind::AsyncArrow | FunctionKind::AsyncGenerator
                ) {
                    out.push_str("await ");
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 17,
                    });
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("Await(non-async context)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    out.push_str("/*await outside async context (operand kept)*/ ");
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
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
                tasks.push(PrintTask::Raw("`"));
                tasks.push(PrintTask::TaggedParts {
                    quasis,
                    exprs,
                    idx: 0,
                });
                tasks.push(PrintTask::Raw("`"));
                tasks.push(PrintTask::Expr {
                    expr: tag,
                    prec: 19,
                });
            }
            Expr::IterResultObj { value, done } => {
                out.push_str("{ value: ");
                tasks.push(PrintTask::Raw(" } /*iter-result*/"));
                tasks.push(PrintTask::Expr {
                    expr: done,
                    prec: 0,
                });
                tasks.push(PrintTask::Raw(", done: "));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Expr::Iter {
                op: IterOp::GetIterator,
                obj,
                ..
            } => {
                tasks.push(PrintTask::Raw("[Symbol.iterator]()"));
                tasks.push(PrintTask::Expr {
                    expr: obj,
                    prec: 19,
                });
            }
            Expr::Iter {
                op: IterOp::GetAsyncIterator,
                obj,
                ..
            } => {
                tasks.push(PrintTask::Raw(
                    "[Symbol.asyncIterator]() /*sync-fallback elided*/",
                ));
                tasks.push(PrintTask::Expr {
                    expr: obj,
                    prec: 19,
                });
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
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
            }
            Expr::CreateGenerator { func } => {
                out.push_str("/*CreateGenerator plumbing*/ ");
                tasks.push(PrintTask::Expr {
                    expr: func,
                    prec: 0,
                });
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
                tasks.push(PrintTask::Expr {
                    expr: genobj,
                    prec: 0,
                });
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
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Expr::AsyncGeneratorResolve { value, .. } => {
                *self
                    .stats
                    .fallback_comments
                    .entry("AsyncGeneratorResolve")
                    .or_insert(0) += 1;
                self.current_fn_has_fallback = true;
                out.push_str(
                    "/*hard-fallback AsyncGeneratorResolve (async-generator driver, R4)*/ ",
                );
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Expr::CopyDataProps { dst, src } => {
                out.push_str("Object.assign(");
                tasks.push(PrintTask::Raw(
                    ") /*CopyDataProps: approximate outside a literal*/",
                ));
                tasks.push(PrintTask::Expr { expr: src, prec: 0 });
                tasks.push(PrintTask::Raw(", "));
                tasks.push(PrintTask::Expr { expr: dst, prec: 0 });
            }
            Expr::SetObjectWithProto { obj, proto } => {
                out.push_str("Object.setPrototypeOf(");
                tasks.push(PrintTask::Raw(") /*NOT identical: no-setter semantics*/"));
                tasks.push(PrintTask::Expr {
                    expr: proto,
                    prec: 0,
                });
                tasks.push(PrintTask::Raw(", "));
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
            }
            Expr::ArraySpread { dst, src, .. } => {
                tasks.push(PrintTask::Raw(") /*ArraySpread: result=new-index*/"));
                tasks.push(PrintTask::Expr { expr: src, prec: 0 });
                tasks.push(PrintTask::Raw(".push(..."));
                tasks.push(PrintTask::Expr {
                    expr: dst,
                    prec: 19,
                });
            }
            Expr::RestObject { obj, .. } => {
                out.push_str("/*CreateObjectWithExcludedKeys plumbing*/ ");
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
            }
            Expr::DefineGetterSetter {
                obj,
                key,
                getter,
                setter,
            } => {
                let g = matches!(getter.as_ref(), Expr::Lit(Lit::Undefined));
                let s = matches!(setter.as_ref(), Expr::Lit(Lit::Undefined));
                out.push_str("Object.defineProperty(");
                tasks.push(PrintTask::Raw(
                    ", configurable: true }) /*DefineGetterSetterByValue: approximate*/",
                ));
                if !s {
                    tasks.push(PrintTask::Expr {
                        expr: setter,
                        prec: 0,
                    });
                    tasks.push(PrintTask::Raw(if !g { ", set: " } else { " set: " }));
                }
                if !g {
                    tasks.push(PrintTask::Expr {
                        expr: getter,
                        prec: 0,
                    });
                    tasks.push(PrintTask::Raw(" get: "));
                }
                tasks.push(PrintTask::Raw(", {"));
                tasks.push(PrintTask::Expr { expr: key, prec: 0 });
                tasks.push(PrintTask::Raw(", "));
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
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

    pub(in crate::emit) fn step_print_obj_entries<'b>(
        &mut self,
        slice: &'b [ObjEntry],
        first: bool,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        let Some((en, rest)) = slice.split_first() else {
            return;
        };
        if !first {
            out.push_str(", ");
        }
        if !rest.is_empty() {
            tasks.push(PrintTask::ObjEntries {
                slice: rest,
                first: false,
            });
        }
        match en {
            ObjEntry::KeyValue(k, v) => {
                out.push_str(&render_lit_key_pub(self.module, k));
                out.push_str(": ");
                tasks.push(PrintTask::Expr { expr: v, prec: 0 });
            }
            ObjEntry::Computed(k, v) => {
                out.push('[');
                tasks.push(PrintTask::Expr { expr: v, prec: 0 });
                tasks.push(PrintTask::Raw("]: "));
                tasks.push(PrintTask::Expr { expr: k, prec: 0 });
            }
            ObjEntry::Spread(x) => {
                out.push_str("...");
                tasks.push(PrintTask::Expr { expr: x, prec: 0 });
            }
            ObjEntry::Proto(x) => {
                out.push_str("__proto__: ");
                tasks.push(PrintTask::Expr { expr: x, prec: 0 });
            }
            ObjEntry::Method(n, f) => {
                let concise = match f {
                    Expr::Closure { body, kind, .. } => {
                        matches!(kind, FunctionKind::Generator | FunctionKind::AsyncGenerator)
                            || fn_uses_super(self.module, *body)
                    }
                    _ => false,
                };
                if concise {
                    let Expr::Closure { body, kind, .. } = f else {
                        unreachable!()
                    };
                    out.push_str(method_prefix(*kind));
                    if is_legal_ident(n) {
                        out.push_str(n);
                    } else {
                        out.push_str(&render_pool_string(self.module, n));
                    }
                    tasks.push(PrintTask::EnterInlineFunc {
                        func: *body,
                        indent: 1,
                        style: InlineHeaderStyle {
                            open_paren: true,
                            drop_ret_ty: false,
                            arrow: false,
                            closing: "}".to_string(),
                        },
                    });
                } else {
                    if is_legal_ident(n) {
                        out.push_str(n);
                    } else {
                        out.push_str(&render_pool_string(self.module, n));
                    }
                    out.push_str(": ");
                    tasks.push(PrintTask::Expr { expr: f, prec: 0 });
                }
            }
            ObjEntry::Getter(k, f) => {
                if let Expr::Closure { body, .. } = f {
                    self.push_concise_accessor("get ", k, *body, tasks, out);
                } else {
                    out.push_str("/* getter: non-closure (data shape) */");
                }
            }
            ObjEntry::Setter(k, f) => {
                if let Expr::Closure { body, .. } = f {
                    self.push_concise_accessor("set ", k, *body, tasks, out);
                } else {
                    out.push_str("/* setter: non-closure (data shape) */");
                }
            }
        }
    }

    fn push_concise_accessor<'b>(
        &self,
        prefix: &str,
        key: &'b crate::expr::ObjKey,
        body: FuncId,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        out.push_str(prefix);
        let inline_task = PrintTask::EnterInlineFunc {
            func: body,
            indent: 1,
            style: InlineHeaderStyle {
                open_paren: true,
                drop_ret_ty: false,
                arrow: false,
                closing: "}".to_string(),
            },
        };
        match key {
            crate::expr::ObjKey::Name(n) => {
                if is_legal_ident(n) {
                    out.push_str(n);
                } else {
                    out.push_str(&render_pool_string(self.module, n));
                }
                tasks.push(inline_task);
            }
            crate::expr::ObjKey::Computed(e) => {
                out.push('[');
                tasks.push(inline_task);
                tasks.push(PrintTask::Raw("]"));
                tasks.push(PrintTask::Expr { expr: e, prec: 0 });
            }
        }
    }

    fn step_print_call<'b>(
        &self,
        callee: &'b Expr,
        this: Option<&'b Expr>,
        args: &'b [Expr],
        kind: CallKind,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        match kind {
            CallKind::Direct | CallKind::Dynamic => {
                if let Some(t) = this {
                    match callee {
                        Expr::PropName {
                            object,
                            name,
                            dot_legal: true,
                        } if object.as_ref() == t => {
                            tasks.push(PrintTask::Raw(")"));
                            tasks.push(PrintTask::CallArgs {
                                args,
                                idx: 0,
                                leading_comma: false,
                            });
                            tasks.push(PrintTask::RawOwned(format!(".{name}(")));
                            tasks.push(PrintTask::Expr { expr: t, prec: 19 });
                        }
                        Expr::PropIndex { object, index: k } | Expr::PropDyn { object, key: k }
                            if object.as_ref() == t =>
                        {
                            tasks.push(PrintTask::Raw(")"));
                            tasks.push(PrintTask::CallArgs {
                                args,
                                idx: 0,
                                leading_comma: false,
                            });
                            tasks.push(PrintTask::Raw("]("));
                            tasks.push(PrintTask::Expr { expr: k, prec: 0 });
                            tasks.push(PrintTask::Raw("["));
                            tasks.push(PrintTask::Expr { expr: t, prec: 19 });
                        }
                        _ => {
                            tasks.push(PrintTask::Raw(")"));
                            tasks.push(PrintTask::CallArgs {
                                args,
                                idx: 0,
                                leading_comma: true,
                            });
                            tasks.push(PrintTask::Expr { expr: t, prec: 0 });
                            tasks.push(PrintTask::Raw(".call("));
                            tasks.push(PrintTask::Expr {
                                expr: callee,
                                prec: 19,
                            });
                        }
                    }
                } else {
                    tasks.push(PrintTask::Raw(")"));
                    tasks.push(PrintTask::CallArgs {
                        args,
                        idx: 0,
                        leading_comma: false,
                    });
                    tasks.push(PrintTask::Raw("("));
                    tasks.push(PrintTask::Expr {
                        expr: callee,
                        prec: 19,
                    });
                }
            }
            CallKind::New => {
                out.push_str("new ");
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: false,
                });
                tasks.push(PrintTask::Raw("("));
                tasks.push(PrintTask::Expr {
                    expr: callee,
                    prec: 19,
                });
            }
            CallKind::NewSpread => {
                out.push_str("new ");
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: false,
                });
                tasks.push(PrintTask::Raw("(..."));
                tasks.push(PrintTask::Expr {
                    expr: callee,
                    prec: 19,
                });
            }
            CallKind::Apply => {
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: true,
                });
                match this {
                    Some(t) => tasks.push(PrintTask::Expr { expr: t, prec: 0 }),
                    None => tasks.push(PrintTask::Raw("undefined")),
                }
                tasks.push(PrintTask::Raw(".apply("));
                tasks.push(PrintTask::Expr {
                    expr: callee,
                    prec: 19,
                });
            }
            CallKind::ClassInit => {
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: true,
                });
                match this {
                    Some(t) => tasks.push(PrintTask::Expr { expr: t, prec: 0 }),
                    None => tasks.push(PrintTask::Raw("this")),
                }
                tasks.push(PrintTask::Raw(".call("));
                tasks.push(PrintTask::Expr {
                    expr: callee,
                    prec: 19,
                });
            }
            CallKind::Super | CallKind::SuperArrow => {
                out.push_str("super(");
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: false,
                });
            }
            CallKind::SuperSpread => {
                out.push_str("super(...");
                tasks.push(PrintTask::Raw(")"));
                tasks.push(PrintTask::CallArgs {
                    args,
                    idx: 0,
                    leading_comma: false,
                });
            }
            CallKind::SuperForwardAllArgs => {
                out.push_str(
                    "super(...arguments) /*forward-all: default derived ctor elision pending*/",
                );
            }
        }
    }

    fn step_print_unary<'b>(
        &self,
        op: UnOp,
        operand: &'b Expr,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        match op {
            UnOp::IsTrue | UnOp::JumpNez => {
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 0,
                });
            }
            UnOp::IsFalse | UnOp::JumpEqz | UnOp::LogicalNot => {
                out.push('!');
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 17,
                });
            }
            UnOp::TypeOf => {
                out.push_str("typeof ");
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 17,
                });
            }
            UnOp::Void => {
                out.push_str("void ");
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 17,
                });
            }
            UnOp::BitNot => {
                out.push('~');
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 17,
                });
            }
            UnOp::ToNumber => {
                out.push('+');
                if needs_unary_pm_parens(operand) {
                    out.push('(');
                    tasks.push(PrintTask::Raw(")"));
                    tasks.push(PrintTask::ExprInner(operand));
                } else {
                    tasks.push(PrintTask::Expr {
                        expr: operand,
                        prec: 17,
                    });
                }
            }
            UnOp::ToNumeric => {
                if matches!(operand, Expr::Lit(Lit::BigInt(_))) {
                    tasks.push(PrintTask::Expr {
                        expr: operand,
                        prec: 17,
                    });
                } else {
                    out.push('+');
                    tasks.push(PrintTask::Raw(" /*ToNumeric*/"));
                    if needs_unary_pm_parens(operand) {
                        out.push('(');
                        tasks.push(PrintTask::Raw(")"));
                        tasks.push(PrintTask::ExprInner(operand));
                    } else {
                        tasks.push(PrintTask::Expr {
                            expr: operand,
                            prec: 17,
                        });
                    }
                }
            }
            UnOp::ToPropertyKey => {
                out.push_str("Reflect.ownKeys({ [");
                tasks.push(PrintTask::Raw("]: 0 })[0]"));
                tasks.push(PrintTask::Expr {
                    expr: operand,
                    prec: 0,
                });
            }
            UnOp::Minus => {
                out.push('-');
                if needs_unary_pm_parens(operand) {
                    out.push('(');
                    tasks.push(PrintTask::Raw(")"));
                    tasks.push(PrintTask::ExprInner(operand));
                } else {
                    tasks.push(PrintTask::Expr {
                        expr: operand,
                        prec: 17,
                    });
                }
            }
            UnOp::Inc | UnOp::Dec => {
                if matches!(operand, Expr::Lit(Lit::BigInt(_))) {
                    out.push('(');
                    tasks.push(PrintTask::Raw(if matches!(op, UnOp::Inc) {
                        " + 1n)"
                    } else {
                        " - 1n)"
                    }));
                    tasks.push(PrintTask::Expr {
                        expr: operand,
                        prec: 14,
                    });
                } else {
                    out.push_str("(+");
                    tasks.push(PrintTask::Raw(if matches!(op, UnOp::Inc) {
                        " + 1)"
                    } else {
                        " - 1)"
                    }));
                    if needs_unary_pm_parens(operand) {
                        out.push('(');
                        tasks.push(PrintTask::Raw(")"));
                        tasks.push(PrintTask::ExprInner(operand));
                    } else {
                        tasks.push(PrintTask::Expr {
                            expr: operand,
                            prec: 17,
                        });
                    }
                }
            }
        }
    }

    /// A literal with JS-valid MethodRef rendering.
    pub(crate) fn render_lit_js(&self, lit: &Lit) -> String {
        crate::consts::render_lit_ex(lit, true)
    }
}

fn peel_truthiness(mut e: &Expr) -> &Expr {
    while let Expr::Unary {
        op: UnOp::IsTrue | UnOp::JumpNez,
        operand,
    } = e
    {
        e = operand;
    }
    e
}

fn is_emitted_unary_lhs(e: &Expr) -> bool {
    let cur = peel_truthiness(e);
    match cur {
        Expr::Unary {
            op: UnOp::Inc | UnOp::Dec | UnOp::ToPropertyKey,
            ..
        } => false,
        Expr::Unary {
            op: UnOp::ToNumeric,
            operand,
        } if matches!(operand.as_ref(), Expr::Lit(Lit::BigInt(s)) if !s.starts_with('-')) => false,
        Expr::Unary { .. } | Expr::Delete { .. } | Expr::Await { .. } => true,
        _ => cur.is_negative_numeric_lit(),
    }
}

fn needs_unary_pm_parens(e: &Expr) -> bool {
    is_emitted_unary_lhs(e)
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

/// Object-literal key rendering (identifier form when legal; `"__proto__"`,
/// negative numeric literals, and BigInt keys render in computed `[...]` form).
pub(in crate::emit) fn render_lit_key_pub(module: &Module, lit: &Lit) -> String {
    let _ = module;
    if let Lit::String(s) = lit {
        if s == "__proto__" {
            return format!("[{}]", crate::consts::render_string(s));
        }
        if is_legal_ident(s) {
            return s.clone();
        }
    }
    let rendered = crate::consts::render_lit_ex(lit, true);
    if rendered.starts_with('-') || rendered.ends_with('n') {
        format!("[{rendered}]")
    } else {
        rendered
    }
}

pub(in crate::emit) fn fmt_loc(loc: Option<Loc>) -> String {
    match loc {
        Some(l) if l.line != u32::MAX => match l.column {
            Some(c) => format!(" @{}:{}", l.line, c),
            None => format!(" @{}", l.line),
        },
        _ => String::new(),
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
