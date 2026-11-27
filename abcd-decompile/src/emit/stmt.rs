//! Iterative `PrintTask` statement, control-flow, and hoisting emission.

use super::*;

pub(in crate::emit) enum PrintRoot<'a> {
    Nodes(&'a [SNode], usize),
    Node(&'a SNode, usize),
    Leaf(&'a Leaf, usize),
    Stmt(&'a Stmt, usize),
    Expr(&'a Expr, u8),
    ClassMethod {
        pad: &'a str,
        indent: usize,
        name: &'a str,
        func: FuncId,
        attrs: Option<&'a abcd_ir::op::MemberAttrs>,
    },
}

#[derive(Clone)]
pub(in crate::emit) struct InlineHeaderStyle {
    pub(in crate::emit) open_paren: bool,
    pub(in crate::emit) drop_ret_ty: bool,
    pub(in crate::emit) arrow: bool,
    pub(in crate::emit) closing: String,
}

pub(in crate::emit) enum PrintTask<'b> {
    Raw(&'static str),
    RawOwned(String),
    TrimEndSince(usize),
    Nodes {
        slice: &'b [SNode],
        indent: usize,
    },
    Node {
        node: &'b SNode,
        indent: usize,
    },
    Leaves {
        slice: &'b [Leaf],
        indent: usize,
    },
    Leaf {
        leaf: &'b Leaf,
        indent: usize,
    },
    Stmt {
        stmt: &'b Stmt,
        indent: usize,
    },
    SwitchCases {
        cases: &'b [crate::structure::SwitchCase],
        indent: usize,
    },
    SwitchCaseTests {
        tests: &'b [Expr],
        body: &'b [SNode],
        indent: usize,
    },
    ExtraCatches {
        catches: &'b [crate::structure::CatchClause],
        primary_binding: String,
        indent: usize,
    },
    Expr {
        expr: &'b Expr,
        prec: u8,
    },
    ExprInner(&'b Expr),
    ObjEntries {
        slice: &'b [ObjEntry],
        first: bool,
    },
    ArrElems {
        slice: &'b [ArrayElem],
        first: bool,
    },
    TaggedParts {
        quasis: &'b [String],
        exprs: &'b [Expr],
        idx: usize,
    },
    CallArgs {
        args: &'b [Expr],
        idx: usize,
        leading_comma: bool,
    },
    EnterInlineFunc {
        func: FuncId,
        indent: usize,
        style: InlineHeaderStyle,
    },
    ExitInlineFunc {
        func: FuncId,
        prev_kind: FunctionKind,
        prev_hoisted: BTreeSet<String>,
        closing: String,
    },
    StartClassBody {
        pad: String,
        indent: usize,
        ctor: FuncId,
        members: abcd_ir::ConstId,
        member_attrs: &'b [abcd_ir::op::MemberAttrs],
    },
    ClassMethods {
        pad: String,
        indent: usize,
        methods: std::vec::IntoIter<(String, FuncId, Option<&'b abcd_ir::op::MemberAttrs>)>,
        skipped: usize,
    },
    EmitClassMethod {
        pad: String,
        indent: usize,
        name: String,
        func: FuncId,
        attrs: Option<&'b abcd_ir::op::MemberAttrs>,
    },
    CloseClass {
        pad: String,
    },
}

fn scan_expr_inline_funcs(
    method_refs: &crate::consts::ConstMethodRefCache,
    root: &Expr,
    out: &mut Vec<FuncId>,
) {
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Closure { body, .. } => out.push(*body),
            Expr::Class { ctor, members, .. } => {
                out.push(*ctor);
                out.extend_from_slice(method_refs.get(*members));
            }
            _ => {}
        }
        stack.extend(crate::folds::expr_children(cur));
    }
}

fn scan_stmt_inline_funcs(
    method_refs: &crate::consts::ConstMethodRefCache,
    stmt: &Stmt,
    out: &mut Vec<FuncId>,
) {
    for e in stmt_exprs(stmt) {
        scan_expr_inline_funcs(method_refs, e, out);
    }
}

fn scan_leaf_inline_funcs(
    method_refs: &crate::consts::ConstMethodRefCache,
    leaf: &Leaf,
    out: &mut Vec<FuncId>,
) {
    match leaf {
        Leaf::Raw(s) => scan_stmt_inline_funcs(method_refs, s, out),
        Leaf::Destructure { obj, .. } => scan_expr_inline_funcs(method_refs, obj, out),
        Leaf::Decl { value: Some(v), .. } | Leaf::Assign { value: v, .. } => {
            scan_expr_inline_funcs(method_refs, v, out);
        }
        Leaf::Decl { value: None, .. } => {}
    }
}

fn scan_nodes_inline_funcs(
    method_refs: &crate::consts::ConstMethodRefCache,
    nodes: &[SNode],
    out: &mut Vec<FuncId>,
) {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(seq) = stack.pop() {
        for n in seq {
            match n {
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        scan_leaf_inline_funcs(method_refs, l, out);
                    }
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    scan_expr_inline_funcs(method_refs, cond, out);
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        scan_expr_inline_funcs(method_refs, c, out);
                    }
                    stack.push(body);
                }
                SNode::DoWhile { body, cond, .. } => {
                    scan_expr_inline_funcs(method_refs, cond, out);
                    stack.push(body);
                }
                SNode::Block(body) | SNode::Labeled { body, .. } => stack.push(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(f) = finally {
                        stack.push(f);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::ForOf { iter, body, .. } => {
                    scan_expr_inline_funcs(method_refs, iter, out);
                    stack.push(body);
                }
                SNode::ForIn { obj, body, .. } => {
                    scan_expr_inline_funcs(method_refs, obj, out);
                    stack.push(body);
                }
                SNode::Switch { disc, cases } => {
                    scan_expr_inline_funcs(method_refs, disc, out);
                    for c in cases.iter().rev() {
                        for t in &c.tests {
                            scan_expr_inline_funcs(method_refs, t, out);
                        }
                        stack.push(&c.body);
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
}

fn collect_negated_ifs_in_nodes(
    nodes: &[SNode],
    out: &mut std::collections::HashMap<*const SNode, Expr>,
) {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(seq) = stack.pop() {
        for n in seq {
            match n {
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    if then.is_empty() && !otherwise.is_empty() {
                        out.insert(std::ptr::from_ref(n), crate::structure::negate(cond));
                    }
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::Block(body)
                | SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => stack.push(body),
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(f) = finally {
                        stack.push(f);
                    }
                    for c in catches.iter().rev() {
                        stack.push(&c.body);
                    }
                    stack.push(body);
                }
                SNode::Switch { cases, .. } => {
                    for c in cases.iter().rev() {
                        stack.push(&c.body);
                    }
                }
                SNode::Stmts(_)
                | SNode::Break { .. }
                | SNode::Continue { .. }
                | SNode::Honest(_) => {}
            }
        }
    }
}

impl<'m> Emitter<'m> {
    // ── Statements & Iterative Printer Driver ────────────────────────

    fn take_or_prepare_inline(&mut self, func: FuncId) -> PreparedFunc {
        if self.opts.arkui {
            return self.peek_prepared(func, false).into_owned();
        }
        match self.prepared.remove(&func) {
            Some(pre) if !pre.top_level => pre,
            Some(other) => {
                self.prepared.insert(func, other);
                prepare_func_only(self.module, self.index, func, false)
            }
            None => prepare_func_only(self.module, self.index, func, false),
        }
    }

    pub(in crate::emit) fn run_print_tasks(&mut self, root: PrintRoot<'_>, out: &mut String) {
        let owned_cache;
        let method_refs = match self.index {
            Some(idx) => &idx.const_method_refs,
            None => {
                owned_cache = crate::consts::ConstMethodRefCache::build(self.module);
                &owned_cache
            }
        };
        let mut queue: Vec<FuncId> = Vec::new();
        match &root {
            PrintRoot::Nodes(s, _) => scan_nodes_inline_funcs(method_refs, s, &mut queue),
            PrintRoot::Node(n, _) => {
                scan_nodes_inline_funcs(method_refs, std::slice::from_ref(*n), &mut queue);
            }
            PrintRoot::Leaf(l, _) => scan_leaf_inline_funcs(method_refs, l, &mut queue),
            PrintRoot::Stmt(s, _) => scan_stmt_inline_funcs(method_refs, s, &mut queue),
            PrintRoot::Expr(e, _) => scan_expr_inline_funcs(method_refs, e, &mut queue),
            PrintRoot::ClassMethod { func, .. } => queue.push(*func),
        }

        let mut inline_pool: BTreeMap<FuncId, PreparedFunc> = BTreeMap::new();
        while let Some(fid) = queue.pop() {
            if self.emitting_funcs.contains(&fid) || inline_pool.contains_key(&fid) {
                continue;
            }
            let pre = self.take_or_prepare_inline(fid);
            scan_nodes_inline_funcs(method_refs, &pre.body, &mut queue);
            inline_pool.insert(fid, pre);
        }

        let mut negated_ifs: std::collections::HashMap<*const SNode, Expr> =
            std::collections::HashMap::new();
        match &root {
            PrintRoot::Nodes(s, _) => collect_negated_ifs_in_nodes(s, &mut negated_ifs),
            PrintRoot::Node(n, _) => {
                collect_negated_ifs_in_nodes(std::slice::from_ref(*n), &mut negated_ifs);
            }
            _ => {}
        }
        for pre in inline_pool.values() {
            collect_negated_ifs_in_nodes(&pre.body, &mut negated_ifs);
        }

        let mut tasks: Vec<PrintTask<'_>> = Vec::new();
        match root {
            PrintRoot::Nodes(slice, indent) => tasks.push(PrintTask::Nodes { slice, indent }),
            PrintRoot::Node(node, indent) => tasks.push(PrintTask::Node { node, indent }),
            PrintRoot::Leaf(leaf, indent) => tasks.push(PrintTask::Leaf { leaf, indent }),
            PrintRoot::Stmt(stmt, indent) => tasks.push(PrintTask::Stmt { stmt, indent }),
            PrintRoot::Expr(expr, prec) => tasks.push(PrintTask::Expr { expr, prec }),
            PrintRoot::ClassMethod {
                pad,
                indent,
                name,
                func,
                attrs,
            } => tasks.push(PrintTask::EmitClassMethod {
                pad: pad.to_string(),
                indent,
                name: name.to_string(),
                func,
                attrs,
            }),
        }

        while let Some(task) = tasks.pop() {
            match task {
                PrintTask::Raw(s) => out.push_str(s),
                PrintTask::RawOwned(s) => out.push_str(&s),
                PrintTask::TrimEndSince(start) => {
                    if start <= out.len() {
                        let trimmed = out[start..].trim_end().len();
                        out.truncate(start + trimmed);
                    }
                }
                PrintTask::Nodes { slice, indent } => {
                    if let Some((first, rest)) = slice.split_first() {
                        if !rest.is_empty() {
                            tasks.push(PrintTask::Nodes {
                                slice: rest,
                                indent,
                            });
                        }
                        tasks.push(PrintTask::Node {
                            node: first,
                            indent,
                        });
                    }
                }
                PrintTask::Node { node, indent } => {
                    self.step_print_node(node, indent, &negated_ifs, &mut tasks, out);
                }
                PrintTask::Leaves { slice, indent } => {
                    if let Some((first, rest)) = slice.split_first() {
                        if !rest.is_empty() {
                            tasks.push(PrintTask::Leaves {
                                slice: rest,
                                indent,
                            });
                        }
                        tasks.push(PrintTask::Leaf {
                            leaf: first,
                            indent,
                        });
                    }
                }
                PrintTask::Leaf { leaf, indent } => {
                    self.step_print_leaf(leaf, indent, &mut tasks, out);
                }
                PrintTask::Stmt { stmt, indent } => {
                    self.step_print_stmt(stmt, indent, &mut tasks, out);
                }
                PrintTask::SwitchCases { cases, indent } => {
                    if let Some((case, rest)) = cases.split_first() {
                        if !rest.is_empty() {
                            tasks.push(PrintTask::SwitchCases {
                                cases: rest,
                                indent,
                            });
                        }
                        let pad = "  ".repeat(indent);
                        if case.tests.is_empty() {
                            out.push_str(&format!("{pad}default: {{\n"));
                            tasks.push(PrintTask::RawOwned(format!("{pad}  }}\n")));
                            tasks.push(PrintTask::Nodes {
                                slice: &case.body,
                                indent: indent + 2,
                            });
                        } else {
                            tasks.push(PrintTask::SwitchCaseTests {
                                tests: &case.tests,
                                body: &case.body,
                                indent,
                            });
                        }
                    }
                }
                PrintTask::SwitchCaseTests {
                    tests,
                    body,
                    indent,
                } => {
                    let pad = "  ".repeat(indent);
                    if let Some((first_test, rest_tests)) = tests.split_first() {
                        if rest_tests.is_empty() {
                            tasks.push(PrintTask::RawOwned(format!("{pad}  }}\n")));
                            tasks.push(PrintTask::Nodes {
                                slice: body,
                                indent: indent + 2,
                            });
                        } else {
                            tasks.push(PrintTask::SwitchCaseTests {
                                tests: rest_tests,
                                body,
                                indent,
                            });
                        }
                        out.push_str(&format!("{pad}case "));
                        tasks.push(PrintTask::Raw(": {\n"));
                        tasks.push(PrintTask::Expr {
                            expr: first_test,
                            prec: 0,
                        });
                    }
                }
                PrintTask::ExtraCatches {
                    catches,
                    primary_binding,
                    indent,
                } => {
                    if let Some((extra, rest)) = catches.split_first() {
                        if !rest.is_empty() {
                            tasks.push(PrintTask::ExtraCatches {
                                catches: rest,
                                primary_binding: primary_binding.clone(),
                                indent,
                            });
                        }
                        let pad = "  ".repeat(indent);
                        out.push_str(&format!(
                            "{pad}  /* additional typed-catch handler (no JS surface) — body merged: */\n"
                        ));
                        if let Some(b) = &extra.binding
                            && *b != primary_binding
                        {
                            if self.hoisted.contains(b) {
                                out.push_str(&format!(
                                    "{pad}  {b} = {primary_binding}; /* merged typed-catch binding */\n"
                                ));
                            } else {
                                out.push_str(&format!(
                                    "{pad}  const {b} = {primary_binding}; /* merged typed-catch binding */\n"
                                ));
                            }
                        }
                        tasks.push(PrintTask::Nodes {
                            slice: &extra.body,
                            indent: indent + 1,
                        });
                    }
                }
                PrintTask::Expr { expr, prec } => {
                    if expr.precedence() < prec {
                        out.push('(');
                        tasks.push(PrintTask::Raw(")"));
                        tasks.push(PrintTask::ExprInner(expr));
                    } else {
                        tasks.push(PrintTask::ExprInner(expr));
                    }
                }
                PrintTask::ExprInner(expr) => {
                    self.step_print_expr_inner(expr, &mut tasks, out);
                }
                PrintTask::ObjEntries { slice, first } => {
                    self.step_print_obj_entries(slice, first, &mut tasks, out);
                }
                PrintTask::ArrElems { slice, first } => {
                    if let Some((el, rest)) = slice.split_first() {
                        if !first {
                            out.push_str(", ");
                        }
                        if !rest.is_empty() {
                            tasks.push(PrintTask::ArrElems {
                                slice: rest,
                                first: false,
                            });
                        }
                        match el {
                            ArrayElem::Item(x) => tasks.push(PrintTask::Expr { expr: x, prec: 0 }),
                            ArrayElem::Spread(x) => {
                                out.push_str("...");
                                tasks.push(PrintTask::Expr { expr: x, prec: 0 });
                            }
                        }
                    }
                }
                PrintTask::TaggedParts { quasis, exprs, idx } => {
                    if let Some(q) = quasis.get(idx) {
                        out.push_str(q);
                        if idx + 1 < quasis.len() {
                            tasks.push(PrintTask::TaggedParts {
                                quasis,
                                exprs,
                                idx: idx + 1,
                            });
                        }
                        if let Some(arg) = exprs.get(idx) {
                            out.push_str("${");
                            tasks.push(PrintTask::Raw("}"));
                            tasks.push(PrintTask::Expr { expr: arg, prec: 0 });
                        }
                    }
                }
                PrintTask::CallArgs {
                    args,
                    idx,
                    leading_comma,
                } => {
                    if let Some(arg) = args.get(idx) {
                        if leading_comma || idx > 0 {
                            out.push_str(", ");
                        }
                        if idx + 1 < args.len() {
                            tasks.push(PrintTask::CallArgs {
                                args,
                                idx: idx + 1,
                                leading_comma,
                            });
                        }
                        tasks.push(PrintTask::Expr { expr: arg, prec: 0 });
                    }
                }
                PrintTask::EnterInlineFunc {
                    func,
                    indent,
                    style,
                } => {
                    self.step_enter_inline_func(func, indent, style, &inline_pool, &mut tasks, out);
                }
                PrintTask::ExitInlineFunc {
                    func,
                    prev_kind,
                    prev_hoisted,
                    closing,
                } => {
                    self.emitting_funcs.remove(&func);
                    self.current_kind = prev_kind;
                    self.hoisted = prev_hoisted;
                    out.push_str(&closing);
                }
                PrintTask::StartClassBody {
                    pad,
                    indent,
                    ctor,
                    members,
                    member_attrs,
                } => {
                    self.step_start_class_body(
                        pad,
                        indent,
                        ctor,
                        members,
                        member_attrs,
                        &mut tasks,
                        out,
                    );
                }
                PrintTask::ClassMethods {
                    pad,
                    indent,
                    mut methods,
                    skipped,
                } => {
                    if let Some((mname, f, attrs)) = methods.next() {
                        tasks.push(PrintTask::ClassMethods {
                            pad: pad.clone(),
                            indent,
                            methods,
                            skipped,
                        });
                        tasks.push(PrintTask::EmitClassMethod {
                            pad,
                            indent,
                            name: mname,
                            func: f,
                            attrs,
                        });
                    } else if skipped > 0 {
                        out.push_str(&format!(
                            "{pad}  /* {skipped} member-buffer metadata entries skipped (name/method pairs consumed; numeric payloads are runtime metadata) */\n"
                        ));
                    }
                }
                PrintTask::EmitClassMethod {
                    pad,
                    indent,
                    name,
                    func,
                    attrs,
                } => {
                    self.step_emit_class_method(&pad, indent, &name, func, attrs, &mut tasks, out);
                }
                PrintTask::CloseClass { pad } => {
                    self.class_depth -= 1;
                    out.push_str(&format!("{pad}}}\n"));
                }
            }
        }
    }

    pub(in crate::emit) fn emit_nodes(&mut self, nodes: &[SNode], indent: usize, out: &mut String) {
        self.run_print_tasks(PrintRoot::Nodes(nodes, indent), out);
    }

    pub(crate) fn emit_node(&mut self, n: &SNode, indent: usize, out: &mut String) {
        self.run_print_tasks(PrintRoot::Node(n, indent), out);
    }

    pub(crate) fn emit_leaf(&mut self, l: &Leaf, indent: usize, out: &mut String) {
        self.run_print_tasks(PrintRoot::Leaf(l, indent), out);
    }

    pub(crate) fn emit_stmt(&mut self, s: &Stmt, indent: usize, out: &mut String) {
        self.run_print_tasks(PrintRoot::Stmt(s, indent), out);
    }

    /// An expression printed at statement (precedence-0) context.
    pub(crate) fn estr(&mut self, e: &Expr) -> String {
        let mut s = String::new();
        self.expr(e, 0, &mut s);
        s
    }

    fn step_print_node<'b>(
        &mut self,
        n: &'b SNode,
        indent: usize,
        negated_ifs: &'b std::collections::HashMap<*const SNode, Expr>,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        let pad = "  ".repeat(indent);
        match n {
            SNode::Stmts(leaves) => {
                tasks.push(PrintTask::Leaves {
                    slice: leaves,
                    indent,
                });
            }
            SNode::Block(body) => {
                out.push_str(&format!("{pad}{{\n"));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                let (cond_ref, then_arm, else_arm) = if then.is_empty() && !otherwise.is_empty() {
                    let neg = negated_ifs.get(&std::ptr::from_ref(n)).unwrap_or(cond);
                    (expr::peel_truthiness(neg), otherwise, then)
                } else {
                    (expr::peel_truthiness(cond), then, otherwise)
                };
                out.push_str(&format!("{pad}if ("));
                if else_arm.is_empty() {
                    tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                    tasks.push(PrintTask::Nodes {
                        slice: then_arm,
                        indent: indent + 1,
                    });
                    tasks.push(PrintTask::Raw(") {\n"));
                    tasks.push(PrintTask::Expr {
                        expr: cond_ref,
                        prec: 0,
                    });
                } else {
                    tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                    tasks.push(PrintTask::Nodes {
                        slice: else_arm,
                        indent: indent + 1,
                    });
                    tasks.push(PrintTask::RawOwned(format!("{pad}}} else {{\n")));
                    tasks.push(PrintTask::Nodes {
                        slice: then_arm,
                        indent: indent + 1,
                    });
                    tasks.push(PrintTask::Raw(") {\n"));
                    tasks.push(PrintTask::Expr {
                        expr: cond_ref,
                        prec: 0,
                    });
                }
            }
            SNode::While { label, cond, body } => {
                let lbl = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                out.push_str(&format!("{pad}{lbl}while ("));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
                tasks.push(PrintTask::Raw(") {\n"));
                match cond {
                    Some(c) => tasks.push(PrintTask::Expr {
                        expr: expr::peel_truthiness(c),
                        prec: 0,
                    }),
                    None => tasks.push(PrintTask::Raw("true")),
                }
            }
            SNode::DoWhile { label, body, cond } => {
                let lbl = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                out.push_str(&format!("{pad}{lbl}do {{\n"));
                tasks.push(PrintTask::Raw(");\n"));
                tasks.push(PrintTask::Expr {
                    expr: expr::peel_truthiness(cond),
                    prec: 0,
                });
                tasks.push(PrintTask::RawOwned(format!("{pad}}} while (")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
            }
            SNode::Break { label } => {
                let l = label.as_ref().map(|l| format!(" {l}")).unwrap_or_default();
                out.push_str(&format!("{pad}break{l};\n"));
            }
            SNode::Continue { label } => {
                let l = label.as_ref().map(|l| format!(" {l}")).unwrap_or_default();
                out.push_str(&format!("{pad}continue{l};\n"));
            }
            SNode::Labeled { label, body } => {
                out.push_str(&format!("{pad}{label}: {{\n"));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
            }
            SNode::Try {
                body,
                catches,
                note,
                finally,
            } => {
                if let Some(note) = note {
                    out.push_str(&format!("{pad}/* {note} */\n"));
                }
                out.push_str(&format!("{pad}try {{\n"));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                if let Some(fbody) = finally {
                    tasks.push(PrintTask::Nodes {
                        slice: fbody,
                        indent: indent + 1,
                    });
                    tasks.push(PrintTask::RawOwned(format!("{pad}}} finally {{\n")));
                }
                match catches.split_first() {
                    Some((first, rest)) => {
                        let binding = first.binding.clone().unwrap_or_else(|| "e".to_string());
                        let catch_param = if self.hoisted.contains(&binding) {
                            format!("{binding}$catch")
                        } else {
                            binding.clone()
                        };
                        if !rest.is_empty() {
                            tasks.push(PrintTask::ExtraCatches {
                                catches: rest,
                                primary_binding: catch_param.clone(),
                                indent,
                            });
                        }
                        tasks.push(PrintTask::Nodes {
                            slice: &first.body,
                            indent: indent + 1,
                        });
                        if self.hoisted.contains(&binding) {
                            tasks.push(PrintTask::RawOwned(format!(
                                "{pad}}} catch ({catch_param}) {{\n{pad}  {binding} = {catch_param};\n"
                            )));
                        } else {
                            tasks.push(PrintTask::RawOwned(format!(
                                "{pad}}} catch ({binding}) {{\n"
                            )));
                        }
                    }
                    None => {
                        if finally.is_none() {
                            tasks.push(PrintTask::RawOwned(format!(
                                "{pad}}} catch (e) {{\n{pad}  /* handler body unavailable */\n"
                            )));
                        }
                    }
                }
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
            }
            SNode::ForOf {
                is_await,
                binding,
                iter,
                body,
            } => {
                let kw = if *is_await { "for await" } else { "for" };
                out.push_str(&format!("{pad}{kw} (const {binding} of "));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
                tasks.push(PrintTask::Raw(") {\n"));
                tasks.push(PrintTask::Expr {
                    expr: iter,
                    prec: 0,
                });
            }
            SNode::ForIn { binding, obj, body } => {
                out.push_str(&format!("{pad}for (const {binding} in "));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                tasks.push(PrintTask::Nodes {
                    slice: body,
                    indent: indent + 1,
                });
                tasks.push(PrintTask::Raw(") {\n"));
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
            }
            SNode::Switch { disc, cases } => {
                out.push_str(&format!("{pad}switch ("));
                tasks.push(PrintTask::RawOwned(format!("{pad}}}\n")));
                if !cases.is_empty() {
                    tasks.push(PrintTask::SwitchCases { cases, indent });
                }
                tasks.push(PrintTask::Raw(") {\n"));
                tasks.push(PrintTask::Expr {
                    expr: disc,
                    prec: 0,
                });
            }
            SNode::Honest(text) => {
                out.push_str(&format!("{pad}/* {text} */\n"));
            }
        }
    }

    fn step_print_leaf<'b>(
        &mut self,
        l: &'b Leaf,
        indent: usize,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        match l {
            Leaf::Raw(s) => tasks.push(PrintTask::Stmt { stmt: s, indent }),
            Leaf::Destructure { obj, keys, rest } => {
                let pad = "  ".repeat(indent);
                let mut parts: Vec<String> = keys
                    .iter()
                    .map(|(k, t)| {
                        if k == t && is_legal_ident(k) {
                            k.clone()
                        } else if crate::legalize::is_ident_name(k) {
                            format!("{k}: {t}")
                        } else {
                            format!("{}: {t}", render_pool_string(self.module, k))
                        }
                    })
                    .collect();
                parts.push(format!("...{rest}"));
                out.push_str(&format!("{pad}const {{{}}} = ", parts.join(", ")));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr { expr: obj, prec: 0 });
            }
            Leaf::Decl {
                name,
                mutable,
                value,
            } => {
                let pad = "  ".repeat(indent);
                let kw = if *mutable { "let" } else { "const" };
                match value {
                    Some(v) => {
                        out.push_str(&format!("{pad}{kw} {name} = "));
                        tasks.push(PrintTask::Raw(";\n"));
                        tasks.push(PrintTask::Expr { expr: v, prec: 0 });
                    }
                    None => out.push_str(&format!("{pad}{kw} {name};\n")),
                }
            }
            Leaf::Assign { target, value } => {
                let pad = "  ".repeat(indent);
                out.push_str(&format!("{pad}{target} = "));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
        }
    }

    #[allow(
        clippy::too_many_lines,
        reason = "statement emitter dispatches across all Stage-A Stmt variants"
    )]
    fn step_print_stmt<'b>(
        &mut self,
        s: &'b Stmt,
        indent: usize,
        tasks: &mut Vec<PrintTask<'b>>,
        out: &mut String,
    ) {
        let pad = "  ".repeat(indent);
        match s {
            Stmt::Declare {
                name,
                mutable,
                value,
                value_id,
            } => {
                if self.opts.line_anchors
                    && let Some(anchor) = self.line_anchor(*value_id)
                {
                    out.push_str(&format!("{pad}{anchor}\n"));
                }
                let kw = if *mutable { "let" } else { "const" };
                let hoisted = self.hoisted.contains(name);
                if let Expr::Class {
                    ctor,
                    heritage,
                    members,
                    member_attrs,
                    sendable,
                    ..
                } = value
                {
                    self.step_start_class(
                        &pad,
                        indent,
                        name,
                        *ctor,
                        heritage.as_deref(),
                        *members,
                        member_attrs,
                        *sendable,
                        tasks,
                        out,
                    );
                    return;
                }
                if hoisted {
                    out.push_str(&format!("{pad}{name} = "));
                } else {
                    out.push_str(&format!("{pad}{kw} {name} = "));
                }
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Stmt::PhiDecl { name, .. } => {
                out.push_str(&format!("{pad}var {name}; /* phi */\n"));
            }
            Stmt::PhiAssign { target, value, .. } => {
                out.push_str(&format!("{pad}{target} = "));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Stmt::Expr(expr) => {
                let wrap = expr::expr_needs_stmt_parens(expr);
                out.push_str(&pad);
                if wrap {
                    out.push('(');
                    tasks.push(PrintTask::Raw(");\n"));
                } else {
                    tasks.push(PrintTask::Raw(";\n"));
                }
                tasks.push(PrintTask::Expr { expr, prec: 0 });
            }
            Stmt::StoreProp {
                object,
                name,
                dot_legal,
                value,
                own,
            } => {
                let member = if *dot_legal {
                    format!(".{name}")
                } else {
                    format!("[{}]", render_pool_string(self.module, name))
                };
                let tag = if *own { " /*own*/" } else { "" };
                out.push_str(&pad);
                tasks.push(PrintTask::RawOwned(format!(";{tag}\n")));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
                tasks.push(PrintTask::RawOwned(format!("{member} = ")));
                tasks.push(PrintTask::Expr {
                    expr: object,
                    prec: 19,
                });
            }
            Stmt::StoreIndex {
                object,
                index,
                value,
                own,
            }
            | Stmt::StoreDyn {
                object,
                key: index,
                value,
                own,
            } => {
                let tag = if *own { " /*own*/" } else { "" };
                out.push_str(&pad);
                tasks.push(PrintTask::RawOwned(format!(";{tag}\n")));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
                tasks.push(PrintTask::Raw("] = "));
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
            Stmt::DefineMethod {
                object,
                name,
                func,
                length,
            } => {
                let member = if is_legal_ident(name) {
                    format!(".{name}")
                } else {
                    format!("[{}]", render_pool_string(self.module, name))
                };
                out.push_str(&pad);
                tasks.push(PrintTask::RawOwned(format!(
                    "; /*method (length={length})*/\n"
                )));
                tasks.push(PrintTask::Expr {
                    expr: func,
                    prec: 0,
                });
                tasks.push(PrintTask::RawOwned(format!("{member} = ")));
                tasks.push(PrintTask::Expr {
                    expr: object,
                    prec: 19,
                });
            }
            Stmt::StorePrivate {
                object,
                name,
                value,
                define,
            } => {
                out.push_str(&pad);
                if self.class_depth > 0 {
                    let tag = if *define { " /*define*/" } else { "" };
                    let pname = expr::format_private_ident(name);
                    tasks.push(PrintTask::RawOwned(format!(";{tag}\n")));
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                    tasks.push(PrintTask::RawOwned(format!(".#{pname} = ")));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 19,
                    });
                } else {
                    *self
                        .stats
                        .fallback_comments
                        .entry("StorePrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    tasks.push(PrintTask::RawOwned(format!(
                        "; /*private #{name} — out-of-class instance initializer (class-field fold pending)*/\n"
                    )));
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                    tasks.push(PrintTask::RawOwned(format!(
                        "[{}] = ",
                        render_pool_string(self.module, name)
                    )));
                    tasks.push(PrintTask::Expr {
                        expr: object,
                        prec: 19,
                    });
                }
            }
            Stmt::StoreSuper { name, key, value } => match (name, key) {
                (Some(n), None) => {
                    out.push_str(&format!("{pad}super.{n} = "));
                    tasks.push(PrintTask::Raw(";\n"));
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                }
                (None, Some(k)) => {
                    out.push_str(&format!("{pad}super["));
                    tasks.push(PrintTask::Raw(";\n"));
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                    tasks.push(PrintTask::Raw("] = "));
                    tasks.push(PrintTask::Expr { expr: k, prec: 0 });
                }
                _ => {
                    out.push_str(&format!("{pad}super[?] = "));
                    tasks.push(PrintTask::Raw(";\n"));
                    tasks.push(PrintTask::Expr {
                        expr: value,
                        prec: 0,
                    });
                }
            },
            Stmt::LexStore { name, value, .. } => {
                out.push_str(&format!("{pad}{} = ", sanitize(name)));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Stmt::GlobalStore { name, value, .. } => {
                let target = if is_legal_ident(name) {
                    name.clone()
                } else {
                    format!("globalThis[{}]", render_pool_string(self.module, name))
                };
                out.push_str(&format!("{pad}{target} = "));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Stmt::ModuleStore { name, value, .. } => {
                out.push_str(&format!("{pad}{name} = "));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr {
                    expr: value,
                    prec: 0,
                });
            }
            Stmt::ScopePush { names } => {
                let slots: Vec<String> = names
                    .iter()
                    .map(|n| n.clone().unwrap_or_else(|| "<unnamed>".to_string()))
                    .collect();
                out.push_str(&format!(
                    "{pad}/* scope-push [{}] (lexical binding scope not provably reconstructable — plain assignments, d-P8) */\n",
                    slots.join(", ")
                ));
            }
            Stmt::ScopePop => {
                out.push_str(&format!("{pad}/* scope-pop */\n"));
            }
            Stmt::PrivateNames { names } => {
                let ns: Vec<String> = names.iter().map(|n| format!("#{n}")).collect();
                out.push_str(&format!("{pad}/* private names {} */\n", ns.join(", ")));
            }
            Stmt::Throw(v) => {
                out.push_str(&format!("{pad}throw "));
                tasks.push(PrintTask::Raw(";\n"));
                tasks.push(PrintTask::Expr { expr: v, prec: 0 });
            }
            Stmt::Return(v) => match v {
                Some(v) => {
                    out.push_str(&format!("{pad}return "));
                    tasks.push(PrintTask::Raw(";\n"));
                    tasks.push(PrintTask::Expr { expr: v, prec: 0 });
                }
                None => out.push_str(&format!("{pad}return;\n")),
            },
            Stmt::Branch { dest } => {
                out.push_str(&format!(
                    "{pad}/* branch B{} (structurer residue) */\n",
                    dest.index()
                ));
            }
            Stmt::CondBranch {
                true_dest,
                false_dest,
                ..
            } => {
                out.push_str(&format!(
                    "{pad}/* cond-branch B{}/B{} (structurer residue) */\n",
                    true_dest.index(),
                    false_dest.index()
                ));
            }
            Stmt::CatchBind { name } => {
                out.push_str(&format!(
                    "{pad}/* catch-bind {name} (projection residue) */\n"
                ));
            }
            Stmt::Elided { op, reason, loc } => {
                *self.stats.elided_comments.entry(op).or_insert(0) += 1;
                out.push_str(&format!(
                    "{pad}/* elided {op}: {reason}{} */\n",
                    fmt_loc(*loc)
                ));
            }
            Stmt::Fallback { op, note, loc } => {
                *self.stats.fallback_comments.entry(op).or_insert(0) += 1;
                self.current_fn_has_fallback = true;
                out.push_str(&format!(
                    "{pad}/* fallback {op}: {note}{} */\n",
                    fmt_loc(*loc)
                ));
            }
            Stmt::Unreachable => {
                out.push_str(&format!("{pad}/* unreachable */\n"));
            }
            Stmt::Debugger => {
                out.push_str(&format!("{pad}debugger;\n"));
            }
        }
    }

    fn line_anchor(&self, v: abcd_ir::ValueId) -> Option<String> {
        let value = self.module.value(v)?;
        let ValueDef::Inst(iid) = value.def else {
            return None;
        };
        let loc = self.module.inst(iid)?.loc?;
        if loc.line == u32::MAX {
            return None;
        }
        Some(format!("// line {}", loc.line))
    }
}

/// Level-0 lexical bindings (`PutLexVar` stores) anywhere in a function
/// body, in first-appearance order — emitted as `let name;` at the
/// function top (d-P4 scope reconstruction v1: declaration placement;
/// the recompile gate needs bindings to exist — es2abc's output is
/// strict-mode, where assigning an undeclared name is a ReferenceError).
/// Level-N>0 stores target ancestor scopes and are declared by the
/// ancestor's own pass. Names already bound as parameters are skipped
/// (a `let` redeclaration of a parameter is a SyntaxError).
pub(crate) fn lex_decls(nodes: &[SNode], params: &[String]) -> Vec<String> {
    fn walk(
        root_nodes: &[SNode],
        out: &mut Vec<String>,
        seen: &mut BTreeSet<String>,
        own: usize,
        pushes: &mut usize,
    ) {
        let mut stack: Vec<std::slice::Iter<'_, SNode>> = vec![root_nodes.iter()];
        while let Some(iter) = stack.last_mut() {
            let Some(n) = iter.next() else {
                stack.pop();
                continue;
            };
            match n {
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        match l {
                            Leaf::Raw(Stmt::ScopePush { .. }) => *pushes += 1,
                            // Only owned frames are declared locally: a
                            // function without its own lexenv sees its
                            // CREATION-time environment at level 0 —
                            // those names are captures declared by an
                            // ancestor, and a local `let` would SHADOW
                            // the capture (dream gate: local/closure
                            // printed NaN from exactly that shadowing).
                            Leaf::Raw(Stmt::LexStore {
                                level,
                                own: true,
                                name,
                                ..
                            }) if (*level as usize) < own => {
                                let name = sanitize(name);
                                if seen.insert(name.clone()) {
                                    out.push(name);
                                }
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
                SNode::Block(body)
                | SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => {
                    stack.push(body.iter());
                }
                SNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    if let Some(fin) = finally {
                        stack.push(fin.iter());
                    }
                    for c in catches.iter().rev() {
                        stack.push(c.body.iter());
                    }
                    stack.push(body.iter());
                }
                SNode::Switch { cases, .. } => {
                    for c in cases.iter().rev() {
                        stack.push(c.body.iter());
                    }
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    // Count own lexenv frames first (the collection order pass).
    let mut pushes = 0usize;
    walk(nodes, &mut Vec::new(), &mut BTreeSet::new(), 0, &mut pushes);
    let mut out = Vec::new();
    let mut seen: BTreeSet<String> = params.iter().cloned().collect();
    walk(nodes, &mut out, &mut seen, pushes, &mut 0);
    out
}

/// All expression nodes of a statement (for the escape analysis).
pub(crate) fn stmt_exprs(s: &Stmt) -> Vec<&Expr> {
    match s {
        Stmt::Declare { value, .. } => vec![value],
        Stmt::PhiAssign { value, .. } => vec![value],
        Stmt::Expr(e) => vec![e],
        Stmt::StoreProp { object, value, .. } => vec![object, value],
        Stmt::StoreIndex {
            object,
            index,
            value,
            ..
        } => vec![object, index, value],
        Stmt::StoreDyn {
            object, key, value, ..
        } => vec![object, key, value],
        Stmt::DefineMethod { object, func, .. } => vec![object, func],
        Stmt::StorePrivate { object, value, .. } => vec![object, value],
        Stmt::StoreSuper { key, value, .. } => key.iter().chain(std::iter::once(value)).collect(),
        Stmt::LexStore { value, .. }
        | Stmt::GlobalStore { value, .. }
        | Stmt::ModuleStore { value, .. } => vec![value],
        Stmt::Throw(e) => vec![e],
        Stmt::Return(Some(e)) => vec![e],
        Stmt::CondBranch { cond, .. } => vec![cond],
        _ => Vec::new(),
    }
}

/// Block-escape analysis for one function body: the names of
/// [`Stmt::Declare`] temporaries referenced from OUTSIDE their
/// declaration's visibility region. A `const`/`let`/`class`
/// declaration is visible from its position to the END of its
/// innermost block list (including nested blocks of later siblings) —
/// and nowhere else. Positions are `(block-path, node-index,
/// leaf-index)` triples; node-level expressions (conditions, the
/// for-of iterated value) get `leaf-index = usize::MAX` at their node's
/// position — except the do-while condition, which JS scopes INSIDE
/// the loop body (after its last position).
///
/// (d-P4 dream gate: sibling `try` blocks aliasing to the same scope
/// path hid destructuring's `next` escape — "next is not defined";
/// and an earlier leaf-level model broke do-while's in-scope cond.)
pub(in crate::emit) fn escaped_temps(nodes: &[SNode]) -> BTreeSet<String> {
    /// A position: scope path + node index within it + leaf index.
    type Pos = (Vec<usize>, usize, usize);
    enum EscapeFrame<'a> {
        EnterNodes { nodes: &'a [SNode], idx: usize },
        PushPath(usize),
        PopPath,
    }
    fn collect_uses(root: &Expr, pos: &Pos, uses: &mut Vec<(String, Pos, bool)>) {
        let mut stack: Vec<&Expr> = vec![root];
        while let Some(e) = stack.pop() {
            match e {
                Expr::Temp { name, .. } => uses.push((name.clone(), pos.clone(), true)),
                Expr::Ident(name) => uses.push((name.clone(), pos.clone(), false)),
                _ => {}
            }
            for c in crate::folds::expr_children(e).into_iter().rev() {
                stack.push(c);
            }
        }
    }
    fn walk(
        root_nodes: &[SNode],
        path: &mut Vec<usize>,
        decls: &mut BTreeMap<String, Vec<Pos>>,
        catch_scopes: &mut BTreeMap<String, Vec<Vec<usize>>>,
        uses: &mut Vec<(String, Pos, bool)>,
    ) {
        let mut frames: Vec<EscapeFrame<'_>> = vec![EscapeFrame::EnterNodes {
            nodes: root_nodes,
            idx: 0,
        }];
        while let Some(frame) = frames.pop() {
            match frame {
                EscapeFrame::PushPath(p) => path.push(p),
                EscapeFrame::PopPath => {
                    path.pop();
                }
                EscapeFrame::EnterNodes { nodes, idx } => {
                    if idx >= nodes.len() {
                        continue;
                    }
                    let i = idx;
                    let n = &nodes[i];
                    frames.push(EscapeFrame::EnterNodes {
                        nodes,
                        idx: idx + 1,
                    });
                    match n {
                        SNode::Stmts(leaves) => {
                            for (li, l) in leaves.iter().enumerate() {
                                let pos: Pos = (path.clone(), i, li);
                                match l {
                                    Leaf::Raw(Stmt::Declare { name, value, .. }) => {
                                        collect_uses(value, &pos, uses);
                                        // A name can be declared in several
                                        // disjoint blocks (the cross-arm fold
                                        // duplicates tails) — a use escapes only
                                        // when it escapes ALL of them.
                                        decls.entry(name.clone()).or_default().push(pos);
                                    }
                                    Leaf::Raw(s) => {
                                        for e in stmt_exprs(s) {
                                            collect_uses(e, &pos, uses);
                                        }
                                    }
                                    Leaf::Destructure { obj, .. } => collect_uses(obj, &pos, uses),
                                    Leaf::Decl { value: Some(v), .. }
                                    | Leaf::Assign { value: v, .. } => collect_uses(v, &pos, uses),
                                    _ => {}
                                }
                            }
                        }
                        SNode::If {
                            cond,
                            then,
                            otherwise,
                        } => {
                            collect_uses(cond, &(path.clone(), i, usize::MAX), uses);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: otherwise,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(1));
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: then,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(0));
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::While { cond, body, .. } => {
                            if let Some(c) = cond {
                                collect_uses(c, &(path.clone(), i, usize::MAX), uses);
                            }
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: body,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(0));
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::DoWhile { body, cond, .. } => {
                            // `D3`: in JS, `while (cond)` in `do { … } while (cond)`
                            // executes in the ENCLOSING scope outside the `{ … }`
                            // body block, so any `const`/`let` declared inside `body`
                            // and referenced in `cond` escapes `body` and hoists to `var`.
                            collect_uses(cond, &(path.clone(), i, usize::MAX), uses);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: body,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(0));
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::Block(body)
                        | SNode::Labeled { body, .. }
                        | SNode::ForOf { body, .. }
                        | SNode::ForIn { body, .. } => {
                            if let SNode::ForOf { iter: head, .. }
                            | SNode::ForIn { obj: head, .. } = n
                            {
                                collect_uses(head, &(path.clone(), i, usize::MAX), uses);
                            }
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: body,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::Try {
                            body,
                            catches,
                            finally,
                            ..
                        } => {
                            for (k, c) in catches.iter().enumerate() {
                                if let Some(b) = &c.binding {
                                    let mut cpath = path.clone();
                                    cpath.push(i);
                                    cpath.push(1 + k);
                                    catch_scopes.entry(b.clone()).or_default().push(cpath);
                                }
                            }
                            if catches.len() > 1
                                && let Some(b0) = &catches[0].binding
                            {
                                for k in 1..catches.len() {
                                    let mut cpath = path.clone();
                                    cpath.push(i);
                                    cpath.push(1 + k);
                                    catch_scopes.entry(b0.clone()).or_default().push(cpath);
                                }
                            }
                            frames.push(EscapeFrame::PopPath);
                            if let Some(fin) = finally {
                                frames.push(EscapeFrame::PopPath);
                                frames.push(EscapeFrame::EnterNodes { nodes: fin, idx: 0 });
                                frames.push(EscapeFrame::PushPath(1 + catches.len()));
                            }
                            for (k, c) in catches.iter().enumerate().rev() {
                                frames.push(EscapeFrame::PopPath);
                                frames.push(EscapeFrame::EnterNodes {
                                    nodes: &c.body,
                                    idx: 0,
                                });
                                frames.push(EscapeFrame::PushPath(1 + k));
                            }
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: body,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(0));
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::Switch { disc, cases } => {
                            collect_uses(disc, &(path.clone(), i, usize::MAX), uses);
                            for t in cases.iter().flat_map(|c| c.tests.iter()) {
                                collect_uses(t, &(path.clone(), i, usize::MAX), uses);
                            }
                            frames.push(EscapeFrame::PopPath);
                            for (k, c) in cases.iter().enumerate().rev() {
                                frames.push(EscapeFrame::PopPath);
                                frames.push(EscapeFrame::EnterNodes {
                                    nodes: &c.body,
                                    idx: 0,
                                });
                                frames.push(EscapeFrame::PushPath(k));
                            }
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
                    }
                }
            }
        }
    }
    let mut decls: BTreeMap<String, Vec<Pos>> = BTreeMap::new();
    let mut catch_scopes: BTreeMap<String, Vec<Vec<usize>>> = BTreeMap::new();
    let mut uses: Vec<(String, Pos, bool)> = Vec::new();
    walk(
        nodes,
        &mut Vec::new(),
        &mut decls,
        &mut catch_scopes,
        &mut uses,
    );
    let mut out = BTreeSet::new();
    for (name, u, is_temp) in uses {
        // Visible: same block list at a later position, or nested
        // under a LATER sibling of the declaration's list.
        let visible = |(ds, dn, dl): &Pos| {
            let (us, un, ul) = &u;
            if us == ds {
                return (un, ul) > (dn, dl);
            }
            us.len() > ds.len() && us[..ds.len()] == ds[..] && us[ds.len()] > *dn
        };
        if is_temp
            && let Some(dpaths) = decls.get(&name)
            && !dpaths.iter().any(visible)
        {
            out.insert(name);
        } else if !decls.contains_key(&name)
            && let Some(cpaths) = catch_scopes.get(&name)
            && !cpaths.iter().any(|cp| u.0.starts_with(cp))
        {
            out.insert(name);
        }
    }
    out
}
