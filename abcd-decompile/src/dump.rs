//! The stable Stage-A debug dump: a deterministic text form of the
//! recovered expression trees per function (golden tests + the corpus
//! gate's byte-identical determinism assertion).
//!
//! The dump is **fully parenthesized** — [`Expr::precedence`] is Stage-C
//! metadata and plays no role here — and uses only sorted/ordered
//! containers, so two runs over the same module are byte-identical.

use std::fmt::Write as _;

use abcd_ir::function::{EdgeKind, Loc};
use abcd_ir::module::{FunctionKind, Module};
use abcd_ir::op::{BinOp, CallKind, CmpOp, UnOp};

use crate::consts::render_lit;
use crate::expr::{Expr, IterOp, Lit, NodeStatus};
use crate::recover::{BlockStmts, RecoveredFunc, Stmt};

/// Dump a whole module (every function, in table order).
pub fn dump_module(module: &Module) -> String {
    let index = crate::names::DecompileIndex::build(module);
    let mut out = String::new();
    for i in 0..module.functions.len() {
        let rf =
            crate::recover::recover_func_with_index(module, abcd_ir::FuncId::new(i as u32), &index);
        out.push_str(&dump_func(&rf));
    }
    out
}

/// Dump one recovered function.
pub fn dump_func(rf: &RecoveredFunc) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "fn #{} {:?} kind={} params=({})",
        rf.func.index(),
        rf.name,
        kind_tag(rf.kind),
        rf.params.join(", ")
    );
    for b in &rf.blocks {
        dump_block(&mut out, b);
    }
    out
}

fn kind_tag(kind: FunctionKind) -> &'static str {
    match kind {
        FunctionKind::Function => "function",
        FunctionKind::Constructor => "constructor",
        FunctionKind::Getter => "getter",
        FunctionKind::Setter => "setter",
        FunctionKind::Generator => "generator",
        FunctionKind::Async => "async",
        FunctionKind::AsyncGenerator => "async-generator",
        FunctionKind::Arrow => "arrow",
        FunctionKind::AsyncArrow => "async-arrow",
    }
}

fn dump_block(out: &mut String, b: &BlockStmts) {
    let preds: Vec<String> = b
        .preds
        .iter()
        .map(|e| {
            format!(
                "B{}:{}",
                e.from.index(),
                match e.kind {
                    EdgeKind::Normal => "N",
                    EdgeKind::Exceptional => "X",
                }
            )
        })
        .collect();
    let _ = writeln!(
        out,
        "  bb B{} preds=[{}]:",
        b.block.index(),
        preds.join(",")
    );
    for s in &b.stmts {
        dump_stmt(out, s);
    }
}

fn fmt_loc(loc: Option<Loc>) -> String {
    match loc {
        Some(l) => match l.column {
            Some(c) => format!(" @{}:{}", l.line, c),
            None => format!(" @{}", l.line),
        },
        None => String::new(),
    }
}

fn dump_stmt(out: &mut String, s: &Stmt) {
    match s {
        Stmt::Declare {
            name,
            mutable,
            value,
            value_id,
        } => {
            let kw = if *mutable { "let" } else { "const" };
            let _ = writeln!(
                out,
                "    {kw} {name} = {} ; v{}",
                dump_expr(value),
                value_id.index()
            );
        }
        Stmt::PhiDecl { name, value_id } => {
            let _ = writeln!(out, "    let {name} ; phi v{}", value_id.index());
        }
        Stmt::PhiAssign {
            target,
            value,
            to,
            exceptional,
        } => {
            let kind = if *exceptional {
                "exceptional"
            } else {
                "normal"
            };
            let _ = writeln!(
                out,
                "    phi-assign {target} = {} ; edge -> B{} ({kind})",
                dump_expr(value),
                to.index()
            );
        }
        Stmt::Expr(e) => {
            let _ = writeln!(out, "    {}", dump_expr(e));
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
                format!("[{}]", crate::consts::render_string(name))
            };
            let tag = if *own { " /*own*/" } else { "" };
            let _ = writeln!(
                out,
                "    {}{member} = {}{tag}",
                dump_expr(object),
                dump_expr(value)
            );
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
            let _ = writeln!(
                out,
                "    {}[{}] = {}{tag}",
                dump_expr(object),
                dump_expr(index),
                dump_expr(value)
            );
        }
        Stmt::DefineMethod {
            object,
            name,
            func,
            length,
        } => {
            let _ = writeln!(
                out,
                "    defmethod {}.{name} = {} /*length={length}*/",
                dump_expr(object),
                dump_expr(func)
            );
        }
        Stmt::StorePrivate {
            object,
            name,
            value,
            define,
        } => {
            let kw = if *define { "define" } else { "store" };
            let _ = writeln!(
                out,
                "    {kw} {}.#{name} = {}",
                dump_expr(object),
                dump_expr(value)
            );
        }
        Stmt::StoreSuper { name, key, value } => {
            let target = match (name, key) {
                (Some(n), None) => format!("super.{n}"),
                (None, Some(k)) => format!("super[{}]", dump_expr(k)),
                _ => "super[?]".to_string(),
            };
            let _ = writeln!(out, "    {target} = {}", dump_expr(value));
        }
        Stmt::LexStore {
            level,
            slot,
            name,
            value,
            ..
        } => {
            let _ = writeln!(
                out,
                "    lex {name} = {} /*L{level}#{slot}*/",
                dump_expr(value)
            );
        }
        Stmt::GlobalStore {
            name,
            value,
            tolerant,
        } => {
            let target = if crate::legalize::is_legal_ident(name) {
                name.clone()
            } else {
                format!("globalThis[{}]", crate::consts::render_string(name))
            };
            let tag = if *tolerant { " /*try*/" } else { "" };
            let _ = writeln!(out, "    {target} = {}{tag}", dump_expr(value));
        }
        Stmt::ModuleStore { index, name, value } => {
            let _ = writeln!(
                out,
                "    {name} = {} /*module slot {index}*/",
                dump_expr(value)
            );
        }
        Stmt::ScopePush { names } => {
            let slots: Vec<String> = names
                .iter()
                .map(|n| n.clone().unwrap_or_else(|| "<unnamed>".to_string()))
                .collect();
            let _ = writeln!(out, "    scope-push [{}]", slots.join(", "));
        }
        Stmt::ScopePop => {
            let _ = writeln!(out, "    scope-pop");
        }
        Stmt::PrivateNames { names } => {
            let names: Vec<String> = names.iter().map(|n| format!("#{n}")).collect();
            let _ = writeln!(out, "    private-names [{}]", names.join(", "));
        }
        Stmt::Throw(e) => {
            let _ = writeln!(out, "    throw {}", dump_expr(e));
        }
        Stmt::Return(v) => {
            let _ = writeln!(
                out,
                "    return{}",
                v.as_ref()
                    .map(|e| format!(" {}", dump_expr(e)))
                    .unwrap_or_default()
            );
        }
        Stmt::Branch { dest } => {
            let _ = writeln!(out, "    branch B{}", dest.index());
        }
        Stmt::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            let _ = writeln!(
                out,
                "    if {} then B{} else B{}",
                dump_expr(cond),
                true_dest.index(),
                false_dest.index()
            );
        }
        Stmt::CatchBind { name } => {
            let _ = writeln!(out, "    catch {name}");
        }
        Stmt::Elided { op, reason, loc } => {
            let _ = writeln!(out, "    ; elided {op}: {reason}{}", fmt_loc(*loc));
        }
        Stmt::Fallback { op, note, loc } => {
            let _ = writeln!(out, "    ; fallback {op}: {note}{}", fmt_loc(*loc));
        }
        Stmt::Unreachable => {
            let _ = writeln!(out, "    unreachable");
        }
        Stmt::Debugger => {
            let _ = writeln!(out, "    debugger");
        }
    }
}

fn binop_sym(op: BinOp) -> &'static str {
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

fn cmpop_sym(op: CmpOp) -> &'static str {
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

/// Render one expression node (fully parenthesized).
pub fn dump_expr(e: &Expr) -> String {
    let mut out = String::new();
    dump_expr_into(e, &mut out);
    out
}

enum DumpTask<'a> {
    Expr(&'a Expr),
    Str(&'static str),
    Owned(String),
}

fn push_comma_exprs<'a>(tasks: &mut Vec<DumpTask<'a>>, exprs: &'a [Expr]) {
    for (idx, ex) in exprs.iter().enumerate().rev() {
        tasks.push(DumpTask::Expr(ex));
        if idx > 0 {
            tasks.push(DumpTask::Str(", "));
        }
    }
}

#[allow(
    clippy::too_many_lines,
    reason = "iterative Stage-A debug printer dispatches across all Expr variants on a heap workstack"
)]
fn dump_expr_into(root: &Expr, out: &mut String) {
    let mut tasks: Vec<DumpTask<'_>> = vec![DumpTask::Expr(root)];
    while let Some(task) = tasks.pop() {
        match task {
            DumpTask::Str(s) => out.push_str(s),
            DumpTask::Owned(s) => out.push_str(&s),
            DumpTask::Expr(e) => match e {
                Expr::Lit(lit) => out.push_str(&render_lit(lit)),
                Expr::Ident(name) | Expr::Temp { name, .. } | Expr::SelfFunction(name) => {
                    out.push_str(name);
                }
                Expr::PropName {
                    object,
                    name,
                    dot_legal,
                } => {
                    out.push('(');
                    let tail = if *dot_legal {
                        format!(".{name})")
                    } else {
                        format!("[{}])", crate::consts::render_string(name))
                    };
                    tasks.push(DumpTask::Owned(tail));
                    tasks.push(DumpTask::Expr(object));
                }
                Expr::PropIndex { object, index } | Expr::PropDyn { object, key: index } => {
                    out.push('(');
                    tasks.push(DumpTask::Str("])"));
                    tasks.push(DumpTask::Expr(index));
                    tasks.push(DumpTask::Str("["));
                    tasks.push(DumpTask::Expr(object));
                }
                Expr::PrivateLoad { object, name } => {
                    out.push('(');
                    tasks.push(DumpTask::Owned(format!(".#{name})")));
                    tasks.push(DumpTask::Expr(object));
                }
                Expr::PrivateTest { object, name } => {
                    let _ = write!(out, "(#{name} in ");
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(object));
                }
                Expr::SuperProp { name, key } => match (name, key) {
                    (Some(n), None) => {
                        let _ = write!(out, "super.{n}");
                    }
                    (None, Some(k)) => {
                        out.push_str("super[");
                        tasks.push(DumpTask::Str("]"));
                        tasks.push(DumpTask::Expr(k));
                    }
                    _ => out.push_str("super[?]"),
                },
                Expr::Call {
                    callee,
                    this,
                    args,
                    kind,
                } => dump_call_tasks(&mut tasks, out, callee, this.as_deref(), args, *kind),
                Expr::SuperMarker => out.push_str("super"),
                Expr::DynamicImport { specifier } => {
                    out.push_str("import(");
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(specifier));
                }
                Expr::Unary { op, operand } => {
                    out.push_str(unop_prefix(*op));
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(operand));
                }
                Expr::Delete { target } => {
                    out.push_str("(delete ");
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(target));
                }
                Expr::Binary { op, left, right } => {
                    out.push('(');
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(right));
                    tasks.push(DumpTask::Owned(format!(" {} ", binop_sym(*op))));
                    tasks.push(DumpTask::Expr(left));
                }
                Expr::Compare { op, left, right } => {
                    out.push('(');
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(right));
                    tasks.push(DumpTask::Owned(format!(" {} ", cmpop_sym(*op))));
                    tasks.push(DumpTask::Expr(left));
                }
                Expr::RegExp { pattern, flags } => {
                    let _ = write!(out, "/{}/{flags}", pattern.replace('/', "\\/"));
                }
                Expr::ObjectLit { entries } => {
                    out.push_str(&render_lit(&Lit::Object(entries.clone())));
                }
                Expr::ArrayLit { elements } => {
                    out.push_str(&render_lit(&Lit::Array(elements.clone())));
                }
                Expr::Closure {
                    body,
                    name,
                    kind,
                    captures,
                } => {
                    let _ = write!(
                        out,
                        "closure(fn#{} {:?} {} captures=[",
                        body.index(),
                        name,
                        kind_tag(*kind)
                    );
                    tasks.push(DumpTask::Str("])"));
                    for (idx, (n, v)) in captures.iter().enumerate().rev() {
                        tasks.push(DumpTask::Expr(v));
                        tasks.push(DumpTask::Owned(if idx > 0 {
                            format!(", {n}=")
                        } else {
                            format!("{n}=")
                        }));
                    }
                }
                Expr::Class {
                    ctor,
                    name,
                    heritage,
                    members,
                    member_attrs: _,
                    sendable,
                } => {
                    let _ = write!(out, "class(fn#{} {:?}", ctor.index(), name);
                    let tag = if *sendable { " /*sendable*/" } else { "" };
                    tasks.push(DumpTask::Owned(format!(
                        " members=c#{}){tag}",
                        members.index()
                    )));
                    if let Some(h) = heritage {
                        tasks.push(DumpTask::Expr(h));
                        tasks.push(DumpTask::Str(" extends "));
                    }
                }
                Expr::Yield { value } => {
                    out.push_str("(yield ");
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(value));
                }
                Expr::YieldStar { value } => {
                    out.push_str("(yield* ");
                    tasks.push(DumpTask::Str(")"));
                    tasks.push(DumpTask::Expr(value));
                }
                Expr::Await { value, uncaught } => {
                    out.push_str("(await ");
                    tasks.push(DumpTask::Str(if *uncaught {
                        " /*uncaught*/)"
                    } else {
                        ")"
                    }));
                    tasks.push(DumpTask::Expr(value));
                }
                Expr::NewTarget => out.push_str("new.target"),
                Expr::GlobalThis => out.push_str("globalThis"),
                Expr::Arguments => out.push_str("arguments"),
                Expr::RestArgs { start_index } => {
                    let _ = write!(out, "...rest[from {start_index}]");
                }
                Expr::TemplateObject { raw, cooked } => {
                    let show = |lits: &[Lit]| {
                        let inner: Vec<String> = lits.iter().map(render_lit).collect();
                        inner.join(", ")
                    };
                    match (raw, cooked) {
                        (Some(r), Some(c)) => {
                            let _ =
                                write!(out, "template(raw [{}], cooked [{}])", show(r), show(c));
                        }
                        (Some(r), None) => {
                            let _ = write!(out, "template(raw [{}], cooked <unresolved>)", show(r));
                        }
                        (None, Some(c)) => {
                            let _ =
                                write!(out, "template([{}]) /*raw absent — cooked-only*/", show(c));
                        }
                        (None, None) => {
                            out.push_str("template(<unresolved>) /*raw+cooked absent*/");
                        }
                    }
                }
                Expr::TaggedTemplate { tag, quasis, exprs } => {
                    tasks.push(DumpTask::Str("`"));
                    for (i, q) in quasis.iter().enumerate().rev() {
                        if let Some(arg) = exprs.get(i) {
                            tasks.push(DumpTask::Str("}"));
                            tasks.push(DumpTask::Expr(arg));
                            tasks.push(DumpTask::Str("${"));
                        }
                        tasks.push(DumpTask::Owned(q.clone()));
                    }
                    tasks.push(DumpTask::Str("`"));
                    tasks.push(DumpTask::Expr(tag));
                }
                Expr::IterResultObj { value, done } => {
                    out.push_str("{value: ");
                    tasks.push(DumpTask::Str("} /*iter-result*/"));
                    tasks.push(DumpTask::Expr(done));
                    tasks.push(DumpTask::Str(", done: "));
                    tasks.push(DumpTask::Expr(value));
                }
                Expr::Iter { op, obj, status } => {
                    let name = match op {
                        IterOp::GetIterator => "get-iterator",
                        IterOp::GetAsyncIterator => "get-async-iterator",
                        IterOp::Next => "iter-next",
                        IterOp::Return => "iter-return",
                        IterOp::Throw => "iter-throw",
                        IterOp::GetPropIterator => "get-prop-iterator",
                        IterOp::NextPropName => "next-prop-name",
                    };
                    let tag = match status {
                        NodeStatus::Fallback => ") /*hard-fallback*/",
                        NodeStatus::Plumbing => ") /*plumbing*/",
                        NodeStatus::Expressed => ")",
                    };
                    let _ = write!(out, "{name}(");
                    tasks.push(DumpTask::Str(tag));
                    tasks.push(DumpTask::Expr(obj));
                }
                Expr::CreateGenerator { func } => {
                    out.push_str("create-generator(");
                    tasks.push(DumpTask::Str(") /*plumbing*/"));
                    tasks.push(DumpTask::Expr(func));
                }
                Expr::GeneratorDriver { resume, genobj } => {
                    let name = if *resume {
                        "resume-generator("
                    } else {
                        "get-resume-mode("
                    };
                    out.push_str(name);
                    tasks.push(DumpTask::Str(") /*hard-fallback*/"));
                    tasks.push(DumpTask::Expr(genobj));
                }
                Expr::AsyncDriver { resolve, value } => {
                    let name = if *resolve {
                        "async-resolve("
                    } else {
                        "async-reject("
                    };
                    out.push_str(name);
                    tasks.push(DumpTask::Str(") /*hard-fallback*/"));
                    tasks.push(DumpTask::Expr(value));
                }
                Expr::AsyncGeneratorResolve {
                    genobj,
                    value,
                    done,
                } => {
                    out.push_str("async-generator-resolve(");
                    tasks.push(DumpTask::Str(") /*hard-fallback*/"));
                    tasks.push(DumpTask::Expr(done));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(value));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(genobj));
                }
                Expr::CopyDataProps { dst, src } => {
                    out.push_str("copy-data-props(");
                    tasks.push(DumpTask::Str(") /*plumbing*/"));
                    tasks.push(DumpTask::Expr(src));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(dst));
                }
                Expr::SetObjectWithProto { obj, proto } => {
                    out.push_str("set-object-with-proto(");
                    tasks.push(DumpTask::Str(") /*plumbing*/"));
                    tasks.push(DumpTask::Expr(proto));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(obj));
                }
                Expr::ArraySpread { dst, index, src } => {
                    out.push_str("array-spread(");
                    tasks.push(DumpTask::Str(") /*plumbing*/"));
                    tasks.push(DumpTask::Expr(src));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(index));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(dst));
                }
                Expr::RestObject { obj, excluded } => {
                    out.push_str("rest-object(");
                    tasks.push(DumpTask::Str("]) /*plumbing*/"));
                    push_comma_exprs(&mut tasks, excluded);
                    tasks.push(DumpTask::Str(", excluded=["));
                    tasks.push(DumpTask::Expr(obj));
                }
                Expr::DefineGetterSetter {
                    obj,
                    key,
                    getter,
                    setter,
                } => {
                    out.push_str("define-getter-setter(");
                    tasks.push(DumpTask::Str(") /*plumbing*/"));
                    tasks.push(DumpTask::Expr(setter));
                    tasks.push(DumpTask::Str(", set="));
                    tasks.push(DumpTask::Expr(getter));
                    tasks.push(DumpTask::Str(", get="));
                    tasks.push(DumpTask::Expr(key));
                    tasks.push(DumpTask::Str(", "));
                    tasks.push(DumpTask::Expr(obj));
                }
                Expr::ModuleNamespace { index } => {
                    let _ = write!(out, "ns{index}");
                }
                Expr::ObjectBuild { entries } => {
                    out.push_str("build-object({");
                    tasks.push(DumpTask::Str("})"));
                    for (idx, ent) in entries.iter().enumerate().rev() {
                        match ent {
                            crate::expr::ObjEntry::KeyValue(k, v) => {
                                tasks.push(DumpTask::Expr(v));
                                tasks.push(DumpTask::Owned(format!("{}: ", render_lit(k))));
                            }
                            crate::expr::ObjEntry::Computed(k, v) => {
                                tasks.push(DumpTask::Expr(v));
                                tasks.push(DumpTask::Str("]: "));
                                tasks.push(DumpTask::Expr(k));
                                tasks.push(DumpTask::Str("["));
                            }
                            crate::expr::ObjEntry::Spread(s) => {
                                tasks.push(DumpTask::Expr(s));
                                tasks.push(DumpTask::Str("..."));
                            }
                            crate::expr::ObjEntry::Proto(p) => {
                                tasks.push(DumpTask::Expr(p));
                                tasks.push(DumpTask::Str("__proto__: "));
                            }
                            crate::expr::ObjEntry::Method(n, f) => {
                                tasks.push(DumpTask::Expr(f));
                                tasks.push(DumpTask::Owned(format!("{n}: ")));
                            }
                            crate::expr::ObjEntry::Getter(k, f) => {
                                tasks.push(DumpTask::Expr(f));
                                tasks.push(DumpTask::Owned(format!("get {k:?}: ")));
                            }
                            crate::expr::ObjEntry::Setter(k, f) => {
                                tasks.push(DumpTask::Expr(f));
                                tasks.push(DumpTask::Owned(format!("set {k:?}: ")));
                            }
                        }
                        if idx > 0 {
                            tasks.push(DumpTask::Str(", "));
                        }
                    }
                }
                Expr::ArrayBuild { elements } => {
                    out.push_str("build-array([");
                    tasks.push(DumpTask::Str("])"));
                    for (idx, elem) in elements.iter().enumerate().rev() {
                        match elem {
                            crate::expr::ArrayElem::Item(i) => tasks.push(DumpTask::Expr(i)),
                            crate::expr::ArrayElem::Spread(s) => {
                                tasks.push(DumpTask::Expr(s));
                                tasks.push(DumpTask::Str("..."));
                            }
                        }
                        if idx > 0 {
                            tasks.push(DumpTask::Str(", "));
                        }
                    }
                }
                Expr::Fallback { op, note, operands } => {
                    if operands.is_empty() {
                        let _ = write!(out, "fallback({op} /*{note}*/)");
                    } else {
                        let _ = write!(out, "fallback({op} /*{note}*/, ");
                        tasks.push(DumpTask::Str(")"));
                        push_comma_exprs(&mut tasks, operands);
                    }
                }
            },
        }
    }
}

fn dump_call_tasks<'a>(
    tasks: &mut Vec<DumpTask<'a>>,
    out: &mut String,
    callee: &'a Expr,
    this: Option<&'a Expr>,
    args: &'a [Expr],
    kind: CallKind,
) {
    match kind {
        CallKind::Direct => {
            out.push_str("call(");
            tasks.push(DumpTask::Str(")"));
            push_comma_exprs(tasks, args);
            tasks.push(DumpTask::Str(", "));
            match this {
                Some(t) => tasks.push(DumpTask::Expr(t)),
                None => tasks.push(DumpTask::Str("?")),
            }
            tasks.push(DumpTask::Str(", this="));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::Dynamic => {
            out.push('(');
            tasks.push(DumpTask::Str("))"));
            push_comma_exprs(tasks, args);
            tasks.push(DumpTask::Str("("));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::New => {
            out.push_str("(new ");
            tasks.push(DumpTask::Str("))"));
            push_comma_exprs(tasks, args);
            tasks.push(DumpTask::Str("("));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::NewSpread => {
            out.push_str("(new ");
            tasks.push(DumpTask::Str("))"));
            push_comma_exprs(tasks, args);
            tasks.push(DumpTask::Str("(..."));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::Apply => {
            out.push('(');
            tasks.push(DumpTask::Str("))"));
            push_comma_exprs(tasks, args);
            tasks.push(DumpTask::Str(", "));
            match this {
                Some(t) => tasks.push(DumpTask::Expr(t)),
                None => tasks.push(DumpTask::Str("?")),
            }
            tasks.push(DumpTask::Str(".apply("));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::ClassInit => {
            out.push('(');
            tasks.push(DumpTask::Str("))"));
            match this {
                Some(t) => tasks.push(DumpTask::Expr(t)),
                None => tasks.push(DumpTask::Str("this")),
            }
            tasks.push(DumpTask::Str(".call("));
            tasks.push(DumpTask::Expr(callee));
        }
        CallKind::Super | CallKind::SuperArrow => {
            out.push_str("super(");
            tasks.push(DumpTask::Str(")"));
            push_comma_exprs(tasks, args);
        }
        CallKind::SuperSpread => {
            out.push_str("super(...");
            tasks.push(DumpTask::Str(")"));
            push_comma_exprs(tasks, args);
        }
        CallKind::SuperForwardAllArgs => {
            out.push_str("super(...args) /*forward-all*/");
        }
    }
}

fn unop_prefix(op: UnOp) -> &'static str {
    match op {
        UnOp::Minus => "(-",
        UnOp::BitNot => "(~",
        UnOp::LogicalNot => "(!",
        UnOp::Inc => "(++",
        UnOp::Dec => "(--",
        UnOp::TypeOf => "(typeof ",
        UnOp::ToNumber => "(+",
        UnOp::ToNumeric => "(tonumeric ",
        UnOp::ToPropertyKey => "(topropertykey ",
        UnOp::Void => "(void ",
        UnOp::IsTrue => "(istrue ",
        UnOp::IsFalse => "(isfalse ",
        UnOp::JumpEqz => "(jeqz ",
        UnOp::JumpNez => "(jnez ",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{ObjEntry, ObjKey};

    fn id(s: &str) -> Expr {
        Expr::Ident(s.to_string())
    }

    // ── kind_tag variants (49-56) ────────────────────────────────────

    #[test]
    fn kind_tag_variants() {
        assert_eq!(kind_tag(FunctionKind::Function), "function");
        assert_eq!(kind_tag(FunctionKind::Constructor), "constructor");
        assert_eq!(kind_tag(FunctionKind::Getter), "getter");
        assert_eq!(kind_tag(FunctionKind::Setter), "setter");
        assert_eq!(kind_tag(FunctionKind::Generator), "generator");
        assert_eq!(kind_tag(FunctionKind::Async), "async");
        assert_eq!(kind_tag(FunctionKind::AsyncGenerator), "async-generator");
        assert_eq!(kind_tag(FunctionKind::Arrow), "arrow");
        assert_eq!(kind_tag(FunctionKind::AsyncArrow), "async-arrow");
    }

    // ── StoreProp bracket member (146) ───────────────────────────────

    #[test]
    fn store_prop_bracket_member() {
        let mut out = String::new();
        dump_stmt(
            &mut out,
            &Stmt::StoreProp {
                object: id("o"),
                name: "1x".to_string(),
                dot_legal: false,
                value: Expr::Lit(Lit::Null),
                own: true,
            },
        );
        assert_eq!(out, "    o[\"1x\"] = null /*own*/\n");
    }

    // ── GlobalStore non-identifier target (232) ──────────────────────

    #[test]
    fn global_store_bracket_target() {
        let mut out = String::new();
        dump_stmt(
            &mut out,
            &Stmt::GlobalStore {
                name: "1x".to_string(),
                value: Expr::Lit(Lit::Null),
                tolerant: true,
            },
        );
        assert_eq!(out, "    globalThis[\"1x\"] = null /*try*/\n");
    }

    // ── SuperProp dynamic key (364) + SuperMarker (373) ──────────────

    #[test]
    fn super_expr_arms() {
        let dynamic = Expr::SuperProp {
            name: None,
            key: Some(Box::new(id("k"))),
        };
        assert_eq!(dump_expr(&dynamic), "super[k]");
        let named = Expr::SuperProp {
            name: Some("n".to_string()),
            key: None,
        };
        assert_eq!(dump_expr(&named), "super.n");
        assert_eq!(dump_expr(&Expr::SuperMarker), "super");
    }

    // ── YieldStar (434) ──────────────────────────────────────────────

    #[test]
    fn yield_star_dump() {
        let e = Expr::YieldStar {
            value: Box::new(id("g")),
        };
        assert_eq!(dump_expr(&e), "(yield* g)");
    }

    // ── TemplateObject raw-only (454) ────────────────────────────────

    #[test]
    fn template_raw_only_dump() {
        let e = Expr::TemplateObject {
            raw: Some(vec![Lit::String("r".to_string())]),
            cooked: None,
        };
        assert_eq!(dump_expr(&e), "template(raw [\"r\"], cooked <unresolved>)");
    }

    // ── SetObjectWithProto (507-510) ─────────────────────────────────

    #[test]
    fn set_object_with_proto_dump() {
        let e = Expr::SetObjectWithProto {
            obj: Box::new(id("o")),
            proto: Box::new(id("p")),
        };
        assert_eq!(dump_expr(&e), "set-object-with-proto(o, p) /*plumbing*/");
    }

    // ── ObjectBuild entry kinds (543-556) ────────────────────────────

    #[test]
    fn object_build_entry_kinds() {
        let e = Expr::ObjectBuild {
            entries: vec![
                ObjEntry::KeyValue(Lit::String("a".to_string()), id("v")),
                ObjEntry::Computed(id("k"), id("v")),
                ObjEntry::Spread(id("s")),
                ObjEntry::Proto(id("p")),
                ObjEntry::Method("m".to_string(), id("f")),
                ObjEntry::Getter(ObjKey::Name("g".to_string()), id("gf")),
                ObjEntry::Setter(ObjKey::Computed(Box::new(id("ck"))), id("sf")),
            ],
        };
        assert_eq!(
            dump_expr(&e),
            "build-object({\"a\": v, [k]: v, ...s, __proto__: p, m: f, get Name(\"g\"): gf, set Computed(Ident(\"ck\")): sf})"
        );
    }

    // ── ArrayBuild (562-570) ─────────────────────────────────────────

    #[test]
    fn array_build_dump() {
        let e = Expr::ArrayBuild {
            elements: vec![
                crate::expr::ArrayElem::Item(id("a")),
                crate::expr::ArrayElem::Spread(id("s")),
            ],
        };
        assert_eq!(dump_expr(&e), "build-array([a, ...s])");
    }

    // ── Fallback with operands (577) ─────────────────────────────────

    #[test]
    fn fallback_with_operands_dump() {
        let e = Expr::Fallback {
            op: "Op",
            note: "why",
            operands: vec![id("a"), Expr::Lit(Lit::Null)],
        };
        assert_eq!(dump_expr(&e), "fallback(Op /*why*/, a, null)");
        let bare = Expr::Fallback {
            op: "Op",
            note: "why",
            operands: Vec::new(),
        };
        assert_eq!(dump_expr(&bare), "fallback(Op /*why*/)");
    }

    // ── UnOp::Void (617) ─────────────────────────────────────────────

    #[test]
    fn unary_void_dump() {
        let e = Expr::Unary {
            op: UnOp::Void,
            operand: Box::new(id("x")),
        };
        assert_eq!(dump_expr(&e), "(void x)");
    }
}
