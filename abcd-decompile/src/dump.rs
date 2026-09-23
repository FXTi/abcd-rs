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
    let mut out = String::new();
    for i in 0..module.functions.len() {
        let rf = crate::recover::recover_func(module, abcd_ir::FuncId::new(i as u32));
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
    match e {
        Expr::Lit(lit) => render_lit(lit),
        Expr::Ident(name) => name.clone(),
        Expr::Temp { name, .. } => name.clone(),
        Expr::PropName {
            object,
            name,
            dot_legal,
        } => {
            if *dot_legal {
                format!("({}.{name})", dump_expr(object))
            } else {
                format!(
                    "({}[{}])",
                    dump_expr(object),
                    crate::consts::render_string(name)
                )
            }
        }
        Expr::PropIndex { object, index } | Expr::PropDyn { object, key: index } => {
            format!("({}[{}])", dump_expr(object), dump_expr(index))
        }
        Expr::PrivateLoad { object, name } => format!("({}.#{name})", dump_expr(object)),
        Expr::PrivateTest { object, name } => format!("(#{name} in {})", dump_expr(object)),
        Expr::SuperProp { name, key } => match (name, key) {
            (Some(n), None) => format!("super.{n}"),
            (None, Some(k)) => format!("super[{}]", dump_expr(k)),
            _ => "super[?]".to_string(),
        },
        Expr::Call {
            callee,
            this,
            args,
            kind,
        } => dump_call(callee, this.as_deref(), args, *kind),
        Expr::SuperMarker => "super".to_string(),
        Expr::DynamicImport { specifier } => format!("import({})", dump_expr(specifier)),
        Expr::Unary { op, operand } => dump_unary(*op, operand),
        Expr::Delete { target } => format!("(delete {})", dump_expr(target)),
        Expr::Binary { op, left, right } => format!(
            "({} {} {})",
            dump_expr(left),
            binop_sym(*op),
            dump_expr(right)
        ),
        Expr::Compare { op, left, right } => format!(
            "({} {} {})",
            dump_expr(left),
            cmpop_sym(*op),
            dump_expr(right)
        ),
        Expr::RegExp { pattern, flags } => {
            format!("/{}/{flags}", pattern.replace('/', "\\/"))
        }
        Expr::ObjectLit { entries } => render_lit(&Lit::Object(entries.clone())),
        Expr::ArrayLit { elements } => render_lit(&Lit::Array(elements.clone())),
        Expr::Closure {
            body,
            name,
            kind,
            captures,
        } => {
            let caps: Vec<String> = captures
                .iter()
                .map(|(n, v)| format!("{n}={}", dump_expr(v)))
                .collect();
            format!(
                "closure(fn#{} {:?} {} captures=[{}])",
                body.index(),
                name,
                kind_tag(*kind),
                caps.join(", ")
            )
        }
        Expr::Class {
            ctor,
            name,
            heritage,
            members,
            member_attrs: _,
            sendable,
        } => {
            let ext = heritage
                .as_ref()
                .map(|h| format!(" extends {}", dump_expr(h)))
                .unwrap_or_default();
            let tag = if *sendable { " /*sendable*/" } else { "" };
            format!(
                "class(fn#{} {:?}{} members=c#{}){tag}",
                ctor.index(),
                name,
                ext,
                members.index()
            )
        }
        Expr::Yield { value } => format!("(yield {})", dump_expr(value)),
        Expr::Await { value, uncaught } => {
            if *uncaught {
                format!("(await {} /*uncaught*/)", dump_expr(value))
            } else {
                format!("(await {})", dump_expr(value))
            }
        }
        Expr::NewTarget => "new.target".to_string(),
        Expr::GlobalThis => "globalThis".to_string(),
        Expr::SelfFunction(name) => name.clone(),
        Expr::Arguments => "arguments".to_string(),
        Expr::RestArgs { start_index } => format!("...rest[from {start_index}]"),
        Expr::TemplateObject { cooked } => match cooked {
            Some(lits) => {
                let inner: Vec<String> = lits.iter().map(render_lit).collect();
                format!("template([{}]) /*cooked-only (G4)*/", inner.join(", "))
            }
            None => "template(<unresolved>) /*cooked-only (G4)*/".to_string(),
        },
        Expr::IterResultObj { value, done } => format!(
            "{{value: {}, done: {}}} /*iter-result*/",
            dump_expr(value),
            dump_expr(done)
        ),
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
                NodeStatus::Fallback => " /*hard-fallback*/",
                NodeStatus::Plumbing => " /*plumbing*/",
                NodeStatus::Expressed => "",
            };
            format!("{name}({}){tag}", dump_expr(obj))
        }
        Expr::CreateGenerator { func } => {
            format!("create-generator({}) /*plumbing*/", dump_expr(func))
        }
        Expr::GeneratorDriver { resume, genobj } => {
            let name = if *resume {
                "resume-generator"
            } else {
                "get-resume-mode"
            };
            format!("{name}({}) /*hard-fallback*/", dump_expr(genobj))
        }
        Expr::AsyncDriver { resolve, value } => {
            let name = if *resolve {
                "async-resolve"
            } else {
                "async-reject"
            };
            format!("{name}({}) /*hard-fallback*/", dump_expr(value))
        }
        Expr::CopyDataProps { dst, src } => {
            format!(
                "copy-data-props({}, {}) /*plumbing*/",
                dump_expr(dst),
                dump_expr(src)
            )
        }
        Expr::SetObjectWithProto { obj, proto } => format!(
            "set-object-with-proto({}, {}) /*plumbing*/",
            dump_expr(obj),
            dump_expr(proto)
        ),
        Expr::ArraySpread { dst, index, src } => format!(
            "array-spread({}, {}, {}) /*plumbing*/",
            dump_expr(dst),
            dump_expr(index),
            dump_expr(src)
        ),
        Expr::RestObject { obj, excluded } => {
            let keys: Vec<String> = excluded.iter().map(dump_expr).collect();
            format!(
                "rest-object({}, excluded=[{}]) /*plumbing*/",
                dump_expr(obj),
                keys.join(", ")
            )
        }
        Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        } => format!(
            "define-getter-setter({}, {}, get={}, set={}) /*plumbing*/",
            dump_expr(obj),
            dump_expr(key),
            dump_expr(getter),
            dump_expr(setter)
        ),
        Expr::ModuleNamespace { index } => format!("ns{index}"),
        Expr::ObjectBuild { entries } => {
            let inner: Vec<String> = entries
                .iter()
                .map(|e| match e {
                    crate::expr::ObjEntry::KeyValue(k, v) => {
                        format!("{}: {}", render_lit(k), dump_expr(v))
                    }
                    crate::expr::ObjEntry::Computed(k, v) => {
                        format!("[{}]: {}", dump_expr(k), dump_expr(v))
                    }
                    crate::expr::ObjEntry::Spread(s) => format!("...{}", dump_expr(s)),
                    crate::expr::ObjEntry::Proto(p) => format!("__proto__: {}", dump_expr(p)),
                    crate::expr::ObjEntry::Method(n, f) => format!("{n}: {}", dump_expr(f)),
                })
                .collect();
            format!("build-object({{{}}})", inner.join(", "))
        }
        Expr::ArrayBuild { elements } => {
            let inner: Vec<String> = elements
                .iter()
                .map(|e| match e {
                    crate::expr::ArrayElem::Item(i) => dump_expr(i),
                    crate::expr::ArrayElem::Spread(s) => format!("...{}", dump_expr(s)),
                })
                .collect();
            format!("build-array([{}])", inner.join(", "))
        }
        Expr::Fallback { op, note, operands } => {
            let ops: Vec<String> = operands.iter().map(dump_expr).collect();
            if ops.is_empty() {
                format!("fallback({op} /*{note}*/)")
            } else {
                format!("fallback({op} /*{note}*/, {})", ops.join(", "))
            }
        }
    }
}

fn dump_call(callee: &Expr, this: Option<&Expr>, args: &[Expr], kind: CallKind) -> String {
    let args: Vec<String> = args.iter().map(dump_expr).collect();
    match kind {
        CallKind::Direct => format!(
            "call({}, this={}, {})",
            dump_expr(callee),
            this.map(dump_expr).unwrap_or_else(|| "?".to_string()),
            args.join(", ")
        ),
        CallKind::Dynamic => format!("({}({}))", dump_expr(callee), args.join(", ")),
        CallKind::New => format!("(new {}({}))", dump_expr(callee), args.join(", ")),
        CallKind::Apply => format!(
            "({}.apply({}, {}))",
            dump_expr(callee),
            this.map(dump_expr).unwrap_or_else(|| "?".to_string()),
            args.join(", ")
        ),
        CallKind::Super => format!("super({})", args.join(", ")),
        CallKind::SuperSpread => format!("super(...{})", args.join(", ")),
        CallKind::SuperForwardAllArgs => "super(...args) /*forward-all*/".to_string(),
    }
}

fn dump_unary(op: UnOp, operand: &Expr) -> String {
    let e = dump_expr(operand);
    match op {
        UnOp::Minus => format!("(-{e})"),
        UnOp::BitNot => format!("(~{e})"),
        UnOp::LogicalNot => format!("(!{e})"),
        UnOp::Inc => format!("(++{e})"),
        UnOp::Dec => format!("(--{e})"),
        UnOp::TypeOf => format!("(typeof {e})"),
        UnOp::ToNumber => format!("(+{e})"),
        UnOp::ToNumeric => format!("(tonumeric {e})"),
        UnOp::Void => format!("(void {e})"),
        UnOp::IsTrue => format!("(istrue {e})"),
        UnOp::IsFalse => format!("(isfalse {e})"),
    }
}
