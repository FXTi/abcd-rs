use abcd_ir::expr::{BinOp, Expr, PropKey, UnOp};
use abcd_ir::stmt::Stmt;
use std::fmt::Write;

/// Emit a list of statements as JavaScript source text.
pub fn emit_js(stmts: &[Stmt]) -> String {
    let mut out = String::new();
    emit_stmts(&mut out, stmts, 0);
    out
}

fn emit_stmts(out: &mut String, stmts: &[Stmt], indent: usize) {
    for stmt in stmts {
        emit_stmt(out, stmt, indent);
    }
}

fn indent_str(level: usize) -> String {
    "    ".repeat(level)
}

fn emit_stmt(out: &mut String, stmt: &Stmt, indent: usize) {
    let pad = indent_str(indent);
    match stmt {
        Stmt::Expr(e) => {
            let _ = writeln!(out, "{pad}{};", emit_expr(e));
        }
        Stmt::Let { name, init } => {
            if let Some(init) = init {
                let _ = writeln!(out, "{pad}let {name} = {};", emit_expr(init));
            } else {
                let _ = writeln!(out, "{pad}let {name};");
            }
        }
        Stmt::Const { name, init } => {
            let _ = writeln!(out, "{pad}const {name} = {};", emit_expr(init));
        }
        Stmt::Assign { target, value } => {
            let _ = writeln!(out, "{pad}{} = {};", emit_expr(target), emit_expr(value));
        }
        Stmt::Return(None) => {
            let _ = writeln!(out, "{pad}return;");
        }
        Stmt::Return(Some(e)) => {
            let _ = writeln!(out, "{pad}return {};", emit_expr(e));
        }
        Stmt::Throw(e) => {
            let _ = writeln!(out, "{pad}throw {};", emit_expr(e));
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            let _ = writeln!(out, "{pad}if ({}) {{", emit_expr(cond));
            emit_stmts(out, then_body, indent + 1);
            if else_body.is_empty() {
                let _ = writeln!(out, "{pad}}}");
            } else {
                let _ = writeln!(out, "{pad}}} else {{");
                emit_stmts(out, else_body, indent + 1);
                let _ = writeln!(out, "{pad}}}");
            }
        }
        Stmt::While { cond, body } => {
            let _ = writeln!(out, "{pad}while ({}) {{", emit_expr(cond));
            emit_stmts(out, body, indent + 1);
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::ForIn {
            binding,
            object,
            body,
        } => {
            let _ = writeln!(out, "{pad}for (let {binding} in {}) {{", emit_expr(object));
            emit_stmts(out, body, indent + 1);
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::ForOf {
            binding,
            iterable,
            body,
        } => {
            let _ = writeln!(
                out,
                "{pad}for (let {binding} of {}) {{",
                emit_expr(iterable)
            );
            emit_stmts(out, body, indent + 1);
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::TryCatch {
            try_body,
            catch_binding,
            catch_body,
            finally_body,
        } => {
            let _ = writeln!(out, "{pad}try {{");
            emit_stmts(out, try_body, indent + 1);
            if !catch_body.is_empty() {
                if let Some(binding) = catch_binding {
                    let _ = writeln!(out, "{pad}}} catch ({binding}) {{");
                } else {
                    let _ = writeln!(out, "{pad}}} catch {{");
                }
                emit_stmts(out, catch_body, indent + 1);
            }
            if !finally_body.is_empty() {
                let _ = writeln!(out, "{pad}}} finally {{");
                emit_stmts(out, finally_body, indent + 1);
            }
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::Switch {
            discriminant,
            cases,
            default,
        } => {
            let _ = writeln!(out, "{pad}switch ({}) {{", emit_expr(discriminant));
            for case in cases {
                let _ = writeln!(out, "{pad}    case {}:", emit_expr(&case.test));
                emit_stmts(out, &case.body, indent + 2);
            }
            if !default.is_empty() {
                let _ = writeln!(out, "{pad}    default:");
                emit_stmts(out, default, indent + 2);
            }
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::Break => {
            let _ = writeln!(out, "{pad}break;");
        }
        Stmt::Continue => {
            let _ = writeln!(out, "{pad}continue;");
        }
        Stmt::Block(body) => {
            let _ = writeln!(out, "{pad}{{");
            emit_stmts(out, body, indent + 1);
            let _ = writeln!(out, "{pad}}}");
        }
        Stmt::Comment(text) => {
            let _ = writeln!(out, "{pad}// {text}");
        }
        Stmt::Debugger => {
            let _ = writeln!(out, "{pad}debugger;");
        }
    }
}

fn emit_expr(expr: &Expr) -> String {
    match expr {
        Expr::NumberLit(n) => {
            if *n == n.floor() && n.is_finite() && n.abs() < 1e15 {
                format!("{}", *n as i64)
            } else if n.is_finite() && n.abs() < 1e-300 && *n != 0.0 {
                // Denormalized float — likely a raw bit pattern (ArkUI attribute ID)
                format!("{:#x}", n.to_bits())
            } else {
                format!("{n}")
            }
        }
        Expr::StringLit(s) => format!("\"{}\"", escape_js_string(s)),
        Expr::BoolLit(b) => format!("{b}"),
        Expr::Null => "null".into(),
        Expr::Undefined => "undefined".into(),
        Expr::Var(name) => name.clone(),
        Expr::This => "this".into(),
        Expr::NewTarget => "new.target".into(),
        Expr::BinaryOp { op, lhs, rhs } => {
            let l = emit_expr_paren(lhs, Some(*op), true);
            let r = emit_expr_paren(rhs, Some(*op), false);
            format!("{l} {op} {r}")
        }
        Expr::UnaryOp { op, expr } => {
            let e = emit_expr_paren(expr, None, false);
            match op {
                UnOp::Inc | UnOp::Dec => format!("{op}{e}"),
                _ => format!("{op}{e}"),
            }
        }
        Expr::TypeOf(e) => format!("typeof {}", emit_expr(e)),
        Expr::MemberAccess { object, property } => {
            let obj = emit_expr_paren(object, None, false);
            if is_valid_ident(property) {
                format!("{obj}.{property}")
            } else {
                format!("{obj}[\"{}\"]", escape_js_string(property))
            }
        }
        Expr::ComputedAccess { object, index } => {
            let obj = emit_expr_paren(object, None, false);
            format!("{obj}[{}]", emit_expr(index))
        }
        Expr::Call { callee, args } => {
            let c = emit_expr(callee);
            let a: Vec<String> = args.iter().map(|a| emit_expr(a)).collect();
            format!("{c}({})", a.join(", "))
        }
        Expr::New { callee, args } => {
            let c = emit_expr(callee);
            let a: Vec<String> = args.iter().map(|a| emit_expr(a)).collect();
            format!("new {c}({})", a.join(", "))
        }
        Expr::SuperCall { args } => {
            let a: Vec<String> = args.iter().map(|a| emit_expr(a)).collect();
            format!("super({})", a.join(", "))
        }
        Expr::ArrayLit(elems) => {
            let e: Vec<String> = elems.iter().map(|e| emit_expr(e)).collect();
            format!("[{}]", e.join(", "))
        }
        Expr::ObjectLit(props) => {
            if props.is_empty() {
                return "{}".into();
            }
            let p: Vec<String> = props
                .iter()
                .map(|(k, v)| {
                    let key = match k {
                        PropKey::Ident(s) => s.clone(),
                        PropKey::Computed(e) => format!("[{}]", emit_expr(e)),
                    };
                    format!("{key}: {}", emit_expr(v))
                })
                .collect();
            format!("{{ {} }}", p.join(", "))
        }
        Expr::TemplateLit(parts) => {
            let p: Vec<String> = parts.iter().map(|e| emit_expr(e)).collect();
            format!("`{}`", p.join(""))
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            format!(
                "{} ? {} : {}",
                emit_expr(cond),
                emit_expr(then_expr),
                emit_expr(else_expr)
            )
        }
        Expr::Spread(e) => format!("...{}", emit_expr(e)),
        Expr::Await(e) => format!("await {}", emit_expr(e)),
        Expr::Yield(e) => format!("yield {}", emit_expr(e)),
        Expr::Assign { target, value } => {
            format!("{} = {}", emit_expr(target), emit_expr(value))
        }
        Expr::Acc => "__acc__".into(),
        Expr::Unknown(s) => s.clone(),
    }
}

fn emit_expr_paren(expr: &Expr, _parent_op: Option<BinOp>, _is_left: bool) -> String {
    let s = emit_expr(expr);
    // Add parens for binary ops nested inside other binary ops
    match expr {
        Expr::BinaryOp { .. } | Expr::Conditional { .. } | Expr::Assign { .. } => {
            format!("({s})")
        }
        _ => s,
    }
}

fn is_valid_ident(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if !first.is_alphabetic() && first != '_' && first != '$' {
        return false;
    }
    chars.all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

fn escape_js_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => {
                let _ = write!(out, "\\u{{{:04x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}
