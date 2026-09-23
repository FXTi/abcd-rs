//! Stage C v1 — emission (design/decompile.md §4.3): precedence-correct
//! expression printing, statement emission with indentation, module /
//! class / function emission, and loud fallback comments (never silent).
//!
//! ## Precedence-correct printing
//!
//! [`Expr::precedence`] drives a standard parenthesization rule: a
//! child prints parenthesized when its precedence is strictly below the
//! context's; right operands of left-associative operators use
//! `prec + 1`. Special cases: `**` is right-associative and a unary
//! left operand of `**` is always parenthesized (JS syntax rule);
//! unary minus applied to a unary operand is parenthesized (`- -x`,
//! never `--x`); object literals parenthesize inside any operator
//! context and at statement position; `yield` parenthesizes inside any
//! operator.
//!
//! ## Fallback honesty
//!
//! Every [`Stmt::Fallback`]/[`Stmt::Elided`]/[`Expr::Fallback`] and
//! every hard-7 plumbing node prints as an annotated comment with the
//! op name and source location — never silently dropped (gen1 lesson
//! 6). [`EmitStats::fallback_comments`] counts them per op for the
//! corpus gate.
//!
//! ## Known v1 limitations (for d-P4's backlog)
//!
//! - Arrow vs `function` is not recoverable from the IR — closures
//!   print as `function` (design §4.3: cosmetic).
//! - Lexical bindings (`LexStore`) print as plain assignments; scope
//!   reconstruction (declaration kind and placement) is d-P4 work.
//! - `SuperForwardAllArgs` prints `super(...args)` with a note; the
//!   default-derived-ctor elision is a later fold.
//! - Template literals print cooked-only with placeholders (IR gap
//!   G4).
//! - Multiple catch handlers per region (typed catches — no JS
//!   surface) merge into the first clause with a note.
//! - `--ts` type annotations are NOT implemented at v1 (the flag in
//!   [`EmitOptions`] is reserved).

use std::collections::{BTreeMap, BTreeSet};

use abcd_ir::function::Loc;
use abcd_ir::module::{ExportDecl, FunctionKind, ImportDecl, Module};
use abcd_ir::op::{BinOp, CallKind, CmpOp, UnOp};
use abcd_ir::{Const, FuncId, Op, ValueDef};

use crate::consts::{lit_of, render_lit, render_string, sym_str};
use crate::expr::{ArrayElem, Expr, IterOp, Lit, NodeStatus, ObjEntry};
use crate::folds::{self, FoldStats};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::recover::{RecoveredFunc, Stmt, recover_func};
use crate::structure::{Leaf, SNode, StructStats, structure_func};

/// Emitter options.
#[derive(Clone, Debug, Default)]
pub struct EmitOptions {
    /// Print `// line N` anchors before statements whose SSA value
    /// carries a source location.
    pub line_anchors: bool,
    /// Reserved (TypeScript annotations are not implemented at v1).
    pub ts: bool,
}

/// Emission counters (the corpus gate prints them verbatim).
#[derive(Clone, Debug, Default)]
pub struct DecompileStats {
    /// Functions decompiled.
    pub functions: usize,
    /// Functions containing at least one fallback comment.
    pub functions_with_fallbacks: usize,
    /// Fallback comments per op (includes hard-7 plumbing).
    pub fallback_comments: BTreeMap<&'static str, usize>,
    /// Elided-guard comments per op.
    pub elided_comments: BTreeMap<&'static str, usize>,
    /// Classes reconstructed.
    pub classes: usize,
    /// Class methods emitted.
    pub class_methods: usize,
    /// Closures emitted inline.
    pub closures: usize,
    /// Aggregate structuring counters.
    pub structure: StructStats,
    /// Aggregate fold firing counters.
    pub folds: FoldStats,
    /// Function BODIES emitted (top-level + closures + class members +
    /// ctors; handlers re-emitted for split try wrappers count again —
    /// this is ≥ the module's function count).
    pub function_bodies: usize,
}

/// A decompiled module.
#[derive(Clone, Debug)]
pub struct DecompiledModule {
    /// The JS text.
    pub text: String,
    /// The counters.
    pub stats: DecompileStats,
}

/// Decompile a whole module to JS text.
pub fn decompile_module(module: &Module, opts: &EmitOptions) -> DecompiledModule {
    let mut em = Emitter {
        module,
        opts,
        stats: DecompileStats::default(),
        fn_names: Legalizer::new(),
        current_fn_has_fallback: false,
        current_kind: FunctionKind::Function,
        class_depth: 0,
    };
    let mut out = String::new();
    out.push_str("// Decompiled by abcd-decompile (abcd-rs) — Stage B + emission v1.\n");
    out.push_str("// Fallback honesty: `/* fallback Op … */` marks unrecoverable ops; `/* elided … */` marks deliberately dropped compiler guards.\n");

    // Imports (1:1 enum mapping).
    for imp in &module.imports {
        match imp {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let import = sanitize(&sym_str(module, *import_name));
                let spec = render_string(&sym_str(module, *module_request));
                em.fn_names.reserve(&local);
                if local == import {
                    out.push_str(&format!("import {{ {local} }} from {spec};\n"));
                } else {
                    out.push_str(&format!("import {{ {import} as {local} }} from {spec};\n"));
                }
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let spec = render_string(&sym_str(module, *module_request));
                em.fn_names.reserve(&local);
                out.push_str(&format!("import * as {local} from {spec};\n"));
            }
        }
    }

    // Module-slot predeclarations (gap G2 synthetic names; declaring
    // them keeps the output strict-mode-parseable).
    let mut slots = BTreeSet::new();
    for inst in &module.insts {
        match &inst.op {
            Op::LoadModuleVar { index } | Op::StoreModuleVar { index, .. } => {
                slots.insert(*index);
            }
            Op::GetModuleNamespace { index } => {
                slots.insert(*index);
            }
            _ => {}
        }
    }
    for s in &slots {
        let name = crate::names::module_slot_fallback(*s);
        em.fn_names.reserve(&name);
        out.push_str(&format!("let {name};\n"));
    }

    // Consumed functions: closure bodies, class ctors, and every
    // MethodRef in the const pool (emitted inline, never top-level).
    let consumed = consumed_functions(module);

    // Top-level functions.
    for i in 0..module.functions.len() {
        let f = FuncId::new(i as u32);
        if consumed.contains(&f) {
            continue;
        }
        em.emit_top_level_function(f, &mut out);
    }

    // Exports (1:1 enum mapping).
    for exp in &module.exports {
        match exp {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let export = sanitize(&sym_str(module, *export_name));
                if local == export {
                    out.push_str(&format!("export {{ {local} }};\n"));
                } else {
                    out.push_str(&format!("export {{ {local} as {export} }};\n"));
                }
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                let import = sanitize(&sym_str(module, *import_name));
                let export = sanitize(&sym_str(module, *export_name));
                let spec = render_string(&sym_str(module, *module_request));
                out.push_str(&format!("export {{ {import} as {export} }} from {spec};\n"));
            }
            ExportDecl::Star { module_request } => {
                let spec = render_string(&sym_str(module, *module_request));
                out.push_str(&format!("export * from {spec};\n"));
            }
        }
    }

    DecompiledModule {
        text: out,
        stats: em.stats,
    }
}

/// The functions a module emits INLINE (closure bodies, class ctors,
/// and MethodRefs in DefineClass member buffers) — everything else
/// emits top-level. Exposed for the corpus gate's per-function
/// coverage assertion. (Orphan MethodRefs in the const pool — buffers
/// no DefineClass references — do NOT consume: their functions emit
/// top-level rather than being dropped.)
pub fn consumed_functions(module: &Module) -> std::collections::BTreeSet<FuncId> {
    let mut consumed = std::collections::BTreeSet::new();
    for inst in &module.insts {
        match &inst.op {
            Op::DefineFunc { body, .. } => {
                consumed.insert(*body);
            }
            Op::DefineClass { ctor, members, .. }
            | Op::DefineSendableClass { ctor, members, .. } => {
                consumed.insert(*ctor);
                collect_method_refs(module, *members, &mut consumed);
            }
            _ => {}
        }
    }
    consumed
}

/// Walk a const (recursively) for `MethodRef` functions.
fn collect_method_refs(module: &Module, cid: abcd_ir::ConstId, out: &mut BTreeSet<FuncId>) {
    let Some(c) = module.consts.get(cid) else {
        return;
    };
    match c {
        Const::MethodRef(f) => {
            out.insert(*f);
        }
        Const::ArrayLiteral(items) => {
            for i in items {
                collect_method_refs_const(module, i, out);
            }
        }
        Const::ObjectLiteral { keys, values } => {
            for i in keys.iter().chain(values.iter()) {
                collect_method_refs_const(module, i, out);
            }
        }
        _ => {}
    }
}

fn collect_method_refs_const(module: &Module, c: &Const, out: &mut BTreeSet<FuncId>) {
    match c {
        Const::MethodRef(f) => {
            out.insert(*f);
        }
        Const::ArrayLiteral(items) => {
            for i in items {
                collect_method_refs_const(module, i, out);
            }
        }
        Const::ObjectLiteral { keys, values } => {
            for i in keys.iter().chain(values.iter()) {
                collect_method_refs_const(module, i, out);
            }
        }
        _ => {}
    }
}

struct Emitter<'m> {
    module: &'m Module,
    opts: &'m EmitOptions,
    stats: DecompileStats,
    /// Module-scope name legalizer (top-level function names).
    fn_names: Legalizer,
    current_fn_has_fallback: bool,
    /// The kind of the function currently being emitted (`yield` is
    /// only printable inside generator kinds; in plain async functions
    /// the `SuspendGenerator` op is async machinery — R4).
    current_kind: FunctionKind,
    /// Nesting depth of class-body emission (private names are only
    /// printable `#x` inside a class body; es2abc's out-of-class
    /// instance initializers print the loud string-key fallback).
    class_depth: usize,
}

impl<'m> Emitter<'m> {
    /// The full per-function pipeline: Stage A → Stage B → folds.
    fn func_nodes(&mut self, func: FuncId) -> (RecoveredFunc, Vec<SNode>) {
        self.stats.function_bodies += 1;
        let rf = recover_func(self.module, func);
        let mut structured = structure_func(self.module, &rf);
        let mut fstats = FoldStats::default();
        folds::fold(&mut structured.body, &mut fstats);
        self.stats.structure =
            merge_struct_stats(std::mem::take(&mut self.stats.structure), &structured.stats);
        self.stats.folds = merge_fold_stats(std::mem::take(&mut self.stats.folds), &fstats);
        (rf, structured.body)
    }

    fn emit_top_level_function(&mut self, func: FuncId, out: &mut String) {
        let (rf, body) = self.func_nodes(func);
        self.stats.functions += 1;
        self.current_fn_has_fallback = false;
        self.current_kind = rf.kind;
        let raw = rf.name.clone();
        let name = self.fn_names.mint(&raw);
        let params = rf.params[1.min(rf.params.len())..].join(", ");
        let keyword = fn_decl_keyword(rf.kind);
        if rf.kind == FunctionKind::Constructor {
            out.push_str("/* constructor outside a class context (data shape) */\n");
        }
        out.push_str(&format!("{keyword} {name}({params}) {{\n"));
        self.emit_nodes(&body, 1, out);
        out.push_str("}\n");
        if self.current_fn_has_fallback {
            self.stats.functions_with_fallbacks += 1;
        }
    }

    /// A closure/class-member body at a given indent.
    fn emit_function_body(
        &mut self,
        func: FuncId,
        indent: usize,
        out: &mut String,
    ) -> RecoveredFunc {
        let (rf, body) = self.func_nodes(func);
        let prev = self.current_kind;
        self.current_kind = rf.kind;
        self.emit_nodes(&body, indent, out);
        self.current_kind = prev;
        rf
    }

    // ── Statements ───────────────────────────────────────────────────

    fn emit_nodes(&mut self, nodes: &[SNode], indent: usize, out: &mut String) {
        for n in nodes {
            self.emit_node(n, indent, out);
        }
    }

    fn emit_node(&mut self, n: &SNode, indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
        match n {
            SNode::Stmts(leaves) => {
                for l in leaves {
                    self.emit_leaf(l, indent, out);
                }
            }
            SNode::If {
                cond,
                then,
                otherwise,
            } => {
                // Presentation: an empty then arm becomes `if (!c)` —
                // never `if (c) {} else {…}` (readability).
                let negated;
                let (cond, then, otherwise) = if then.is_empty() && !otherwise.is_empty() {
                    negated = crate::structure::negate(cond);
                    (&negated, otherwise, then)
                } else {
                    (cond, then, otherwise)
                };
                let mut c = String::new();
                self.expr(cond, 0, &mut c);
                if otherwise.is_empty() {
                    out.push_str(&format!("{pad}if ({c}) {{\n"));
                    self.emit_nodes(then, indent + 1, out);
                    out.push_str(&format!("{pad}}}\n"));
                } else {
                    out.push_str(&format!("{pad}if ({c}) {{\n"));
                    self.emit_nodes(then, indent + 1, out);
                    out.push_str(&format!("{pad}}} else {{\n"));
                    self.emit_nodes(otherwise, indent + 1, out);
                    out.push_str(&format!("{pad}}}\n"));
                }
            }
            SNode::While { label, cond, body } => {
                let c = match cond {
                    Some(c) => {
                        let mut s = String::new();
                        self.expr(c, 0, &mut s);
                        s
                    }
                    None => "true".to_string(),
                };
                let lbl = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                out.push_str(&format!("{pad}{lbl}while ({c}) {{\n"));
                self.emit_nodes(body, indent + 1, out);
                out.push_str(&format!("{pad}}}\n"));
            }
            SNode::DoWhile { label, body, cond } => {
                let lbl = label.as_ref().map(|l| format!("{l}: ")).unwrap_or_default();
                out.push_str(&format!("{pad}{lbl}do {{\n"));
                self.emit_nodes(body, indent + 1, out);
                let mut c = String::new();
                self.expr(cond, 0, &mut c);
                out.push_str(&format!("{pad}}} while ({c});\n"));
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
                self.emit_nodes(body, indent + 1, out);
                out.push_str(&format!("{pad}}}\n"));
            }
            SNode::Try {
                body,
                catches,
                note,
            } => {
                if let Some(note) = note {
                    out.push_str(&format!("{pad}/* {note} */\n"));
                }
                out.push_str(&format!("{pad}try {{\n"));
                self.emit_nodes(body, indent + 1, out);
                match catches.split_first() {
                    Some((first, rest)) => {
                        let binding = first.binding.clone().unwrap_or_else(|| "e".to_string());
                        out.push_str(&format!("{pad}}} catch ({binding}) {{\n"));
                        self.emit_nodes(&first.body, indent + 1, out);
                        for extra in rest {
                            out.push_str(&format!(
                                "{pad}  /* additional typed-catch handler (no JS surface) — body merged: */\n"
                            ));
                            self.emit_nodes(&extra.body, indent + 1, out);
                        }
                        out.push_str(&format!("{pad}}}\n"));
                    }
                    None => {
                        out.push_str(&format!("{pad}}} catch (e) {{\n"));
                        out.push_str(&format!("{pad}  /* handler body unavailable */\n{pad}}}\n"));
                    }
                }
            }
            SNode::ForOf {
                is_await,
                binding,
                iter,
                body,
            } => {
                let mut it = String::new();
                self.expr(iter, 0, &mut it);
                let kw = if *is_await { "for await" } else { "for" };
                out.push_str(&format!("{pad}{kw} (const {binding} of {it}) {{\n"));
                self.emit_nodes(body, indent + 1, out);
                out.push_str(&format!("{pad}}}\n"));
            }
            SNode::ForIn { binding, obj, body } => {
                let mut o = String::new();
                self.expr(obj, 0, &mut o);
                out.push_str(&format!("{pad}for (const {binding} in {o}) {{\n"));
                self.emit_nodes(body, indent + 1, out);
                out.push_str(&format!("{pad}}}\n"));
            }
            SNode::Switch { disc, cases } => {
                let mut d = String::new();
                self.expr(disc, 0, &mut d);
                out.push_str(&format!("{pad}switch ({d}) {{\n"));
                for case in cases {
                    if case.tests.is_empty() {
                        out.push_str(&format!("{pad}default:\n"));
                    } else {
                        for t in &case.tests {
                            let mut ts = String::new();
                            self.expr(t, 0, &mut ts);
                            out.push_str(&format!("{pad}case {ts}:\n"));
                        }
                    }
                    self.emit_nodes(&case.body, indent + 1, out);
                }
                out.push_str(&format!("{pad}}}\n"));
            }
            SNode::Honest(text) => {
                out.push_str(&format!("{pad}/* {text} */\n"));
            }
        }
    }

    fn emit_leaf(&mut self, l: &Leaf, indent: usize, out: &mut String) {
        match l {
            Leaf::Raw(s) => self.emit_stmt(s, indent, out),
            Leaf::Destructure { obj, keys, rest } => {
                let pad = "  ".repeat(indent);
                let mut o = String::new();
                self.expr(obj, 0, &mut o);
                let mut parts: Vec<String> = keys
                    .iter()
                    .map(|(k, t)| {
                        if k == t {
                            k.clone()
                        } else {
                            format!("{k}: {t}")
                        }
                    })
                    .collect();
                parts.push(format!("...{rest}"));
                out.push_str(&format!("{pad}const {{{}}} = {o};\n", parts.join(", ")));
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
                        let mut e = String::new();
                        self.expr(v, 0, &mut e);
                        out.push_str(&format!("{pad}{kw} {name} = {e};\n"));
                    }
                    None => out.push_str(&format!("{pad}{kw} {name};\n")),
                }
            }
            Leaf::Assign { target, value } => {
                let pad = "  ".repeat(indent);
                let mut e = String::new();
                self.expr(value, 0, &mut e);
                out.push_str(&format!("{pad}{target} = {e};\n"));
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn emit_stmt(&mut self, s: &Stmt, indent: usize, out: &mut String) {
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
                // Class declaration form.
                if let Expr::Class {
                    ctor,
                    name: class_name,
                    heritage,
                    members,
                    sendable,
                } = value
                {
                    let _ = class_name;
                    let ctor = *ctor;
                    let heritage = heritage.clone();
                    let members = *members;
                    let sendable = *sendable;
                    self.emit_class(&pad, indent, name, ctor, heritage, members, sendable, out);
                    return;
                }
                out.push_str(&format!("{pad}{kw} {name} = {};\n", self.estr(value)));
            }
            Stmt::PhiDecl { name, .. } => {
                // `var`, not `let`: per-edge phi assignments can
                // precede the join textually in the structured output
                // (TDZ-safety; documented phi-lowering trade-off).
                out.push_str(&format!("{pad}var {name}; /* phi */\n"));
            }
            Stmt::PhiAssign { target, value, .. } => {
                out.push_str(&format!("{pad}{target} = {};\n", self.estr(value)));
            }
            Stmt::Expr(expr) => {
                let mut text = self.estr(expr);
                // A statement starting with `{` parses as a block.
                if matches!(expr, Expr::ObjectLit { .. } | Expr::ObjectBuild { .. }) {
                    text = format!("({text})");
                }
                out.push_str(&format!("{pad}{text};\n"));
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
                    format!("[{}]", render_string(name))
                };
                let tag = if *own { " /*own*/" } else { "" };
                out.push_str(&format!(
                    "{pad}{}{member} = {};{tag}\n",
                    self.member_base(object),
                    self.estr(value)
                ));
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
                out.push_str(&format!(
                    "{pad}{}[{}] = {};{tag}\n",
                    self.member_base(object),
                    self.estr(index),
                    self.estr(value)
                ));
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
                    format!("[{}]", render_string(name))
                };
                out.push_str(&format!(
                    "{pad}{}{member} = {}; /*method (length={length})*/\n",
                    self.member_base(object),
                    self.estr(func)
                ));
            }
            Stmt::StorePrivate {
                object,
                name,
                value,
                define,
            } => {
                if self.class_depth > 0 {
                    let tag = if *define { " /*define*/" } else { "" };
                    out.push_str(&format!(
                        "{pad}{}.#{name} = {};{tag}\n",
                        self.member_base(object),
                        self.estr(value)
                    ));
                } else {
                    // Out-of-class instance initializer (es2abc class-
                    // field lowering): `#x` does not parse outside a
                    // class body — loud string-key form.
                    *self
                        .stats
                        .fallback_comments
                        .entry("StorePrivate(out-of-class)")
                        .or_insert(0) += 1;
                    self.current_fn_has_fallback = true;
                    out.push_str(&format!(
                        "{pad}{}[{}] = {}; /*private #{name} — out-of-class instance initializer (class-field fold pending)*/\n",
                        self.member_base(object),
                        render_string(name),
                        self.estr(value)
                    ));
                }
            }
            Stmt::StoreSuper { name, key, value } => {
                let target = match (name, key) {
                    (Some(n), None) => format!("super.{n}"),
                    (None, Some(k)) => format!("super[{}]", self.estr(k)),
                    _ => "super[?]".to_string(),
                };
                out.push_str(&format!("{pad}{target} = {};\n", self.estr(value)));
            }
            Stmt::LexStore { name, value, .. } => {
                out.push_str(&format!(
                    "{pad}{} = {};\n",
                    sanitize(name),
                    self.estr(value)
                ));
            }
            Stmt::GlobalStore { name, value, .. } => {
                let target = if is_legal_ident(name) {
                    name.clone()
                } else {
                    format!("globalThis[{}]", render_string(name))
                };
                out.push_str(&format!("{pad}{target} = {};\n", self.estr(value)));
            }
            Stmt::ModuleStore { name, value, .. } => {
                out.push_str(&format!("{pad}{name} = {};\n", self.estr(value)));
            }
            Stmt::ScopePush { names } => {
                let slots: Vec<String> = names
                    .iter()
                    .map(|n| n.clone().unwrap_or_else(|| "<unnamed>".to_string()))
                    .collect();
                out.push_str(&format!(
                    "{pad}/* scope-push [{}] (lexical bindings print as plain assignments at v1) */\n",
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
                out.push_str(&format!("{pad}throw {};\n", self.estr(v)));
            }
            Stmt::Return(v) => match v {
                Some(v) => out.push_str(&format!("{pad}return {};\n", self.estr(v))),
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

    /// An expression printed at statement (precedence-0) context.
    fn estr(&mut self, e: &Expr) -> String {
        let mut s = String::new();
        self.expr(e, 0, &mut s);
        s
    }

    /// A member-expression base, parenthesized when needed.
    fn member_base(&mut self, e: &Expr) -> String {
        let mut s = String::new();
        self.expr(e, 19, &mut s);
        s
    }

    fn line_anchor(&self, v: abcd_ir::ValueId) -> Option<String> {
        let value = self.module.value(v)?;
        let ValueDef::Inst(iid) = value.def else {
            return None;
        };
        let loc = self.module.inst(iid)?.loc?;
        Some(format!("// line {}", loc.line))
    }

    // ── Classes & closures ───────────────────────────────────────────

    /// `class Name extends H { constructor(…) {…} …methods… }`.
    fn emit_class(
        &mut self,
        pad: &str,
        indent: usize,
        name: &str,
        ctor: FuncId,
        heritage: Option<Box<Expr>>,
        members: abcd_ir::ConstId,
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
            Some(Expr::Lit(Lit::Hole | Lit::Undefined)) | None => String::new(),
            Some(h) => {
                let mut s = String::new();
                self.expr(h, 0, &mut s);
                format!(" extends {s}")
            }
        };
        out.push_str(&format!("{pad}class {name}{ext} {{\n"));
        self.class_depth += 1;
        // The constructor.
        out.push_str(&format!("{pad}  constructor("));
        let rf = {
            // Emit the ctor body into a scratch buffer to interleave
            // the signature.
            let mut body = String::new();
            let rf = self.emit_function_body(ctor, indent + 2, &mut body);
            let params = rf.params[1.min(rf.params.len())..].join(", ");
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
        collect_private_names(self.module, ctor, &mut priv_names);
        if let Some(Lit::Array(items)) = lit_of(self.module, members) {
            for item in &items {
                if let Lit::MethodRef(f) = item {
                    collect_private_names(self.module, *f, &mut priv_names);
                }
            }
        }
        for name in &priv_names {
            out.push_str(&format!("{pad}  #{};\n", sanitize(name)));
        }
        // The member buffer: flat [name, MethodRef, …metadata…].
        if let Some(Lit::Array(items)) = lit_of(self.module, members) {
            let mut pending: Option<String> = None;
            let mut skipped = 0usize;
            for item in &items {
                match item {
                    Lit::String(s) => pending = Some(s.clone()),
                    Lit::MethodRef(f) => {
                        let mname = pending.take().unwrap_or_else(|| format!("m${}", f.index()));
                        self.emit_class_method(pad, indent, &mname, *f, out);
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
        out: &mut String,
    ) {
        self.stats.class_methods += 1;
        let kind = self
            .module
            .func(f)
            .map(|d| d.kind)
            .unwrap_or(FunctionKind::Function);
        let prefix = method_prefix(kind);
        let key = if is_legal_ident(name) {
            name.to_string()
        } else {
            render_string(name)
        };
        let mut body = String::new();
        let rf = self.emit_function_body(f, indent + 2, &mut body);
        let params = rf.params[1.min(rf.params.len())..].join(", ");
        out.push_str(&format!("{pad}  {prefix}{key}({params}) {{\n{body}"));
        out.push_str(&format!("{pad}  }}\n"));
    }

    // ── Expressions (precedence-correct) ─────────────────────────────

    /// Print an expression; parenthesize when its precedence is below
    /// `prec`.
    fn expr(&mut self, e: &Expr, prec: u8, out: &mut String) {
        if e.precedence() < prec {
            out.push('(');
            self.expr_inner(e, out);
            out.push(')');
        } else {
            self.expr_inner(e, out);
        }
    }

    /// A sub-expression at context precedence `prec`.
    fn sub(&mut self, e: &Expr, prec: u8, out: &mut String) {
        self.expr(e, prec, out);
    }

    #[allow(clippy::too_many_lines)]
    fn expr_inner(&mut self, e: &Expr, out: &mut String) {
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
                    out.push_str(&format!("[{}]", render_string(name)));
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
                        render_string(name)
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
                    out.push_str(&format!("({} in ", render_string(name)));
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
                out.push_str(&format!("/{}/{flags}", pattern.replace('/', "\\/")));
            }
            Expr::ObjectLit { entries } => {
                out.push_str(&render_lit(&Lit::Object(entries.clone())));
            }
            Expr::ArrayLit { elements } => {
                out.push_str(&render_lit(&Lit::Array(elements.clone())));
            }
            Expr::ObjectBuild { entries } => {
                out.push('{');
                let parts: Vec<String> = entries
                    .iter()
                    .map(|en| {
                        let mut s = String::new();
                        match en {
                            ObjEntry::KeyValue(k, v) => {
                                s.push_str(&render_lit_key_pub(k));
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
                                if is_legal_ident(n) {
                                    s.push_str(n);
                                } else {
                                    s.push_str(&render_string(n));
                                }
                                s.push_str(": ");
                                self.expr(f, 0, &mut s);
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
                let keyword = closure_prefix(kind);
                if named {
                    out.push_str(&format!("{keyword} {display}("));
                } else {
                    out.push_str(&format!("{keyword} ("));
                }
                let mut text = String::new();
                let rf = self.emit_function_body(body, 1, &mut text);
                let params = rf.params[1.min(rf.params.len())..].join(", ");
                out.push_str(&format!("{params}) {{\n{text}}}"));
                out.push_str(&format!(
                    " /* arrow vs function is not recoverable (design §4.3) */"
                ));
            }
            Expr::Class {
                ctor,
                name,
                heritage,
                members,
                sendable,
            } => {
                // Class expression form.
                let (ctor, name, heritage, members, sendable) =
                    (*ctor, name.clone(), heritage.clone(), *members, *sendable);
                let mut s = String::new();
                self.emit_class(
                    "",
                    0,
                    &sanitize(&name),
                    ctor,
                    heritage,
                    members,
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
            Expr::Await { value, .. } => {
                out.push_str("await ");
                self.sub(value, 17, out);
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
            Expr::TemplateObject { cooked } => {
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
                                other => render_lit(other),
                            })
                            .collect();
                        out.push_str(&format!(
                            "{} /*template: cooked-only, interpolations not recovered (G4)*/",
                            render_string(&joined.join(""))
                        ));
                    }
                    None => out.push_str("\"\" /*template unresolved (G4)*/"),
                }
            }
            Expr::IterResultObj { value, done } => {
                out.push_str("{ value: ");
                self.sub(value, 0, out);
                out.push_str(", done: ");
                self.sub(done, 0, out);
                out.push_str(" } /*iter-result*/");
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
                out.push_str("Object.defineProperties(");
                self.sub(obj, 0, out);
                out.push_str(", { [");
                self.sub(key, 0, out);
                out.push_str("]: { get: ");
                self.sub(getter, 0, out);
                out.push_str(", set: ");
                self.sub(setter, 0, out);
                out.push_str(" } }) /*DefineGetterSetterByValue: approximate*/");
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
                self.sub(callee, 19, out);
                self.emit_args(args, out);
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
                out.push_str(
                    "super(...args) /*forward-all: default derived ctor elision pending*/",
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
                self.sub(operand, 17, out);
            }
            UnOp::ToNumeric => {
                out.push('+');
                self.sub(operand, 17, out);
                out.push_str(" /*ToNumeric*/");
            }
            UnOp::Minus | UnOp::Inc | UnOp::Dec => {
                let sym = match op {
                    UnOp::Minus => "-",
                    UnOp::Inc => "++",
                    UnOp::Dec => "--",
                    _ => unreachable!(),
                };
                out.push_str(sym);
                // Inc/Dec: the bytecode operator applies to a reference;
                // es2abc's ToNumber/ToNumeric coercion of the TARGET is
                // part of the operation — strip it or the printed
                // `--(+x)` is not assignable (parse error).
                let target = if matches!(op, UnOp::Inc | UnOp::Dec) {
                    match operand {
                        Expr::Unary {
                            op: UnOp::ToNumber | UnOp::ToNumeric,
                            operand: inner,
                        } => inner.as_ref(),
                        _ => operand,
                    }
                } else {
                    operand
                };
                // `--x`-style ambiguity: parenthesize unary operands.
                if matches!(target, Expr::Unary { .. }) {
                    out.push('(');
                    self.expr_inner(target, out);
                    out.push(')');
                } else {
                    self.sub(target, 17, out);
                }
            }
        }
    }

    /// A literal with JS-valid MethodRef rendering.
    fn render_lit_js(&self, lit: &Lit) -> String {
        match lit {
            Lit::MethodRef(f) => format!("undefined /*method fn#{}*/", f.index()),
            Lit::Array(items) => {
                let inner: Vec<String> = items.iter().map(|i| self.render_lit_js(i)).collect();
                format!("[{}]", inner.join(", "))
            }
            Lit::Object(entries) => {
                let inner: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| format!("{}: {}", render_lit_key_pub(k), self.render_lit_js(v)))
                    .collect();
                format!("{{{}}}", inner.join(", "))
            }
            other => render_lit(other),
        }
    }
}

/// Collect private names referenced by a function's private-name ops
/// (the names are level/slot fallbacks when unresolvable — IR gap,
/// documented; the set makes declarations duplicate-safe).
fn collect_private_names(module: &Module, func: FuncId, out: &mut BTreeSet<String>) {
    let Some(f) = module.func(func) else {
        return;
    };
    let scopes = crate::names::NameScopes::build(module, func);
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
fn fn_decl_keyword(kind: FunctionKind) -> &'static str {
    match kind {
        FunctionKind::Async => "async function",
        FunctionKind::Generator => "function*",
        FunctionKind::AsyncGenerator => "async function*",
        _ => "function",
    }
}

/// The declaration keyword for a closure expression.
fn closure_prefix(kind: FunctionKind) -> &'static str {
    fn_decl_keyword(kind)
}

/// A class-member prefix for [`FunctionKind`].
fn method_prefix(kind: FunctionKind) -> &'static str {
    match kind {
        FunctionKind::Constructor => "",
        FunctionKind::Getter => "get ",
        FunctionKind::Setter => "set ",
        FunctionKind::Async => "async ",
        FunctionKind::Generator => "*",
        FunctionKind::AsyncGenerator => "async *",
        FunctionKind::Function => "",
    }
}

fn iter_op_name(op: IterOp) -> &'static str {
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
fn render_lit_key_pub(lit: &Lit) -> String {
    if let Lit::String(s) = lit
        && is_legal_ident(s)
    {
        return s.clone();
    }
    render_lit(lit)
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

fn merge_struct_stats(mut a: StructStats, b: &StructStats) -> StructStats {
    a.ifs += b.ifs;
    a.loops_while += b.loops_while;
    a.loops_do_while += b.loops_do_while;
    a.loops_while_true += b.loops_while_true;
    a.labeled_exits += b.labeled_exits;
    a.alternates += b.alternates;
    a.irreducible_fallbacks += b.irreducible_fallbacks;
    a.state_machine_blocks += b.state_machine_blocks;
    a.try_catches += b.try_catches;
    a.try_cuts += b.try_cuts;
    a.try_splits += b.try_splits;
    a.multi_catch += b.multi_catch;
    a.handler_shims += b.handler_shims;
    a.exit_phi_after_loop += b.exit_phi_after_loop;
    a.cross_arm_notes += b.cross_arm_notes;
    a.cross_arm_folds += b.cross_arm_folds;
    a.cross_arm_dup_blocks += b.cross_arm_dup_blocks;
    a.break_target_notes += b.break_target_notes;
    a
}

fn merge_fold_stats(mut a: FoldStats, b: &FoldStats) -> FoldStats {
    a.for_of += b.for_of;
    a.for_await_of += b.for_await_of;
    a.for_in += b.for_in;
    a.object_lit += b.object_lit;
    a.array_lit += b.array_lit;
    a.rest += b.rest;
    a.switch += b.switch;
    a
}
