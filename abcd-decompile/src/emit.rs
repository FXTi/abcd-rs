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
//! ## Known limitations (post-d-P4 backlog)
//!
//! - Arrow vs `function` is not recoverable from the IR — closures
//!   print as `function` (design §4.3: cosmetic).
//! - Lexical bindings print as assignments to declarations hoisted to
//!   the function top (`let`/`var` placement, not per-scope `const`
//!   reconstruction) — declaration KIND and precise scope extents are
//!   future scope-reconstruction work.
//! - `SuperForwardAllArgs` prints `super(...arguments)`; the
//!   default-derived-ctor elision is a later fold.
//! - Template literals print cooked-only with placeholders (IR gap
//!   G4).
//! - Multiple catch handlers per region (typed catches — no JS
//!   surface) merge into the first clause with a note.
//! - Class member-buffer attribute payloads (static vs instance
//!   placement, `Enumerable`/`Readable` bits) are skipped — methods
//!   land as instance members (dream-gate registered:
//!   private-property-in/private-field).
//! - The try-projection approximation zone (protected-range vs
//!   structure mismatch: join placement inside a protected span, the
//!   `cuts`/`splits` families) diverges on the optimizer try-catch
//!   corpus families (dream-gate registered).
//! - Vendor bigint inc/dec polymorphism (`5n--` → `4n`) is not
//!   expressible with the pure `x - 1` form (no corpus coverage).
//! - `--ts` annotations reflect only what the format carries: signatures
//!   exist on ≤11-format files (fact #A7); 12+/24 functions keep bare
//!   parameter lists under the flag (d-P8).

use std::collections::{BTreeMap, BTreeSet};

use abcd_ir::function::Loc;
use abcd_ir::module::{ExportDecl, FunctionKind, ImportDecl, Module, Signature};
use abcd_ir::op::{BinOp, CallKind, CmpOp, UnOp};
use abcd_ir::ty::{DynPrim, StaticTy, Ty};
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
    /// TypeScript annotations from the IR `Signature` metadata (d-P8).
    /// Honest scope: the file format carries signatures only on
    /// ≤11-format files (format fact #A7 — 12+/24 functions emit BARE
    /// parameter lists under this flag, never fabricated `any`s), and
    /// JS sources declare `any` everywhere, so on a JS corpus the flag
    /// only adds `: any` on ≤11 fixtures. Static (ArkTS) annotations —
    /// including `Reference` types resolved through the module's class
    /// table — render as their TS names when present.
    pub ts: bool,
    /// Append a `func_main_0();` call after the top-level functions so
    /// the module entry point actually executes (the d-P4 recompile
    /// gate needs it: the abc entry is invoked by the VM, but JS source
    /// declares it). Off by default — human-facing output stays clean.
    pub call_entry: bool,
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
        hoisted: BTreeSet::new(),
    };
    let mut out = String::new();
    out.push_str("// Decompiled by abcd-decompile (abcd-rs) — Stage B + emission v1.\n");
    out.push_str("// Fallback honesty: `/* fallback Op … */` marks unrecoverable ops; `/* elided … */` marks deliberately dropped compiler guards.\n");
    if opts.ts {
        out.push_str("// TypeScript mode: annotations come from IR signatures (≤11-format files only, format fact #A7); functions without signatures keep bare parameter lists.\n");
    }

    // Imports (1:1 enum mapping).
    for imp in &module.imports {
        match imp {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let import = module_facing_name(&sym_str(module, *import_name));
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

    // Global-binding predeclarations: `StoreGlobal`/`TryStoreGlobal`
    // (top-level sloppy-script bindings) are emitted as plain
    // assignments, which strict mode (es2abc's output mode) rejects
    // unless the name is declared. A script-top `var name;` creates the
    // global binding the assignment then sets (d-P4 — the recompile
    // gate found this: ReferenceError on every global store).
    let mut globals = BTreeSet::new();
    for inst in &module.insts {
        if let Op::StoreGlobal { name, .. } | Op::TryStoreGlobal { name, .. } = &inst.op {
            let n = sanitize(&sym_str(module, *name));
            if globals.insert(n.clone()) {
                em.fn_names.reserve(&n);
            }
        }
    }
    for g in &globals {
        out.push_str(&format!("var {g};\n"));
    }

    // Module-slot predeclarations (gap G2: `module_slot_names` resolves
    // the slot↔binding-name correspondence from file evidence — TDZ
    // guard names and stored definitions; evidence-free slots keep the
    // synthetic `m{index}` fallback). Declaring them at module scope
    // keeps the output strict-mode-parseable AND gives the trailing
    // `export { name }` records a binding to reference.
    let slot_names = crate::names::module_slot_names(module);
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
        let name = slot_names
            .get(s)
            .cloned()
            .unwrap_or_else(|| crate::names::module_slot_fallback(*s));
        em.fn_names.reserve(&name);
        out.push_str(&format!("let {name};\n"));
    }

    // Orphan lexical-slot predeclarations (G1; see
    // `orphan_lexenv_names`).
    for name in orphan_lexenv_names(module) {
        em.fn_names.reserve(&name);
        out.push_str(&format!("let {name}; /* orphan lexenv slot (G1) */\n"));
    }

    // Consumed functions: closure bodies, class ctors, and every
    // MethodRef in the const pool (emitted inline, never top-level).
    let consumed = consumed_functions(module);

    // Top-level functions.
    let mut entry_call: Option<String> = None;
    for i in 0..module.functions.len() {
        let f = FuncId::new(i as u32);
        if consumed.contains(&f) {
            continue;
        }
        let emitted = em.emit_top_level_function(f, &mut out);
        if opts.call_entry && emitted.1 == "func_main_0" {
            entry_call = Some(emitted.0);
        }
    }
    // The recompile gate: invoke the module entry point.
    if let Some(name) = entry_call {
        out.push_str(&format!("{name}();\n"));
    }

    // Exports (1:1 enum mapping). The local side is a module-scope
    // binding (resolved G2 slot names included); the `as` side is a
    // ModuleExportName — an IdentifierName, reserved words legal.
    for exp in &module.exports {
        match exp {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let export = module_facing_name(&sym_str(module, *export_name));
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
                let import = module_facing_name(&sym_str(module, *import_name));
                let export = module_facing_name(&sym_str(module, *export_name));
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

/// A module-facing name (`export { x as NAME }`, `import { NAME as x
/// }`) is an IdentifierName, not a binding: reserved words are legal
/// (`as default` is THE default-export spelling). Keep valid
/// IdentifierNames verbatim; sanitize only genuinely broken shapes.
fn module_facing_name(raw: &str) -> String {
    if crate::legalize::is_ident_name(raw) {
        raw.to_string()
    } else {
        sanitize(raw)
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
            // Method entries in object shape buffers emit inline too
            // (`{name: function …}`) — never top-level.
            Op::AllocObject { shape } => {
                collect_method_refs(module, *shape, &mut consumed);
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
    /// Temporaries of the CURRENT function whose uses escape their
    /// declaration's structured block (JS `const`/`let`/`class` are
    /// block-scoped; SSA dominance is not block-aligned). They are
    /// hoisted: `var name;` at the function top, `name = value;` at
    /// the original site. (d-P4 dream gate: `ReferenceError: _funcObj$1
    /// is not defined` — a class declared inside a `try` block, used
    /// after it.)
    hoisted: BTreeSet<String>,
}

/// Orphan lexical bindings (IR gap G1): unnamed lexenv slots get
/// fallback names `v{level}_{slot}`; when the slot's OWNING function
/// never stores to it textually (write-only-from-inner-closure), no
/// `let` is ever emitted and the capture is a free reference (dream
/// gate: for-update-continue-1, "v2_1 is not defined"). Declaring the
/// fallback names at module top is sound under textual nesting:
/// functions that DO declare the name shadow it locally.
fn orphan_lexenv_names(module: &Module) -> BTreeSet<String> {
    fn is_fallback(name: &str) -> bool {
        let b = name.as_bytes();
        // v<digits>_<digits>
        if !b.starts_with(b"v") {
            return false;
        }
        let rest = &name[1..];
        let Some((a, bb)) = rest.split_once('_') else {
            return false;
        };
        !a.is_empty()
            && !bb.is_empty()
            && a.bytes().all(|c| c.is_ascii_digit())
            && bb.bytes().all(|c| c.is_ascii_digit())
    }
    fn walk_expr(e: &Expr, out: &mut BTreeSet<String>) {
        if let Expr::Ident(name) = e
            && is_fallback(name)
        {
            out.insert(name.clone());
        }
        for c in crate::folds::expr_children(e) {
            walk_expr(c, out);
        }
    }
    let mut out = BTreeSet::new();
    for i in 0..module.functions.len() {
        let rf = recover_func(module, FuncId::new(i as u32));
        for b in &rf.blocks {
            for st in &b.stmts {
                if let Stmt::LexStore { name, .. } = st
                    && is_fallback(&sanitize(name))
                {
                    out.insert(sanitize(name));
                }
                for e in stmt_exprs(st) {
                    walk_expr(e, &mut out);
                }
            }
        }
    }
    out
}

/// The full per-function pipeline: Stage A → Stage B → folds.
impl<'m> Emitter<'m> {
    /// The full per-function pipeline: Stage A → Stage B → folds.
    fn func_nodes(&mut self, func: FuncId) -> (RecoveredFunc, Vec<SNode>) {
        self.stats.function_bodies += 1;
        let rf = recover_func(self.module, func);
        let mut structured = structure_func(self.module, &rf);
        let mut fstats = FoldStats::default();
        // The generator driver fold runs FIRST (d-P11, R4): pre-fold the
        // resume-mode dispatch is a plain if-chain everywhere (the
        // switch re-detection never sees it), giving one uniform match
        // shape across all profiles.
        folds::generator_machine_fold(&mut structured.body, rf.kind, &mut fstats);
        // The async-completion fold (N68/G6) runs BEFORE fold()'s
        // rethrow-try dissolution so a folded `catch (e) { throw e; }`
        // rejection wrapper dissolves as the no-op it is.
        folds::async_driver_fold(&mut structured.body, rf.kind, &mut fstats);
        folds::fold(&mut structured.body, &mut fstats);
        folds::scope_fold(&mut structured.body, &rf.params, &mut fstats);
        self.stats.structure =
            merge_struct_stats(std::mem::take(&mut self.stats.structure), &structured.stats);
        self.stats.folds = merge_fold_stats(std::mem::take(&mut self.stats.folds), &fstats);
        (rf, structured.body)
    }

    /// Returns the (legalized, minted) emitted name and the raw name.
    fn emit_top_level_function(&mut self, func: FuncId, out: &mut String) -> (String, String) {
        let (rf, body) = self.func_nodes(func);
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
    fn emit_function_body(
        &mut self,
        func: FuncId,
        indent: usize,
        out: &mut String,
    ) -> RecoveredFunc {
        let (rf, body) = self.func_nodes(func);
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
                finally,
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
                            // JS has ONE catch clause: the typed-catch
                            // handlers merge into it in dispatch order.
                            // The extra handler's exception param is
                            // bound to the clause's binding (a typed
                            // dispatch is unrecoverable — the file's
                            // type table does not reach the IR — so the
                            // merge is unconditional and says so).
                            out.push_str(&format!(
                                "{pad}  /* additional typed-catch handler (no JS surface) — body merged: */\n"
                            ));
                            if let Some(b) = &extra.binding
                                && *b != binding
                            {
                                out.push_str(&format!(
                                    "{pad}  const {b} = {binding}; /* merged typed-catch binding */\n"
                                ));
                            }
                            self.emit_nodes(&extra.body, indent + 1, out);
                        }
                    }
                    None => {
                        // A `finally` clause needs no catch (`try/finally`
                        // is valid JS); without either, keep the honesty
                        // empty-catch form.
                        if finally.is_none() {
                            out.push_str(&format!("{pad}}} catch (e) {{\n"));
                            out.push_str(&format!("{pad}  /* handler body unavailable */\n"));
                        }
                    }
                }
                if let Some(fbody) = finally {
                    // The `} finally {` line closes the try (no catch) or
                    // the last catch clause.
                    out.push_str(&format!("{pad}}} finally {{\n"));
                    self.emit_nodes(fbody, indent + 1, out);
                }
                out.push_str(&format!("{pad}}}\n"));
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
                        out.push_str(&format!("{pad}default: {{\n"));
                    } else {
                        for t in &case.tests {
                            let mut ts = String::new();
                            self.expr(t, 0, &mut ts);
                            out.push_str(&format!("{pad}case {ts}: {{\n"));
                        }
                    }
                    // Braced: switch cases share ONE block scope in JS,
                    // but the fold's arms can carry same-named temporaries
                    // (cross-arm tail duplication) — `const x` twice in one
                    // scope is a SyntaxError (dream gate: es2abc rejected
                    // super-properties with "already declared").
                    self.emit_nodes(&case.body, indent + 2, out);
                    out.push_str(&format!("{pad}  }}\n"));
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
                // Hoisted escapee: the `var` declaration is at the
                // function top; here a plain assignment.
                let hoisted = self.hoisted.contains(name);
                // Class declaration form.
                if let Expr::Class {
                    ctor,
                    name: class_name,
                    heritage,
                    members,
                    member_attrs,
                    sendable,
                } = value
                {
                    let _ = class_name;
                    let ctor = *ctor;
                    let heritage = heritage.clone();
                    let members = *members;
                    let member_attrs = member_attrs.clone();
                    let sendable = *sendable;
                    if hoisted {
                        self.emit_class_assign(
                            &pad,
                            indent,
                            name,
                            ctor,
                            heritage,
                            members,
                            &member_attrs,
                            sendable,
                            out,
                        );
                    } else {
                        self.emit_class(
                            &pad,
                            indent,
                            name,
                            ctor,
                            heritage,
                            members,
                            &member_attrs,
                            sendable,
                            out,
                        );
                    }
                    return;
                }
                if hoisted {
                    out.push_str(&format!("{pad}{name} = {};\n", self.estr(value)));
                } else {
                    out.push_str(&format!("{pad}{kw} {name} = {};\n", self.estr(value)));
                }
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

    /// Assignment form of a hoisted class (`name = class …`); the
    /// hoisted check in [`Emitter::emit_class`] does the work.
    fn emit_class_assign(
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
    fn emit_class(
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
            Some(Expr::Lit(Lit::Hole | Lit::Undefined)) | None => String::new(),
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
        collect_private_names(self.module, ctor, &mut priv_names);
        if let Some(Lit::Array(items)) = lit_of(self.module, members) {
            for item in &items {
                if let Lit::MethodRef(f) = item {
                    collect_private_names(self.module, *f, &mut priv_names);
                }
            }
        }
        // B2 class-field fold: the instance initializer's constant
        // private definitions print as `#name = <const>;` declarations
        // (the ctor's initializer call is elided at recover). Folded
        // names are EXCLUDED from the bare `#name;` set — a duplicate
        // private declaration would be a SyntaxError.
        let fold = crate::classfold::plan(self.module, ctor);
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
        let kind = attrs.map(|a| a.kind.clone()).unwrap_or_else(|| {
            self.module
                .func(f)
                .map(|d| d.kind)
                .unwrap_or(FunctionKind::Function)
        });
        let placement = if attrs.is_some_and(|a| a.is_static) {
            "static "
        } else {
            ""
        };
        let prefix = method_prefix(kind);
        let key = if is_legal_ident(name) {
            name.to_string()
        } else {
            render_string(name)
        };
        let mut body = String::new();
        let rf = self.emit_function_body(f, indent + 2, &mut body);
        let (params, ret) = self.params_ret(&rf);
        out.push_str(&format!(
            "{pad}  {placement}{prefix}{key}({params}){ret} {{\n{body}"
        ));
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
                                        other => render_lit(other),
                                    })
                                    .collect();
                                out.push_str(&format!(
                                    "{} /*template: raw absent, cooked-only*/",
                                    render_string(&joined.join(""))
                                ));
                            }
                            None => {
                                out.push_str("\"\" /*template unresolved (raw+cooked absent)*/")
                            }
                        }
                    }
                }
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
                self.sub(operand, 17, out);
            }
            UnOp::ToNumeric => {
                out.push('+');
                self.sub(operand, 17, out);
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
                // pure arithmetic form, keeping the ToNumber/ToNumeric
                // coercion. Corner: vendor bigint inc/dec polymorphism
                // (`5n--` → `4n`) is not expressible purely (`5n - 1`
                // throws) — no corpus fixture exercises it (registered).
                out.push('(');
                self.sub(operand, 0, out);
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
        // Arrows never appear in member position (concise methods are
        // `None` at the file level, not NC); degrade to plain syntax.
        FunctionKind::Function | FunctionKind::Arrow | FunctionKind::AsyncArrow => "",
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

/// Render an IR type as a TypeScript annotation (the `--ts` flag).
/// `Reference` types resolve through the module's own class table.
fn ty_ts(module: &Module, ty: &Ty) -> String {
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
    fn params_ret(&self, rf: &RecoveredFunc) -> (String, String) {
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

/// Level-0 lexical bindings (`PutLexVar` stores) anywhere in a function
/// body, in first-appearance order — emitted as `let name;` at the
/// function top (d-P4 scope reconstruction v1: declaration placement;
/// the recompile gate needs bindings to exist — es2abc's output is
/// strict-mode, where assigning an undeclared name is a ReferenceError).
/// Level-N>0 stores target ancestor scopes and are declared by the
/// ancestor's own pass. Names already bound as parameters are skipped
/// (a `let` redeclaration of a parameter is a SyntaxError).
fn lex_decls(nodes: &[SNode], params: &[String]) -> Vec<String> {
    fn walk(
        nodes: &[SNode],
        out: &mut Vec<String>,
        seen: &mut BTreeSet<String>,
        own: usize,
        pushes: &mut usize,
    ) {
        for n in nodes {
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
                            Leaf::Raw(Stmt::LexStore { level, name, .. })
                                if (*level as usize) < own =>
                            {
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
                    walk(then, out, seen, own, pushes);
                    walk(otherwise, out, seen, own, pushes);
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => walk(body, out, seen, own, pushes),
                SNode::Try { body, catches, .. } => {
                    walk(body, out, seen, own, pushes);
                    for c in catches {
                        walk(&c.body, out, seen, own, pushes);
                    }
                }
                SNode::Switch { cases, .. } => {
                    for c in cases {
                        walk(&c.body, out, seen, own, pushes);
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
fn stmt_exprs(s: &Stmt) -> Vec<&Expr> {
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
fn escaped_temps(nodes: &[SNode]) -> BTreeSet<String> {
    /// A position: scope path + node index within it + leaf index.
    type Pos = (Vec<usize>, usize, usize);
    fn collect_uses(e: &Expr, pos: &Pos, uses: &mut Vec<(String, Pos)>) {
        if let Expr::Temp { name, .. } = e {
            uses.push((name.clone(), pos.clone()));
        }
        for c in crate::folds::expr_children(e) {
            collect_uses(c, pos, uses);
        }
    }
    fn walk(
        nodes: &[SNode],
        path: &mut Vec<usize>,
        decls: &mut BTreeMap<String, Vec<Pos>>,
        uses: &mut Vec<(String, Pos)>,
    ) {
        for (i, n) in nodes.iter().enumerate() {
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
                            Leaf::Decl { value: Some(v), .. } | Leaf::Assign { value: v, .. } => {
                                collect_uses(v, &pos, uses)
                            }
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
                    path.push(i);
                    path.push(0);
                    walk(then, path, decls, uses);
                    path.pop();
                    path.push(1);
                    walk(otherwise, path, decls, uses);
                    path.pop();
                    path.pop();
                }
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        collect_uses(c, &(path.clone(), i, usize::MAX), uses);
                    }
                    path.push(i);
                    path.push(0);
                    walk(body, path, decls, uses);
                    path.pop();
                    path.pop();
                }
                SNode::DoWhile { body, cond, .. } => {
                    path.push(i);
                    path.push(0);
                    walk(body, path, decls, uses);
                    // JS scope: the do-while condition is INSIDE the
                    // loop body's block (`do { const x … } while (x)`
                    // is legal), after the last body position.
                    collect_uses(cond, &(path.clone(), usize::MAX, usize::MAX), uses);
                    path.pop();
                    path.pop();
                }
                SNode::Labeled { body, .. } => {
                    path.push(i);
                    walk(body, path, decls, uses);
                    path.pop();
                }
                SNode::ForOf { iter, body, .. } => {
                    collect_uses(iter, &(path.clone(), i, usize::MAX), uses);
                    path.push(i);
                    walk(body, path, decls, uses);
                    path.pop();
                }
                SNode::ForIn { obj, body, .. } => {
                    collect_uses(obj, &(path.clone(), i, usize::MAX), uses);
                    path.push(i);
                    walk(body, path, decls, uses);
                    path.pop();
                }
                SNode::Try { body, catches, .. } => {
                    path.push(i);
                    path.push(0);
                    walk(body, path, decls, uses);
                    path.pop();
                    for (k, c) in catches.iter().enumerate() {
                        path.push(1 + k);
                        walk(&c.body, path, decls, uses);
                        path.pop();
                    }
                    path.pop();
                }
                SNode::Switch { disc, cases } => {
                    collect_uses(disc, &(path.clone(), i, usize::MAX), uses);
                    for t in cases.iter().flat_map(|c| c.tests.iter()) {
                        collect_uses(t, &(path.clone(), i, usize::MAX), uses);
                    }
                    path.push(i);
                    for (k, c) in cases.iter().enumerate() {
                        path.push(k);
                        walk(&c.body, path, decls, uses);
                        path.pop();
                    }
                    path.pop();
                }
                SNode::Break { .. } | SNode::Continue { .. } | SNode::Honest(_) => {}
            }
        }
    }
    let mut decls: BTreeMap<String, Vec<Pos>> = BTreeMap::new();
    let mut uses: Vec<(String, Pos)> = Vec::new();
    walk(nodes, &mut Vec::new(), &mut decls, &mut uses);
    let mut out = BTreeSet::new();
    for (name, u) in uses {
        if let Some(dpaths) = decls.get(&name) {
            // Visible: same block list at a later position, or nested
            // under a LATER sibling of the declaration's list.
            let visible = |(ds, dn, dl): &Pos| {
                let (us, un, ul) = &u;
                if us == ds {
                    return (un, ul) > (dn, dl);
                }
                us.len() > ds.len() && us[..ds.len()] == ds[..] && us[ds.len()] > *dn
            };
            if !dpaths.iter().any(visible) {
                out.insert(name);
            }
        }
    }
    out
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
    a.try_join_hoists += b.try_join_hoists;
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
    a.finally_fold += b.finally_fold;
    a.scope_fold += b.scope_fold;
    a.gen_driver_sites += b.gen_driver_sites;
    a.gen_driver_entry += b.gen_driver_entry;
    a.gen_driver_bound += b.gen_driver_bound;
    a.async_driver += b.async_driver;
    a
}
