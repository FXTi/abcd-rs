//! Stage C — emission (`design/decompile.md` §4.3): precedence-correct
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
//! op name and source location — never silently dropped
//! (`design/decompile.md` §5, `design/decisions.md`).
//! [`DecompileStats::fallback_comments`] counts them per op for the
//! corpus gate.
//!
//! ## Emitter invariants
//!
//! - Lexical bindings that `folds::scope_fold` cannot prove single-run
//!   block-local hoist to function-top `let`/`var` declarations (`const`
//!   vs `let` requires cross-closure reassignment proofs).
//! - `SuperForwardAllArgs` prints `super(...arguments)`.
//! - Template literals emit backtick raw+cooked forms when both lists
//!   resolve, degrading loudly to cooked-only comments when raw arrays
//!   are absent.
//! - Multiple catch handlers per region (typed catches — no JS surface)
//!   merge into the single `catch` clause with explicit bindings.
//! - Vendor bigint inc/dec polymorphism (`5n--` → `4n`) has no corpus
//!   coverage under the pure `x - 1` form.
//! - `--ts` annotations reflect only what the format carries: signatures
//!   exist on ≤11-format files; 12+/24 functions keep bare parameter
//!   lists under the flag.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Write;

use abcd_ir::function::Loc;
use abcd_ir::module::{ExportDecl, FunctionKind, ImportDecl, Module, Signature};
use abcd_ir::op::{BinOp, CallKind, CmpOp, UnOp};
use abcd_ir::ty::{DynPrim, StaticTy, Ty};
use abcd_ir::{Const, FuncId, Op, ValueDef};
use rayon::prelude::*;

use crate::consts::{lit_of, render_lit_m, render_pool_string, render_sym_string, sym_str};
use crate::expr::{ArrayElem, Expr, IterOp, Lit, NodeStatus, ObjEntry};
use crate::folds::{self, FoldStats};
use crate::legalize::{Legalizer, is_legal_ident, sanitize};
use crate::names::DecompileIndex;
use crate::recover::{RecoveredFunc, Stmt, recover_func, recover_func_with_index};
use crate::structure::{Leaf, SNode, StructStats, structure_func};

mod decl;
mod expr;

#[cfg(test)]
mod tests;

use expr::fmt_loc;

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
    /// Append a `func_main_0.call(this);` call after the top-level
    /// functions so the module entry point actually executes (the d-P4
    /// recompile gate needs it: the abc entry is invoked by the VM, but
    /// JS source declares it). The `.call(this)` passes the emitted
    /// file's own top-level receiver — the VM binds a script main's
    /// `this` to the global object, and a plain call would rebind it to
    /// `undefined` under es2abc's strict functions (N74). Off by
    /// default — human-facing output stays clean.
    pub call_entry: bool,
    /// Reconstruct OpenHarmony ArkUI declarative `@Entry` / `@Component struct`
    /// definitions (`@State`, `@Prop`, `@Link`, `@Provide`, `@Consume`,
    /// `build() { ... }`) from `ets_loader`-lowered `ViewPU` / `View` classes
    /// (#26 Phase 3). Off by default so JS recompile gates stay pure ES.
    pub arkui: bool,
}

/// Emission counters (the corpus gate prints them verbatim).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

/// Maximum total functions (roots + transitive inline closures/methods)
/// materialized as [`PreparedFunc`] ASTs in a single parallel batch (`512`),
/// bounding peak AST memory even when each top-level `func_main_0` pulls in
/// dozens of inline class/closure bodies.
pub(crate) const MAX_BATCH_PREPARED_FUNCS: usize = 512;

/// Number of candidate functions scanned per parallel chunk during the
/// lightweight Stage-A orphan lexical-slot pass.
const ORPHAN_SCAN_BATCH: usize = 512;

/// Cap retained capacity of the reusable per-function string buffer (`1 MiB`)
/// so a single outlier function never pins a huge allocation across the run.
const MAX_RETAINED_FN_BUF: usize = 1024 * 1024;

/// Decompile a whole module to JS text.
pub fn decompile_module(module: &Module, opts: &EmitOptions) -> DecompiledModule {
    let mut buf = Vec::new();
    let stats = decompile_module_to_writer(module, opts, &mut buf).unwrap_or_default();
    let text = String::from_utf8(buf)
        .unwrap_or_else(|e| String::from_utf8_lossy(&e.into_bytes()).into_owned());
    DecompiledModule { text, stats }
}

/// Stream a decompiled module directly to `out` without buffering all function
/// ASTs or the full module source text in memory.
///
/// Top-level functions and their transitive inline functions (closures, class
/// constructors/methods, object-shape methods, and `--arkui` prototype methods)
/// are prepared in bounded parallel batches, emitted in deterministic
/// [`FuncId`] order, written per function to `out`, and immediately dropped.
/// Output bytes and [`DecompileStats`] are 100% identical to
/// [`decompile_module`].
pub fn decompile_module_to_writer<W: Write>(
    module: &Module,
    opts: &EmitOptions,
    out: &mut W,
) -> std::io::Result<DecompileStats> {
    // Consumed functions: closure bodies, class ctors, and every
    // MethodRef in the const pool (emitted inline, never top-level).
    let consumed = consumed_functions(module);
    let index = DecompileIndex::build(module);
    let orphan_names = collect_module_orphan_lexenv_names(module, &index);

    let mut em = Emitter {
        module,
        index: Some(&index),
        opts,
        stats: DecompileStats::default(),
        fn_names: Legalizer::new(),
        current_fn_has_fallback: false,
        current_kind: FunctionKind::Function,
        class_depth: 0,
        hoisted: BTreeSet::new(),
        prepared: BTreeMap::new(),
    };
    out.write_all(
        "// Decompiled by abcd-decompile (abcd-rs) — Stage B + emission v1.\n".as_bytes(),
    )?;
    out.write_all(
        "// Fallback honesty: `/* fallback Op … */` marks unrecoverable ops; `/* elided … */` marks deliberately dropped compiler guards.\n"
            .as_bytes(),
    )?;
    if opts.ts {
        out.write_all(
            "// TypeScript mode: annotations come from IR signatures (≤11-format files only, format fact #A7); functions without signatures keep bare parameter lists.\n"
                .as_bytes(),
        )?;
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
                let spec = render_sym_string(module, *module_request);
                em.fn_names.reserve(&local);
                if local == import {
                    writeln!(out, "import {{ {local} }} from {spec};")?;
                } else {
                    writeln!(out, "import {{ {import} as {local} }} from {spec};")?;
                }
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                let local = sanitize(&sym_str(module, *local_name));
                let spec = render_sym_string(module, *module_request);
                em.fn_names.reserve(&local);
                writeln!(out, "import * as {local} from {spec};")?;
            }
        }
    }

    // Global-binding name RESERVATION (the hoist itself is now
    // module-only — see below): `StoreGlobal`/`StoreGlobalRecord`/
    // `TryStoreGlobal` names must not collide with minted temporaries.
    // Module outputs still hoist `var name;` per name: undeclared
    // stores are an early error under es2abc's module mode (d-P4 — the
    // recompile gate found this: ReferenceError on every global store).
    // N72-C4: record stores (source-level `let`/`const`/`class` at
    // global scope) share this story — the module-scope `var` shadows
    // the global object inside the emitted module exactly like the
    // lexical record did (recover.rs `Stmt::GlobalStore` fold).
    let mut globals = BTreeSet::new();
    let mut record_globals = BTreeSet::new();
    for inst in &module.insts {
        match &inst.op {
            Op::StoreGlobal { name, .. } | Op::TryStoreGlobal { name, .. } => {
                let n = sanitize(&sym_str(module, *name));
                if globals.insert(n.clone()) {
                    em.fn_names.reserve(&n);
                }
            }
            Op::StoreGlobalRecord { name, .. } => {
                let n = sanitize(&sym_str(module, *name));
                if record_globals.insert(n.clone()) {
                    em.fn_names.reserve(&n);
                }
            }
            _ => {}
        }
    }
    for g in &globals {
        writeln!(out, "var {g};")?;
    }
    // N74 residual (decl-lex-configurable-global): a name stored ONLY
    // via StoreGlobalRecord is a source-level LEXICAL global
    // (let/const/class at script top level). A `var` hoist lowers to
    // `stglobalvar` under es2abc script mode — a REAL store that
    // clobbers a same-named configurable global-object property
    // (ark_js_vm overwrites it: `var Array;` made `this.Array` read
    // undefined). Hoist as `let` instead: `sttoglobalrecord`, the
    // declarative record — the global object stays untouched.
    for g in record_globals.difference(&globals) {
        writeln!(out, "let {g};")?;
    }
    // N74-W4: the hoisted `var` initializes the binding at module
    // evaluation, destroying the undeclared-read/TDZ windows (a sloppy
    // store creates the global AT the store; es2abc compiles function
    // bodies STRICT, so an undeclared STORE is itself a ReferenceError
    // — the hoist cannot simply be dropped, probe probe2.js). The
    // window is instead restored per-binding by
    // [`folds::late_decl_fold`], which converts the first root-level
    // store into the declaration (a function-scope `let` shadowing the
    // module `var`: reads before it throw the same ReferenceError).

    // Module-slot predeclarations (gap G2: `module_slot_names` resolves
    // the slot↔binding-name correspondence from file evidence — TDZ
    // guard names and stored definitions; evidence-free slots keep the
    // synthetic `m{index}` fallback). Declaring them at module scope
    // keeps the output strict-mode-parseable AND gives the trailing
    // `export { name }` records a binding to reference.
    let slot_names = &index.slot_names;
    let mut slots = BTreeSet::new();
    for inst in &module.insts {
        match &inst.op {
            Op::LoadModuleVar { index, .. } | Op::StoreModuleVar { index, .. } => {
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
        writeln!(out, "let {name};")?;
    }

    // Orphan lexical-slot predeclarations (G1; see
    // `orphan_lexenv_names_in_func`).
    for name in orphan_names {
        em.fn_names.reserve(&name);
        writeln!(out, "let {name}; /* orphan lexenv slot (G1) */")?;
    }

    // Top-level functions in bounded parallel batches.
    let top_funcs: Vec<FuncId> = (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .filter(|f| !consumed.contains(f))
        .collect();
    let mut entry_call: Option<String> = None;
    let mut fn_buf = String::new();
    let mut cursor = 0usize;
    while cursor < top_funcs.len() {
        let (take, batch_fids) =
            next_bounded_top_batch(module, &top_funcs[cursor..], MAX_BATCH_PREPARED_FUNCS);
        let chunk = &top_funcs[cursor..cursor + take];
        cursor += take;
        let prepared_batch: Vec<(FuncId, PreparedFunc)> = batch_fids
            .into_par_iter()
            .map(|fid| {
                let top_level = !consumed.contains(&fid);
                (fid, prepare_func_only(module, Some(&index), fid, top_level))
            })
            .collect();
        em.prepared = prepared_batch.into_iter().collect();

        for &f in chunk {
            fn_buf.clear();
            if opts.arkui
                && !opts.call_entry
                && module
                    .func(f)
                    .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
                && crate::arkui::try_emit_arkui_main(&mut em, f, &mut fn_buf)
            {
                out.write_all(fn_buf.as_bytes())?;
                if fn_buf.capacity() > MAX_RETAINED_FN_BUF {
                    fn_buf = String::new();
                }
                continue;
            }
            let emitted = em.emit_top_level_function(f, &mut fn_buf);
            if opts.call_entry && emitted.1 == "func_main_0" {
                entry_call = Some(emitted.0);
            }
            out.write_all(fn_buf.as_bytes())?;
            if fn_buf.capacity() > MAX_RETAINED_FN_BUF {
                fn_buf = String::new();
            }
        }
        // Drop any remaining ASTs in this batch (e.g. skipped synthetic ArkUI methods)
        // before starting the next batch.
        em.prepared.clear();
    }

    // The recompile gate: invoke the module entry point WITH the
    // script-level receiver. The VM binds a script main's `this` to
    // the global object at entry (ark sloppy script semantics; the
    // this-role frame slot, abcd_ir::frame) — a plain call would give
    // the wrapper `undefined` under es2abc's strict functions (N74:
    // test262 dream-gate class `top-level-this-undefined`). The
    // emitted file's own top-level `this` is exactly that receiver:
    // globalThis in a script, undefined in a module (matching module
    // semantics — the plain call already behaved correctly there).
    if let Some(name) = entry_call {
        writeln!(out, "{name}.call(this);")?;
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
                    writeln!(out, "export {{ {local} }};")?;
                } else {
                    writeln!(out, "export {{ {local} as {export} }};")?;
                }
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                let import = module_facing_name(&sym_str(module, *import_name));
                let export = module_facing_name(&sym_str(module, *export_name));
                let spec = render_sym_string(module, *module_request);
                writeln!(out, "export {{ {import} as {export} }} from {spec};")?;
            }
            ExportDecl::Star { module_request } => {
                let spec = render_sym_string(module, *module_request);
                writeln!(out, "export * from {spec};")?;
            }
        }
    }

    out.flush()?;
    Ok(em.stats)
}

/// A module-facing name (`export { x as NAME }`, `import { NAME as x
/// }`) is an IdentifierName, not a binding: reserved words are legal
/// (`as default` is THE default-export spelling). Keep valid
/// IdentifierNames verbatim; sanitize only genuinely broken shapes.
pub(crate) fn module_facing_name(raw: &str) -> String {
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
            Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                consumed.insert(cls.ctor);
                collect_method_refs(module, cls.members, &mut consumed);
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

/// Walk a pooled constant graph (iteratively via an explicit heap workstack and
/// visited-`ConstId` cycle guard) for `MethodRef` functions.
pub(in crate::emit) fn collect_method_refs(
    module: &Module,
    root_cid: abcd_ir::ConstId,
    out: &mut BTreeSet<FuncId>,
) {
    let mut visited: HashSet<abcd_ir::ConstId> = HashSet::new();
    if !visited.insert(root_cid) {
        return;
    }
    let mut stack: Vec<abcd_ir::ConstId> = vec![root_cid];
    while let Some(cid) = stack.pop() {
        let Some(c) = module.consts.get(cid) else {
            continue;
        };
        match c {
            Const::MethodRef(f) => {
                out.insert(*f);
            }
            Const::ArrayLiteral(items) => {
                for &i in items.iter().rev() {
                    if visited.insert(i) {
                        stack.push(i);
                    }
                }
            }
            Const::ObjectLiteral { keys, values } => {
                for &i in values.iter().rev().chain(keys.iter().rev()) {
                    if visited.insert(i) {
                        stack.push(i);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Try to insert `roots` and all inline functions transitively referenced from
/// them (`DefineFunc`, `DefineClass`/`DefineSendableClass` ctor & `MethodRef`
/// members, and `AllocObject` shape `MethodRef`s) into `visited` using an
/// explicit heap workstack and cycle guard.
///
/// When `abort_over` is `Some(limit)` and `visited.len()` exceeds `limit`,
/// rolls back every [`FuncId`] added by this call and returns `false` (leaving
/// `visited` untouched).
pub(crate) fn try_extend_batch_funcs(
    module: &Module,
    roots: &[FuncId],
    visited: &mut BTreeSet<FuncId>,
    abort_over: Option<usize>,
) -> bool {
    let mut added: Vec<FuncId> = Vec::new();
    let mut stack: Vec<FuncId> = Vec::new();
    let mut inline_refs = BTreeSet::new();

    for &r in roots {
        if visited.insert(r) {
            added.push(r);
            stack.push(r);
            if let Some(limit) = abort_over
                && visited.len() > limit
            {
                for f in added {
                    visited.remove(&f);
                }
                return false;
            }
        }
    }

    while let Some(fid) = stack.pop() {
        let Some(fd) = module.func(fid) else {
            continue;
        };
        for &bid in &fd.blocks {
            let Some(block) = module.block(bid) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::DefineFunc { body, .. } => {
                        if visited.insert(*body) {
                            added.push(*body);
                            stack.push(*body);
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if visited.insert(cls.ctor) {
                            added.push(cls.ctor);
                            stack.push(cls.ctor);
                        }
                        inline_refs.clear();
                        collect_method_refs(module, cls.members, &mut inline_refs);
                        for &m in &inline_refs {
                            if visited.insert(m) {
                                added.push(m);
                                stack.push(m);
                            }
                        }
                    }
                    Op::AllocObject { shape } => {
                        inline_refs.clear();
                        collect_method_refs(module, *shape, &mut inline_refs);
                        for &m in &inline_refs {
                            if visited.insert(m) {
                                added.push(m);
                                stack.push(m);
                            }
                        }
                    }
                    _ => {}
                }
                if let Some(limit) = abort_over
                    && visited.len() > limit
                {
                    for f in added {
                        visited.remove(&f);
                    }
                    return false;
                }
            }
        }
    }
    true
}

/// Collect `roots` plus every inline [`FuncId`] transitively referenced from
/// them in deterministic ascending [`FuncId`] order.
#[cfg(test)]
pub(crate) fn collect_batch_funcs(module: &Module, roots: &[FuncId]) -> Vec<FuncId> {
    let mut visited = BTreeSet::new();
    let _ = try_extend_batch_funcs(module, roots, &mut visited, None);
    visited.into_iter().collect()
}

/// Select a non-empty prefix `&top_funcs[..take]` (`take >= 1` whenever
/// `!top_funcs.is_empty()`) whose total transitive function set stays within
/// `max_prepared` functions (always taking at least `top_funcs[0]` even if that
/// single root transitively owns `> max_prepared` functions), returning
/// `(take, batch_fids)`.
pub(crate) fn next_bounded_top_batch(
    module: &Module,
    top_funcs: &[FuncId],
    max_prepared: usize,
) -> (usize, Vec<FuncId>) {
    let mut visited = BTreeSet::new();
    let mut take = 0usize;
    for (idx, &root) in top_funcs.iter().enumerate() {
        let limit = (idx > 0).then_some(max_prepared);
        if !try_extend_batch_funcs(module, &[root], &mut visited, limit) {
            break;
        }
        take = idx + 1;
        if visited.len() >= max_prepared {
            break;
        }
    }
    (take, visited.into_iter().collect())
}

pub(crate) struct Emitter<'m> {
    pub(crate) module: &'m Module,
    pub(crate) index: Option<&'m DecompileIndex>,
    pub(crate) opts: &'m EmitOptions,
    pub(crate) stats: DecompileStats,
    /// Module-scope name legalizer (top-level function names).
    pub(crate) fn_names: Legalizer,
    pub(crate) current_fn_has_fallback: bool,
    /// The kind of the function currently being emitted (`yield` is
    /// only printable inside generator kinds; in plain async functions
    /// the `SuspendGenerator` op is async machinery — R4).
    pub(crate) current_kind: FunctionKind,
    /// Nesting depth of class-body emission (private names are only
    /// printable `#x` inside a class body; es2abc's out-of-class
    /// instance initializers print the loud string-key fallback).
    pub(crate) class_depth: usize,
    /// Temporaries of the CURRENT function whose uses escape their
    /// declaration's structured block (JS `const`/`let`/`class` are
    /// block-scoped; SSA dominance is not block-aligned). They are
    /// hoisted: `var name;` at the function top, `name = value;` at
    /// the original site. (d-P4 dream gate: `ReferenceError: _funcObj$1
    /// is not defined` — a class declared inside a `try` block, used
    /// after it.)
    pub(crate) hoisted: BTreeSet<String>,
    /// Bounded batch of precomputed per-function Stage A + Stage B + Folds
    /// outputs. Entries are removed (never cloned) on first emission and
    /// dropped immediately after each function finishes emitting; the `< 0.1%`
    /// tail-duplicated inline closures re-run `prepare_func_only` on demand.
    pub(crate) prepared: BTreeMap<FuncId, PreparedFunc>,
}

#[derive(Clone)]
pub(crate) struct PreparedFunc {
    pub(crate) top_level: bool,
    pub(crate) rf: RecoveredFunc,
    pub(crate) body: Vec<SNode>,
    pub(crate) struct_stats: StructStats,
    pub(crate) fold_stats: FoldStats,
}

/// Whether `name` matches the synthetic unnamed-lexenv fallback shape
/// `v<digits>_<digits>`.
pub(crate) fn is_fallback_lexenv_name(name: &str) -> bool {
    let b = name.as_bytes();
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

/// Whether any resolved module/namespace slot name in `index` happens to have
/// the `v<digits>_<digits>` shape.
pub(crate) fn index_has_fallback_module_slot(index: &DecompileIndex) -> bool {
    if index
        .slot_names
        .values()
        .any(|n| is_fallback_lexenv_name(n))
    {
        return true;
    }
    if let Some(per_cls) = &index.per_class_env {
        for env in per_cls.values() {
            if env
                .external_slots
                .values()
                .chain(env.local_slots.values())
                .chain(env.namespace_slots.values())
                .any(|n| is_fallback_lexenv_name(n))
            {
                return true;
            }
        }
    }
    false
}

/// Sound prefilter for [`orphan_lexenv_names_in_func`]: returns `false` only
/// when Stage A recovery of `func` cannot possibly emit a `Stmt::LexStore` or
/// `Expr::Ident` matching `v<digits>_<digits>`.
pub(crate) fn func_may_have_orphan_lexenv(
    module: &Module,
    func: FuncId,
    index: &DecompileIndex,
    has_fallback_module_slot: bool,
) -> bool {
    let Some(fd) = module.func(func) else {
        return false;
    };
    if let Some(dbg) = &fd.debug {
        for &psym in &dbg.param_names {
            if is_fallback_lexenv_name(&sanitize(&sym_str(module, psym))) {
                return true;
            }
        }
        for ln in &dbg.local_names {
            if is_fallback_lexenv_name(&sanitize(&sym_str(module, ln.name))) {
                return true;
            }
        }
    }
    let mut has_lexvar = false;
    for &bid in &fd.blocks {
        let Some(block) = module.block(bid) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::GetLexVar { .. } | Op::PutLexVar { .. } => has_lexvar = true,
                Op::TryGetGlobal { name, .. } => {
                    if is_fallback_lexenv_name(&sanitize(&sym_str(module, *name))) {
                        return true;
                    }
                }
                Op::LoadModuleVar { .. } | Op::GetModuleNamespace { .. }
                    if has_fallback_module_slot =>
                {
                    return true;
                }
                _ => {}
            }
        }
    }
    if !has_lexvar {
        return false;
    }
    let scopes = crate::names::NameScopes::build_with_index(module, func, Some(index));
    if scopes.has_fallback_lexenv_name() {
        return true;
    }
    for &bid in &fd.blocks {
        let Some(block) = module.block(bid) else {
            continue;
        };
        for &iid in &block.insts {
            if let Some(inst) = module.inst(iid)
                && matches!(inst.op, Op::GetLexVar { .. } | Op::PutLexVar { .. })
                && scopes.name_of(iid).is_none()
            {
                return true;
            }
        }
    }
    false
}

/// Collect orphan lexenv names across `fids` in bounded parallel chunks,
/// running only Stage A on candidate functions and dropping each
/// [`RecoveredFunc`] immediately inside the worker closure.
pub(crate) fn collect_orphans_for_funcs(
    module: &Module,
    index: &DecompileIndex,
    fids: &[FuncId],
    has_fallback_module_slot: bool,
) -> BTreeSet<String> {
    let candidates: Vec<FuncId> = fids
        .par_iter()
        .copied()
        .filter(|&fid| func_may_have_orphan_lexenv(module, fid, index, has_fallback_module_slot))
        .collect();
    let mut orphan_names = BTreeSet::new();
    for chunk in candidates.chunks(ORPHAN_SCAN_BATCH) {
        let sets: Vec<BTreeSet<String>> = chunk
            .par_iter()
            .map(|&fid| {
                let rf = recover_func_with_index(module, fid, index);
                orphan_lexenv_names_in_func(&rf)
            })
            .collect();
        for s in sets {
            orphan_names.extend(s);
        }
    }
    orphan_names
}

/// Collect orphan lexenv names across the entire module without retaining
/// recovered ASTs.
pub(crate) fn collect_module_orphan_lexenv_names(
    module: &Module,
    index: &DecompileIndex,
) -> BTreeSet<String> {
    let has_fallback_slot = index_has_fallback_module_slot(index);
    let candidates: Vec<FuncId> = (0..module.functions.len())
        .into_par_iter()
        .map(|i| FuncId::new(i as u32))
        .filter(|&fid| func_may_have_orphan_lexenv(module, fid, index, has_fallback_slot))
        .collect();
    let mut orphan_names = BTreeSet::new();
    for chunk in candidates.chunks(ORPHAN_SCAN_BATCH) {
        let sets: Vec<BTreeSet<String>> = chunk
            .par_iter()
            .map(|&fid| {
                let rf = recover_func_with_index(module, fid, index);
                orphan_lexenv_names_in_func(&rf)
            })
            .collect();
        for s in sets {
            orphan_names.extend(s);
        }
    }
    orphan_names
}

/// Orphan lexical bindings (IR gap G1): unnamed lexenv slots get
/// fallback names `v{level}_{slot}`; when the slot's OWNING function
/// never stores to it textually (write-only-from-inner-closure), no
/// `let` is ever emitted and the capture is a free reference (dream
/// gate: for-update-continue-1, "v2_1 is not defined"). Declaring the
/// fallback names at module top is sound under textual nesting:
/// functions that DO declare the name shadow it locally.
pub(crate) fn orphan_lexenv_names_in_func(rf: &RecoveredFunc) -> BTreeSet<String> {
    fn walk_expr(root: &Expr, out: &mut BTreeSet<String>) {
        let mut stack: Vec<&Expr> = vec![root];
        while let Some(e) = stack.pop() {
            if let Expr::Ident(name) = e
                && is_fallback_lexenv_name(name)
            {
                out.insert(name.clone());
            }
            for c in crate::folds::expr_children(e).into_iter().rev() {
                stack.push(c);
            }
        }
    }
    let mut out = BTreeSet::new();
    for b in &rf.blocks {
        for st in &b.stmts {
            if let Stmt::LexStore { name, .. } = st {
                let clean = sanitize(name);
                if is_fallback_lexenv_name(&clean) {
                    out.insert(clean);
                }
            }
            for e in stmt_exprs(st) {
                walk_expr(e, &mut out);
            }
        }
    }
    out
}

fn finish_prepare(module: &Module, mut rf: RecoveredFunc, top_level: bool) -> PreparedFunc {
    let mut structured = structure_func(module, &rf);
    let mut fstats = FoldStats::default();
    folds::generator_machine_fold(&mut structured.body, rf.kind, &mut fstats);
    folds::async_driver_fold(&mut structured.body, rf.kind, &mut fstats);
    folds::async_machine_fold(&mut structured.body, rf.kind, &mut fstats);
    folds::async_generator_machine_fold(&mut structured.body, rf.kind, &mut fstats);
    folds::yield_star_fold(&mut structured.body, rf.kind, &mut fstats);
    folds::fold(&mut structured.body, &mut fstats);
    folds::scope_fold(&mut structured.body, &rf.params, &mut fstats);
    folds::late_decl_fold(&mut structured.body, &rf.params, top_level, &mut fstats);
    folds::rest_param_fold(
        &mut structured.body,
        &mut rf.params,
        rf.hidden_params,
        &mut fstats,
    );
    PreparedFunc {
        top_level,
        rf,
        body: structured.body,
        struct_stats: structured.stats,
        fold_stats: fstats,
    }
}

/// Pure per-function pipeline: Stage A → Stage B → folds (without orphan scan).
pub(crate) fn prepare_func_only(
    module: &Module,
    index: Option<&DecompileIndex>,
    func: FuncId,
    top_level: bool,
) -> PreparedFunc {
    let rf = match index {
        Some(idx) => recover_func_with_index(module, func, idx),
        None => recover_func(module, func),
    };
    finish_prepare(module, rf, top_level)
}

/// Pure per-function pipeline: Stage A → orphan scan → Stage B → folds.
pub(crate) fn prepare_func(
    module: &Module,
    index: Option<&DecompileIndex>,
    func: FuncId,
    top_level: bool,
) -> (PreparedFunc, BTreeSet<String>) {
    let rf = match index {
        Some(idx) => recover_func_with_index(module, func, idx),
        None => recover_func(module, func),
    };
    let orphans = orphan_lexenv_names_in_func(&rf);
    (finish_prepare(module, rf, top_level), orphans)
}

/// The full per-function pipeline: Stage A → Stage B → folds.
impl<'m> Emitter<'m> {
    /// Inspect (or prepare on-demand) `func` without consuming its batch slot.
    pub(crate) fn peek_prepared(&mut self, func: FuncId, top_level: bool) -> Cow<'_, PreparedFunc> {
        if !self.prepared.contains_key(&func) {
            let pre = prepare_func_only(self.module, self.index, func, top_level);
            self.prepared.insert(func, pre);
        }
        if let Some(p) = self.prepared.get(&func)
            && p.top_level == top_level
        {
            return Cow::Borrowed(p);
        }
        Cow::Owned(prepare_func_only(self.module, self.index, func, top_level))
    }

    /// Consume the precomputed Stage A → Stage B → folds output (removing it
    /// from `self.prepared` so its AST is freed immediately after emission), or
    /// recompute on demand for the `< 0.1%` tail-duplicated inline closures.
    pub(crate) fn func_nodes(
        &mut self,
        func: FuncId,
        top_level: bool,
    ) -> (RecoveredFunc, Vec<SNode>) {
        self.stats.function_bodies += 1;
        let p = match self.prepared.remove(&func) {
            Some(pre) if pre.top_level == top_level => pre,
            Some(other) => {
                self.prepared.insert(func, other);
                prepare_func_only(self.module, self.index, func, top_level)
            }
            None => prepare_func_only(self.module, self.index, func, top_level),
        };
        self.stats.structure =
            merge_struct_stats(std::mem::take(&mut self.stats.structure), &p.struct_stats);
        self.stats.folds = merge_fold_stats(std::mem::take(&mut self.stats.folds), &p.fold_stats);
        (p.rf, p.body)
    }
}

impl<'m> Emitter<'m> {
    // ── Statements ───────────────────────────────────────────────────

    fn emit_nodes(&mut self, nodes: &[SNode], indent: usize, out: &mut String) {
        for n in nodes {
            self.emit_node(n, indent, out);
        }
    }

    pub(crate) fn emit_node(&mut self, n: &SNode, indent: usize, out: &mut String) {
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

    pub(crate) fn emit_leaf(&mut self, l: &Leaf, indent: usize, out: &mut String) {
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
    pub(crate) fn emit_stmt(&mut self, s: &Stmt, indent: usize, out: &mut String) {
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
                    format!("[{}]", render_pool_string(self.module, name))
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
                    format!("[{}]", render_pool_string(self.module, name))
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
                        render_pool_string(self.module, name),
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
                    format!("globalThis[{}]", render_pool_string(self.module, name))
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
    pub(crate) fn estr(&mut self, e: &Expr) -> String {
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
                    stack.push(otherwise.iter());
                    stack.push(then.iter());
                }
                SNode::While { body, .. }
                | SNode::DoWhile { body, .. }
                | SNode::Labeled { body, .. }
                | SNode::ForOf { body, .. }
                | SNode::ForIn { body, .. } => {
                    stack.push(body.iter());
                }
                SNode::Try { body, catches, .. } => {
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
pub(in crate::emit) fn stmt_exprs(s: &Stmt) -> Vec<&Expr> {
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
        DoWhileCond(&'a Expr),
    }
    fn collect_uses(root: &Expr, pos: &Pos, uses: &mut Vec<(String, Pos)>) {
        let mut stack: Vec<&Expr> = vec![root];
        while let Some(e) = stack.pop() {
            if let Expr::Temp { name, .. } = e {
                uses.push((name.clone(), pos.clone()));
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
        uses: &mut Vec<(String, Pos)>,
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
                EscapeFrame::DoWhileCond(cond) => {
                    collect_uses(cond, &(path.clone(), usize::MAX, usize::MAX), uses);
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
                            // JS scope: the do-while condition is INSIDE the
                            // loop body's block (`do { const x … } while (x)`
                            // is legal), after the last body position.
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::PopPath);
                            frames.push(EscapeFrame::DoWhileCond(cond));
                            frames.push(EscapeFrame::EnterNodes {
                                nodes: body,
                                idx: 0,
                            });
                            frames.push(EscapeFrame::PushPath(0));
                            frames.push(EscapeFrame::PushPath(i));
                        }
                        SNode::Labeled { body, .. }
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
                        SNode::Try { body, catches, .. } => {
                            frames.push(EscapeFrame::PopPath);
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

pub(crate) fn merge_struct_stats(mut a: StructStats, b: &StructStats) -> StructStats {
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
    a.handler_tail_dups += b.handler_tail_dups;
    a.handler_tail_dup_blocks += b.handler_tail_dup_blocks;
    a.tower_deabsorbs += b.tower_deabsorbs;
    a.deabsorb_bails += b.deabsorb_bails;
    a.deabsorb_join_blocks += b.deabsorb_join_blocks;
    a.loop_cut_rewrites += b.loop_cut_rewrites;
    a.loop_cut_bails += b.loop_cut_bails;
    a
}

pub(crate) fn merge_fold_stats(mut a: FoldStats, b: &FoldStats) -> FoldStats {
    a.for_of += b.for_of;
    a.for_await_of += b.for_await_of;
    a.for_in += b.for_in;
    a.object_lit += b.object_lit;
    a.array_lit += b.array_lit;
    a.rest += b.rest;
    a.switch += b.switch;
    a.finally_fold += b.finally_fold;
    a.scope_fold += b.scope_fold;
    a.late_decl += b.late_decl;
    a.rest_param += b.rest_param;
    a.gen_driver_sites += b.gen_driver_sites;
    a.gen_driver_entry += b.gen_driver_entry;
    a.gen_driver_bound += b.gen_driver_bound;
    a.async_driver += b.async_driver;
    a.async_machine_sites += b.async_machine_sites;
    a.async_machine_bound += b.async_machine_bound;
    a.agen_entry += b.agen_entry;
    a.agen_yields += b.agen_yields;
    a.agen_bound += b.agen_bound;
    a.agen_awaits += b.agen_awaits;
    a.agen_await_bound += b.agen_await_bound;
    a.agen_returns += b.agen_returns;
    a.yield_star_sites += b.yield_star_sites;
    a.yield_star_bound += b.yield_star_bound;
    a.dead_exit_throw += b.dead_exit_throw;
    a
}
