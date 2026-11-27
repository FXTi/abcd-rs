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
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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

mod stmt;
#[cfg(test)]
mod tests;

use expr::fmt_loc;

pub(in crate::emit) use stmt::{InlineHeaderStyle, PrintRoot, PrintTask, escaped_temps};
pub(crate) use stmt::{lex_decls, stmt_exprs};

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

/// Maximum total deduplicated instruction weight (`sum` of per-function
/// `block.insts.len().max(1)`) materialized as [`PreparedFunc`] ASTs in a
/// single parallel batch (`65,536`), preventing giant functions (`10k+`
/// instructions each) from pinning millions of AST nodes simultaneously while
/// allowing small getters/closures to batch efficiently up to
/// [`MAX_BATCH_PREPARED_FUNCS`].
pub(crate) const MAX_BATCH_PREPARED_INSTS: usize = 65_536;

/// Secondary cap on total deduplicated functions (roots + transitive inline
/// closures/methods) materialized as [`PreparedFunc`] ASTs in a single
/// parallel batch (`512`).
pub(crate) const MAX_BATCH_PREPARED_FUNCS: usize = 512;

/// Instruction-weight and function-count budget for parallel [`PreparedFunc`]
/// batching.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BatchLimits {
    pub(crate) max_insts: usize,
    pub(crate) max_funcs: usize,
}

impl Default for BatchLimits {
    fn default() -> Self {
        Self {
            max_insts: MAX_BATCH_PREPARED_INSTS,
            max_funcs: MAX_BATCH_PREPARED_FUNCS,
        }
    }
}

/// Number of candidate functions scanned per parallel chunk during the
/// lightweight Stage-A orphan lexical-slot pass.
pub(crate) const ORPHAN_SCAN_BATCH: usize = 512;

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

/// Test-only helper exposing [`decompile_module`] with custom [`BatchLimits`].
#[cfg(test)]
pub(crate) fn decompile_module_with_limits(
    module: &Module,
    opts: &EmitOptions,
    limits: BatchLimits,
) -> DecompiledModule {
    let mut buf = Vec::new();
    let stats =
        decompile_module_to_writer_with_limits(module, opts, limits, &mut buf).unwrap_or_default();
    let text = String::from_utf8(buf)
        .unwrap_or_else(|e| String::from_utf8_lossy(&e.into_bytes()).into_owned());
    DecompiledModule { text, stats }
}

/// Stream a decompiled module directly to `out` without buffering all function
/// ASTs or the full module source text in memory.
///
/// Top-level functions and their transitive inline functions (closures, class
/// constructors/methods, object-shape methods, and `--arkui` prototype methods)
/// are prepared in bounded parallel batches (`65,536` deduplicated instructions /
/// `512` functions), emitted in deterministic [`FuncId`] order, written per
/// function to `out`, and immediately dropped. Output bytes and
/// [`DecompileStats`] are 100% identical to [`decompile_module`].
pub fn decompile_module_to_writer<W: Write>(
    module: &Module,
    opts: &EmitOptions,
    out: &mut W,
) -> std::io::Result<DecompileStats> {
    decompile_module_to_writer_with_limits(module, opts, BatchLimits::default(), out)
}

pub(crate) fn decompile_module_to_writer_with_limits<W: Write>(
    module: &Module,
    opts: &EmitOptions,
    limits: BatchLimits,
    out: &mut W,
) -> std::io::Result<DecompileStats> {
    // Consumed functions: closure bodies, class ctors, and every
    // MethodRef in the const pool (emitted inline, never top-level).
    let consumed = consumed_functions(module);
    let inst_weights = precompute_func_inst_weights(module);
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
        emitting_funcs: HashSet::new(),
        arkui_components: HashMap::new(),
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

    let slot_names = &index.slot_names;
    let record_env = index
        .per_class_env
        .as_ref()
        .and_then(|m| m.get(&abcd_ir::ClassId::new(0)));

    // Imports (1:1 enum mapping, plus side-effect-only module requests in exact
    // `[[RequestedModules]]` index order).
    let mut import_buf = String::new();
    emit_esm_imports(
        module,
        &module.imports,
        &module.exports,
        &module.module_requests,
        record_env.map(|env| env.import_locals.as_slice()),
        &mut em.fn_names,
        &|spec| render_sym_string(module, spec),
        &mut import_buf,
    );
    out.write_all(import_buf.as_bytes())?;

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
    let mut local_slots = BTreeSet::new();
    let mut unresolved_ns_slots = BTreeSet::new();
    for inst in &module.insts {
        match &inst.op {
            Op::LoadModuleVar {
                index: sidx,
                kind:
                    abcd_ir::ModuleVarKind::Local
                    | abcd_ir::ModuleVarKind::SendableLocal
                    | abcd_ir::ModuleVarKind::SendableClass,
            }
            | Op::StoreModuleVar { index: sidx, .. } => {
                local_slots.insert(*sidx);
            }
            Op::GetModuleNamespace { index: ns_idx }
                if record_env
                    .and_then(|env| env.namespace_slots.get(ns_idx))
                    .is_none() =>
            {
                unresolved_ns_slots.insert(*ns_idx);
            }
            _ => {}
        }
    }
    let mut declared_module_locals = BTreeSet::new();
    for s in &local_slots {
        let name = record_env
            .and_then(|env| env.local_slots.get(s))
            .or_else(|| slot_names.get(s))
            .cloned()
            .unwrap_or_else(|| crate::names::module_slot_fallback(*s));
        em.fn_names.reserve(&name);
        if declared_module_locals.insert(name.clone()) {
            writeln!(out, "let {name};")?;
        }
    }
    for ns_idx in &unresolved_ns_slots {
        let name = crate::names::namespace_fallback(*ns_idx);
        em.fn_names.reserve(&name);
        if declared_module_locals.insert(name.clone()) {
            writeln!(out, "let {name};")?;
        }
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
            next_bounded_top_batch(module, &inst_weights, &top_funcs[cursor..], limits);
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
            if opts.arkui {
                crate::arkui::precompute_arkui_components(&mut em, f);
            }
            if opts.arkui
                && !opts.call_entry
                && module
                    .func(f)
                    .is_some_and(|fd| sym_str(module, fd.name) == "func_main_0")
                && crate::arkui::try_emit_arkui_main(&mut em, f, &mut fn_buf)
            {
                em.arkui_components.clear();
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
            if opts.arkui {
                em.arkui_components.clear();
            }
            out.write_all(fn_buf.as_bytes())?;
            if fn_buf.capacity() > MAX_RETAINED_FN_BUF {
                fn_buf = String::new();
            }
        }
        // Drop any remaining ASTs in this batch (e.g. skipped synthetic ArkUI methods)
        // before starting the next batch.
        em.prepared.clear();
        em.arkui_components.clear();
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
                let local = resolve_export_local_ident(
                    module,
                    &module.exports,
                    record_env,
                    &sym_str(module, *local_name),
                );
                let export = module_facing_name(module, &sym_str(module, *export_name));
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
                let import = module_facing_name(module, &sym_str(module, *import_name));
                let export = module_facing_name(module, &sym_str(module, *export_name));
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

/// Emit ES `import` declarations and side-effect-only `import "spec";` requests
/// in exact `module_requests` (`[[RequestedModules]]`) evaluation order, using
/// `import_locals` to disambiguate any import bindings colliding with module-top
/// declarations (`import { foo as foo$1 }`).
#[allow(
    clippy::too_many_arguments,
    reason = "ESM import emitter coordinates module pool, import/export/request slices, disambiguated locals, legalizer, and specifier formatter"
)]
pub(crate) fn emit_esm_imports(
    module: &Module,
    imports: &[ImportDecl],
    exports: &[ExportDecl],
    module_requests: &[abcd_ir::module::ModuleRequest],
    import_locals: Option<&[String]>,
    fn_names: &mut Legalizer,
    resolve_spec: &dyn Fn(abcd_ir::Sym) -> String,
    out: &mut String,
) {
    let mut indirect_or_star = HashSet::new();
    for exp in exports {
        match exp {
            ExportDecl::Indirect { module_request, .. } | ExportDecl::Star { module_request } => {
                indirect_or_star.insert(*module_request);
            }
            ExportDecl::Local { .. } => {}
        }
    }

    let emit_one_import =
        |imp_idx: usize, imp: &ImportDecl, fn_names: &mut Legalizer, out: &mut String| match imp {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                let local = import_locals
                    .and_then(|v| v.get(imp_idx))
                    .cloned()
                    .unwrap_or_else(|| sanitize(&sym_str(module, *local_name)));
                let import = module_facing_name(module, &sym_str(module, *import_name));
                let spec = resolve_spec(*module_request);
                fn_names.reserve(&local);
                if import == "default" && is_legal_ident(&local) {
                    out.push_str(&format!("import {local} from {spec};\n"));
                } else if local == import && is_legal_ident(&local) {
                    out.push_str(&format!("import {{ {local} }} from {spec};\n"));
                } else {
                    out.push_str(&format!("import {{ {import} as {local} }} from {spec};\n"));
                }
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                let local = import_locals
                    .and_then(|v| v.get(imp_idx))
                    .cloned()
                    .unwrap_or_else(|| sanitize(&sym_str(module, *local_name)));
                let spec = resolve_spec(*module_request);
                fn_names.reserve(&local);
                out.push_str(&format!("import * as {local} from {spec};\n"));
            }
        };

    let mut emitted_imp = vec![false; imports.len()];
    let mut seen_req_specs = HashSet::new();
    for req in module_requests {
        if !seen_req_specs.insert(req.specifier) {
            continue;
        }
        let mut matched_any = false;
        for (imp_idx, imp) in imports.iter().enumerate() {
            let req_sym = match imp {
                ImportDecl::Regular { module_request, .. }
                | ImportDecl::Namespace { module_request, .. } => *module_request,
            };
            if req_sym == req.specifier {
                matched_any = true;
                emitted_imp[imp_idx] = true;
                emit_one_import(imp_idx, imp, fn_names, out);
            }
        }
        if !matched_any && !indirect_or_star.contains(&req.specifier) {
            let spec = resolve_spec(req.specifier);
            out.push_str(&format!("import {spec};\n"));
        }
    }

    for (imp_idx, imp) in imports.iter().enumerate() {
        if !emitted_imp[imp_idx] {
            emit_one_import(imp_idx, imp, fn_names, out);
        }
    }
}

/// A module-facing name (`export { x as NAME }`, `import { NAME as x }`) is an
/// ES2022 `ModuleExportName` (`IdentifierName` or `StringLiteral`): reserved
/// words are legal unquoted (`as default`), and non-identifier names emit as
/// quoted string literals (`export { x as "a-b" }`) rather than mangling the
/// public export contract.
pub(crate) fn module_facing_name(module: &Module, raw: &str) -> String {
    if crate::legalize::is_ident_name(raw) {
        raw.to_string()
    } else {
        render_pool_string(module, raw)
    }
}

/// Resolve an `ExportDecl::Local` binding's emitted identifier: when `raw_local`
/// is a compiler-synthetic default export tag (such as `*default*`) whose local
/// module slot already resolved to a concrete binding in `record_env`, bind the
/// export clause to that resolved slot identifier instead of declaring a second
/// uninitialized `let _default_;`.
pub(crate) fn resolve_export_local_ident(
    module: &Module,
    exports: &[ExportDecl],
    record_env: Option<&crate::names::RecordModuleEnv>,
    raw_local: &str,
) -> String {
    let sanitized = sanitize(raw_local);
    let Some(env) = record_env else {
        return sanitized;
    };
    if env.local_slots.values().any(|v| v == &sanitized) {
        return sanitized;
    }
    let mut distinct_locals = Vec::new();
    let mut seen = BTreeSet::new();
    let mut all_sanitized = BTreeSet::new();
    for exp in exports {
        if let ExportDecl::Local { local_name, .. } = exp {
            let r = sym_str(module, *local_name);
            all_sanitized.insert(sanitize(&r));
            if seen.insert(r.clone()) {
                distinct_locals.push(r);
            }
        }
    }
    if let Some(slot_idx) = distinct_locals.iter().position(|r| r == raw_local)
        && let Some(resolved) = env.local_slots.get(&(slot_idx as u32))
        && !all_sanitized.contains(resolved)
    {
        return resolved.clone();
    }
    sanitized
}

/// The functions a module emits INLINE (closure bodies, class ctors,
/// and MethodRefs in DefineClass member buffers) — everything else
/// emits top-level. Self-referential `DefineFunc(f)` inside `f` and
/// unreachable mutual `DefineFunc` cycles keep a deterministic cycle-entry
/// root top-level so no function is ever dropped (`#87.5`).
pub fn consumed_functions(module: &Module) -> std::collections::BTreeSet<FuncId> {
    let n = module.functions.len();
    let mut block_owner: std::collections::HashMap<abcd_ir::BlockId, FuncId> =
        std::collections::HashMap::new();
    for (fi, fd) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        for &bid in &fd.blocks {
            block_owner.entry(bid).or_insert(fid);
        }
    }

    let mut edges: Vec<BTreeSet<FuncId>> = vec![BTreeSet::new(); n];
    let mut orphan_consumed: BTreeSet<FuncId> = BTreeSet::new();
    let mut tmp_refs: BTreeSet<FuncId> = BTreeSet::new();

    for inst in &module.insts {
        tmp_refs.clear();
        match &inst.op {
            Op::DefineFunc { body, .. } => {
                tmp_refs.insert(*body);
            }
            Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                tmp_refs.insert(cls.ctor);
                collect_method_refs(module, cls.members, &mut tmp_refs);
            }
            Op::AllocObject { shape } => {
                collect_method_refs(module, *shape, &mut tmp_refs);
            }
            _ => continue,
        }
        if let Some(&owner) = block_owner.get(&inst.block) {
            for &target in &tmp_refs {
                if target != owner && target.index() < n {
                    edges[owner.index()].insert(target);
                } else if target.index() >= n {
                    orphan_consumed.insert(target);
                }
            }
        } else {
            orphan_consumed.extend(tmp_refs.iter().copied());
        }
    }

    let mut in_degree = vec![0usize; n];
    for children in &edges {
        for &c in children {
            in_degree[c.index()] += 1;
        }
    }

    let mut consumed: BTreeSet<FuncId> = orphan_consumed.clone();
    let mut visited = vec![false; n];
    let mut stack: Vec<FuncId> = Vec::new();

    for &oc in &orphan_consumed {
        if oc.index() < n && !visited[oc.index()] {
            visited[oc.index()] = true;
            stack.push(oc);
        }
    }
    for (fi, &deg) in in_degree.iter().enumerate() {
        if deg == 0 && !visited[fi] {
            visited[fi] = true;
            stack.push(FuncId::new(fi as u32));
        }
    }

    let drain_stack =
        |stack: &mut Vec<FuncId>, visited: &mut [bool], consumed: &mut BTreeSet<FuncId>| {
            while let Some(cur) = stack.pop() {
                let Some(children) = edges.get(cur.index()) else {
                    continue;
                };
                for &child in children {
                    let ci = child.index();
                    if ci < n && !visited[ci] {
                        visited[ci] = true;
                        consumed.insert(child);
                        stack.push(child);
                    }
                }
            }
        };

    drain_stack(&mut stack, &mut visited, &mut consumed);

    // Any remaining unvisited functions belong to pure inline cycles with no
    // external non-cycle parent: keep the smallest `FuncId` of each component
    // top-level (`!consumed`) and mark the rest `consumed`.
    for fi in 0..n {
        if !visited[fi] {
            visited[fi] = true;
            stack.push(FuncId::new(fi as u32));
            drain_stack(&mut stack, &mut visited, &mut consumed);
        }
    }

    consumed
}

/// Walk a pooled constant graph (iteratively via an explicit heap workstack and
/// visited-`ConstId` cycle guard) for `MethodRef` functions.
pub(crate) fn collect_method_refs(
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
            Const::MethodRef { func, .. } => {
                out.insert(*func);
            }
            Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
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
            Const::LiteralBufferRef(inner) if visited.insert(*inner) => {
                stack.push(*inner);
            }
            _ => {}
        }
    }
}

/// Compute the instruction weight of `fid` (`sum` of `block.insts.len().max(1)`
/// across `fd.blocks`, minimum `1` for valid functions and `0` for foreign/invalid
/// [`FuncId`]s).
pub(crate) fn func_inst_weight(module: &Module, fid: FuncId) -> usize {
    let Some(fd) = module.func(fid) else {
        return 0;
    };
    let mut total = 0usize;
    for &bid in &fd.blocks {
        let w = module.block(bid).map_or(1, |b| b.insts.len().max(1));
        total = total.saturating_add(w);
    }
    total.max(1)
}

/// Precompute [`func_inst_weight`] for every function in `module` into a dense
/// `Vec<u32>` of length `module.functions.len()`.
pub(crate) fn precompute_func_inst_weights(module: &Module) -> Vec<u32> {
    (0..module.functions.len())
        .map(|i| func_inst_weight(module, FuncId::new(i as u32)).min(u32::MAX as usize) as u32)
        .collect()
}

#[inline]
fn cached_inst_weight(inst_weights: &[u32], fid: FuncId) -> usize {
    inst_weights.get(fid.index()).copied().unwrap_or(0) as usize
}

/// Try to insert `roots` and all inline functions transitively referenced from
/// them (`DefineFunc`, `DefineClass`/`DefineSendableClass` ctor & `MethodRef`
/// members, and `AllocObject` shape `MethodRef`s) into `visited` using an
/// explicit heap workstack and cycle guard, accumulating newly admitted
/// instruction weights from `inst_weights` into `batch_inst_weight`.
///
/// Functions already present in `visited` are skipped without re-walking their
/// bodies or double-counting their weight. When `abort_over` is `Some(limits)`
/// and `visited.len() > limits.max_funcs || *batch_inst_weight > limits.max_insts`,
/// rolls back every [`FuncId`] added by this call, restores `*batch_inst_weight`,
/// and returns `false` (leaving `visited` and `*batch_inst_weight` untouched).
pub(crate) fn try_extend_batch_funcs(
    module: &Module,
    inst_weights: &[u32],
    roots: &[FuncId],
    visited: &mut BTreeSet<FuncId>,
    batch_inst_weight: &mut usize,
    abort_over: Option<BatchLimits>,
) -> bool {
    let orig_weight = *batch_inst_weight;
    let mut added_weight = 0usize;
    let mut added: Vec<FuncId> = Vec::new();
    let mut stack: Vec<FuncId> = Vec::new();
    let mut inline_refs = BTreeSet::new();

    let exceeds = |visited_len: usize, cur_weight: usize| -> bool {
        abort_over.is_some_and(|lim| visited_len > lim.max_funcs || cur_weight > lim.max_insts)
    };

    for &r in roots {
        if visited.insert(r) {
            added.push(r);
            stack.push(r);
            added_weight = added_weight.saturating_add(cached_inst_weight(inst_weights, r));
            let cur_weight = orig_weight.saturating_add(added_weight);
            if exceeds(visited.len(), cur_weight) {
                for f in added {
                    visited.remove(&f);
                }
                *batch_inst_weight = orig_weight;
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
                            added_weight = added_weight
                                .saturating_add(cached_inst_weight(inst_weights, *body));
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if visited.insert(cls.ctor) {
                            added.push(cls.ctor);
                            stack.push(cls.ctor);
                            added_weight = added_weight
                                .saturating_add(cached_inst_weight(inst_weights, cls.ctor));
                        }
                        inline_refs.clear();
                        collect_method_refs(module, cls.members, &mut inline_refs);
                        for &m in &inline_refs {
                            if visited.insert(m) {
                                added.push(m);
                                stack.push(m);
                                added_weight = added_weight
                                    .saturating_add(cached_inst_weight(inst_weights, m));
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
                                added_weight = added_weight
                                    .saturating_add(cached_inst_weight(inst_weights, m));
                            }
                        }
                    }
                    _ => {}
                }
                let cur_weight = orig_weight.saturating_add(added_weight);
                if exceeds(visited.len(), cur_weight) {
                    for f in added {
                        visited.remove(&f);
                    }
                    *batch_inst_weight = orig_weight;
                    return false;
                }
            }
        }
    }
    *batch_inst_weight = orig_weight.saturating_add(added_weight);
    true
}

/// Collect `roots` plus every inline [`FuncId`] transitively referenced from
/// them in deterministic ascending [`FuncId`] order.
#[cfg(test)]
pub(crate) fn collect_batch_funcs(module: &Module, roots: &[FuncId]) -> Vec<FuncId> {
    let inst_weights = precompute_func_inst_weights(module);
    let mut visited = BTreeSet::new();
    let mut weight = 0usize;
    let _ = try_extend_batch_funcs(
        module,
        &inst_weights,
        roots,
        &mut visited,
        &mut weight,
        None,
    );
    visited.into_iter().collect()
}

/// Select a non-empty prefix `&top_funcs[..take]` (`take >= 1` whenever
/// `!top_funcs.is_empty()`) whose deduplicated transitive function set stays
/// within `limits` (`max_insts` and `max_funcs`), always taking at least
/// `top_funcs[0]` even if that single root + its transitive inline closures
/// exceed `limits`, returning `(take, batch_fids)`.
pub(crate) fn next_bounded_top_batch(
    module: &Module,
    inst_weights: &[u32],
    top_funcs: &[FuncId],
    limits: BatchLimits,
) -> (usize, Vec<FuncId>) {
    let mut visited = BTreeSet::new();
    let mut batch_inst_weight = 0usize;
    let mut take = 0usize;
    for (idx, &root) in top_funcs.iter().enumerate() {
        let cap = (idx > 0).then_some(limits);
        if !try_extend_batch_funcs(
            module,
            inst_weights,
            &[root],
            &mut visited,
            &mut batch_inst_weight,
            cap,
        ) {
            break;
        }
        take = idx + 1;
        if visited.len() >= limits.max_funcs || batch_inst_weight >= limits.max_insts {
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
    /// Active function emission stack to break cyclic `DefineFunc` / `MethodRef`
    /// inline chains without stack overflow (`#87.5`).
    pub(crate) emitting_funcs: HashSet<FuncId>,
    /// Precomputed `@Component struct` outputs keyed by `(ctor, var_name)` so
    /// [`Emitter::step_start_class`] never calls back into `crate::arkui`.
    pub(crate) arkui_components: HashMap<(FuncId, String), (String, DecompileStats, bool)>,
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
                Op::TryGetGlobal { name, .. }
                    if is_fallback_lexenv_name(&sanitize(&sym_str(module, *name))) =>
                {
                    return true;
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

pub(crate) fn accumulate_decompile_stats(dst: &mut DecompileStats, src: &DecompileStats) {
    dst.functions += src.functions;
    dst.functions_with_fallbacks += src.functions_with_fallbacks;
    for (&k, &v) in &src.fallback_comments {
        *dst.fallback_comments.entry(k).or_insert(0) += v;
    }
    for (&k, &v) in &src.elided_comments {
        *dst.elided_comments.entry(k).or_insert(0) += v;
    }
    dst.classes += src.classes;
    dst.class_methods += src.class_methods;
    dst.closures += src.closures;
    dst.structure = merge_struct_stats(std::mem::take(&mut dst.structure), &src.structure);
    dst.folds = merge_fold_stats(std::mem::take(&mut dst.folds), &src.folds);
    dst.function_bodies += src.function_bodies;
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
