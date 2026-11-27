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

fn scan_expr_inline_funcs(module: &Module, root: &Expr, out: &mut Vec<FuncId>) {
    let mut stack: Vec<&Expr> = vec![root];
    let mut mrefs = BTreeSet::new();
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::Closure { body, .. } => out.push(*body),
            Expr::Class { ctor, members, .. } => {
                out.push(*ctor);
                mrefs.clear();
                collect_method_refs(module, *members, &mut mrefs);
                out.extend(mrefs.iter().copied());
            }
            _ => {}
        }
        stack.extend(crate::folds::expr_children(cur));
    }
}

fn scan_stmt_inline_funcs(module: &Module, stmt: &Stmt, out: &mut Vec<FuncId>) {
    for e in stmt_exprs(stmt) {
        scan_expr_inline_funcs(module, e, out);
    }
}

fn scan_leaf_inline_funcs(module: &Module, leaf: &Leaf, out: &mut Vec<FuncId>) {
    match leaf {
        Leaf::Raw(s) => scan_stmt_inline_funcs(module, s, out),
        Leaf::Destructure { obj, .. } => scan_expr_inline_funcs(module, obj, out),
        Leaf::Decl { value: Some(v), .. } | Leaf::Assign { value: v, .. } => {
            scan_expr_inline_funcs(module, v, out);
        }
        Leaf::Decl { value: None, .. } => {}
    }
}

fn scan_nodes_inline_funcs(module: &Module, nodes: &[SNode], out: &mut Vec<FuncId>) {
    let mut stack: Vec<&[SNode]> = vec![nodes];
    while let Some(seq) = stack.pop() {
        for n in seq {
            match n {
                SNode::Stmts(leaves) => {
                    for l in leaves {
                        scan_leaf_inline_funcs(module, l, out);
                    }
                }
                SNode::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    scan_expr_inline_funcs(module, cond, out);
                    stack.push(otherwise);
                    stack.push(then);
                }
                SNode::While { cond, body, .. } => {
                    if let Some(c) = cond {
                        scan_expr_inline_funcs(module, c, out);
                    }
                    stack.push(body);
                }
                SNode::DoWhile { body, cond, .. } => {
                    scan_expr_inline_funcs(module, cond, out);
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
                    scan_expr_inline_funcs(module, iter, out);
                    stack.push(body);
                }
                SNode::ForIn { obj, body, .. } => {
                    scan_expr_inline_funcs(module, obj, out);
                    stack.push(body);
                }
                SNode::Switch { disc, cases } => {
                    scan_expr_inline_funcs(module, disc, out);
                    for c in cases.iter().rev() {
                        for t in &c.tests {
                            scan_expr_inline_funcs(module, t, out);
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
        let mut queue: Vec<FuncId> = Vec::new();
        match &root {
            PrintRoot::Nodes(s, _) => scan_nodes_inline_funcs(self.module, s, &mut queue),
            PrintRoot::Node(n, _) => {
                scan_nodes_inline_funcs(self.module, std::slice::from_ref(*n), &mut queue);
            }
            PrintRoot::Leaf(l, _) => scan_leaf_inline_funcs(self.module, l, &mut queue),
            PrintRoot::Stmt(s, _) => scan_stmt_inline_funcs(self.module, s, &mut queue),
            PrintRoot::Expr(e, _) => scan_expr_inline_funcs(self.module, e, &mut queue),
            PrintRoot::ClassMethod { func, .. } => queue.push(*func),
        }

        let mut inline_pool: BTreeMap<FuncId, PreparedFunc> = BTreeMap::new();
        while let Some(fid) = queue.pop() {
            if self.emitting_funcs.contains(&fid) || inline_pool.contains_key(&fid) {
                continue;
            }
            let pre = self.take_or_prepare_inline(fid);
            scan_nodes_inline_funcs(self.module, &pre.body, &mut queue);
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
                            out.push_str(&format!(
                                "{pad}  const {b} = {primary_binding}; /* merged typed-catch binding */\n"
                            ));
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
                        if !rest.is_empty() {
                            tasks.push(PrintTask::ExtraCatches {
                                catches: rest,
                                primary_binding: binding.clone(),
                                indent,
                            });
                        }
                        tasks.push(PrintTask::Nodes {
                            slice: &first.body,
                            indent: indent + 1,
                        });
                        tasks.push(PrintTask::RawOwned(format!(
                            "{pad}}} catch ({binding}) {{\n"
                        )));
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
