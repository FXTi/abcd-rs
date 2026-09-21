//! Function inlining for the v0.2 IR — the D2 (maintainer ruling
//! 2026-09-21) rewrite of v0.1's quarantined inline pass (N44), built
//! on [`abcd_ir2::Module`]. **Opt-in only**: nothing here is wired into
//! [`crate::optimize_module`]; the corpus gates (v2lift/v2opt
//! byte-identity and the VM oracle) stay untouched. Callers opt in via
//! [`inline_module`].
//!
//! ## Why v0.1 failed, and how this construction kills N44
//!
//! v0.1's inline produced module-INVALID IR: callee parameters were
//! left unmapped, call-site predecessors were not rebuilt, and try
//! regions were lost (4 structural verifier errors on one inline; the
//! red proof on the v0.2 IR lives in `abcd-opt/tests/opt_inline_red.rs`).
//! This rewrite kills each defect by construction:
//!
//! - **Fresh identities**: the callee CFG is cloned with FRESH
//!   `ValueId`s/`InstId`s/`BlockId`s (arena append — no id reuse, T1).
//! - **Parameter mapping** (`bind_params`): callee `params` are bound
//!   to call-site operands per the §5.3 [`CallKind`] table — `this`
//!   (T4: `params[0]` for non-static callees), formals in order,
//!   missing formals bound to a pooled `undefined` constant, extra
//!   arguments dropped (the callee cannot observe them: `arguments`
//!   users are ineligible).
//! - **Predecessor rebuild** (`inline_site` steps E–H): the call block
//!   is split at the call; the continuation block inherits the moved
//!   terminator, EVERY old Normal successor's preds and phi entries are
//!   re-keyed from the call block to the continuation, and the callee's
//!   `Return`s become branches into the continuation, whose value
//!   replaces the call result (directly for a single return, through a
//!   phi for several).
//! - **Exception semantics** (step H): v0.2's first-class
//!   [`EdgeKind::Exceptional`] edges make the rule expressible — see
//!   below.
//!
//! ## The exception-edge rule (hard contract)
//!
//! The VM dispatches exceptions by PC range: a throw anywhere inside a
//! called function whose call site sits in a try range lands in the
//! caller's handler, with the caller's register file exactly as it was
//! at the call (the callee had its own frame). After inlining, the
//! callee's temporaries live in fresh registers and the caller's
//! registers are still untouched, so:
//!
//! > If the call block is protected by a caller try region, EVERY
//! > cloned callee block and the continuation block join that region's
//! > `protected` set (not just blocks containing potentially-throwing
//! > instructions — the effects table deliberately does not model
//! > coercion throws, design/ir-v0.2.md §4.4, and VM dispatch is by PC
//! > range, not instruction kind). Every catch handler of the region
//! > gains an `EdgeKind::Exceptional` pred from each new protected
//! > block, and every handler phi gains an entry for each new edge
//! > carrying THE SAME value as the entry the original call block's
//! > exceptional edge carried (the register state visible at the call —
//! > the v0.2 model's block-granular imprecision, N38, is preserved
//! > exactly, neither narrowed nor widened).
//!
//! Callees with their OWN try regions are ineligible in this first
//! iteration (`SkipReason::CalleeHasTryRegions`); widening requires
//! remapping their catches with fresh `ExceptionParam` values.
//!
//! ## Eligibility (conservative; widen only with evidence)
//!
//! A call site is eligible iff ALL of the following hold:
//!
//! - `CallKind::Direct` or `CallKind::Dynamic` (the only kinds whose
//!   argument binding is statically known; `New` needs an
//!   OrdinaryCreateFromConstructor op the IR does not have — see the
//!   `new.target` note below — and `Apply`/`Super*` spread or inherit
//!   their arguments).
//! - The callee value resolves through `AllocClosure` → `DefineFunc` to
//!   a same-module [`FuncId`] with a body (`resolve_callee`).
//! - Not a self-call (recursion; mutual recursion is bounded by
//!   construction — each function is processed once and freshly cloned
//!   call sites are never revisited, so the pass terminates).
//! - The callee is a plain [`FunctionKind::Function`], has no try
//!   regions, and its entry block has no predecessors (a self-loop
//!   entry would need extra phi entries for the call block's edge).
//! - The callee uses none of: lexical-environment ops (`GetLexVar`/
//!   `PutLexVar`/`NewLexEnv*`/`PopLexEnv` — env identity changes across
//!   inlining), private-name ops (env level/slot addressing), `arguments`
//!   (`GetUnmappedArgs`/`CopyRestArgs` — the caller's arguments object
//!   is a different object), `LoadFunction` (function identity),
//!   super ops (home-object/`this` context), suspend ops
//!   (`Await`/`SuspendGenerator`/… — the caller is not the callee's
//!   async/generator frame), or nested definitions whose transitive
//!   bodies read or mutate the lexical environment they would capture
//!   (`DefineFunc`/`DefineClass`/`DefineSendableClass` — a nested
//!   closure's captured env is the callee's frame env, not the
//!   caller's; env-observability is decided by
//!   `nested_definitions_read_outer_env`, so callees that merely CALL
//!   other known functions still inline).
//! - `this` is bindable: `this: Some(v)` at the call site binds the
//!   callee's `this` param to `v` (both `Direct` and `Dynamic`+`Some`
//!   — the `callthis*` family); `this: None` requires the callee to
//!   never USE its `this` param (a `Dynamic` callee computes `this`
//!   from its own strictness, which the IR cannot prove).
//! - Size caps: the callee has at most [`InlinePolicy::max_callee_insts`]
//!   instructions and the caller's per-function inlined-instruction
//!   budget ([`InlinePolicy::max_inlined_insts_per_caller`]) is not
//!   exhausted.
//!
//! ## `new.target` (T4)
//!
//! `LoadNewTarget` in the callee is BOUND per call kind, never left
//! dangling: `Direct`/`Dynamic` → a pooled `undefined` constant (the
//! §5.3 table: `new.target` is undefined outside construction); `New`
//! → the call-site callee value. `New` call sites are currently always
//! ineligible (the `new` result-override semantics — a constructor
//! returning a non-object yields the fresh `this`, which no op can
//! materialize), so the `New` arm is exercised by the binding-table
//! unit test and by skip statistics; the `Direct`/`Dynamic` arm is
//! exercised end-to-end.
//!
//! ## Loc fidelity (design §7)
//!
//! Cloned instructions keep their source [`Loc`](abcd_ir2::Loc)s
//! verbatim. Glue instructions created by the splice (the call block's
//! branch into the callee, return-block branches into the continuation,
//! the continuation's result phi) carry `loc: None` — never fabricated.
//!
//! ## Library rule
//!
//! No panics on data: every arena access is checked; a site that cannot
//! be soundly rewritten is recorded in the skip histogram, never
//! half-spliced.

use std::collections::{BTreeMap, HashMap};

use abcd_ir2::{
    BlockId, CallKind, Const, ConstId, Edge, EdgeKind, FuncId, FunctionKind, Inst, InstId,
    Modifiers, Module, Op, Ty, ValueDef, ValueId,
};

/// Inlining policy knobs. The defaults are deliberately conservative
/// (documented constants; widen only with corpus evidence).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InlinePolicy {
    /// Maximum instruction count of an inlinable callee (default 64 —
    /// small leaf-ish helpers; the corpus skip histogram reports how
    /// often this bites).
    pub max_callee_insts: usize,
    /// Maximum TOTAL instructions inlined into any one caller (default
    /// 512 — bounds code growth from fan-out call sites).
    pub max_inlined_insts_per_caller: usize,
}

impl Default for InlinePolicy {
    fn default() -> Self {
        Self {
            max_callee_insts: 64,
            max_inlined_insts_per_caller: 512,
        }
    }
}

/// Why a call site was not inlined (the skip-histogram key — stable
/// vocabulary, gate evidence like the corpus driver's SKIP categories).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SkipReason {
    /// `New`/`Apply`/`Super*` call kinds (argument binding not
    /// statically known or not materializable — see module docs).
    UnsupportedCallKind,
    /// Callee value is not `AllocClosure(DefineFunc(body))`.
    UnresolvedCallee,
    /// The callee IS the caller (direct recursion).
    SelfRecursive,
    /// The callee has no body (external/native declaration).
    CalleeNoBody,
    /// The callee is not a plain `FunctionKind::Function` (constructor,
    /// accessor, generator, async).
    CalleeKind,
    /// The callee exceeds `InlinePolicy::max_callee_insts`.
    CalleeTooLarge,
    /// The caller's per-function inlined-instruction budget is
    /// exhausted.
    CallerBudgetExhausted,
    /// The callee has try regions (first-iteration exclusion).
    CalleeHasTryRegions,
    /// The callee's entry block has predecessors (a self-loop entry
    /// would need extra phi entries for the call block's edge).
    CalleeEntryHasPreds,
    /// The callee uses a value that is neither a param, an
    /// instruction result, nor a pool constant (foreign value).
    CalleeForeignValue,
    /// The callee reads/writes lexical environments (env identity is
    /// not preserved by inlining).
    CalleeUsesLexEnv,
    /// The callee uses private-name ops (env level/slot addressing).
    CalleeUsesPrivateNames,
    /// The callee uses `arguments` (`GetUnmappedArgs`/`CopyRestArgs` —
    /// the caller's arguments object is a different object).
    CalleeUsesArguments,
    /// The callee loads its own function object (`LoadFunction`).
    CalleeUsesFunctionIdentity,
    /// The callee uses super ops (home-object/`this` context).
    CalleeUsesSuper,
    /// The callee suspends (`Await`/`SuspendGenerator`/`Resume*`/
    /// async ops/`CreateGenerator`) — the caller is not its frame.
    CalleeSuspends,
    /// A nested function/class definition in the callee transitively
    /// READS OR MUTATES the lexical environment it would capture (env
    /// identity changes across inlining; see
    /// `nested_definitions_read_outer_env`). Nested definitions that
    /// never observe the env are inlined fine.
    CalleeDefinesClosure,
    /// `this: None` (a non-`callthis*` dynamic call) but the callee
    /// uses its `this` param — the binding depends on the callee's
    /// strictness, which the IR cannot prove.
    ThisBindingUnprovable,
    /// `CallKind::Direct` with `this: None` (the §5.3 table requires
    /// an explicit receiver; malformed input).
    DirectWithoutThis,
    /// A region protecting the call block also uses it as a catch
    /// handler (handler identity would be disturbed).
    CallBlockIsHandler,
}

impl SkipReason {
    /// Stable histogram label.
    pub fn label(self) -> &'static str {
        match self {
            SkipReason::UnsupportedCallKind => "unsupported-call-kind",
            SkipReason::UnresolvedCallee => "unresolved-callee",
            SkipReason::SelfRecursive => "self-recursive",
            SkipReason::CalleeNoBody => "callee-no-body",
            SkipReason::CalleeKind => "callee-kind",
            SkipReason::CalleeTooLarge => "callee-too-large",
            SkipReason::CallerBudgetExhausted => "caller-budget-exhausted",
            SkipReason::CalleeHasTryRegions => "callee-has-try-regions",
            SkipReason::CalleeEntryHasPreds => "callee-entry-has-preds",
            SkipReason::CalleeForeignValue => "callee-foreign-value",
            SkipReason::CalleeUsesLexEnv => "callee-uses-lexenv",
            SkipReason::CalleeUsesPrivateNames => "callee-uses-private-names",
            SkipReason::CalleeUsesArguments => "callee-uses-arguments",
            SkipReason::CalleeUsesFunctionIdentity => "callee-uses-function-identity",
            SkipReason::CalleeUsesSuper => "callee-uses-super",
            SkipReason::CalleeSuspends => "callee-suspends",
            SkipReason::CalleeDefinesClosure => "callee-defines-closure",
            SkipReason::ThisBindingUnprovable => "this-binding-unprovable",
            SkipReason::DirectWithoutThis => "direct-without-this",
            SkipReason::CallBlockIsHandler => "call-block-is-handler",
        }
    }
}

/// The outcome of an [`inline_module`] run: how many call sites were
/// inlined, how many instructions were cloned in, and the skip
/// histogram (reason → count). This is the evidence that the pass
/// actually fires.
#[derive(Clone, Debug, Default)]
pub struct InlineReport {
    /// Call sites successfully inlined.
    pub sites_inlined: usize,
    /// Total callee instructions cloned into callers.
    pub insts_inlined: usize,
    /// Skip reason → number of call sites skipped for that reason.
    pub skips: BTreeMap<SkipReason, usize>,
}

impl InlineReport {
    fn record_skip(&mut self, reason: SkipReason) {
        *self.skips.entry(reason).or_insert(0) += 1;
    }

    /// Fold another report into this one (corpus aggregation).
    pub fn merge(&mut self, other: &InlineReport) {
        self.sites_inlined += other.sites_inlined;
        self.insts_inlined += other.insts_inlined;
        for (&reason, &count) in &other.skips {
            *self.skips.entry(reason).or_insert(0) += count;
        }
    }
}

/// Run the inliner over a whole module (opt-in; NOT part of
/// [`crate::optimize_module`]). Functions are processed in table order;
/// within a function, the call sites present at function-entry are
/// processed in block/inst order. Freshly cloned call sites are never
/// revisited (no recursive inlining), so the pass always terminates.
/// Idempotent only in the trivial sense that a second run sees the
/// remaining (skipped) call sites again.
pub fn inline_module(module: &mut Module, policy: &InlinePolicy) -> InlineReport {
    let mut report = InlineReport::default();
    for fi in 0..module.functions.len() {
        inline_func(module, FuncId::new(fi as u32), policy, &mut report);
    }
    report
}

/// Inline the eligible call sites of one function.
fn inline_func(
    module: &mut Module,
    caller: FuncId,
    policy: &InlinePolicy,
    report: &mut InlineReport,
) {
    // Snapshot the call sites present NOW. Cloned call sites are
    // appended after this snapshot and are deliberately never
    // revisited (no recursive inlining — termination by construction).
    let mut sites: Vec<InstId> = Vec::new();
    let Some(func) = module.func(caller) else {
        return;
    };
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if matches!(module.inst(iid).map(|i| &i.op), Some(Op::Call { .. })) {
                sites.push(iid);
            }
        }
    }

    let mut budget = policy.max_inlined_insts_per_caller;
    for iid in sites {
        // The call may have moved to a fresh continuation block when an
        // earlier call site in the same original block was inlined;
        // re-read its block from the inst record each time.
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        } = &inst.op
        else {
            continue;
        };
        let (callee_val, this, args, kind) = (*callee_val, *this, args.clone(), *kind);
        let call_block = inst.block;

        let reason = match eligibility(module, policy, caller, call_block, callee_val, this, kind) {
            Ok(callee) => {
                let size = callee_inst_count(module, callee);
                if size > budget {
                    Some(SkipReason::CallerBudgetExhausted)
                } else {
                    match inline_site(module, caller, iid, call_block, callee, &this, &args, kind) {
                        Ok(()) => {
                            report.sites_inlined += 1;
                            report.insts_inlined += size;
                            budget -= size;
                            None
                        }
                        Err(reason) => Some(reason),
                    }
                }
            }
            Err(reason) => Some(reason),
        };
        if let Some(reason) = reason {
            report.record_skip(reason);
        }
    }
}

/// Number of instructions in the callee's body (the size-cap metric and
/// the caller-budget unit).
fn callee_inst_count(module: &Module, callee: FuncId) -> usize {
    module
        .func(callee)
        .map(|f| {
            f.blocks
                .iter()
                .map(|&bb| module.block(bb).map(|b| b.insts.len()).unwrap_or(0))
                .sum()
        })
        .unwrap_or(0)
}

/// Resolve the callee value to a same-module function:
/// `AllocClosure { func }` whose operand is `DefineFunc { body }`.
/// `Mov` chains are traced through (a pure copy cannot change the
/// closure's identity). Anything else — a global load (a mutable
/// binding another script could reassign), a phi, a parameter — is
/// deliberately NOT resolved.
fn resolve_callee(module: &Module, callee_val: ValueId) -> Option<FuncId> {
    let mut current = callee_val;
    // Mov chains are short and acyclic in valid SSA; the bound is
    // defensive against malformed input.
    for _ in 0..16 {
        let ValueDef::Inst(def) = module.value(current)?.def else {
            return None;
        };
        match &module.inst(def)?.op {
            Op::Mov { src } => current = *src,
            Op::AllocClosure { func } => {
                let ValueDef::Inst(define_inst) = module.value(*func)?.def else {
                    return None;
                };
                let Op::DefineFunc { body, .. } = &module.inst(define_inst)?.op else {
                    return None;
                };
                return Some(*body);
            }
            _ => return None,
        }
    }
    None
}

/// All eligibility checks for one call site. `Ok(callee)` means the
/// site is inlinable; `Err(reason)` is the skip-histogram entry.
#[allow(clippy::too_many_arguments)]
fn eligibility(
    module: &Module,
    policy: &InlinePolicy,
    caller: FuncId,
    call_block: BlockId,
    callee_val: ValueId,
    this: Option<ValueId>,
    kind: CallKind,
) -> Result<FuncId, SkipReason> {
    if !matches!(kind, CallKind::Direct | CallKind::Dynamic) {
        return Err(SkipReason::UnsupportedCallKind);
    }
    let callee = resolve_callee(module, callee_val).ok_or(SkipReason::UnresolvedCallee)?;
    if callee == caller {
        return Err(SkipReason::SelfRecursive);
    }
    let func = module.func(callee).ok_or(SkipReason::CalleeNoBody)?;
    if func.blocks.is_empty() || func.is_external {
        return Err(SkipReason::CalleeNoBody);
    }
    if func.kind != FunctionKind::Function {
        return Err(SkipReason::CalleeKind);
    }
    if !func.try_regions.is_empty() {
        return Err(SkipReason::CalleeHasTryRegions);
    }
    let entry = func.blocks[0];
    if module.block(entry).is_some_and(|b| !b.preds.is_empty()) {
        return Err(SkipReason::CalleeEntryHasPreds);
    }
    if callee_inst_count(module, callee) > policy.max_callee_insts {
        return Err(SkipReason::CalleeTooLarge);
    }

    // Callee body scan: forbidden op classes + value sanity. Nested
    // function/class definitions are collected and checked separately
    // (a nested closure is skippable only when its captured env is
    // OBSERVABLE — see nested_definitions_read_outer_env).
    let is_static = func.modifiers.contains(Modifiers::STATIC);
    let this_param = (!is_static).then(|| func.params.first()).flatten().copied();
    let mut nested_roots: Vec<FuncId> = Vec::new();
    let blocks = func.blocks.clone();
    for &bb in &blocks {
        let Some(block) = module.block(bb) else {
            return Err(SkipReason::CalleeNoBody);
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                return Err(SkipReason::CalleeNoBody);
            };
            match &inst.op {
                Op::DefineFunc { body, .. } => nested_roots.push(*body),
                Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
                    nested_roots.push(*ctor)
                }
                _ => {}
            }
            if let Some(reason) = forbidden_op(&inst.op) {
                return Err(reason);
            }
            // Every value the callee uses must be re-mappable: a callee
            // param, a callee instruction result, or a pool constant
            // (const-defined values are module-wide and dominate
            // everything, so they transplant verbatim).
            for v in inst.op.operands() {
                match module.value(v).map(|val| val.def) {
                    Some(ValueDef::Param(_) | ValueDef::Inst(_) | ValueDef::Const(_)) => {}
                    _ => return Err(SkipReason::CalleeForeignValue),
                }
            }
            // CFG integrity: every branch target and phi edge source is
            // a callee block, so the clone's remapping is total (the
            // splice must never index a missing map entry).
            match &inst.op {
                Op::Branch { dest } => {
                    if !blocks.contains(dest) {
                        return Err(SkipReason::CalleeForeignValue);
                    }
                }
                Op::CondBranch {
                    true_dest,
                    false_dest,
                    ..
                } => {
                    if !blocks.contains(true_dest) || !blocks.contains(false_dest) {
                        return Err(SkipReason::CalleeForeignValue);
                    }
                }
                Op::Phi { entries } => {
                    if entries.iter().any(|(edge, _)| !blocks.contains(&edge.from)) {
                        return Err(SkipReason::CalleeForeignValue);
                    }
                }
                _ => {}
            }
        }
    }
    if nested_definitions_read_outer_env(module, &nested_roots) {
        return Err(SkipReason::CalleeDefinesClosure);
    }

    // `this` binding per §5.3 (T4: params[0] for non-static callees).
    match (this, this_param) {
        (None, Some(tp)) => {
            // A non-callthis* dynamic/direct call: the callee's `this`
            // is computed at callee entry from its own strictness —
            // unprovable here. Direct without a receiver is malformed.
            if kind == CallKind::Direct {
                return Err(SkipReason::DirectWithoutThis);
            }
            if callee_uses_value(module, callee, tp) {
                return Err(SkipReason::ThisBindingUnprovable);
            }
        }
        _ => {}
    }

    // Structural oddity: a region protecting the call block that also
    // uses it as a catch handler would have its handler identity
    // disturbed by the splice.
    if let Some(caller_data) = module.func(caller) {
        for region in &caller_data.try_regions {
            if region.protected.contains(&call_block)
                && region.catches.iter().any(|c| c.handler == call_block)
            {
                return Err(SkipReason::CallBlockIsHandler);
            }
        }
    }

    Ok(callee)
}

/// The forbidden-op classification (the conservative eligibility
/// exclusions; `LoadNewTarget` is NOT forbidden — it is bound per call
/// kind, see `bind_new_target`).
fn forbidden_op(op: &Op) -> Option<SkipReason> {
    use Op::*;
    match op {
        GetLexVar { .. }
        | PutLexVar { .. }
        | NewLexEnv { .. }
        | NewLexEnvWithName { .. }
        | PopLexEnv => Some(SkipReason::CalleeUsesLexEnv),
        LoadPrivate { .. }
        | StorePrivate { .. }
        | DefinePrivate { .. }
        | TestPrivate { .. }
        | CreatePrivateNames { .. } => Some(SkipReason::CalleeUsesPrivateNames),
        GetUnmappedArgs | CopyRestArgs { .. } => Some(SkipReason::CalleeUsesArguments),
        LoadFunction => Some(SkipReason::CalleeUsesFunctionIdentity),
        LoadSuper { .. } | StoreSuper { .. } | ThrowIfSuperNotCalled { .. } => {
            Some(SkipReason::CalleeUsesSuper)
        }
        Await { .. }
        | AwaitUncaught { .. }
        | SuspendGenerator { .. }
        | ResumeGenerator { .. }
        | GetResumeMode { .. }
        | AsyncFunctionEnter
        | AsyncResolve { .. }
        | AsyncReject { .. }
        | CreateGenerator { .. } => Some(SkipReason::CalleeSuspends),
        _ => None,
    }
}

/// Do any of the given nested definitions' transitive bodies OBSERVE
/// the environment they are created in? A nested closure created inside
/// the callee captures, at runtime, the env current in the callee's
/// frame; after inlining that point runs with the CALLER's env. The
/// env identity is observable only through env-relative ops, so a
/// nested definition is safe to inline iff its transitive DefineFunc
/// graph contains:
///
/// - no `GetLexVar`/`PutLexVar` at ANY level (level 0 reads the
///   function's own current env only when it created one — not
///   decidable cheaply, so any read/write is barred), and
/// - no private-name ops (`LoadPrivate`/`StorePrivate`/`DefinePrivate`/
///   `TestPrivate` — env level/slot addressing) and no
///   `CreatePrivateNames` (registers names into the CURRENT env, which
///   may be the captured one — an env MUTATION).
///
/// `NewLexEnv*`/`PopLexEnv` in nested bodies are allowed: they push/pop
/// the nested function's OWN env chain without touching the captured
/// one. Cycles in the DefineFunc graph (mutual recursion) are cut by
/// the visited set.
fn nested_definitions_read_outer_env(module: &Module, roots: &[FuncId]) -> bool {
    use std::collections::HashSet;
    let mut visited: HashSet<FuncId> = HashSet::new();
    let mut stack: Vec<FuncId> = roots.to_vec();
    while let Some(fid) = stack.pop() {
        if !visited.insert(fid) {
            continue;
        }
        let Some(func) = module.func(fid) else {
            continue;
        };
        for &bb in &func.blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::GetLexVar { .. }
                    | Op::PutLexVar { .. }
                    | Op::LoadPrivate { .. }
                    | Op::StorePrivate { .. }
                    | Op::DefinePrivate { .. }
                    | Op::TestPrivate { .. }
                    | Op::CreatePrivateNames { .. } => return true,
                    Op::DefineFunc { body, .. } => stack.push(*body),
                    Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
                        stack.push(*ctor)
                    }
                    _ => {}
                }
            }
        }
    }
    false
}

/// Does the callee's body use `value` anywhere?
fn callee_uses_value(module: &Module, callee: FuncId, value: ValueId) -> bool {
    let Some(func) = module.func(callee) else {
        return false;
    };
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            if module
                .inst(iid)
                .is_some_and(|i| i.op.operands().contains(&value))
            {
                return true;
            }
        }
    }
    false
}

/// Get-or-create the pooled `Const::Undefined` (scalar dedup, lift
/// parity) and return a FRESH const-defined value for it (one per
/// splice; values are the SSA identity, constants the payload).
fn undefined_value(module: &mut Module) -> (ConstId, ValueId) {
    let cid = (0..module.consts.len())
        .map(|i| ConstId::new(i as u32))
        .find(|&c| matches!(module.consts.get(c), Some(Const::Undefined)))
        .unwrap_or_else(|| module.consts.push(Const::Undefined));
    let val = ValueId::new(module.values.len() as u32);
    module.values.push(abcd_ir2::Value {
        def: ValueDef::Const(cid),
        ty: Ty::Any,
    });
    (cid, val)
}

/// The `new.target` binding for a call kind (T4/§5.3): `New` binds the
/// callee itself; `Direct`/`Dynamic` bind undefined. `None` for kinds
/// whose sites are never eligible (`Apply`/`Super*`), where binding
/// would be meaningless. Kept as a separate function so the binding
/// table is unit-testable independently of site eligibility.
fn new_target_binding(kind: CallKind) -> Option<NewTargetBinding> {
    match kind {
        CallKind::New => Some(NewTargetBinding::CalleeValue),
        CallKind::Direct | CallKind::Dynamic => Some(NewTargetBinding::Undefined),
        _ => None,
    }
}

/// What a cloned `LoadNewTarget` becomes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NewTargetBinding {
    /// `LoadConst` of the pooled `undefined` (Direct/Dynamic).
    Undefined,
    /// Uses of the result are replaced by the call-site callee value
    /// (New).
    CalleeValue,
}

/// The splice: clone the callee into the call site. Every fallible
/// check below duplicates an eligibility validation, so on
/// eligibility-passing input none can fire; were one ever to fire, the
/// early return would leave only unreferenced arena appends (blocks/
/// insts/values owned by no function — verifier-neutral), never a
/// half-rewritten CFG.
#[allow(clippy::too_many_arguments)]
fn inline_site(
    module: &mut Module,
    caller: FuncId,
    call_iid: InstId,
    call_block: BlockId,
    callee: FuncId,
    this: &Option<ValueId>,
    args: &[ValueId],
    kind: CallKind,
) -> Result<(), SkipReason> {
    let (undef_cid, undef_val) = undefined_value(module);
    let nt_binding = new_target_binding(kind).expect("eligibility limited kinds to Direct/Dynamic");

    // ── Step A: parameter binding (T4 + §5.3) ────────────────────────
    let callee_data = module.func(callee).ok_or(SkipReason::CalleeNoBody)?;
    let is_static = callee_data.modifiers.contains(Modifiers::STATIC);
    let mut value_map: HashMap<ValueId, ValueId> = HashMap::new();
    for (i, &param) in callee_data.params.iter().enumerate() {
        let binding = if !is_static && i == 0 {
            // The `this` binding: explicit receiver when present;
            // otherwise the callee never uses it (eligibility) — bind
            // the shared undefined so the map is total.
            this.unwrap_or(undef_val)
        } else {
            let formal = if is_static { i } else { i - 1 };
            args.get(formal).copied().unwrap_or(undef_val)
        };
        value_map.insert(param, binding);
    }

    // ── Step B: clone blocks (fresh BlockIds, arena append) ──────────
    let callee_blocks = callee_data.blocks.clone();
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::new();
    for &gb in &callee_blocks {
        let fresh = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(abcd_ir2::Block::default());
        block_map.insert(gb, fresh);
    }

    // ── Step C: fresh result values (two phases: phi/loop operands may
    // reference results defined later in callee order) ────────────────
    let base_iid = module.insts.len() as u32;
    {
        let mut seq = 0u32;
        for &gb in &callee_blocks {
            let insts: Vec<InstId> = module
                .block(gb)
                .map(|b| b.insts.clone())
                .unwrap_or_default();
            for iid in insts {
                let Some(inst) = module.inst(iid) else {
                    return Err(SkipReason::CalleeNoBody);
                };
                if let Some(result) = inst.result {
                    let ty = module.value(result).map(|v| v.ty.clone());
                    let Some(ty) = ty else {
                        return Err(SkipReason::CalleeForeignValue);
                    };
                    let fresh = ValueId::new(module.values.len() as u32);
                    module.values.push(abcd_ir2::Value {
                        def: ValueDef::Inst(InstId::new(base_iid + seq)),
                        ty,
                    });
                    value_map.insert(result, fresh);
                }
                seq += 1;
            }
        }
    }
    // Const-defined values transplant verbatim (module-wide identity).
    let remap = |value_map: &HashMap<ValueId, ValueId>, v: ValueId| -> ValueId {
        value_map.get(&v).copied().unwrap_or(v)
    };

    // ── Step D: clone instructions (operands, block payloads, and phi
    // edges remapped; locs kept verbatim) ─────────────────────────────
    // Eligibility's CFG-integrity scan guarantees every mapping exists;
    // stay defensive anyway (library rule: no panics on data).
    let map_block = |b: BlockId| -> Result<BlockId, SkipReason> {
        block_map
            .get(&b)
            .copied()
            .ok_or(SkipReason::CalleeForeignValue)
    };
    for &gb in &callee_blocks {
        let Some(block) = module.block(gb) else {
            return Err(SkipReason::CalleeNoBody);
        };
        let insts = block.insts.clone();
        let fresh_block = map_block(gb)?;
        for &iid in &insts {
            let Some(inst) = module.inst(iid) else {
                return Err(SkipReason::CalleeNoBody);
            };
            let mut op = inst.op.clone();
            for v in op.operands_mut() {
                *v = remap(&value_map, *v);
            }
            match &mut op {
                Op::Branch { dest } => *dest = map_block(*dest)?,
                Op::CondBranch {
                    true_dest,
                    false_dest,
                    ..
                } => {
                    *true_dest = map_block(*true_dest)?;
                    *false_dest = map_block(*false_dest)?;
                }
                Op::Phi { entries } => {
                    for (edge, v) in entries.iter_mut() {
                        edge.from = map_block(edge.from)?;
                        *v = remap(&value_map, *v);
                    }
                }
                _ => {}
            }
            // new.target binding (T4): Direct/Dynamic → LoadConst of the
            // pooled undefined; New (currently ineligible) → the result
            // is rewritten to a Mov of the call-site callee value.
            if matches!(op, Op::LoadNewTarget) {
                op = match nt_binding {
                    NewTargetBinding::Undefined => Op::LoadConst(undef_cid),
                    NewTargetBinding::CalleeValue => {
                        let Some(inst) = module.inst(call_iid) else {
                            return Err(SkipReason::UnresolvedCallee);
                        };
                        let Op::Call {
                            callee: callee_val, ..
                        } = &inst.op
                        else {
                            return Err(SkipReason::UnresolvedCallee);
                        };
                        Op::Mov { src: *callee_val }
                    }
                };
            }
            let result = match inst.result {
                Some(r) => Some(
                    value_map
                        .get(&r)
                        .copied()
                        .ok_or(SkipReason::CalleeForeignValue)?,
                ),
                None => None,
            };
            let loc = inst.loc;
            let fresh_iid = InstId::new(module.insts.len() as u32);
            module.insts.push(Inst {
                op,
                result,
                block: fresh_block,
                loc,
            });
            module
                .block_mut(fresh_block)
                .expect("fresh block in arena")
                .insts
                .push(fresh_iid);
        }
        // Predecessors clone from the callee (all Normal — the callee
        // has no try regions), remapped.
        let mut preds: Vec<Edge> = Vec::new();
        if let Some(b) = module.block(gb) {
            for e in &b.preds {
                preds.push(Edge {
                    from: map_block(e.from)?,
                    kind: e.kind,
                });
            }
        }
        module
            .block_mut(fresh_block)
            .expect("fresh block in arena")
            .preds = preds;
    }
    let clone_entry = map_block(callee_blocks[0])?;

    // ── Step E: split the call block at the call ─────────────────────
    let (pre_len, post) = {
        let Some(block) = module.block(call_block) else {
            return Err(SkipReason::CalleeNoBody);
        };
        let pos = block
            .insts
            .iter()
            .position(|&i| i == call_iid)
            .expect("call inst is listed in its block");
        (pos, block.insts[pos + 1..].to_vec())
    };
    let cont = BlockId::new(module.blocks.len() as u32);
    module.blocks.push(abcd_ir2::Block {
        insts: post.clone(),
        preds: Vec::new(),
    });
    for &iid in &post {
        if let Some(inst) = module.inst_mut(iid) {
            inst.block = cont;
        }
    }
    // The call block ends in a fresh branch into the callee clone (glue;
    // loc: None — never fabricate).
    let br = InstId::new(module.insts.len() as u32);
    module.insts.push(Inst {
        op: Op::Branch { dest: clone_entry },
        result: None,
        block: call_block,
        loc: None,
    });
    {
        let block = module.block_mut(call_block).expect("call block in arena");
        block.insts.truncate(pre_len);
        block.insts.push(br);
    }
    if let Some(entry_block) = module.block_mut(clone_entry) {
        entry_block.preds.push(Edge {
            from: call_block,
            kind: EdgeKind::Normal,
        });
    }

    // ── Step F: re-key the call block's old Normal successors to the
    // continuation block (the moved terminator owns them now) ─────────
    let moved_succs: Vec<BlockId> = {
        let Some(block) = module.block(cont) else {
            return Err(SkipReason::CalleeNoBody);
        };
        let Some(&last) = block.insts.last() else {
            return Err(SkipReason::CalleeNoBody);
        };
        match module.inst(last).map(|i| &i.op) {
            Some(Op::Branch { dest }) => vec![*dest],
            Some(Op::CondBranch {
                true_dest,
                false_dest,
                ..
            }) => vec![*true_dest, *false_dest],
            _ => Vec::new(),
        }
    };
    for succ in moved_succs {
        if let Some(succ_block) = module.block_mut(succ) {
            for edge in succ_block.preds.iter_mut() {
                if edge.from == call_block && edge.kind == EdgeKind::Normal {
                    edge.from = cont;
                }
            }
        }
        let phi_ids: Vec<InstId> = module
            .block(succ)
            .map(|b| {
                b.insts
                    .iter()
                    .copied()
                    .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                    .collect()
            })
            .unwrap_or_default();
        for phi_id in phi_ids {
            if let Some(phi) = module.inst_mut(phi_id) {
                if let Op::Phi { entries } = &mut phi.op {
                    for (edge, _) in entries.iter_mut() {
                        if edge.from == call_block && edge.kind == EdgeKind::Normal {
                            edge.from = cont;
                        }
                    }
                }
            }
        }
    }

    // ── Step I: own the new blocks. Must precede the use replacement
    // below: replace_uses_in_func iterates the caller's block list, and
    // the uses of the call result live in the continuation. ───────────
    let mut cloned_blocks: Vec<BlockId> = Vec::with_capacity(callee_blocks.len());
    for &gb in &callee_blocks {
        cloned_blocks.push(map_block(gb)?);
    }
    if let Some(func) = module.func_mut(caller) {
        func.blocks.extend(cloned_blocks.iter().copied());
        func.blocks.push(cont);
    }

    // ── Step G: callee Returns become branches into the continuation;
    // the call result is replaced by the return value (single return)
    // or a continuation-block phi (several) ───────────────────────────
    let mut ret_points: Vec<(BlockId, InstId, Option<ValueId>)> = Vec::new();
    for &cb in &cloned_blocks {
        let Some(block) = module.block(cb) else {
            continue;
        };
        let Some(&last) = block.insts.last() else {
            continue;
        };
        if let Some(Op::Return { value }) = module.inst(last).map(|i| &i.op) {
            ret_points.push((cb, last, *value));
        }
    }

    let call_result = module.inst(call_iid).and_then(|i| i.result);
    let replacement: ValueId = match ret_points.as_slice() {
        // The callee never returns (throws/loops forever): the
        // continuation is unreachable; bind the result to undefined so
        // no orphan value lingers.
        [] => undef_val,
        [(_rb, riid, value)] => {
            if let Some(inst) = module.inst_mut(*riid) {
                inst.op = Op::Branch { dest: cont };
            }
            value.unwrap_or(undef_val)
        }
        many => {
            // One branch per return block into the continuation, and a
            // phi at its head merging the return values.
            let mut entries = Vec::with_capacity(many.len());
            for &(rb, riid, value) in many {
                if let Some(inst) = module.inst_mut(riid) {
                    inst.op = Op::Branch { dest: cont };
                }
                entries.push((
                    Edge {
                        from: rb,
                        kind: EdgeKind::Normal,
                    },
                    value.unwrap_or(undef_val),
                ));
            }
            let phi_iid = InstId::new(module.insts.len() as u32);
            let phi_val = ValueId::new(module.values.len() as u32);
            module.values.push(abcd_ir2::Value {
                def: ValueDef::Inst(phi_iid),
                ty: Ty::Any,
            });
            module.insts.push(Inst {
                op: Op::Phi { entries },
                result: Some(phi_val),
                block: cont,
                loc: None,
            });
            module
                .block_mut(cont)
                .expect("continuation in arena")
                .insts
                .insert(0, phi_iid);
            phi_val
        }
    };
    {
        let preds: Vec<Edge> = ret_points
            .iter()
            .map(|&(rb, _, _)| Edge {
                from: rb,
                kind: EdgeKind::Normal,
            })
            .collect();
        if let Some(cont_block) = module.block_mut(cont) {
            cont_block.preds = preds;
        }
    }
    if let Some(result) = call_result {
        if result != replacement {
            crate::analysis::replace_uses_in_func(module, caller, result, replacement);
        }
    }

    // ── Step H: exception participation (the module-docs rule) ───────
    // Every region protecting the call block now protects ALL cloned
    // blocks and the continuation; handlers gain Exceptional preds and
    // same-value phi entries for each new protected block.
    let new_protected: Vec<BlockId> = cloned_blocks.iter().copied().chain([cont]).collect();
    let protecting: Vec<usize> = module
        .func(caller)
        .map(|f| {
            f.try_regions
                .iter()
                .enumerate()
                .filter(|(_, r)| r.protected.contains(&call_block))
                .map(|(i, _)| i)
                .collect()
        })
        .unwrap_or_default();
    for region_idx in protecting {
        let mut handlers: Vec<BlockId> = module
            .func(caller)
            .map(|f| {
                f.try_regions[region_idx]
                    .catches
                    .iter()
                    .map(|c| c.handler)
                    .collect()
            })
            .unwrap_or_default();
        handlers.sort_unstable();
        handlers.dedup();
        for handler in handlers {
            let call_edge = Edge {
                from: call_block,
                kind: EdgeKind::Exceptional,
            };
            if let Some(handler_block) = module.block_mut(handler) {
                for &x in &new_protected {
                    let edge = Edge {
                        from: x,
                        kind: EdgeKind::Exceptional,
                    };
                    if !handler_block.preds.contains(&edge) {
                        handler_block.preds.push(edge);
                    }
                }
            }
            let phi_ids: Vec<InstId> = module
                .block(handler)
                .map(|b| {
                    b.insts
                        .iter()
                        .copied()
                        .take_while(|&id| module.inst(id).is_some_and(|i| i.op.is_phi()))
                        .collect()
                })
                .unwrap_or_default();
            for phi_id in phi_ids {
                if let Some(phi) = module.inst_mut(phi_id) {
                    if let Op::Phi { entries } = &mut phi.op {
                        // The value the original call-block edge
                        // carried — the caller register state
                        // visible at the call. Verified input
                        // guarantees the entry; stay defensive.
                        let Some(v) = entries
                            .iter()
                            .find(|(edge, _)| *edge == call_edge)
                            .map(|(_, v)| *v)
                        else {
                            continue;
                        };
                        for &x in &new_protected {
                            entries.push((
                                Edge {
                                    from: x,
                                    kind: EdgeKind::Exceptional,
                                },
                                v,
                            ));
                        }
                    }
                }
            }
        }
        if let Some(func) = module.func_mut(caller) {
            let region = &mut func.try_regions[region_idx];
            region.protected.extend(new_protected.iter().copied());
            region.protected.sort_by_key(|b| b.index());
            region.protected.dedup();
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The T4 new.target binding table: New → the callee itself,
    /// Direct/Dynamic → undefined, everything else unbindable (and
    /// ineligible at the call site).
    #[test]
    fn new_target_binding_table() {
        assert_eq!(
            new_target_binding(CallKind::New),
            Some(NewTargetBinding::CalleeValue)
        );
        assert_eq!(
            new_target_binding(CallKind::Direct),
            Some(NewTargetBinding::Undefined)
        );
        assert_eq!(
            new_target_binding(CallKind::Dynamic),
            Some(NewTargetBinding::Undefined)
        );
        for kind in [
            CallKind::Apply,
            CallKind::Super,
            CallKind::SuperSpread,
            CallKind::SuperForwardAllArgs,
        ] {
            assert_eq!(new_target_binding(kind), None, "{kind:?} is unbindable");
        }
    }

    /// The skip-reason vocabulary is stable (corpus histogram keys).
    #[test]
    fn skip_reason_labels_are_stable() {
        assert_eq!(
            SkipReason::UnsupportedCallKind.label(),
            "unsupported-call-kind"
        );
        assert_eq!(
            SkipReason::CalleeHasTryRegions.label(),
            "callee-has-try-regions"
        );
        assert_eq!(
            SkipReason::ThisBindingUnprovable.label(),
            "this-binding-unprovable"
        );
    }
}
