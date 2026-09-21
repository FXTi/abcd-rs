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
//! - **Parameter mapping** (the vendored frame-slot model — see
//!   [`CallType`]): the callee's `params` are the code-header arg
//!   slots. The leading slots are the vendored implicit frame slots
//!   `[func][new.target][this]` (present per the callee's
//!   `L_ESCallTypeAnnotation;` callType bits; annotation ABSENT → the
//!   vendored `0xF` default, the es2abc corpus shape), followed by the
//!   source formals filled LEFT-aligned, `undefined`-padded
//!   (interpreter-inl.cpp:488), extra arguments dropped (unreadable
//!   for `arguments`-free callees, which are the only eligible ones).
//!   Slot bindings: func → the call-site closure value, new.target →
//!   per call kind (T4), this → the explicit receiver
//!   (`callthis*`/Direct) or EXACTLY `undefined` (vendored `setVregs`
//!   pushes undefined when callThis = false). `LoadFunction` and
//!   `LoadNewTarget` in the body bind the same two values.
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
//!   is a different object), super ops (home-object/`this` context),
//!   suspend ops (`Await`/`SuspendGenerator`/… — the caller is not the
//!   callee's async/generator frame), or nested definitions whose
//!   transitive bodies read or mutate the lexical environment they
//!   would capture (`DefineFunc`/`DefineClass`/`DefineSendableClass` —
//!   a nested closure's captured env is the callee's frame env, not
//!   the caller's; env-observability is decided by
//!   `nested_definitions_read_outer_env`, so callees that merely CALL
//!   other known functions still inline).
//! - The call-type slot roles are determinable ([`CallType`]): from
//!   the callee's `L_ESCallTypeAnnotation;` when present, else the
//!   vendored `0xF` default for STATIC callees (the corpus shape). A
//!   NON-STATIC callee without the annotation is refused
//!   (`SkipReason::CallTypeUnknown`): the vendored default and lift's
//!   T4 `params[0]`-is-this convention conflict there and no corpus
//!   evidence arbitrates.
//! - `this` is bindable: trivially always — `this: Some(v)` binds the
//!   receiver; `this: None` binds exactly `undefined` (vendored
//!   `setVregs`). `Direct` with `this: None` is malformed and skipped.
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
    /// `CallKind::Direct` with `this: None` (the §5.3 table requires
    /// an explicit receiver; malformed input).
    DirectWithoutThis,
    /// The callee's call-type slot roles cannot be determined: a
    /// NON-STATIC callee without an `L_ESCallTypeAnnotation;` (the
    /// vendored default and lift's T4 convention conflict there), or a
    /// callee with fewer params than its call-type's implicit slots.
    CallTypeUnknown,
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
            SkipReason::CalleeUsesSuper => "callee-uses-super",
            SkipReason::CalleeSuspends => "callee-suspends",
            SkipReason::CalleeDefinesClosure => "callee-defines-closure",
            SkipReason::DirectWithoutThis => "direct-without-this",
            SkipReason::CallTypeUnknown => "call-type-unknown",
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

/// The callee's call-type: which leading `params` slots are the
/// vendored implicit frame slots rather than source formals.
///
/// Vendored ground truth (arkcompiler_ets_runtime-master
/// ecmascript/jspandafile/method_literal.cpp `MethodLiteral::Initialize`
/// + ecmascript/method.h:459-464): the runtime builds the frame as
/// `[func?][newTarget?][this?][formals...]` inside the code header's
/// `num_args`, with the three implicit slots present iff the
/// corresponding `L_ESCallTypeAnnotation;` `callType` bits
/// (HaveThis = bit 0, HaveNewTarget = bit 1, HaveFunc = bit 3;
/// HaveExtra = bit 2 changes only the un-named actualNumArgs push, not
/// a param slot). When the annotation is ABSENT the vendored default is
/// `callType = 0xF` — all three implicit slots — which is exactly the
/// es2abc corpus shape (every corpus function is `<static>` with
/// `num_args = 3 + formals`; verified empirically against the VM: a
/// 4-formal function declares `num_args = 7` and reads its first formal
/// from `a3`).
///
/// Arguments fill the formal slots LEFT-aligned; missing formals are
/// `undefined` (interpreter-inl.cpp:488 `CALL_PUSH_UNDEFINED`), extra
/// arguments are unreadable stack content for callees that cannot
/// observe `arguments` (those are ineligible anyway).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct CallType {
    /// The func slot (the closure itself) leads.
    func: bool,
    /// The new.target slot follows.
    new_target: bool,
    /// The this slot follows.
    this: bool,
}

impl CallType {
    /// The vendored annotation-absent default (`UINT32_MAX & 0xF`).
    const DEFAULT: Self = Self {
        func: true,
        new_target: true,
        this: true,
    };

    /// Number of leading implicit slots.
    fn implicit_slots(self) -> usize {
        self.func as usize + self.new_target as usize + self.this as usize
    }

    /// Whether the callType annotation was present.
    fn from_annotation(module: &Module, callee: FuncId) -> Option<Self> {
        let func = module.func(callee)?;
        for ann in &func.annotations {
            let is_call_type = module
                .class(ann.class)
                .and_then(|c| module.sym.resolve(c.descriptor))
                == Some("L_ESCallTypeAnnotation;");
            if !is_call_type {
                continue;
            }
            for (name, value) in &ann.elements {
                if module.sym.resolve(*name) != Some("callType") {
                    continue;
                }
                let abcd_ir2::AnnValue::Const(cid) = value else {
                    continue;
                };
                let bits = module
                    .consts
                    .get(*cid)
                    .and_then(Const::as_f64)
                    .map(|x| x as u32)?;
                return Some(Self {
                    func: bits & 0b1000 != 0,
                    new_target: bits & 0b0010 != 0,
                    this: bits & 0b0001 != 0,
                });
            }
        }
        None
    }
}

/// The role of one callee `params` slot (vendored frame order:
/// func, new.target, this, then formals).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotRole {
    /// The closure object itself.
    Func,
    /// `new.target`.
    NewTarget,
    /// The `this` binding.
    This,
    /// A source formal, by index into the call's argument list.
    Formal(usize),
}

/// Assign roles to the callee's params per its [`CallType`]; `None`
/// when the params are fewer than the implicit slots (malformed — the
/// vendored ASSERT's shape).
fn slot_roles(call_type: CallType, param_count: usize) -> Option<Vec<SlotRole>> {
    if param_count < call_type.implicit_slots() {
        return None;
    }
    let mut roles = Vec::with_capacity(param_count);
    if call_type.func {
        roles.push(SlotRole::Func);
    }
    if call_type.new_target {
        roles.push(SlotRole::NewTarget);
    }
    if call_type.this {
        roles.push(SlotRole::This);
    }
    for i in 0..(param_count - call_type.implicit_slots()) {
        roles.push(SlotRole::Formal(i));
    }
    Some(roles)
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

    // The call-type slot roles (vendored MethodLiteral rule). A
    // NON-STATIC callee WITHOUT the annotation is refused: the vendored
    // 0xF default (this at slot 2) and lift's T4 convention (this at
    // params[0] for non-static kinds) conflict there, and no corpus
    // evidence arbitrates. Static callees without the annotation take
    // the vendored default (the corpus shape).
    let is_static = func.modifiers.contains(Modifiers::STATIC);
    let call_type = match CallType::from_annotation(module, callee) {
        Some(ct) => ct,
        None if is_static => CallType::DEFAULT,
        None => return Err(SkipReason::CallTypeUnknown),
    };
    if slot_roles(call_type, func.params.len()).is_none() {
        return Err(SkipReason::CallTypeUnknown);
    }

    // `Direct` without an explicit receiver is malformed per the §5.3
    // table (Direct: this = call.this).
    if kind == CallKind::Direct && this.is_none() {
        return Err(SkipReason::DirectWithoutThis);
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

/// Get-or-create the pooled `Const::Undefined` (scalar dedup, lift
/// parity). Passes must NEVER create `ValueDef::Const` values of their
/// own: the lower's `frame_init_consts` attributes const-defined values
/// to functions by id RANGE under the lift's creation-order convention,
/// so a pass-created const value lands in the wrong function's range
/// and register allocation never colors it (the typescript-enum corpus
/// failure). `undefined` is instead materialized as a `LoadConst`
/// INSTRUCTION — see [`Undef`].
fn undefined_const(module: &mut Module) -> ConstId {
    (0..module.consts.len())
        .map(|i| ConstId::new(i as u32))
        .find(|&c| matches!(module.consts.get(c), Some(Const::Undefined)))
        .unwrap_or_else(|| module.consts.push(Const::Undefined))
}

/// The per-splice `undefined` materialization: ONE `LoadConst` of the
/// pooled undefined, inserted into the call block immediately before
/// the call (so it dominates every cloned block and the continuation —
/// the call block is on every path through the splice). Lazily created
/// on first use; inst-defined, so register allocation colors it like
/// any other instruction result. Glue instruction: `loc: None` (never
/// fabricated).
struct Undef {
    cid: ConstId,
    value: Option<ValueId>,
}

impl Undef {
    fn new(module: &mut Module) -> Self {
        Self {
            cid: undefined_const(module),
            value: None,
        }
    }

    /// The undefined value, materializing the `LoadConst` on first use
    /// at `insert_pos` in `block`.
    fn get(&mut self, module: &mut Module, block: BlockId, insert_pos: usize) -> ValueId {
        if let Some(v) = self.value {
            return v;
        }
        let iid = InstId::new(module.insts.len() as u32);
        let val = ValueId::new(module.values.len() as u32);
        module.values.push(abcd_ir2::Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op: Op::LoadConst(self.cid),
            result: Some(val),
            block,
            loc: None,
        });
        let pos = insert_pos.min(module.blocks[block.index()].insts.len());
        module.blocks[block.index()].insts.insert(pos, iid);
        self.value = Some(val);
        val
    }
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
    let mut undef = Undef::new(module);
    let nt_binding = new_target_binding(kind).expect("eligibility limited kinds to Direct/Dynamic");
    // The call's position in its block: the `undefined` materialization
    // (when needed) is inserted there, before the call, so it dominates
    // every cloned block and the continuation.
    let call_pos = module
        .block(call_block)
        .and_then(|b| b.insts.iter().position(|&i| i == call_iid))
        .ok_or(SkipReason::CalleeNoBody)?;

    // ── Step A: parameter binding (the vendored frame-slot model — see
    // CallType): leading implicit slots [func][new.target][this], then
    // formals left-aligned, undefined-padded. ─────────────────────────
    let callee_data = module.func(callee).ok_or(SkipReason::CalleeNoBody)?;
    let is_static = callee_data.modifiers.contains(Modifiers::STATIC);
    let callee_params = callee_data.params.clone();
    let callee_blocks = callee_data.blocks.clone();
    let call_type = match CallType::from_annotation(module, callee) {
        Some(ct) => ct,
        None if is_static => CallType::DEFAULT,
        None => return Err(SkipReason::CallTypeUnknown),
    };
    let roles = slot_roles(call_type, callee_params.len()).ok_or(SkipReason::CallTypeUnknown)?;
    let callee_val = match &module
        .inst(call_iid)
        .ok_or(SkipReason::UnresolvedCallee)?
        .op
    {
        Op::Call { callee, .. } => *callee,
        _ => return Err(SkipReason::UnresolvedCallee),
    };
    let mut value_map: HashMap<ValueId, ValueId> = HashMap::new();
    for (param, role) in callee_params.iter().copied().zip(roles.iter().copied()) {
        let binding = match role {
            // The closure being called (vendored: the func slot is the
            // called closure).
            SlotRole::Func => callee_val,
            // new.target: bound per call kind (T4; Direct/Dynamic →
            // undefined, like `LoadNewTarget`).
            SlotRole::NewTarget => match nt_binding {
                NewTargetBinding::Undefined => undef.get(module, call_block, call_pos),
                NewTargetBinding::CalleeValue => callee_val,
            },
            // this: the explicit receiver for callthis*/Direct;
            // vendored `setVregs` pushes exactly `undefined` for a
            // non-callthis call (callThis = false), so a receiver-less
            // Dynamic call binds undefined EXACTLY.
            SlotRole::This => match this {
                Some(t) => *t,
                None => undef.get(module, call_block, call_pos),
            },
            SlotRole::Formal(k) => match args.get(k) {
                Some(a) => *a,
                None => undef.get(module, call_block, call_pos),
            },
        };
        value_map.insert(param, binding);
    }

    // ── Step B: clone blocks (fresh BlockIds, arena append) ──────────
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
                    NewTargetBinding::Undefined => Op::LoadConst(undef.cid),
                    NewTargetBinding::CalleeValue => Op::Mov { src: callee_val },
                };
            }
            // Function-identity binding: the callee observing its own
            // function object sees exactly the called closure (the same
            // value the vendored func slot carries).
            if matches!(op, Op::LoadFunction) {
                op = Op::Mov { src: callee_val };
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
        [] => undef.get(module, call_block, call_pos),
        [(_rb, riid, value)] => {
            if let Some(inst) = module.inst_mut(*riid) {
                inst.op = Op::Branch { dest: cont };
            }
            value.unwrap_or_else(|| undef.get(module, call_block, call_pos))
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
                    value.unwrap_or_else(|| undef.get(module, call_block, call_pos)),
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
        assert_eq!(SkipReason::CallTypeUnknown.label(), "call-type-unknown");
    }
}
