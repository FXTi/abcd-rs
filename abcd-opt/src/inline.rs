//! Conservative intra-module function inlining over [`abcd_ir::Module`]
//! (`design/ir.md`, `design/decisions.md` `D2`/`N44`, `#93`). **Opt-in only**:
//! nothing here is wired into [`crate::optimize_module`], preserving function
//! boundaries for decompilation and corpus gates. Callers opt in via
//! [`inline_module`].
//!
//! ## Structural & semantic soundness (`N44`, `N82`, `#93`)
//!
//! - **Disjoint arena ownership**: cloned blocks, instructions, result values,
//!   and constant materializations (`Op::LoadConst`) receive fresh caller-owned
//!   IDs — `ValueDef::Const` `frame_init_consts` `ValueId`s are never shared
//!   across functions (`VerifyErrorKind::DuplicateValueDef`).
//! - **Canonical [`abcd_ir::FrameSlots`] parameter binding**: leading implicit
//!   frame slots `[func][new.target][this]` + left-aligned `undefined`-padded
//!   formals derive directly from [`abcd_ir::FrameSlots`] (honoring
//!   `L_ESCallTypeAnnotation;` and `FrameSlots::has_extra`).
//! - **Complete transitive closure / lexical-environment scan**: nested
//!   functions referenced via `Op::for_each_func_id`, `Op::AllocClosure`,
//!   `Op::DefineMethod`, and transitive `ConstPool` literal shapes
//!   (`ArrayLiteral` / `TypedArrayLiteral` / `ObjectLiteral` /
//!   `LiteralBufferRef` → `Const::MethodRef`) are inspected iteratively with
//!   cycle guards so no lexical-environment capture is missed.
//! - **Inline-cache (`ic8` / `u16`) & instruction budgets**: callers stay
//!   within valid 8-bit (`< 0xFF` `IC_SLOT_INVALID`) and 16-bit (`<= 0xFFFE`)
//!   inline-cache capacities as well as [`InlinePolicy`] instruction caps.
//! - **Linear call-site pre-indexing & batched substitution**: candidate sites
//!   and caller IC counts are collected in a single pre-pass per caller, callee
//!   summaries and `ConstPool` `MethodRef` DAGs are memoized across the module
//!   (evicting modified callers on splice, `#103`), and call-result
//!   replacements + `DebugData` pruning apply in one linear pass per modified
//!   caller.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use abcd_ir::{
    BlockId, CallKind, Const, ConstId, Dialect, Edge, EdgeKind, FrameSlots, FuncId, FunctionKind,
    Inst, InstId, Modifiers, Module, Op, PropKey, Ty, UnOp, ValueDef, ValueId, normal_succs_inline,
};

use crate::const_eval::{
    block_phis, is_loadable_scalar_const, prune_func_debug_data, replace_uses_map_in_func,
    resolve_subst,
};

/// Maximum 8-bit IC slots (`0..0xFF` excluding `0xFF = IC_SLOT_INVALID`, leaving
/// 1 slot margin so trailing 2-slot `ic8` ops never straddle `0xFE..0xFF`).
const MAX_CALLER_IC8_SLOTS: usize = 254;

/// Maximum total 16-bit IC slots (`0..=0xFFFF` with 2-slot straddle margin).
const MAX_CALLER_TOTAL_IC_SLOTS: usize = 0xFFFE;

/// Inlining policy knobs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InlinePolicy {
    /// Maximum instruction count of an inlinable callee (default 64).
    pub max_callee_insts: usize,
    /// Maximum total instructions inlined into any one caller (default 512).
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

/// Why a call site was not inlined (stable skip-histogram vocabulary).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SkipReason {
    /// `New`/`Apply`/`Super*`/`NewSpread`/`ClassInit` call kinds.
    UnsupportedCallKind,
    /// Callee value is not `AllocClosure(DefineFunc(body))`.
    UnresolvedCallee,
    /// The callee IS the caller (direct recursion).
    SelfRecursive,
    /// The callee has no body (external/native declaration).
    CalleeNoBody,
    /// The callee is not a plain `FunctionKind::Function` in `DynamicEcma`.
    CalleeKind,
    /// The callee exceeds `InlinePolicy::max_callee_insts`.
    CalleeTooLarge,
    /// The caller's instruction or inline-cache (`ic8`/`u16`) budget is exhausted.
    CallerBudgetExhausted,
    /// The callee has try regions.
    CalleeHasTryRegions,
    /// The callee's entry block has predecessors.
    CalleeEntryHasPreds,
    /// The callee uses a foreign/unmappable value or cross-class module slot.
    CalleeForeignValue,
    /// The callee reads/writes/pushes/pops lexical environments.
    CalleeUsesLexEnv,
    /// The callee uses private-name ops.
    CalleeUsesPrivateNames,
    /// The callee uses `arguments` (`GetUnmappedArgs`/`CopyRestArgs`).
    CalleeUsesArguments,
    /// The callee uses `super` ops.
    CalleeUsesSuper,
    /// The callee suspends (`Await` / generator / async / concurrent ops).
    CalleeSuspends,
    /// A nested function/method/class closure in the callee transitively
    /// observes or mutates the lexical environment it captures.
    CalleeDefinesClosure,
    /// `CallKind::Direct` with `this: None` (malformed input).
    DirectWithoutThis,
    /// The callee's call-type slot roles cannot be determined.
    CallTypeUnknown,
    /// A region protecting the call block also uses it as a catch handler.
    CallBlockIsHandler,
    /// The call is the last instruction of its block (`N82`).
    BlockTerminalCall,
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
            SkipReason::BlockTerminalCall => "block-terminal-call",
        }
    }
}

/// Outcome of an [`inline_module`] run.
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

/// Role of one callee `params` slot (`[func][new.target][this][formals...]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotRole {
    Func,
    NewTarget,
    This,
    Formal(usize),
}

/// Cached structural and IC-slot summary of one candidate callee (`FuncId`).
#[derive(Clone)]
struct CalleeSummary {
    class_id: abcd_ir::ClassId,
    inst_count: usize,
    ic8_slots: usize,
    ic_total_slots: usize,
    has_module_ops: bool,
    base_skip: Option<SkipReason>,
    roles: Vec<SlotRole>,
}

/// Module-wide caches shared across one [`inline_module`] run.
struct InlineCtx {
    undef_cid: ConstId,
    empty_funcs: Rc<[FuncId]>,
    const_method_refs_cache: HashMap<ConstId, Rc<[FuncId]>>,
    env_reads_cache: HashMap<FuncId, bool>,
    callee_cache: HashMap<FuncId, CalleeSummary>,
}

/// Run the opt-in inliner over a whole module.
pub fn inline_module(module: &mut Module, policy: &InlinePolicy) -> InlineReport {
    let mut report = InlineReport::default();
    let mut ctx = InlineCtx {
        undef_cid: module.consts.intern(Const::Undefined),
        empty_funcs: Rc::from([]),
        const_method_refs_cache: HashMap::new(),
        env_reads_cache: HashMap::new(),
        callee_cache: HashMap::new(),
    };
    for fi in 0..module.functions.len() {
        inline_func(
            module,
            FuncId::new(fi as u32),
            policy,
            &mut ctx,
            &mut report,
        );
    }
    report
}

/// Estimate `(ic8_slots, total_ic_slots)` consumed by `op` when lowered to
/// ArkCompiler bytecode (`abcd-lower/src/isel.rs`, `N71`).
fn op_ic_slots(op: &Op) -> (usize, usize) {
    match op {
        Op::BinaryOp { .. } => (1, 1),
        Op::Compare {
            op: abcd_ir::CmpOp::InstanceOf,
            ..
        } => (2, 2),
        Op::Compare { .. } => (1, 1),
        Op::UnaryOp { op: uop, .. } => match uop {
            UnOp::TypeOf => (2, 2),
            UnOp::Minus
            | UnOp::BitNot
            | UnOp::Inc
            | UnOp::Dec
            | UnOp::ToNumber
            | UnOp::ToNumeric => (1, 1),
            UnOp::LogicalNot
            | UnOp::IsTrue
            | UnOp::IsFalse
            | UnOp::JumpEqz
            | UnOp::JumpNez
            | UnOp::ToPropertyKey
            | UnOp::Void => (0, 0),
        },
        Op::AllocRegExp { .. } => (2, 2),
        Op::AllocObject { .. }
        | Op::AllocArray { .. }
        | Op::GetTemplateObject { .. }
        | Op::GetIterator { .. }
        | Op::GetAsyncIterator { .. }
        | Op::IteratorReturn { .. }
        | Op::IteratorThrow { .. }
        | Op::DefineFunc { .. }
        | Op::DefineMethod { .. }
        | Op::DefineClass(_)
        | Op::DefineSendableClass(_) => (1, 1),
        Op::TestProp {
            key: PropKey::Index(_) | PropKey::Dynamic(_),
            ..
        } => (1, 1),
        Op::Call { args, .. } => {
            if args.len() > u8::MAX as usize {
                (0, 0)
            } else {
                (2, 2)
            }
        }
        Op::LoadProp { .. }
        | Op::LoadPropIdx { .. }
        | Op::LoadPropDyn { .. }
        | Op::StoreProp { .. }
        | Op::StorePropIdx { .. }
        | Op::StorePropDyn { .. }
        | Op::StoreOwnPropName { .. }
        | Op::StoreOwnPropDyn { .. }
        | Op::StoreOwnPropIdx { .. }
        | Op::SetObjectWithProto { .. }
        | Op::LoadSuper { .. }
        | Op::StoreSuper { .. }
        | Op::TryGetGlobal { .. }
        | Op::StoreGlobal { .. }
        | Op::StoreGlobalRecord { .. }
        | Op::TryStoreGlobal { .. }
        | Op::LoadPrivate { .. }
        | Op::StorePrivate { .. }
        | Op::DefinePrivate { .. }
        | Op::TestPrivate { .. } => (0, 2),
        _ => (0, 0),
    }
}

/// Inline the eligible call sites of one caller in linear time (`#93`).
fn inline_func(
    module: &mut Module,
    caller: FuncId,
    policy: &InlinePolicy,
    ctx: &mut InlineCtx,
    report: &mut InlineReport,
) {
    let Some(caller_func) = module.func(caller) else {
        return;
    };
    if caller_func.blocks.is_empty() {
        return;
    }
    let caller_dialect = module.func_dialect(caller_func);
    let caller_class = caller_func.class_id;

    // Single linear pre-pass over `caller`: collect candidate call `InstId`s
    // and compute initial `(ic8, ic_total)` slot counts.
    let mut sites: Vec<InstId> = Vec::new();
    let mut caller_ic8 = 0usize;
    let mut caller_ic_total = 0usize;
    for &bb in &caller_func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            let (ic8, ict) = op_ic_slots(&inst.op);
            caller_ic8 += ic8;
            caller_ic_total += ict;
            if matches!(inst.op, Op::Call { .. }) {
                sites.push(iid);
            }
        }
    }
    if sites.is_empty() {
        return;
    }

    let mut budget = policy.max_inlined_insts_per_caller;
    let mut call_result_subst: HashMap<ValueId, ValueId> = HashMap::new();
    let mut inlined_any = false;

    for iid in sites {
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Call {
            callee: raw_callee_val,
            this: raw_this,
            ref args,
            kind,
        } = inst.op
        else {
            continue;
        };
        let (site_ic8, site_ic_total) = op_ic_slots(&inst.op);
        let call_block = inst.block;
        let callee_val = resolve_subst(&call_result_subst, raw_callee_val);
        let this = raw_this.map(|t| resolve_subst(&call_result_subst, t));
        let resolved_args: Vec<ValueId> = args
            .iter()
            .map(|&a| resolve_subst(&call_result_subst, a))
            .collect();

        let check = check_site_eligibility(
            module,
            policy,
            ctx,
            caller,
            caller_dialect,
            caller_class,
            call_block,
            iid,
            callee_val,
            this,
            kind,
        );

        let skip_reason = match check {
            Ok((callee, summary)) => {
                let next_ic8 = caller_ic8.saturating_sub(site_ic8) + summary.ic8_slots;
                let next_ic_total =
                    caller_ic_total.saturating_sub(site_ic_total) + summary.ic_total_slots;
                let ic_overflow = (summary.ic8_slots > site_ic8 && next_ic8 > MAX_CALLER_IC8_SLOTS)
                    || (summary.ic_total_slots > site_ic_total
                        && next_ic_total > MAX_CALLER_TOTAL_IC_SLOTS);

                if summary.inst_count > budget || ic_overflow {
                    Some(SkipReason::CallerBudgetExhausted)
                } else {
                    match inline_site(
                        module,
                        ctx.undef_cid,
                        caller,
                        iid,
                        call_block,
                        callee,
                        &summary.roles,
                        callee_val,
                        &this,
                        &resolved_args,
                        kind,
                        &mut call_result_subst,
                    ) {
                        Ok(()) => {
                            report.sites_inlined += 1;
                            report.insts_inlined += summary.inst_count;
                            budget -= summary.inst_count;
                            caller_ic8 = next_ic8;
                            caller_ic_total = next_ic_total;
                            inlined_any = true;
                            None
                        }
                        Err(reason) => Some(reason),
                    }
                }
            }
            Err(reason) => Some(reason),
        };
        if let Some(reason) = skip_reason {
            report.record_skip(reason);
        }
    }

    if inlined_any {
        if !call_result_subst.is_empty() {
            replace_uses_map_in_func(module, caller, &call_result_subst);
        }
        let _ = prune_func_debug_data(module, caller);
        ctx.callee_cache.remove(&caller);
        ctx.env_reads_cache.remove(&caller);
    }
}

/// Resolve `callee_val` through bounded `Mov` chains to
/// `AllocClosure { func: DefineFunc { body } }`.
fn resolve_callee(module: &Module, callee_val: ValueId) -> Option<FuncId> {
    let mut current = callee_val;
    for _ in 0..16 {
        let ValueDef::Inst(def) = module.value(current)?.def else {
            return None;
        };
        match &module.inst(def)?.op {
            Op::Mov { src } => {
                if *src == current {
                    return None;
                }
                current = *src;
            }
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

/// Resolve a closure/template operand of `Op::AllocClosure` or `Op::DefineMethod`
/// to a target [`FuncId`] if statically determinable.
fn resolve_closure_operand_func(module: &Module, start: ValueId) -> Option<FuncId> {
    let mut cur = start;
    for _ in 0..16 {
        let val = module.value(cur)?;
        match val.def {
            ValueDef::Const(cid) => {
                if let Some(Const::MethodRef { func, .. }) = module.consts.get(cid) {
                    return Some(*func);
                }
                return None;
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src } | Op::AllocClosure { func: src } => {
                    if *src == cur {
                        return None;
                    }
                    cur = *src;
                }
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(cid) => {
                    if let Some(Const::MethodRef { func, .. }) = module.consts.get(*cid) {
                        return Some(*func);
                    }
                    return None;
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
    None
}

#[inline]
const fn is_composite_const(konst: &Const) -> bool {
    matches!(
        konst,
        Const::LiteralBufferRef(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
    )
}

fn push_composite_const_children(konst: &Const, out: &mut Vec<ConstId>) {
    match konst {
        Const::LiteralBufferRef(inner) => out.push(*inner),
        Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
            out.extend_from_slice(items);
        }
        Const::ObjectLiteral { keys, values } => {
            out.extend_from_slice(keys);
            out.extend_from_slice(values);
        }
        _ => {}
    }
}

/// Iteratively evaluate and memoize every [`Const::MethodRef`] [`FuncId`]
/// reachable from `root_cid` (`ArrayLiteral`, `TypedArrayLiteral`,
/// `ObjectLiteral`, `LiteralBufferRef`) across the module (`#103`).
///
/// Scalar constants return in `O(1)` without touching any hash table or heap
/// allocation; composite literal DAGs are evaluated once in iterative
/// post-order (`O(|ConstPool|)` total across the module), with a cycle-safe
/// fallback for malformed cyclic `ConstPool` inputs.
fn collect_method_refs_from_const(
    module: &Module,
    root_cid: ConstId,
    ctx: &mut InlineCtx,
    local_seen_consts: &mut HashSet<ConstId>,
    out_funcs: &mut Vec<FuncId>,
) {
    let Some(root_konst) = module.consts.get(root_cid) else {
        return;
    };
    match root_konst {
        Const::MethodRef { func, .. } => {
            if local_seen_consts.insert(root_cid) {
                out_funcs.push(*func);
            }
            return;
        }
        k if is_composite_const(k) => {}
        _ => return,
    }
    if !local_seen_consts.insert(root_cid) {
        return;
    }
    if let Some(cached) = ctx.const_method_refs_cache.get(&root_cid) {
        out_funcs.extend_from_slice(cached);
        return;
    }

    let mut stack: Vec<(ConstId, bool)> = vec![(root_cid, false)];
    let mut in_progress: HashSet<ConstId> = HashSet::new();
    let mut cycle_tainted: HashSet<ConstId> = HashSet::new();
    let mut children_buf: Vec<ConstId> = Vec::new();

    while let Some((cid, expanded)) = stack.pop() {
        if ctx.const_method_refs_cache.contains_key(&cid) {
            if expanded {
                in_progress.remove(&cid);
            }
            continue;
        }
        if !expanded {
            if !in_progress.insert(cid) {
                continue;
            }
            stack.push((cid, true));
            let Some(konst) = module.consts.get(cid) else {
                continue;
            };
            children_buf.clear();
            push_composite_const_children(konst, &mut children_buf);
            for &child in children_buf.iter().rev() {
                if ctx.const_method_refs_cache.contains_key(&child) {
                    continue;
                }
                if in_progress.contains(&child) {
                    cycle_tainted.insert(cid);
                    continue;
                }
                if module.consts.get(child).is_some_and(is_composite_const) {
                    stack.push((child, false));
                }
            }
        } else {
            in_progress.remove(&cid);
            let Some(konst) = module.consts.get(cid) else {
                ctx.const_method_refs_cache
                    .insert(cid, Rc::clone(&ctx.empty_funcs));
                continue;
            };
            children_buf.clear();
            push_composite_const_children(konst, &mut children_buf);

            let mut tainted = cycle_tainted.contains(&cid);
            let mut direct_count = 0usize;
            let mut single_child: Option<(ConstId, Rc<[FuncId]>)> = None;
            let mut multi_child = false;

            for &child in &children_buf {
                if in_progress.contains(&child) || cycle_tainted.contains(&child) {
                    tainted = true;
                    break;
                }
                match module.consts.get(child) {
                    Some(Const::MethodRef { .. }) => {
                        direct_count += 1;
                    }
                    Some(k) if is_composite_const(k) => {
                        if let Some(rc) = ctx.const_method_refs_cache.get(&child)
                            && !rc.is_empty()
                        {
                            match &single_child {
                                None if !multi_child => {
                                    single_child = Some((child, Rc::clone(rc)));
                                }
                                Some((prev_cid, _)) if *prev_cid == child => {}
                                _ => {
                                    single_child = None;
                                    multi_child = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }

            if tainted {
                cycle_tainted.insert(cid);
                continue;
            }

            let resolved: Rc<[FuncId]> = if direct_count == 0 && !multi_child {
                single_child.map_or_else(|| Rc::clone(&ctx.empty_funcs), |(_, rc)| rc)
            } else {
                let mut funcs: Vec<FuncId> = Vec::new();
                let mut seen: HashSet<FuncId> = HashSet::new();
                for &child in &children_buf {
                    match module.consts.get(child) {
                        Some(Const::MethodRef { func, .. }) => {
                            if seen.insert(*func) {
                                funcs.push(*func);
                            }
                        }
                        Some(k) if is_composite_const(k) => {
                            if let Some(rc) = ctx.const_method_refs_cache.get(&child) {
                                for &f in rc.iter() {
                                    if seen.insert(f) {
                                        funcs.push(f);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if funcs.is_empty() {
                    Rc::clone(&ctx.empty_funcs)
                } else {
                    Rc::from(funcs)
                }
            };
            ctx.const_method_refs_cache.insert(cid, resolved);
        }
    }

    if let Some(cached) = ctx.const_method_refs_cache.get(&root_cid) {
        out_funcs.extend_from_slice(cached);
        return;
    }

    // Defensive fallback for malformed cyclic `ConstPool` graphs: collect all
    // reachable `MethodRef`s from `root_cid` iteratively with a visited guard.
    let mut visited: HashSet<ConstId> = HashSet::new();
    let mut seen_funcs: HashSet<FuncId> = HashSet::new();
    let mut funcs: Vec<FuncId> = Vec::new();
    let mut worklist: Vec<ConstId> = vec![root_cid];
    while let Some(cid) = worklist.pop() {
        if let Some(cached) = ctx.const_method_refs_cache.get(&cid) {
            for &f in cached.iter() {
                if seen_funcs.insert(f) {
                    funcs.push(f);
                }
            }
            continue;
        }
        if !visited.insert(cid) {
            continue;
        }
        let Some(konst) = module.consts.get(cid) else {
            continue;
        };
        match konst {
            Const::MethodRef { func, .. } => {
                if seen_funcs.insert(*func) {
                    funcs.push(*func);
                }
            }
            k if is_composite_const(k) => {
                children_buf.clear();
                push_composite_const_children(k, &mut children_buf);
                for &child in children_buf.iter().rev() {
                    worklist.push(child);
                }
            }
            _ => {}
        }
    }
    let rc: Rc<[FuncId]> = if funcs.is_empty() {
        Rc::clone(&ctx.empty_funcs)
    } else {
        Rc::from(funcs)
    };
    out_funcs.extend_from_slice(&rc);
    ctx.const_method_refs_cache.insert(root_cid, rc);
}

/// Collect all nested [`FuncId`]s referenced directly or via `ConstPool`
/// literal shapes by `op`. Returns `false` if `op` allocates/defines a closure
/// over an unresolved dynamic operand whose body cannot be inspected.
fn collect_nested_funcs_from_op(
    module: &Module,
    op: &Op,
    ctx: &mut InlineCtx,
    local_seen_consts: &mut HashSet<ConstId>,
    out_funcs: &mut Vec<FuncId>,
) -> bool {
    op.for_each_func_id(|fid| out_funcs.push(fid));
    op.for_each_const_id(|cid| {
        collect_method_refs_from_const(module, cid, ctx, local_seen_consts, out_funcs);
    });
    op.for_each_operand(|v| {
        if let Some(ValueDef::Const(cid)) = module.value(v).map(|val| val.def) {
            collect_method_refs_from_const(module, cid, ctx, local_seen_consts, out_funcs);
        }
    });
    match op {
        Op::AllocClosure { func } | Op::DefineMethod { func, .. } => {
            if let Some(fid) = resolve_closure_operand_func(module, *func) {
                out_funcs.push(fid);
                true
            } else {
                false
            }
        }
        _ => true,
    }
}

/// Assign roles to `callee`'s parameters from canonical [`FrameSlots`].
fn slot_roles(slots: FrameSlots, param_count: usize) -> Option<Vec<SlotRole>> {
    let implicit = slots.implicit_count();
    if param_count < implicit {
        return None;
    }
    let mut roles = Vec::with_capacity(param_count);
    if slots.func {
        roles.push(SlotRole::Func);
    }
    if slots.new_target {
        roles.push(SlotRole::NewTarget);
    }
    if slots.this {
        roles.push(SlotRole::This);
    }
    for i in 0..(param_count - implicit) {
        roles.push(SlotRole::Formal(i));
    }
    Some(roles)
}

/// Resolve `callee`'s [`FrameSlots`] for inlining (`D6`): explicit
/// `L_ESCallTypeAnnotation;` wins; unannotated `STATIC` callees in
/// `DynamicEcma` take [`FrameSlots::of`] (`0xF` default, `has_extra == true`
/// verified unobservable because `arguments` ops are barred); unannotated
/// non-static callees return `None` (`SkipReason::CallTypeUnknown`).
fn resolve_callee_frame_slots(module: &Module, func: &abcd_ir::FunctionData) -> Option<FrameSlots> {
    if let Some(annotated) = FrameSlots::from_call_type_annotation(module, func) {
        let _ = FrameSlots::has_extra(module, func);
        return Some(annotated);
    }
    if func.modifiers.contains(Modifiers::STATIC) {
        let _ = FrameSlots::has_extra(module, func);
        Some(FrameSlots::of(module, func))
    } else {
        None
    }
}

fn is_concurrent_or_sendable_func(module: &Module, func: &abcd_ir::FunctionData) -> bool {
    func.annotations.iter().any(|ann| {
        matches!(
            module
                .class(ann.class)
                .and_then(|c| module.sym.resolve(c.descriptor)),
            Some("L_ESConcurrentModuleRequestsAnnotation;" | "L_ESSendableAnnotation;")
        )
    })
}

/// Build and memoize the callee summary for `callee`.
fn summarize_callee(module: &Module, ctx: &mut InlineCtx, callee: FuncId) -> Option<CalleeSummary> {
    if let Some(cached) = ctx.callee_cache.get(&callee) {
        return Some(cached.clone());
    }
    let func = module.func(callee)?;
    let class_id = func.class_id;
    if func.blocks.is_empty() || func.is_external {
        let s = CalleeSummary {
            class_id,
            inst_count: 0,
            ic8_slots: 0,
            ic_total_slots: 0,
            has_module_ops: false,
            base_skip: Some(SkipReason::CalleeNoBody),
            roles: Vec::new(),
        };
        ctx.callee_cache.insert(callee, s.clone());
        return Some(s);
    }
    if func.kind != FunctionKind::Function
        || module.func_dialect(func) != Dialect::DynamicEcma
        || is_concurrent_or_sendable_func(module, func)
    {
        let s = CalleeSummary {
            class_id,
            inst_count: 0,
            ic8_slots: 0,
            ic_total_slots: 0,
            has_module_ops: false,
            base_skip: Some(SkipReason::CalleeKind),
            roles: Vec::new(),
        };
        ctx.callee_cache.insert(callee, s.clone());
        return Some(s);
    }
    if !func.try_regions.is_empty() {
        let s = CalleeSummary {
            class_id,
            inst_count: 0,
            ic8_slots: 0,
            ic_total_slots: 0,
            has_module_ops: false,
            base_skip: Some(SkipReason::CalleeHasTryRegions),
            roles: Vec::new(),
        };
        ctx.callee_cache.insert(callee, s.clone());
        return Some(s);
    }
    let entry = func.blocks[0];
    if module.block(entry).is_some_and(|b| !b.preds.is_empty()) {
        let s = CalleeSummary {
            class_id,
            inst_count: 0,
            ic8_slots: 0,
            ic_total_slots: 0,
            has_module_ops: false,
            base_skip: Some(SkipReason::CalleeEntryHasPreds),
            roles: Vec::new(),
        };
        ctx.callee_cache.insert(callee, s.clone());
        return Some(s);
    }

    let blocks = func.blocks.clone();
    let block_set: HashSet<BlockId> = blocks.iter().copied().collect();
    let params_len = func.params.len();

    let mut inst_count = 0usize;
    let mut ic8_slots = 0usize;
    let mut ic_total_slots = 0usize;
    for &bb in &blocks {
        let Some(block) = module.block(bb) else {
            let s = CalleeSummary {
                class_id,
                inst_count: 0,
                ic8_slots: 0,
                ic_total_slots: 0,
                has_module_ops: false,
                base_skip: Some(SkipReason::CalleeNoBody),
                roles: Vec::new(),
            };
            ctx.callee_cache.insert(callee, s.clone());
            return Some(s);
        };
        inst_count += block.insts.len();
    }

    let mut nested_roots: Vec<FuncId> = Vec::new();
    let mut visited_consts: HashSet<ConstId> = HashSet::new();
    let mut unresolved_closure = false;
    let mut has_module_ops = false;
    let mut body_skip: Option<SkipReason> = None;

    'scan: for &bb in &blocks {
        let Some(block) = module.block(bb) else {
            body_skip = Some(SkipReason::CalleeNoBody);
            break;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                body_skip = Some(SkipReason::CalleeNoBody);
                break 'scan;
            };
            let (ic8, ict) = op_ic_slots(&inst.op);
            ic8_slots += ic8;
            ic_total_slots += ict;

            if matches!(
                inst.op,
                Op::LoadModuleVar { .. }
                    | Op::StoreModuleVar { .. }
                    | Op::GetModuleNamespace { .. }
                    | Op::DynamicImport { .. }
            ) {
                has_module_ops = true;
            }
            if !collect_nested_funcs_from_op(
                module,
                &inst.op,
                ctx,
                &mut visited_consts,
                &mut nested_roots,
            ) {
                unresolved_closure = true;
            }
            if let Some(reason) = forbidden_op(&inst.op) {
                body_skip = Some(reason);
                break 'scan;
            }
            let mut foreign_val = false;
            inst.op.for_each_operand(|v| {
                if !foreign_val {
                    match module.value(v).map(|val| val.def) {
                        Some(ValueDef::Param(_) | ValueDef::Inst(_) | ValueDef::Const(_)) => {}
                        _ => foreign_val = true,
                    }
                }
            });
            inst.op.for_each_block_id(|target_bb| {
                if !block_set.contains(&target_bb) {
                    foreign_val = true;
                }
            });
            if foreign_val {
                body_skip = Some(SkipReason::CalleeForeignValue);
                break 'scan;
            }
        }
    }

    if body_skip.is_none()
        && (unresolved_closure || nested_definitions_read_outer_env(module, &nested_roots, ctx))
    {
        body_skip = Some(SkipReason::CalleeDefinesClosure);
    }

    let mut roles = Vec::new();
    if body_skip.is_none() {
        let func_ref = module.func(callee)?;
        match resolve_callee_frame_slots(module, func_ref)
            .and_then(|slots| slot_roles(slots, params_len))
        {
            Some(r) => roles = r,
            None => body_skip = Some(SkipReason::CallTypeUnknown),
        }
    }

    let summary = CalleeSummary {
        class_id,
        inst_count,
        ic8_slots,
        ic_total_slots,
        has_module_ops,
        base_skip: body_skip,
        roles,
    };
    ctx.callee_cache.insert(callee, summary.clone());
    Some(summary)
}

#[expect(
    clippy::too_many_arguments,
    reason = "site validation inspects caller, dialect, class, block, inst, callee, receiver, kind, policy, and cache"
)]
fn check_site_eligibility(
    module: &Module,
    policy: &InlinePolicy,
    ctx: &mut InlineCtx,
    caller: FuncId,
    caller_dialect: Dialect,
    caller_class: abcd_ir::ClassId,
    call_block: BlockId,
    call_iid: InstId,
    callee_val: ValueId,
    this: Option<ValueId>,
    kind: CallKind,
) -> Result<(FuncId, CalleeSummary), SkipReason> {
    if !matches!(kind, CallKind::Direct | CallKind::Dynamic) {
        return Err(SkipReason::UnsupportedCallKind);
    }
    let callee = resolve_callee(module, callee_val).ok_or(SkipReason::UnresolvedCallee)?;
    if callee == caller {
        return Err(SkipReason::SelfRecursive);
    }
    let summary = summarize_callee(module, ctx, callee).ok_or(SkipReason::CalleeNoBody)?;
    if matches!(summary.base_skip, Some(SkipReason::CalleeNoBody)) {
        return Err(SkipReason::CalleeNoBody);
    }
    if caller_dialect != Dialect::DynamicEcma {
        return Err(SkipReason::CalleeKind);
    }
    if matches!(
        summary.base_skip,
        Some(
            SkipReason::CalleeKind
                | SkipReason::CalleeHasTryRegions
                | SkipReason::CalleeEntryHasPreds
        )
    ) {
        return Err(summary.base_skip.unwrap_or(SkipReason::CalleeKind));
    }
    if summary.inst_count > policy.max_callee_insts {
        return Err(SkipReason::CalleeTooLarge);
    }
    if summary.has_module_ops && summary.class_id != caller_class {
        // `'scan` in `summarize_callee` halts immediately on the first
        // `forbidden_op` or foreign operand/block, so `has_module_ops == true`
        // guarantees a module op preceded any later `forbidden_op`.
        return Err(SkipReason::CalleeForeignValue);
    }
    if let Some(skip) = summary.base_skip {
        return Err(skip);
    }
    if kind == CallKind::Direct && this.is_none() {
        return Err(SkipReason::DirectWithoutThis);
    }
    if let Some(caller_data) = module.func(caller) {
        for region in &caller_data.try_regions {
            if region.protected.contains(&call_block)
                && region.catches.iter().any(|c| c.handler == call_block)
            {
                return Err(SkipReason::CallBlockIsHandler);
            }
        }
    }
    if module
        .block(call_block)
        .is_some_and(|b| b.insts.last() == Some(&call_iid))
    {
        return Err(SkipReason::BlockTerminalCall);
    }
    Ok((callee, summary))
}

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
        Call {
            kind:
                CallKind::Super
                | CallKind::SuperArrow
                | CallKind::SuperSpread
                | CallKind::SuperForwardAllArgs
                | CallKind::ClassInit,
            ..
        } => Some(SkipReason::CalleeUsesSuper),
        Await { .. }
        | AwaitUncaught { .. }
        | SuspendGenerator { .. }
        | ResumeGenerator { .. }
        | GetResumeMode { .. }
        | AsyncFunctionEnter
        | AsyncResolve { .. }
        | AsyncReject { .. }
        | CreateGenerator { .. }
        | CreateAsyncGenerator { .. }
        | AsyncGeneratorResolve { .. }
        | AsyncGeneratorReject { .. }
        | SetGeneratorState { .. }
        | NotifyConcurrentResult { .. } => Some(SkipReason::CalleeSuspends),
        _ => None,
    }
}

/// Iterative transitive check over nested function, class, method, and literal
/// `MethodRef` definitions to determine whether any nested body observes or
/// mutates the lexical environment captured from the callee (`#93`, `#103`).
fn nested_definitions_read_outer_env(
    module: &Module,
    roots: &[FuncId],
    ctx: &mut InlineCtx,
) -> bool {
    for &root in roots {
        if let Some(cached) = ctx.env_reads_cache.get(&root).copied() {
            if cached {
                return true;
            }
            continue;
        }
        let mut visited_set: HashSet<FuncId> = HashSet::new();
        let mut visited_order: Vec<FuncId> = Vec::new();
        let mut visited_consts: HashSet<ConstId> = HashSet::new();
        let mut stack: Vec<FuncId> = vec![root];
        let mut reads = false;
        let mut trigger_fid: Option<FuncId> = None;

        while let Some(fid) = stack.pop() {
            if let Some(known) = ctx.env_reads_cache.get(&fid).copied() {
                if known {
                    reads = true;
                    break;
                }
                continue;
            }
            if !visited_set.insert(fid) {
                continue;
            }
            visited_order.push(fid);
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
                    if matches!(
                        inst.op,
                        Op::GetLexVar { .. }
                            | Op::PutLexVar { .. }
                            | Op::NewLexEnv { .. }
                            | Op::NewLexEnvWithName { .. }
                            | Op::PopLexEnv
                            | Op::LoadPrivate { .. }
                            | Op::StorePrivate { .. }
                            | Op::DefinePrivate { .. }
                            | Op::TestPrivate { .. }
                            | Op::CreatePrivateNames { .. }
                            | Op::NotifyConcurrentResult { .. }
                    ) {
                        reads = true;
                        trigger_fid = Some(fid);
                        break;
                    }
                    if !collect_nested_funcs_from_op(
                        module,
                        &inst.op,
                        ctx,
                        &mut visited_consts,
                        &mut stack,
                    ) {
                        reads = true;
                        trigger_fid = Some(fid);
                        break;
                    }
                }
                if reads {
                    break;
                }
            }
            if reads {
                break;
            }
        }

        ctx.env_reads_cache.insert(root, reads);
        if let Some(tf) = trigger_fid {
            ctx.env_reads_cache.insert(tf, true);
        }
        if !reads {
            for v in visited_order {
                ctx.env_reads_cache.insert(v, false);
            }
        } else {
            return true;
        }
    }
    false
}

/// Per-splice helper materializing fresh caller-owned `Op::LoadConst`
/// instructions in `call_block` ahead of the spliced call (deduplicating
/// identical constants within the splice and never sharing `frame_init_consts`
/// `ValueId`s across functions).
struct SiteConstMaterializer {
    undef_cid: ConstId,
    insert_pos: usize,
    materialized: HashMap<ConstId, ValueId>,
}

impl SiteConstMaterializer {
    fn new(undef_cid: ConstId, call_pos: usize) -> Self {
        Self {
            undef_cid,
            insert_pos: call_pos,
            materialized: HashMap::new(),
        }
    }

    fn materialize_undef(&mut self, module: &mut Module, block: BlockId) -> ValueId {
        self.materialize_const(module, block, self.undef_cid, Ty::Any)
    }

    fn materialize_const(
        &mut self,
        module: &mut Module,
        block: BlockId,
        cid: ConstId,
        ty: Ty,
    ) -> ValueId {
        if ty == Ty::Any
            && let Some(&existing) = self.materialized.get(&cid)
        {
            return existing;
        }
        let is_scalar = module.consts.get(cid).is_some_and(is_loadable_scalar_const);
        if !is_scalar {
            // Defensive fallback for unverified IR referencing a non-scalar
            // `ValueDef::Const(cid)`: allocate a fresh caller-owned
            // `frame_init_consts` `ValueId` (still disjoint from callee!).
            let val = ValueId::new(module.values.len() as u32);
            module.values.push(abcd_ir::Value {
                def: ValueDef::Const(cid),
                ty,
            });
            return val;
        }
        let iid = InstId::new(module.insts.len() as u32);
        let val = ValueId::new(module.values.len() as u32);
        let is_any = ty == Ty::Any;
        module.values.push(abcd_ir::Value {
            def: ValueDef::Inst(iid),
            ty,
        });
        module.insts.push(Inst {
            op: Op::LoadConst(cid),
            result: Some(val),
            block,
            loc: None,
        });
        let pos = self
            .insert_pos
            .min(module.blocks[block.index()].insts.len());
        module.blocks[block.index()].insts.insert(pos, iid);
        self.insert_pos = pos + 1;
        if is_any {
            self.materialized.insert(cid, val);
        }
        val
    }
}

fn new_target_binding(kind: CallKind) -> Option<NewTargetBinding> {
    match kind {
        CallKind::New => Some(NewTargetBinding::CalleeValue),
        CallKind::Direct | CallKind::Dynamic => Some(NewTargetBinding::Undefined),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NewTargetBinding {
    Undefined,
    CalleeValue,
}

#[expect(
    clippy::too_many_arguments,
    reason = "call-site splice requires caller, call_iid, call_block, callee, roles, receiver, args, kind, and subst map"
)]
fn inline_site(
    module: &mut Module,
    undef_cid: ConstId,
    caller: FuncId,
    call_iid: InstId,
    call_block: BlockId,
    callee: FuncId,
    roles: &[SlotRole],
    callee_val: ValueId,
    this: &Option<ValueId>,
    args: &[ValueId],
    kind: CallKind,
    call_result_subst: &mut HashMap<ValueId, ValueId>,
) -> Result<(), SkipReason> {
    let nt_binding = new_target_binding(kind).ok_or(SkipReason::CalleeKind)?;
    let initial_call_pos = module
        .block(call_block)
        .and_then(|b| b.insts.iter().position(|&i| i == call_iid))
        .ok_or(SkipReason::CalleeNoBody)?;
    let mut const_mat = SiteConstMaterializer::new(undef_cid, initial_call_pos);

    // ── Step A: parameter binding via canonical FrameSlots roles ──────
    let callee_data = module.func(callee).ok_or(SkipReason::CalleeNoBody)?;
    let callee_params = callee_data.params.clone();
    let callee_blocks = callee_data.blocks.clone();
    if callee_params.len() != roles.len() {
        return Err(SkipReason::CallTypeUnknown);
    }

    let mut value_map: HashMap<ValueId, ValueId> = HashMap::new();
    for (param, role) in callee_params.iter().copied().zip(roles.iter().copied()) {
        let binding = match role {
            SlotRole::Func => callee_val,
            SlotRole::NewTarget => match nt_binding {
                NewTargetBinding::Undefined => const_mat.materialize_undef(module, call_block),
                NewTargetBinding::CalleeValue => callee_val,
            },
            SlotRole::This => match this {
                Some(t) => *t,
                None => const_mat.materialize_undef(module, call_block),
            },
            SlotRole::Formal(k) => match args.get(k) {
                Some(a) => *a,
                None => const_mat.materialize_undef(module, call_block),
            },
        };
        value_map.insert(param, binding);
    }

    // Materialize fresh caller-owned `Op::LoadConst` values for any
    // `ValueDef::Const(cid)` operands referenced inside `callee` (`#93` — never
    // share `frame_init_consts` `ValueId`s across functions!).
    let mut callee_const_operands: Vec<(ValueId, ConstId, Ty)> = Vec::new();
    let mut seen_callee_consts: HashSet<ValueId> = HashSet::new();
    for &gb in &callee_blocks {
        let Some(block) = module.block(gb) else {
            return Err(SkipReason::CalleeNoBody);
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                return Err(SkipReason::CalleeNoBody);
            };
            inst.op.for_each_operand(|v| {
                if !value_map.contains_key(&v)
                    && seen_callee_consts.insert(v)
                    && let Some(val) = module.value(v)
                    && let ValueDef::Const(cid) = val.def
                {
                    callee_const_operands.push((v, cid, val.ty.clone()));
                }
            });
        }
    }
    let mut non_scalar_caller_consts: Vec<ValueId> = Vec::new();
    for (callee_vid, cid, ty) in callee_const_operands {
        let fresh_vid = const_mat.materialize_const(module, call_block, cid, ty);
        if matches!(
            module.value(fresh_vid).map(|v| v.def),
            Some(ValueDef::Const(_))
        ) {
            non_scalar_caller_consts.push(fresh_vid);
        }
        value_map.insert(callee_vid, fresh_vid);
    }
    if !non_scalar_caller_consts.is_empty()
        && let Some(caller_fn) = module.func_mut(caller)
    {
        caller_fn.frame_init_consts.extend(non_scalar_caller_consts);
    }

    // ── Step B: clone blocks (fresh BlockIds, arena append) ──────────
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::with_capacity(callee_blocks.len());
    for &gb in &callee_blocks {
        let fresh = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(abcd_ir::Block::default());
        block_map.insert(gb, fresh);
    }

    // ── Step C: fresh result values ──────────────────────────────────
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
                    let Some(ty) = module.value(result).map(|v| v.ty.clone()) else {
                        return Err(SkipReason::CalleeForeignValue);
                    };
                    let fresh = ValueId::new(module.values.len() as u32);
                    module.values.push(abcd_ir::Value {
                        def: ValueDef::Inst(InstId::new(base_iid + seq)),
                        ty,
                    });
                    value_map.insert(result, fresh);
                }
                seq += 1;
            }
        }
    }

    // ── Step D: clone instructions ───────────────────────────────────
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
            op.for_each_operand_mut(|v| {
                if let Some(&mapped) = value_map.get(v) {
                    *v = mapped;
                }
            });
            let mut bad_block = false;
            op.for_each_block_id_mut(|b| {
                if let Some(&mapped) = block_map.get(b) {
                    *b = mapped;
                } else {
                    bad_block = true;
                }
            });
            if bad_block {
                return Err(SkipReason::CalleeForeignValue);
            }
            if matches!(op, Op::LoadNewTarget) {
                op = match nt_binding {
                    NewTargetBinding::Undefined => Op::LoadConst(undef_cid),
                    NewTargetBinding::CalleeValue => Op::Mov { src: callee_val },
                };
            }
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
                .ok_or(SkipReason::CalleeNoBody)?
                .insts
                .push(fresh_iid);
        }
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
            .ok_or(SkipReason::CalleeNoBody)?
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
            .ok_or(SkipReason::CalleeNoBody)?;
        (pos, block.insts[pos + 1..].to_vec())
    };
    let mut post_results: HashSet<ValueId> = HashSet::new();
    for &iid in &post {
        if let Some(res) = module.inst(iid).and_then(|i| i.result) {
            post_results.insert(res);
        }
    }
    let cont = BlockId::new(module.blocks.len() as u32);
    module.blocks.push(abcd_ir::Block {
        insts: post.clone(),
        preds: Vec::new(),
    });
    for &iid in &post {
        if let Some(inst) = module.inst_mut(iid) {
            inst.block = cont;
        }
    }
    let br = InstId::new(module.insts.len() as u32);
    module.insts.push(Inst {
        op: Op::Branch { dest: clone_entry },
        result: None,
        block: call_block,
        loc: None,
    });
    {
        let block = module
            .block_mut(call_block)
            .ok_or(SkipReason::CalleeNoBody)?;
        block.insts.truncate(pre_len);
        block.insts.push(br);
    }
    if let Some(entry_block) = module.block_mut(clone_entry) {
        entry_block.preds.push(Edge {
            from: call_block,
            kind: EdgeKind::Normal,
        });
    }

    // ── Step F: re-key the call block's old Normal successors to `cont`
    let moved_succs: Vec<BlockId> = module
        .block(cont)
        .and_then(|b| b.insts.last().copied())
        .and_then(|iid| module.inst(iid))
        .map(|inst| {
            let (targets, count) = normal_succs_inline(&inst.op);
            targets[..count].to_vec()
        })
        .unwrap_or_default();
    for succ in moved_succs {
        if let Some(succ_block) = module.block_mut(succ) {
            for edge in succ_block.preds.iter_mut() {
                if edge.from == call_block && edge.kind == EdgeKind::Normal {
                    edge.from = cont;
                }
            }
        }
        for phi_id in block_phis(module, succ) {
            if let Some(phi) = module.inst_mut(phi_id)
                && let Op::Phi { entries } = &mut phi.op
            {
                for (edge, _) in entries.iter_mut() {
                    if edge.from == call_block && edge.kind == EdgeKind::Normal {
                        edge.from = cont;
                    }
                }
            }
        }
    }

    // ── Step I: own the new blocks ───────────────────────────────────
    let mut cloned_blocks: Vec<BlockId> = Vec::with_capacity(callee_blocks.len());
    for &gb in &callee_blocks {
        cloned_blocks.push(map_block(gb)?);
    }
    if let Some(func) = module.func_mut(caller) {
        func.blocks.extend(cloned_blocks.iter().copied());
        func.blocks.push(cont);
    }

    // ── Step G: callee Returns become branches into `cont` ───────────
    let mut ret_points: Vec<(BlockId, InstId, Option<ValueId>)> = Vec::new();
    for &cb in &cloned_blocks {
        let Some(&last) = module.block(cb).and_then(|b| b.insts.last()) else {
            continue;
        };
        if let Some(Op::Return { value }) = module.inst(last).map(|i| &i.op) {
            ret_points.push((cb, last, *value));
        }
    }

    let call_result = module.inst(call_iid).and_then(|i| i.result);
    // Insert any late `undefined` materializations immediately before `br` in `call_block`.
    const_mat.insert_pos = module
        .block(call_block)
        .map_or(0, |b| b.insts.len().saturating_sub(1));

    let replacement: ValueId = match ret_points.as_slice() {
        [] => const_mat.materialize_undef(module, call_block),
        [(_rb, riid, value)] => {
            if let Some(inst) = module.inst_mut(*riid) {
                inst.op = Op::Branch { dest: cont };
            }
            value.unwrap_or_else(|| const_mat.materialize_undef(module, call_block))
        }
        many => {
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
                    value.unwrap_or_else(|| const_mat.materialize_undef(module, call_block)),
                ));
            }
            let phi_iid = InstId::new(module.insts.len() as u32);
            let phi_val = ValueId::new(module.values.len() as u32);
            module.values.push(abcd_ir::Value {
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
                .ok_or(SkipReason::CalleeNoBody)?
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

    // ── Step H: exception participation (`R3-H10`) ───────────────────
    let call_edge = Edge {
        from: call_block,
        kind: EdgeKind::Exceptional,
    };
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
    let mut handlers: Vec<BlockId> = module
        .func(caller)
        .map(|f| {
            protecting
                .iter()
                .flat_map(|&idx| f.try_regions[idx].catches.iter().map(|c| c.handler))
                .collect()
        })
        .unwrap_or_default();
    handlers.sort_by_key(|b| b.index());
    handlers.dedup();

    let mut handler_phi_snapshots: Vec<(InstId, ValueId)> = Vec::new();
    for &handler in &handlers {
        for phi_id in block_phis(module, handler) {
            if let Some(Op::Phi { entries }) = module.inst(phi_id).map(|i| &i.op)
                && let Some(raw_v) = entries
                    .iter()
                    .find(|(edge, _)| *edge == call_edge)
                    .map(|(_, v)| *v)
            {
                let snap_v = resolve_subst(call_result_subst, raw_v);
                handler_phi_snapshots.push((phi_id, snap_v));
            }
        }
    }

    if let Some(result) = call_result
        && result != replacement
    {
        call_result_subst.insert(result, replacement);
    }

    let new_protected: Vec<BlockId> = cloned_blocks.iter().copied().chain([cont]).collect();
    for &handler in &handlers {
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
    }
    let mut caller_undef_const_val: Option<ValueId> = None;
    for (phi_id, snap_val) in handler_phi_snapshots {
        let (pre_val, cont_val) =
            if Some(snap_val) == call_result || post_results.contains(&snap_val) {
                let uval = *caller_undef_const_val.get_or_insert_with(|| {
                    let existing = module.func(caller).and_then(|f| {
                        f.frame_init_consts.iter().copied().find(|&v| {
                            matches!(
                                module.value(v).map(|val| val.def),
                                Some(ValueDef::Const(c)) if c == undef_cid
                            )
                        })
                    });
                    if let Some(v) = existing {
                        v
                    } else {
                        let v = ValueId::new(module.values.len() as u32);
                        module.values.push(abcd_ir::Value {
                            def: ValueDef::Const(undef_cid),
                            ty: Ty::Any,
                        });
                        if let Some(f) = module.func_mut(caller) {
                            f.frame_init_consts.push(v);
                        }
                        v
                    }
                });
                let post_v = if Some(snap_val) == call_result {
                    replacement
                } else {
                    snap_val
                };
                (uval, post_v)
            } else {
                (snap_val, snap_val)
            };
        if let Some(phi) = module.inst_mut(phi_id)
            && let Op::Phi { entries } = &mut phi.op
        {
            for (edge, val) in entries.iter_mut() {
                if *edge == call_edge {
                    *val = pre_val;
                }
            }
            for &cb in &cloned_blocks {
                let edge = Edge {
                    from: cb,
                    kind: EdgeKind::Exceptional,
                };
                if !entries.iter().any(|(e, _)| *e == edge) {
                    entries.push((edge, pre_val));
                }
            }
            let cont_edge = Edge {
                from: cont,
                kind: EdgeKind::Exceptional,
            };
            if !entries.iter().any(|(e, _)| *e == cont_edge) {
                entries.push((cont_edge, cont_val));
            }
            let mut seen_edges = HashSet::with_capacity(entries.len());
            entries.retain(|(e, _)| seen_edges.insert(*e));
        }
    }
    if let Some(func) = module.func_mut(caller) {
        for region_idx in protecting {
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

    #[test]
    fn inline_policy_default_constants() {
        let p = InlinePolicy::default();
        assert_eq!(p.max_callee_insts, 64);
        assert_eq!(p.max_inlined_insts_per_caller, 512);
    }

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
            CallKind::SuperArrow,
            CallKind::SuperSpread,
            CallKind::SuperForwardAllArgs,
            CallKind::NewSpread,
            CallKind::ClassInit,
        ] {
            assert_eq!(new_target_binding(kind), None, "{kind:?} is unbindable");
        }
    }

    #[test]
    fn skip_reason_labels_are_stable() {
        let labels: [(SkipReason, &str); 20] = [
            (SkipReason::UnsupportedCallKind, "unsupported-call-kind"),
            (SkipReason::UnresolvedCallee, "unresolved-callee"),
            (SkipReason::SelfRecursive, "self-recursive"),
            (SkipReason::CalleeNoBody, "callee-no-body"),
            (SkipReason::CalleeKind, "callee-kind"),
            (SkipReason::CalleeTooLarge, "callee-too-large"),
            (SkipReason::CallerBudgetExhausted, "caller-budget-exhausted"),
            (SkipReason::CalleeHasTryRegions, "callee-has-try-regions"),
            (SkipReason::CalleeEntryHasPreds, "callee-entry-has-preds"),
            (SkipReason::CalleeForeignValue, "callee-foreign-value"),
            (SkipReason::CalleeUsesLexEnv, "callee-uses-lexenv"),
            (
                SkipReason::CalleeUsesPrivateNames,
                "callee-uses-private-names",
            ),
            (SkipReason::CalleeUsesArguments, "callee-uses-arguments"),
            (SkipReason::CalleeUsesSuper, "callee-uses-super"),
            (SkipReason::CalleeSuspends, "callee-suspends"),
            (SkipReason::CalleeDefinesClosure, "callee-defines-closure"),
            (SkipReason::DirectWithoutThis, "direct-without-this"),
            (SkipReason::CallTypeUnknown, "call-type-unknown"),
            (SkipReason::CallBlockIsHandler, "call-block-is-handler"),
            (SkipReason::BlockTerminalCall, "block-terminal-call"),
        ];
        let mut seen = std::collections::BTreeSet::new();
        for (reason, want) in labels {
            assert_eq!(reason.label(), want, "{reason:?}");
            assert!(seen.insert(want), "labels are unique: {want}");
        }
    }

    #[test]
    fn const_method_refs_memoizes_dags_and_handles_cyclic_constpool() {
        let mut module = Module::new();
        let f_a = FuncId::new(10);
        let f_b = FuncId::new(20);
        let c_num = module.consts.push(Const::number(1.0));
        let mr_a = module.consts.push(Const::method_ref(f_a));
        let mr_b = module.consts.push(Const::method_ref(f_b));

        // Acyclic diamond DAG: root -> [mid, mid], mid -> [mr_a, c_num, mr_b, mr_a].
        let mid = module
            .consts
            .push(Const::ArrayLiteral(vec![mr_a, c_num, mr_b, mr_a]));
        let root = module.consts.push(Const::ArrayLiteral(vec![mid, mid]));

        // Malformed cyclic ConstPool: cyc0 -> [cyc1, mr_b], cyc1 -> [cyc0].
        let cyc0_pred = ConstId::new(root.index() as u32 + 1);
        let cyc1_pred = ConstId::new(root.index() as u32 + 2);
        let cyc0 = module
            .consts
            .push(Const::ArrayLiteral(vec![cyc1_pred, mr_b]));
        let cyc1 = module.consts.push(Const::ArrayLiteral(vec![cyc0]));
        assert_eq!(cyc0, cyc0_pred);
        assert_eq!(cyc1, cyc1_pred);

        let mut ctx = InlineCtx {
            undef_cid: module.consts.intern(Const::Undefined),
            empty_funcs: Rc::from([]),
            const_method_refs_cache: HashMap::new(),
            env_reads_cache: HashMap::new(),
            callee_cache: HashMap::new(),
        };

        let mut seen = HashSet::new();
        let mut out = Vec::new();
        collect_method_refs_from_const(&module, c_num, &mut ctx, &mut seen, &mut out);
        assert!(out.is_empty());
        assert!(
            ctx.const_method_refs_cache.is_empty(),
            "scalar consts must bypass HashMap allocation"
        );

        collect_method_refs_from_const(&module, root, &mut ctx, &mut seen, &mut out);
        assert_eq!(out, vec![f_a, f_b]);
        assert_eq!(
            ctx.const_method_refs_cache.get(&mid).map(|r| r.as_ref()),
            Some([f_a, f_b].as_slice())
        );
        assert_eq!(
            ctx.const_method_refs_cache.get(&root).map(|r| r.as_ref()),
            Some([f_a, f_b].as_slice())
        );

        // Query cyc0 first, then cyc1: neither may cache an incomplete cycle-cut subset.
        let mut seen_cyc0 = HashSet::new();
        let mut out_cyc0 = Vec::new();
        collect_method_refs_from_const(&module, cyc0, &mut ctx, &mut seen_cyc0, &mut out_cyc0);
        assert_eq!(out_cyc0, vec![f_b]);

        let mut seen_cyc1 = HashSet::new();
        let mut out_cyc1 = Vec::new();
        collect_method_refs_from_const(&module, cyc1, &mut ctx, &mut seen_cyc1, &mut out_cyc1);
        assert_eq!(out_cyc1, vec![f_b]);
    }
}
