//! Instruction selection: IR instructions → ArkCompiler bytecodes
//! (`design/ir.md` §5, `design/decisions.md` `ADR-03`, `ADR-06`, `ADR-07`).
//!
//! Takes an IR function with register allocation results and produces
//! a sequence of ArkCompiler bytecodes per basic block:
//!
//! - Entity operands are emitted as module-scoped IR identities (never file
//!   offsets — reverse resolution and per-method `u16` compaction live in
//!   `method_body`): strings ride as the raw [`Sym`] index, method references
//!   as the module function-table index ([`FuncId`]), literal shapes as the
//!   [`ConstId`].
//! - Expansion chains fold back via [`Suppression`]: `DefineFunc`+`AllocClosure`
//!   → `definefunc`, +`DefineMethod` → `definemethod`, `LoadConst`+`LoadPropIdx`
//!   → `ldobjbyindex`, `LoadConst(undefined)`+`TryGetGlobal` →
//!   `tryldglobalbyname`.
//! - Frame-initial values ([`ValueDef::Const`]) are materialized at the entry
//!   block top in reverse creation order.
//! - Comparisons ([`Op::Compare`]) always emit unfused (`eq`/`noteq`/`stricteq`/
//!   `strictnoteq`/…) followed by `jnez` at the branch, never the dead fused
//!   compare-and-branch family (`ADR-07`).

use std::collections::{HashMap, HashSet};

use abcd_ir::{
    BinOp, BlockId, CallKind, CmpOp, Const, ConstId, DefineClassData, DynPrim, FuncId, InstId,
    LexEnvKind, Module, Op, OwnStoreKind, StaticTy, SuperCheck, SuperKey, Sym, Ty, UnOp, ValueDef,
    ValueId,
};
use abcd_isa::{Bytecode, BytecodeFlags, EntityId, EntityKind, Imm, Label, Reg};

use crate::LowerError;
use crate::copy_resolve::{emit_copy, resolve_slot_copies};
use crate::fusion::{Suppression, const_u32_index};
use crate::regalloc::{self, RegAlloc, RegSlot};

/// Result of instruction selection for one function.
#[derive(Debug, Default)]
pub struct IselResult {
    /// Bytecodes per block (in RPO order).
    pub block_codes: Vec<(BlockId, Vec<Bytecode>)>,
    /// Audit trail of every emitted entity operand, keyed by `(entity kind,
    /// raw IR operand value)`. Emitted operands are IR identities by
    /// construction (always [`EntityTrace::Traced`]); source-file traceability
    /// is verified during relocation in `method_body::to_method_body`.
    pub entity_traces: HashMap<(EntityKind, u32), EntityTrace>,
    /// Total number of IC slots allocated for this function.
    pub ic_size: u32,
    /// Optional unsupported-instruction message (retained for diagnostic
    /// compatibility; `select_inst` returns `Result::Err` directly on
    /// unsupported shapes).
    pub unsupported: Option<String>,
    /// Per-block `(InstId, local_pc)` map for reconstructing `MethodDebugInfo` (`#57` `R3-H8`).
    pub block_inst_pcs: HashMap<BlockId, Vec<(InstId, usize)>>,
    /// Intra-block synthetic `(label_id, block, local_pc)` targets for standalone `JumpEqz`/`JumpNez`.
    pub internal_labels: Vec<(u32, BlockId, usize)>,
    /// Number of leading `ExceptionParam`-homing instructions per catch handler block (`R3-M2`).
    pub handler_prologue_len: HashMap<BlockId, usize>,
    /// `CondBranch` blocks whose `acc` at the branch is guaranteed boolean (`R3-X1`).
    pub bool_cond_blocks: HashSet<BlockId>,
}

/// Whether an emitted entity operand value is traceable to a source-file
/// entity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntityTrace {
    /// The operand value traces to an IR entity.
    Traced,
    /// At least one use of this operand value could not be traced.
    Untraced,
}

/// Records every emitted entity operand for the audit trail.
struct EntityTracer {
    traces: HashMap<(EntityKind, u32), EntityTrace>,
}

impl EntityTracer {
    /// Emit a string operand: the raw [`Sym`] arena index. Reverse
    /// resolution (content → source offset) happens in
    /// `method_body::to_method_body`.
    fn eid(&mut self, sym: Sym) -> EntityId {
        self.traces
            .insert((EntityKind::StringId, sym.0), EntityTrace::Traced);
        EntityId(sym.0)
    }

    /// Emit a method-reference operand: the raw module function-table
    /// index. Reverse resolution (index → method offset) happens in
    /// `method_body::to_method_body`.
    fn method_eid(&mut self, func: FuncId) -> EntityId {
        self.traces
            .insert((EntityKind::MethodId, func.0), EntityTrace::Traced);
        EntityId(func.0)
    }

    /// Emit a literal-shape operand: the raw [`ConstId`]. Reverse
    /// resolution (content → literal-array offset) happens in
    /// `method_body::to_method_body`.
    fn literal_eid(&mut self, shape: ConstId) -> EntityId {
        self.traces
            .insert((EntityKind::LiteralarrayId, shape.0), EntityTrace::Traced);
        EntityId(shape.0)
    }
}

/// Per-function IC slot allocator.
struct IcAllocator {
    counter: u32,
}

impl IcAllocator {
    fn new() -> Self {
        Self { counter: 0 }
    }

    /// Allocate `slot_count` consecutive IC slots, skipping the reserved
    /// [`IC_SLOT_INVALID`] (`0xFF`) slot and `0xFE..=0xFF` boundary straddle,
    /// and degrading instructions once `counter > 0xFFFF` to `0xFF` without
    /// advancing `counter` (`templates/isa.h.erb` `SetIcSlot`, `#61` `R3-X2`).
    fn alloc(&mut self, slot_count: u16) -> Imm {
        let width = u32::from(slot_count);
        if self.counter <= IC_SLOT_INVALID && self.counter.saturating_add(width) > IC_SLOT_INVALID {
            self.counter = IC_SLOT_INVALID + 1;
        }
        if self.counter <= 0xFFFF {
            let id = self.counter;
            self.counter += width;
            Imm(i64::from(id))
        } else {
            Imm(i64::from(IC_SLOT_INVALID))
        }
    }

    /// Allocate 1 IC slot (`ONE_SLOT` instructions).
    fn one(&mut self) -> Imm {
        self.alloc(1)
    }

    /// Allocate 2 IC slots (`two_slot` instructions).
    fn two(&mut self) -> Imm {
        self.alloc(2)
    }
}

/// The runtime's "no inline cache" sentinel for a one-byte IC-slot
/// immediate: `MethodLiteral::INVALID_IC_SLOT`
/// (arkcompiler_ets_runtime-master/ecmascript/jspandafile/method_literal.h:40).
/// Slot 0xFF is never a real slot — the runtime reserves it even in its
/// slot sizing (method_literal.h:431-434) — so an `eight_bit_ic`
/// instruction that no longer fits the one-byte region DEGRADES to it:
/// the VM runs the uncached slow path and behavior is preserved. This is
/// exactly what upstream output looks like on IC-heavy methods (the N71
/// shift-operator fixtures carry hundreds of `shl2 0xff`).
const IC_SLOT_INVALID: u32 = 0xFF;

/// The vendor IC-slot count of an IC-carrying instruction: the isa.yaml
/// generator derives `one_slot ? 1 : 2` (es2panda
/// compiler/templates/isa.h.erb — `SetIcSlot`'s `ret`).
fn ic_slot_count(bc: &Bytecode) -> u32 {
    if bc.has_flag(BytecodeFlags::ONE_SLOT) {
        1
    } else {
        2
    }
}

/// Mutable access to the IC-slot immediate (always operand 0) of every
/// bytecode variant isel emits an IC slot for — exactly the `ic.one()` /
/// `ic.two()` consumers in this file. Totality against the vendor
/// property tables is enforced at lower time by [`rearrange_ic_slots`]'
/// cross-check, so a missed or stale arm is a hard error, never silent
/// misassignment.
fn ic_slot_imm_mut(bc: &mut Bytecode) -> Option<&mut Imm> {
    use Bytecode::*;
    Some(match bc {
        Add2(i, _)
        | Sub2(i, _)
        | Mul2(i, _)
        | Div2(i, _)
        | Mod2(i, _)
        | Exp(i, _)
        | Shl2(i, _)
        | Shr2(i, _)
        | Ashr2(i, _)
        | And2(i, _)
        | Or2(i, _)
        | Xor2(i, _)
        | Eq(i, _)
        | Noteq(i, _)
        | Stricteq(i, _)
        | Strictnoteq(i, _)
        | Less(i, _)
        | Lesseq(i, _)
        | Greater(i, _)
        | Greatereq(i, _)
        | Isin(i, _)
        | Instanceof(i, _) => i,
        Neg(i) | Not(i) | Inc(i) | Dec(i) | Typeof(i) | Tonumber(i) | Tonumeric(i) => i,
        Createobjectwithbuffer(i, _) | Createarraywithbuffer(i, _) => i,
        Createemptyarray(i) | Gettemplateobject(i) | Getiterator(i) | Getasynciterator(i) => i,
        Createregexpwithliteral(i, ..) | Definefunc(i, ..) | Definemethod(i, ..) => i,
        Defineclasswithbuffer(i, ..) | CallruntimeDefinesendableclass(i, ..) => i,
        Ldglobalvar(i, _)
        | Tryldglobalbyname(i, _)
        | Stglobalvar(i, _)
        | Sttoglobalrecord(i, _)
        | Stconsttoglobalrecord(i, _)
        | Trystglobalbyname(i, _) => i,
        Ldprivateproperty(i, ..)
        | Stprivateproperty(i, ..)
        | CallruntimeDefineprivateproperty(i, ..)
        | Testin(i, ..) => i,
        Setobjectwithproto(i, _)
        | Ldobjbyname(i, _)
        | Ldobjbyvalue(i, _)
        | Ldobjbyindex(i, _)
        | Ldsuperbyname(i, _)
        | Ldsuperbyvalue(i, _)
        | Closeiterator(i, _) => i,
        Stobjbyname(i, ..)
        | Stobjbyvalue(i, ..)
        | Stobjbyindex(i, ..)
        | Stownbyname(i, ..)
        | Stownbynamewithnameset(i, ..)
        | Definefieldbyname(i, ..)
        | Definepropertybyname(i, ..)
        | Stownbyvalue(i, ..)
        | Stownbyvaluewithnameset(i, ..)
        | CallruntimeDefinefieldbyvalue(i, ..)
        | Stownbyindex(i, ..)
        | CallruntimeDefinefieldbyindex(i, ..)
        | Stsuperbyname(i, ..)
        | Stsuperbyvalue(i, ..) => i,
        Callarg0(i) => i,
        Callarg1(i, _)
        | Callargs2(i, ..)
        | Callargs3(i, ..)
        | Callthis0(i, _)
        | Callthis1(i, ..)
        | Callthis2(i, ..)
        | Callthis3(i, ..)
        | Apply(i, ..)
        | Supercallspread(i, _)
        | Newobjapply(i, _)
        | CallruntimeCallinit(i, _) => i,
        Callrange(i, ..)
        | Callthisrange(i, ..)
        | Supercallthisrange(i, ..)
        | Supercallarrowrange(i, ..)
        | Newobjrange(i, ..) => i,
        _ => return None,
    })
}

/// N71: mirror of upstream es2panda's `PandaGen::ReArrangeIc()`
/// (arkcompiler_ets_frontend-master/es2panda/compiler/core/pandagen.cpp:2278,
/// overflow trigger regAllocator.cpp:56-64, per-instruction semantics
/// templates/isa.h.erb `SetIcSlot`).
///
/// The dense per-function [`IcAllocator`] assigns IC slots in emission
/// order from a single counter. When a method's total IC-slot consumption
/// exceeds the one-byte region, an `eight_bit_ic` instruction (isa.yaml:
/// `imm:u8`, no wide form — add2/shr2/ashr2/strictnoteq/tonumber/neg/
/// callarg1/callthis0-3, …) ends up with a slot immediate the encoder
/// cannot store (`operand out of range`, the N71 encode failure on 24
/// test262 fixtures). Upstream survives by REARRANGING the slot space
/// after the fact, and so do we:
///
/// - Pass A: the one-byte-slot-only (`eight_bit_ic`) instructions
///   re-allocate densely from slot 0, in emission order. An instruction
///   that no longer fits (or straddles the boundary — a two-slot
///   instruction needs both slots below 0xFF) degrades to
///   [`IC_SLOT_INVALID`], the runtime's "no IC" sentinel, exactly like
///   upstream.
/// - Pass B: every other IC instruction (`sixteen_bit_ic` /
///   `eight_sixteen_bit_ic`) continues from where pass A ended; a
///   two-slot instruction straddling 0xFF skips to 0x100, and once
///   `counter > 0xFFFF` instructions degrade to [`IC_SLOT_INVALID`]
///   (`0xFF`) without advancing `counter` (upstream `SetIcSlot`).
///
/// The rearrangement fires ONLY when the dense assignment actually
/// overflowed (an `eight_bit_ic` immediate outside `0..0xFF`), so every
/// non-overflowing function keeps its dense assignment byte-for-byte.
/// Returns the total IC-slot consumption (for `IselResult::ic_size`).
fn rearrange_ic_slots(
    func_id: FuncId,
    block_codes: &mut [(BlockId, Vec<Bytecode>)],
    dense_total: u32,
) -> Result<u32, LowerError> {
    // Cross-check isel's IC-immediate operand map against the vendor
    // property tables (an unmapped IC instruction would keep a stale slot
    // — silent misassignment) and detect the overflow.
    let mut overflow = false;
    for (_, codes) in block_codes.iter_mut() {
        for bc in codes {
            let vendor_ic =
                bc.has_flag(BytecodeFlags::IC_SLOT) || bc.has_flag(BytecodeFlags::JIT_IC_SLOT);
            if vendor_ic != ic_slot_imm_mut(bc).is_some() {
                return Err(LowerError::IcOperandMapGap {
                    func: func_id,
                    mnemonic: bc.mnemonic().to_string(),
                    vendor_ic,
                });
            }
            if vendor_ic && bc.has_flag(BytecodeFlags::EIGHT_BIT_IC) {
                let imm = ic_slot_imm_mut(bc).expect("cross-checked above");
                if !(0..i64::from(IC_SLOT_INVALID)).contains(&imm.0)
                    || imm.0 + i64::from(ic_slot_count(bc)) > i64::from(IC_SLOT_INVALID)
                {
                    overflow = true;
                }
            }
        }
    }
    if !overflow {
        return Ok(dense_total);
    }

    // Pass A: one-byte-slot-only instructions first, densely from 0.
    let mut counter: u32 = 0;
    for (_, codes) in block_codes.iter_mut() {
        for bc in codes {
            if !bc.has_flag(BytecodeFlags::EIGHT_BIT_IC) {
                continue;
            }
            let slots = ic_slot_count(bc);
            let imm = ic_slot_imm_mut(bc).expect("cross-checked above");
            if counter + slots <= IC_SLOT_INVALID {
                *imm = Imm(i64::from(counter));
                counter += slots;
            } else if counter <= IC_SLOT_INVALID {
                // Boundary straddle: jump the counter past the region and
                // degrade this instruction to no-IC (upstream's exact
                // `return 0x100 - slot` behavior).
                *imm = Imm(i64::from(IC_SLOT_INVALID));
                counter = IC_SLOT_INVALID + 1;
            } else {
                // One-byte region exhausted: degrade to no-IC.
                *imm = Imm(i64::from(IC_SLOT_INVALID));
            }
        }
    }

    // Pass B: the sixteen-bit-capable IC instructions continue.
    for (_, codes) in block_codes.iter_mut() {
        for bc in codes {
            let vendor_ic =
                bc.has_flag(BytecodeFlags::IC_SLOT) || bc.has_flag(BytecodeFlags::JIT_IC_SLOT);
            if !vendor_ic || bc.has_flag(BytecodeFlags::EIGHT_BIT_IC) {
                continue;
            }
            let slots = ic_slot_count(bc);
            let imm = ic_slot_imm_mut(bc).expect("cross-checked above");
            if counter <= IC_SLOT_INVALID && counter + slots > IC_SLOT_INVALID {
                // Boundary straddle: skip to 0x100 (upstream's exact
                // `imm = 0x100; return ret + (0x100 - slot)` behavior).
                *imm = Imm(i64::from(IC_SLOT_INVALID + 1));
                counter = IC_SLOT_INVALID + 1 + slots;
            } else if counter <= 0xFFFF {
                *imm = Imm(i64::from(counter));
                counter += slots;
            } else {
                // Beyond u16 immediate space (`counter > 0xFFFF`): degrade to
                // `IC_SLOT_INVALID` (`0xFF`) without advancing `counter`.
                *imm = Imm(i64::from(IC_SLOT_INVALID));
            }
        }
    }
    Ok(counter)
}

/// Emission-time model of the PHYSICAL accumulator content (B4:
/// "acc-as-cache"). The accumulator is one physical location; register
/// allocation gives every value a register home, and this tracker records
/// — as an emission-time fact — which value's content the acc provably
/// holds at each point. `ensure_acc` consults it: a hit elides the `Lda`.
///
/// Soundness invariant: [`AccContent::Holds`]`(v)` is recorded ONLY at
/// points where the physical acc was just written with v's content (an
/// acc-writing instruction's result, the homing `Sta`, an `Lda(home v)`,
/// or exception dispatch), and every later acc write updates the tracker
/// (the helpers in this file are the only acc writers). A stale entry is
/// therefore impossible in the dangerous direction: a hit and a miss
/// always produce the same physical acc content. The worst a modeling gap
/// can do is forget a content (`Unknown`), costing a redundant `Lda`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AccContent {
    /// Frame-entry state: the vendor frame init leaves the hole in acc
    /// (arkcompiler_ets_runtime-master/ecmascript/interpreter/
    /// interpreter-inl.cpp:739, :1482). Never equal to a value's content.
    Hole,
    /// The physical acc provably holds this SSA value's content.
    Holds(ValueId),
    /// Unknown content: an acc-writing instruction whose result is not a
    /// tracked value, exception dispatch of an uncolored exception value,
    /// the meet of disagreeing predecessors, or a not-yet-emitted
    /// (back-edge) predecessor.
    Unknown,
}

/// Meet the acc content at a block entry over its already-emitted
/// predecessors: the content is known only when EVERY predecessor exits
/// with the SAME content. A predecessor without a recorded exit state (a
/// back edge — RPO emits it later — or an unreachable block) degrades the
/// meet to `Unknown`. Layout-inserted phi copies and trampolines are pure
/// `Mov`s (vendor `acc: none`) and never perturb the content across an
/// edge, so per-predecessor exit states are valid at successor entries.
fn meet_acc_content<'a>(
    preds: impl IntoIterator<Item = &'a abcd_ir::Edge>,
    exit_states: &HashMap<BlockId, AccContent>,
) -> AccContent {
    let mut meet: Option<AccContent> = None;
    for edge in preds {
        let state = exit_states
            .get(&edge.from)
            .copied()
            .unwrap_or(AccContent::Unknown);
        meet = Some(match (meet, state) {
            (None, s) => s,
            (Some(a), b) if a == b => a,
            _ => AccContent::Unknown,
        });
    }
    meet.unwrap_or(AccContent::Unknown)
}

/// Select instructions for a function.
pub fn select(
    module: &Module,
    func_id: FuncId,
    alloc: &RegAlloc,
    rpo: &[BlockId],
    suppression: &Suppression,
) -> Result<IselResult, LowerError> {
    select_with_options(
        module,
        func_id,
        alloc,
        rpo,
        suppression,
        crate::LowerOptions::default(),
    )
}

/// [`select`] with explicit [`crate::LowerOptions`].
pub fn select_with_options(
    module: &Module,
    func_id: FuncId,
    alloc: &RegAlloc,
    rpo: &[BlockId],
    suppression: &Suppression,
    _options: crate::LowerOptions,
) -> Result<IselResult, LowerError> {
    let mut block_codes: Vec<(BlockId, Vec<Bytecode>)> = Vec::new();
    let mut ic = IcAllocator::new();
    let mut tracer = EntityTracer {
        traces: HashMap::new(),
    };

    let Some(func) = module.func(func_id) else {
        return Err(LowerError::EmptyFunction(func_id));
    };
    let entry_block = func.entry().ok_or(LowerError::EmptyFunction(func_id))?;

    // Values with at least one use: an acc-writing instruction's result is
    // homed (`Sta`) only when it has a use — a dead result never leaves the
    // accumulator, so its acc content is `Unknown` to the tracker.
    // Suppressed values are never home-read (fusion).
    let mut used: HashSet<ValueId> = HashSet::new();
    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            if let Some(inst) = module.inst(inst_id) {
                used.extend(
                    inst.op
                        .operands()
                        .into_iter()
                        .filter(|v| !suppression.values.contains(v)),
                );
            }
        }
    }

    // Per-block EXIT acc content, filled as blocks are emitted (RPO: every
    // non-back-edge predecessor is emitted before its successors).
    let mut exit_states: HashMap<BlockId, AccContent> = HashMap::new();

    // R3-X4: handler block → all of its distinct `ExceptionParam` values across
    // `TryRegion`s targeting the handler. Each used value receives `acc` at entry.
    let mut handler_exc: HashMap<BlockId, Vec<ValueId>> = HashMap::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            let list = handler_exc.entry(catch.handler).or_default();
            if !list.contains(&catch.exception) {
                list.push(catch.exception);
            }
        }
    }
    let handler_blocks: HashSet<BlockId> = func
        .try_regions
        .iter()
        .flat_map(|region| region.catches.iter().map(|c| c.handler))
        .collect();

    let mut entry_consts = regalloc::frame_init_consts(module, func_id);
    entry_consts.sort_unstable_by(|a, b| b.cmp(a));

    let mut after_def_stores: HashMap<ValueId, Vec<(ValueId, ValueId)>> = HashMap::new();
    let mut block_start_stores: HashMap<BlockId, Vec<(ValueId, ValueId)>> = HashMap::new();
    for &(pred, src, dst) in &alloc.handler_phi_stores {
        let defined_in_pred = match module.value(src).map(|v| v.def) {
            Some(ValueDef::Inst(i)) => module
                .inst(i)
                .is_some_and(|inst| !inst.op.is_phi() && inst.block == pred),
            Some(ValueDef::Const(_)) => pred == entry_block,
            _ => false,
        };
        if defined_in_pred {
            after_def_stores.entry(src).or_default().push((src, dst));
        } else {
            block_start_stores.entry(pred).or_default().push((src, dst));
        }
    }
    for stores in block_start_stores.values_mut() {
        stores.sort_unstable();
    }
    for stores in after_def_stores.values_mut() {
        stores.sort_unstable();
    }

    let mut block_inst_pcs: HashMap<BlockId, Vec<(InstId, usize)>> =
        HashMap::with_capacity(rpo.len());
    let mut handler_prologue_len: HashMap<BlockId, usize> = HashMap::new();
    let mut ctx = IselCtx {
        func_id,
        module,
        alloc,
        used: &used,
        suppression,
        tracer: &mut tracer,
        ic: &mut ic,
        next_internal_label: 0x8000_0000,
        internal_labels: Vec::new(),
        bool_cond_blocks: HashSet::new(),
    };

    for &bb in rpo {
        let mut codes = Vec::new();
        let Some(block) = module.block(bb) else {
            continue;
        };

        let mut tracker = if bb == entry_block {
            AccContent::Hole
        } else if handler_blocks.contains(&bb) {
            AccContent::Unknown
        } else {
            meet_acc_content(&block.preds, &exit_states)
        };

        if bb == entry_block {
            emit_param_copy_in(func_id, module, alloc, &mut codes)?;
        }

        // N13 + R3-X4 + R3-M2: Home `acc` into every used `ExceptionParam` of `bb`
        // and record the prologue length so normal CFG jumps skip over it.
        if let Some(excs) = handler_exc.get(&bb) {
            let prol_start = codes.len();
            for &exc in excs {
                if let Some(&RegSlot::Reg(home)) = alloc.allocation.get(&exc) {
                    emit_sta_home(func_id, home, alloc, &mut codes)?;
                    tracker = AccContent::Holds(exc);
                }
            }
            let prol_len = codes.len() - prol_start;
            if prol_len > 0 {
                handler_prologue_len.insert(bb, prol_len);
            }
        }

        // R3-X3: Sequentialize parallel handler-phi stores in slot space so
        // swaps/WAR chains never overwrite an unread source.
        if let Some(stores) = block_start_stores.get(&bb) {
            emit_pinned_stores(func_id, stores, alloc, &mut codes)?;
        }

        if bb == entry_block {
            for &cval in &entry_consts {
                let Some(ValueDef::Const(cid)) = module.value(cval).map(|v| v.def) else {
                    continue;
                };
                let bc = const_load_bytecode(module, cid, func_id, ctx.tracer)?;
                codes.push(bc);
                if used.contains(&cval) {
                    let r = home_of(func_id, cval, alloc)?;
                    emit_sta_home(func_id, r, alloc, &mut codes)?;
                    tracker = AccContent::Holds(cval);
                } else {
                    tracker = AccContent::Unknown;
                }
                if let Some(stores) = after_def_stores.get(&cval) {
                    emit_pinned_stores(func_id, stores, alloc, &mut codes)?;
                }
            }
        }

        let mut local_pcs: Vec<(InstId, usize)> = Vec::with_capacity(block.insts.len());
        for &inst in &block.insts {
            local_pcs.push((inst, codes.len()));
            if suppression.insts.contains(&inst) {
                continue;
            }
            let Some(node) = module.inst(inst) else {
                continue;
            };

            ctx.select_inst(bb, node, &mut codes, &mut tracker)?;

            if let Some(v) = node.result
                && let Some(stores) = after_def_stores.get(&v)
            {
                emit_pinned_stores(func_id, stores, alloc, &mut codes)?;
            }
        }

        block_inst_pcs.insert(bb, local_pcs);
        exit_states.insert(bb, tracker);
        block_codes.push((bb, codes));
    }

    let internal_labels = ctx.internal_labels;
    let bool_cond_blocks = ctx.bool_cond_blocks;
    let dense_ic = ctx.ic.counter;
    let ic_size = rearrange_ic_slots(func_id, &mut block_codes, dense_ic)?;

    Ok(IselResult {
        block_codes,
        entity_traces: tracer.traces,
        ic_size,
        unsupported: None,
        block_inst_pcs,
        internal_labels,
        handler_prologue_len,
        bool_cond_blocks,
    })
}

/// Emit the copy-in prologue at the very start of the entry block: for each
/// parameter `i`, `Mov(home_i, Reg(num_regs + i))` moves the ABI top slot
/// into the parameter's vreg home. The vendor frame is
/// `num_vregs + num_args` with arguments in the top slots
/// (static_core/runtime/include/method.h); `to_method_body` declares
/// `num_vregs = num_regs`, so the arg slots of the lowered frame start
/// exactly at `Reg(num_regs)`. `alloc.num_regs` is final here — it already
/// includes the `copy_temp` reservation.
///
/// `mcs_color` pre-assigns every parameter a register home (there is no
/// accumulator coloring since B4), so an uncolored parameter can only come
/// from a hand-crafted allocation and is a hard error, never a silent
/// path. The prologue is pure `Mov`s (vendor `acc: none`) and does not
/// perturb the emission-time acc tracker.
///
/// Emission-point safety: `layout` inserts phi copies before predecessor
/// TERMINATORS (or into trampolines appended after all real blocks), never
/// at the start of a block, and the entry block has no predecessors in
/// practice — so code prepended at `codes[0..]` of the entry block cannot
/// interleave with phi-copy sequences.
fn emit_param_copy_in(
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    let Some(func) = module.func(func_id) else {
        return Err(LowerError::EmptyFunction(func_id));
    };
    for (i, &val) in func.params.iter().enumerate() {
        let home = home_of(func_id, val, alloc)?;
        let arg_slot = u32::from(alloc.num_regs) + i as u32;
        if arg_slot > u32::from(u16::MAX) {
            return Err(LowerError::RegisterOverflow(func_id));
        }
        codes.push(Bytecode::Mov(Reg(home), Reg(arg_slot as u16)));
    }
    Ok(())
}

/// Look up the register home allocation assigned to a value. A missing
/// entry means the operand was never colored (e.g. a dangling value
/// reference in unverified IR), which the old code silently treated as
/// acc-resident.
fn home_of(func_id: FuncId, val: ValueId, alloc: &RegAlloc) -> Result<u16, LowerError> {
    match alloc.allocation.get(&val).copied() {
        Some(RegSlot::Reg(r)) => Ok(r),
        None => Err(LowerError::UnallocatedOperand {
            func: func_id,
            value: val,
        }),
    }
}

/// Get the Reg for a value's register operand: its colored home.
///
/// High-register routing (S2): `sta`/`lda` are `op_v_8`-only in the vendored
/// ISA and — except for the auto-widening `mov` — every register operand
/// slot isel emits is u8-only as well (isa.yaml format audit: all `v`/`vN`
/// operands are `_8`; the `op_imm_16_v_8`-style second formats widen only
/// the imm). A value colored to a register ≥ 256 is therefore routed
/// through the reserved LOW scratch block (`RegAlloc::low_scratch_base`),
/// one scratch per operand position, so simultaneous operands never alias.
/// `operand_idx` is the operand's position within its instruction. The
/// emitted `mov` never touches the accumulator (vendor `acc: none`), so
/// the emission-time acc tracker is unaffected.
fn val_reg(
    func_id: FuncId,
    val: ValueId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    operand_idx: usize,
) -> Result<Reg, LowerError> {
    let r = home_of(func_id, val, alloc)?;
    if r <= 255 {
        return Ok(Reg(r));
    }
    let scratch = operand_scratch(func_id, alloc, operand_idx)?;
    codes.push(Bytecode::Mov(scratch, Reg(r)));
    Ok(scratch)
}

/// The low operand-routing scratch for position `idx` (high-register mode).
fn operand_scratch(func_id: FuncId, alloc: &RegAlloc, idx: usize) -> Result<Reg, LowerError> {
    let base = alloc
        .low_scratch_base
        .ok_or(LowerError::MissingLowScratch(func_id))?;
    if idx >= regalloc::LOW_OPERAND_SCRATCHES as usize {
        return Err(LowerError::LowScratchExhausted(func_id));
    }
    Ok(Reg(base + idx as u16))
}

/// The reserved low acc-routing scratch (high-register mode).
fn acc_scratch(func_id: FuncId, alloc: &RegAlloc) -> Result<Reg, LowerError> {
    alloc
        .low_scratch_base
        .map(|base| Reg(base + regalloc::LOW_OPERAND_SCRATCHES))
        .ok_or(LowerError::MissingLowScratch(func_id))
}

/// Emit `Sta(home)` for the register home `r` (a high home detours through
/// the reserved low acc scratch: `sta scratch; mov home, scratch`). `sta`
/// reads but never writes the accumulator (vendor `acc: in`), so the
/// emission-time acc tracker is the caller's concern.
fn emit_sta_home(
    func_id: FuncId,
    r: u16,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    if r <= 255 {
        codes.push(Bytecode::Sta(Reg(r)));
    } else {
        let scratch = acc_scratch(func_id, alloc)?;
        codes.push(Bytecode::Sta(scratch));
        codes.push(Bytecode::Mov(Reg(r), scratch));
    }
    Ok(())
}

/// Ensure a value's content is physically in the accumulator, consulting
/// the emission-time acc tracker (B4, acc-as-cache): a hit — the tracker
/// proves the acc already holds THIS value — is a no-op. A miss emits
/// `Lda(home)` (a high home first detours through the reserved low acc
/// scratch: `mov scratch, high; lda scratch`) and records the new content.
fn ensure_acc(
    tracker: &mut AccContent,
    func_id: FuncId,
    val: ValueId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    if *tracker == AccContent::Holds(val) {
        return Ok(());
    }
    let r = home_of(func_id, val, alloc)?;
    if r <= 255 {
        codes.push(Bytecode::Lda(Reg(r)));
    } else {
        let scratch = acc_scratch(func_id, alloc)?;
        codes.push(Bytecode::Mov(scratch, Reg(r)));
        codes.push(Bytecode::Lda(scratch));
    }
    *tracker = AccContent::Holds(val);
    Ok(())
}

/// Materialize one instruction's operands: resolve every register operand
/// to its home (high registers detour through a per-position low scratch —
/// `mov` never touches acc), then bring the acc operand into the
/// accumulator (tracker-aware: a hit elides the `Lda`).
///
/// The old spill-before-load dance (B3) is gone by construction: no
/// operand can be "acc-resident" anymore, because the accumulator is not a
/// coloring class — register operands always read their register homes,
/// and `ensure_acc` is the only acc writer here.
fn materialize_operands(
    tracker: &mut AccContent,
    func_id: FuncId,
    reg_operands: &[ValueId],
    acc_operand: Option<ValueId>,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Vec<Reg>, LowerError> {
    let mut regs = Vec::with_capacity(reg_operands.len());
    for (idx, &v) in reg_operands.iter().enumerate() {
        regs.push(val_reg(func_id, v, alloc, codes, idx)?);
    }
    if let Some(acc_val) = acc_operand {
        ensure_acc(tracker, func_id, acc_val, alloc, codes)?;
    }
    Ok(regs)
}

/// Home an acc-writing instruction's result and update the emission-time
/// acc tracker.
///
/// The instruction's bytecode just wrote the accumulator (vendor
/// `acc: out`/`acc: inout` — every result-producing opcode isel emits has
/// one of those modes). A result with at least one use gets a `Sta(home)`
/// and the tracker records that acc now holds the value — the next acc use
/// of it is a cache hit. A dead result (no uses) needs no store; the acc
/// content is then not a tracked value (`Unknown`), so the next acc use of
/// ANY value reloads from its home.
fn home_result(
    tracker: &mut AccContent,
    result: Option<ValueId>,
    used: &HashSet<ValueId>,
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    match result {
        Some(v) if used.contains(&v) => {
            let r = home_of(func_id, v, alloc)?;
            emit_sta_home(func_id, r, alloc, codes)?;
            *tracker = AccContent::Holds(v);
        }
        _ => *tracker = AccContent::Unknown,
    }
    Ok(())
}

/// Sequentialize and emit parallel handler-phi stores (`R3-X3`).
fn emit_pinned_stores(
    func_id: FuncId,
    stores: &[(ValueId, ValueId)],
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    let mut slot_pairs: Vec<(RegSlot, RegSlot)> = Vec::with_capacity(stores.len());
    for &(src, dst) in stores {
        let s = RegSlot::Reg(home_of(func_id, src, alloc)?);
        let d = RegSlot::Reg(home_of(func_id, dst, alloc)?);
        if s != d {
            slot_pairs.push((s, d));
        }
    }
    if slot_pairs.is_empty() {
        return Ok(());
    }
    let resolved = resolve_slot_copies(&slot_pairs, alloc.copy_temp)
        .map_err(|_| LowerError::MissingCopyTemp(func_id))?;
    for (s, d) in resolved {
        codes.push(emit_copy(s, d));
    }
    Ok(())
}

/// Canonical quiet-NaN bit pattern (`0x7ff8_0000_0000_0000`, `#60`).
const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

/// Materialize a scalar constant into `acc` (`#57`, `#60`).
fn const_load_bytecode(
    module: &Module,
    cid: ConstId,
    func_id: FuncId,
    tracer: &mut EntityTracer,
) -> Result<Bytecode, LowerError> {
    let Some(c) = module.consts.get(cid) else {
        return Err(LowerError::UnsupportedInstruction {
            func: func_id,
            message: format!("LoadConst of unknown constant {cid}"),
        });
    };
    Ok(match c {
        Const::Undefined => Bytecode::Ldundefined,
        Const::Hole => Bytecode::Ldhole,
        Const::Null | Const::LitNull(_) => Bytecode::Ldnull,
        Const::Bool(true) => Bytecode::Ldtrue,
        Const::Bool(false) => Bytecode::Ldfalse,
        Const::Int8(n) => Bytecode::Ldai(Imm(i64::from(*n))),
        Const::Int32(n) => Bytecode::Ldai(Imm(i64::from(*n as i32))),
        Const::Float32(bits) => {
            let f = f32::from_bits(*bits);
            if f.is_nan() {
                Bytecode::Ldnan
            } else if f == f32::INFINITY {
                Bytecode::Ldinfinity
            } else {
                let n = f64::from(f);
                if n == (n as i32) as f64 && !(n == 0.0 && n.is_sign_negative()) {
                    Bytecode::Ldai(Imm(n as i64))
                } else {
                    Bytecode::Fldai(Imm(n.to_bits() as i64))
                }
            }
        }
        Const::Number(bits) => {
            if *bits == CANONICAL_NAN_BITS {
                Bytecode::Ldnan
            } else if *bits == f64::INFINITY.to_bits() {
                Bytecode::Ldinfinity
            } else {
                let n = f64::from_bits(*bits);
                // N37: exclude `-0.0` from `ldai 0` so its sign bit survives.
                if !n.is_nan() && n == (n as i32) as f64 && !(n == 0.0 && n.is_sign_negative()) {
                    Bytecode::Ldai(Imm(n as i64))
                } else {
                    Bytecode::Fldai(Imm(*bits as i64))
                }
            }
        }
        Const::String(s) | Const::EtsImplements(s) => Bytecode::LdaStr(tracer.eid(*s)),
        Const::BigInt(s) => Bytecode::Ldbigint(tracer.eid(*s)),
        Const::Int64(_) | Const::UInt64(_) => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: format!(
                    "LoadConst of 64-bit static integer ({c:?}) has no dynamic .abc \
                     accumulator-load bytecode"
                ),
            });
        }
        Const::Accessor(_)
        | Const::MethodAffiliate(_)
        | Const::BuiltinTypeIndex(_)
        | Const::ArrayLiteral(_)
        | Const::TypedArrayLiteral { .. }
        | Const::ObjectLiteral { .. }
        | Const::LiteralBufferRef(_)
        | Const::MethodRef { .. } => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: format!(
                    "LoadConst of a literal shape / method reference ({c:?}) has no \
                     materialization bytecode — shapes flow through their dedicated ops"
                ),
            });
        }
    })
}

/// Recover the exact `0..=u32::MAX` immediate of a fused `*PropIdx` (`#61` `R3-X5`).
fn fused_index_u32(module: &Module, index: ValueId, suppression: &Suppression) -> Option<u32> {
    if !suppression.values.contains(&index) {
        return None;
    }
    let ValueDef::Inst(iid) = module.value(index)?.def else {
        return None;
    };
    let Op::LoadConst(cid) = &module.inst(iid)?.op else {
        return None;
    };
    const_u32_index(module.consts.get(*cid)?)
}

/// Whether `cond` is guaranteed to hold a runtime JS `Boolean` (`true`/`false`),
/// allowing `CondBranch` to omit `Bytecode::Istrue` and invert `jnez`/`jeqz` (`R3-X1`).
fn is_proven_boolean(module: &Module, cond: ValueId) -> bool {
    let Some(val) = module.value(cond) else {
        return false;
    };
    if matches!(
        val.ty,
        Ty::DynPrim(DynPrim::Bool) | Ty::Static(StaticTy::U1)
    ) {
        return true;
    }
    match val.def {
        ValueDef::Const(cid) => matches!(module.consts.get(cid), Some(Const::Bool(_))),
        ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::Compare { .. }) => true,
            Some(Op::UnaryOp { op, .. }) => op.is_boolean_result(),
            Some(Op::LoadConst(cid)) => matches!(module.consts.get(*cid), Some(Const::Bool(_))),
            _ => false,
        },
        _ => false,
    }
}

/// The [`FuncId`] of a `DefineFunc` body when `v` is (a possibly
/// closure-wrapped) fused define-chain value: directly a suppressed
/// `DefineFunc` result, or a suppressed `AllocClosure` result wrapping
/// one.
fn fused_definefunc_body(module: &Module, v: ValueId, suppression: &Suppression) -> Option<FuncId> {
    if !suppression.values.contains(&v) {
        return None;
    }
    let ValueDef::Inst(iid) = module.value(v)?.def else {
        return None;
    };
    match &module.inst(iid)?.op {
        Op::DefineFunc { body, .. } => Some(*body),
        Op::AllocClosure { func } => {
            let ValueDef::Inst(fiid) = module.value(*func)?.def else {
                return None;
            };
            let Op::DefineFunc { body, .. } = &module.inst(fiid)?.op else {
                return None;
            };
            Some(*body)
        }
        _ => None,
    }
}

struct IselCtx<'a> {
    func_id: FuncId,
    module: &'a Module,
    alloc: &'a RegAlloc,
    used: &'a HashSet<ValueId>,
    suppression: &'a Suppression,
    tracer: &'a mut EntityTracer,
    ic: &'a mut IcAllocator,
    next_internal_label: u32,
    internal_labels: Vec<(u32, BlockId, usize)>,
    bool_cond_blocks: HashSet<BlockId>,
}

impl<'a> IselCtx<'a> {
    fn alloc_label(&mut self) -> u32 {
        let id = self.next_internal_label;
        self.next_internal_label += 1;
        id
    }

    fn select_inst(
        &mut self,
        bb: BlockId,
        node: &abcd_ir::Inst,
        codes: &mut Vec<Bytecode>,
        tracker: &mut AccContent,
    ) -> Result<(), LowerError> {
        let func_id = self.func_id;
        let module = self.module;
        let alloc = self.alloc;
        let used = self.used;
        let suppression = self.suppression;
        let data = &node.op;
        let result = node.result;
        match data {
            // ── Constants ────────────────────────────────────────────────
            Op::LoadConst(cid) => {
                let bc = const_load_bytecode(module, *cid, func_id, self.tracer)?;
                codes.push(bc);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Binary / Compare / Unary ─────────────────────────────────
            Op::BinaryOp { op, left, right } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*right], Some(*left), alloc, codes)?;
                let r = regs[0];
                let bc = match op {
                    BinOp::Add => Bytecode::Add2(self.ic.one(), r),
                    BinOp::Sub => Bytecode::Sub2(self.ic.one(), r),
                    BinOp::Mul => Bytecode::Mul2(self.ic.one(), r),
                    BinOp::Div => Bytecode::Div2(self.ic.one(), r),
                    BinOp::Mod => Bytecode::Mod2(self.ic.one(), r),
                    BinOp::Exp => Bytecode::Exp(self.ic.one(), r),
                    BinOp::Shl => Bytecode::Shl2(self.ic.one(), r),
                    BinOp::Shr => Bytecode::Shr2(self.ic.one(), r),
                    BinOp::Ashr => Bytecode::Ashr2(self.ic.one(), r),
                    BinOp::BitAnd => Bytecode::And2(self.ic.one(), r),
                    BinOp::BitOr => Bytecode::Or2(self.ic.one(), r),
                    BinOp::BitXor => Bytecode::Xor2(self.ic.one(), r),
                };
                codes.push(bc);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::Compare { op, left, right } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*right], Some(*left), alloc, codes)?;
                let r = regs[0];
                let bc = match op {
                    CmpOp::Eq => Bytecode::Eq(self.ic.one(), r),
                    CmpOp::NotEq => Bytecode::Noteq(self.ic.one(), r),
                    CmpOp::StrictEq => Bytecode::Stricteq(self.ic.one(), r),
                    CmpOp::StrictNotEq => Bytecode::Strictnoteq(self.ic.one(), r),
                    CmpOp::Less => Bytecode::Less(self.ic.one(), r),
                    CmpOp::LessEq => Bytecode::Lesseq(self.ic.one(), r),
                    CmpOp::Greater => Bytecode::Greater(self.ic.one(), r),
                    CmpOp::GreaterEq => Bytecode::Greatereq(self.ic.one(), r),
                    CmpOp::In => Bytecode::Isin(self.ic.one(), r),
                    // R3-X2: `instanceof` occupies TWO IC slots in isa.yaml:794.
                    CmpOp::InstanceOf => Bytecode::Instanceof(self.ic.two(), r),
                };
                codes.push(bc);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::UnaryOp { op, operand } => {
                ensure_acc(tracker, func_id, *operand, alloc, codes)?;
                match op {
                    UnOp::JumpEqz | UnOp::JumpNez => {
                        if let Some(v) = result
                            && used.contains(&v)
                        {
                            let lbl_true = self.alloc_label();
                            let lbl_done = self.alloc_label();
                            codes.push(match op {
                                UnOp::JumpEqz => Bytecode::Jeqz(Label(lbl_true)),
                                _ => Bytecode::Jnez(Label(lbl_true)),
                            });
                            codes.push(Bytecode::Ldfalse);
                            codes.push(Bytecode::Jmp(Label(lbl_done)));
                            self.internal_labels.push((lbl_true, bb, codes.len()));
                            codes.push(Bytecode::Ldtrue);
                            self.internal_labels.push((lbl_done, bb, codes.len()));
                            home_result(tracker, result, used, func_id, alloc, codes)?;
                        } else {
                            *tracker = AccContent::Unknown;
                        }
                    }
                    _ => {
                        let bc = match op {
                            UnOp::Minus => Bytecode::Neg(self.ic.one()),
                            // R3-M1: JS `!x` is `isfalse` (boolean negation), NEVER bitwise `not`!
                            UnOp::LogicalNot | UnOp::IsFalse => Bytecode::Isfalse,
                            UnOp::Inc => Bytecode::Inc(self.ic.one()),
                            UnOp::Dec => Bytecode::Dec(self.ic.one()),
                            // R3-X2: `typeof` occupies TWO IC slots in isa.yaml:700.
                            UnOp::TypeOf => Bytecode::Typeof(self.ic.two()),
                            UnOp::ToNumber => Bytecode::Tonumber(self.ic.one()),
                            UnOp::ToNumeric => Bytecode::Tonumeric(self.ic.one()),
                            UnOp::ToPropertyKey => Bytecode::CallruntimeTopropertykey,
                            UnOp::BitNot => Bytecode::Not(self.ic.one()),
                            UnOp::Void => Bytecode::Ldundefined,
                            UnOp::IsTrue => Bytecode::Istrue,
                            UnOp::JumpEqz | UnOp::JumpNez => unreachable!("handled above"),
                        };
                        codes.push(bc);
                        home_result(tracker, result, used, func_id, alloc, codes)?;
                    }
                }
            }
            Op::Mov { src } => {
                // Pure register copy: no accumulator involvement (vendor
                // `mov` is `acc: none`). Never produced by `abcd-lift`, but
                // lowered for IR completeness.
                if let Some(v) = result
                    && used.contains(&v)
                {
                    let d = home_of(func_id, v, alloc)?;
                    let s = home_of(func_id, *src, alloc)?;
                    if s != d {
                        codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                    }
                }
            }

            // ── Object / Array creation ──────────────────────────────────
            Op::AllocObject { shape } => {
                match module.consts.get(*shape) {
                    Some(Const::ObjectLiteral { keys, values })
                        if keys.is_empty() && values.is_empty() =>
                    {
                        codes.push(Bytecode::Createemptyobject);
                    }
                    Some(Const::ObjectLiteral { .. }) | Some(Const::ArrayLiteral(_)) => {
                        codes.push(Bytecode::Createobjectwithbuffer(
                            self.ic.one(),
                            self.tracer.literal_eid(*shape),
                        ));
                    }
                    _ => {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: format!(
                                "AllocObject shape {shape} is not a literal object/array shape"
                            ),
                        });
                    }
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AllocArray { shape } => {
                match shape {
                    None => {
                        codes.push(Bytecode::Createemptyarray(self.ic.one()));
                    }
                    Some(shape) => {
                        codes.push(Bytecode::Createarraywithbuffer(
                            self.ic.one(),
                            self.tracer.literal_eid(*shape),
                        ));
                    }
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AllocRegExp { pattern, flags } => {
                // R3-X2: `createregexpwithliteral` occupies TWO IC slots in isa.yaml:529.
                codes.push(Bytecode::Createregexpwithliteral(
                    self.ic.two(),
                    self.tracer.eid(*pattern),
                    Imm(i64::from(*flags)),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AllocClosure { func } => {
                if suppression.values.contains(func) {
                    let Some(ValueDef::Inst(fiid)) = module.value(*func).map(|v| v.def) else {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: "AllocClosure of a non-instruction value".into(),
                        });
                    };
                    let Some(finst) = module.inst(fiid) else {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: "AllocClosure of a dangling DefineFunc".into(),
                        });
                    };
                    let Op::DefineFunc { body, length, .. } = &finst.op else {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: "AllocClosure of a non-DefineFunc value".into(),
                        });
                    };
                    codes.push(Bytecode::Definefunc(
                        self.ic.one(),
                        self.tracer.method_eid(*body),
                        Imm(i64::from(*length)),
                    ));
                    home_result(tracker, result, used, func_id, alloc, codes)?;
                } else if let Some(v) = result
                    && used.contains(&v)
                {
                    let d = home_of(func_id, v, alloc)?;
                    let s = home_of(func_id, *func, alloc)?;
                    if s != d {
                        codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                    }
                }
            }
            Op::CreateObjectWithExcludedKeys { obj, keys } => {
                // #55: `createobjectwithexcludedkeys` has `range_1` (`isa.yaml:498`),
                // reading `imm + 1` consecutive key registers (`imm = keys.len() - 1`).
                // Empty `keys` (`let { ...rest } = obj`) lowers via `createemptyobject`
                // + `copydataproperties` using the reserved 1-slot call window.
                if keys.is_empty() {
                    let wbase = alloc
                        .call_window_base
                        .ok_or(LowerError::MissingCallWindow(func_id))?;
                    if wbase > 255 {
                        return Err(LowerError::CallWindowOverflow(func_id));
                    }
                    codes.push(Bytecode::Createemptyobject);
                    codes.push(Bytecode::Sta(Reg(wbase)));
                    ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                    codes.push(Bytecode::Copydataproperties(Reg(wbase)));
                    home_result(tracker, result, used, func_id, alloc, codes)?;
                } else {
                    let imm_val = keys.len() - 1;
                    if imm_val > usize::from(u16::MAX) {
                        return Err(LowerError::CallArgcOverflow {
                            func: func_id,
                            argc: keys.len(),
                        });
                    }
                    let regs = materialize_operands(tracker, func_id, &[*obj], None, alloc, codes)?;
                    let obj_r = regs[0];
                    let start_r = fill_excluded_keys_window(func_id, keys, alloc, codes)?;
                    let imm = Imm(imm_val as i64);
                    let bc = if imm_val <= 255 {
                        Bytecode::Createobjectwithexcludedkeys(imm, obj_r, start_r)
                    } else {
                        Bytecode::WideCreateobjectwithexcludedkeys(imm, obj_r, start_r)
                    };
                    codes.push(bc);
                    home_result(tracker, result, used, func_id, alloc, codes)?;
                }
            }
            Op::SetObjectWithProto { proto, obj } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*proto], Some(*obj), alloc, codes)?;
                codes.push(Bytecode::Setobjectwithproto(self.ic.two(), regs[0]));
            }

            // ── Property access ──────────────────────────────────────────
            Op::LoadProp { object, name } => {
                ensure_acc(tracker, func_id, *object, alloc, codes)?;
                codes.push(Bytecode::Ldobjbyname(self.ic.two(), self.tracer.eid(*name)));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StoreProp {
                object,
                name,
                value,
            } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stobjbyname(
                    self.ic.two(),
                    self.tracer.eid(*name),
                    regs[0],
                ));
            }
            Op::LoadPropDyn { object, key } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*object], Some(*key), alloc, codes)?;
                codes.push(Bytecode::Ldobjbyvalue(self.ic.two(), regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StorePropDyn { object, key, value } => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*object, *key],
                    Some(*value),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Stobjbyvalue(self.ic.two(), regs[0], regs[1]));
            }
            Op::LoadPropIdx { object, index } => {
                // R3-X5 + R3-H7: Exact `0..=u32::MAX` fused index selects narrow/wide
                // `ldobjbyindex`; any non-constant / out-of-range / `-0.0` / multi-use
                // index falls back to `ldobjbyvalue`.
                if let Some(idx) = fused_index_u32(module, *index, suppression) {
                    ensure_acc(tracker, func_id, *object, alloc, codes)?;
                    if idx <= u32::from(u16::MAX) {
                        codes.push(Bytecode::Ldobjbyindex(self.ic.two(), Imm(i64::from(idx))));
                    } else {
                        codes.push(Bytecode::WideLdobjbyindex(Imm(i64::from(idx))));
                    }
                } else {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*object],
                        Some(*index),
                        alloc,
                        codes,
                    )?;
                    codes.push(Bytecode::Ldobjbyvalue(self.ic.two(), regs[0]));
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StorePropIdx {
                object,
                index,
                value,
            } => {
                if let Some(idx) = fused_index_u32(module, *index, suppression) {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*object],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    if idx <= u32::from(u16::MAX) {
                        codes.push(Bytecode::Stobjbyindex(
                            self.ic.two(),
                            regs[0],
                            Imm(i64::from(idx)),
                        ));
                    } else {
                        codes.push(Bytecode::WideStobjbyindex(regs[0], Imm(i64::from(idx))));
                    }
                } else {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*object, *index],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    codes.push(Bytecode::Stobjbyvalue(self.ic.two(), regs[0], regs[1]));
                }
            }
            Op::StoreOwnPropName {
                object,
                name,
                value,
                kind,
            } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
                let eid = self.tracer.eid(*name);
                let bc = match kind {
                    OwnStoreKind::OwnProp => Bytecode::Stownbyname(self.ic.two(), eid, regs[0]),
                    OwnStoreKind::OwnPropWithNameSet => {
                        Bytecode::Stownbynamewithnameset(self.ic.two(), eid, regs[0])
                    }
                    OwnStoreKind::ClassField => {
                        Bytecode::Definefieldbyname(self.ic.two(), eid, regs[0])
                    }
                    OwnStoreKind::DefineProperty => {
                        Bytecode::Definepropertybyname(self.ic.two(), eid, regs[0])
                    }
                };
                codes.push(bc);
            }
            Op::StoreOwnPropDyn {
                object,
                key,
                value,
                kind,
            } => {
                if matches!(kind, OwnStoreKind::DefineProperty) {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "StoreOwnPropDyn with OwnStoreKind::DefineProperty has no opcode"
                            .into(),
                    });
                }
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*object, *key],
                    Some(*value),
                    alloc,
                    codes,
                )?;
                let bc = match kind {
                    OwnStoreKind::OwnProp => {
                        Bytecode::Stownbyvalue(self.ic.two(), regs[0], regs[1])
                    }
                    OwnStoreKind::OwnPropWithNameSet => {
                        Bytecode::Stownbyvaluewithnameset(self.ic.two(), regs[0], regs[1])
                    }
                    OwnStoreKind::ClassField => {
                        Bytecode::CallruntimeDefinefieldbyvalue(self.ic.two(), regs[0], regs[1])
                    }
                    OwnStoreKind::DefineProperty => unreachable!("rejected above"),
                };
                codes.push(bc);
            }
            Op::StoreOwnPropIdx {
                object,
                index,
                value,
                kind,
            } => {
                if !matches!(kind, OwnStoreKind::OwnProp | OwnStoreKind::ClassField) {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!("StoreOwnPropIdx has no encoding for {kind:?}"),
                    });
                }
                if let Some(idx) = fused_index_u32(module, *index, suppression) {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*object],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    match kind {
                        OwnStoreKind::OwnProp => {
                            if idx <= u32::from(u16::MAX) {
                                codes.push(Bytecode::Stownbyindex(
                                    self.ic.two(),
                                    regs[0],
                                    Imm(i64::from(idx)),
                                ));
                            } else {
                                codes
                                    .push(Bytecode::WideStownbyindex(regs[0], Imm(i64::from(idx))));
                            }
                        }
                        OwnStoreKind::ClassField => {
                            codes.push(Bytecode::CallruntimeDefinefieldbyindex(
                                self.ic.two(),
                                Imm(i64::from(idx)),
                                regs[0],
                            ));
                        }
                        _ => unreachable!("checked above"),
                    }
                } else {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*object, *index],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    let bc = match kind {
                        OwnStoreKind::OwnProp => {
                            Bytecode::Stownbyvalue(self.ic.two(), regs[0], regs[1])
                        }
                        OwnStoreKind::ClassField => {
                            Bytecode::CallruntimeDefinefieldbyvalue(self.ic.two(), regs[0], regs[1])
                        }
                        _ => unreachable!("checked above"),
                    };
                    codes.push(bc);
                }
            }
            Op::DeleteProp { object, key } => {
                // Vendor (N65): `delobjprop v0` takes the OBJECT in the
                // register operand and the KEY in acc.
                let regs =
                    materialize_operands(tracker, func_id, &[*object], Some(*key), alloc, codes)?;
                codes.push(Bytecode::Delobjprop(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::TestProp { .. } => {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "TestProp has no v0.1 lowering equivalent (never produced by \
                     the lift; the `in` family lowers through Compare)"
                        .into(),
                });
            }
            Op::CopyDataProps { dst, src } => {
                // Vendor `copydataproperties v:in:top, acc: inout:top`: the
                // register operand is the target, the accumulator carries the
                // source (and receives the result). dst is resolved to its
                // home first, then src is brought into acc (tracker-aware).
                // No entity operands — nothing for the tracer/relocation
                // channel. The bytecode writes acc but the IR instruction has
                // no result, so the acc content is afterwards untracked.
                let regs =
                    materialize_operands(tracker, func_id, &[*dst], Some(*src), alloc, codes)?;
                codes.push(Bytecode::Copydataproperties(regs[0]));
                *tracker = AccContent::Unknown;
            }
            Op::ArraySpread { dst, index, src } => {
                // Vendor `starrayspread v1:in:top, v2:in:top, acc: inout:top`
                // (isa.yaml:1329-1332): v1 = destination array, v2 = start
                // index, acc = source iterable; acc out = the NEW INDEX (the
                // IR result). Register operands first, then the acc operand
                // (B3 ordering); the result is homed per `acc: inout`.
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*dst, *index],
                    Some(*src),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Starrayspread(regs[0], regs[1]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Private properties ───────────────────────────────────────
            Op::LoadPrivate { level, slot, obj } => {
                ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                codes.push(Bytecode::Ldprivateproperty(
                    self.ic.two(),
                    Imm(*level as i64),
                    Imm(*slot as i64),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StorePrivate {
                level,
                slot,
                obj,
                value,
            } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*obj], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stprivateproperty(
                    self.ic.two(),
                    Imm(*level as i64),
                    Imm(*slot as i64),
                    regs[0],
                ));
            }
            Op::DefinePrivate {
                level,
                slot,
                obj,
                value,
            } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*obj], Some(*value), alloc, codes)?;
                codes.push(Bytecode::CallruntimeDefineprivateproperty(
                    self.ic.two(),
                    Imm(*level as i64),
                    Imm(*slot as i64),
                    regs[0],
                ));
            }
            Op::TestPrivate { level, slot, obj } => {
                ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                codes.push(Bytecode::Testin(
                    self.ic.two(),
                    Imm(*level as i64),
                    Imm(*slot as i64),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::CreatePrivateNames { count, names } => {
                codes.push(Bytecode::CallruntimeCreateprivateproperty(
                    Imm(*count as i64),
                    self.tracer.literal_eid(*names),
                ));
            }
            Op::LoadSuper { key, this_value } => {
                match key {
                    SuperKey::Name(name) => {
                        // R3-H1: `ldsuperbyname` reads `this_value` from `acc` (`acc: inout:top`).
                        ensure_acc(tracker, func_id, *this_value, alloc, codes)?;
                        codes.push(Bytecode::Ldsuperbyname(
                            self.ic.two(),
                            self.tracer.eid(*name),
                        ));
                    }
                    SuperKey::Dynamic(k) => {
                        let regs = materialize_operands(
                            tracker,
                            func_id,
                            &[*this_value],
                            Some(*k),
                            alloc,
                            codes,
                        )?;
                        codes.push(Bytecode::Ldsuperbyvalue(self.ic.two(), regs[0]));
                    }
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StoreSuper {
                key,
                this_value,
                value,
            } => match key {
                SuperKey::Name(name) => {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*this_value],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    codes.push(Bytecode::Stsuperbyname(
                        self.ic.two(),
                        self.tracer.eid(*name),
                        regs[0],
                    ));
                }
                SuperKey::Dynamic(k) => {
                    let regs = materialize_operands(
                        tracker,
                        func_id,
                        &[*this_value, *k],
                        Some(*value),
                        alloc,
                        codes,
                    )?;
                    codes.push(Bytecode::Stsuperbyvalue(self.ic.two(), regs[0], regs[1]));
                }
            },

            // ── Global variables ─────────────────────────────────────────
            Op::TryGetGlobal { name, default } => {
                match default {
                    None => {
                        codes.push(Bytecode::Ldglobalvar(self.ic.one(), self.tracer.eid(*name)));
                    }
                    Some(dflt) => {
                        let fused = suppression.values.contains(dflt)
                            || matches!(
                                module.value(*dflt).map(|v| v.def),
                                Some(ValueDef::Const(cid))
                                    if matches!(module.consts.get(cid), Some(Const::Undefined))
                            );
                        if !fused {
                            return Err(LowerError::UnsupportedInstruction {
                                func: func_id,
                                message: "TryGetGlobal with a non-undefined default has no \
                                 vendor encoding (tryldglobalbyname's fallback is undefined)"
                                    .into(),
                            });
                        }
                        codes.push(Bytecode::Tryldglobalbyname(
                            self.ic.one(),
                            self.tracer.eid(*name),
                        ));
                    }
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StoreGlobal { name, value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::Stglobalvar(self.ic.one(), self.tracer.eid(*name)));
            }
            Op::StoreGlobalRecord {
                name,
                value,
                is_const,
            } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                let eid = self.tracer.eid(*name);
                codes.push(if *is_const {
                    Bytecode::Stconsttoglobalrecord(self.ic.one(), eid)
                } else {
                    Bytecode::Sttoglobalrecord(self.ic.one(), eid)
                });
            }
            Op::TryStoreGlobal { name, value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::Trystglobalbyname(
                    self.ic.one(),
                    self.tracer.eid(*name),
                ));
            }

            // ── Lexical variables (`#55` `LexEnvKind` + `R3-H7` `wide.*`) ──
            Op::GetLexVar { level, slot, kind } => {
                let bc = match kind {
                    LexEnvKind::Plain => {
                        if *level <= 255 && *slot <= 255 {
                            Bytecode::Ldlexvar(Imm(i64::from(*level)), Imm(i64::from(*slot)))
                        } else {
                            Bytecode::WideLdlexvar(Imm(i64::from(*level)), Imm(i64::from(*slot)))
                        }
                    }
                    LexEnvKind::Sendable => {
                        if *level <= 255 && *slot <= 255 {
                            Bytecode::CallruntimeLdsendablevar(
                                Imm(i64::from(*level)),
                                Imm(i64::from(*slot)),
                            )
                        } else {
                            Bytecode::CallruntimeWideldsendablevar(
                                Imm(i64::from(*level)),
                                Imm(i64::from(*slot)),
                            )
                        }
                    }
                    LexEnvKind::Patch => {
                        if *level != 0 {
                            return Err(LowerError::UnsupportedInstruction {
                                func: func_id,
                                message: format!("GetLexVar Patch requires level 0, got {level}"),
                            });
                        }
                        Bytecode::WideLdpatchvar(Imm(i64::from(*slot)))
                    }
                };
                codes.push(bc);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::PutLexVar {
                level,
                slot,
                value,
                kind,
            } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                let bc = match kind {
                    LexEnvKind::Plain => {
                        if *level <= 255 && *slot <= 255 {
                            Bytecode::Stlexvar(Imm(i64::from(*level)), Imm(i64::from(*slot)))
                        } else {
                            Bytecode::WideStlexvar(Imm(i64::from(*level)), Imm(i64::from(*slot)))
                        }
                    }
                    LexEnvKind::Sendable => {
                        if *level <= 255 && *slot <= 255 {
                            Bytecode::CallruntimeStsendablevar(
                                Imm(i64::from(*level)),
                                Imm(i64::from(*slot)),
                            )
                        } else {
                            Bytecode::CallruntimeWidestsendablevar(
                                Imm(i64::from(*level)),
                                Imm(i64::from(*slot)),
                            )
                        }
                    }
                    LexEnvKind::Patch => {
                        if *level != 0 {
                            return Err(LowerError::UnsupportedInstruction {
                                func: func_id,
                                message: format!("PutLexVar Patch requires level 0, got {level}"),
                            });
                        }
                        Bytecode::WideStpatchvar(Imm(i64::from(*slot)))
                    }
                };
                codes.push(bc);
            }
            Op::NewLexEnv { num_vars, kind } => match kind {
                LexEnvKind::Plain => {
                    if *num_vars <= 255 {
                        codes.push(Bytecode::Newlexenv(Imm(i64::from(*num_vars))));
                    } else {
                        codes.push(Bytecode::WideNewlexenv(Imm(i64::from(*num_vars))));
                    }
                    home_result(tracker, result, used, func_id, alloc, codes)?;
                }
                LexEnvKind::Sendable => {
                    if *num_vars <= 255 {
                        codes.push(Bytecode::CallruntimeNewsendableenv(Imm(i64::from(
                            *num_vars,
                        ))));
                    } else {
                        codes.push(Bytecode::CallruntimeWidenewsendableenv(Imm(i64::from(
                            *num_vars,
                        ))));
                    }
                    if let Some(v) = result
                        && used.contains(&v)
                    {
                        home_result(tracker, result, used, func_id, alloc, codes)?;
                    }
                }
                LexEnvKind::Patch => {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "NewLexEnv cannot use LexEnvKind::Patch".into(),
                    });
                }
            },
            Op::NewLexEnvWithName {
                num_vars,
                scope_names,
            } => {
                let eid = self.tracer.literal_eid(*scope_names);
                if *num_vars <= 255 {
                    codes.push(Bytecode::Newlexenvwithname(Imm(i64::from(*num_vars)), eid));
                } else {
                    codes.push(Bytecode::WideNewlexenvwithname(
                        Imm(i64::from(*num_vars)),
                        eid,
                    ));
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::PopLexEnv => {
                codes.push(Bytecode::Poplexenv);
            }

            // ── Module variables ─────────────────────────────────────────
            Op::LoadModuleVar { index, kind } => {
                use abcd_ir::ModuleVarKind;
                let bc = match (*kind, u8::try_from(*index), u16::try_from(*index)) {
                    (ModuleVarKind::Local, Ok(n), _) => {
                        Bytecode::Ldlocalmodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::Local, Err(_), Ok(w)) => {
                        Bytecode::WideLdlocalmodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::External, Ok(n), _) => {
                        Bytecode::Ldexternalmodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::External, Err(_), Ok(w)) => {
                        Bytecode::WideLdexternalmodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::Lazy, Ok(n), _) => {
                        Bytecode::CallruntimeLdlazymodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::Lazy, Err(_), Ok(w)) => {
                        Bytecode::CallruntimeWideldlazymodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::SendableLocal, Ok(n), _) => {
                        Bytecode::CallruntimeLdsendablelocalmodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::SendableLocal, Err(_), Ok(w)) => {
                        Bytecode::CallruntimeWideldsendablelocalmodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::SendableExternal, Ok(n), _) => {
                        Bytecode::CallruntimeLdsendableexternalmodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::SendableExternal, Err(_), Ok(w)) => {
                        Bytecode::CallruntimeWideldsendableexternalmodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::LazySendable, Ok(n), _) => {
                        Bytecode::CallruntimeLdlazysendablemodulevar(Imm(i64::from(n)))
                    }
                    (ModuleVarKind::LazySendable, Err(_), Ok(w)) => {
                        Bytecode::CallruntimeWideldlazysendablemodulevar(Imm(i64::from(w)))
                    }
                    (ModuleVarKind::SendableClass, _, Ok(w)) => {
                        Bytecode::CallruntimeLdsendableclass(Imm(i64::from(w)))
                    }
                    (_, _, Err(_)) => {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: format!("LoadModuleVar index {index} exceeds u16::MAX"),
                        });
                    }
                };
                codes.push(bc);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::StoreModuleVar { index, value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                if let Ok(n) = u8::try_from(*index) {
                    codes.push(Bytecode::Stmodulevar(Imm(i64::from(n))));
                } else if let Ok(w) = u16::try_from(*index) {
                    codes.push(Bytecode::WideStmodulevar(Imm(i64::from(w))));
                } else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!("StoreModuleVar index {index} exceeds u16::MAX"),
                    });
                }
            }
            Op::GetModuleNamespace { index } => {
                if let Ok(n) = u8::try_from(*index) {
                    codes.push(Bytecode::Getmodulenamespace(Imm(i64::from(n))));
                } else if let Ok(w) = u16::try_from(*index) {
                    codes.push(Bytecode::WideGetmodulenamespace(Imm(i64::from(w))));
                } else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!("GetModuleNamespace index {index} exceeds u16::MAX"),
                    });
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::DynamicImport { specifier } => {
                ensure_acc(tracker, func_id, *specifier, alloc, codes)?;
                codes.push(Bytecode::Dynamicimport);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Function / Class definition ──────────────────────────────
            Op::DefineFunc {
                body,
                captures,
                length,
            } => {
                if !captures.is_empty() {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "DefineFunc with explicit captures has no vendor encoding \
                         (es2abc closure captures are lexenv-based)"
                            .into(),
                    });
                }
                codes.push(Bytecode::Definefunc(
                    self.ic.one(),
                    self.tracer.method_eid(*body),
                    Imm(i64::from(*length)),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::DefineMethod {
                object,
                func,
                length,
                ..
            } => {
                let Some(body) = fused_definefunc_body(module, *func, suppression) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "DefineMethod of a non-fused closure (expected the lift's \
                         DefineFunc + AllocClosure chain)"
                            .into(),
                    });
                };
                ensure_acc(tracker, func_id, *object, alloc, codes)?;
                codes.push(Bytecode::Definemethod(
                    self.ic.one(),
                    self.tracer.method_eid(body),
                    Imm(i64::from(*length)),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::DefineClass(cls) => {
                let DefineClassData {
                    ctor,
                    heritage,
                    members,
                    member_attrs: _,
                    count,
                } = cls.as_ref();
                let Some(base) = heritage else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "DefineClass without a heritage register has no \
                         defineclasswithbuffer encoding"
                            .into(),
                    });
                };
                let base_r = val_reg(func_id, *base, alloc, codes, 0)?;
                codes.push(Bytecode::Defineclasswithbuffer(
                    self.ic.one(),
                    self.tracer.method_eid(*ctor),
                    self.tracer.literal_eid(*members),
                    Imm(i64::from(*count)),
                    base_r,
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::DefineSendableClass(cls) => {
                let DefineClassData {
                    ctor,
                    heritage,
                    members,
                    member_attrs: _,
                    count,
                } = cls.as_ref();
                let Some(base) = heritage else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "DefineSendableClass without a heritage register has no \
                         callruntime.definesendableclass encoding"
                            .into(),
                    });
                };
                let base_r = val_reg(func_id, *base, alloc, codes, 0)?;
                codes.push(Bytecode::CallruntimeDefinesendableclass(
                    self.ic.one(),
                    self.tracer.method_eid(*ctor),
                    self.tracer.literal_eid(*members),
                    Imm(i64::from(*count)),
                    base_r,
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::DefineGetterSetterByValue {
                obj,
                key,
                getter,
                setter,
                set_name,
            } => {
                // R3-H2: `definegettersetterbyvalue` takes `set_name` boolean in `acc`!
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*obj, *key, *getter, *setter],
                    Some(*set_name),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Definegettersetterbyvalue(
                    regs[0], regs[1], regs[2], regs[3],
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Calls ────────────────────────────────────────────────────
            Op::Call {
                callee,
                this,
                args,
                kind,
            } => {
                self.select_call(*kind, *callee, *this, args, codes, tracker)?;
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Special value loaders ────────────────────────────────────
            Op::LoadSymbol => {
                codes.push(Bytecode::Ldsymbol);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::LoadNewTarget => {
                codes.push(Bytecode::Ldnewtarget);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::LoadGlobalObject => {
                codes.push(Bytecode::Ldglobal);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::LoadFunction => {
                codes.push(Bytecode::Ldfunction);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::GetUnmappedArgs => {
                codes.push(Bytecode::Getunmappedargs);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::CopyRestArgs { start_index } => {
                if *start_index <= 255 {
                    codes.push(Bytecode::Copyrestargs(Imm(i64::from(*start_index))));
                } else {
                    codes.push(Bytecode::WideCopyrestargs(Imm(i64::from(*start_index))));
                }
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::GetTemplateObject { literal } => {
                ensure_acc(tracker, func_id, *literal, alloc, codes)?;
                codes.push(Bytecode::Gettemplateobject(self.ic.one()));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Iterators ────────────────────────────────────────────────
            Op::GetIterator { obj } => {
                ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                codes.push(Bytecode::Getiterator(self.ic.two()));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::GetAsyncIterator { obj } => {
                ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                codes.push(Bytecode::Getasynciterator(self.ic.two()));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::GetPropIterator { obj } => {
                ensure_acc(tracker, func_id, *obj, alloc, codes)?;
                codes.push(Bytecode::Getpropiterator);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::IteratorNext { .. } | Op::IteratorThrow { .. } => {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "IteratorNext/IteratorThrow has no v0.1 lowering equivalent \
                     (never produced by the lift)"
                        .into(),
                });
            }
            Op::IteratorReturn { iterator } => {
                let iter_r = val_reg(func_id, *iterator, alloc, codes, 0)?;
                codes.push(Bytecode::Closeiterator(self.ic.two(), iter_r));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::NextPropName { iterator } => {
                let iter_r = val_reg(func_id, *iterator, alloc, codes, 0)?;
                codes.push(Bytecode::Getnextpropname(iter_r));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Generator / Async / Concurrent (`#55`) ───────────────────
            Op::CreateGenerator { func } => {
                let func_r = val_reg(func_id, *func, alloc, codes, 0)?;
                codes.push(Bytecode::Creategeneratorobj(func_r));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::CreateAsyncGenerator { func } => {
                let func_r = val_reg(func_id, *func, alloc, codes, 0)?;
                codes.push(Bytecode::Createasyncgeneratorobj(func_r));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::SetGeneratorState { genobj, state } => {
                ensure_acc(tracker, func_id, *genobj, alloc, codes)?;
                codes.push(Bytecode::Setgeneratorstate(Imm(i64::from(*state))));
            }
            Op::SuspendGenerator { genobj, value } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*genobj], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Suspendgenerator(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::ResumeGenerator { genobj } => {
                ensure_acc(tracker, func_id, *genobj, alloc, codes)?;
                codes.push(Bytecode::Resumegenerator);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::GetResumeMode { genobj } => {
                ensure_acc(tracker, func_id, *genobj, alloc, codes)?;
                codes.push(Bytecode::Getresumemode);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::Await { .. } => {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "Await has no v0.1 lowering equivalent (es2abc's await form is \
                     asyncfunctionawaituncaught — Op::AwaitUncaught)"
                        .into(),
                });
            }
            Op::AwaitUncaught { funcobj, value } => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*funcobj],
                    Some(*value),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Asyncfunctionawaituncaught(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AsyncFunctionEnter => {
                codes.push(Bytecode::Asyncfunctionenter);
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AsyncResolve { funcobj, value } => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*funcobj],
                    Some(*value),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Asyncfunctionresolve(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AsyncReject { funcobj, value } => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*funcobj],
                    Some(*value),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Asyncfunctionreject(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AsyncGeneratorResolve {
                genobj,
                value,
                done,
            } => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[*genobj, *value, *done],
                    None,
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Asyncgeneratorresolve(regs[0], regs[1], regs[2]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::AsyncGeneratorReject { genobj, value } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*genobj], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Asyncgeneratorreject(regs[0]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }
            Op::NotifyConcurrentResult { value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::CallruntimeNotifyconcurrentresult);
                *tracker = AccContent::Unknown;
            }
            Op::CreateIterResultObj { value, done } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*value, *done], None, alloc, codes)?;
                codes.push(Bytecode::Createiterresultobj(regs[0], regs[1]));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            }

            // ── Exception handling ───────────────────────────────────────
            Op::Throw { value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::Throw);
            }
            Op::ThrowIfNotObject { value } => {
                let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
                codes.push(Bytecode::ThrowIfnotobject(val_r));
            }
            Op::ThrowConstAssignment { name } => {
                let name_r = val_reg(func_id, *name, alloc, codes, 0)?;
                codes.push(Bytecode::ThrowConstassignment(name_r));
            }
            Op::ThrowUndefinedIfHole { name, value } => {
                let regs =
                    materialize_operands(tracker, func_id, &[*name, *value], None, alloc, codes)?;
                codes.push(Bytecode::ThrowUndefinedifhole(regs[0], regs[1]));
            }
            Op::ThrowUndefinedIfHoleWithName { name, value } => {
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::ThrowUndefinedifholewithname(
                    self.tracer.eid(*name),
                ));
            }
            Op::ThrowIfSuperNotCalled { value, kind } => {
                let k = match kind {
                    SuperCheck::NotCalled => 0,
                    SuperCheck::Rebind => 1,
                };
                ensure_acc(tracker, func_id, *value, alloc, codes)?;
                codes.push(Bytecode::ThrowIfsupernotcorrectcall(Imm(k)));
            }
            Op::ThrowNotExists => {
                codes.push(Bytecode::ThrowNotexists);
            }
            Op::ThrowPatternNonCoercible => {
                codes.push(Bytecode::ThrowPatternnoncoercible);
            }
            Op::ThrowDeleteSuperProperty => {
                codes.push(Bytecode::ThrowDeletesuperproperty);
            }

            // ── Terminators (`R3-X1`, `R3-A7`) ───────────────────────────
            Op::Branch { dest } => {
                codes.push(Bytecode::Jmp(Label(dest.0)));
            }
            Op::CondBranch {
                cond,
                true_dest,
                false_dest,
            } => {
                let _ = false_dest;
                // Case 1 & 2: Fused single-use `UnOp::JumpNez` / `UnOp::JumpEqz`
                // emits raw `jnez` / `jeqz` directly on the underlying operand
                // (do NOT mark `bool_cond_blocks`, since `jeqz` and `jnez` are not
                // complements on `null`/`undefined`/strings/objects).
                if suppression.values.contains(cond)
                    && let Some(ValueDef::Inst(piid)) = module.value(*cond).map(|v| v.def)
                    && let Some(Op::UnaryOp {
                        op: raw_op @ (UnOp::JumpEqz | UnOp::JumpNez),
                        operand,
                    }) = module.inst(piid).map(|i| &i.op)
                {
                    ensure_acc(tracker, func_id, *operand, alloc, codes)?;
                    codes.push(match raw_op {
                        UnOp::JumpEqz => Bytecode::Jeqz(Label(true_dest.0)),
                        _ => Bytecode::Jnez(Label(true_dest.0)),
                    });
                } else {
                    // Case 3 & 4: Proven boolean emits `jnez` directly; non-boolean
                    // first coerces via `Bytecode::Istrue` so strings/objects/`NaN`
                    // obey ECMA-262 `ToBoolean` (`R3-X1`).
                    ensure_acc(tracker, func_id, *cond, alloc, codes)?;
                    if !is_proven_boolean(module, *cond) {
                        codes.push(Bytecode::Istrue);
                        *tracker = AccContent::Unknown;
                    }
                    self.bool_cond_blocks.insert(bb);
                    codes.push(Bytecode::Jnez(Label(true_dest.0)));
                }
            }
            Op::Return { value } => {
                if let Some(val) = value {
                    ensure_acc(tracker, func_id, *val, alloc, codes)?;
                    codes.push(Bytecode::Return);
                } else {
                    codes.push(Bytecode::Returnundefined);
                }
            }
            Op::Unreachable => {
                codes.push(Bytecode::Returnundefined);
            }

            // ── Phi / Debug ──────────────────────────────────────────────
            Op::Phi { .. } => {}
            Op::Debugger => {
                codes.push(Bytecode::Debugger);
            }
        }
        Ok(())
    }

    fn select_call(
        &mut self,
        kind: CallKind,
        callee: ValueId,
        this: Option<ValueId>,
        args: &[ValueId],
        codes: &mut Vec<Bytecode>,
        tracker: &mut AccContent,
    ) -> Result<(), LowerError> {
        let func_id = self.func_id;
        let alloc = self.alloc;
        match kind {
            CallKind::Dynamic | CallKind::Direct => match this {
                None => match args.len() {
                    0 => {
                        materialize_operands(tracker, func_id, &[], Some(callee), alloc, codes)?;
                        codes.push(Bytecode::Callarg0(self.ic.two()));
                    }
                    n @ (1..=3) => {
                        let regs = materialize_operands(
                            tracker,
                            func_id,
                            args,
                            Some(callee),
                            alloc,
                            codes,
                        )?;
                        let bc = match n {
                            1 => Bytecode::Callarg1(self.ic.two(), regs[0]),
                            2 => Bytecode::Callargs2(self.ic.two(), regs[0], regs[1]),
                            _ => Bytecode::Callargs3(self.ic.two(), regs[0], regs[1], regs[2]),
                        };
                        codes.push(bc);
                    }
                    _ => self.emit_range_call(RangeForm::Call, callee, args, codes, tracker)?,
                },
                Some(this_val) => {
                    let mut values = Vec::with_capacity(args.len() + 1);
                    values.push(this_val);
                    values.extend_from_slice(args);
                    match values.len() {
                        n @ (1..=4) => {
                            let regs = materialize_operands(
                                tracker,
                                func_id,
                                &values,
                                Some(callee),
                                alloc,
                                codes,
                            )?;
                            let bc = match n {
                                1 => Bytecode::Callthis0(self.ic.two(), regs[0]),
                                2 => Bytecode::Callthis1(self.ic.two(), regs[0], regs[1]),
                                3 => Bytecode::Callthis2(self.ic.two(), regs[0], regs[1], regs[2]),
                                _ => Bytecode::Callthis3(
                                    self.ic.two(),
                                    regs[0],
                                    regs[1],
                                    regs[2],
                                    regs[3],
                                ),
                            };
                            codes.push(bc);
                        }
                        _ => self.emit_range_call(
                            RangeForm::CallThis,
                            callee,
                            &values,
                            codes,
                            tracker,
                        )?,
                    }
                }
            },
            CallKind::Super => {
                self.emit_range_call(RangeForm::SuperCallThis, callee, args, codes, tracker)?;
            }
            CallKind::SuperArrow => {
                if this.is_some() {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "supercallarrowrange requires this=None".into(),
                    });
                }
                self.emit_range_call(RangeForm::SuperCallArrow, callee, args, codes, tracker)?;
            }
            CallKind::Apply => {
                let (Some(this_val), [array]) = (this, args) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!(
                            "apply requires exactly (this, args array), got this={} args={}",
                            this.is_some(),
                            args.len()
                        ),
                    });
                };
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[this_val, *array],
                    Some(callee),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::Apply(self.ic.two(), regs[0], regs[1]));
            }
            CallKind::SuperSpread => {
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &args[..1.min(args.len())],
                    Some(callee),
                    alloc,
                    codes,
                )?;
                let arg_r = if args.is_empty() { Reg(0) } else { regs[0] };
                codes.push(Bytecode::Supercallspread(self.ic.two(), arg_r));
            }
            CallKind::SuperForwardAllArgs => {
                let [this_func] = args else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!(
                            "supercallforwardallargs requires exactly the lifted register operand \
                             (thisFunc), got {} args",
                            args.len()
                        ),
                    });
                };
                let regs =
                    materialize_operands(tracker, func_id, &[*this_func], None, alloc, codes)?;
                codes.push(Bytecode::CallruntimeSupercallforwardallargs(regs[0]));
            }
            CallKind::New => {
                emit_construct(callee, args, func_id, alloc, codes, self.ic)?;
            }
            CallKind::NewSpread => {
                // #55: `newobjapply imm:u16, v:in:top; acc: inout:top` — `v` is the
                // constructor (`callee`) and `acc` carries the spread array (`args[0]`).
                let (None, [array]) = (this, args) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!(
                            "newobjapply requires this=None and 1 spread array, got this={} args={}",
                            this.is_some(),
                            args.len()
                        ),
                    });
                };
                let regs =
                    materialize_operands(tracker, func_id, &[callee], Some(*array), alloc, codes)?;
                codes.push(Bytecode::Newobjapply(self.ic.two(), regs[0]));
            }
            CallKind::ClassInit => {
                // #55: `callruntime.callinit imm:u8, v:in:top; acc: in:top` — `acc`
                // holds `callee` and `v` holds `this` (`args` is empty).
                let (Some(this_val), []) = (this, args) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!(
                            "callruntime.callinit requires this=Some and 0 args, got this={} args={}",
                            this.is_some(),
                            args.len()
                        ),
                    });
                };
                let regs = materialize_operands(
                    tracker,
                    func_id,
                    &[this_val],
                    Some(callee),
                    alloc,
                    codes,
                )?;
                codes.push(Bytecode::CallruntimeCallinit(self.ic.two(), regs[0]));
            }
        }
        Ok(())
    }

    fn emit_range_call(
        &mut self,
        form: RangeForm,
        callee: ValueId,
        args: &[ValueId],
        codes: &mut Vec<Bytecode>,
        tracker: &mut AccContent,
    ) -> Result<(), LowerError> {
        let start = fill_call_window(self.func_id, args, self.alloc, codes)?;
        ensure_acc(tracker, self.func_id, callee, self.alloc, codes)?;

        let window = args.len();
        let argc = match form {
            RangeForm::CallThis => window.saturating_sub(1),
            RangeForm::Call | RangeForm::SuperCallThis | RangeForm::SuperCallArrow => window,
        };
        let argc_imm = Imm(argc as i64);
        let bc = match (form, argc <= 255) {
            (RangeForm::Call, true) => Bytecode::Callrange(self.ic.two(), argc_imm, start),
            (RangeForm::Call, false) => Bytecode::WideCallrange(argc_imm, start),
            (RangeForm::CallThis, true) => Bytecode::Callthisrange(self.ic.two(), argc_imm, start),
            (RangeForm::CallThis, false) => Bytecode::WideCallthisrange(argc_imm, start),
            (RangeForm::SuperCallThis, true) => {
                Bytecode::Supercallthisrange(self.ic.two(), argc_imm, start)
            }
            (RangeForm::SuperCallThis, false) => Bytecode::WideSupercallthisrange(argc_imm, start),
            (RangeForm::SuperCallArrow, true) => {
                Bytecode::Supercallarrowrange(self.ic.two(), argc_imm, start)
            }
            (RangeForm::SuperCallArrow, false) => {
                Bytecode::WideSupercallarrowrange(argc_imm, start)
            }
        };
        codes.push(bc);
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum RangeForm {
    Call,
    CallThis,
    SuperCallThis,
    SuperCallArrow,
}

/// Emit a construct call (`new callee(args...)`) — vendor
/// `newobjrange imm1:u16, imm2:u8, v:in:top` /
/// `wide.newobjrange imm:u16, v:in:top`
/// (`vendor/arkcompiler_runtime_core/static_core/isa/isa.yaml` / dynamic ISA).
///
/// The reserved consecutive window is filled [callee, args...] IN ORDER:
/// the runtime reads the constructor from the FIRST register of the range
/// and passes it as BOTH func and newTarget
/// (`SlowRuntimeStub::NewObjRange(thread, ctor, ctor, ...)`,
/// arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:4205),
/// and the encoded argc counts it (argc = args.len() + 1). Unlike the
/// plain-call range forms the accumulator is NOT an input (vendor
/// `acc: out:top`), so no `ensure_acc` is emitted for the callee.
///
/// Width selection inherits the S2 rule: argc+1 ≤ 255 keeps the narrow
/// form (with its two-slot IC); 256..=65535 selects the wide form (u16
/// argc, NO IC slot consumed — verified for newobjrange specifically:
/// isa.yaml ~:540 has no ic_slot property); argc+1 above u16::MAX, a
/// window base above 255, or a window end past the register space are the
/// same hard errors as the plain range calls (shared `fill_call_window`).
fn emit_construct(
    callee: ValueId,
    args: &[ValueId],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) -> Result<(), LowerError> {
    let mut window_values = Vec::with_capacity(args.len() + 1);
    window_values.push(callee);
    window_values.extend_from_slice(args);
    let start = fill_call_window(func_id, &window_values, alloc, codes)?;

    let argc = window_values.len();
    let argc_imm = Imm(argc as i64);
    let bc = if argc <= 255 {
        Bytecode::Newobjrange(ic.two(), argc_imm, start)
    } else {
        Bytecode::WideNewobjrange(argc_imm, start)
    };
    codes.push(bc);
    Ok(())
}

/// Fill the reserved consecutive per-function call window
/// (`RegAlloc::call_window_base`) with `values` in order and return the
/// encoded start register. Shared by the plain range calls (values = the
/// arguments) and construct calls (values = [callee, args...]).
///
/// An empty `values` encodes start = Reg(0): argc = 0 reads no argument
/// registers, so the start operand is dead and no window is needed (or
/// reserved) for the site.
///
/// Hard errors (S2 contract — nothing is silently truncated): argc above
/// u16::MAX (`CallArgcOverflow`), a window base above 255
/// (`CallWindowOverflow` — BOTH the narrow and the wide forms carry a u8
/// start operand), and a window end past the register space
/// (`RegisterOverflow`).
///
/// The fill is pure `mov`s from the values' register homes (every value
/// has one — B4), so it never touches the accumulator and needs no
/// tracker update (vendor `mov` is `acc: none`).
fn fill_call_window(
    func_id: FuncId,
    values: &[ValueId],
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Reg, LowerError> {
    let argc = values.len();
    if argc > u16::MAX as usize {
        return Err(LowerError::CallArgcOverflow {
            func: func_id,
            argc,
        });
    }
    if argc == 0 {
        return Ok(Reg(0));
    }

    let base = alloc
        .call_window_base
        .ok_or(LowerError::MissingCallWindow(func_id))?;
    if base > 255 {
        return Err(LowerError::CallWindowOverflow(func_id));
    }
    if base as u32 + argc as u32 - 1 > u16::MAX as u32 {
        return Err(LowerError::RegisterOverflow(func_id));
    }
    // Fill the window in order. `mov` auto-widens to its v16 form,
    // so both the window slot (which may exceed 255) and the value's
    // colored home are always encodable.
    for (j, &val) in values.iter().enumerate() {
        let dst = Reg(base + j as u16);
        let r = home_of(func_id, val, alloc)?;
        codes.push(Bytecode::Mov(dst, Reg(r)));
    }
    Ok(Reg(base))
}

/// Fill the reserved consecutive window for non-empty `CreateObjectWithExcludedKeys`
/// (`1..=65536` keys, where `imm = keys.len() - 1` fits `u16`).
fn fill_excluded_keys_window(
    func_id: FuncId,
    keys: &[ValueId],
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Reg, LowerError> {
    let base = alloc
        .call_window_base
        .ok_or(LowerError::MissingCallWindow(func_id))?;
    if base > 255 {
        return Err(LowerError::CallWindowOverflow(func_id));
    }
    if u32::from(base) + keys.len() as u32 - 1 > u32::from(u16::MAX) {
        return Err(LowerError::RegisterOverflow(func_id));
    }
    for (j, &val) in keys.iter().enumerate() {
        let dst = Reg(base + j as u16);
        let r = home_of(func_id, val, alloc)?;
        codes.push(Bytecode::Mov(dst, Reg(r)));
    }
    Ok(Reg(base))
}

#[cfg(test)]
mod tests {
    use super::{
        AccContent, LowerError, RegAlloc, RegSlot, ensure_acc, home_result, materialize_operands,
        val_reg,
    };
    use abcd_ir::{FuncId, ValueId};
    use abcd_isa::{Bytecode, Reg};
    use std::collections::{HashMap, HashSet};

    const F: FuncId = FuncId(0);

    fn alloc_with(slots: &[(ValueId, u16)]) -> RegAlloc {
        RegAlloc {
            allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
            phi_copies: HashMap::new(),
            handler_phi_stores: Vec::new(),
            num_regs: 8,
            copy_temp: None,
            call_window_base: None,
            low_scratch_base: None,
        }
    }

    fn used_set(values: &[ValueId]) -> HashSet<ValueId> {
        values.iter().copied().collect()
    }

    #[test]
    fn reg_colored_operand_passes_through_without_emission() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 2)]);
        let mut codes = Vec::new();
        let r = val_reg(F, v, &alloc, &mut codes, 0).expect("reg operand must resolve");
        assert_eq!(r, Reg(2));
        assert!(codes.is_empty(), "no lda/sta expected, got {codes:?}");
    }

    #[test]
    fn unallocated_operand_is_a_hard_error_not_silent_acc() {
        let alloc = alloc_with(&[]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        let dangling = ValueId::new(42);
        assert!(matches!(
            val_reg(F, dangling, &alloc, &mut codes, 0),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
        assert!(matches!(
            ensure_acc(&mut tracker, F, dangling, &alloc, &mut codes),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
    }

    #[test]
    fn ensure_acc_loads_the_home_on_a_miss_and_records_the_content() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 3)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("load must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(3))]),
            "a tracker miss must emit Lda(home), got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(v));
    }

    #[test]
    fn ensure_acc_hit_emits_no_load() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 3)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Holds(v);
        ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("hit must succeed");
        assert!(codes.is_empty(), "a cache hit must not emit, got {codes:?}");
        // A DIFFERENT value is a miss even when the tracker holds something.
        let w = ValueId::new(2);
        let alloc = alloc_with(&[(v, 3), (w, 4)]);
        ensure_acc(&mut tracker, F, w, &alloc, &mut codes).expect("miss must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(4))]),
            "a different value must reload from its own home, got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(w));
    }

    #[test]
    fn used_results_are_homed_and_tracked_dead_results_are_not() {
        let live = ValueId::new(1);
        let dead = ValueId::new(2);
        let alloc = alloc_with(&[(live, 5), (dead, 6)]);
        let used = used_set(&[live]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;

        home_result(&mut tracker, Some(live), &used, F, &alloc, &mut codes)
            .expect("homing must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Sta(Reg(5))]),
            "a used result must be homed with Sta, got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(live));

        codes.clear();
        home_result(&mut tracker, Some(dead), &used, F, &alloc, &mut codes)
            .expect("dead result must not error");
        assert!(codes.is_empty(), "a dead result gets no Sta, got {codes:?}");
        assert_eq!(
            tracker,
            AccContent::Unknown,
            "a dead result's acc content is untracked"
        );
    }

    #[test]
    fn register_operands_read_homes_and_the_acc_operand_loads_last() {
        // obj in R7, key in R0: val_reg emits nothing (low homes), then
        // ensure_acc(key) emits the Lda. No spill slot, no Sta — the old
        // B3 spill-before-load dance is gone by construction.
        let obj = ValueId::new(1);
        let key = ValueId::new(2);
        let alloc = alloc_with(&[(obj, 7), (key, 0)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        let regs = materialize_operands(&mut tracker, F, &[obj], Some(key), &alloc, &mut codes)
            .expect("materialization must succeed");
        assert_eq!(regs, vec![Reg(7)]);
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(0))]),
            "expected exactly the key's Lda(home), got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(key));
    }
}
