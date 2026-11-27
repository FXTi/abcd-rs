//! # abcd-lower — lower converter: `abcd_ir::Module` → `abcd_file::File` / `MethodBody`
//!
//! Format-aware lowering layer (`design/ir.md` §5, `design/decisions.md`)
//! that compiles the SSA IR ([`abcd_ir::Module`]) back to `.abc` bytecode and
//! container structures: Hack–Grund–Goos dominance-tree SSA register
//! allocation with Boissinot CSSA isolation and biased coalescing, slot-level
//! parallel-copy cycle breaking, accumulator-as-cache instruction selection,
//! basic-block layout with edge trampolines, try-range reconstruction, entity
//! relocation and per-method `u16` compaction, in-place file rewriting
//! ([`rewrite_file`]), and standalone whole-module lowering ([`lower_module`]).

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod copy_resolve;
pub mod fusion;
pub mod isel;
pub mod layout;
pub mod method_body;
pub mod module_lower;
pub mod regalloc;

use abcd_ir::{BlockId, FuncId, Module, ValueId};

pub use layout::{LayoutResult, LoweredCatchBlock, LoweredTryBlock};
pub use method_body::{EntityResolver, lower_module_bodies, to_method_body};
pub use module_lower::{
    lower_module, lower_module_with_options, rebuild_method_debug, rewrite_file,
};
pub use regalloc::RegAlloc;

/// Lowering options.
///
/// Frame-initial constant ownership now lives directly on
/// [`abcd_ir::FunctionData::frame_init_consts`] and is swept by ADCE (#30),
/// so unoptimized and optimized modules lower through the same uniform
/// configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LowerOptions {}

/// Errors that can occur during lowering.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    /// The function has no blocks (e.g. an external/native function).
    #[error("function {0:?} has no blocks")]
    EmptyFunction(FuncId),
    /// Register allocation overflow.
    #[error("register allocation overflow in function {0:?}")]
    RegisterOverflow(FuncId),
    /// An instruction has no faithful bytecode encoding.
    #[error("unsupported instruction in function {func:?}: {message}")]
    UnsupportedInstruction {
        /// The owning function.
        func: FuncId,
        /// What cannot be encoded.
        message: String,
    },
    /// A slot-level phi copy cycle exists but no copy temp was reserved.
    #[error(
        "function {0:?} has a slot-level phi copy cycle but no reserved copy temporary register"
    )]
    MissingCopyTemp(FuncId),
    /// An operand was never colored by register allocation.
    #[error("function {func:?} uses value {value:?} that register allocation never colored")]
    UnallocatedOperand {
        /// The owning function.
        func: FuncId,
        /// The uncolored value.
        value: ValueId,
    },
    /// An entity operand cannot be traced back to a source-file offset.
    #[error(
        "function {func:?} has a {kind:?} entity operand with raw value {raw:#x} that cannot \
         be traced to a source-file entity (string content, method function-table index, or \
         literal-array content)"
    )]
    UntraceableEntity {
        /// The owning function.
        func: FuncId,
        /// The entity kind.
        kind: abcd_isa::EntityKind,
        /// The raw operand value.
        raw: u32,
    },
    /// A high (>= 256) register routes through the accumulator but no low
    /// scratch block was reserved.
    #[error(
        "function {0:?} routes a high (>= 256) register through the accumulator but register \
         allocation reserved no low (<= 255) scratch block; sta/lda are op_v_8-only"
    )]
    MissingLowScratch(FuncId),
    /// An instruction has more register operands than the low scratch block.
    #[error(
        "function {0:?} has an instruction with more register operands than the reserved low \
         scratch block holds"
    )]
    LowScratchExhausted(FuncId),
    /// A range-form call exists but no argument window was reserved.
    #[error(
        "function {0:?} contains a range-form call but register allocation reserved no \
         consecutive argument window"
    )]
    MissingCallWindow(FuncId),
    /// The range-call window would start above register 255.
    #[error(
        "range-call argument window in function {0:?} would start above register 255; the \
         vendored start-register operand is u8 in every callrange form (narrow and wide)"
    )]
    CallWindowOverflow(FuncId),
    /// A range-form call exceeds the u16 argc encoding limit.
    #[error(
        "range-form call in function {func:?} has {argc} arguments, exceeding the u16 argc \
         encoding limit of the wide callrange forms"
    )]
    CallArgcOverflow {
        /// The owning function.
        func: FuncId,
        /// The argument count.
        argc: usize,
    },
    /// A catch-handler phi has a same-slot result/incoming pair that
    /// interferes.
    #[error(
        "function {0:?}: a catch-handler phi has a same-slot result/incoming pair that \
         interferes (inconsistent input — coloring never assigns one slot to an \
         interfering pair)"
    )]
    HandlerPhiConflict(FuncId),
    /// A catch-handler phi result or incoming value was never colored.
    #[error(
        "function {0:?}: a catch-handler phi result has no register home or an incoming \
         value was never colored"
    )]
    HandlerPhiUncoalesced(FuncId),
    /// Phi copies remain on an exception edge — no code may run there.
    #[error(
        "function {func:?}: phi copies remain on exception edge {pred:?} -> {handler:?}; \
         no code may run on an exception edge — the VM dispatches directly to the handler's \
         flat offset (N21)"
    )]
    HandlerEdgeCopies {
        /// The owning function.
        func: FuncId,
        /// The protected predecessor.
        pred: BlockId,
        /// The handler block.
        handler: BlockId,
    },
    /// Phi copies keyed to an edge that is neither a terminator successor
    /// nor a catch-handler edge.
    #[error(
        "function {func:?}: phi copies keyed to {pred:?} -> {succ:?}, which is neither a \
         terminator successor nor a catch-handler edge — inconsistent input"
    )]
    InconsistentEdgeCopies {
        /// The owning function.
        func: FuncId,
        /// The predecessor.
        pred: BlockId,
        /// The successor.
        succ: BlockId,
    },
    /// isel's IC-immediate operand map disagrees with the vendor property
    /// tables (internal invariant: the map must cover exactly the
    /// `ic_slot`/`jit_ic_slot` instructions isel emits — a gap would leave
    /// a stale slot immediate after the N71 rearrangement).
    #[error(
        "function {func:?}: internal IC-operand map gap for {mnemonic} (vendor ic_slot flag: \
         {vendor_ic})"
    )]
    IcOperandMapGap {
        /// The owning function.
        func: FuncId,
        /// The instruction whose coverage disagrees.
        mnemonic: String,
        /// Whether the vendor tables mark the instruction IC-carrying.
        vendor_ic: bool,
    },
    /// A block emitted zero bytecodes (N49).
    #[error(
        "function {func:?}: block {block:?} emitted zero bytecodes — inconsistent input (a \
         block with no terminator). Its flat offset would alias the next block's, and the \
         next-greater-offset extent in try/handler range reconstruction would swallow the \
         following block into this one's range (N49)"
    )]
    ZeroExtentBlock {
        /// The owning function.
        func: FuncId,
        /// The offending block.
        block: BlockId,
    },
    /// Synthetic entity offset space (`u32`) overflowed while materializing
    /// new container items.
    #[error("synthetic entity offset overflowed u32 address space")]
    SyntheticOffsetOverflow,
    /// A single method references more than `u16::MAX + 1` distinct entities
    /// of one [`abcd_isa::EntityKind`], exceeding the 16-bit bytecode `id:u16`
    /// operand encoding limit.
    #[error(
        "function {0:?} references more than 65536 distinct entities of one kind, exceeding \
         the u16 entity operand limit"
    )]
    EntityIndexOverflow(FuncId),
    /// A jump bytecode carries a [`abcd_isa::Label`] that resolves to neither a
    /// laid-out basic block nor an internal instruction label (`#57` `R3-M3`).
    #[error(
        "function {func:?}: branch target label {target} does not resolve to any laid-out block"
    )]
    UnresolvedLabel {
        /// The owning function.
        func: FuncId,
        /// The unresolved raw label payload.
        target: u32,
    },
    /// Internal entity-operand visitor count disagreed with
    /// `abcd_isa::Bytecode::entity_operands` (`#58` `R3-M9`).
    #[error(
        "function {func:?}: entity operand visitor mismatch for {mnemonic} \
         (expected {expected}, visited {visited})"
    )]
    EntityOperandMismatch {
        /// The owning function.
        func: FuncId,
        /// Bytecode mnemonic.
        mnemonic: String,
        /// Operand count reported by `Bytecode::entity_operands`.
        expected: usize,
        /// Operand count visited by `for_each_entity_operand_mut`.
        visited: usize,
    },
    /// An instruction immediate exceeds its narrow bytecode operand width.
    #[error("function {func:?}: {op} immediate {field} = {value} exceeds {max}")]
    ImmediateOutOfRange {
        /// The owning function.
        func: FuncId,
        /// Instruction or opcode name.
        op: &'static str,
        /// Immediate field name.
        field: &'static str,
        /// Out-of-range immediate value.
        value: u64,
        /// Maximum encodable value.
        max: u64,
    },
}

/// Lower a single IR function back to bytecodes with default [`LowerOptions`].
pub fn lower_function(module: &Module, func_id: FuncId) -> Result<LayoutResult, LowerError> {
    lower_function_with_options(module, func_id, LowerOptions::default())
}

/// Lower a single IR function back to bytecodes with explicit options.
pub fn lower_function_with_options(
    module: &Module,
    func_id: FuncId,
    options: LowerOptions,
) -> Result<LayoutResult, LowerError> {
    let func = module
        .func(func_id)
        .ok_or(LowerError::EmptyFunction(func_id))?;
    if func.blocks.is_empty() {
        return Err(LowerError::EmptyFunction(func_id));
    }

    // Step 0: Fusion analysis (BEFORE register allocation): suppress
    // single-use IR expansion intermediates (DefineFunc/AllocClosure chains,
    // integral by-index constant loads, undefined TryGetGlobal defaults) so
    // suppressed values are invisible to register coloring and fold directly
    // into their consuming bytecode at instruction selection.
    let suppression = fusion::analyze(module, &func.blocks);

    // Step 1: Register allocation.
    let alloc = regalloc::allocate_with_options(module, func_id, &suppression, options).map_err(
        |e| match e {
            regalloc::RegAllocError::RegisterOverflow => LowerError::RegisterOverflow(func_id),
            regalloc::RegAllocError::WindowBaseOverflow => LowerError::CallWindowOverflow(func_id),
            regalloc::RegAllocError::HandlerPhiSlotConflict => {
                LowerError::HandlerPhiConflict(func_id)
            }
            regalloc::RegAllocError::HandlerPhiUncoalesced => {
                LowerError::HandlerPhiUncoalesced(func_id)
            }
        },
    )?;

    // Step 2: Compute RPO (reuse from regalloc).
    let rpo = regalloc::compute_rpo(module, func_id);

    // Step 3: Instruction selection.
    let isel_result =
        isel::select_with_options(module, func_id, &alloc, &rpo, &suppression, options)?;
    if let Some(message) = isel_result.unsupported.clone() {
        return Err(LowerError::UnsupportedInstruction {
            func: func_id,
            message,
        });
    }

    // Step 4: Layout and jump resolution.
    layout::layout(module, func_id, &isel_result, &alloc, &rpo)
}

#[cfg(test)]
mod tests {
    use super::lower_function;
    use abcd_ir::{
        Block, BlockId, ClassId, FuncId, FunctionData, FunctionKind, Inst, InstId, Module, Op, Ty,
        Value, ValueDef, ValueId,
    };

    /// N25: the name is the runtime VALUE in the register operand (vendor
    /// `throw.constassignment v:in:top, acc: none`, isa.yaml:987-991) —
    /// lowering succeeds and emits the name's register home, never a
    /// hardcoded Reg(0).
    #[test]
    fn const_assignment_lowers_with_the_name_register() {
        let mut module = Module::new();
        let descriptor = module.sym.intern("Ltest;");
        module
            .classes
            .push(abcd_ir::ClassData::new(descriptor, descriptor));
        let name_sym = module.sym.intern("f");
        let func = FuncId::new(0);
        module.functions.push(FunctionData::new(
            ClassId::new(0),
            name_sym,
            FunctionKind::Function,
        ));
        let entry = BlockId::new(0);
        module.blocks.push(Block::default());
        module.functions[0].blocks.push(entry);
        // One parameter (the name value).
        let param = ValueId::new(0);
        module.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        module.functions[0].params.push(param);
        let throw = InstId::new(0);
        module.insts.push(Inst {
            op: Op::ThrowConstAssignment { name: param },
            result: None,
            block: entry,
            loc: None,
        });
        let ret = InstId::new(1);
        module.insts.push(Inst {
            op: Op::Return { value: None },
            result: None,
            block: entry,
            loc: None,
        });
        module.blocks[0].insts.push(throw);
        module.blocks[0].insts.push(ret);

        let result = lower_function(&module, func).expect("throw.constassignment must lower");
        assert!(
            result
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, abcd_isa::Bytecode::ThrowConstassignment(_))),
            "the lowered stream must contain throw.constassignment: {:?}",
            result.bytecodes
        );
    }
}
