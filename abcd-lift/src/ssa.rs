//! Braun SSA construction: register/accumulator → SSA values (ported
//! from v0.1 `abcd-ir/src/lift/ssa.rs` — "Simple and Efficient
//! Construction of SSA Form", Braun et al. 2013).
//!
//! The v0.2 adaptations:
//!
//! - phi entries key on [`Edge`] (kind-qualified), not bare blocks —
//!   exception edges are first-class (T5);
//! - frame-initial values are CONSTANTS
//!   ([`ValueDef::Const`](abcd_ir2::ValueDef)) — no seeding
//!   instructions; the v0.1 entry-block `LiteralUndefined`/`LiteralHole`
//!   materialization stays a v0.1 detail (design/ir-v0.2.md §5.1). One
//!   shared `Const::Undefined` for vregs, one shared `Const::Hole` for
//!   the accumulator (vendor: `CALL_PUSH_UNDEFINED(numVregs)` +
//!   `state->acc = JSTaggedValue::Hole()` at frame creation —
//!   interpreter-inl.cpp:285-291/:731-732/:1471-1472, :739/:1482;
//!   interpreter_assembly.cpp:3653-3657, :3695).

use std::collections::HashMap;

use abcd_ir2::{BlockId, ConstId, InstId, Module, Op, Ty, Value, ValueDef, ValueId};

use crate::emit_inst;

/// Identifies a virtual location: either the accumulator or a register.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegOrAcc {
    /// The accumulator.
    Acc,
    /// A virtual register.
    Reg(u16),
}

/// Per-block SSA state: maps each virtual location to its current SSA
/// value.
type BlockDefs = HashMap<RegOrAcc, ValueId>;

/// SSA construction context using the Braun algorithm.
pub struct SsaBuilder {
    /// Per-block definition maps.
    defs: HashMap<BlockId, BlockDefs>,
    /// Tracks which blocks are "sealed" (all predecessors known).
    sealed: HashMap<BlockId, bool>,
    /// Incomplete phis: block → [(location, phi_value)] for unsealed
    /// blocks.
    incomplete_phis: HashMap<BlockId, Vec<(RegOrAcc, ValueId)>>,
    /// Lazily materialized frame-initial constants, one shared value per
    /// location kind (minimal liveness perturbation; vendor citations in
    /// the module docs). The underlying pool constants come from the
    /// lifter's deduplicated scalar pool, so frame-initial values share
    /// their `ConstId` with literal loads of the same constant.
    frame_initial_undefined: Option<ValueId>,
    frame_initial_hole: Option<ValueId>,
    undefined_const: ConstId,
    hole_const: ConstId,
}

impl SsaBuilder {
    /// A fresh builder; `undefined_const`/`hole_const` are the pooled
    /// frame-initial constants (deduplicated module-wide).
    pub fn new(undefined_const: ConstId, hole_const: ConstId) -> Self {
        Self {
            defs: HashMap::new(),
            sealed: HashMap::new(),
            incomplete_phis: HashMap::new(),
            frame_initial_undefined: None,
            frame_initial_hole: None,
            undefined_const,
            hole_const,
        }
    }

    /// Record a definition: `loc` is defined as `val` in `block`.
    pub fn write_variable(&mut self, loc: RegOrAcc, block: BlockId, val: ValueId) {
        self.defs.entry(block).or_default().insert(loc, val);
    }

    /// Read a variable in `block`. If not locally defined, recursively
    /// searches predecessors and inserts phi nodes as needed.
    pub fn read_variable(&mut self, loc: RegOrAcc, block: BlockId, module: &mut Module) -> ValueId {
        if let Some(val) = self.defs.get(&block).and_then(|m| m.get(&loc)).copied() {
            return val;
        }
        self.read_variable_recursive(loc, block, module)
    }

    fn read_variable_recursive(
        &mut self,
        loc: RegOrAcc,
        block: BlockId,
        module: &mut Module,
    ) -> ValueId {
        let preds = module.blocks[block.index()].preds.clone();
        // Predecessor edges are fully built before SSA construction
        // starts, so a block with no predecessors (the entry block, or
        // code unreachable from it) can never gain phi operands later.
        // A location read there has no reaching definition: resolve to
        // the Ark frame-initial value instead of an invalid zero-entry
        // phi.
        let val = if preds.is_empty() {
            self.frame_initial(loc, module)
        } else if !self.is_sealed(block) {
            // Block not sealed yet — create an incomplete phi.
            let phi_val = self.emit_empty_phi(block, module);
            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((loc, phi_val));
            phi_val
        } else if preds.len() == 1 {
            // Single predecessor — no phi needed, just recurse.
            self.read_variable(loc, preds[0].from, module)
        } else {
            // Multiple predecessors — insert a phi and fill it.
            let phi_val = self.emit_empty_phi(block, module);
            // Write before recursing to break cycles.
            self.write_variable(loc, block, phi_val);
            self.add_phi_operands(loc, block, phi_val, module)
        };
        self.write_variable(loc, block, val);
        val
    }

    /// The frame-initial value for a location with no reaching
    /// definition: one shared `Const::Undefined` for vregs, one shared
    /// `Const::Hole` for the accumulator. v0.2 represents these as
    /// `ValueDef::Const` — constants dominate everything and need no
    /// materializing instruction.
    fn frame_initial(&mut self, loc: RegOrAcc, module: &mut Module) -> ValueId {
        let cached = match loc {
            RegOrAcc::Acc => self.frame_initial_hole,
            RegOrAcc::Reg(_) => self.frame_initial_undefined,
        };
        if let Some(val) = cached {
            return val;
        }

        let const_id = match loc {
            RegOrAcc::Acc => self.hole_const,
            RegOrAcc::Reg(_) => self.undefined_const,
        };
        let val = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Const(const_id),
            ty: Ty::Any,
        });

        match loc {
            RegOrAcc::Acc => self.frame_initial_hole = Some(val),
            RegOrAcc::Reg(_) => self.frame_initial_undefined = Some(val),
        }
        val
    }

    /// Mark a block as sealed (all predecessors are known). Completes
    /// any incomplete phis.
    pub fn seal_block(&mut self, block: BlockId, module: &mut Module) {
        self.sealed.insert(block, true);
        if let Some(incomplete) = self.incomplete_phis.remove(&block) {
            for (loc, phi_val) in incomplete {
                self.add_phi_operands(loc, block, phi_val, module);
            }
        }
    }

    /// Whether the block is sealed.
    pub fn is_sealed(&self, block: BlockId) -> bool {
        self.sealed.get(&block).copied().unwrap_or(false)
    }

    /// Emit an empty phi node in `block` and return its result value.
    fn emit_empty_phi(&self, block: BlockId, module: &mut Module) -> ValueId {
        let (_inst_id, result) = emit_inst(
            module,
            block,
            Op::Phi {
                entries: Vec::new(),
            },
            None,
        );
        result.expect("phi has a result")
    }

    /// Fill phi operands by reading the variable from each predecessor
    /// edge.
    fn add_phi_operands(
        &mut self,
        loc: RegOrAcc,
        block: BlockId,
        phi_val: ValueId,
        module: &mut Module,
    ) -> ValueId {
        let preds = module.blocks[block.index()].preds.clone();
        let mut entries = Vec::with_capacity(preds.len());
        for edge in &preds {
            let val = self.read_variable(loc, edge.from, module);
            entries.push((*edge, val));
        }

        // Find the phi instruction for this value and update its
        // entries.
        let phi_inst = match module.values[phi_val.index()].def {
            ValueDef::Inst(inst) => inst,
            _ => unreachable!("phi_val must be an instruction result"),
        };
        module.insts[phi_inst.index()].op = Op::Phi { entries };

        self.try_remove_trivial_phi(phi_val, phi_inst, module)
    }

    /// If a phi is trivial (all operands are the same value or the phi
    /// itself), remove it and replace uses with the single value.
    fn try_remove_trivial_phi(
        &mut self,
        phi_val: ValueId,
        phi_inst: InstId,
        module: &mut Module,
    ) -> ValueId {
        let entries = match &module.insts[phi_inst.index()].op {
            Op::Phi { entries } => entries.clone(),
            _ => return phi_val,
        };

        let mut same: Option<ValueId> = None;
        for (_, val) in &entries {
            if *val == phi_val {
                continue; // self-reference
            }
            if let Some(s) = same {
                if *val == s {
                    continue; // same as existing
                }
                return phi_val; // non-trivial: at least two distinct values
            }
            same = Some(*val);
        }

        // If same is None, all operands are self-references (unreachable
        // in practice).
        let replacement = match same {
            Some(v) => v,
            None => return phi_val,
        };

        // Replace all uses of phi_val with replacement in the definition
        // maps.
        for block_defs in self.defs.values_mut() {
            for val in block_defs.values_mut() {
                if *val == phi_val {
                    *val = replacement;
                }
            }
        }

        // Keep the phi in the block during SSA construction. Earlier
        // instructions may already refer to its value; removing it here
        // without a function-wide use rewrite would create an undefined
        // SSA value. (CopyProp performs that rewrite before removing
        // dead phis — a pass-layer concern.)

        replacement
    }
}
