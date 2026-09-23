//! Function graph: SSA bodies, blocks, edges, try regions, debug info
//! (design/ir-v0.2.md §3, §5.1–§5.2).

use crate::id::{BlockId, ClassId, ConstId, InstId, Sym, ValueId};
use crate::module::{Annotation, FunctionKind, Modifiers, Signature};
use crate::op::Op;
use crate::ty::Ty;

/// A source location: line/column only. Instruction *offsets* are a
/// code-layout detail and are banned from the IR (design/ir.md §2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Loc {
    /// 1-based source line.
    pub line: u32,
    /// 1-based source column, when the source carried one.
    pub column: Option<u32>,
}

/// How an SSA value is defined.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValueDef {
    /// A function parameter, by index into
    /// [`FunctionData::params`]. Parameters are entry-defined: they
    /// dominate every block of the function.
    Param(u16),
    /// The result of an instruction (including phis).
    Inst(InstId),
    /// A constant from the module pool; materializable anywhere, so it
    /// dominates everything.
    Const(ConstId),
    /// The exception object delivered by exception dispatch at a catch
    /// handler's entry (T5). Not an instruction: the exceptional edge
    /// itself is the definition point. Valid in the owning handler block
    /// and its exceptional-reachable downstream (see
    /// [`crate::verify`]).
    ExceptionParam(BlockId),
}

/// An SSA value: its definition and its (analysis) type.
#[derive(Clone, Debug)]
pub struct Value {
    /// The definition point.
    pub def: ValueDef,
    /// The value's type (dynamic-first lattice; statics are annotations).
    pub ty: Ty,
}

/// One instruction: a semantic op, its SSA result, its home block, and
/// its source location.
#[derive(Clone, Debug)]
pub struct Inst {
    /// The operation.
    pub op: Op,
    /// The SSA value this instruction defines, iff
    /// [`Op::has_result`]. Passes must keep the two in agreement.
    pub result: Option<ValueId>,
    /// The owning block.
    pub block: BlockId,
    /// Source location (T8): present whenever the source had line info.
    /// Passes propagate or drop it — never fabricate it (§7 hard
    /// contract).
    pub loc: Option<Loc>,
}

/// A CFG edge kind (T5): exception flow is a first-class edge, so IFDS
/// path edges and CFG analyses see it without consulting `TryRegion`s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    /// Ordinary control flow (terminator successor).
    Normal,
    /// Exception dispatch from a protected block to a catch handler.
    Exceptional,
}

/// A CFG edge into a block (stored on the successor side, in
/// [`Block::preds`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Edge {
    /// The source block.
    pub from: BlockId,
    /// The edge kind.
    pub kind: EdgeKind,
}

/// A basic block: phi nodes first, then instructions, ending in exactly
/// one terminator (verifier-checked). Successors are derived from the
/// terminator plus the function's [`TryRegion`]s.
#[derive(Clone, Debug, Default)]
pub struct Block {
    /// Instructions; leading [`Op::Phi`]s form the phi prefix.
    pub insts: Vec<InstId>,
    /// Incoming edges (both kinds).
    pub preds: Vec<Edge>,
}

/// A catch entry of a [`TryRegion`].
#[derive(Clone, Debug)]
pub struct Catch {
    /// The handler's entry block.
    pub handler: BlockId,
    /// The exception object value delivered at the handler entry. Its
    /// [`Value::def`] must be [`ValueDef::ExceptionParam`] of `handler`.
    pub exception: ValueId,
    /// The exception type index of a TYPED catch, when the source
    /// carried one (`None` = catch-all).
    pub type_idx: Option<u32>,
}

/// A structured try region (§5.2): both structure (for lowering) and the
/// source of [`EdgeKind::Exceptional`] edges — every protected block has
/// an exceptional edge to every catch handler of the region.
#[derive(Clone, Debug)]
pub struct TryRegion {
    /// Blocks whose executing instructions are protected.
    pub protected: Vec<BlockId>,
    /// Catch handlers, in dispatch order.
    pub catches: Vec<Catch>,
}

/// Per-function debug information (§7: program semantics — local names
/// feed taint readability; line tables replay at lower per the #16 rule).
/// Tables key on [`InstId`], never on instruction offsets.
#[derive(Clone, Debug, Default)]
pub struct DebugData {
    /// Source file name, when known.
    pub source_file: Option<Sym>,
    /// Source code text, when the file carried it (content, not a name —
    /// deliberately not interned into the [`crate::symbol::SymbolTable`]).
    pub source_code: Option<String>,
    /// Instruction → source line table.
    pub line_table: Vec<LineEntry>,
    /// Instruction → source column table.
    pub column_table: Vec<ColumnEntry>,
    /// Local variable names (from the source's debug info).
    pub local_names: Vec<LocalName>,
    /// Parameter names, in parameter order (may be shorter than
    /// [`FunctionData::params`]).
    pub param_names: Vec<Sym>,
    /// The lexical scope-names constant of the function's home record
    /// (the `_ESScopeNamesRecord` field blob), when present.
    pub scope_names: Option<ConstId>,
}

/// One line-table entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineEntry {
    /// The instruction.
    pub inst: InstId,
    /// 1-based source line.
    pub line: u32,
}

/// One column-table entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ColumnEntry {
    /// The instruction.
    pub inst: InstId,
    /// 1-based source column.
    pub column: u32,
}

/// A named local variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalName {
    /// The local's source name.
    pub name: Sym,
    /// Its declared type, when the source carried one.
    pub ty: Option<Ty>,
    /// The source-level scope of the name (the debug info's `start`/`end`
    /// extents, mapped onto lifted instructions): `start` is the first
    /// lifted instruction whose source position is at-or-after the
    /// scope's start, `end` the last lifted instruction whose source
    /// position is at-or-before the scope's end. `None` when the source
    /// range covers no lifted instruction (e.g. the range only contained
    /// register moves, which have no IR presence).
    pub scope: Option<LocalScope>,
}

/// A local variable's scope extent over lifted instructions (inclusive
/// on both ends).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalScope {
    /// First in-scope instruction.
    pub start: InstId,
    /// Last in-scope instruction.
    pub end: InstId,
}

/// IR representation of one function/method.
#[derive(Clone, Debug)]
pub struct FunctionData {
    /// The class this function belongs to (the module top-level is itself
    /// a class record, so every function has one).
    pub class_id: ClassId,
    /// Function name (display/lookup only — identity is the
    /// [`FuncId`](crate::id::FuncId)).
    pub name: Sym,
    /// Declared signature, when the source carried one (format fact #A7:
    /// absent on 12+/24). The IR reflects reality, so this is an `Option`.
    pub sig: Option<Signature>,
    /// Semantic function kind.
    pub kind: FunctionKind,
    /// Modifiers.
    pub modifiers: Modifiers,
    /// External/native attachment point (T6): the IR carries no native
    /// bodies; taint summaries register against `(name, arity)` keys
    /// outside the IR.
    pub is_external: bool,
    /// SSA values for the parameters, in code-header argument order.
    /// **Frame-slot model (T4/§5.3, canonical — [`crate::frame`]):** the
    /// leading slots are the vendored implicit frame slots
    /// `[func][new.target][this]` (per the callee's
    /// `L_ESCallTypeAnnotation;` callType bits; absent → the `0xF`
    /// default, the es2abc shape), then the source formals. The
    /// this-role slot is [`crate::frame::this_param_index`] — NOT
    /// `params[0]` (the FUNC slot under the `0xF` default; the earlier
    /// "`params[0]` = `this`" convention is superseded, N66/N67).
    pub params: Vec<ValueId>,
    /// Blocks owned by this function; `blocks[0]` is the entry block.
    pub blocks: Vec<BlockId>,
    /// Structured try regions (§5.2); also the source of exceptional CFG
    /// edges.
    pub try_regions: Vec<TryRegion>,
    /// Debug information.
    pub debug: Option<DebugData>,
    /// Annotations (single folded list).
    pub annotations: Vec<Annotation>,
}

impl FunctionData {
    /// A minimal function record with no blocks. `class_id`/`name` are
    /// the required identities; everything else starts empty.
    pub fn new(class_id: ClassId, name: Sym, kind: FunctionKind) -> Self {
        Self {
            class_id,
            name,
            sig: None,
            kind,
            modifiers: Modifiers::NONE,
            is_external: false,
            params: Vec::new(),
            blocks: Vec::new(),
            try_regions: Vec::new(),
            debug: None,
            annotations: Vec::new(),
        }
    }

    /// The entry block (`blocks[0]`); `None` when the function has no
    /// blocks (e.g. an external function).
    pub fn entry(&self) -> Option<BlockId> {
        self.blocks.first().copied()
    }
}
