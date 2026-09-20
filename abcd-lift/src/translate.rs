//! Bytecode → v0.2 IR translation (the full v0.1 `translate.rs` arm
//! list, ported). v0.1's proven operand-role semantics are preserved
//! EXACTLY: every `read_reg`/`read_acc`/`write_reg`/`write_acc` happens
//! in v0.1's order per arm — reads drive Braun phi materialization, so
//! the SSA structure matches v0.1's one-for-one (the comparison
//! harness in `compare.rs` machine-checks this).
//!
//! # The opcode → op mapping table
//!
//! 1:1 mappings (canonical-equal in the harness): lda/sta/mov (SSA
//! aliases), all literals → `LoadConst` (Undefined/Null/Bool/Number/
//! String/BigInt/Hole/NaN/Infinity), arithmetic `*2` → `BinaryOp`,
//! comparisons (eq/noteq/less*/greater*/strict*/isin/instanceof) →
//! `Compare`, unary → `UnaryOp` (`not` is BITWISE, N39), istrue/isfalse
//! → `UnaryOp::{IsTrue,IsFalse}`, createemptyobject → `AllocObject`
//! (empty shape), createemptyarray → `AllocArray`,
//! createarray/objectwithbuffer → `AllocObject{shape}` (the literal
//! array as a pooled shape), createregexpwithliteral → `AllocRegExp`
//! (flags as u32 — v0.1's decimal-string flags canonicalize to it),
//! createobjectwithexcludedkeys → `CreateObjectWithExcludedKeys`,
//! ld/stobjbyname → `LoadProp`/`StoreProp`, ld/stobjbyvalue →
//! `LoadPropDyn`/`StorePropDyn`, ld/stobjbyindex → `LoadPropIdx`/
//! `StorePropIdx` (the constant index MATERIALIZED as a `LoadConst` —
//! §9 resolution 3), stownby*/definefieldbyname/definepropertybyname/
//! callruntime.definefieldby* → the `StoreProp*` family (the
//! own-vs-plain store distinction folds — documented), ld/stthisby* →
//! hard [`LiftError::UnsupportedThisByAccess`] (N51: es2panda never
//! emits the IC-fused this-by-* family — never silently invented),
//! ld/stsuperbyname →
//! `LoadSuper`/`StoreSuper` (Name), ld/stsuperbyvalue → (Dynamic),
//! delobjprop → `DeleteProp`, private-property family →
//! `LoadPrivate`/`StorePrivate`/`DefinePrivate`/`TestPrivate`/
//! `CreatePrivateNames{count, names}`, ldglobalvar →
//! `TryGetGlobal{name, default: None}` (the THROWING form: `None` =
//! no fallback), tryldglobalbyname → `TryGetGlobal{name, default:
//! Some(undefined)}` (the tolerant form), stglobalvar/trystglobalbyname/
//! st(const)toglobalrecord → `StoreGlobal` (tolerant/strict store
//! distinction folds — documented), ld/stlexvar → `GetLexVar`/
//! `PutLexVar`, newlexenv → `NewLexEnv{num_vars}`, newlexenvwithname →
//! `NewLexEnvWithName{num_vars, scope_names}`, poplexenv → `PopLexEnv`,
//! module-var family → `LoadModuleVar`/`StoreModuleVar` (local vs
//! external folds — documented) /`GetModuleNamespace`, dynamicimport →
//! `DynamicImport`, definefunc → `DefineFunc{body, captures: [],
//! length}` + `AllocClosure` (the closure allocation is explicit in
//! v0.2 — captures are analysis-layer, deferred empty), definemethod →
//! `DefineFunc` + `AllocClosure` + `DefineMethod{object, name, func,
//! length}`, defineclasswithbuffer (+callruntime.definesendableclass,
//! N53) → `DefineClass{ctor, heritage, members, count}` (N15's count
//! modeled), definegettersetterbyvalue → `DefineGetterSetterByValue`,
//! iterators → `GetIterator`/`GetAsyncIterator`/`GetPropIterator`/
//! `IteratorReturn` (closeiterator) /`NextPropName`, generator family →
//! `CreateGenerator` (async folds — documented) /`SuspendGenerator`/
//! `ResumeGenerator`/`GetResumeMode`, async family →
//! `AsyncFunctionEnter`/`AwaitUncaught` (incl. the deprecated form)/
//! `AsyncResolve`/`AsyncReject`/`CreateIterResultObj`
//! (asyncgeneratorresolve folds, v0.1 parity), gettemplateobject →
//! `GetTemplateObject` (acc inout), setobjectwithproto →
//! `SetObjectWithProto` (NEVER a property copy), starrayspread →
//! `ArraySpread` (result = the new index), copydataproperties →
//! `CopyDataProps` (acc := dst after, v0.1 parity), copyrestargs →
//! `CopyRestArgs{start_index}`, getunmappedargs → `GetUnmappedArgs`,
//! ldnewtarget → `LoadNewTarget`, ldglobal → `LoadGlobalObject`,
//! ldfunction (+deprecated.ldlexenv/ldhomeobject) → `LoadFunction`,
//! ldthis → the `this` VALUE (`params[0]` for non-static kinds — T4;
//! `LoadConst(Undefined)` for static/zero-param frames — documented),
//! throw → `Throw`, throw.constassignment → `ThrowConstAssignment`
//! (runtime name value), throw.undefinedifhole →
//! `ThrowUndefinedIfHole` (two-reg), throw.undefinedifholewithname →
//! `ThrowUndefinedIfHoleWithName` (compile-time name), throw.ifnotobject
//! → `ThrowIfNotObject`, throw.ifsupernotcorrectcall →
//! `ThrowIfSuperNotCalled{kind}` (0 → NotCalled, 1 → Rebind, anything
//! else → hard [`LiftError::InvalidSuperCheckKind`]), throw.notexists/
//! patternnoncoercible/deletesuperproperty → the dedicated ops,
//! debugger → `Debugger`, jumps → `Branch`/`CondBranch` (jeqz-family
//! via `UnaryOp::{IsTrue,IsFalse}`; jeq-family via `Compare`), return
//! family → `Return`, setgeneratorstate/nop/callruntime.
//! notifyconcurrentresult/callruntime.topropertykey → no-ops (v0.1
//! parity).
//!
//! Calls: the whole call family folds into one `Call{callee, this,
//! args, kind}` — callarg*/callrange → `Dynamic{this: None}`,
//! callthis* (+withname, callruntime.callinit) → `Dynamic{this:
//! Some(args[0]), args: args[1..]}`, supercallthis/arrowrange →
//! `Super{this: None}` (arrow distinction folds), supercallspread →
//! `Super{args: [array]}` (spread role documented), apply (+deprecated.
//! callspread) → `Apply{this: Some(this), args: [array]}` (the spread
//! role is IR-explicit — v0.1's `CallKind::Apply`, N57), newobjrange → `New{callee: window[0], args:
//! window[1..]}` (argc counts the ctor; argc=0 keeps v0.1's acc
//! fallback), newobjapply → `New{callee: ctor, args: [array]}` (v0.1's
//! swapped NewObjApply roles NORMALIZED to callee=ctor — documented),
//! callruntime.supercallforwardallargs → `Super{args: [this]}` (v0.1's
//! approximation kept verbatim).
//!
//! Deprecated opcodes fold to the modern ops (v0.1 convention), with
//! v0.1's exact operand reads preserved (including its DISCARDED reads
//! — they drive phi materialization): deprecated.ld/stmodulevar and
//! deprecated.getmodulenamespace keep v0.1's raw-symbol-index payload
//! hack (documented), deprecated.createarray/objectwithbuffer and
//! deprecated.createobjecthavingmethod resolve the RAW table index
//! (v0.1 parity), deprecated.defineclasswithbuffer keeps v0.1's operand
//! roles (N54's registered latent issue — base_reg as heritage, env
//! unread).
//!
//! Super-property access by constant INDEX: the ISA has no such opcode
//! — [`LiftError::UnsupportedSuperByIndex`], a hard error, never
//! invented semantics (see [`super_key`]).

use std::collections::HashMap;

use abcd_file::{AccessFlags, Method, MethodBody};
use abcd_ir2::{
    BinOp, BlockId, CallKind, CmpOp, Const, ConstId, FuncId, InstId, Loc, Op, SuperCheck, SuperKey,
    Sym, Ty, UnOp, ValueDef, ValueId,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Reg};

use crate::cfg::RawCfg;
use crate::resolve;
use crate::ssa::{RegOrAcc, SsaBuilder};
use crate::{LiftError, Lifter, emit_inst};

/// A super-property key in the three conceivable forms; the ISA
/// provides name/dynamic producers only.
pub enum SuperKeyForm {
    /// A statically known property name (`ld/stsuperbyname`).
    Name(Sym),
    /// A computed key (`ld/stsuperbyvalue`).
    Dynamic(ValueId),
    /// A constant index — NO ArkCompiler opcode exists.
    Index(u32),
}

/// Convert a super-property key form to the IR key. The constant-index
/// form is a hard error: `isa.yaml` has no super-by-index opcode, so
/// the form is unconstructible from real bytecode and no semantics may
/// be invented for it (v0.1 lower's `UnsupportedInstruction` ruling).
pub fn super_key(form: SuperKeyForm) -> Result<SuperKey, LiftError> {
    match form {
        SuperKeyForm::Name(n) => Ok(SuperKey::Name(n)),
        SuperKeyForm::Dynamic(k) => Ok(SuperKey::Dynamic(k)),
        SuperKeyForm::Index(_) => Err(LiftError::UnsupportedSuperByIndex),
    }
}

/// Per-function translation context.
pub struct FnLift<'l, 'f> {
    /// The module-level conversion state.
    pub lf: &'l mut Lifter<'f>,
    /// The method being lifted.
    pub method: &'f Method,
    /// Its body.
    pub body: &'f MethodBody,
    /// The reserved function-table slot.
    pub func_id: FuncId,
    /// Raw block index → IR block.
    pub block_map: HashMap<usize, BlockId>,
    /// The raw CFG.
    pub raw_cfg: RawCfg,
    /// The Braun construction state.
    pub ssa: SsaBuilder,
    /// Decoded line table, sorted by instruction index — SPARSE
    /// (line-change entries; the running line applies to every pc
    /// at-or-after the entry).
    pub line_table: Vec<(u32, u32)>,
    /// Decoded column table, sorted by instruction index (same sparse
    /// running-value semantics).
    pub col_table: Vec<(u32, u32)>,
    /// Emitted inst → its source bytecode index (derived insts share
    /// their parent bytecode's position; phis have none).
    pub inst_pc: HashMap<InstId, u32>,
    /// `params[0]` for non-static kinds (the `this` value, T4); `None`
    /// for static/zero-parameter frames (set after entry seeding).
    pub this_param: Option<ValueId>,
    /// The method is static (no `this` binding).
    is_static: bool,
}

impl<'l, 'f> FnLift<'l, 'f> {
    /// Build the translation context.
    pub fn new(
        lf: &'l mut Lifter<'f>,
        method: &'f Method,
        body: &'f MethodBody,
        func_id: FuncId,
        block_map: HashMap<usize, BlockId>,
        raw_cfg: RawCfg,
    ) -> Self {
        let undefined_const = lf.const_scalar(Const::Undefined);
        let hole_const = lf.const_scalar(Const::Hole);
        let mut line_table = Vec::new();
        let mut col_table = Vec::new();
        if let Some(debug) = &method.debug {
            for e in &debug.line_table {
                line_table.push((e.index, e.line));
            }
            for e in &debug.column_table {
                col_table.push((e.index, e.column));
            }
        }
        line_table.sort_unstable();
        col_table.sort_unstable();
        let is_static = method.access_flags.contains(AccessFlags::STATIC);
        Self {
            lf,
            method,
            body,
            func_id,
            block_map,
            raw_cfg,
            ssa: SsaBuilder::new(undefined_const, hole_const),
            line_table,
            col_table,
            inst_pc: HashMap::new(),
            this_param: None,
            is_static,
        }
    }

    /// Push a fresh SSA value into the arena.
    pub fn new_value(&mut self, def: ValueDef, ty: Ty) -> ValueId {
        let val = ValueId::new(self.lf.module.values.len() as u32);
        self.lf.module.values.push(abcd_ir2::Value { def, ty });
        val
    }

    /// The running value of a sparse (index → value) debug table at
    /// `pc`: the last entry at-or-before `pc`.
    fn table_lookup(table: &[(u32, u32)], pc: u32) -> Option<u32> {
        match table.partition_point(|&(idx, _)| idx <= pc) {
            0 => None,
            n => Some(table[n - 1].1),
        }
    }

    /// The source line of a bytecode index (running line of the LNP
    /// stream).
    pub fn line_of(&self, pc: u32) -> Option<u32> {
        Self::table_lookup(&self.line_table, pc)
    }

    /// The source column of a bytecode index.
    pub fn column_of(&self, pc: u32) -> Option<u32> {
        Self::table_lookup(&self.col_table, pc)
    }

    /// Source location of a bytecode index (from the LNP tables).
    fn loc_of(&self, pc: u32) -> Option<Loc> {
        self.line_of(pc).map(|line| Loc {
            line,
            column: self.column_of(pc),
        })
    }

    /// Emit an instruction (recording its source position).
    pub fn emit(&mut self, block: BlockId, op: Op, pc: Option<u32>) -> (InstId, Option<ValueId>) {
        let loc = pc.and_then(|pc| self.loc_of(pc));
        let (iid, res) = emit_inst(&mut self.lf.module, block, op, loc);
        if let Some(pc) = pc {
            self.inst_pc.insert(iid, pc);
        }
        (iid, res)
    }

    /// Emit and return the result value.
    pub fn emit_val(&mut self, block: BlockId, op: Op, pc: Option<u32>) -> ValueId {
        self.emit(block, op, pc)
            .1
            .expect("instruction has no result")
    }

    /// Emit a void instruction (no result).
    pub fn emit_void(&mut self, block: BlockId, op: Op, pc: Option<u32>) {
        self.emit(block, op, pc);
    }

    /// Read the accumulator SSA value.
    pub fn read_acc(&mut self, block: BlockId) -> ValueId {
        self.ssa
            .read_variable(RegOrAcc::Acc, block, &mut self.lf.module)
    }

    /// Write the accumulator SSA value.
    pub fn write_acc(&mut self, block: BlockId, val: ValueId) {
        self.ssa.write_variable(RegOrAcc::Acc, block, val);
    }

    /// Read a register SSA value.
    pub fn read_reg(&mut self, reg: Reg, block: BlockId) -> ValueId {
        self.ssa
            .read_variable(RegOrAcc::Reg(reg.0), block, &mut self.lf.module)
    }

    /// Write a register SSA value.
    pub fn write_reg(&mut self, reg: Reg, block: BlockId, val: ValueId) {
        self.ssa.write_variable(RegOrAcc::Reg(reg.0), block, val);
    }

    /// Read a range of consecutive registers.
    pub fn read_reg_range(&mut self, start: u16, count: u16, block: BlockId) -> Vec<ValueId> {
        (0..count)
            .map(|i| self.read_reg(Reg(start + i), block))
            .collect()
    }

    /// The `this` value: `params[0]` for non-static kinds (T4), a
    /// materialized `undefined` constant for static/zero-param frames
    /// (documented — vendor `ldthis` yields undefined there).
    pub fn this_value(&mut self, block: BlockId, pc: Option<u32>) -> ValueId {
        if !self.is_static {
            if let Some(v) = self.this_param {
                return v;
            }
        }
        let c = self.lf.const_scalar(Const::Undefined);
        self.emit_val(block, Op::LoadConst(c), pc)
    }

    /// Resolve a string-pool entity to a symbol.
    pub fn resolve_str(&mut self, eid: EntityId) -> Result<Sym, LiftError> {
        resolve::resolve_sym(self.lf, self.body, eid, EntityKind::StringId)
    }

    /// Resolve a method-reference entity to (display name, FuncId).
    pub fn resolve_method(&mut self, eid: EntityId) -> Result<(Sym, FuncId), LiftError> {
        resolve::resolve_method(self.lf, self.body, eid)
    }

    /// Resolve a literal-array entity to its pooled shape constant.
    pub fn resolve_literal(&mut self, eid: EntityId) -> Result<ConstId, LiftError> {
        resolve::resolve_literal_const(self.lf, self.body, eid)
    }

    /// Emit a `LoadConst` for a scalar constant (deduplicated pool).
    pub fn load_const(&mut self, block: BlockId, c: Const, pc: Option<u32>) -> ValueId {
        let id = self.lf.const_scalar(c);
        self.emit_val(block, Op::LoadConst(id), pc)
    }

    /// The IR block for a jump target label.
    pub fn label_block(&self, label: abcd_isa::Label) -> BlockId {
        let target_idx = label.0 as usize;
        let raw_bi = self.raw_cfg.leader_to_block[&target_idx];
        self.block_map[&raw_bi]
    }

    /// The fall-through block (the block containing the instruction
    /// after `idx`).
    pub fn fallthrough_block(&self, idx: usize) -> BlockId {
        let next_idx = idx + 1;
        for (bi, rb) in self.raw_cfg.blocks.iter().enumerate() {
            if next_idx >= rb.start && next_idx < rb.end {
                return self.block_map[&bi];
            }
        }
        if let Some(&bi) = self.raw_cfg.leader_to_block.get(&next_idx) {
            return self.block_map[&bi];
        }
        let last_bi = self.raw_cfg.blocks.len() - 1;
        self.block_map[&last_bi]
    }
}

/// Translate a single bytecode instruction into v0.2 IR.
pub fn translate_bytecode(
    fx: &mut FnLift,
    bc: &Bytecode,
    idx: usize,
    block: BlockId,
) -> Result<(), LiftError> {
    let loc = Some(idx as u32);

    match bc {
        // ── Data movement (SSA aliases only) ─────────────────────────
        Bytecode::Lda(r) => {
            let v = fx.read_reg(*r, block);
            fx.write_acc(block, v);
        }
        Bytecode::Sta(r) => {
            let v = fx.read_acc(block);
            fx.write_reg(*r, block, v);
        }
        Bytecode::Mov(dst, src) => {
            let v = fx.read_reg(*src, block);
            fx.write_reg(*dst, block, v);
        }

        // ── Literals ─────────────────────────────────────────────────
        Bytecode::Ldundefined => {
            let v = fx.load_const(block, Const::Undefined, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnull => {
            let v = fx.load_const(block, Const::Null, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldtrue => {
            let v = fx.load_const(block, Const::Bool(true), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldfalse => {
            let v = fx.load_const(block, Const::Bool(false), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldai(imm) => {
            let v = fx.load_const(block, Const::number(imm.0 as f64), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Fldai(imm) => {
            let v = fx.load_const(block, Const::Number(imm.0 as u64), loc);
            fx.write_acc(block, v);
        }
        Bytecode::LdaStr(eid) => {
            let s = fx.resolve_str(*eid)?;
            let v = fx.load_const(block, Const::String(s), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldbigint(eid) => {
            // Vendor `ldbigint string_id` (isa.yaml:1622-1626): acc out
            // is a BIGINT built from the constant-pool entry, not a
            // string — a distinct Const, never collapsible into String.
            let s = fx.resolve_str(*eid)?;
            let v = fx.load_const(block, Const::BigInt(s), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnan => {
            let v = fx.load_const(block, Const::number(f64::NAN), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldinfinity => {
            let v = fx.load_const(block, Const::number(f64::INFINITY), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldhole => {
            let v = fx.load_const(block, Const::Hole, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldsymbol => {
            let name = fx.lf.sym("Symbol");
            let default = fx.load_const(block, Const::Undefined, loc);
            let v = fx.emit_val(
                block,
                Op::TryGetGlobal {
                    name,
                    default: Some(default),
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Binary operations (acc = acc OP reg, IC slot discarded) ──
        Bytecode::Add2(_ic, r) => binary_op(fx, BinOp::Add, r, block, loc),
        Bytecode::Sub2(_ic, r) => binary_op(fx, BinOp::Sub, r, block, loc),
        Bytecode::Mul2(_ic, r) => binary_op(fx, BinOp::Mul, r, block, loc),
        Bytecode::Div2(_ic, r) => binary_op(fx, BinOp::Div, r, block, loc),
        Bytecode::Mod2(_ic, r) => binary_op(fx, BinOp::Mod, r, block, loc),
        Bytecode::Exp(_ic, r) => binary_op(fx, BinOp::Exp, r, block, loc),
        Bytecode::Shl2(_ic, r) => binary_op(fx, BinOp::Shl, r, block, loc),
        Bytecode::Shr2(_ic, r) => binary_op(fx, BinOp::Shr, r, block, loc),
        Bytecode::Ashr2(_ic, r) => binary_op(fx, BinOp::Ashr, r, block, loc),
        Bytecode::And2(_ic, r) => binary_op(fx, BinOp::BitAnd, r, block, loc),
        Bytecode::Or2(_ic, r) => binary_op(fx, BinOp::BitOr, r, block, loc),
        Bytecode::Xor2(_ic, r) => binary_op(fx, BinOp::BitXor, r, block, loc),
        Bytecode::Eq(_ic, r) => compare_op(fx, CmpOp::Eq, r, block, loc),
        Bytecode::Noteq(_ic, r) => compare_op(fx, CmpOp::NotEq, r, block, loc),
        Bytecode::Less(_ic, r) => compare_op(fx, CmpOp::Less, r, block, loc),
        Bytecode::Lesseq(_ic, r) => compare_op(fx, CmpOp::LessEq, r, block, loc),
        Bytecode::Greater(_ic, r) => compare_op(fx, CmpOp::Greater, r, block, loc),
        Bytecode::Greatereq(_ic, r) => compare_op(fx, CmpOp::GreaterEq, r, block, loc),
        Bytecode::Isin(_ic, r) => compare_op(fx, CmpOp::In, r, block, loc),
        Bytecode::Instanceof(_ic, r) => compare_op(fx, CmpOp::InstanceOf, r, block, loc),
        Bytecode::Stricteq(_ic, r) => compare_op(fx, CmpOp::StrictEq, r, block, loc),
        Bytecode::Strictnoteq(_ic, r) => compare_op(fx, CmpOp::StrictNotEq, r, block, loc),

        // ── Unary operations (acc = OP acc, IC slot discarded) ───────
        Bytecode::Neg(_ic) => unary_op(fx, UnOp::Minus, block, loc),
        // N39: vendored `not` is BITWISE ~acc, not logical negation
        // (interpreter_assembly.cpp:767-790).
        Bytecode::Not(_ic) => unary_op(fx, UnOp::BitNot, block, loc),
        Bytecode::Inc(_ic) => unary_op(fx, UnOp::Inc, block, loc),
        Bytecode::Dec(_ic) => unary_op(fx, UnOp::Dec, block, loc),
        Bytecode::Typeof(_ic) => unary_op(fx, UnOp::TypeOf, block, loc),
        Bytecode::Tonumber(_ic) => unary_op(fx, UnOp::ToNumber, block, loc),
        Bytecode::Tonumeric(_ic) => unary_op(fx, UnOp::ToNumeric, block, loc),
        Bytecode::Istrue => unary_op(fx, UnOp::IsTrue, block, loc),
        Bytecode::Isfalse => unary_op(fx, UnOp::IsFalse, block, loc),

        // ── Object / Array creation ──────────────────────────────────
        Bytecode::Createemptyobject => {
            let shape = fx.lf.empty_object_shape();
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createemptyarray(_ic) => {
            let v = fx.emit_val(block, Op::AllocArray, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createarraywithbuffer(_ic, eid) => {
            let shape = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createobjectwithbuffer(_ic, eid) => {
            let shape = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createregexpwithliteral(_ic, eid, flags_imm) => {
            let pattern = fx.resolve_str(*eid)?;
            let v = fx.emit_val(
                block,
                Op::AllocRegExp {
                    pattern,
                    flags: flags_imm.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Createobjectwithexcludedkeys(num, obj_reg, start_reg)
        | Bytecode::WideCreateobjectwithexcludedkeys(num, obj_reg, start_reg) => {
            let obj = fx.read_reg(*obj_reg, block);
            let count = num.0 as u16;
            let keys = fx.read_reg_range(start_reg.0, count, block);
            let v = fx.emit_val(block, Op::CreateObjectWithExcludedKeys { obj, keys }, loc);
            fx.write_acc(block, v);
        }

        // ── Property access ──────────────────────────────────────────
        Bytecode::Ldobjbyname(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::LoadProp { object: obj, name }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(
                block,
                Op::StoreProp {
                    object: obj,
                    name,
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyvalue(_ic, obj_reg) => {
            let key = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let v = fx.emit_val(block, Op::LoadPropDyn { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyvalue(_ic, obj_reg, key_reg) => {
            // Vendor: v1 = receiver, v2 = propKey, acc = VALUE
            // (isa.yaml:1353-1357, interpreter_assembly.cpp:2306-2335).
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            fx.emit_void(
                block,
                Op::StorePropDyn {
                    object: obj,
                    key,
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyindex(_, index) | Bytecode::WideLdobjbyindex(index) => {
            let obj = fx.read_acc(block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            let v = fx.emit_val(
                block,
                Op::LoadPropIdx {
                    object: obj,
                    index: konst,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyindex(_, obj_reg, index) | Bytecode::WideStobjbyindex(obj_reg, index) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StorePropIdx {
                    object: obj,
                    index: konst,
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyname(_ic, eid, obj_reg)
        | Bytecode::Stownbynamewithnameset(_ic, eid, obj_reg) => {
            // Own-store fold: v0.2 has one named-store family
            // (documented).
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(
                block,
                Op::StoreProp {
                    object: obj,
                    name,
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyvalue(_ic, obj_reg, key_reg)
        | Bytecode::Stownbyvaluewithnameset(_ic, obj_reg, key_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            fx.emit_void(
                block,
                Op::StorePropDyn {
                    object: obj,
                    key,
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyindex(_, obj_reg, index) | Bytecode::WideStownbyindex(obj_reg, index) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StorePropIdx {
                    object: obj,
                    index: konst,
                    value,
                },
                loc,
            );
        }
        // N51: the `this-by-*` family (isa.yaml:1627-1642) is IC-fused
        // `this` property access that es2panda NEVER emits (`this[k] = v`
        // compiles to `ldthis` + `stobjbyvalue`; upstream source grep zero
        // hits). Zero corpus coverage means no VM evidence for the IC
        // semantics — hard error, never silently invented (maintainer
        // ruling 2026-09-20; mirrors v0.1's
        // `LiftError::UnsupportedThisByAccess`).
        Bytecode::Ldthisbyname(..) => {
            return Err(LiftError::UnsupportedThisByAccess("ldthisbyname"));
        }
        Bytecode::Stthisbyname(..) => {
            return Err(LiftError::UnsupportedThisByAccess("stthisbyname"));
        }
        Bytecode::Ldthisbyvalue(..) => {
            return Err(LiftError::UnsupportedThisByAccess("ldthisbyvalue"));
        }
        Bytecode::Stthisbyvalue(..) => {
            return Err(LiftError::UnsupportedThisByAccess("stthisbyvalue"));
        }
        Bytecode::Ldsuperbyname(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            let v = fx.emit_val(block, Op::LoadSuper { key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stsuperbyname(_ic, eid, val_reg) => {
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            let value = fx.read_reg(*val_reg, block);
            fx.emit_void(block, Op::StoreSuper { key, value }, loc);
        }
        Bytecode::Ldsuperbyvalue(_ic, key_reg) => {
            let k = fx.read_reg(*key_reg, block);
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let v = fx.emit_val(block, Op::LoadSuper { key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stsuperbyvalue(_ic, key_reg, val_reg) => {
            let k = fx.read_reg(*key_reg, block);
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let value = fx.read_reg(*val_reg, block);
            fx.emit_void(block, Op::StoreSuper { key, value }, loc);
        }
        Bytecode::Delobjprop(key_reg) => {
            let obj = fx.read_acc(block);
            let key = fx.read_reg(*key_reg, block);
            let v = fx.emit_val(block, Op::DeleteProp { object: obj, key }, loc);
            fx.write_acc(block, v);
        }

        // ── Private properties ───────────────────────────────────────
        Bytecode::Ldprivateproperty(_ic, level, slot) => {
            // Vendor: imm2 = level, imm3 = slot; acc in = the OBJECT,
            // acc out = the private value (isa.yaml:436-440,
            // interpreter_stub.cpp:853-867). NOT a ByIndex load.
            let obj = fx.read_acc(block);
            let v = fx.emit_val(
                block,
                Op::LoadPrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stprivateproperty(_ic, level, slot, obj_reg) => {
            // Vendor: the REGISTER operand is the OBJECT, the acc
            // carries the VALUE (isa.yaml:441-445,
            // interpreter_stub.cpp:869-879).
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(
                block,
                Op::StorePrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                    value,
                },
                loc,
            );
        }
        Bytecode::Testin(_ic, level, slot) => {
            // Vendor: acc in = the OBJECT, acc out = the boolean result
            // (isa.yaml:446-450, interpreter_stub.cpp:881-890).
            let obj = fx.read_acc(block);
            let v = fx.emit_val(
                block,
                Op::TestPrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Define field/property by name ────────────────────────────
        Bytecode::Definefieldbyname(_ic, eid, obj_reg)
        | Bytecode::Definepropertybyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(
                block,
                Op::StoreProp {
                    object: obj,
                    name,
                    value,
                },
                loc,
            );
        }

        // ── Global variables ─────────────────────────────────────────
        Bytecode::Ldglobalvar(_ic, eid) => {
            // The THROWING form: `default: None` = no fallback when the
            // global is absent (documented convention).
            let name = fx.resolve_str(*eid)?;
            let v = fx.emit_val(
                block,
                Op::TryGetGlobal {
                    name,
                    default: None,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stglobalvar(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::StoreGlobal { name, value }, loc);
        }
        Bytecode::Tryldglobalbyname(_ic, eid) => {
            // The tolerant form: fallback is `undefined` (vendor
            // behavior when the name is missing).
            let name = fx.resolve_str(*eid)?;
            let default = fx.load_const(block, Const::Undefined, loc);
            let v = fx.emit_val(
                block,
                Op::TryGetGlobal {
                    name,
                    default: Some(default),
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Trystglobalbyname(_ic, eid) => {
            // Tolerant/strict store distinction folds (documented).
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::StoreGlobal { name, value }, loc);
        }
        Bytecode::Stconsttoglobalrecord(_ic, eid) | Bytecode::Sttoglobalrecord(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::StoreGlobal { name, value }, loc);
        }

        // ── Lexical variables ────────────────────────────────────────
        Bytecode::Ldlexvar(level, slot) | Bytecode::WideLdlexvar(level, slot) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stlexvar(level, slot) | Bytecode::WideStlexvar(level, slot) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::Newlexenv(num) | Bytecode::WideNewlexenv(num) => {
            let v = fx.emit_val(
                block,
                Op::NewLexEnv {
                    num_vars: num.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newlexenvwithname(num, eid) | Bytecode::WideNewlexenvwithname(num, eid) => {
            let scope_names = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(
                block,
                Op::NewLexEnvWithName {
                    num_vars: num.0 as u16,
                    scope_names,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Poplexenv => {
            fx.emit_void(block, Op::PopLexEnv, loc);
        }

        // ── Module variables ─────────────────────────────────────────
        Bytecode::Ldlocalmodulevar(index) | Bytecode::WideLdlocalmodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Ldexternalmodulevar(index) | Bytecode::WideLdexternalmodulevar(index) => {
            // Local vs external module-var distinction folds
            // (documented).
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stmodulevar(index) | Bytecode::WideStmodulevar(index) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreModuleVar {
                    index: index.0 as u32,
                    value,
                },
                loc,
            );
        }
        Bytecode::Getmodulenamespace(index) | Bytecode::WideGetmodulenamespace(index) => {
            let v = fx.emit_val(
                block,
                Op::GetModuleNamespace {
                    index: index.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Dynamicimport => {
            let specifier = fx.read_acc(block);
            let v = fx.emit_val(block, Op::DynamicImport { specifier }, loc);
            fx.write_acc(block, v);
        }

        // ── Function / Class definition ──────────────────────────────
        Bytecode::Definefunc(_ic, eid, length) => {
            let (_name, body_id) = fx.resolve_method(*eid)?;
            let f = fx.emit_val(
                block,
                Op::DefineFunc {
                    body: body_id,
                    captures: Vec::new(),
                    length: length.0 as u16,
                },
                loc,
            );
            let v = fx.emit_val(block, Op::AllocClosure { func: f }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Definemethod(_ic, eid, length) => {
            let (name, body_id) = fx.resolve_method(*eid)?;
            let home_object = fx.read_acc(block);
            let f = fx.emit_val(
                block,
                Op::DefineFunc {
                    body: body_id,
                    captures: Vec::new(),
                    length: length.0 as u16,
                },
                loc,
            );
            let c = fx.emit_val(block, Op::AllocClosure { func: f }, loc);
            let v = fx.emit_val(
                block,
                Op::DefineMethod {
                    object: home_object,
                    name,
                    func: c,
                    length: length.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Defineclasswithbuffer(_ic, method_eid, lit_eid, count, base_reg) => {
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let members = fx.resolve_literal(*lit_eid)?;
            let base = fx.read_reg(*base_reg, block);
            let v = fx.emit_val(
                block,
                Op::DefineClass {
                    ctor,
                    heritage: Some(base),
                    members,
                    count: count.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Definegettersetterbyvalue(obj_reg, key_reg, getter_reg, setter_reg) => {
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            let getter = fx.read_reg(*getter_reg, block);
            let setter = fx.read_reg(*setter_reg, block);
            let v = fx.emit_val(
                block,
                Op::DefineGetterSetterByValue {
                    obj,
                    key,
                    getter,
                    setter,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Calls ────────────────────────────────────────────────────
        Bytecode::Callarg0(_ic) => {
            let callee = fx.read_acc(block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callarg1(_ic, a0) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callargs2(_ic, a0, a1) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callargs3(_ic, a0, a1, a2) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let arg2 = fx.read_reg(*a2, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callrange(_, argc, start) | Bytecode::WideCallrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis0(_, this_reg) | Bytecode::Callthis0withname(_, _, this_reg) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis1(_, this_reg, a0) | Bytecode::Callthis1withname(_, _, this_reg, a0) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis2(_, this_reg, a0, a1)
        | Bytecode::Callthis2withname(_, _, this_reg, a0, a1) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis3(_, this_reg, a0, a1, a2)
        | Bytecode::Callthis3withname(_, _, this_reg, a0, a1, a2) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let arg2 = fx.read_reg(*a2, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthisrange(_, argc, start) | Bytecode::WideCallthisrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = call_this_args(fx, start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: args.0,
                    args: args.1,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthisrangewithname(_, argc, _, start)
        | Bytecode::WideCallthisrangewithname(argc, _, start) => {
            // callthis*withname: the method name is only a JIT IC hint;
            // folds into the plain callthis form (v0.1 parity).
            let callee = fx.read_acc(block);
            let args = call_this_args(fx, start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: args.0,
                    args: args.1,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallthisrange(_, argc, start)
        | Bytecode::WideSupercallthisrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Super,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallarrowrange(_, argc, start)
        | Bytecode::WideSupercallarrowrange(argc, start) => {
            // Arrow distinction folds into Super (documented).
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Super,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallspread(_ic, arg_reg) => {
            let callee = fx.read_acc(block);
            let arg = fx.read_reg(*arg_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg],
                    kind: CallKind::Super,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Apply(_ic, this_reg, args_reg) => {
            // N57: the apply opcode identity is IR-explicit
            // (`CallKind::Apply`, v0.1 parity) — args[0] is the argument
            // ARRAY, never a positional argument.
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let args_arr = fx.read_reg(*args_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![args_arr],
                    kind: CallKind::Apply,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newobjrange(_, argc, start) | Bytecode::WideNewobjrange(argc, start) => {
            // Vendor: the constructor is the FIRST register of the
            // range and argc COUNTS it; the slow path passes the ctor
            // as both func and newTarget (interpreter-inl.cpp:4205,
            // wide twin :4476).
            let range = fx.read_reg_range(start.0, argc.0 as u16, block);
            let (callee, args) = match range.split_first() {
                Some((&ctor, rest)) => (ctor, rest.to_vec()),
                // Degenerate argc = 0: v0.1's acc fallback (no operand
                // invented or dropped).
                None => (fx.read_acc(block), Vec::new()),
            };
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::New,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newobjapply(_ic, obj_reg) => {
            // Vendor (interpreter_assembly.cpp:1912-1926): the REGISTER
            // operand is the constructor, the ACC is the spread array.
            // v0.2 NORMALIZES to callee=ctor (v0.1's NewObjApply
            // carried the swapped roles — documented).
            let array = fx.read_acc(block);
            let ctor = fx.read_reg(*obj_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee: ctor,
                    this: None,
                    args: vec![array],
                    kind: CallKind::New,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Special value loaders ────────────────────────────────────
        Bytecode::Ldthis => {
            let v = fx.this_value(block, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnewtarget => {
            let v = fx.emit_val(block, Op::LoadNewTarget, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldglobal => {
            let v = fx.emit_val(block, Op::LoadGlobalObject, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldfunction => {
            let v = fx.emit_val(block, Op::LoadFunction, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getunmappedargs => {
            let v = fx.emit_val(block, Op::GetUnmappedArgs, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Copyrestargs(index) | Bytecode::WideCopyrestargs(index) => {
            let v = fx.emit_val(
                block,
                Op::CopyRestArgs {
                    start_index: index.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Iterators ────────────────────────────────────────────────
        Bytecode::Getiterator(_ic) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getasynciterator(_ic) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetAsyncIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getpropiterator => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetPropIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Closeiterator(_ic, iter_reg) => {
            // `closeiterator` calls the iterator's `return()` —
            // v0.2's IteratorReturn (documented rename).
            let iterator = fx.read_reg(*iter_reg, block);
            let v = fx.emit_val(block, Op::IteratorReturn { iterator }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getnextpropname(iter_reg) => {
            // Vendor: the register operand is the for-in iterator; the
            // NEXT PROPERTY NAME goes to acc (isa.yaml:1289-1292).
            let iterator = fx.read_reg(*iter_reg, block);
            let v = fx.emit_val(block, Op::NextPropName { iterator }, loc);
            fx.write_acc(block, v);
        }

        // ── Generator / Async ────────────────────────────────────────
        Bytecode::Creategeneratorobj(func_reg) => {
            let func = fx.read_reg(*func_reg, block);
            let v = fx.emit_val(block, Op::CreateGenerator { func }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createasyncgeneratorobj(func_reg) => {
            // Async-generator fold (documented).
            let func = fx.read_reg(*func_reg, block);
            let v = fx.emit_val(block, Op::CreateGenerator { func }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Suspendgenerator(gen_reg) => {
            // Vendor: the register operand is the generator object, the
            // accumulator carries the YIELD VALUE; the resume result
            // goes back to acc (isa.yaml:1302-1305).
            let genobj = fx.read_reg(*gen_reg, block);
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::SuspendGenerator { genobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Resumegenerator => {
            // Vendor `acc: inout:top`, no register operand
            // (isa.yaml:1261-1264).
            let genobj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::ResumeGenerator { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getresumemode => {
            // Vendor `acc: inout:top`, no register operand
            // (isa.yaml:1270-1273). Distinct from ResumeGenerator.
            let genobj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetResumeMode { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Setgeneratorstate(_imm) => {
            // State bookkeeping — no IR side effect needed (v0.1
            // parity).
        }
        Bytecode::Asyncfunctionenter => {
            let v = fx.emit_val(block, Op::AsyncFunctionEnter, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionawaituncaught(val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AwaitUncaught { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionresolve(val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncResolve { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionreject(val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncReject { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncgeneratorresolve(val_reg, done_reg, _next_reg) => {
            // v0.1 folds to the iter-result object (parity); _next_reg
            // is not read by v0.1 either.
            let value = fx.read_reg(*val_reg, block);
            let done = fx.read_reg(*done_reg, block);
            let v = fx.emit_val(block, Op::CreateIterResultObj { value, done }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncgeneratorreject(val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncReject { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createiterresultobj(val_reg, done_reg) => {
            let value = fx.read_reg(*val_reg, block);
            let done = fx.read_reg(*done_reg, block);
            let v = fx.emit_val(block, Op::CreateIterResultObj { value, done }, loc);
            fx.write_acc(block, v);
        }

        // ── Misc ─────────────────────────────────────────────────────
        Bytecode::Gettemplateobject(_ic) => {
            // Vendor `acc: inout:top` (isa.yaml:1279-1283): the acc
            // carries the template literal, the (cached) template
            // object goes back to acc. NOT an element read.
            let literal = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetTemplateObject { literal }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Setobjectwithproto(_ic, proto_reg) => {
            // Vendor: v is the proto, the OBJECT rides the accumulator;
            // sets the prototype link directly — NEVER a property copy
            // (isa.yaml:1333-1337).
            let obj = fx.read_acc(block);
            let proto = fx.read_reg(*proto_reg, block);
            fx.emit_void(block, Op::SetObjectWithProto { proto, obj }, loc);
        }
        Bytecode::Starrayspread(arr_reg, index_reg) => {
            // Vendor: v1 = destination array, v2 = start index, acc =
            // source iterable; the NEW INDEX is written back to acc
            // (isa.yaml:1329-1332, interpreter_assembly.cpp:2876-2894).
            let src = fx.read_acc(block);
            let dst = fx.read_reg(*arr_reg, block);
            let index = fx.read_reg(*index_reg, block);
            let v = fx.emit_val(block, Op::ArraySpread { dst, index, src }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Copydataproperties(dst_reg) => {
            // Vendor: the register operand is the TARGET, the acc
            // carries the SOURCE and receives the result (the target).
            let src = fx.read_acc(block);
            let dst = fx.read_reg(*dst_reg, block);
            fx.emit_void(block, Op::CopyDataProps { dst, src }, loc);
            // acc: inout — after the instruction acc holds the target.
            fx.write_acc(block, dst);
        }

        // ── Control flow — jumps ─────────────────────────────────────
        Bytecode::Jmp(label) => {
            let dest = fx.label_block(*label);
            fx.emit_void(block, Op::Branch { dest }, loc);
        }
        Bytecode::Jeqz(label) => cond_branch_acc(fx, false, *label, idx, block, loc),
        Bytecode::Jnez(label) => cond_branch_acc(fx, true, *label, idx, block, loc),
        Bytecode::Jstricteqz(label) => {
            // acc === 0 → branch
            cond_branch_acc(fx, false, *label, idx, block, loc);
        }
        Bytecode::Jnstricteqz(label) => cond_branch_acc(fx, true, *label, idx, block, loc),
        Bytecode::Jeqnull(label) | Bytecode::Jstricteqnull(label) => {
            cond_branch_acc(fx, false, *label, idx, block, loc);
        }
        Bytecode::Jnenull(label) | Bytecode::Jnstricteqnull(label) => {
            cond_branch_acc(fx, true, *label, idx, block, loc);
        }
        Bytecode::Jequndefined(label) | Bytecode::Jstrictequndefined(label) => {
            cond_branch_acc(fx, false, *label, idx, block, loc);
        }
        Bytecode::Jneundefined(label) | Bytecode::Jnstrictequndefined(label) => {
            cond_branch_acc(fx, true, *label, idx, block, loc);
        }
        Bytecode::Jeq(reg, label) => {
            compare_branch(fx, CmpOp::Eq, reg, *label, idx, block, loc);
        }
        Bytecode::Jne(reg, label) => {
            compare_branch(fx, CmpOp::NotEq, reg, *label, idx, block, loc);
        }
        Bytecode::Jstricteq(reg, label) => {
            compare_branch(fx, CmpOp::StrictEq, reg, *label, idx, block, loc);
        }
        Bytecode::Jnstricteq(reg, label) => {
            compare_branch(fx, CmpOp::StrictNotEq, reg, *label, idx, block, loc);
        }

        // ── Return ───────────────────────────────────────────────────
        Bytecode::Return => {
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::Return { value: Some(value) }, loc);
        }
        Bytecode::Returnundefined => {
            fx.emit_void(block, Op::Return { value: None }, loc);
        }

        // ── Exception handling ───────────────────────────────────────
        Bytecode::Throw => {
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::Throw { value }, loc);
        }
        Bytecode::ThrowNotexists => {
            fx.emit_void(block, Op::ThrowNotExists, loc);
        }
        Bytecode::ThrowPatternnoncoercible => {
            fx.emit_void(block, Op::ThrowPatternNonCoercible, loc);
        }
        Bytecode::ThrowDeletesuperproperty => {
            fx.emit_void(block, Op::ThrowDeleteSuperProperty, loc);
        }
        Bytecode::ThrowConstassignment(name_reg) => {
            // Vendor: the register operand carries the variable name AS
            // A RUNTIME STRING VALUE (isa.yaml:987-991).
            let name = fx.read_reg(*name_reg, block);
            fx.emit_void(block, Op::ThrowConstAssignment { name }, loc);
        }
        Bytecode::ThrowIfnotobject(val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            fx.emit_void(block, Op::ThrowIfNotObject { value }, loc);
        }
        Bytecode::ThrowUndefinedifhole(name_reg, val_reg) => {
            // Vendor: v1 carries the variable name AS A RUNTIME STRING
            // VALUE, v2 the checked value; acc untouched
            // (isa.yaml:998-1002).
            let name = fx.read_reg(*name_reg, block);
            let value = fx.read_reg(*val_reg, block);
            fx.emit_void(block, Op::ThrowUndefinedIfHole { name, value }, loc);
        }
        Bytecode::ThrowUndefinedifholewithname(eid) => {
            // Vendor: here the name IS a compile-time source string and
            // the checked value rides the accumulator
            // (isa.yaml:1010-1015) — a distinct instruction from the
            // two-register form.
            let name = fx.resolve_str(*eid)?;
            let acc = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::ThrowUndefinedIfHoleWithName { name, value: acc },
                loc,
            );
        }
        Bytecode::ThrowIfsupernotcorrectcall(imm) => {
            // Vendor: the imm selects the CHECK KIND (0 = TDZ guard,
            // 1 = re-bind guard — runtime_stubs-inl.h:2520-2532) and
            // the acc carries the `this` value being checked
            // (isa.yaml:1003-1008).
            let value = fx.read_acc(block);
            let kind = match imm.0 as u16 {
                0 => SuperCheck::NotCalled,
                1 => SuperCheck::Rebind,
                other => return Err(LiftError::InvalidSuperCheckKind(other)),
            };
            fx.emit_void(block, Op::ThrowIfSuperNotCalled { value, kind }, loc);
        }

        // ── Debug ────────────────────────────────────────────────────
        Bytecode::Debugger => {
            fx.emit_void(block, Op::Debugger, loc);
        }
        Bytecode::Nop => { /* no-op */ }

        // ── Callruntime variants ─────────────────────────────────────
        Bytecode::CallruntimeNotifyconcurrentresult | Bytecode::CallruntimeTopropertykey => {
            // acc stays unchanged or is a pass-through (v0.1 parity).
        }
        Bytecode::CallruntimeDefinefieldbyvalue(_ic, key_reg, obj_reg) => {
            // Vendor: the FIRST register operand is the propKey, the
            // SECOND is the obj, the acc carries the value
            // (isa.yaml:826-831, interpreter_stub.cpp:6031-6043).
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            fx.emit_void(
                block,
                Op::StorePropDyn {
                    object: obj,
                    key,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeDefinefieldbyindex(_ic, index, obj_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StorePropIdx {
                    object: obj,
                    index: konst,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCreateprivateproperty(count, eid) => {
            // Vendor: registers `count` private names from the literal
            // array in the current environment (isa.yaml:843-848,
            // interpreter_stub.cpp:6066-6077). VOID, but observable.
            let names = fx.resolve_literal(*eid)?;
            fx.emit_void(
                block,
                Op::CreatePrivateNames {
                    count: count.0 as u16,
                    names,
                },
                loc,
            );
        }
        Bytecode::CallruntimeDefineprivateproperty(_ic, level, slot, obj_reg) => {
            // Vendor: the REGISTER operand is the OBJECT, the acc
            // carries the VALUE (isa.yaml:849-854,
            // interpreter_stub.cpp:6079-6091).
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(
                block,
                Op::DefinePrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCallinit(_ic, this_reg) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeDefinesendableclass(_ic, method_eid, lit_eid, count, base_reg) => {
            // N53: folds into the plain defineclasswithbuffer form.
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let members = fx.resolve_literal(*lit_eid)?;
            let base = fx.read_reg(*base_reg, block);
            let v = fx.emit_val(
                block,
                Op::DefineClass {
                    ctor,
                    heritage: Some(base),
                    members,
                    count: count.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdsendableclass(index)
        | Bytecode::CallruntimeLdsendableexternalmodulevar(index)
        | Bytecode::CallruntimeWideldsendableexternalmodulevar(index)
        | Bytecode::CallruntimeLdsendablelocalmodulevar(index)
        | Bytecode::CallruntimeWideldsendablelocalmodulevar(index)
        | Bytecode::CallruntimeLdlazymodulevar(index)
        | Bytecode::CallruntimeWideldlazymodulevar(index)
        | Bytecode::CallruntimeLdlazysendablemodulevar(index)
        | Bytecode::CallruntimeWideldlazysendablemodulevar(index) => {
            // Sendable/lazy module-var forms fold to the plain
            // module-var load (v0.1 parity).
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeNewsendableenv(num) | Bytecode::CallruntimeWidenewsendableenv(num) => {
            let v = fx.emit_val(
                block,
                Op::NewLexEnv {
                    num_vars: num.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeStsendablevar(level, slot)
        | Bytecode::CallruntimeWidestsendablevar(level, slot) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeLdsendablevar(level, slot)
        | Bytecode::CallruntimeWideldsendablevar(level, slot) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeIstrue(_ic) => unary_op(fx, UnOp::IsTrue, block, loc),
        Bytecode::CallruntimeIsfalse(_ic) => unary_op(fx, UnOp::IsFalse, block, loc),
        Bytecode::CallruntimeSupercallforwardallargs(this_reg) => {
            // v0.1's approximation kept verbatim: the enclosing `this`
            // is modeled as the single forwarded argument.
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![this],
                    kind: CallKind::Super,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Patch var (for hot-reload) ───────────────────────────────
        Bytecode::WideLdpatchvar(index) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: 0,
                    slot: index.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::WideStpatchvar(index) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: 0,
                    slot: index.0 as u16,
                    value,
                },
                loc,
            );
        }

        // ── Deprecated variants ──────────────────────────────────────
        // Map deprecated instructions to the same IR as their modern
        // equivalents (v0.1 convention).
        Bytecode::DeprecatedLdlexenv | Bytecode::DeprecatedLdhomeobject => {
            // These load environment/home object into acc — v0.1 models
            // them as LoadFunction (parity).
            let v = fx.emit_val(block, Op::LoadFunction, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedPoplexenv => {
            fx.emit_void(block, Op::PopLexEnv, loc);
        }
        Bytecode::DeprecatedGetiteratornext(iter_reg, _step_reg) => {
            // v0.1's fold kept verbatim (GetIterator over the register
            // operand).
            let iterator = fx.read_reg(*iter_reg, block);
            let v = fx.emit_val(block, Op::GetIterator { obj: iterator }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCreatearraywithbuffer(idx)
        | Bytecode::DeprecatedCreateobjectwithbuffer(idx) => {
            // v0.1 parity: the deprecated form carries the RAW table
            // index (no entity-offset indirection).
            let shape = resolve::const_for_literal_array(fx.lf, idx.0 as u32)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedTonumber(dst) | Bytecode::DeprecatedTonumeric(dst) => {
            let val = fx.read_reg(*dst, block);
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::ToNumber,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedNeg(src) => {
            let val = fx.read_reg(*src, block);
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Minus,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedNot(src) => {
            // N39: `deprecated.not` is the same BITWISE ~ on the
            // register operand (interpreter_assembly.cpp:4761-4786).
            let val = fx.read_reg(*src, block);
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::BitNot,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedInc(src) => {
            let val = fx.read_reg(*src, block);
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Inc,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDec(src) => {
            let val = fx.read_reg(*src, block);
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Dec,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallarg0(callee_reg) => {
            let callee = fx.read_reg(*callee_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallarg1(callee_reg, a0) => {
            let callee = fx.read_reg(*callee_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallargs2(callee_reg, a0, a1) => {
            let callee = fx.read_reg(*callee_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallargs3(callee_reg, a0, a1, a2) => {
            let callee = fx.read_reg(*callee_reg, block);
            let arg0 = fx.read_reg(*a0, block);
            let arg1 = fx.read_reg(*a1, block);
            let arg2 = fx.read_reg(*a2, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallspread(func_reg, this_reg, array_reg) => {
            // Vendor `deprecated.callspread v1, v2, v3`
            // (isa.yaml:1109): CallSpread(func=v1, obj=v2, array=v3) —
            // identical semantics to the modern `apply` with func in
            // acc; lifts to the 2-role Apply form (N16/N57, v0.1
            // parity).
            let func = fx.read_reg(*func_reg, block);
            let this = fx.read_reg(*this_reg, block);
            let array = fx.read_reg(*array_reg, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee: func,
                    this: Some(this),
                    args: vec![array],
                    kind: CallKind::Apply,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallthisrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = call_this_args(fx, start.0, argc.0 as u16, block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: args.0,
                    args: args.1,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDefineclasswithbuffer(
            method_eid,
            lit_idx,
            count,
            base_reg,
            _env_reg,
        ) => {
            // v0.1 parity (N54's registered latent issue): base_reg is
            // read as the heritage, _env_reg is NOT read.
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let members = resolve::const_for_literal_array(fx.lf, lit_idx.0 as u32)?;
            let base = fx.read_reg(*base_reg, block);
            let v = fx.emit_val(
                block,
                Op::DefineClass {
                    ctor,
                    heritage: Some(base),
                    members,
                    count: count.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedResumegenerator(gen_reg) => {
            // Vendor: genobj is the register operand here
            // (isa.yaml:1265-1269).
            let genobj = fx.read_reg(*gen_reg, block);
            let v = fx.emit_val(block, Op::ResumeGenerator { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedGetresumemode(gen_reg) => {
            // Vendor: genobj is the register operand here
            // (isa.yaml:1274-1278).
            let genobj = fx.read_reg(*gen_reg, block);
            let v = fx.emit_val(block, Op::GetResumeMode { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedGettemplateobject(tpl_reg) => {
            // Vendor: the template literal comes from the register
            // operand (isa.yaml:1284-1288); folds into the modern op.
            let literal = fx.read_reg(*tpl_reg, block);
            let v = fx.emit_val(block, Op::GetTemplateObject { literal }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDelobjprop(obj_reg, key_reg) => {
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            let v = fx.emit_val(block, Op::DeleteProp { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedSuspendgenerator(gen_reg, val_reg) => {
            // Vendor: v1 is the generator object, v2 the yield value
            // (isa.yaml:1306-1310).
            let genobj = fx.read_reg(*gen_reg, block);
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::SuspendGenerator { genobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionawaituncaught(async_reg, val_reg) => {
            // v0.1 reads (and discards) the async object register —
            // the read is preserved: it drives phi materialization.
            let _async_obj = fx.read_reg(*async_reg, block);
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AwaitUncaught { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCopydataproperties(dst_reg, src_reg) => {
            // Vendor: v1 = target, v2 = source; the result (the target)
            // is written to acc (v0.1 parity).
            let dst = fx.read_reg(*dst_reg, block);
            let src = fx.read_reg(*src_reg, block);
            fx.emit_void(block, Op::CopyDataProps { dst, src }, loc);
            fx.write_acc(block, dst);
        }
        Bytecode::DeprecatedSetobjectwithproto(proto_reg, obj_reg) => {
            // Vendor: v1 = proto, v2 = obj (isa.yaml:1338-1342); folds
            // into the modern op.
            let proto = fx.read_reg(*proto_reg, block);
            let obj = fx.read_reg(*obj_reg, block);
            fx.emit_void(block, Op::SetObjectWithProto { proto, obj }, loc);
        }
        Bytecode::DeprecatedLdobjbyvalue(obj_reg, key_reg) => {
            let obj = fx.read_reg(*obj_reg, block);
            let key = fx.read_reg(*key_reg, block);
            let v = fx.emit_val(block, Op::LoadPropDyn { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdsuperbyvalue(obj_reg, key_reg) => {
            // v0.1 reads (and discards) the receiver register — the
            // read is preserved.
            let _obj = fx.read_reg(*obj_reg, block);
            let k = fx.read_reg(*key_reg, block);
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let v = fx.emit_val(block, Op::LoadSuper { key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdobjbyindex(obj_reg, index) => {
            let obj = fx.read_reg(*obj_reg, block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            let v = fx.emit_val(
                block,
                Op::LoadPropIdx {
                    object: obj,
                    index: konst,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionresolve(async_reg, val_reg, _can_suspend_reg) => {
            let _async_obj = fx.read_reg(*async_reg, block);
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncResolve { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionreject(async_reg, val_reg, _can_suspend_reg) => {
            let _async_obj = fx.read_reg(*async_reg, block);
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncReject { value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStlexvar(level, slot, val_reg) => {
            let value = fx.read_reg(*val_reg, block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                },
                loc,
            );
        }
        Bytecode::DeprecatedGetmodulenamespace(eid) => {
            // v0.1's raw-symbol-index payload hack kept verbatim
            // (documented): the deprecated form references the module
            // by a string id that has no module-slot meaning.
            let name = fx.resolve_str(*eid)?;
            let v = fx.emit_val(block, Op::GetModuleNamespace { index: name.0 }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStmodulevar(eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreModuleVar {
                    index: name.0,
                    value,
                },
                loc,
            );
        }
        Bytecode::DeprecatedLdobjbyname(eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let obj = fx.read_reg(*obj_reg, block);
            let v = fx.emit_val(block, Op::LoadProp { object: obj, name }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdsuperbyname(eid, _obj_reg) => {
            // v0.1 does NOT read the receiver register here (parity).
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            let v = fx.emit_val(block, Op::LoadSuper { key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdmodulevar(eid, _flag) => {
            let name = fx.resolve_str(*eid)?;
            let v = fx.emit_val(block, Op::LoadModuleVar { index: name.0 }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStconsttoglobalrecord(eid)
        | Bytecode::DeprecatedStlettoglobalrecord(eid)
        | Bytecode::DeprecatedStclasstoglobalrecord(eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::StoreGlobal { name, value }, loc);
        }
        Bytecode::DeprecatedCreateobjecthavingmethod(idx) => {
            let shape = resolve::const_for_literal_array(fx.lf, idx.0 as u32)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDynamicimport(spec_reg) => {
            let specifier = fx.read_reg(*spec_reg, block);
            let v = fx.emit_val(block, Op::DynamicImport { specifier }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncgeneratorreject(gen_reg, val_reg) => {
            let _gen = fx.read_reg(*gen_reg, block);
            let value = fx.read_reg(*val_reg, block);
            let v = fx.emit_val(block, Op::AsyncReject { value }, loc);
            fx.write_acc(block, v);
        }
    }

    Ok(())
}

// ─── Helper functions ────────────────────────────────────────────────────────

/// Emit a binary operation: acc = acc OP reg.
fn binary_op(fx: &mut FnLift, op: BinOp, r: &Reg, block: BlockId, loc: Option<u32>) {
    let left = fx.read_acc(block);
    let right = fx.read_reg(*r, block);
    let v = fx.emit_val(block, Op::BinaryOp { op, left, right }, loc);
    fx.write_acc(block, v);
}

/// Emit a comparison: acc = acc CMP reg.
fn compare_op(fx: &mut FnLift, op: CmpOp, r: &Reg, block: BlockId, loc: Option<u32>) {
    let left = fx.read_acc(block);
    let right = fx.read_reg(*r, block);
    let v = fx.emit_val(block, Op::Compare { op, left, right }, loc);
    fx.write_acc(block, v);
}

/// Emit a unary operation: acc = OP acc.
fn unary_op(fx: &mut FnLift, op: UnOp, block: BlockId, loc: Option<u32>) {
    let operand = fx.read_acc(block);
    let v = fx.emit_val(block, Op::UnaryOp { op, operand }, loc);
    fx.write_acc(block, v);
}

/// Read a callthis-family register window: the first register is
/// `this`, the rest are the call arguments. An empty window (degenerate
/// argc = 0) yields `this: None` (no operand invented).
fn call_this_args(
    fx: &mut FnLift,
    start: u16,
    count: u16,
    block: BlockId,
) -> (Option<ValueId>, Vec<ValueId>) {
    let range = fx.read_reg_range(start, count, block);
    match range.split_first() {
        Some((&this, rest)) => (Some(this), rest.to_vec()),
        None => (None, Vec::new()),
    }
}

/// Emit a conditional branch based on the accumulator value. If
/// `truthy` is true, branch to `label` when acc is truthy (jnez-like);
/// otherwise branch when acc is falsy (jeqz-like).
fn cond_branch_acc(
    fx: &mut FnLift,
    truthy: bool,
    label: abcd_isa::Label,
    idx: usize,
    block: BlockId,
    loc: Option<u32>,
) {
    let acc = fx.read_acc(block);
    let op = if truthy { UnOp::IsTrue } else { UnOp::IsFalse };
    let cond = fx.emit_val(block, Op::UnaryOp { op, operand: acc }, loc);
    let true_dest = fx.label_block(label);
    let false_dest = fx.fallthrough_block(idx);
    fx.emit_void(
        block,
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        },
        loc,
    );
}

/// Emit a compare + conditional branch (jeq/jne/jstricteq/jnstricteq):
/// jump to `label` when `acc CMP reg` holds.
fn compare_branch(
    fx: &mut FnLift,
    op: CmpOp,
    reg: &Reg,
    label: abcd_isa::Label,
    idx: usize,
    block: BlockId,
    loc: Option<u32>,
) {
    let acc = fx.read_acc(block);
    let other = fx.read_reg(*reg, block);
    let cond = fx.emit_val(
        block,
        Op::Compare {
            op,
            left: acc,
            right: other,
        },
        loc,
    );
    let true_dest = fx.label_block(label);
    let false_dest = fx.fallthrough_block(idx);
    fx.emit_void(
        block,
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        },
        loc,
    );
}
