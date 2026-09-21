//! Shared test infrastructure for the abcd-opt regression tests: a small
//! hand-builder for v0.2 IR modules (abcd-ir has no IRBuilder — tests
//! construct modules directly, same policy as abcd-lower's tests) and a
//! minimal deterministic bytecode interpreter for the end-to-end
//! lift → optimize → lower tests (ported from v0.1 `abcd-ir/tests/common`
//! via abcd-lower's tests/common).
//!
//! Every test target compiles this shared module separately and uses a
//! different subset of the helpers — allow dead code module-wide.
#![allow(dead_code)]

use std::collections::HashMap;

use abcd_ir::{
    Block, BlockId, ClassId, Const, ConstId, Edge, EdgeKind, FuncId, FunctionData, FunctionKind,
    Inst, InstId, Module, Op, Sym, Ty, Value, ValueDef, ValueId,
};
use abcd_isa::Bytecode;

// ─── v0.2 IR hand-builder ────────────────────────────────────────────────────

/// A minimal v0.2 module/function builder for lowering tests.
pub struct V2Builder<'m> {
    /// The module under construction.
    pub module: &'m mut Module,
    /// The function being built.
    pub func: FuncId,
    insert: BlockId,
}

impl<'m> V2Builder<'m> {
    /// Create a function (with its entry block) and return its id.
    /// A stub class record is created on first use so
    /// [`FunctionData::class_id`] is valid.
    pub fn create_function(module: &'m mut Module, name: &str, kind: FunctionKind) -> FuncId {
        if module.classes.is_empty() {
            let descriptor = module.sym.intern("Ltest;");
            module.classes.push(abcd_ir::ClassData {
                descriptor,
                name: descriptor,
                modifiers: abcd_ir::Modifiers::NONE,
                source_lang: abcd_ir::SourceLang::EcmaScript,
                super_class: None,
                interfaces: Vec::new(),
                fields: Vec::new(),
                methods: Vec::new(),
                annotations: Vec::new(),
                source_file: None,
            });
        }
        let sym = module.sym.intern(name);
        let func = FuncId::new(module.functions.len() as u32);
        module
            .functions
            .push(FunctionData::new(ClassId::new(0), sym, kind));
        let entry = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());
        module.functions[func.index()].blocks.push(entry);
        func
    }

    /// Start building `func`'s body (insertion point: the entry block).
    pub fn new(module: &'m mut Module, func: FuncId) -> Self {
        let insert = module.functions[func.index()].blocks[0];
        Self {
            module,
            func,
            insert,
        }
    }

    /// The entry block of the function under construction.
    pub fn entry(&self) -> BlockId {
        self.module.functions[self.func.index()].blocks[0]
    }

    /// Append a fresh block to the function and return its id.
    pub fn create_block(&mut self) -> BlockId {
        let bb = BlockId::new(self.module.blocks.len() as u32);
        self.module.blocks.push(Block::default());
        self.module.functions[self.func.index()].blocks.push(bb);
        bb
    }

    /// Set the insertion block for subsequent emits.
    pub fn set_insert_block(&mut self, bb: BlockId) {
        self.insert = bb;
    }

    /// Add a Normal CFG predecessor edge.
    pub fn add_predecessor(&mut self, block: BlockId, pred: BlockId) {
        self.module.blocks[block.index()].preds.push(Edge {
            from: pred,
            kind: EdgeKind::Normal,
        });
    }

    /// Add an Exceptional CFG predecessor edge.
    pub fn add_exceptional_predecessor(&mut self, block: BlockId, pred: BlockId) {
        self.module.blocks[block.index()].preds.push(Edge {
            from: pred,
            kind: EdgeKind::Exceptional,
        });
    }

    /// Push a constant into the pool, returning its id.
    pub fn konst(&mut self, c: Const) -> ConstId {
        self.module.consts.push(c)
    }

    /// Intern a name, returning its symbol.
    pub fn sym(&mut self, s: &str) -> Sym {
        self.module.sym.intern(s)
    }

    /// Emit an op in the insertion block; returns (inst, result).
    pub fn emit(&mut self, op: Op) -> (InstId, Option<ValueId>) {
        let has_result = op.has_result();
        let is_phi = op.is_phi();
        let iid = InstId::new(self.module.insts.len() as u32);
        let result = if has_result {
            let val = ValueId::new(self.module.values.len() as u32);
            self.module.values.push(Value {
                def: ValueDef::Inst(iid),
                ty: Ty::Any,
            });
            Some(val)
        } else {
            None
        };
        self.module.insts.push(Inst {
            op,
            result,
            block: self.insert,
            loc: None,
        });
        let bb = &mut self.module.blocks[self.insert.index()];
        if is_phi {
            let phi_len = bb
                .insts
                .iter()
                .take_while(|&&i| self.module.insts[i.index()].op.is_phi())
                .count();
            bb.insts.insert(phi_len, iid);
        } else {
            bb.insts.push(iid);
        }
        (iid, result)
    }

    /// Emit an op and return its result value.
    pub fn emit_val(&mut self, op: Op) -> ValueId {
        self.emit(op).1.expect("op has a result")
    }

    /// Emit a void op (no result).
    pub fn emit_void(&mut self, op: Op) {
        self.emit(op);
    }

    /// Create a function parameter value (appended to `func.params`).
    pub fn create_param(&mut self) -> ValueId {
        let i = self.module.functions[self.func.index()].params.len() as u16;
        let val = ValueId::new(self.module.values.len() as u32);
        self.module.values.push(Value {
            def: ValueDef::Param(i),
            ty: Ty::Any,
        });
        self.module.functions[self.func.index()].params.push(val);
        val
    }

    /// Create a handler exception parameter for `handler`.
    pub fn create_exception_param(&mut self, handler: BlockId) -> ValueId {
        let val = ValueId::new(self.module.values.len() as u32);
        self.module.values.push(Value {
            def: ValueDef::ExceptionParam(handler),
            ty: Ty::Any,
        });
        val
    }

    /// Emit a `LoadConst` of a pooled number, returning its value.
    pub fn emit_number(&mut self, n: f64) -> ValueId {
        let cid = self.konst(Const::number(n));
        self.emit_val(Op::LoadConst(cid))
    }

    /// Add a catch-all try region over `protected` with handler `handler`,
    /// creating the handler's exception parameter and the Exceptional
    /// predecessor edges the v0.2 verifier requires (T5). Returns the
    /// exception value.
    pub fn add_try(&mut self, protected: Vec<BlockId>, handler: BlockId) -> ValueId {
        let exc = ValueId::new(self.module.values.len() as u32);
        self.module.values.push(Value {
            def: ValueDef::ExceptionParam(handler),
            ty: Ty::Any,
        });
        for &p in &protected {
            self.module.blocks[handler.index()].preds.push(Edge {
                from: p,
                kind: EdgeKind::Exceptional,
            });
        }
        self.module.functions[self.func.index()]
            .try_regions
            .push(abcd_ir::TryRegion {
                protected,
                catches: vec![abcd_ir::Catch {
                    handler,
                    exception: exc,
                    type_idx: None,
                }],
            });
        exc
    }

    /// Create a frame-initial-style const value.
    pub fn create_const_value(&mut self, c: Const) -> ValueId {
        let cid = self.module.consts.push(c);
        let val = ValueId::new(self.module.values.len() as u32);
        self.module.values.push(Value {
            def: ValueDef::Const(cid),
            ty: Ty::Any,
        });
        val
    }
}

/// Every phi instruction (anywhere in the module's function block lists)
/// with zero entries — the N27 shape.
pub fn empty_phis(module: &Module) -> Vec<String> {
    let mut out = Vec::new();
    for (fi, func) in module.functions.iter().enumerate() {
        for &bb in &func.blocks {
            for &inst_id in &module.blocks[bb.index()].insts {
                if let Op::Phi { entries } = &module.insts[inst_id.index()].op {
                    if entries.is_empty() {
                        out.push(format!("FuncId({fi}) {bb} {inst_id}"));
                    }
                }
            }
        }
    }
    out
}

// ─── Minimal deterministic bytecode interpreter (v0.1 port) ─────────────────

/// What the machine observed when execution stopped.
#[allow(dead_code)] // variants are constructed only when a path executes them
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Halt {
    /// `Return`: accumulator value at the point of return.
    Return(i64),
    /// `Returnundefined`.
    ReturnUndefined,
    /// `Stobjbyvalue` (record-and-inspect): `obj` is the FIRST register
    /// operand's contents (the receiver), `key` the SECOND register
    /// operand's contents (the propKey), `value` the accumulator.
    StObjByValue { key: i64, obj: i64, value: i64 },
    /// `Copydataproperties` (record-and-inspect): `dst` is the operand
    /// register's contents (the target object), `src` the accumulator.
    CopyDataProperties { dst: i64, src: i64 },
    /// `Callrange` (record-and-inspect): `argc`/`start` are the recorded
    /// operands; the argument values are `regs[start .. start + argc]`.
    CallRange { argc: i64, start: u16 },
    /// `WideCallrange` (record-and-inspect): u16 argc, u8 start, no IC.
    WideCallRange { argc: i64, start: u16 },
    /// `Newobjrange` (record-and-inspect): argc INCLUDING the constructor,
    /// window start; window[0] = ctor.
    NewObjRange { argc: i64, start: u16 },
    /// `WideNewobjrange` (record-and-inspect): u16 argc including the
    /// constructor, u8 start, no IC.
    WideNewObjRange { argc: i64, start: u16 },
    /// `Suspendgenerator` (record-and-inspect): `genobj` the register,
    /// `value` the accumulator (the yield value).
    SuspendGenerator { genobj: i64, value: i64 },
    /// `Resumegenerator` (record-and-inspect): `genobj` is the acc.
    ResumeGenerator { genobj: i64 },
    /// `Getresumemode` (record-and-inspect): `genobj` is the acc.
    GetResumeMode { genobj: i64 },
    /// `ThrowIfsupernotcorrectcall` (record-and-stop): `value` the acc,
    /// `kind` the imm.
    ThrowIfSuperNotCorrectCall { kind: i64, value: i64 },
    /// `Definegettersetterbyvalue` (record-and-inspect): the four register
    /// operands' contents (obj, key, getter, setter).
    DefineGetterSetterByValue {
        /// Receiver object.
        obj: i64,
        /// Property key.
        key: i64,
        /// Getter closure.
        getter: i64,
        /// Setter closure.
        setter: i64,
    },
    /// `ThrowConstassignment` (record-and-stop): `name` is the register's
    /// contents (the variable name string VALUE).
    ThrowConstAssignment { name: i64 },
    /// `ThrowUndefinedifhole` (record-and-stop): `name` the first
    /// register's contents, `value` the second's.
    ThrowUndefinedIfHole { name: i64, value: i64 },
    /// `ThrowUndefinedifholewithname` (record-and-stop): `value` is the
    /// accumulator (the checked value).
    ThrowUndefinedIfHoleWithName { value: i64 },
    /// `Setobjectwithproto` (record-and-stop): `proto` the register's
    /// contents, `obj` the accumulator.
    SetObjectWithProto { proto: i64, obj: i64 },
    /// `Createobjectwithexcludedkeys` (record-and-inspect): key count,
    /// object register's contents, range start.
    CreateObjectWithExcludedKeys { argc: i64, obj: i64, start: u16 },
    /// `WideCreateobjectwithexcludedkeys` (record-and-inspect): u16 key
    /// count, u8 range start.
    WideCreateObjectWithExcludedKeys { argc: i64, obj: i64, start: u16 },
    /// `run_until` reached the stop pc WITHOUT executing the instruction
    /// there — models an exception thrown between two instructions.
    Stopped,
}

/// A tiny register machine: `HashMap<u16, i64>` registers plus one
/// accumulator. Missing registers read as 0.
pub struct Machine {
    /// The register file.
    pub regs: HashMap<u16, i64>,
    /// The accumulator.
    pub acc: i64,
}

/// Frame-initial value sentinels. The i64 machine has no tagged values,
/// so the two VM frame-initial states are modeled as distinct sentinels:
/// `UNDEFINED` (vreg slots at frame creation) and `HOLE` (acc at frame
/// creation).
#[allow(dead_code)] // used by the vreg-hole regressions
pub const UNDEFINED: i64 = i64::MIN;
#[allow(dead_code)]
pub const HOLE: i64 = i64::MIN + 1;
/// Sentinel for `createemptyobject` — the i64 machine has no objects.
#[allow(dead_code)]
pub const EMPTY_OBJECT: i64 = i64::MIN + 2;
/// Sentinel for `definefunc` — the i64 machine has no function objects;
/// the closure value only needs to be distinguishable from numbers.
#[allow(dead_code)]
pub const FUNCTION: i64 = i64::MIN + 3;

#[allow(dead_code)] // helpers are shared across several test binaries
impl Machine {
    /// A zeroed machine.
    pub fn new() -> Self {
        Self {
            regs: HashMap::new(),
            acc: 0,
        }
    }

    /// Builder: preset a register.
    pub fn with_reg(mut self, reg: u16, val: i64) -> Self {
        self.regs.insert(reg, val);
        self
    }

    /// Builder: preset the accumulator.
    pub fn with_acc(mut self, val: i64) -> Self {
        self.acc = val;
        self
    }

    /// Read a register (missing reads as 0).
    pub fn reg(&self, reg: u16) -> i64 {
        self.regs.get(&reg).copied().unwrap_or(0)
    }

    /// Execute `code` from index 0 until a terminator/record point.
    /// Panics on any opcode outside the supported subset.
    pub fn run(&mut self, code: &[Bytecode]) -> Halt {
        self.run_at(code, 0)
    }

    /// Execute `code` from `pc` until a terminator/record point.
    /// Used to simulate exception dispatch: the VM enters a catch handler
    /// at its `TryBlock` offset, not at pc 0.
    pub fn run_at(&mut self, code: &[Bytecode], pc: usize) -> Halt {
        self.exec(code, pc, None)
    }

    /// Execute `code` from `pc`, stopping WITHOUT executing the
    /// instruction at `stop_pc` (returns [`Halt::Stopped`]). Simulates an
    /// exception thrown between two instructions: run a try body up to
    /// the throw point, then enter the handler with `run_at`.
    pub fn run_until(&mut self, code: &[Bytecode], pc: usize, stop_pc: usize) -> Halt {
        self.exec(code, pc, Some(stop_pc))
    }

    fn exec(&mut self, code: &[Bytecode], pc: usize, stop_pc: Option<usize>) -> Halt {
        let mut pc = pc;
        loop {
            if Some(pc) == stop_pc {
                return Halt::Stopped;
            }
            let Some(bc) = code.get(pc) else {
                panic!("simulator: program counter {pc} escaped the code buffer")
            };
            match *bc {
                Bytecode::Lda(r) => {
                    self.acc = self.reg(r.0);
                    pc += 1;
                }
                Bytecode::Sta(r) => {
                    self.regs.insert(r.0, self.acc);
                    pc += 1;
                }
                // `mov v1:out, v2:in` — first operand is the destination.
                Bytecode::Mov(dst, src) => {
                    let val = self.reg(src.0);
                    self.regs.insert(dst.0, val);
                    pc += 1;
                }
                Bytecode::Ldai(imm) => {
                    self.acc = imm.0;
                    pc += 1;
                }
                Bytecode::Ldundefined => {
                    self.acc = UNDEFINED;
                    pc += 1;
                }
                Bytecode::Ldtrue => {
                    self.acc = 1;
                    pc += 1;
                }
                Bytecode::Ldfalse => {
                    self.acc = 0;
                    pc += 1;
                }
                Bytecode::Ldhole => {
                    self.acc = HOLE;
                    pc += 1;
                }
                Bytecode::Createemptyobject => {
                    self.acc = EMPTY_OBJECT;
                    pc += 1;
                }
                // `add2 imm, v0` — acc = acc + v0 (ic slot ignored).
                Bytecode::Add2(_, r) => {
                    self.acc += self.reg(r.0);
                    pc += 1;
                }
                // `sub2 imm, v0` — acc = acc - v0 (ic slot ignored).
                Bytecode::Sub2(_, r) => {
                    self.acc -= self.reg(r.0);
                    pc += 1;
                }
                // `greater imm, v0` — acc = (acc > v0) (ic slot ignored).
                Bytecode::Greater(_, r) => {
                    self.acc = i64::from(self.acc > self.reg(r.0));
                    pc += 1;
                }
                // `eq imm, v0` — acc = (acc == v0) (ic slot ignored).
                Bytecode::Eq(_, r) => {
                    self.acc = i64::from(self.acc == self.reg(r.0));
                    pc += 1;
                }
                // `istrue` — acc = ToBoolean(acc) (modeled as != 0).
                Bytecode::Istrue => {
                    self.acc = i64::from(self.acc != 0);
                    pc += 1;
                }
                Bytecode::Jmp(label) => {
                    pc = label.0 as usize;
                }
                Bytecode::Jnez(label) => {
                    if self.acc != 0 {
                        pc = label.0 as usize;
                    } else {
                        pc += 1;
                    }
                }
                // `jeq v0, label` — jump if acc == v0.
                Bytecode::Jeq(r, label) => {
                    if self.acc == self.reg(r.0) {
                        pc = label.0 as usize;
                    } else {
                        pc += 1;
                    }
                }
                Bytecode::Return => return Halt::Return(self.acc),
                Bytecode::Returnundefined => return Halt::ReturnUndefined,
                Bytecode::Stobjbyvalue(_, obj_r, key_r) => {
                    return Halt::StObjByValue {
                        key: self.reg(key_r.0),
                        obj: self.reg(obj_r.0),
                        value: self.acc,
                    };
                }
                // Side-effect-only stores the regressions use to pin
                // register-resident values.
                Bytecode::Stobjbyname(..) => {
                    pc += 1;
                }
                Bytecode::Stglobalvar(..) => {
                    pc += 1;
                }
                Bytecode::Copydataproperties(dst_r) => {
                    return Halt::CopyDataProperties {
                        dst: self.reg(dst_r.0),
                        src: self.acc,
                    };
                }
                // `definefunc imm, method_id, length` — acc = a fresh
                // closure (modeled as the FUNCTION sentinel; the machine
                // does not execute calls itself).
                Bytecode::Definefunc(..) => {
                    self.acc = FUNCTION;
                    pc += 1;
                }
                // Fixed-arity calls (record-and-inspect): the callee is
                // the acc; `start` is the first argument register (0 for
                // the no-argument form).
                Bytecode::Callarg0(_) => {
                    return Halt::CallRange { argc: 0, start: 0 };
                }
                Bytecode::Callarg1(_, a0) => {
                    return Halt::CallRange {
                        argc: 1,
                        start: a0.0,
                    };
                }
                Bytecode::Callargs2(_, a0, _) => {
                    return Halt::CallRange {
                        argc: 2,
                        start: a0.0,
                    };
                }
                Bytecode::Callargs3(_, a0, ..) => {
                    return Halt::CallRange {
                        argc: 3,
                        start: a0.0,
                    };
                }
                Bytecode::Callrange(_, argc, start) => {
                    return Halt::CallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                Bytecode::WideCallrange(argc, start) => {
                    return Halt::WideCallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                Bytecode::Newobjrange(_, argc, start) => {
                    return Halt::NewObjRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                Bytecode::WideNewobjrange(argc, start) => {
                    return Halt::WideNewObjRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                Bytecode::Suspendgenerator(gen_r) => {
                    return Halt::SuspendGenerator {
                        genobj: self.reg(gen_r.0),
                        value: self.acc,
                    };
                }
                Bytecode::Resumegenerator => {
                    return Halt::ResumeGenerator { genobj: self.acc };
                }
                Bytecode::Getresumemode => {
                    return Halt::GetResumeMode { genobj: self.acc };
                }
                Bytecode::ThrowIfsupernotcorrectcall(imm) => {
                    return Halt::ThrowIfSuperNotCorrectCall {
                        kind: imm.0,
                        value: self.acc,
                    };
                }
                Bytecode::Definegettersetterbyvalue(obj_r, key_r, get_r, set_r) => {
                    return Halt::DefineGetterSetterByValue {
                        obj: self.reg(obj_r.0),
                        key: self.reg(key_r.0),
                        getter: self.reg(get_r.0),
                        setter: self.reg(set_r.0),
                    };
                }
                Bytecode::ThrowConstassignment(name_r) => {
                    return Halt::ThrowConstAssignment {
                        name: self.reg(name_r.0),
                    };
                }
                Bytecode::ThrowUndefinedifhole(name_r, val_r) => {
                    return Halt::ThrowUndefinedIfHole {
                        name: self.reg(name_r.0),
                        value: self.reg(val_r.0),
                    };
                }
                Bytecode::ThrowUndefinedifholewithname(_) => {
                    return Halt::ThrowUndefinedIfHoleWithName { value: self.acc };
                }
                Bytecode::Setobjectwithproto(_, proto_r) => {
                    return Halt::SetObjectWithProto {
                        proto: self.reg(proto_r.0),
                        obj: self.acc,
                    };
                }
                Bytecode::Createobjectwithexcludedkeys(argc, obj_r, start) => {
                    return Halt::CreateObjectWithExcludedKeys {
                        argc: argc.0,
                        obj: self.reg(obj_r.0),
                        start: start.0,
                    };
                }
                Bytecode::WideCreateobjectwithexcludedkeys(argc, obj_r, start) => {
                    return Halt::WideCreateObjectWithExcludedKeys {
                        argc: argc.0,
                        obj: self.reg(obj_r.0),
                        start: start.0,
                    };
                }
                other => panic!("simulator: unsupported bytecode {other:?}"),
            }
        }
    }
}
