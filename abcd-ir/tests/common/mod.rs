//! Minimal deterministic bytecode interpreter shared by the lowering
//! regression tests.
//!
//! It supports only the opcodes the crafted sequences use
//! (`Lda`/`Sta`/`Mov`/`Ldai`/`Add2`/`Sub2`/`Greater`/`Eq`/`Istrue`/`Jmp`/
//! `Jnez`/`Jeq`/`Return`/`Returnundefined`, no-op `Stobjbyname`, plus
//! record-and-stop for `Stobjbyvalue`). Labels in `layout` output are
//! already resolved to absolute instruction indices by `resolve_labels`,
//! so jumps use the label operand directly as a program counter.

use std::collections::HashMap;

use abcd_isa::Bytecode;

/// What the machine observed when execution stopped.
#[allow(dead_code)] // variants are constructed only when a path executes them
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Halt {
    /// `Return`: accumulator value at the point of return.
    Return(i64),
    /// `Returnundefined`.
    ReturnUndefined,
    /// `Stobjbyvalue` (record-and-inspect): `key` is the accumulator
    /// (the ByValue key), `obj`/`value` are the operand register contents.
    StObjByValue { key: i64, obj: i64, value: i64 },
    /// `Copydataproperties` (record-and-inspect): `dst` is the operand
    /// register's contents (the target object), `src` the accumulator
    /// (the source object) — vendor `copydataproperties v:in:top,
    /// acc: inout:top`.
    CopyDataProperties { dst: i64, src: i64 },
    /// `Callrange` (record-and-inspect): vendor `callrange imm1:u8, imm2:u8,
    /// v:in:top` (isa.yaml ~:1082) — imm1 is the IC slot (ignored), imm2 the
    /// argument count, v the START of the consecutive argument register
    /// window. `argc`/`start` are the recorded operands; the argument
    /// values are `regs[start .. start + argc]` at halt time.
    CallRange { argc: i64, start: u16 },
    /// `WideCallrange` (record-and-inspect): vendor `wide.callrange imm:u16,
    /// v:in:top` (isa.yaml ~:1087) — imm is the u16 argument count, v the
    /// u8 window start; NO IC slot operand on the wide form.
    WideCallRange { argc: i64, start: u16 },
}

/// A tiny register machine: `HashMap<u16, i64>` registers plus one
/// accumulator. Missing registers read as 0.
pub struct Machine {
    pub regs: HashMap<u16, i64>,
    pub acc: i64,
}

#[allow(dead_code)] // helpers are shared across several test binaries
impl Machine {
    pub fn new() -> Self {
        Self {
            regs: HashMap::new(),
            acc: 0,
        }
    }

    pub fn with_reg(mut self, reg: u16, val: i64) -> Self {
        self.regs.insert(reg, val);
        self
    }

    pub fn with_acc(mut self, val: i64) -> Self {
        self.acc = val;
        self
    }

    pub fn reg(&self, reg: u16) -> i64 {
        self.regs.get(&reg).copied().unwrap_or(0)
    }

    /// Execute `code` from index 0 until a terminator/`Stobjbyvalue`.
    /// Panics on any opcode outside the supported subset.
    pub fn run(&mut self, code: &[Bytecode]) -> Halt {
        let mut pc = 0usize;
        loop {
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
                // `add2 imm:u8, v:in:top` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 590):
                // acc = acc + v0 (ic slot operand ignored).
                Bytecode::Add2(_, r) => {
                    self.acc += self.reg(r.0);
                    pc += 1;
                }
                // `sub2 imm, v0` — acc = acc - v0 (ic slot operand ignored).
                Bytecode::Sub2(_, r) => {
                    self.acc -= self.reg(r.0);
                    pc += 1;
                }
                // `greater imm, v0` — acc = (acc > v0) (ic slot operand ignored).
                Bytecode::Greater(_, r) => {
                    self.acc = i64::from(self.acc > self.reg(r.0));
                    pc += 1;
                }
                // `eq imm:u8, v:in:top` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 615):
                // acc = (acc == v0) (ic slot operand ignored).
                Bytecode::Eq(_, r) => {
                    self.acc = i64::from(self.acc == self.reg(r.0));
                    pc += 1;
                }
                // `istrue` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 761):
                // acc = ToBoolean(acc); the machine's i64 values model
                // truthiness as != 0.
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
                // `jeq v:in:top, imm:i16` with `acc: in:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 1746):
                // jump if acc == v0.
                Bytecode::Jeq(r, label) => {
                    if self.acc == self.reg(r.0) {
                        pc = label.0 as usize;
                    } else {
                        pc += 1;
                    }
                }
                Bytecode::Return => return Halt::Return(self.acc),
                Bytecode::Returnundefined => return Halt::ReturnUndefined,
                Bytecode::Stobjbyvalue(_, obj_r, val_r) => {
                    return Halt::StObjByValue {
                        key: self.acc,
                        obj: self.reg(obj_r.0),
                        value: self.reg(val_r.0),
                    };
                }
                // Store to a named property: a side effect the lowering
                // regressions only use to pin register-resident values.
                Bytecode::Stobjbyname(..) => {
                    pc += 1;
                }
                Bytecode::Copydataproperties(dst_r) => {
                    return Halt::CopyDataProperties {
                        dst: self.reg(dst_r.0),
                        src: self.acc,
                    };
                }
                // `callrange imm1:u8, imm2:u8, v:in:top` — record imm2 (argc)
                // and v (window start); the IC slot imm1 is ignored.
                Bytecode::Callrange(_, argc, start) => {
                    return Halt::CallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                // `wide.callrange imm:u16, v:in:top` — u16 argc, u8 start,
                // no IC slot.
                Bytecode::WideCallrange(argc, start) => {
                    return Halt::WideCallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                other => panic!("simulator: unsupported bytecode {other:?}"),
            }
        }
    }
}
