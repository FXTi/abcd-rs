use abcd_isa::Opcode;

/// A decoded operand from a bytecode instruction.
#[derive(Debug, Clone)]
pub enum Operand {
    /// Virtual register index.
    Reg(u16),
    /// Signed immediate value.
    Imm(i64),
    /// Float immediate value.
    FloatImm(f64),
    /// Entity ID (resolved from 16-bit index): string, method, literalarray, etc.
    EntityId(u32),
    /// Relative jump offset in bytes.
    JumpOffset(i32),
}

/// A single decoded bytecode instruction with resolved operands.
#[derive(Debug, Clone)]
pub struct Instruction {
    /// Byte offset within the method's code.
    pub offset: u32,
    /// The opcode.
    pub opcode: Opcode,
    /// Decoded operands.
    pub operands: Vec<Operand>,
    /// Total instruction size in bytes.
    pub size: u8,
}

/// Try-block metadata from the code section.
#[derive(Debug, Clone)]
pub struct TryBlockInfo {
    pub start_pc: u32,
    pub length: u32,
    pub catch_blocks: Vec<CatchBlockInfo>,
}

/// Catch-block metadata.
#[derive(Debug, Clone)]
pub struct CatchBlockInfo {
    pub type_idx: u32,
    pub handler_pc: u32,
    pub code_size: u32,
}
