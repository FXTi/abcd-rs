use abcd_isa::Bytecode;

/// A single decoded bytecode instruction.
#[derive(Debug, Clone)]
pub struct Instruction {
    /// Byte offset within the method's code.
    pub offset: u32,
    /// The decoded bytecode instruction.
    pub opcode: Bytecode,
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
