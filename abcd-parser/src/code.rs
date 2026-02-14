use crate::error::ParseError;
use crate::leb128::decode_uleb128;

/// Parsed try block from a method's code.
#[derive(Debug, Clone)]
pub struct TryBlock {
    pub start_pc: u32,
    pub length: u32,
    pub catch_blocks: Vec<CatchBlock>,
}

/// Parsed catch block.
#[derive(Debug, Clone)]
pub struct CatchBlock {
    /// Type index + 1 (0 = catch-all).
    pub type_idx: u32,
    /// PC of the handler.
    pub handler_pc: u32,
    /// Handler code size.
    pub code_size: u32,
}

/// Parsed code section of a method.
#[derive(Debug, Clone)]
pub struct CodeData {
    /// Number of virtual registers (excluding arguments).
    pub num_vregs: u32,
    /// Number of arguments.
    pub num_args: u32,
    /// Raw bytecode instructions.
    pub instructions: Vec<u8>,
    /// Try blocks.
    pub try_blocks: Vec<TryBlock>,
}

impl CodeData {
    /// Parse a Code structure at the given offset.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        let (num_vregs, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let (num_args, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let (code_size, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let (tries_size, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        // Read instructions
        let insn_end = pos + code_size as usize;
        if insn_end > data.len() {
            return Err(ParseError::OffsetOutOfBounds(insn_end, data.len()));
        }
        let instructions = data[pos..insn_end].to_vec();
        pos = insn_end;

        // Read try blocks
        let mut try_blocks = Vec::with_capacity(tries_size as usize);
        for _ in 0..tries_size {
            let (start_pc, consumed) = decode_uleb128(data, pos)?;
            pos += consumed;
            let (length, consumed) = decode_uleb128(data, pos)?;
            pos += consumed;
            let (num_catches, consumed) = decode_uleb128(data, pos)?;
            pos += consumed;

            let mut catch_blocks = Vec::with_capacity(num_catches as usize);
            for _ in 0..num_catches {
                let (type_idx, consumed) = decode_uleb128(data, pos)?;
                pos += consumed;
                let (handler_pc, consumed) = decode_uleb128(data, pos)?;
                pos += consumed;
                let (code_size, consumed) = decode_uleb128(data, pos)?;
                pos += consumed;

                catch_blocks.push(CatchBlock {
                    type_idx: type_idx as u32,
                    handler_pc: handler_pc as u32,
                    code_size: code_size as u32,
                });
            }

            try_blocks.push(TryBlock {
                start_pc: start_pc as u32,
                length: length as u32,
                catch_blocks,
            });
        }

        Ok(Self {
            num_vregs: num_vregs as u32,
            num_args: num_args as u32,
            instructions,
            try_blocks,
        })
    }
}
