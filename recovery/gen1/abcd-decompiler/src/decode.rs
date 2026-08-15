use abcd_ir::instruction::Instruction;

/// Decode a raw bytecode byte slice into a list of instructions.
pub fn decode_method(code: &[u8]) -> Vec<Instruction> {
    let decoded = match abcd_isa::decode(code) {
        Ok(d) => d,
        Err(e) => {
            log::warn!("decode failed: {e}");
            return Vec::new();
        }
    };

    let total_len = code.len() as u32;
    let offsets: Vec<u32> = decoded.iter().map(|(_, off)| *off).collect();

    decoded
        .iter()
        .enumerate()
        .map(|(i, (bc, offset))| {
            let size = if i + 1 < offsets.len() {
                (offsets[i + 1] - offset) as u8
            } else {
                (total_len - offset) as u8
            };
            Instruction {
                offset: *offset,
                opcode: *bc,
                size,
            }
        })
        .collect()
}
