use abcd_ir::instruction::{Instruction, Operand};
use abcd_isa::OpcodeInfo;

/// Decode a raw bytecode byte slice into a list of instructions.
pub fn decode_method(code: &[u8]) -> Vec<Instruction> {
    let mut instructions = Vec::new();
    let mut offset = 0u32;

    while (offset as usize) < code.len() {
        let bytes = &code[offset as usize..];
        let Ok((opcode, info)) = abcd_isa::decode(bytes) else {
            // Unknown opcode - skip one byte
            log::warn!("Unknown opcode at offset {offset:#x}: {:#04x}", bytes[0]);
            offset += 1;
            continue;
        };

        let size = info.size() as u8;
        let operands = decode_operands(bytes, info);

        instructions.push(Instruction {
            offset,
            opcode,
            operands,
            size,
        });

        offset += size as u32;
    }

    instructions
}

fn decode_operands(bytes: &[u8], info: OpcodeInfo) -> Vec<Operand> {
    let mut operands = Vec::new();

    for part in info.operands() {
        let byte_offset = part.byte_offset();
        match part.kind() {
            abcd_isa::OperandKind::Reg => {
                let val = read_uint(
                    bytes,
                    byte_offset,
                    part.bit_width(),
                    part.bit_offset_in_byte(),
                );
                operands.push(Operand::Reg(val as u16));
            }
            abcd_isa::OperandKind::Imm => {
                if part.is_jump() {
                    let val = read_int(
                        bytes,
                        byte_offset,
                        part.bit_width(),
                        part.bit_offset_in_byte(),
                    );
                    operands.push(Operand::JumpOffset(val as i32));
                } else if part.is_float() {
                    let bits = read_uint(
                        bytes,
                        byte_offset,
                        part.bit_width(),
                        part.bit_offset_in_byte(),
                    );
                    operands.push(Operand::FloatImm(f64::from_bits(bits)));
                } else if part.bit_width() >= 32 {
                    // 32-bit+ immediates may be signed (e.g. ldai)
                    let val = read_int(
                        bytes,
                        byte_offset,
                        part.bit_width(),
                        part.bit_offset_in_byte(),
                    );
                    operands.push(Operand::Imm(val));
                } else {
                    // 4/8/16-bit immediates are unsigned (IC slots, counts, indices)
                    let val = read_uint(
                        bytes,
                        byte_offset,
                        part.bit_width(),
                        part.bit_offset_in_byte(),
                    );
                    operands.push(Operand::Imm(val as i64));
                }
            }
            abcd_isa::OperandKind::Id => {
                let val = read_uint(
                    bytes,
                    byte_offset,
                    part.bit_width(),
                    part.bit_offset_in_byte(),
                );
                operands.push(Operand::EntityId(val as u32));
            }
        }
    }

    operands
}

fn read_uint(bytes: &[u8], offset: usize, bit_width: usize, bit_offset_in_byte: usize) -> u64 {
    match bit_width {
        4 => {
            let byte = bytes.get(offset).copied().unwrap_or(0);
            // Extract the correct nibble based on bit_offset_in_byte
            ((byte >> bit_offset_in_byte) & 0x0f) as u64
        }
        8 => bytes.get(offset).copied().unwrap_or(0) as u64,
        16 => {
            let lo = bytes.get(offset).copied().unwrap_or(0) as u64;
            let hi = bytes.get(offset + 1).copied().unwrap_or(0) as u64;
            lo | (hi << 8)
        }
        32 => {
            let mut val = 0u64;
            for i in 0..4 {
                val |= (bytes.get(offset + i).copied().unwrap_or(0) as u64) << (i * 8);
            }
            val
        }
        64 => {
            let mut val = 0u64;
            for i in 0..8 {
                val |= (bytes.get(offset + i).copied().unwrap_or(0) as u64) << (i * 8);
            }
            val
        }
        _ => 0,
    }
}

fn read_int(bytes: &[u8], offset: usize, bit_width: usize, bit_offset_in_byte: usize) -> i64 {
    let val = read_uint(bytes, offset, bit_width, bit_offset_in_byte);
    // Sign-extend
    let shift = 64 - bit_width;
    ((val as i64) << shift) >> shift
}
