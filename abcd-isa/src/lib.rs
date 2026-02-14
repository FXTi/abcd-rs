//! ArkCompiler ISA definitions, auto-generated from `isa.yaml`.
//!
//! This crate provides opcode definitions, instruction formats, and decoding
//! functions for the ArkCompiler bytecode instruction set.

// The bitflags crate is used by generated code
pub use bitflags;

include!(concat!(env!("OUT_DIR"), "/generated.rs"));

#[cfg(test)]
mod tests {
    //! Tests migrated from arkcompiler runtime_core/libpandafile/tests/bytecode_instruction_tests.cpp
    //!
    //! The C++ tests verify operand extraction from raw bytecode. Here we verify that
    //! `decode_opcode` correctly identifies opcodes and that `OpcodeInfo` metadata
    //! (format, flags, operand descriptors) is consistent.

    use super::*;

    // --- Basic decode tests ---

    #[test]
    fn decode_ldundefined() {
        // opcode 0x00 is ldundefined in the ArkCompiler ISA
        let bytecode = [0x00u8];
        let result = decode_opcode(&bytecode);
        assert!(result.is_some(), "opcode 0x00 should decode");
        let (op, info) = result.unwrap();
        assert_eq!(op.mnemonic(), "ldundefined");
        assert_eq!(info.mnemonic, "ldundefined");
    }

    #[test]
    fn decode_empty_bytecode() {
        let bytecode: [u8; 0] = [];
        assert!(decode_opcode(&bytecode).is_none());
    }

    #[test]
    fn decode_prefixed_opcode() {
        // Prefix bytes are 0xfb..0xfe. Test that a prefixed instruction decodes.
        // callruntime.notifyconcurrentresult (prefix 0xfb, sub-opcode 0x00)
        let bytecode = [0xfbu8, 0x00];
        let result = decode_opcode(&bytecode);
        assert!(result.is_some(), "prefixed opcode 0xfb00 should decode");
        let (_, info) = result.unwrap();
        assert!(info.is_prefixed);
    }

    #[test]
    fn decode_prefixed_needs_two_bytes() {
        // Only one byte for a prefix — should fail
        let bytecode = [0xfbu8];
        assert!(decode_opcode(&bytecode).is_none());
    }

    // --- Format size tests (from bytecode_instruction_tests.cpp format parsing) ---

    #[test]
    fn format_sizes_are_positive() {
        // Every format should have a size >= 1
        for &(_, ref info) in OPCODE_TABLE {
            assert!(
                info.format.size() >= 1,
                "format {:?} has size 0",
                info.format
            );
        }
    }

    #[test]
    fn non_prefixed_opcodes_fit_in_u8() {
        for &(value, ref info) in OPCODE_TABLE {
            if !info.is_prefixed {
                assert!(
                    value <= 0xFF,
                    "non-prefixed opcode {} has value {:#x} > 0xFF",
                    info.mnemonic,
                    value
                );
            }
        }
    }

    #[test]
    fn prefixed_opcodes_have_high_byte() {
        for &(value, ref info) in OPCODE_TABLE {
            if info.is_prefixed {
                assert!(
                    value > 0xFF,
                    "prefixed opcode {} has value {:#x} <= 0xFF",
                    info.mnemonic,
                    value
                );
            }
        }
    }

    // --- Operand descriptor tests ---

    #[test]
    fn operand_byte_offsets_within_format() {
        for &(_, ref info) in OPCODE_TABLE {
            let fmt_size = info.format.size();
            for desc in info.operand_parts {
                let end = desc.byte_offset + (desc.bit_width + 7) / 8;
                assert!(
                    end <= fmt_size,
                    "operand in {} extends to byte {} but format size is {}",
                    info.mnemonic,
                    end,
                    fmt_size
                );
            }
        }
    }

    // --- Flag consistency tests ---

    #[test]
    fn jump_opcodes_have_jump_flag() {
        for &(_, ref info) in OPCODE_TABLE {
            if info.mnemonic.starts_with("jmp")
                || info.mnemonic.starts_with("jeqz")
                || info.mnemonic.starts_with("jnez")
                || info.mnemonic.starts_with("jstricteqz")
                || info.mnemonic.starts_with("jnstricteqz")
                || info.mnemonic.starts_with("jeqnull")
                || info.mnemonic.starts_with("jnenull")
                || info.mnemonic.starts_with("jundefined")
                || info.mnemonic.starts_with("jnundefined")
                || info.mnemonic.starts_with("jeq")
                || info.mnemonic.starts_with("jne")
                || info.mnemonic.starts_with("jstricteq")
                || info.mnemonic.starts_with("jnstricteq")
            {
                assert!(
                    info.flags.contains(OpcodeFlags::JUMP),
                    "{} should have JUMP flag",
                    info.mnemonic
                );
            }
        }
    }

    #[test]
    fn return_opcodes_have_return_flag() {
        for &(_, ref info) in OPCODE_TABLE {
            if info.mnemonic.starts_with("return") {
                assert!(
                    info.flags.contains(OpcodeFlags::RETURN),
                    "{} should have RETURN flag",
                    info.mnemonic
                );
            }
        }
    }

    #[test]
    fn throw_opcodes_have_throw_flag() {
        for &(_, ref info) in OPCODE_TABLE {
            if info.mnemonic.starts_with("throw") {
                assert!(
                    info.flags.contains(OpcodeFlags::THROW),
                    "{} should have THROW flag",
                    info.mnemonic
                );
            }
        }
    }

    // --- Specific instruction tests from bytecode_instruction_tests.cpp ---

    #[test]
    fn decode_ldai() {
        // ldai is a common instruction: opcode + imm32
        let info = lookup_opcode_by_mnemonic("ldai");
        assert!(info.is_some(), "ldai should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::ACC_WRITE));
    }

    #[test]
    fn decode_fldai() {
        // fldai loads a float immediate into accumulator
        let info = lookup_opcode_by_mnemonic("fldai");
        assert!(info.is_some(), "fldai should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::ACC_WRITE));
        assert!(info.flags.contains(OpcodeFlags::FLOAT));
    }

    #[test]
    fn decode_sta() {
        // sta stores accumulator to register
        let info = lookup_opcode_by_mnemonic("sta");
        assert!(info.is_some(), "sta should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::ACC_READ));
    }

    #[test]
    fn decode_lda() {
        // lda loads register to accumulator
        let info = lookup_opcode_by_mnemonic("lda");
        assert!(info.is_some(), "lda should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::ACC_WRITE));
    }

    #[test]
    fn decode_returnundefined() {
        let info = lookup_opcode_by_mnemonic("returnundefined");
        assert!(info.is_some(), "returnundefined should exist in ISA");
        let info = info.unwrap();
        assert!(info.flags.contains(OpcodeFlags::RETURN));
    }

    // --- Helper ---

    fn lookup_opcode_by_mnemonic(mnemonic: &str) -> Option<&'static OpcodeInfo> {
        OPCODE_TABLE
            .iter()
            .find(|(_, info)| info.mnemonic == mnemonic)
            .map(|(_, info)| info)
    }
}
