//! Debug info extraction for ABC files.
//!
//! Reference: arkcompiler/runtime_core/static_core/libarkfile/debug_data_accessor.h
//!            arkcompiler/runtime_core/static_core/libarkfile/debug_info_extractor.h
//!
//! Binary layout:
//! ```text
//! DebugInfo {
//!     line_start:              uleb128
//!     num_parameters:          uleb128
//!     parameters:              [uleb128; num_parameters]  // string offsets (0 = no name)
//!     constant_pool_size:      uleb128
//!     constant_pool:           [u8; constant_pool_size]
//!     line_number_program_idx: uleb128
//! }
//! ```

use crate::error::ParseError;
use crate::leb128::{decode_sleb128, decode_uleb128};
use crate::string_table::read_string;

/// Line number program opcodes.
const LNP_END_SEQUENCE: u8 = 0x00;
const LNP_ADVANCE_PC: u8 = 0x01;
const LNP_ADVANCE_LINE: u8 = 0x02;
const LNP_START_LOCAL: u8 = 0x03;
const LNP_START_LOCAL_EXTENDED: u8 = 0x04;
const LNP_END_LOCAL: u8 = 0x05;
const LNP_RESTART_LOCAL: u8 = 0x06;
const LNP_SET_PROLOGUE_END: u8 = 0x07;
const LNP_SET_EPILOGUE_BEGIN: u8 = 0x08;
const LNP_SET_FILE: u8 = 0x09;
const LNP_SET_SOURCE_CODE: u8 = 0x0a;
const LNP_SET_COLUMN: u8 = 0x0b;

/// First special opcode value.
const OPCODE_BASE: u8 = 0x0c;
/// Line base for special opcode decoding.
const LINE_BASE: i32 = -4;
/// Line range for special opcode decoding.
const LINE_RANGE: i32 = 15;

/// A line number table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineEntry {
    /// Bytecode offset.
    pub offset: u32,
    /// Source line number.
    pub line: u32,
}

/// A column number table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnEntry {
    /// Bytecode offset.
    pub offset: u32,
    /// Source column number.
    pub column: u32,
}

/// A local variable scope entry.
#[derive(Debug, Clone)]
pub struct LocalVariableInfo {
    /// Variable name.
    pub name: String,
    /// Type descriptor string.
    pub type_name: String,
    /// Type signature (for generics, empty if not present).
    pub type_signature: String,
    /// Register number (-1 for accumulator).
    pub reg_number: i32,
    /// Bytecode offset where variable comes into scope.
    pub start_offset: u32,
    /// Bytecode offset where variable goes out of scope.
    pub end_offset: u32,
}

/// Parsed debug info for a method.
#[derive(Debug, Clone)]
pub struct DebugInfo {
    /// Initial line number.
    pub line_start: u32,
    /// Parameter names (empty string if unnamed).
    pub parameters: Vec<String>,
    /// Constant pool bytes.
    pub constant_pool: Vec<u8>,
    /// Line number program index (offset into LNP table).
    pub line_number_program_idx: u32,
}

impl DebugInfo {
    /// Parse debug info at the given offset.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        let (line_start, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let (num_params, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let mut parameters = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            let (str_off, consumed) = decode_uleb128(data, pos)?;
            pos += consumed;
            if str_off == 0 {
                parameters.push(String::new());
            } else {
                parameters.push(read_string(data, str_off as usize).unwrap_or_default());
            }
        }

        let (cp_size, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let cp_end = pos + cp_size as usize;
        if cp_end > data.len() {
            return Err(ParseError::OffsetOutOfBounds(cp_end, data.len()));
        }
        let constant_pool = data[pos..cp_end].to_vec();
        pos = cp_end;

        let (lnp_idx, _consumed) = decode_uleb128(data, pos)?;

        Ok(Self {
            line_start: line_start as u32,
            parameters,
            constant_pool,
            line_number_program_idx: lnp_idx as u32,
        })
    }
}

/// Execute a line number program and extract tables.
///
/// `lnp_data` is the raw bytes of the line number program.
/// `constant_pool` is the constant pool from the DebugInfo.
/// `file_data` is the full ABC file data (for resolving strings).
/// `line_start` is the initial line number.
/// `code_size` is the total bytecode size (for END_LOCAL default end offset).
pub fn execute_line_program(
    lnp_data: &[u8],
    constant_pool: &[u8],
    file_data: &[u8],
    line_start: u32,
    code_size: u32,
) -> LineProgramResult {
    let mut state = LnpState {
        address: 0,
        line: line_start as i64,
        column: 0,
        cp_pos: 0,
    };

    let mut result = LineProgramResult {
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_variables: Vec::new(),
    };

    // Track active locals: reg -> (name, type, signature, start_offset)
    let mut active_locals: std::collections::HashMap<i32, PendingLocal> =
        std::collections::HashMap::new();

    let mut pos = 0usize;
    while pos < lnp_data.len() {
        let opcode = lnp_data[pos];
        pos += 1;

        match opcode {
            LNP_END_SEQUENCE => {
                // Close all remaining locals
                for (_, local) in active_locals.drain() {
                    result.local_variables.push(LocalVariableInfo {
                        name: local.name,
                        type_name: local.type_name,
                        type_signature: local.type_signature,
                        reg_number: local.reg_number,
                        start_offset: local.start_offset,
                        end_offset: code_size,
                    });
                }
                break;
            }
            LNP_ADVANCE_PC => {
                let val = read_cp_uleb128(constant_pool, &mut state.cp_pos);
                state.address += val;
            }
            LNP_ADVANCE_LINE => {
                let val = read_cp_sleb128(constant_pool, &mut state.cp_pos);
                state.line += val as i64;
            }
            LNP_START_LOCAL => {
                let (reg, consumed) = decode_sleb128_at(lnp_data, pos);
                pos += consumed;
                let name_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);
                let type_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);

                // Close previous local in same register if any
                if let Some(prev) = active_locals.remove(&(reg as i32)) {
                    result.local_variables.push(LocalVariableInfo {
                        name: prev.name,
                        type_name: prev.type_name,
                        type_signature: prev.type_signature,
                        reg_number: prev.reg_number,
                        start_offset: prev.start_offset,
                        end_offset: state.address,
                    });
                }

                let name = if name_off > 0 {
                    read_string(file_data, name_off as usize).unwrap_or_default()
                } else {
                    String::new()
                };
                let type_name = if type_off > 0 {
                    read_string(file_data, type_off as usize).unwrap_or_default()
                } else {
                    String::new()
                };

                active_locals.insert(
                    reg as i32,
                    PendingLocal {
                        name,
                        type_name,
                        type_signature: String::new(),
                        reg_number: reg as i32,
                        start_offset: state.address,
                    },
                );
            }
            LNP_START_LOCAL_EXTENDED => {
                let (reg, consumed) = decode_sleb128_at(lnp_data, pos);
                pos += consumed;
                let name_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);
                let type_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);
                let sig_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);

                if let Some(prev) = active_locals.remove(&(reg as i32)) {
                    result.local_variables.push(LocalVariableInfo {
                        name: prev.name,
                        type_name: prev.type_name,
                        type_signature: prev.type_signature,
                        reg_number: prev.reg_number,
                        start_offset: prev.start_offset,
                        end_offset: state.address,
                    });
                }

                let name = if name_off > 0 {
                    read_string(file_data, name_off as usize).unwrap_or_default()
                } else {
                    String::new()
                };
                let type_name = if type_off > 0 {
                    read_string(file_data, type_off as usize).unwrap_or_default()
                } else {
                    String::new()
                };
                let type_signature = if sig_off > 0 {
                    read_string(file_data, sig_off as usize).unwrap_or_default()
                } else {
                    String::new()
                };

                active_locals.insert(
                    reg as i32,
                    PendingLocal {
                        name,
                        type_name,
                        type_signature,
                        reg_number: reg as i32,
                        start_offset: state.address,
                    },
                );
            }
            LNP_END_LOCAL => {
                let (reg, consumed) = decode_sleb128_at(lnp_data, pos);
                pos += consumed;
                if let Some(local) = active_locals.remove(&(reg as i32)) {
                    result.local_variables.push(LocalVariableInfo {
                        name: local.name,
                        type_name: local.type_name,
                        type_signature: local.type_signature,
                        reg_number: local.reg_number,
                        start_offset: local.start_offset,
                        end_offset: state.address,
                    });
                }
            }
            LNP_RESTART_LOCAL => {
                let (_reg, consumed) = decode_sleb128_at(lnp_data, pos);
                pos += consumed;
                // Re-introduce a previously ended local — simplified: skip
            }
            LNP_SET_PROLOGUE_END | LNP_SET_EPILOGUE_BEGIN => {}
            LNP_SET_FILE => {
                let _file_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);
            }
            LNP_SET_SOURCE_CODE => {
                let _src_off = read_cp_uleb128(constant_pool, &mut state.cp_pos);
            }
            LNP_SET_COLUMN => {
                let col = read_cp_uleb128(constant_pool, &mut state.cp_pos);
                state.column = col;
                result.column_table.push(ColumnEntry {
                    offset: state.address,
                    column: state.column,
                });
            }
            special if special >= OPCODE_BASE => {
                // Special opcode: encodes both PC and line increment
                let adjusted = (special - OPCODE_BASE) as i32;
                let pc_delta = adjusted / LINE_RANGE;
                let line_delta = (adjusted % LINE_RANGE) + LINE_BASE;
                state.address += pc_delta as u32;
                state.line += line_delta as i64;
                result.line_table.push(LineEntry {
                    offset: state.address,
                    line: state.line as u32,
                });
            }
            _ => {
                // Unknown opcode — skip
            }
        }
    }

    result
}

/// Result of executing a line number program.
#[derive(Debug, Clone)]
pub struct LineProgramResult {
    pub line_table: Vec<LineEntry>,
    pub column_table: Vec<ColumnEntry>,
    pub local_variables: Vec<LocalVariableInfo>,
}

struct LnpState {
    address: u32,
    line: i64,
    column: u32,
    cp_pos: usize,
}

struct PendingLocal {
    name: String,
    type_name: String,
    type_signature: String,
    reg_number: i32,
    start_offset: u32,
}

/// Read a uleb128 from the constant pool, advancing cp_pos.
fn read_cp_uleb128(cp: &[u8], cp_pos: &mut usize) -> u32 {
    if *cp_pos >= cp.len() {
        return 0;
    }
    match decode_uleb128(cp, *cp_pos) {
        Ok((val, consumed)) => {
            *cp_pos += consumed;
            val as u32
        }
        Err(_) => 0,
    }
}

/// Read a sleb128 from the constant pool, advancing cp_pos.
fn read_cp_sleb128(cp: &[u8], cp_pos: &mut usize) -> i32 {
    if *cp_pos >= cp.len() {
        return 0;
    }
    match decode_sleb128(cp, *cp_pos) {
        Ok((val, consumed)) => {
            *cp_pos += consumed;
            val as i32
        }
        Err(_) => 0,
    }
}

/// Decode sleb128 at a position in a byte slice. Returns (value, bytes_consumed).
fn decode_sleb128_at(data: &[u8], pos: usize) -> (i64, usize) {
    match decode_sleb128(data, pos) {
        Ok((val, consumed)) => (val, consumed),
        Err(_) => (0, 1),
    }
}

#[cfg(test)]
mod tests {
    //! Tests migrated from:
    //! - runtime_core/libpandafile/tests/file_items_test.cpp (EmitSpecialOpcode)
    //! - runtime_core/libpandafile/tests/file_item_container_test.cpp (TestDebugInfo)
    //! - runtime_core/static_core/libarkfile/tests/debug_info_extractor_test.cpp

    use super::*;

    #[test]
    fn parse_debug_info_basic() {
        let data = vec![
            10, // line_start (uleb128)
            2,  // num_params (uleb128)
            0,  // param 0 string offset = 0 (unnamed)
            0,  // param 1 string offset = 0 (unnamed)
            0,  // constant_pool_size = 0
            5,  // line_number_program_idx = 5
        ];
        let info = DebugInfo::parse(&data, 0).unwrap();
        assert_eq!(info.line_start, 10);
        assert_eq!(info.parameters.len(), 2);
        assert_eq!(info.parameters[0], "");
        assert_eq!(info.parameters[1], "");
        assert_eq!(info.constant_pool.len(), 0);
        assert_eq!(info.line_number_program_idx, 5);
    }

    /// Migrated from: runtime_core/libpandafile/tests/file_items_test.cpp
    /// Tests special opcode encoding formula:
    ///   opcode = (line_inc - LINE_BASE) + (pc_inc * LINE_RANGE) + OPCODE_BASE
    /// With LINE_BASE=-4, LINE_RANGE=15, OPCODE_BASE=12
    #[test]
    fn special_opcode_encoding_from_file_items_test() {
        // (pc_inc=1, line_inc=-4): ((-4)-(-4)) + (1*15) + 12 = 27 = 0x1b
        let opcode1: u8 = ((-4i32 - LINE_BASE) + (1 * LINE_RANGE) + OPCODE_BASE as i32) as u8;
        assert_eq!(opcode1, 0x1b);

        // (pc_inc=2, line_inc=10): ((10)-(-4)) + (2*15) + 12 = 56 = 0x38
        let opcode2: u8 = ((10i32 - LINE_BASE) + (2 * LINE_RANGE) + OPCODE_BASE as i32) as u8;
        assert_eq!(opcode2, 0x38);

        // Verify decoding matches encoding
        let adj1 = (opcode1 - OPCODE_BASE) as i32;
        assert_eq!(adj1 / LINE_RANGE, 1); // pc_inc
        assert_eq!((adj1 % LINE_RANGE) + LINE_BASE, -4); // line_inc

        let adj2 = (opcode2 - OPCODE_BASE) as i32;
        assert_eq!(adj2 / LINE_RANGE, 2); // pc_inc
        assert_eq!((adj2 % LINE_RANGE) + LINE_BASE, 10); // line_inc
    }

    /// Migrated from: runtime_core/libpandafile/tests/file_items_test.cpp
    /// LINE_MAX_INC = LINE_RANGE + LINE_BASE - 1 = 15 + (-4) - 1 = 10
    /// LINE_MIN_INC = LINE_BASE = -4
    #[test]
    fn special_opcode_line_range_bounds() {
        let line_max_inc = LINE_RANGE + LINE_BASE - 1; // 10
        let line_min_inc = LINE_BASE; // -4
        assert_eq!(line_max_inc, 10);
        assert_eq!(line_min_inc, -4);

        // Verify min/max produce valid opcodes
        let min_opcode = ((line_min_inc - LINE_BASE) + (0 * LINE_RANGE) + OPCODE_BASE as i32) as u8;
        assert_eq!(min_opcode, OPCODE_BASE); // 0x0c

        let max_opcode = ((line_max_inc - LINE_BASE) + (0 * LINE_RANGE) + OPCODE_BASE as i32) as u8;
        assert_eq!(max_opcode, OPCODE_BASE + 14); // 0x1a
    }

    #[test]
    fn execute_end_sequence_only() {
        let lnp = vec![LNP_END_SEQUENCE];
        let result = execute_line_program(&lnp, &[], &[], 1, 100);
        assert!(result.line_table.is_empty());
        assert!(result.column_table.is_empty());
        assert!(result.local_variables.is_empty());
    }

    /// Migrated from: runtime_core/libpandafile/tests/file_item_container_test.cpp (TestDebugInfo)
    /// Tests: SET_SOURCE_CODE, SET_FILE, SET_PROLOGUE_END, ADVANCE_PC(10),
    ///        ADVANCE_LINE(-5), SET_EPILOGUE_BEGIN, END_SEQUENCE
    /// Starting line = 5
    #[test]
    fn execute_container_test_debug_info() {
        // Constant pool: [source_code_off(uleb128), file_off(uleb128), pc_advance=10(uleb128), line_advance=-5(sleb128)]
        let cp = vec![
            50,   // source_code offset (uleb128) — arbitrary, just consumed
            60,   // file offset (uleb128) — arbitrary, just consumed
            10,   // pc advance = 10 (uleb128)
            0x7b, // line advance = -5 (sleb128: 0x7b = -5)
        ];
        let lnp = vec![
            LNP_SET_SOURCE_CODE,    // 0x0a — reads from CP
            LNP_SET_FILE,           // 0x09 — reads from CP
            LNP_SET_PROLOGUE_END,   // 0x07 — no args
            LNP_ADVANCE_PC,         // 0x01 — reads pc=10 from CP
            LNP_ADVANCE_LINE,       // 0x02 — reads line=-5 from CP
            LNP_SET_EPILOGUE_BEGIN, // 0x08 — no args
            LNP_END_SEQUENCE,       // 0x00
        ];
        let result = execute_line_program(&lnp, &cp, &[], 5, 100);
        // No special opcodes emitted, so no line table entries
        assert!(result.line_table.is_empty());
        // State after execution: address=10, line=0 (5 + (-5))
    }

    /// Tests special opcodes produce correct line table entries
    #[test]
    fn execute_special_opcodes_from_file_items() {
        // Encode (pc_inc=1, line_inc=-4) and (pc_inc=2, line_inc=10)
        let opcode1 = 0x1bu8; // (pc=1, line=-4)
        let opcode2 = 0x38u8; // (pc=2, line=10)
        let lnp = vec![opcode1, opcode2, LNP_END_SEQUENCE];
        let result = execute_line_program(&lnp, &[], &[], 10, 100);
        assert_eq!(result.line_table.len(), 2);
        // After opcode1: address=1, line=10+(-4)=6
        assert_eq!(result.line_table[0], LineEntry { offset: 1, line: 6 });
        // After opcode2: address=1+2=3, line=6+10=16
        assert_eq!(
            result.line_table[1],
            LineEntry {
                offset: 3,
                line: 16
            }
        );
    }

    /// Migrated from: runtime_core/static_core/libarkfile/tests/debug_info_extractor_test.cpp
    /// Tests ADVANCE_PC + ADVANCE_LINE + special opcode sequence
    #[test]
    fn execute_advance_pc_and_line() {
        // CP: pc_advance=1(uleb128), line_advance=1(sleb128)
        let cp = vec![1, 1];
        // LNP: ADVANCE_PC, ADVANCE_LINE, special(0,0)=0x10, END
        let lnp = vec![LNP_ADVANCE_PC, LNP_ADVANCE_LINE, 0x10, LNP_END_SEQUENCE];
        let result = execute_line_program(&lnp, &cp, &[], 3, 100);
        assert_eq!(result.line_table.len(), 1);
        // After ADVANCE_PC: address=1, After ADVANCE_LINE: line=4, After 0x10: pc_delta=0, line_delta=0
        assert_eq!(result.line_table[0], LineEntry { offset: 1, line: 4 });
    }

    /// Migrated from: runtime_core/static_core/libarkfile/tests/debug_info_extractor_test.cpp
    /// Tests SET_COLUMN opcode
    #[test]
    fn execute_column_tracking() {
        // CP: col=7, col=8, col=9
        let cp = vec![7, 8, 9];
        let lnp = vec![
            LNP_SET_COLUMN, // col=7
            0x10,           // special opcode (pc=0, line=0)
            LNP_SET_COLUMN, // col=8
            0x20,           // special opcode (pc=1, line=1) → (1-(-4))+(1*15)+12=32=0x20
            LNP_SET_COLUMN, // col=9
            LNP_END_SEQUENCE,
        ];
        let result = execute_line_program(&lnp, &cp, &[], 3, 100);
        assert_eq!(result.column_table.len(), 3);
        assert_eq!(
            result.column_table[0],
            ColumnEntry {
                offset: 0,
                column: 7
            }
        );
        assert_eq!(
            result.column_table[1],
            ColumnEntry {
                offset: 0,
                column: 8
            }
        );
        assert_eq!(
            result.column_table[2],
            ColumnEntry {
                offset: 1,
                column: 9
            }
        );
    }

    /// Migrated from: runtime_core/static_core/libarkfile/tests/debug_info_extractor_test.cpp
    /// Tests START_LOCAL and END_LOCAL for local variable tracking.
    /// Simulates the `foo` method test: 3 locals in registers 1, 2, 3
    #[test]
    fn execute_local_variable_tracking() {
        // File data with strings for variable names and types
        let mut file_data = vec![0u8; 200];
        // "local_0" at offset 10
        file_data[10] = 7;
        file_data[11..18].copy_from_slice(b"local_0");
        file_data[18] = 0;
        // "local_1" at offset 30
        file_data[30] = 7;
        file_data[31..38].copy_from_slice(b"local_1");
        file_data[38] = 0;
        // "local_2" at offset 50
        file_data[50] = 7;
        file_data[51..58].copy_from_slice(b"local_2");
        file_data[58] = 0;
        // "I" (type) at offset 70
        file_data[70] = 1;
        file_data[71] = b'I';
        file_data[72] = 0;
        // "type_i32" at offset 80
        file_data[80] = 8;
        file_data[81..89].copy_from_slice(b"type_i32");
        file_data[89] = 0;

        // Constant pool: name_off and type_off for each START_LOCAL
        // START_LOCAL reg=1: name=10, type=70
        // START_LOCAL_EXTENDED reg=2: name=30, type=70, sig=80
        // START_LOCAL reg=3: name=50, type=70
        let cp = vec![
            10, 70, // local_0: name_off=10, type_off=70
            30, 70, 80, // local_1: name_off=30, type_off=70, sig_off=80
            50, 70, // local_2: name_off=50, type_off=70
        ];

        let lnp = vec![
            LNP_START_LOCAL,
            1,    // reg=1 (sleb128)
            0x20, // special opcode: pc_inc=1, line_inc=1
            LNP_START_LOCAL_EXTENDED,
            2, // reg=2 (sleb128)
            LNP_END_LOCAL,
            1,    // reg=1 ends here (address=1)
            0x20, // special opcode: pc_inc=1, line_inc=1 → address=2
            LNP_START_LOCAL,
            3, // reg=3 (sleb128)
            LNP_END_SEQUENCE,
        ];

        let result = execute_line_program(&lnp, &cp, &file_data, 3, 10);

        // Should have 3 local variables
        assert_eq!(result.local_variables.len(), 3);

        // Sort by reg_number for deterministic order
        let mut vars = result.local_variables;
        vars.sort_by_key(|v| v.reg_number);

        // reg=1: local_0, type=I, start=0, end=1 (END_LOCAL at address=1)
        assert_eq!(vars[0].name, "local_0");
        assert_eq!(vars[0].type_name, "I");
        assert_eq!(vars[0].reg_number, 1);
        assert_eq!(vars[0].start_offset, 0);
        assert_eq!(vars[0].end_offset, 1);

        // reg=2: local_1, type=I, sig=type_i32, start=1, end=10 (code_size, never END_LOCAL'd)
        assert_eq!(vars[1].name, "local_1");
        assert_eq!(vars[1].type_name, "I");
        assert_eq!(vars[1].type_signature, "type_i32");
        assert_eq!(vars[1].reg_number, 2);
        assert_eq!(vars[1].start_offset, 1);
        assert_eq!(vars[1].end_offset, 10); // code_size

        // reg=3: local_2, type=I, start=2, end=10 (code_size, never END_LOCAL'd)
        assert_eq!(vars[2].name, "local_2");
        assert_eq!(vars[2].type_name, "I");
        assert_eq!(vars[2].reg_number, 3);
        assert_eq!(vars[2].start_offset, 2);
        assert_eq!(vars[2].end_offset, 10); // code_size
    }

    /// Migrated from: runtime_core/static_core/libarkfile/tests/debug_info_extractor_test.cpp
    /// Verifies line-to-offset mapping: line 6 → bytecode offset 3
    #[test]
    fn line_to_offset_mapping() {
        // Simulate foo method: line_start=3
        // ADVANCE_PC(1), ADVANCE_LINE(1), special(0,0) → line=4, addr=1
        // special(1,1) → line=5, addr=2
        // special(1,1) → line=6, addr=3
        // END_SEQUENCE
        let cp = vec![
            1, // pc advance = 1
            1, // line advance = 1
        ];
        let lnp = vec![
            LNP_ADVANCE_PC,
            LNP_ADVANCE_LINE,
            0x10, // special(0,0): line stays 4, addr stays 1
            0x20, // special(1,1): line=5, addr=2
            0x20, // special(1,1): line=6, addr=3
            LNP_END_SEQUENCE,
        ];
        let result = execute_line_program(&lnp, &cp, &[], 3, 10);
        assert_eq!(result.line_table.len(), 3);
        // Find entry for line 6
        let line6 = result.line_table.iter().find(|e| e.line == 6);
        assert!(line6.is_some());
        assert_eq!(line6.unwrap().offset, 3);
    }
}
