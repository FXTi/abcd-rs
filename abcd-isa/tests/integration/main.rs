//! Consolidated integration test suite for `abcd-isa`.

mod common;

mod bytecode;
mod decode_errors;
mod differential_oracle;
mod emitter_formats;
mod encode_errors;
mod entity_operands;
mod entity_relocation;
mod imm_boundaries;
mod legacy;
mod legacy_table_full;
mod long_jumps;
mod roundtrip;
mod version;
