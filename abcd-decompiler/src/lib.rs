pub mod decode;
pub mod expr_recovery;
pub mod js_emitter;
pub mod structuring;

pub use decode::decode_method;

use abcd_ir::cfg::CFG;
use abcd_ir::instruction::TryBlockInfo;
use abcd_isa::EntityId;

/// Decompile a method's bytecode into JavaScript source.
pub fn decompile_method(
    code_bytes: &[u8],
    try_blocks: &[TryBlockInfo],
    resolver: &dyn expr_recovery::StringResolver,
    method_off: EntityId,
    num_vregs: u32,
    num_args: u32,
) -> String {
    let instructions = decode::decode_method(code_bytes);
    let cfg = CFG::build(&instructions, try_blocks);
    let stmts = structuring::structure_method(
        &instructions,
        &cfg,
        try_blocks,
        resolver,
        method_off,
        num_vregs,
        num_args,
    );
    js_emitter::emit_js(&stmts)
}
