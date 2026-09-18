//! Phase 0 审计探针（临时文件，验证后即删）。
//! 用法: probe <invalid-opcode|invalid-prefixed|emit-drop>
fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "invalid-opcode" => {
            // 0xE2 未分配（isa.yaml 非前缀最大 0xE1）。
            let r = abcd_isa::decode(&[0xE2]);
            println!("decode([0xE2]) -> {:?}", r.map(|v| v.len()));
        }
        "invalid-prefixed" => {
            // callruntime(0xFB) 子 opcode 0xFF 未分配（最大 0x1b）。
            let r = abcd_isa::decode(&[0xFB, 0xFF]);
            println!("decode([0xFB,0xFF]) -> {:?}", r.map(|v| v.len()));
        }
        "emit-drop" => {
            // Ldlexvar 最宽格式 imm1_8_imm2_8：Imm(300) 无格式可配。
            let p = [abcd_isa::insn::Ldlexvar::new(
                abcd_isa::Imm(300),
                abcd_isa::Imm(0),
            )];
            match abcd_isa::encode(&p) {
                Ok((bytes, offsets)) => println!(
                    "encode returned Ok: {} bytes, offsets {:?} (input had 1 instruction)",
                    bytes.len(),
                    offsets
                ),
                Err(e) => println!("encode error: {e}"),
            }
        }
        other => eprintln!("unknown mode {other}"),
    }
}
