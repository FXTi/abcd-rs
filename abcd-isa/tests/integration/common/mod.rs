use abcd_isa::*;

pub fn assert_roundtrip(program: &[Bytecode]) {
    let (bytes, _) = encode(program).unwrap();
    let decoded = decode(&bytes).unwrap();
    assert_eq!(decoded.len(), program.len(), "length mismatch");
    for (i, (a, (b, _))) in program.iter().zip(&decoded).enumerate() {
        assert_eq!(a.emit_args(), b.emit_args(), "mismatch at {i}: {a} vs {b}",);
    }
}
