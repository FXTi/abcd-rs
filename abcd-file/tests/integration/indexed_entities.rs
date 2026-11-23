use abcd_file::{AccessFlags, Builder, Error, SourceLang, Type, decode};
use abcd_isa::{Bytecode, EntityId, Imm, encode};

#[test]
fn invalid_string_and_method_indices_are_reported_with_context() {
    for instruction in [
        Bytecode::LdaStr(EntityId(u16::MAX as u32)),
        Bytecode::Definefunc(Imm(0), EntityId(u16::MAX as u32), Imm(0)),
    ] {
        let mut builder = Builder::new();
        builder.set_api(12, "beta1");
        let class = builder.add_global_class();
        builder.class_set_source_lang(class, SourceLang::EcmaScript);
        let proto = builder.create_proto(Type::Tagged, &[]);
        let (code, _) = encode(&[instruction, Bytecode::Returnundefined]).unwrap();
        builder.class_add_method(class, "f", proto, AccessFlags::PUBLIC, &code, 0, 0);
        let data = builder.finalize().unwrap();
        match decode(&data).unwrap_err() {
            Error::Malformed {
                field: "bytecode entity reference",
                context,
            } => {
                assert!(context.contains(instruction.mnemonic()), "{context}");
                assert!(context.contains("index 65535"), "{context}");
            }
            error => panic!("unexpected error: {error}"),
        }
    }
}
