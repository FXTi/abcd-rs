//! Test group E — debug info completeness: source file/code, line and
//! column tables, local variables (incl. start_local_extended), and
//! parameter names.

use abcd_file::{AccessFlags, Builder, SourceLang, Type, decode};

fn build_debug() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65, 0x65, 0x65, 0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 10);
    let src = b.add_string("main.js");
    b.lnp_emit_set_file(lnp, debug, src);
    let src_code = b.add_string("function main() {}");
    b.lnp_emit_set_source_code(lnp, debug, src_code);

    let p1 = b.add_string("param1");
    b.debug_add_param(debug, p1);
    let p2 = b.add_string("param2");
    b.debug_add_param(debug, p2);

    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_advance_line(lnp, debug, 2);
    b.lnp_emit_column(lnp, debug, 0, 3);

    let vname = b.add_string("local_var");
    let vtype = b.add_string("I");
    b.lnp_emit_start_local(lnp, debug, 1, vname, vtype);
    let vname2 = b.add_string("local_var2");
    let vtype2 = b.add_string("D");
    let vsig = b.add_string("sig");
    b.lnp_emit_start_local_extended(lnp, debug, 2, vname2, vtype2, vsig);
    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_end_local(lnp, 1);

    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);

    b.finalize().expect("finalize")
}

#[test]
fn debug_info_decodes_completely() {
    let file = decode(&build_debug()).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let debug = g.methods[0].debug.as_ref().expect("debug info");

    assert_eq!(
        debug.source_file.map(|s| file.strings.resolve(s)),
        Some(Some("main.js"))
    );
    assert_eq!(
        debug.source_code.map(|s| file.strings.resolve(s)),
        Some(Some("function main() {}"))
    );

    let params: Vec<Option<&str>> = debug
        .params
        .iter()
        .map(|p| file.strings.resolve(p.name))
        .collect();
    assert_eq!(params, vec![Some("param1"), Some("param2")]);

    // Line table: the initial row + advance entries.
    assert!(!debug.line_table.is_empty());
    assert_eq!(debug.line_table[0].line, 10, "line start");

    // Column table: one SET_COLUMN entry.
    assert_eq!(debug.column_table.len(), 1);
    assert_eq!(debug.column_table[0].column, 3);

    // Local variables: start_local + start_local_extended, one closed.
    assert_eq!(debug.local_vars.len(), 2);
    let v0 = &debug.local_vars[0];
    assert_eq!(file.strings.resolve(v0.name), Some("local_var"));
    assert_eq!(file.strings.resolve(v0.type_name), Some("I"));
    assert_eq!(v0.reg_number, 1);
    assert_ne!(v0.end, v0.start, "END_LOCAL must close the first variable");
    let v1 = &debug.local_vars[1];
    assert_eq!(file.strings.resolve(v1.name), Some("local_var2"));
    assert_eq!(file.strings.resolve(v1.type_signature), Some("sig"));
    assert_eq!(v1.reg_number, 2);
}
