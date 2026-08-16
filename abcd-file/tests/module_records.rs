//! Test group C — module records: all five ModuleRecord kinds decoded from
//! the module literal-array encoding (requests + regular/namespace/local/
//! indirect/star records), as es2abc writes them.

use abcd_file::{AccessFlags, Builder, ModuleRecord, SourceLang, Type, decode};

fn build_module_array() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    // Module record literal array (the layout es2abc emits):
    //   requests: count, then string offsets
    //   regular imports: count, [local, import, request_idx]*
    //   namespace imports: count, [local, request_idx]*
    //   local exports: count, [local, export]*
    //   indirect exports: count, [export, import, request_idx]*
    //   star exports: count, [request_idx]*
    let la = b.add_literal_array("module");

    b.literal_array_add_integer(la, 1); // requests
    let dep = b.add_string("dep1");
    b.literal_array_add_string(la, dep);

    b.literal_array_add_integer(la, 1); // regular imports
    let l1 = b.add_string("local1");
    let i1 = b.add_string("imp1");
    b.literal_array_add_string(la, l1);
    b.literal_array_add_string(la, i1);
    b.literal_array_add_method_affiliate(la, 0);

    b.literal_array_add_integer(la, 1); // namespace imports
    let ns = b.add_string("ns1");
    b.literal_array_add_string(la, ns);
    b.literal_array_add_method_affiliate(la, 0);

    b.literal_array_add_integer(la, 1); // local exports
    let l2 = b.add_string("local2");
    let e2 = b.add_string("export2");
    b.literal_array_add_string(la, l2);
    b.literal_array_add_string(la, e2);

    b.literal_array_add_integer(la, 1); // indirect exports
    let e3 = b.add_string("export3");
    let i3 = b.add_string("imp3");
    b.literal_array_add_string(la, e3);
    b.literal_array_add_string(la, i3);
    b.literal_array_add_method_affiliate(la, 0);

    b.literal_array_add_integer(la, 1); // star exports
    b.literal_array_add_method_affiliate(la, 0);

    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

#[test]
fn all_five_module_record_kinds_decode() {
    let file = decode(&build_module_array()).expect("decode");
    let module = file.decode_module(0).expect("module data");

    assert_eq!(module.requests.len(), 1);
    assert_eq!(file.strings.resolve(module.requests[0]), Some("dep1"));

    assert_eq!(module.records.len(), 5);
    match &module.records[0] {
        ModuleRecord::RegularImport {
            local_name,
            import_name,
            module_request_idx,
        } => {
            assert_eq!(file.strings.resolve(*local_name), Some("local1"));
            assert_eq!(file.strings.resolve(*import_name), Some("imp1"));
            assert_eq!(*module_request_idx, 0);
        }
        other => panic!("expected RegularImport, got {other:?}"),
    }
    match &module.records[1] {
        ModuleRecord::NamespaceImport {
            local_name,
            module_request_idx,
        } => {
            assert_eq!(file.strings.resolve(*local_name), Some("ns1"));
            assert_eq!(*module_request_idx, 0);
        }
        other => panic!("expected NamespaceImport, got {other:?}"),
    }
    match &module.records[2] {
        ModuleRecord::LocalExport {
            local_name,
            export_name,
        } => {
            assert_eq!(file.strings.resolve(*local_name), Some("local2"));
            assert_eq!(file.strings.resolve(*export_name), Some("export2"));
        }
        other => panic!("expected LocalExport, got {other:?}"),
    }
    match &module.records[3] {
        ModuleRecord::IndirectExport {
            export_name,
            import_name,
            module_request_idx,
        } => {
            assert_eq!(file.strings.resolve(*export_name), Some("export3"));
            assert_eq!(file.strings.resolve(*import_name), Some("imp3"));
            assert_eq!(*module_request_idx, 0);
        }
        other => panic!("expected IndirectExport, got {other:?}"),
    }
    match &module.records[4] {
        ModuleRecord::StarExport { module_request_idx } => {
            assert_eq!(*module_request_idx, 0);
        }
        other => panic!("expected StarExport, got {other:?}"),
    }
}

#[test]
fn module_records_survive_encode_roundtrip() {
    let file1 = decode(&build_module_array()).expect("first decode");
    let encoded = abcd_file::encode(&file1).expect("encode");
    let file2 = decode(&encoded).expect("second decode");
    let module2 = file2
        .decode_module(0)
        .expect("module data after round-trip");
    assert_eq!(module2.records.len(), 5);
    assert_eq!(file2.strings.resolve(module2.requests[0]), Some("dep1"));
}
