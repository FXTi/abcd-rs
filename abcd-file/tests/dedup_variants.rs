//! P2 test gap: the two SPLIT dedup variants. The combined
//! `Builder::deduplicate()` is exercised by other suites; these pin
//! `deduplicate_code_and_debug_info` and `deduplicate_annotations`
//! individually.

use abcd_file::{AccessFlags, AnnotationElemDefEx, AnnotationElemValue, Builder, Type, decode};
use abcd_isa::Bytecode;

/// Two static methods with byte-identical bodies (a debug info item each,
/// so the debug-info dedup arm is exercised too).
fn build_identical_methods(dedup: impl FnOnce(&mut Builder)) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    for name in ["f1", "f2"] {
        let m = b.class_add_method(cls, name, proto, AccessFlags::STATIC, &code, 0, 0);
        let lnp = b.create_lnp();
        b.lnp_emit_end(lnp);
        let dbg = b.create_debug_info(lnp, 1);
        b.method_set_debug_info(m, dbg);
    }
    dedup(&mut b);
    b.finalize().expect("finalize")
}

#[test]
fn deduplicate_code_and_debug_info_merges_identical_bodies() {
    let plain = build_identical_methods(|_| {});
    let deduped = build_identical_methods(|b| b.deduplicate_code_and_debug_info());
    assert!(
        deduped.len() < plain.len(),
        "identical code+debug items must merge: deduped {} < plain {}",
        deduped.len(),
        plain.len()
    );
    let file = decode(&deduped).expect("decode deduped");
    let names: Vec<&str> = file
        .all_methods()
        .map(|(_, m)| file.strings.resolve(m.name).unwrap())
        .collect();
    assert_eq!(names.len(), 2, "both methods survive dedup: {names:?}");
    for (_, m) in file.all_methods() {
        let body = m.body.as_ref().expect("body");
        assert!(
            matches!(body.bytecodes.as_slice(), [Bytecode::Returnundefined]),
            "method body intact after dedup"
        );
    }
}

/// Two classes carrying byte-identical runtime annotations.
fn build_identical_annotations(dedup: impl FnOnce(&mut Builder)) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let global = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    b.class_add_method(
        global,
        "func_main_0",
        proto,
        AccessFlags::STATIC,
        &code,
        0,
        0,
    );
    let name = b.add_string("v");
    // One shared annotation CLASS: two separately created but byte-identical
    // annotation items (same class, same elements) attached to two owners.
    let anno_cls = b.add_class("LAnno;");
    for desc in ["LA;", "LB;"] {
        let cls = b.add_class(desc);
        let ann = b.create_annotation_ex(
            anno_cls,
            &[AnnotationElemDefEx {
                name,
                tag: b'1', // U32 scalar
                value: AnnotationElemValue::Scalar(7),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
    }
    dedup(&mut b);
    b.finalize().expect("finalize")
}

#[test]
fn deduplicate_annotations_merges_identical_items() {
    let plain = build_identical_annotations(|_| {});
    let deduped = build_identical_annotations(|b| b.deduplicate_annotations());
    assert!(
        deduped.len() < plain.len(),
        "identical annotation items must merge: deduped {} < plain {}",
        deduped.len(),
        plain.len()
    );
    let file = decode(&deduped).expect("decode deduped");
    for desc in ["LA;", "LB;"] {
        let cls = file.class_by_str(desc).expect("class");
        // The vendored writer folds the runtime bucket into compile-time
        // on write (the documented annotation-category contract).
        assert_eq!(
            cls.annotations.compile_time.len(),
            1,
            "annotation survives dedup on {desc}"
        );
    }
}
