use abcd_file::{AccessFlags, Builder, Error, File, Type, Version, decode, encode};
use abcd_isa::Bytecode;

fn add_method(builder: &mut Builder) {
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Tagged, &[Type::I32]);
    let (code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, 0, 1);
}

fn finish(builder: &mut Builder) -> File {
    builder.deduplicate();
    decode(&builder.finalize().unwrap()).unwrap()
}

#[test]
fn exact_source_versions_are_preserved() {
    // Corpus versions are assertions of supported behavior, not production
    // API selection rules. Both the mapping and serialization are upstream.
    for version in [
        Version::new(9, 0, 0, 0),
        Version::new(11, 0, 2, 0),
        Version::new(12, 0, 2, 0),
        Version::new(12, 0, 6, 0),
        Version::new(13, 0, 1, 0),
        Version::new(24, 0, 0, 0),
    ] {
        let mut builder = Builder::new();
        builder.set_file_version(version).unwrap();
        add_method(&mut builder);
        let original = finish(&mut builder);
        assert_eq!(original.version, version);
        let output = decode(&encode(&original).unwrap()).unwrap();
        assert_eq!(output.version, version);
    }
}

#[test]
fn unknown_patch_versions_are_rejected_without_changing_selection() {
    let mut builder = Builder::new();
    let selected = Version::new(9, 0, 0, 0);
    builder.set_file_version(selected).unwrap();
    for version in [
        Version::new(12, 0, 5, 0),
        Version::new(24, 1, 0, 0),
        Version::new(255, 0, 0, 0),
    ] {
        assert_eq!(
            builder.set_file_version(version),
            Err(Error::UnsupportedOutputVersion(version))
        );
    }
    add_method(&mut builder);
    let mut file = finish(&mut builder);
    assert_eq!(file.version, selected);
    file.version = Version::new(12, 0, 5, 0);
    assert_eq!(
        encode(&file),
        Err(Error::UnsupportedOutputVersion(file.version))
    );
}

#[test]
fn interleaved_builders_keep_their_own_api_and_proto_policy() {
    let mut legacy = Builder::new();
    let mut current = Builder::new();
    legacy.set_file_version(Version::new(9, 0, 0, 0)).unwrap();
    current.set_file_version(Version::new(24, 0, 0, 0)).unwrap();
    // Create the old proto after changing the other builder's policy.
    add_method(&mut legacy);
    add_method(&mut current);
    let old = finish(&mut legacy);
    let new = finish(&mut current);
    assert_eq!(old.version, Version::new(9, 0, 0, 0));
    assert_eq!(new.version, Version::new(24, 0, 0, 0));
    let old_method = old.all_methods().next().unwrap().1;
    let new_method = new.all_methods().next().unwrap().1;
    assert_eq!(old_method.return_type, Some(Type::Tagged));
    assert_eq!(old_method.arg_types, vec![Type::I32]);
    assert_eq!(new_method.return_type, None);
}

#[test]
fn parallel_builders_do_not_mix_writer_policies() {
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let handles = [Version::new(9, 0, 0, 0), Version::new(24, 0, 0, 0)].map(|version| {
        let barrier = barrier.clone();
        std::thread::spawn(move || {
            let mut builder = Builder::new();
            builder.set_file_version(version).unwrap();
            barrier.wait();
            add_method(&mut builder);
            let file = finish(&mut builder);
            assert_eq!(file.version, version);
            if version == Version::new(9, 0, 0, 0) {
                assert_eq!(
                    file.all_methods().next().unwrap().1.return_type,
                    Some(Type::Tagged)
                );
            }
        })
    });
    for handle in handles {
        handle.join().unwrap();
    }
}
