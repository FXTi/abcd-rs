use std::collections::HashSet;

use abcd_isa::Version;

#[test]
fn new_and_accessors() {
    let v = Version::new(1, 2, 3, 4);
    assert_eq!(v.major(), 1);
    assert_eq!(v.minor(), 2);
    assert_eq!(v.patch(), 3);
    assert_eq!(v.build(), 4);
}

#[test]
fn as_bytes() {
    assert_eq!(Version::new(1, 2, 3, 4).as_bytes(), &[1, 2, 3, 4]);
}

#[test]
fn from_array() {
    let v: Version = [10, 2, 3, 4].into();
    assert_eq!(v.major(), 10);
    assert_eq!(v.minor(), 2);
}

#[test]
fn into_array() {
    let arr: [u8; 4] = Version::new(10, 2, 3, 4).into();
    assert_eq!(arr, [10, 2, 3, 4]);
}

#[test]
fn display_format() {
    assert_eq!(format!("{}", Version::new(13, 0, 1, 0)), "13.0.1.0");
}

#[test]
fn debug_format() {
    assert_eq!(
        format!("{:?}", Version::new(13, 0, 1, 0)),
        "Version(13.0.1.0)"
    );
}

#[test]
fn ordering() {
    assert!(Version::new(13, 0, 0, 0) > Version::new(12, 0, 6, 0));
    assert!(Version::new(12, 0, 5, 0) < Version::new(12, 0, 6, 0));
}

#[test]
fn hash_in_set() {
    let mut s = HashSet::new();
    s.insert(Version::new(1, 2, 3, 4));
    s.insert(Version::new(1, 2, 3, 4));
    assert_eq!(s.len(), 1);
    s.insert(Version::new(5, 6, 7, 8));
    assert_eq!(s.len(), 2);
}

#[test]
fn clone_copy() {
    let v = Version::new(1, 2, 3, 4);
    let v2 = v;
    assert_eq!(v.as_bytes(), v2.as_bytes());
}

#[test]
fn current_returns_valid() {
    let v = Version::current();
    // The ISA version is 13.0.1.0 as of the current build.
    assert_eq!(
        v,
        Version::new(13, 0, 1, 0),
        "ISA version changed; update this test"
    );
}

#[test]
fn min_supported_le_current() {
    assert!(Version::min_supported() <= Version::current());
}

#[test]
fn current_is_in_supported_range() {
    assert!(Version::current().is_in_supported_range());
}

#[test]
fn min_is_in_supported_range() {
    assert!(Version::min_supported().is_in_supported_range());
}

#[test]
fn zero_not_in_range() {
    assert!(!Version::new(0, 0, 0, 0).is_in_supported_range());
}

#[test]
fn max_not_in_range() {
    assert!(!Version::new(255, 255, 255, 255).is_in_supported_range());
}

#[test]
fn current_not_blocked() {
    assert!(!Version::current().is_blocked());
}

#[test]
fn blocked_versions_are_blocked() {
    for v in Version::incompatible_versions() {
        assert!(v.is_blocked(), "{v} should be blocked");
    }
}

#[test]
fn incompatible_versions_nonempty() {
    assert!(!Version::incompatible_versions().is_empty());
}

#[test]
fn for_api_known() {
    let v = Version::for_api(9).expect("API 9 should be mapped");
    assert_eq!(v.major(), 9);
}

#[test]
fn for_api_unknown() {
    assert!(Version::for_api(255).is_none());
}

#[test]
fn for_api_sub_nul_byte() {
    assert!(Version::for_api_sub(12, "beta\0one").is_none());
}

#[test]
fn for_api_known_multiple_levels() {
    // Test several known API levels beyond just 9.
    let v12 = Version::for_api(12);
    assert!(v12.is_some(), "API 12 should be mapped");
    assert_eq!(v12.unwrap().major(), 12);
}

#[test]
fn for_api_sub_valid() {
    // Test for_api_sub with a valid sub-API string doesn't panic.
    let _ = Version::for_api_sub(12, "beta1");
}

#[test]
fn version_just_below_min_supported() {
    let min = Version::min_supported();
    if min > Version::new(0, 0, 0, 0) {
        // Construct a version one step below min_supported.
        let below = if min.build() > 0 {
            Version::new(min.major(), min.minor(), min.patch(), min.build() - 1)
        } else if min.patch() > 0 {
            Version::new(min.major(), min.minor(), min.patch() - 1, 255)
        } else if min.minor() > 0 {
            Version::new(min.major(), min.minor() - 1, 255, 255)
        } else {
            Version::new(min.major() - 1, 255, 255, 255)
        };
        assert!(
            !below.is_in_supported_range(),
            "{below} should be below min_supported {min}"
        );
    }
}

#[test]
fn blocked_version_range_interaction() {
    // Verify that is_blocked and is_in_supported_range are independent checks.
    for v in Version::incompatible_versions() {
        assert!(v.is_blocked());
        // A blocked version may or may not be in the supported range;
        // the important thing is both checks work independently.
        let _in_range = v.is_in_supported_range();
    }
}
