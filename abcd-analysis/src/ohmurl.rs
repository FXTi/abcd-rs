//! Canonical OpenHarmony OHM URL (`OHMUrl`) parser (`D3`, `#94`).
//!
//! OpenHarmony / ArkCompiler `.abc` containers and `--merge-abc` module records
//! encode module specifiers and record class descriptors across several OHM URL
//! forms (`arkcompiler_ets_runtime` `ModulePathHelper`):
//!
//! - **5-field normalized**:
//!   `@normalized:<is_native>&<module_name>&<bundle_name>&<import_path>&<version>`
//!   (for example, `@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0`
//!   or native `@normalized:Y&entry&com.demo&libentry.so&1.0.0`).
//! - **4-field / 3-field normalized**:
//!   `@normalized:N&<module_name>&<bundle_or_import_path>&<version>` and
//!   `@normalized:N&<module_name>&<import_path>`.
//! - **Bare `&`-prefixed record names** (emitted as class names inside merged
//!   `.abc` files with the leading `@normalized:N` stripped):
//!   `&<module_name>&<bundle_name>&<import_path>&<version>`,
//!   `&<module_name>&<import_path>&<version>`, and `&<import_path>&<version>&`.
//! - **Bundle / package / app specifiers**:
//!   `@bundle:<bundle>/<module>/<path>`, `@package:<pkg_modules_path>`,
//!   `@app:<bundle>/<module>/<target>`.
//! - **System / SDK / native specifiers**:
//!   `@ohos:<name>`, `@ohos.<name>`, `@hms:<name>`, `@hms.<name>`,
//!   `@kit.<name>`, `@kit:<name>`, `@arkts.<name>`, `@arkts:<name>`,
//!   `@system:<name>`, `@system.<name>`, `@native:<name>`.
//!
//! Both [`crate::module_link`] and downstream `abcd-decompile` consume this
//! single zero-copy parser rather than ad-hoc `&`-splitting.

/// Classification of an OpenHarmony OHM URL scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OhmUrlKind {
    /// `@normalized:{Y|N}&...` or bare `&...` normalized OHM URL.
    Normalized {
        /// `true` when the leading native flag is `"Y"` (native `.so` module).
        is_native: bool,
    },
    /// `@bundle:<bundle>/<module>/<path>`.
    Bundle,
    /// `@package:<pkg_modules_path>`.
    Package,
    /// `@app:<bundle>/<module>/<target>`.
    App,
    /// `@ohos:<name>` or `@ohos.<name>`.
    OhosSdk,
    /// `@hms:<name>` or `@hms.<name>`.
    HmsSdk,
    /// `@kit.<name>` or `@kit:<name>`.
    KitSdk,
    /// `@arkts.<name>` or `@arkts:<name>`.
    ArktsSdk,
    /// `@system:<name>` or `@system.<name>`.
    SystemSdk,
    /// `@native:<name>`.
    Native,
}

/// Zero-copy parsed OpenHarmony OHM URL (`D3`, `#94`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OhmUrl<'a> {
    /// Recognized OHM URL scheme.
    pub kind: OhmUrlKind,
    /// Module / HAR / HSP name when present (`"entry"`, `"har_net"`, …), else `""`.
    pub module_name: &'a str,
    /// Bundle name when present (`"com.demo.app"`, …), else `""`.
    pub bundle_name: &'a str,
    /// Logical import path or SDK target (`"entry/src/main/ets/Helper"`, `"net.http"`, …).
    pub import_path: &'a str,
    /// Optional version segment (`Some("1.0.0")`) when non-empty.
    pub version: Option<&'a str>,
}

impl<'a> OhmUrl<'a> {
    /// Strip surrounding Panda class-descriptor delimiters (`L...;`) when present.
    #[must_use]
    #[inline]
    pub fn strip_descriptor(raw: &'a str) -> &'a str {
        raw.strip_prefix('L')
            .and_then(|s| s.strip_suffix(';'))
            .unwrap_or(raw)
    }

    /// Parse an OHM URL from a module specifier or bare record name.
    ///
    /// Returns `None` for ordinary relative/bare ECMAScript specifiers
    /// (`"./foo"`, `"../bar"`, `"L_GLOBAL;"`, dot-encoded class names, …).
    #[must_use]
    pub fn parse(raw: &'a str) -> Option<Self> {
        if let Some(rest) = raw.strip_prefix("@normalized:") {
            return parse_normalized_body(rest);
        }
        if let Some(rest) = raw.strip_prefix('&') {
            return parse_bare_ampersand_body(rest);
        }
        if let Some(rest) = raw.strip_prefix("@bundle:") {
            if rest.is_empty() {
                return None;
            }
            let mut segs = rest.splitn(3, '/');
            let bundle_name = segs.next().unwrap_or("");
            let module_name = segs.next().unwrap_or("");
            return Some(Self {
                kind: OhmUrlKind::Bundle,
                module_name,
                bundle_name,
                import_path: rest,
                version: None,
            });
        }
        if let Some(rest) = raw.strip_prefix("@package:") {
            if rest.is_empty() {
                return None;
            }
            return Some(Self {
                kind: OhmUrlKind::Package,
                module_name: "",
                bundle_name: "",
                import_path: rest,
                version: None,
            });
        }
        if let Some(rest) = raw.strip_prefix("@app:") {
            if rest.is_empty() {
                return None;
            }
            let mut segs = rest.splitn(3, '/');
            let bundle_name = segs.next().unwrap_or("");
            let module_name = segs.next().unwrap_or("");
            return Some(Self {
                kind: OhmUrlKind::App,
                module_name,
                bundle_name,
                import_path: rest,
                version: None,
            });
        }
        for (prefix, kind) in [
            ("@ohos:", OhmUrlKind::OhosSdk),
            ("@ohos.", OhmUrlKind::OhosSdk),
            ("@hms:", OhmUrlKind::HmsSdk),
            ("@hms.", OhmUrlKind::HmsSdk),
            ("@kit:", OhmUrlKind::KitSdk),
            ("@kit.", OhmUrlKind::KitSdk),
            ("@arkts:", OhmUrlKind::ArktsSdk),
            ("@arkts.", OhmUrlKind::ArktsSdk),
            ("@system:", OhmUrlKind::SystemSdk),
            ("@system.", OhmUrlKind::SystemSdk),
            ("@native:", OhmUrlKind::Native),
        ] {
            if let Some(rest) = raw.strip_prefix(prefix) {
                if rest.is_empty() {
                    return None;
                }
                return Some(Self {
                    kind,
                    module_name: "",
                    bundle_name: "",
                    import_path: rest,
                    version: None,
                });
            }
        }
        None
    }

    /// Parse an OHM URL from either a `L...;` class descriptor or a raw specifier.
    #[must_use]
    #[inline]
    pub fn parse_descriptor(raw: &'a str) -> Option<Self> {
        Self::parse(Self::strip_descriptor(raw))
    }

    /// Whether this URL designates an external system SDK or native `.so`
    /// target outside user JS/ArkTS bytecode bundles.
    #[must_use]
    #[inline]
    pub const fn is_external_sdk(&self) -> bool {
        matches!(
            self.kind,
            OhmUrlKind::Normalized { is_native: true }
                | OhmUrlKind::OhosSdk
                | OhmUrlKind::HmsSdk
                | OhmUrlKind::KitSdk
                | OhmUrlKind::ArktsSdk
                | OhmUrlKind::SystemSdk
                | OhmUrlKind::Native
        )
    }

    /// Whether `raw` is an external SDK or `@normalized:Y&...` native specifier.
    #[must_use]
    pub fn is_sdk_specifier(raw: &str) -> bool {
        if raw.starts_with("@normalized:Y&") {
            return true;
        }
        OhmUrl::parse(raw).is_some_and(|u| u.is_external_sdk())
    }

    /// Whether this URL is an internal container OHM URL (`@bundle:`, `@package:`,
    /// or non-native `@normalized:N&...` / `&...`) eligible for intra-bundle
    /// path peeling and relative-import rewriting.
    #[must_use]
    #[inline]
    pub const fn is_internal_bundle_url(&self) -> bool {
        matches!(
            self.kind,
            OhmUrlKind::Normalized { is_native: false } | OhmUrlKind::Bundle | OhmUrlKind::Package
        )
    }

    /// Unwrap `@bundle:`, `@package:`, `@normalized:`, or bare `&...` OHM URL
    /// prefixes to their underlying logical module path, returning `raw`
    /// unchanged for non-OHM paths.
    #[must_use]
    pub fn peel_import_path(raw: &'a str) -> &'a str {
        if let Some(parsed) = Self::parse(raw)
            && matches!(
                parsed.kind,
                OhmUrlKind::Bundle | OhmUrlKind::Package | OhmUrlKind::Normalized { .. }
            )
        {
            return parsed.import_path;
        }
        if let Some(rest) = raw.strip_prefix("@normalized:") {
            return rest;
        }
        raw
    }
}

fn non_empty_opt(s: &str) -> Option<&str> {
    (!s.is_empty()).then_some(s)
}

fn parse_normalized_body(rest: &str) -> Option<OhmUrl<'_>> {
    let parts: Vec<&str> = rest.split('&').collect();
    let is_native = matches!(parts.first().copied(), Some("Y" | "y"));
    let (module_name, bundle_name, import_path, version) = match parts.as_slice() {
        // Canonical 5-field: `<is_native>&<module>&<bundle>&<import_path>&<version>[&...]`
        [_flag, mod_name, bundle_name, import_path, ver, ..] => {
            (*mod_name, *bundle_name, *import_path, non_empty_opt(ver))
        }
        // 4-field forms:
        // - `N&entry&&entry/src/main/ets/Helper` (`p2` empty or `p3` is a `/`-path)
        // - `N&har&com.demo/har/src/main/ets/Api&1.0.0` (`p2` is `<bundle>/<path>`, `p3` is `<ver>`)
        [_flag, mod_name, p2, p3] => {
            if p3.contains('/') || (!p3.is_empty() && p2.is_empty()) {
                (*mod_name, "", *p3, None)
            } else {
                (*mod_name, "", *p2, non_empty_opt(p3))
            }
        }
        // 3-field form: `N&<module>&<import_path>`
        [_flag, mod_name, import_path] => (*mod_name, "", *import_path, None),
        _ => return None,
    };
    if import_path.is_empty() {
        return None;
    }
    Some(OhmUrl {
        kind: OhmUrlKind::Normalized { is_native },
        module_name,
        bundle_name,
        import_path,
        version,
    })
}

fn parse_bare_ampersand_body(rest: &str) -> Option<OhmUrl<'_>> {
    let parts: Vec<&str> = rest.split('&').collect();
    let (module_name, bundle_name, import_path, version) = match parts.as_slice() {
        // 4+-field bare `&<module>&<bundle>&<import_path>&<version>[&...]`
        // vs 3-field trailing-`&` `&<import_path>&<version>&` (where `parts` has 3 items, handled below;
        // if 4 items with empty trailing item e.g. `&mod&path&1.0.0&`, check whether `p2` is path or version!)
        [p0, p1, p2, p3, ..] => {
            if !p2.is_empty()
                && (p2.contains('/') || !p3.is_empty() || p1.is_empty() || !p1.contains('/'))
            {
                (*p0, *p1, *p2, non_empty_opt(p3))
            } else if p1.contains('/') {
                (*p0, "", *p1, non_empty_opt(p2))
            } else {
                ("", "", *p0, non_empty_opt(p1))
            }
        }
        [p0, p1, ver] => {
            if p1.contains('/') {
                (*p0, "", *p1, non_empty_opt(ver))
            } else {
                ("", "", *p0, non_empty_opt(p1))
            }
        }
        [p0, ver] => ("", "", *p0, non_empty_opt(ver)),
        [p0] => ("", "", *p0, None),
        [] => return None,
    };
    if import_path.is_empty() {
        return None;
    }
    Some(OhmUrl {
        kind: OhmUrlKind::Normalized { is_native: false },
        module_name,
        bundle_name,
        import_path,
        version,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_five_field_and_four_field_normalized_ohmurls() {
        let u5 = OhmUrl::parse("@normalized:N&entry&com.demo&entry/src/main/ets/Helper&1.0.0")
            .expect("5-field normalized");
        assert_eq!(u5.kind, OhmUrlKind::Normalized { is_native: false });
        assert_eq!(u5.module_name, "entry");
        assert_eq!(u5.bundle_name, "com.demo");
        assert_eq!(u5.import_path, "entry/src/main/ets/Helper");
        assert_eq!(u5.version, Some("1.0.0"));
        assert!(!u5.is_external_sdk());
        assert!(u5.is_internal_bundle_url());

        let u4_har =
            OhmUrl::parse("@normalized:N&har_net&com.demo.app/har_net/src/main/ets/NetRepo&1.0.0")
                .expect("4-field commercial HAR normalized");
        assert_eq!(u4_har.kind, OhmUrlKind::Normalized { is_native: false });
        assert_eq!(u4_har.module_name, "har_net");
        assert_eq!(u4_har.bundle_name, "");
        assert_eq!(
            u4_har.import_path,
            "com.demo.app/har_net/src/main/ets/NetRepo"
        );
        assert_eq!(u4_har.version, Some("1.0.0"));
        assert_eq!(
            OhmUrl::peel_import_path(
                "@normalized:N&har_net&com.demo.app/har_net/src/main/ets/NetRepo&1.0.0"
            ),
            "com.demo.app/har_net/src/main/ets/NetRepo"
        );

        let u4_empty_bundle =
            OhmUrl::parse("@normalized:N&entry&&entry/src/main/ets/Helper").expect("empty bundle");
        assert_eq!(u4_empty_bundle.module_name, "entry");
        assert_eq!(u4_empty_bundle.bundle_name, "");
        assert_eq!(u4_empty_bundle.import_path, "entry/src/main/ets/Helper");
        assert_eq!(u4_empty_bundle.version, None);

        let native = OhmUrl::parse("@normalized:Y&entry&com.demo&libentry.so&1.0.0")
            .expect("native normalized");
        assert_eq!(native.kind, OhmUrlKind::Normalized { is_native: true });
        assert_eq!(native.import_path, "libentry.so");
        assert!(native.is_external_sdk());
        assert!(!native.is_internal_bundle_url());
    }

    #[test]
    fn parses_bare_ampersand_bundle_package_and_sdk_forms() {
        let bare4 = OhmUrl::parse_descriptor("L&entry&com.demo&entry/src/main/ets/Foo&1.0.0;")
            .expect("bare 4-field descriptor");
        assert_eq!(bare4.module_name, "entry");
        assert_eq!(bare4.bundle_name, "com.demo");
        assert_eq!(bare4.import_path, "entry/src/main/ets/Foo");
        assert_eq!(bare4.version, Some("1.0.0"));

        let bare_har = OhmUrl::parse("&har&com.demo/har/src/main/ets/Api&1.0.0").expect("bare har");
        assert_eq!(bare_har.module_name, "har");
        assert_eq!(bare_har.import_path, "com.demo/har/src/main/ets/Api");
        assert_eq!(bare_har.version, Some("1.0.0"));

        let bare_short = OhmUrl::parse("&com.demo/entry/ets/Foo&1.0.0&").expect("bare short");
        assert_eq!(bare_short.import_path, "com.demo/entry/ets/Foo");
        assert_eq!(bare_short.version, Some("1.0.0"));

        let bundle = OhmUrl::parse("@bundle:com.demo.app/entry/ets/pages/Index").expect("@bundle:");
        assert_eq!(bundle.kind, OhmUrlKind::Bundle);
        assert_eq!(bundle.bundle_name, "com.demo.app");
        assert_eq!(bundle.module_name, "entry");
        assert_eq!(bundle.import_path, "com.demo.app/entry/ets/pages/Index");
        assert!(bundle.is_internal_bundle_url());

        let pkg = OhmUrl::parse(
            "@package:pkg_modules/.ohpm/@ohos+axios@2.2.0/pkg_modules/@ohos/axios/index",
        )
        .expect("@package:");
        assert_eq!(pkg.kind, OhmUrlKind::Package);
        assert!(pkg.is_internal_bundle_url());

        for (spec, expected_kind, expected_target) in [
            ("@ohos:net.http", OhmUrlKind::OhosSdk, "net.http"),
            ("@ohos.security.huks", OhmUrlKind::OhosSdk, "security.huks"),
            ("@hms:core.account", OhmUrlKind::HmsSdk, "core.account"),
            ("@hms.core.push", OhmUrlKind::HmsSdk, "core.push"),
            ("@kit.NetworkKit", OhmUrlKind::KitSdk, "NetworkKit"),
            ("@arkts.collections", OhmUrlKind::ArktsSdk, "collections"),
            ("@system.app", OhmUrlKind::SystemSdk, "app"),
            (
                "@native:system.HashMap",
                OhmUrlKind::Native,
                "system.HashMap",
            ),
        ] {
            let parsed = OhmUrl::parse(spec).expect(spec);
            assert_eq!(parsed.kind, expected_kind);
            assert_eq!(parsed.import_path, expected_target);
            assert!(parsed.is_external_sdk());
            assert!(OhmUrl::is_sdk_specifier(spec));
        }

        assert!(OhmUrl::parse("./local/Helper").is_none());
        assert_eq!(OhmUrl::peel_import_path("./local/Helper"), "./local/Helper");
    }
}
