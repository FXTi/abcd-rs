use std::fmt;

use crate::generated::{
    API_12, API_12_SUB_QUALIFIERS, API_12_SUB_VERSION, API_VERSION_MAP, CURRENT_VERSION,
    INCOMPATIBLE_VERSIONS, MIN_VERSION,
};

/// `.abc` file format version (`major.minor.patch.build`).
///
/// Wraps the 4-byte version tuple used by ArkCompiler panda files in 100% pure
/// Safe Rust, backed by constants generated from `file_format_version.h.erb`
/// via `scripts/vendor-gen.py`.
///
/// ```
/// use abcd_isa::Version;
///
/// let v = Version::current();
/// assert_eq!(v, Version::new(24, 0, 0, 0));
///
/// let file_ver = Version::new(12, 0, 6, 0);
/// assert!(file_ver.is_in_supported_range());
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version([u8; 4]);

impl Version {
    /// Create a version from individual components.
    #[inline]
    #[must_use]
    pub const fn new(major: u8, minor: u8, patch: u8, build: u8) -> Self {
        Self([major, minor, patch, build])
    }

    /// Major version component.
    #[inline]
    #[must_use]
    pub const fn major(&self) -> u8 {
        self.0[0]
    }

    /// Minor version component.
    #[inline]
    #[must_use]
    pub const fn minor(&self) -> u8 {
        self.0[1]
    }

    /// Patch version component.
    #[inline]
    #[must_use]
    pub const fn patch(&self) -> u8 {
        self.0[2]
    }

    /// Build version component.
    #[inline]
    #[must_use]
    pub const fn build(&self) -> u8 {
        self.0[3]
    }

    /// Raw 4-byte representation.
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 4] {
        &self.0
    }

    /// Current ISA file format version.
    #[inline]
    #[must_use]
    pub const fn current() -> Self {
        Self(CURRENT_VERSION)
    }

    /// Minimum supported file format version.
    #[inline]
    #[must_use]
    pub const fn min_supported() -> Self {
        Self(MIN_VERSION)
    }

    /// Check if this version is within the supported range
    /// (`>= min_supported` and `<= current`).
    ///
    /// Note: a version can be in the supported range yet still be
    /// explicitly blocked — check [`is_blocked`](Self::is_blocked) separately.
    #[inline]
    #[must_use]
    pub fn is_in_supported_range(&self) -> bool {
        *self >= Self::min_supported() && *self <= Self::current()
    }

    /// Check if this version is in the known-incompatible blocklist.
    ///
    /// This is independent of [`is_in_supported_range`](Self::is_in_supported_range):
    /// a version can be both in range and blocked.
    #[inline]
    #[must_use]
    pub fn is_blocked(&self) -> bool {
        INCOMPATIBLE_VERSIONS.contains(&self.0)
    }

    /// Look up the file format version for a HarmonyOS API level.
    ///
    /// Returns `None` if the API level is not in `api_version_map`.
    #[must_use]
    pub fn for_api(api_level: u8) -> Option<Self> {
        API_VERSION_MAP
            .binary_search_by_key(&api_level, |&(api, _)| api)
            .ok()
            .map(|idx| Self(API_VERSION_MAP[idx].1))
    }

    /// Look up the file format version for an API level with a sub-API
    /// qualifier (e.g. API 12 `"beta1"`).
    ///
    /// Returns `None` if `sub_api` contains an interior NUL byte. Matches
    /// upstream `GetVersionByApi`: unknown API levels fall back to
    /// [`Self::current`].
    #[must_use]
    pub fn for_api_sub(api_level: u8, sub_api: &str) -> Option<Self> {
        if sub_api.as_bytes().contains(&0) {
            return None;
        }
        if api_level == API_12 && API_12_SUB_QUALIFIERS.contains(&sub_api) {
            return Some(Self(API_12_SUB_VERSION));
        }
        Some(Self::for_api(api_level).unwrap_or_else(Self::current))
    }

    /// All versions in the known-incompatible set.
    #[must_use]
    pub fn incompatible_versions() -> Vec<Self> {
        INCOMPATIBLE_VERSIONS.iter().copied().map(Self).collect()
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}.{}", self.0[0], self.0[1], self.0[2], self.0[3])
    }
}

impl fmt::Debug for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Version({self})")
    }
}

impl From<[u8; 4]> for Version {
    fn from(bytes: [u8; 4]) -> Self {
        Self(bytes)
    }
}

impl From<Version> for [u8; 4] {
    fn from(v: Version) -> Self {
        v.0
    }
}
