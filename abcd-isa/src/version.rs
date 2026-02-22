use std::ffi::CString;
use std::fmt;

/// .abc file format version (`major.minor.patch.build`).
///
/// Wraps the 4-byte version tuple used by ArkCompiler panda files.
///
/// ```
/// use abcd_isa::Version;
///
/// let v = Version::current();
/// println!("ISA version: {v}");  // e.g. "13.0.1.0"
///
/// let file_ver = Version::new(12, 0, 6, 0);
/// assert!(file_ver.is_in_supported_range());
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version([u8; 4]);

impl Version {
    /// Create a version from individual components.
    #[inline]
    pub const fn new(major: u8, minor: u8, patch: u8, build: u8) -> Self {
        Self([major, minor, patch, build])
    }

    /// Major version component.
    #[inline]
    pub const fn major(&self) -> u8 {
        self.0[0]
    }

    /// Minor version component.
    #[inline]
    pub const fn minor(&self) -> u8 {
        self.0[1]
    }

    /// Patch version component.
    #[inline]
    pub const fn patch(&self) -> u8 {
        self.0[2]
    }

    /// Build version component.
    #[inline]
    pub const fn build(&self) -> u8 {
        self.0[3]
    }

    /// Raw 4-byte representation.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8; 4] {
        &self.0
    }

    /// Current ISA file format version.
    pub fn current() -> Self {
        let mut out = [0u8; 4];
        // SAFETY: out is a 4-byte array on the stack; C side writes exactly 4 bytes.
        unsafe { abcd_isa_sys::isa_get_version(out.as_mut_ptr()) };
        Self(out)
    }

    /// Minimum supported file format version.
    pub fn min_supported() -> Self {
        let mut out = [0u8; 4];
        // SAFETY: out is a 4-byte array on the stack; C side writes exactly 4 bytes.
        unsafe { abcd_isa_sys::isa_get_min_version(out.as_mut_ptr()) };
        Self(out)
    }

    /// Check if this version is within the supported range
    /// (`>= min_supported` and `<= current`).
    ///
    /// Note: a version can be in the supported range yet still be
    /// explicitly blocked — check [`is_blocked`](Self::is_blocked) separately.
    pub fn is_in_supported_range(&self) -> bool {
        // SAFETY: self.0 is a 4-byte array; C side reads exactly 4 bytes.
        unsafe { abcd_isa_sys::isa_is_version_compatible(self.0.as_ptr()) != 0 }
    }

    /// Check if this version is in the known-incompatible blocklist.
    ///
    /// This is independent of [`is_in_supported_range`](Self::is_in_supported_range):
    /// a version can be both in range and blocked.
    pub fn is_blocked(&self) -> bool {
        // SAFETY: self.0 is a 4-byte array; C side reads exactly 4 bytes.
        unsafe { abcd_isa_sys::isa_is_version_incompatible(self.0.as_ptr()) != 0 }
    }

    /// Look up the file format version for a HarmonyOS API level.
    ///
    /// Returns `None` if the API level is not in the mapping.
    pub fn for_api(api_level: u8) -> Option<Self> {
        let mut out = [0u8; 4];
        // SAFETY: out is a 4-byte array on the stack; C side writes exactly 4 bytes on success.
        let rc = unsafe { abcd_isa_sys::isa_get_version_by_api(api_level, out.as_mut_ptr()) };
        if rc == 0 { Some(Self(out)) } else { None }
    }

    /// Look up the file format version for an API level with a sub-API
    /// qualifier (e.g. API 12 `"beta1"`).
    ///
    /// Returns `None` if `sub_api` contains a NUL byte. Note that the
    /// underlying C++ implementation does not validate the sub-API string;
    /// an unrecognised qualifier may still return `Some`.
    pub fn for_api_sub(api_level: u8, sub_api: &str) -> Option<Self> {
        let c_sub = CString::new(sub_api).ok()?;
        let mut out = [0u8; 4];
        // SAFETY: c_sub is a valid NUL-terminated C string; out is a 4-byte
        // stack array; C side writes exactly 4 bytes on success.
        let rc = unsafe {
            abcd_isa_sys::isa_get_version_by_api_sub(api_level, c_sub.as_ptr(), out.as_mut_ptr())
        };
        if rc == 0 { Some(Self(out)) } else { None }
    }

    /// All versions in the known-incompatible set.
    pub fn incompatible_versions() -> Vec<Self> {
        // SAFETY: pure query, no preconditions.
        let count = unsafe { abcd_isa_sys::isa_incompatible_version_count() };
        let mut result = Vec::with_capacity(count);
        for i in 0..count {
            let mut out = [0u8; 4];
            // SAFETY: i < count (loop bound); out is a 4-byte stack array.
            unsafe { abcd_isa_sys::isa_incompatible_version_at(i, out.as_mut_ptr()) };
            result.push(Self(out));
        }
        result
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
