//! Literal data accessor.

use crate::{EntityId, File, error::Error};
use std::ffi::CStr;
use std::fmt;

/// Literal tag values from the ABC file format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LiteralTag {
    TagValue = 0x00,
    Bool = 0x01,
    Integer = 0x02,
    Float = 0x03,
    Double = 0x04,
    String = 0x05,
    Method = 0x06,
    GeneratorMethod = 0x07,
    Accessor = 0x08,
    MethodAffiliate = 0x09,
    ArrayU1 = 0x0a,
    ArrayU8 = 0x0b,
    ArrayI8 = 0x0c,
    ArrayU16 = 0x0d,
    ArrayI16 = 0x0e,
    ArrayU32 = 0x0f,
    ArrayI32 = 0x10,
    ArrayU64 = 0x11,
    ArrayI64 = 0x12,
    ArrayF32 = 0x13,
    ArrayF64 = 0x14,
    ArrayString = 0x15,
    AsyncGeneratorMethod = 0x16,
    LiteralBufferIndex = 0x17,
    LiteralArray = 0x18,
    BuiltinTypeIndex = 0x19,
    Getter = 0x1a,
    Setter = 0x1b,
    EtsImplements = 0x1c,
    NullValue = 0xff,
}

impl LiteralTag {
    pub fn from_u8(val: u8) -> Option<Self> {
        match val {
            0x00 => Some(Self::TagValue),
            0x01 => Some(Self::Bool),
            0x02 => Some(Self::Integer),
            0x03 => Some(Self::Float),
            0x04 => Some(Self::Double),
            0x05 => Some(Self::String),
            0x06 => Some(Self::Method),
            0x07 => Some(Self::GeneratorMethod),
            0x08 => Some(Self::Accessor),
            0x09 => Some(Self::MethodAffiliate),
            0x0a => Some(Self::ArrayU1),
            0x0b => Some(Self::ArrayU8),
            0x0c => Some(Self::ArrayI8),
            0x0d => Some(Self::ArrayU16),
            0x0e => Some(Self::ArrayI16),
            0x0f => Some(Self::ArrayU32),
            0x10 => Some(Self::ArrayI32),
            0x11 => Some(Self::ArrayU64),
            0x12 => Some(Self::ArrayI64),
            0x13 => Some(Self::ArrayF32),
            0x14 => Some(Self::ArrayF64),
            0x15 => Some(Self::ArrayString),
            0x16 => Some(Self::AsyncGeneratorMethod),
            0x17 => Some(Self::LiteralBufferIndex),
            0x18 => Some(Self::LiteralArray),
            0x19 => Some(Self::BuiltinTypeIndex),
            0x1a => Some(Self::Getter),
            0x1b => Some(Self::Setter),
            0x1c => Some(Self::EtsImplements),
            0xff => Some(Self::NullValue),
            _ => None,
        }
    }
}

impl fmt::Display for LiteralTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// A literal value from a literal array.
#[derive(Debug, Clone)]
pub struct LiteralVal {
    pub tag: Option<LiteralTag>,
    pub u64_val: u64,
    /// String data (decoded from MUTF-8). Present when tag is STRING or ARRAY_STRING.
    pub str_data: Option<String>,
    /// UTF-16 length of the string. 0 for non-string tags.
    pub str_utf16_len: u32,
}

impl LiteralVal {
    pub fn as_u8(&self) -> u8 {
        self.u64_val as u8
    }
    pub fn as_u16(&self) -> u16 {
        self.u64_val as u16
    }
    pub fn as_u32(&self) -> u32 {
        self.u64_val as u32
    }
    pub fn as_u64(&self) -> u64 {
        self.u64_val
    }
    pub fn as_i32(&self) -> i32 {
        self.u64_val as i32
    }
    pub fn as_i64(&self) -> i64 {
        self.u64_val as i64
    }
    pub fn as_f32(&self) -> f32 {
        f32::from_bits(self.u64_val as u32)
    }
    pub fn as_f64(&self) -> f64 {
        f64::from_bits(self.u64_val)
    }
    pub fn as_bool(&self) -> bool {
        self.u64_val != 0
    }

    /// Checked conversion to `u8`. Returns `None` if the value doesn't fit.
    pub fn try_as_u8(&self) -> Option<u8> {
        u8::try_from(self.u64_val).ok()
    }
    /// Checked conversion to `u16`. Returns `None` if the value doesn't fit.
    pub fn try_as_u16(&self) -> Option<u16> {
        u16::try_from(self.u64_val).ok()
    }
    /// Checked conversion to `u32`. Returns `None` if the value doesn't fit.
    pub fn try_as_u32(&self) -> Option<u32> {
        u32::try_from(self.u64_val).ok()
    }
    /// Checked conversion to `i8`. Returns `None` if the value doesn't fit.
    pub fn try_as_i8(&self) -> Option<i8> {
        i8::try_from(self.u64_val as i64).ok()
    }
    /// Checked conversion to `i16`. Returns `None` if the value doesn't fit.
    pub fn try_as_i16(&self) -> Option<i16> {
        i16::try_from(self.u64_val as i64).ok()
    }
    /// Checked conversion to `i32`. Returns `None` if the value doesn't fit.
    pub fn try_as_i32(&self) -> Option<i32> {
        i32::try_from(self.u64_val as i64).ok()
    }
    /// Checked conversion to `i64`. Returns `None` if the value doesn't fit in `i64`.
    pub fn try_as_i64(&self) -> Option<i64> {
        i64::try_from(self.u64_val).ok()
    }

    /// Convert to a typed `LiteralValue` using the tag.
    pub fn to_value(&self) -> LiteralValue {
        match self.tag {
            Some(LiteralTag::Bool) => LiteralValue::Bool(self.as_bool()),
            Some(LiteralTag::Integer) => LiteralValue::Integer(self.u64_val as i64),
            Some(LiteralTag::Float) => LiteralValue::Float(self.as_f32()),
            Some(LiteralTag::Double) => LiteralValue::Double(self.as_f64()),
            Some(LiteralTag::String | LiteralTag::ArrayString) => {
                LiteralValue::String(EntityId(self.as_u32()))
            }
            Some(
                LiteralTag::Method
                | LiteralTag::GeneratorMethod
                | LiteralTag::AsyncGeneratorMethod
                | LiteralTag::Getter
                | LiteralTag::Setter
                | LiteralTag::Accessor,
            ) => LiteralValue::Method(EntityId(self.as_u32())),
            Some(LiteralTag::MethodAffiliate) => LiteralValue::MethodAffiliate(self.as_u16()),
            Some(LiteralTag::NullValue) => LiteralValue::Null,
            Some(LiteralTag::TagValue) => LiteralValue::TagValue(self.as_u32()),
            _ => LiteralValue::TagValue(self.as_u32()),
        }
    }
}

/// A typed literal value (high-level interpretation of [`LiteralVal`]).
#[derive(Debug, Clone)]
pub enum LiteralValue {
    Bool(bool),
    Integer(i64),
    Float(f32),
    Double(f64),
    String(EntityId),
    Method(EntityId),
    Null,
    MethodAffiliate(u16),
    TagValue(u32),
}

/// A parsed literal array (collection of tag-value pairs).
#[derive(Debug, Clone)]
pub struct LiteralArray {
    pub entries: Vec<(LiteralTag, LiteralValue)>,
}

/// A literal data accessor. Borrows from a [`File`].
pub struct Literal<'f> {
    handle: *mut abcd_file_sys::AbcLiteralAccessor,
    file: &'f File,
    off: EntityId,
}

unsafe extern "C" fn literal_val_cb(
    val: *const abcd_file_sys::AbcLiteralVal,
    ctx: *mut std::ffi::c_void,
) {
    unsafe {
        let v = &mut *(ctx as *mut Vec<LiteralVal>);
        let lv = &*val;
        let str_data = if !lv.str_data.is_null() {
            // SAFETY: The C++ side returns a null-terminated MUTF-8 string.
            let cstr = CStr::from_ptr(lv.str_data as *const std::ffi::c_char);
            let bytes = cstr.to_bytes();
            String::from_utf8_lossy(bytes).into_owned().into()
        } else {
            None
        };
        v.push(LiteralVal {
            tag: LiteralTag::from_u8(lv.tag),
            u64_val: lv.__bindgen_anon_1.u64_val,
            str_data,
            str_utf16_len: lv.str_utf16_len,
        });
    }
}

impl<'f> Literal<'f> {
    pub(crate) fn open(file: &'f File, literal_data_off: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_literal_open(file.handle(), literal_data_off.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_literal_open failed at offset {literal_data_off:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: literal_data_off,
        })
    }

    /// The offset in the ABC file where this literal was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn count(&self) -> u32 {
        unsafe { abcd_file_sys::abc_literal_count(self.handle) }
    }

    pub fn vals_num(&self, array_off: EntityId) -> u32 {
        unsafe { abcd_file_sys::abc_literal_get_vals_num(self.handle, array_off.0) }
    }

    pub fn vals_num_by_index(&self, index: u32) -> u32 {
        unsafe { abcd_file_sys::abc_literal_get_vals_num_by_index(self.handle, index) }
    }

    pub fn array_id(&self, index: u32) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_literal_get_array_id(self.handle, index) })
    }

    pub fn enumerate_vals(&self, array_off: EntityId) -> Vec<LiteralVal> {
        let mut vals = Vec::new();
        unsafe {
            abcd_file_sys::abc_literal_enumerate_vals(
                self.handle,
                array_off.0,
                Some(literal_val_cb),
                &mut vals as *mut Vec<LiteralVal> as *mut std::ffi::c_void,
            );
        }
        vals
    }

    pub fn enumerate_vals_by_index(&self, index: u32) -> Vec<LiteralVal> {
        let mut vals = Vec::new();
        unsafe {
            abcd_file_sys::abc_literal_enumerate_vals_by_index(
                self.handle,
                index,
                Some(literal_val_cb),
                &mut vals as *mut Vec<LiteralVal> as *mut std::ffi::c_void,
            );
        }
        vals
    }

    pub fn resolve_index(&self, entity_off: EntityId) -> Option<u32> {
        let idx = unsafe { abcd_file_sys::abc_literal_resolve_index(self.handle, entity_off.0) };
        if idx == u32::MAX { None } else { Some(idx) }
    }

    pub fn data_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_literal_get_data_id(self.handle) })
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Literal<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_literal_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Literal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Literal")
            .field("offset", &self.off)
            .finish()
    }
}
