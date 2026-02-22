//! Code data accessor.

use crate::{EntityId, File, error::Error};

/// Try block info.
#[derive(Debug, Clone)]
pub struct TryBlock {
    pub start_pc: u32,
    pub length: u32,
    pub num_catches: u32,
    pub catches: Vec<CatchBlock>,
}

/// Catch block info.
#[derive(Debug, Clone)]
pub struct CatchBlock {
    pub type_idx: u32,
    pub handler_pc: u32,
    pub code_size: u32,
}

/// A code data accessor. Borrows from a [`File`].
pub struct Code<'f> {
    handle: *mut abcd_file_sys::AbcCodeAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Code<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_code_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_code_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this code block was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn num_vregs(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_num_vregs(self.handle) }
    }

    pub fn num_args(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_num_args(self.handle) }
    }

    pub fn code_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_code_size(self.handle) }
    }

    pub fn instructions(&self) -> &[u8] {
        let ptr = unsafe { abcd_file_sys::abc_code_instructions(self.handle) };
        if ptr.is_null() {
            return &[];
        }
        let size = self.code_size() as usize;
        unsafe { std::slice::from_raw_parts(ptr, size) }
    }

    pub fn tries_size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_tries_size(self.handle) }
    }

    pub fn try_blocks(&self) -> Vec<TryBlock> {
        let mut blocks = Vec::new();
        unsafe extern "C" fn cb(
            info: *const abcd_file_sys::AbcTryBlockInfo,
            catches: *const abcd_file_sys::AbcCatchBlockInfo,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                let v = &mut *(ctx as *mut Vec<TryBlock>);
                let ti = &*info;
                let catch_slice = std::slice::from_raw_parts(catches, ti.num_catches as usize);
                let catch_vec = catch_slice
                    .iter()
                    .map(|c| CatchBlock {
                        type_idx: c.type_idx,
                        handler_pc: c.handler_pc,
                        code_size: c.code_size,
                    })
                    .collect();
                v.push(TryBlock {
                    start_pc: ti.start_pc,
                    length: ti.length,
                    num_catches: ti.num_catches,
                    catches: catch_vec,
                });
            }
            0
        }
        unsafe {
            abcd_file_sys::abc_code_enumerate_try_blocks_full(
                self.handle,
                Some(cb),
                &mut blocks as *mut Vec<TryBlock> as *mut std::ffi::c_void,
            );
        }
        blocks
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_code_get_size(self.handle) }
    }

    pub fn code_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_code_get_code_id(self.handle) })
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Code<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_code_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Code<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Code").field("offset", &self.off).finish()
    }
}
