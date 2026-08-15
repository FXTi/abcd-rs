use crate::error::ParseError;
use crate::string_table::read_string;

/// Parsed module record from an ABC file.
#[derive(Debug, Clone)]
pub struct ModuleRecord {
    pub module_requests: Vec<String>,
    pub regular_imports: Vec<RegularImport>,
    pub namespace_imports: Vec<NamespaceImport>,
    pub local_exports: Vec<LocalExport>,
    pub indirect_exports: Vec<IndirectExport>,
    pub star_exports: Vec<StarExport>,
}

#[derive(Debug, Clone)]
pub struct RegularImport {
    pub local_name: String,
    pub import_name: String,
    pub module_request_idx: u16,
}

#[derive(Debug, Clone)]
pub struct NamespaceImport {
    pub local_name: String,
    pub module_request_idx: u16,
}

#[derive(Debug, Clone)]
pub struct LocalExport {
    pub local_name: String,
    pub export_name: String,
}

#[derive(Debug, Clone)]
pub struct IndirectExport {
    pub export_name: String,
    pub import_name: String,
    pub module_request_idx: u16,
}

#[derive(Debug, Clone)]
pub struct StarExport {
    pub module_request_idx: u16,
}

impl ModuleRecord {
    /// Parse a module record at the given offset in the ABC file.
    /// The offset points to a module literal array.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        // Skip literal_num (4 bytes)
        if pos + 4 > data.len() {
            return Err(ParseError::OffsetOutOfBounds(pos, data.len()));
        }
        pos += 4;

        // num_module_requests (4 bytes)
        let num_requests = read_u32(data, &mut pos)?;

        // Module request string offsets
        let mut module_requests = Vec::with_capacity(num_requests as usize);
        for _ in 0..num_requests {
            let str_off = read_u32(data, &mut pos)?;
            let s = read_string(data, str_off as usize).unwrap_or_default();
            module_requests.push(s);
        }

        // Regular imports
        let num_regular = read_u32(data, &mut pos)?;
        let mut regular_imports = Vec::with_capacity(num_regular as usize);
        for _ in 0..num_regular {
            let local_name_off = read_u32(data, &mut pos)?;
            let import_name_off = read_u32(data, &mut pos)?;
            let module_request_idx = read_u16(data, &mut pos)?;
            regular_imports.push(RegularImport {
                local_name: read_string(data, local_name_off as usize).unwrap_or_default(),
                import_name: read_string(data, import_name_off as usize).unwrap_or_default(),
                module_request_idx,
            });
        }

        // Namespace imports
        let num_namespace = read_u32(data, &mut pos)?;
        let mut namespace_imports = Vec::with_capacity(num_namespace as usize);
        for _ in 0..num_namespace {
            let local_name_off = read_u32(data, &mut pos)?;
            let module_request_idx = read_u16(data, &mut pos)?;
            namespace_imports.push(NamespaceImport {
                local_name: read_string(data, local_name_off as usize).unwrap_or_default(),
                module_request_idx,
            });
        }

        // Local exports
        let num_local_exports = read_u32(data, &mut pos)?;
        let mut local_exports = Vec::with_capacity(num_local_exports as usize);
        for _ in 0..num_local_exports {
            let local_name_off = read_u32(data, &mut pos)?;
            let export_name_off = read_u32(data, &mut pos)?;
            local_exports.push(LocalExport {
                local_name: read_string(data, local_name_off as usize).unwrap_or_default(),
                export_name: read_string(data, export_name_off as usize).unwrap_or_default(),
            });
        }

        // Indirect exports
        let num_indirect = read_u32(data, &mut pos)?;
        let mut indirect_exports = Vec::with_capacity(num_indirect as usize);
        for _ in 0..num_indirect {
            let export_name_off = read_u32(data, &mut pos)?;
            let import_name_off = read_u32(data, &mut pos)?;
            let module_request_idx = read_u16(data, &mut pos)?;
            indirect_exports.push(IndirectExport {
                export_name: read_string(data, export_name_off as usize).unwrap_or_default(),
                import_name: read_string(data, import_name_off as usize).unwrap_or_default(),
                module_request_idx,
            });
        }

        // Star exports
        let num_star = read_u32(data, &mut pos)?;
        let mut star_exports = Vec::with_capacity(num_star as usize);
        for _ in 0..num_star {
            let module_request_idx = read_u16(data, &mut pos)?;
            star_exports.push(StarExport { module_request_idx });
        }

        Ok(ModuleRecord {
            module_requests,
            regular_imports,
            namespace_imports,
            local_exports,
            indirect_exports,
            star_exports,
        })
    }
}

fn read_u32(data: &[u8], pos: &mut usize) -> Result<u32, ParseError> {
    if *pos + 4 > data.len() {
        return Err(ParseError::OffsetOutOfBounds(*pos, data.len()));
    }
    let val = u32::from_le_bytes(data[*pos..*pos + 4].try_into().unwrap());
    *pos += 4;
    Ok(val)
}

fn read_u16(data: &[u8], pos: &mut usize) -> Result<u16, ParseError> {
    if *pos + 2 > data.len() {
        return Err(ParseError::OffsetOutOfBounds(*pos, data.len()));
    }
    let val = u16::from_le_bytes(data[*pos..*pos + 2].try_into().unwrap());
    *pos += 2;
    Ok(val)
}
