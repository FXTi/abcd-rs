use crate::error::Error;
use crate::literal::LiteralValue;

/// A single module record entry with interned strings.
///
/// Each variant carries only the fields present for that record kind.
/// Variants correspond to the vendored `panda_file::ModuleTag` values
/// (vendor `module_data_accessor.h`); the raw tag never crosses into Rust.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleRecord {
    RegularImport {
        local_name: crate::StringId,
        import_name: crate::StringId,
        module_request_idx: u32,
    },
    NamespaceImport {
        local_name: crate::StringId,
        module_request_idx: u32,
    },
    LocalExport {
        local_name: crate::StringId,
        export_name: crate::StringId,
    },
    IndirectExport {
        export_name: crate::StringId,
        import_name: crate::StringId,
        module_request_idx: u32,
    },
    StarExport {
        module_request_idx: u32,
    },
}

/// Decoded module data (import/export declarations for an ES module).
///
/// On disk the module data is an UNTAGGED literal-array item read through
/// the vendored `ModuleDataAccessor` (request count + request strings, then
/// per-tag section counts and entries; vendor `module_data_accessor-inl.h`).
/// `_ESModuleRecord` record fields reference the blob by file offset; decode
/// surfaces them as [`crate::FieldValue::ModuleData`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleData {
    /// Offset of the module blob in the source file; 0 for hand-built
    /// models. Re-emission relocates the blob, so this is informational.
    pub source_offset: u32,
    /// Module request strings (paths of imported modules).
    pub requests: Vec<crate::StringId>,
    /// Import/export records in vendored section order.
    pub records: Vec<ModuleRecord>,
}

impl ModuleData {
    /// Parse module data from a flat slice of decoded literal values.
    ///
    /// The expected layout matches the ArkCompiler module literal array format:
    /// counts as `Integer`, strings as `String`, module indices as `MethodAffiliate`.
    ///
    /// Note: this parses the *tagged* pandasm-level representation. Real
    /// on-disk module blobs are untagged and surface through
    /// [`crate::FieldValue::ModuleData`] instead.
    pub fn from_literal_values(values: &[LiteralValue]) -> Result<Self, Error> {
        let mut cur = Cursor { values, pos: 0 };

        // Module requests.
        let n = cur.read_u32("module_requests_count")?;
        let mut requests = Vec::with_capacity(n as usize);
        for _ in 0..n {
            requests.push(cur.read_string_id("module_request")?);
        }

        let mut records = Vec::new();

        // Regular imports: [local_name, import_name, module_idx] × N
        let n = cur.read_u32("regular_import_count")?;
        for _ in 0..n {
            let local_name = cur.read_string_id("regular_import.local_name")?;
            let import_name = cur.read_string_id("regular_import.import_name")?;
            let module_request_idx = cur.read_u16("regular_import.module_idx")? as u32;
            records.push(ModuleRecord::RegularImport {
                local_name,
                import_name,
                module_request_idx,
            });
        }

        // Namespace imports: [local_name, module_idx] × N
        let n = cur.read_u32("namespace_import_count")?;
        for _ in 0..n {
            let local_name = cur.read_string_id("namespace_import.local_name")?;
            let module_request_idx = cur.read_u16("namespace_import.module_idx")? as u32;
            records.push(ModuleRecord::NamespaceImport {
                local_name,
                module_request_idx,
            });
        }

        // Local exports: [local_name, export_name] × N
        let n = cur.read_u32("local_export_count")?;
        for _ in 0..n {
            let local_name = cur.read_string_id("local_export.local_name")?;
            let export_name = cur.read_string_id("local_export.export_name")?;
            records.push(ModuleRecord::LocalExport {
                local_name,
                export_name,
            });
        }

        // Indirect exports: [export_name, import_name, module_idx] × N
        let n = cur.read_u32("indirect_export_count")?;
        for _ in 0..n {
            let export_name = cur.read_string_id("indirect_export.export_name")?;
            let import_name = cur.read_string_id("indirect_export.import_name")?;
            let module_request_idx = cur.read_u16("indirect_export.module_idx")? as u32;
            records.push(ModuleRecord::IndirectExport {
                export_name,
                import_name,
                module_request_idx,
            });
        }

        // Star exports: [module_idx] × N
        let n = cur.read_u32("star_export_count")?;
        for _ in 0..n {
            let module_request_idx = cur.read_u16("star_export.module_idx")? as u32;
            records.push(ModuleRecord::StarExport { module_request_idx });
        }

        Ok(ModuleData {
            source_offset: 0,
            requests,
            records,
        })
    }
}

// ---------------------------------------------------------------------------
// Internal cursor for walking a &[LiteralValue] sequentially
// ---------------------------------------------------------------------------

struct Cursor<'a> {
    values: &'a [LiteralValue],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn next(&mut self, ctx: &str) -> Result<&'a LiteralValue, Error> {
        let v = self.values.get(self.pos).ok_or_else(|| Error::Malformed {
            field: "module_data",
            context: format!("unexpected end at {ctx}"),
        })?;
        self.pos += 1;
        Ok(v)
    }

    fn read_u32(&mut self, ctx: &str) -> Result<u32, Error> {
        match self.next(ctx)? {
            LiteralValue::Integer(n) => Ok(*n),
            other => Err(Error::Malformed {
                field: "module_data",
                context: format!("expected Integer for {ctx}, got {other:?}"),
            }),
        }
    }

    fn read_string_id(&mut self, ctx: &str) -> Result<crate::StringId, Error> {
        match self.next(ctx)? {
            LiteralValue::String(sid) => Ok(*sid),
            other => Err(Error::Malformed {
                field: "module_data",
                context: format!("expected String for {ctx}, got {other:?}"),
            }),
        }
    }

    fn read_u16(&mut self, ctx: &str) -> Result<u16, Error> {
        match self.next(ctx)? {
            LiteralValue::MethodAffiliate(n) => Ok(*n),
            other => Err(Error::Malformed {
                field: "module_data",
                context: format!("expected MethodAffiliate for {ctx}, got {other:?}"),
            }),
        }
    }
}
