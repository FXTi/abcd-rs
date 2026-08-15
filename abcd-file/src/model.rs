//! Data structures for a fully-decoded ABC file.
//!
//! Every field is owned — no lifetimes, no raw pointers.

use std::collections::{BTreeMap, HashMap};

use abcd_isa::Version;

use crate::FileType;
use crate::types::{AccessFlags, FunctionKind, HasAccessFlags, SourceLang, Type};
use crate::{StringId, StringPool};

// Re-export leaf types that are already owned.
pub use crate::annotation::{
    AnnotationElem, AnnotationValue, MethodHandleType, ResolvedMethodHandle,
};
pub use crate::code::{CatchBlock, TryBlock};
pub use crate::debug::{ColumnEntry, LineEntry, LocalVarInfo, ParamInfo};
pub use crate::literal::{LiteralArrayIdx, LiteralValue};
pub use crate::module::{ModuleData, ModuleRecord};
pub use abcd_isa::{Bytecode, DecodeError};

// ---------------------------------------------------------------------------
// Data structures
// ---------------------------------------------------------------------------

/// Fully-decoded ABC file.
#[derive(Clone, Debug)]
pub struct File {
    pub version: Version,
    pub checksum: u32,
    pub size: u32,
    pub file_type: FileType,
    /// String interner — all string data lives here.
    pub strings: StringPool,
    /// Classes keyed by interned descriptor (e.g. `"L_GLOBAL;"`).
    pub classes: BTreeMap<StringId, Class>,
    /// Literal arrays (indexed by position in the file).
    pub literal_arrays: Vec<LiteralArray>,
    /// offset → interned name/descriptor, for resolving bytecode `EntityId` operands.
    pub entity_map: HashMap<u32, StringId>,
}

/// A decoded class with nested methods, fields, and annotations.
#[derive(Clone, Debug)]
pub struct Class {
    pub descriptor: StringId,
    pub name: StringId,
    pub access_flags: AccessFlags,
    pub source_lang: SourceLang,
    pub source_file: Option<StringId>,
    pub is_external: bool,
    pub super_class: Option<StringId>,
    pub interfaces: Vec<StringId>,
    pub methods: Vec<Method>,
    pub fields: Vec<Field>,
    pub annotations: Annotations,
}

/// A decoded method.
#[derive(Clone, Debug)]
pub struct Method {
    pub name: StringId,
    pub access_flags: AccessFlags,
    pub function_kind: FunctionKind,
    pub source_lang: SourceLang,
    pub is_external: bool,
    pub return_type: Option<Type>,
    pub arg_types: Vec<Type>,
    pub body: Option<MethodBody>,
    pub annotations: Annotations,
    pub debug: Option<MethodDebugInfo>,
}

/// A decoded field.
#[derive(Clone, Debug)]
pub struct Field {
    pub name: StringId,
    pub field_type: Type,
    pub access_flags: AccessFlags,
    pub is_external: bool,
    pub initial_value: Option<FieldValue>,
    pub annotations: Annotations,
}

/// Initial value of a field.
#[derive(Clone, Debug)]
pub enum FieldValue {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

/// Decoded method body (bytecodes + exception handlers).
#[derive(Clone, Debug)]
pub struct MethodBody {
    /// Number of virtual registers used by this method.
    pub num_vregs: u32,
    /// Number of arguments (including `this` for instance methods).
    pub num_args: u32,
    pub bytecodes: Vec<Bytecode>,
    pub try_blocks: Vec<TryBlock>,
}

/// Four kinds of annotations grouped by retention policy.
#[derive(Clone, Debug, Default)]
pub struct Annotations {
    pub compile_time: Vec<Annotation>,
    pub runtime: Vec<Annotation>,
    pub compile_time_type: Vec<Annotation>,
    pub runtime_type: Vec<Annotation>,
}

/// Trait for types that carry [`Annotations`].
pub trait HasAnnotations {
    fn annotations(&self) -> &Annotations;
    fn annotations_mut(&mut self) -> &mut Annotations;
}

/// A single decoded annotation.
#[derive(Clone, Debug, PartialEq)]
pub struct Annotation {
    pub class_descriptor: StringId,
    pub elements: Vec<AnnotationElem>,
}

/// Per-method debug information.
#[derive(Clone, Debug)]
pub struct MethodDebugInfo {
    pub source_file: Option<StringId>,
    pub source_code: Option<StringId>,
    pub line_table: Vec<LineEntry>,
    pub column_table: Vec<ColumnEntry>,
    pub local_vars: Vec<LocalVarInfo>,
    pub params: Vec<ParamInfo>,
}

/// Decoded literal array.
#[derive(Clone, Debug)]
pub struct LiteralArray {
    pub values: Vec<LiteralValue>,
}

// ---------------------------------------------------------------------------
// Convenience methods
// ---------------------------------------------------------------------------

impl File {
    /// Look up a class by interned descriptor.
    pub fn class(&self, descriptor: StringId) -> Option<&Class> {
        self.classes.get(&descriptor)
    }

    /// Look up a class by descriptor string (convenience).
    pub fn class_by_str(&self, descriptor: &str) -> Option<&Class> {
        let sid = self.strings.get(descriptor)?;
        self.classes.get(&sid)
    }

    /// Flat iterator over `(class_descriptor, method)` across all classes.
    pub fn all_methods(&self) -> impl Iterator<Item = (StringId, &Method)> {
        self.classes
            .iter()
            .flat_map(|(&desc, c)| c.methods.iter().map(move |m| (desc, m)))
    }

    /// Resolve a bytecode `EntityId` offset to an interned string id.
    pub fn resolve_entity(&self, id: u32) -> Option<StringId> {
        self.entity_map.get(&id).copied()
    }

    /// Resolve a bytecode `EntityId` offset to a name/descriptor string.
    pub fn resolve_entity_str(&self, id: u32) -> Option<&str> {
        let sid = self.entity_map.get(&id)?;
        self.strings.resolve(*sid)
    }

    /// Get a literal array by index (for resolving bytecode operands).
    pub fn literal_array(&self, index: usize) -> Option<&LiteralArray> {
        self.literal_arrays.get(index)
    }

    /// Decode module data from the literal array at the given index.
    ///
    /// Module data is stored as a special literal array in ABC files.
    /// Returns `Err` if the index is out of bounds or the data cannot be
    /// parsed as valid module data.
    pub fn decode_module(&self, index: usize) -> Result<ModuleData, crate::Error> {
        let la = self
            .literal_arrays
            .get(index)
            .ok_or_else(|| crate::Error::Malformed {
                field: "literal_array_index",
                context: format!("index {index} out of bounds"),
            })?;
        ModuleData::from_literal_values(&la.values)
    }
}

impl HasAccessFlags for Class {
    fn access_flags(&self) -> AccessFlags {
        self.access_flags
    }
}

impl HasAnnotations for Class {
    fn annotations(&self) -> &Annotations {
        &self.annotations
    }
    fn annotations_mut(&mut self) -> &mut Annotations {
        &mut self.annotations
    }
}

impl Class {
    /// Find a method by interned name within this class.
    pub fn method_by_name(&self, name: StringId) -> Option<&Method> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Find a method by name string (requires the string pool for lookup).
    pub fn method_by_name_str<'a>(&'a self, pool: &StringPool, name: &str) -> Option<&'a Method> {
        let sid = pool.get(name)?;
        self.methods.iter().find(|m| m.name == sid)
    }

    /// Find a field by interned name within this class.
    pub fn field_by_name(&self, name: StringId) -> Option<&Field> {
        self.fields.iter().find(|f| f.name == name)
    }

    /// Find a field by name string (requires the string pool for lookup).
    pub fn field_by_name_str<'a>(&'a self, pool: &StringPool, name: &str) -> Option<&'a Field> {
        let sid = pool.get(name)?;
        self.fields.iter().find(|f| f.name == sid)
    }

    /// Look up the super class in the given file.
    pub fn super_class_in<'a>(&self, file: &'a File) -> Option<&'a Class> {
        file.class(self.super_class?)
    }
}

impl HasAccessFlags for Method {
    fn access_flags(&self) -> AccessFlags {
        self.access_flags
    }
}

impl HasAnnotations for Method {
    fn annotations(&self) -> &Annotations {
        &self.annotations
    }
    fn annotations_mut(&mut self) -> &mut Annotations {
        &mut self.annotations
    }
}

impl HasAccessFlags for Field {
    fn access_flags(&self) -> AccessFlags {
        self.access_flags
    }
}

impl HasAnnotations for Field {
    fn annotations(&self) -> &Annotations {
        &self.annotations
    }
    fn annotations_mut(&mut self) -> &mut Annotations {
        &mut self.annotations
    }
}
