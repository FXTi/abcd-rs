//! EntityId resolution: bytecode EntityId → StringId / method references.
//!
//! Wraps `File::resolve_entity()` and interns the result into the module's
//! [`StringPool`].

use abcd_file::File;
use abcd_isa::EntityId;

use crate::entity::StringId;
use crate::module::Module;

/// Resolve an [`EntityId`] to a [`StringId`] by looking it up in the file's
/// entity map and interning the result.
///
/// Returns `None` if the entity cannot be resolved.
pub fn resolve_entity(file: &File, module: &mut Module, id: EntityId) -> Option<StringId> {
    let file_sid = file.resolve_entity(id.0)?;
    let name = file.strings.resolve(file_sid)?;
    Some(module.strings.intern(name))
}
