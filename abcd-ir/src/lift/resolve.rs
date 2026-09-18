//! EntityId resolution: bytecode EntityId → StringId / method references.
//!
//! Wraps `File::resolve_entity()` and interns the result into the module's
//! [`StringPool`].

use abcd_file::{File, MethodBody};
use abcd_isa::{EntityId, EntityKind};

use crate::entity::StringId;
use crate::module::Module;

/// Resolve an [`EntityId`] through the owning method's typed index mapping,
/// then look up the offset in the file's name map.
///
/// Returns `None` if the entity cannot be resolved.
///
/// Only `EntityKind::StringId` resolutions are recorded into
/// `module.string_entities`: that map is name-keyed first-wins, which is
/// safe for strings (encode resolves string operands content-addressed, so
/// two offsets with equal content yield the same pool entry) but wrong for
/// methods — a method name can collide with a string of the same content,
/// and two distinct methods can share one name. Method identity is the
/// source offset; use [`resolve_method_entity`] for method references.
pub fn resolve_entity(
    file: &File,
    body: &MethodBody,
    module: &mut Module,
    id: EntityId,
    kind: EntityKind,
) -> Option<StringId> {
    let offset = body.entity_offsets.get(&(kind, id.0))?;
    let file_sid = file.resolve_entity(*offset)?;
    let name = file.strings.resolve(file_sid)?;
    let string_id = module.strings.intern(name);
    if kind == EntityKind::StringId {
        module
            .string_entities
            .entry(string_id)
            .or_insert(EntityId(*offset));
    }
    Some(string_id)
}

/// Resolve a method-reference [`EntityId`] to its display name AND its
/// precise source-file offset.
///
/// `body.entity_offsets[(MethodId, raw)]` gives the exact offset for THIS
/// use-site (decode records it per operand), so two same-named methods
/// referenced from one body resolve to their own offsets. The offset is the
/// identity the lowering/encode path keys on; the name is display-only.
pub fn resolve_method_entity(
    file: &File,
    body: &MethodBody,
    module: &mut Module,
    id: EntityId,
) -> Option<(StringId, u32)> {
    let offset = *body.entity_offsets.get(&(EntityKind::MethodId, id.0))?;
    let file_sid = file.resolve_entity(offset)?;
    let name = file.strings.resolve(file_sid)?;
    let string_id = module.strings.intern(name);
    Some((string_id, offset))
}

pub fn resolve_literal_array(file: &File, body: &MethodBody, id: EntityId) -> Option<u32> {
    let offset = *body
        .entity_offsets
        .get(&(EntityKind::LiteralarrayId, id.0))?;
    file.literal_array_offsets.get(&offset).copied()
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_file::{FileType, StringPool, Version};

    #[test]
    fn the_same_index_resolves_in_its_own_method_region() {
        let mut file = File {
            version: Version::new(12, 0, 6, 0),
            checksum: 0,
            size: 0,
            file_type: FileType::Dynamic,
            strings: StringPool::default(),
            classes: Default::default(),
            literal_arrays: vec![],
            entity_map: Default::default(),
            literal_array_offsets: Default::default(),
        };
        for (offset, name) in [
            (100, "first"),
            (200, "second"),
            (0, "wrong-offset-fallback"),
        ] {
            let sid = file.strings.get_or_intern(name);
            file.entity_map.insert(offset, sid);
        }
        let mut body = MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![],
            try_blocks: vec![],
            entity_offsets: [((EntityKind::MethodId, 0), 100)].into_iter().collect(),
        };
        let mut module = Module::new(file.version, file.file_type);
        let first =
            resolve_entity(&file, &body, &mut module, EntityId(0), EntityKind::MethodId).unwrap();
        assert_eq!(module.strings.get(first), "first");
        assert_eq!(
            module.string_entities.get(&first),
            None,
            "method-kind resolutions must not enter the string entity map"
        );
        let (method_name, method_offset) =
            resolve_method_entity(&file, &body, &mut module, EntityId(0)).unwrap();
        assert_eq!(module.strings.get(method_name), "first");
        assert_eq!(method_offset, 100);
        body.entity_offsets.insert((EntityKind::StringId, 0), 100);
        let as_string =
            resolve_entity(&file, &body, &mut module, EntityId(0), EntityKind::StringId).unwrap();
        assert_eq!(module.string_entities.get(&as_string), Some(&EntityId(100)));
        body.entity_offsets.insert((EntityKind::MethodId, 0), 200);
        let second =
            resolve_entity(&file, &body, &mut module, EntityId(0), EntityKind::MethodId).unwrap();
        assert_eq!(module.strings.get(second), "second");
        assert!(
            resolve_entity(
                &file,
                &body,
                &mut module,
                EntityId(0),
                EntityKind::LiteralarrayId
            )
            .is_none(),
            "a literal-array index must not alias a method index"
        );
        body.entity_offsets.clear();
        assert!(
            resolve_entity(&file, &body, &mut module, EntityId(0), EntityKind::MethodId).is_none()
        );
    }
}
