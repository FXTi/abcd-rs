//! IR type system covering both dynamic JS/TS and ArkTS static types.

use abcd_file::Type as AbcType;

/// IR type: supports both the dynamic JS type lattice and ArkTS static types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IrType {
    /// Dynamic type lattice (bitmask), used for JS/TS values.
    Dynamic(DynType),
    /// Static type from ArkTS method signatures (delegates to `abcd_file::Type`).
    Static(AbcType),
}

impl Default for IrType {
    fn default() -> Self {
        IrType::Dynamic(DynType::ANY)
    }
}

/// Bitmask-based JavaScript type lattice.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DynType(pub u16);

impl DynType {
    pub const NONE: Self = Self(0);
    pub const EMPTY: Self = Self(1 << 0); // TDZ
    pub const UNDEFINED: Self = Self(1 << 1);
    pub const NULL: Self = Self(1 << 2);
    pub const BOOLEAN: Self = Self(1 << 3);
    pub const NUMBER: Self = Self(1 << 4);
    pub const STRING: Self = Self(1 << 5);
    pub const BIGINT: Self = Self(1 << 6);
    pub const SYMBOL: Self = Self(1 << 7);
    pub const OBJECT: Self = Self(1 << 8);
    pub const ENVIRONMENT: Self = Self(1 << 9);

    pub const ANY: Self = Self(
        Self::UNDEFINED.0
            | Self::NULL.0
            | Self::BOOLEAN.0
            | Self::NUMBER.0
            | Self::STRING.0
            | Self::BIGINT.0
            | Self::SYMBOL.0
            | Self::OBJECT.0,
    );

    #[inline]
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    #[inline]
    pub fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
    #[inline]
    pub fn is_subset_of(self, other: Self) -> bool {
        (self.0 & !other.0) == 0
    }
    #[inline]
    pub fn can_be(self, ty: Self) -> bool {
        (self.0 & ty.0) != 0
    }
    #[inline]
    pub fn is_none(self) -> bool {
        self.0 == 0
    }
}

impl std::fmt::Debug for DynType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self == Self::ANY {
            return write!(f, "any");
        }
        let mut first = true;
        let flags = [
            (Self::EMPTY, "empty"),
            (Self::UNDEFINED, "undefined"),
            (Self::NULL, "null"),
            (Self::BOOLEAN, "boolean"),
            (Self::NUMBER, "number"),
            (Self::STRING, "string"),
            (Self::BIGINT, "bigint"),
            (Self::SYMBOL, "symbol"),
            (Self::OBJECT, "object"),
            (Self::ENVIRONMENT, "environment"),
        ];
        for (flag, name) in flags {
            if self.can_be(flag) {
                if !first {
                    write!(f, "|")?;
                }
                write!(f, "{name}")?;
                first = false;
            }
        }
        if first {
            write!(f, "none")?;
        }
        Ok(())
    }
}
