/// Line number entry.
#[derive(Clone, Copy, Debug)]
pub struct LineEntry {
    /// Instruction index in the method's bytecode sequence.
    pub index: u32,
    pub line: u32,
}

/// Column number entry.
#[derive(Clone, Copy, Debug)]
pub struct ColumnEntry {
    /// Instruction index in the method's bytecode sequence.
    pub index: u32,
    pub column: u32,
}

/// Local variable debug info.
#[derive(Clone, Copy, Debug)]
pub struct LocalVarInfo {
    pub name: crate::StringId,
    pub type_name: crate::StringId,
    pub type_signature: crate::StringId,
    pub reg_number: i32,
    /// Instruction index where this variable's scope starts.
    pub start: u32,
    /// Instruction index where this variable's scope ends.
    pub end: u32,
}

/// Parameter debug info.
#[derive(Clone, Copy, Debug)]
pub struct ParamInfo {
    pub name: crate::StringId,
    pub signature: crate::StringId,
}
