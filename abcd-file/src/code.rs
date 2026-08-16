/// Try-catch block information.
///
/// All indices/counts refer to positions in
/// [`MethodBody::bytecodes`](crate::MethodBody::bytecodes).
#[derive(Clone, Debug)]
pub struct TryBlock {
    /// Instruction index where the try region starts.
    pub start: u32,
    /// Number of instructions covered by the try region.
    pub len: u32,
    pub catches: Vec<CatchBlock>,
}

/// Catch handler information.
///
/// All indices/counts refer to positions in
/// [`MethodBody::bytecodes`](crate::MethodBody::bytecodes).
#[derive(Clone, Copy, Debug)]
pub struct CatchBlock {
    /// Class entity offset of the caught type; `u32::MAX` = catch-all.
    /// (The file stores a region class *index* + 1; decode resolves it to
    /// the entity offset so the model carries entity identity.)
    pub type_idx: u32,
    /// Instruction index where the catch handler starts.
    pub handler: u32,
    /// Number of instructions in the catch handler.
    pub len: u32,
}
