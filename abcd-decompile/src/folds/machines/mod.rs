//! State-machine desugaring folds (`function*`, `async`, `async function*`, `yield*`).

pub(in crate::folds) mod async_fn;
pub(in crate::folds) mod async_gen;
pub(in crate::folds) mod generator;
pub(in crate::folds) mod yield_star;

pub use async_fn::{async_driver_fold, async_machine_fold};
pub use async_gen::async_generator_machine_fold;
pub use generator::generator_machine_fold;
pub use yield_star::yield_star_fold;
