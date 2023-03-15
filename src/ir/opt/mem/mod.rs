//! Memory optimizations

/// Oblivious array elimination.
///
/// Replace arrays with tuples, using ITEs to handle variable indexing.
pub mod lin;
/// Oblivious array elimination.
///
/// Replace arrays that are accessed at constant indices with tuples.
pub mod obliv;
/// RAM extraction techniques
pub mod ram;
