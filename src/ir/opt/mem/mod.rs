//! Memory optimizations

/// Oblivious array elimination.
///
/// Replace arrays that are accessed at constant indices with tuples.
pub mod obliv;
/// Oblivious array elimination.
///
/// Replace arrays with tuples, using ITEs to handle variable indexing.
pub mod lin;
