//! Heap Size helpers for use with [datasize].

use rug::Integer;

/// Measure memory footprint of an integer
pub fn estimate_heap_size_integer(i: &Integer) -> usize {
    // a guess
    i.capacity() / 8
}
