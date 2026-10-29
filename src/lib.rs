//! # CirC
//!
//! A compiler infrastructure for compiling programs to circuits

#![warn(missing_docs)]
#![deny(warnings)]
#![allow(rustdoc::private_intra_doc_links)]
#![allow(clippy::mutable_key_type)]
#![allow(clippy::manual_filter)]
#![allow(clippy::single_element_loop)]
#![allow(clippy::useless_borrows_in_formatting)]

#[macro_use]
pub mod ir;
pub mod cfg;
pub mod circify;
#[cfg(feature = "r1cs")]
pub mod compile;
pub mod front;
pub mod target;
pub mod util;

/// Orchestrates the ZoKratesCurly `@test` pipeline (frontend -> compile ->
/// proof backend). Gated on the features it needs: the SMT frontend, the curly
/// frontend, and R1CS.
#[cfg(all(feature = "smt", feature = "zokc", feature = "r1cs"))]
pub mod test_runner;
