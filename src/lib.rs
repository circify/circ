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
pub mod front;
pub mod target;
pub mod util;
