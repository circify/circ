//! # CirC
//!
//! A compiler infrastructure for compiling programs to circuits

#![feature(drain_filter)]
#![feature(box_patterns)]
#![warn(missing_docs)]

#[macro_use]
pub mod ir;
pub mod circify;
pub mod front;
pub mod target;
pub mod util;
