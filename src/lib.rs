//! # CirC
//!
//! A compiler infrastructure for compiling programs to circuits

#![warn(missing_docs)]
#![deny(warnings)]
#![allow(unreachable_code, dead_code, unused)]

#[macro_use]
pub mod ir;
pub mod cfg;
pub mod circify;
pub mod front;
pub mod target;
pub mod util;
