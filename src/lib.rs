#![feature(or_insert_with_key)]
#![feature(drain_filter)]
#![feature(box_patterns)]
#![feature(move_ref_pattern)]

#[macro_use]
pub mod ir;
pub mod circify;
pub mod target;
pub mod util;
