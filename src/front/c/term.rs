//! C Terms

use crate::ir::term::*;

pub enum CTermData {
    CBool, 
    CInt(Bool, usize)
}   


#[derive(Eq)]
pub struct CTerm {
    term: CTermData,
    udef: Bool, 
}
