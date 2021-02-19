pub mod zokrates;
use super::ir::term::Constraints;

pub trait FrontEnd {
    type Inputs;
    fn gen(i: Self::Inputs) -> Constraints;
}
