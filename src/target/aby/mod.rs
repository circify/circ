//! ABY

pub mod output;
pub mod trans;

#[derive(Clone, Debug)]
/// ABY.
pub struct ABY {
    setup: Vec<String>,
    circs: Vec<String>,
    closer: Vec<String>,
}

impl ABY {
    /// Make an empty constraint system.
    pub fn new() -> Self {
        ABY {
            setup: Vec::new(),
            circs: Vec::new(),
            closer: Vec::new(),
        }
    }
}
