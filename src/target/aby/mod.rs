//! ABY
pub mod assignment;
pub mod output;
pub mod trans;


#[derive(Clone, Debug)]
/// ABY Circuit
/// The ABY Circuit consists of three Vec<String>: setup, circ, and closer
/// *setup* holds code for initializing the ABY party, sharing scheme, and input values
/// *circs* holds the lowered code from the IR to ABY Circuits
/// *closer* holds the code for executing the ABY Circuits and printing the output value
pub struct ABY {
    setup: Vec<String>,
    circs: Vec<String>,
    closer: Vec<String>,
}

impl ABY {
    /// Initialize ABY circuit
    pub fn new() -> Self {
        ABY {
            setup: Vec::new(),
            circs: Vec::new(),
            closer: Vec::new(),
        }
    }
}
