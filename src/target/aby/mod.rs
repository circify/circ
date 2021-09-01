//! ABY
pub mod assignment;
pub mod output;
pub mod trans;

#[derive(Clone, Debug)]
/// ABY Circuit
/// The ABY Circuit consists of three Vec<String>: setup, circ, and closer
/// *setup* holds code for initializing the ABY party, sharing scheme, and input values
/// *circs* holds the lowered code from the IR to ABY Circuits
/// *output* holds the code for printing the output value
pub struct ABY {
    setup: Vec<String>,
    circs: Vec<String>,
    output: Vec<String>,
}

impl ABY {
    /// Initialize ABY circuit
    pub fn new() -> Self {
        ABY {
            setup: Vec::new(),
            circs: Vec::new(),
            output: Vec::new(),
        }
    }
}
