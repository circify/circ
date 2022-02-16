//! FHE
pub mod output;
pub mod trans;

#[derive(Clone, Debug)]
/// FHE program
/// The FHE program consists of two functions: main, and server_call
///
/// int main(): Acts as the client.
///     - Sets up the seal parameters
///     - Encrypts the private inputs
///     - Calls the server({params}) with the ctext and ptext parameters
///     - Decrypts the output from the server call
///     - Runs post computations
///
/// Ciphertext server(): Acts as the server
///     - Runs computations on homomorphically encrypted inputs
///
/// The FHE program consists of 5 Vec<String>:
///     header_inputs, server, setup, call_inputs, and post_computation
///
/// *header_inputs* holds the code of the input list for the header of server()
/// *server* holds the lowered code from the IR to FHE, which is the body of server()
/// *setup* holds the code for setting up SEAL params and encrypted data in main()
/// *call_inputs* holds the code of the input list for the call to server() in main()
/// *post_computation* holds the code that runs after the server() output has been decrypted
pub struct FHE {
    header_inputs: Vec<String>,
    server: Vec<String>,
    setup: Vec<String>,
    call_inputs: Vec<String>,
    post_computation: Vec<String>,
    main_inputs: Vec<String>,
}

impl Default for FHE {
    fn default() -> Self {
        Self::new()
    }
}

impl FHE {
    /// Initialize FHE circuit
    pub fn new() -> Self {
        FHE {
            header_inputs: Vec::new(),
            server: Vec::new(),
            setup: Vec::new(),
            call_inputs: Vec::new(),
            post_computation: Vec::new(),
            main_inputs: Vec::new(),
        }
    }
}
