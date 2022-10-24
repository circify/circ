use super::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;

/// Computations are expressed in terms of arithmetic circuits, in particular
/// rank-1 quadratic constraint systems. The `Circuit` trait represents a
/// circuit that can be synthesized. The `synthesize` method is called during
/// CRS generation and during proving.
pub trait RandomCircuit<Scalar: PrimeField> {
    /// Synthesize the circuit into a rank-1 quadratic constraint system
    fn synthesize<CS: RandomConstraintSystem<Scalar>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>;
}

/// Represents a constraint system which can have new variables
/// allocated and constrains between them formed.
pub trait RandomConstraintSystem<Scalar: PrimeField>: Sized + ConstraintSystem<Scalar> {
    fn alloc_random_coin<A, AR>(
        &mut self,
        annotation: A,
    ) -> Result<(Variable, Scalar), SynthesisError>
    where
        A: FnOnce() -> AR,
        AR: Into<String>;
}
