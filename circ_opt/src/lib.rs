//! Options for CirC.
//!
//! ## Contents
//!
//! * A type for circ options [CircOpt] containing fields for module options:
//!    * `r1cs`: [R1csOpt]
//!    * `datalog`: [DatalogOpt]
//!    * `zsharp`: [ZsharpOpt]
//!    * `c` : [COpt]
//!    * `field`: [FieldOpt]
//!    * `fmt`: [FmtOpt]
//!    * all options types implement:
//!       * std's [Default]
//!       * clap's [Args]; all options are settable by
//!          * environmental variable (SHOUTY_SNEK_CASE), e.g., `"R1CS_LC_ELIM_THRESH"`
//!          * long option (kebab-case), e.g., `"--r1cs-lc-elim-thresh"`
//!       * these a guaranteed to agree (and we test this)
//!
//! ## Constructing custom options in a compiler
//!
//! We recommend that compilers construct custom options using [`clap`][clap].
//! Simply use our (rexported) version of clap in your compiler ([crate::clap])
//! and include [CircOpt] in your [clap::Parser].
//!
//! ```rust
//! use circ_opt::{CircOpt, clap::Parser};
//!
//! #[derive(Parser, Debug)]
//! struct BinaryOpt {
//!     #[command(flatten)]
//!     pub circ: CircOpt,
//! }
//!
//! fn main() {
//!     let opt = BinaryOpt::parse();
//! }
//! ```
//!
//! [clap]: https://crates.io/crates/clap

use clap::{ArgAction, Args, ValueEnum};

use std::default::Default;

/// Re-export our version of clap.
pub use clap;

#[derive(Args, Debug, Clone, Default, PartialEq, Eq)]
/// Options that configure CirC
pub struct CircOpt {
    /// Options for the R1cs backend
    #[command(flatten)]
    pub r1cs: R1csOpt,
    /// Options for the prime field used
    #[command(flatten)]
    pub field: FieldOpt,
    /// Options for the IR itself
    #[command(flatten)]
    pub ir: IrOpt,
    /// Options for RAM optimization
    #[command(flatten)]
    pub ram: RamOpt,
    /// Options for term formatting
    #[command(flatten)]
    pub fmt: FmtOpt,
    /// Options for the Z# frontend
    #[command(flatten)]
    pub zsharp: ZsharpOpt,
    /// Options for the datalog frontend
    #[command(flatten)]
    pub datalog: DatalogOpt,
    /// Options for C frontend
    #[command(flatten)]
    pub c: COpt,
}

/// Options for the R1cs backend
#[derive(Args, Debug, Clone, PartialEq, Eq)]
pub struct R1csOpt {
    /// Use the verified field-blaster
    #[arg(long = "r1cs-verified", env = "R1CS_VERIFIED", action = ArgAction::Set, default_value = "false")]
    pub verified: bool,

    /// Profile the R1CS lowering pass: attributing cosntraints and vars to terms
    #[arg(long = "r1cs-profile", env = "R1CS_PROFILE", action = ArgAction::Set, default_value = "false")]
    pub profile: bool,

    /// Which field division-by-zero semantics to encode in R1cs
    #[arg(
        long = "r1cs-div-by-zero",
        env = "R1CS_DIV_BY_ZERO",
        value_enum,
        default_value = "incomplete"
    )]
    pub div_by_zero: FieldDivByZero,

    #[arg(
        long = "r1cs-lc-elim-thresh",
        env = "R1CS_LC_ELIM_THRESH",
        default_value = "50"
    )]
    /// linear combination constraints up to this size will be eliminated
    pub lc_elim_thresh: usize,
}

impl Default for R1csOpt {
    fn default() -> Self {
        Self {
            verified: false,
            profile: false,
            div_by_zero: FieldDivByZero::Incomplete,
            lc_elim_thresh: 50,
        }
    }
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// Which field division-by-zero semantics to encode in R1cs
pub enum FieldDivByZero {
    /// Division-by-zero renders the circuit incomplete
    Incomplete,
    /// Division-by-zero gives zero
    Zero,
    /// Division-by-zero gives a per-division unspecified result
    NonDet,
}

impl Default for FieldDivByZero {
    fn default() -> Self {
        FieldDivByZero::Incomplete
    }
}

/// Options for the prime field used
#[derive(Args, Debug, Default, Clone, PartialEq, Eq)]
pub struct FieldOpt {
    /// Which field to use
    #[arg(
        long = "field-builtin",
        env = "FIELD_BUILTIN",
        value_enum,
        default_value = "bls12381"
    )]
    pub builtin: BuiltinField,

    /// Which modulus to use (overrides [FieldOpt::builtin])
    #[arg(
        long = "field-custom-modulus",
        env = "FIELD_CUSTOM_MODULUS",
        default_value = ""
    )]
    pub custom_modulus: String,
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// Which field to use
pub enum BuiltinField {
    /// BLS12-381 scalar field
    Bls12381,
    /// BN-254 scalar field
    Bn254,
}

impl Default for BuiltinField {
    fn default() -> Self {
        BuiltinField::Bls12381
    }
}

/// Options for the prime field used
#[derive(Args, Debug, Default, Clone, PartialEq, Eq)]
pub struct IrOpt {
    /// Which field to use
    #[arg(
        long = "ir-field-to-bv",
        env = "IR_FIELD_TO_BV",
        value_enum,
        default_value = "wrap"
    )]
    pub field_to_bv: FieldToBv,
    /// Garbage collection after each optimization pass.
    #[arg(
        long = "ir-frequent-gc",
        env = "IR_FREQUENT_GC",
        action = ArgAction::Set,
        default_value = "false"
    )]
    pub frequent_gc: bool,
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// When evaluating IR, if a field element x >= 2^b is converted to a length-b bit-vector, the
/// result should be
pub enum FieldToBv {
    /// x % 2^b
    Wrap,
    /// a panic
    Panic,
}

impl Default for FieldToBv {
    fn default() -> Self {
        FieldToBv::Wrap
    }
}

/// Options related to memory.
#[derive(Args, Debug, Default, Clone, PartialEq, Eq)]
pub struct RamOpt {
    /// Whether to use advanced RAM techniques
    #[arg(
        long = "ram",
        env = "RAM",
        action = ArgAction::Set,
        default_value = "false"
    )]
    pub enabled: bool,
    /// How to argue that values are in a range
    #[arg(
        long = "ram-range",
        env = "RAM_RANGE",
        value_enum,
        default_value = "sort"
    )]
    pub range: RangeStrategy,
    /// How to argue that indices are only repeated in blocks.
    #[arg(
        long = "ram-index",
        env = "RAM_INDEX",
        value_enum,
        default_value = "uniqueness"
    )]
    pub index: IndexStrategy,
    /// How to argue that indices are only repeated in blocks.
    #[arg(
        long = "ram-permutation",
        env = "RAM_PERMUTATION",
        value_enum,
        default_value = "msh"
    )]
    pub permutation: PermutationStrategy,
    /// ROM approach
    #[arg(
        long = "ram-rom",
        env = "RAM_ROM",
        value_enum,
        default_value = "haboeck"
    )]
    pub rom: RomStrategy,
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// How to argue that values are in a range
pub enum RangeStrategy {
    /// Bit-split them.
    BitSplit,
    /// Add the whole range & sort all values.
    Sort,
}

impl Default for RangeStrategy {
    fn default() -> Self {
        RangeStrategy::Sort
    }
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// How to argue that indices are only repeated in blocks.
pub enum IndexStrategy {
    /// Check that the blocks are sorted
    Sort,
    /// Use the GCD-derivative uniqueness argument
    Uniqueness,
}

impl Default for IndexStrategy {
    fn default() -> Self {
        IndexStrategy::Uniqueness
    }
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// How to argue that accesses have been permuted
pub enum PermutationStrategy {
    /// Use the AS-Waksman network
    Waksman,
    /// Use the (keyed) multi-set hash
    Msh,
}

impl Default for PermutationStrategy {
    fn default() -> Self {
        PermutationStrategy::Msh
    }
}

#[derive(ValueEnum, Debug, PartialEq, Eq, Clone, Copy)]
/// How to argue that accesses have been permuted
pub enum RomStrategy {
    /// Use Haboeck's argument
    Haboeck,
    /// Use permute-and-check
    Permute,
}

impl Default for RomStrategy {
    fn default() -> Self {
        RomStrategy::Haboeck
    }
}

/// Options for the prime field used
#[derive(Args, Debug, Clone, PartialEq, Eq)]
pub struct FmtOpt {
    /// Which field to use
    #[arg(
        long = "fmt-use-default-field",
        env = "FMT_USE_DEFAULT_FIELD",
        action = ArgAction::Set,
        default_value = "true")]
    pub use_default_field: bool,
    /// Always hide the field
    #[arg(
        long = "fmt-hide-field",
        env = "FMT_HIDE_FIELD",
        action = ArgAction::Set,
        default_value = "false")]
    pub hide_field: bool,
}

impl Default for FmtOpt {
    fn default() -> Self {
        Self {
            use_default_field: true,
            hide_field: false,
        }
    }
}

/// Options for the datalog frontend
#[derive(Args, Debug, Default, Clone, PartialEq, Eq)]
pub struct ZsharpOpt {
    /// In Z#, "isolate" assertions. That is, assertions in if/then/else expressions only take
    /// effect if that branch is active.
    ///
    /// See `--branch-isolation` in
    /// [ZoKrates](https://zokrates.github.io/language/control_flow.html).
    #[arg(long = "zsharp-isolate-asserts", env = "ZSHARP_ISOLATE_ASSERTS", action = ArgAction::Set, default_value = "false")]
    pub isolate_asserts: bool,
}

/// Options for the datalog frontend
#[derive(Args, Debug, Clone, PartialEq, Eq)]
pub struct DatalogOpt {
    /// How many recursions to allow
    #[arg(
        long = "datalog-rec-limit",
        env = "DATALOG_REC_LIMIT",
        name = "N",
        default_value = "5"
    )]
    pub rec_limit: usize,

    /// Lint recursions that are allegedly primitive recursive
    #[arg(long = "datalog-lint-prim-rec", env = "DATALOG_LINT_PRIM_REC", action = ArgAction::Set, default_value = "false")]
    pub lint_prim_rec: bool,
}

impl Default for DatalogOpt {
    fn default() -> Self {
        Self {
            rec_limit: 5,
            lint_prim_rec: false,
        }
    }
}

/// Options for the C frontend
#[derive(Args, Debug, Default, Clone, PartialEq, Eq)]
pub struct COpt {
    /// Enable SV competition builtin functions
    #[arg(long = "c-sv-functions", env = "C_SV_FUNCTIONS", action = ArgAction::SetTrue, default_value = "false")]
    pub sv_functions: bool,

    /// Assert no undefined behavior
    #[arg(long = "c-assert-no-ub", env = "C_ASSERT_NO_UB", action = ArgAction::SetTrue, default_value = "false")]
    pub assert_no_ub: bool,
}

#[cfg(test)]
mod test {

    use super::*;

    use clap::{CommandFactory, Parser};
    use heck::{ToKebabCase, ToShoutySnekCase};

    #[derive(Parser, Debug)]
    struct BinaryOpt {
        #[command(flatten)]
        pub circ: CircOpt,
    }

    #[test]
    fn std_and_clap_defaults_agree() {
        let std_default: CircOpt = Default::default();
        let clap_default: CircOpt = BinaryOpt::parse_from::<_, &str>(std::iter::empty()).circ;
        assert_eq!(std_default, clap_default);
    }

    #[test]
    fn long_and_env_names_agree() {
        for arg in BinaryOpt::command().get_arguments() {
            if let Some(long_name) = arg.get_long() {
                if let Some(env_name) = arg.get_env() {
                    let env_name = env_name.to_str().unwrap();
                    assert_eq!(
                        env_name,
                        long_name.TO_SHOUTY_SNEK_CASE(),
                        "The long name\n    '{}'\ndoes not match the envvar name\n    '{}'\n",
                        long_name,
                        env_name,
                    );
                    assert_eq!(
                        env_name,
                        env_name.TO_SHOUTY_SNEK_CASE(),
                        "The envvar name '{}' is not in SHOUTY_SNEK_CASE",
                        env_name,
                    );
                    assert_eq!(
                        long_name,
                        long_name.to_kebab_case(),
                        "The long name '{}' is not in kebab-case",
                        long_name,
                    );
                } else {
                    panic!("Long option '{}' has no envvar", long_name);
                }
            } else if let Some(env_name) = arg.get_env() {
                let env_name = env_name.to_str().unwrap();
                panic!("Envar option '{}' has no long_name", env_name);
            }
        }
    }
}
