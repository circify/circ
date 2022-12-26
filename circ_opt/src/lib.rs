//! Options for CirC.
//!
//! ## Contents
//!
//! * A type for circ options [CircOpt] containing fields for module options:
//!    * `r1cs`: [R1csOpt]
//!    * `datalog`: [DatalogOpt]
//!    * `zsharp`: [ZsharpOpt]
//!    * `field`: [FieldOpt]
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
    /// Options for the Z# frontend
    #[command(flatten)]
    pub zsharp: ZsharpOpt,
    /// Options for the datalog frontend
    #[command(flatten)]
    pub datalog: DatalogOpt,
}

/// Options for the R1cs backend
#[derive(Args, Debug, Clone, PartialEq, Eq)]
pub struct R1csOpt {
    /// Use the verified field-blaster
    #[arg(long = "r1cs-verified", env = "R1CS_VERIFIED", action = ArgAction::Set, default_value = "false")]
    pub verified: bool,

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
