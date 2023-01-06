//! CirC Configuration
//!
//! This module contains two components:
//! * A type [CircCfg] for configuration information.
//! * Static configuration storage
//!    * set with [set] and [set_cfg]
//!    * read with [cfg]
//!    * it can only be set once per process
//!       * if you want to unit-test your component, we recommend that it **should not** use [cfg].

use circ_fields::FieldT;

use once_cell::sync::OnceCell;
use rug::Integer;

use std::convert::From;
use std::default::Default;

/// Re-export our clap version
pub use circ_opt::clap;
/// Re-export our clap [clap::Args]
pub use circ_opt::CircOpt;

/// A Circ configuration. Contructible [From::from] [CircOpt].
#[derive(Clone, Debug)]
pub struct CircCfg {
    opt: CircOpt,
    field: FieldT,
}

/// Set the CirC configuration from a [CircOpt].
///
/// If you want to build the CirC configuration [CircCfg] object yourself,
/// you can set it with [set_cfg].
///
/// [CircOpt] implements [clap::Args], so it can be build from your command line or envvars. See
/// its documentation.
pub fn set(o: &CircOpt) {
    set_cfg(From::from(o.clone()))
}

/// Set the CirC configuration to its defaults.
/// See [set] to customize
pub fn set_default() {
    set_cfg(Default::default())
}

/// Set the CirC configuration from a [CircCfg].
///
/// We recommends using [set], which takes a [CircOpt] instead.
pub fn set_cfg(c: CircCfg) {
    CFG.set(c).unwrap_or_else(|c| {
        panic!(
            "Tried to set the CirC configuration, but it had already been set.\nNew cfg:\n{:#?}",
            c
        )
    })
}

/// Get the configuration
pub fn cfg() -> &'static CircCfg {
    CFG.get().expect("A component tried to read the CirC configuration, but it was not yet set. Did the top-level application call `circ::cfg::set`?")
}

/// Get the configuration, setting the configuration to the default value if it is unset.
pub fn cfg_or_default() -> &'static CircCfg {
    if !is_cfg_set() {
        set_default();
    }
    cfg()
}

/// Has the configuration been set yet?
pub fn is_cfg_set() -> bool {
    CFG.get().is_some()
}

static CFG: OnceCell<CircCfg> = OnceCell::new();

impl From<CircOpt> for CircCfg {
    fn from(opt: CircOpt) -> Self {
        let field = if !opt.field.custom_modulus.is_empty() {
            let error =
                |r: &str| panic!("The field modulus '{}' is {}", &opt.field.custom_modulus, r);
            let i = Integer::from_str_radix(&opt.field.custom_modulus, 10)
                .unwrap_or_else(|_| error("not an integer"));
            if i.is_probably_prime(30) == rug::integer::IsPrime::No {
                error("not a prime");
            }
            FieldT::from(i)
        } else {
            match opt.field.builtin {
                circ_opt::BuiltinField::Bls12381 => FieldT::FBls12381,
                circ_opt::BuiltinField::Bn254 => FieldT::FBn254,
            }
        };
        Self { opt, field }
    }
}

impl Default for CircCfg {
    fn default() -> Self {
        Self::from(CircOpt::default())
    }
}

/// Used to expose all fields of [CircOpt].
impl std::ops::Deref for CircCfg {
    type Target = CircOpt;

    fn deref(&self) -> &Self::Target {
        &self.opt
    }
}

/// Additional functionality
impl CircCfg {
    /// The default field
    pub fn field(&self) -> &FieldT {
        &self.field
    }
}
