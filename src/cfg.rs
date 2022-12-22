//! CirC Configuration

use circ_fields::FieldT;

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

impl<'a> From<&'a CircOpt> for CircCfg {
    fn from(c: &'a CircOpt) -> Self {
        Self::from(c.clone())
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
