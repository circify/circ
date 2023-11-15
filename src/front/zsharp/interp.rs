//! Utilities for interpretting zsharp

use super::term::{Ty, T};
use crate::ir::term::*;
use fxhash::FxHashMap as HashMap;

/// Given
/// * a variable name,
/// * a variable type, and
/// * a map from delimited names (e.g., "x", "x.0", "x.field_name") to values
///
/// computes a [T] (of the given type) that contains only constants. These constants are extracted
/// from the map
pub fn extract(
    name: &str,
    ty: &Ty,
    scalar_input_values: &mut HashMap<String, Value>,
) -> Result<T, String> {
    match ty {
        Ty::Bool | Ty::Field | Ty::Uint(..) => {
            let ir_val = scalar_input_values
                .remove(name)
                .ok_or_else(|| format!("Could not find scalar variable {name} in the input map"))?;
            Ok(T::new(ty.clone(), leaf_term(Op::Const(ir_val))))
        }
        Ty::Array(elem_count, elem_ty) => T::new_array(
            (0..*elem_count)
                .map(|i| extract(&format!("{name}.{i}"), elem_ty, scalar_input_values))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Ty::MutArray(elem_count) => T::new_array(
            (0..*elem_count)
                .map(|i| extract(&format!("{name}.{i}"), &Ty::Field, scalar_input_values))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Ty::Struct(s_name, fields) => Ok(T::new_struct(
            s_name.clone(),
            fields
                .fields()
                .map(|(f_name, f_ty)| -> Result<(String, T), String> {
                    Ok((
                        f_name.clone(),
                        extract(&format!("{name}.{f_name}"), f_ty, scalar_input_values)?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}
