//! Oprators for maps

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::ArrayToMap].
pub fn check_array_to_map(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [array] = ty::count_or(arg_sorts)?;
    let (k, v, _size) = ty::array_or(array, "ArrayToMap expects array")?;
    Ok(Sort::Map(Box::new(k.clone()), Box::new(v.clone())))
}

/// Evaluate [super::ExtOp::ArrayToMap].
pub fn eval_array_to_map(args: &[&Value]) -> Value {
    let array = &args[0].as_array();
    let key_sort = array.key_sort.clone();
    let value_sort = array.default.sort();
    Value::Map(map::Map::new(key_sort, value_sort, array.map.clone()))
}

/// Type-check [super::ExtOp::MapFlip].
pub fn check_map_flip(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [map] = ty::count_or(arg_sorts)?;
    let (k, v) = ty::map_or(map, "MapFlip expects map")?;
    Ok(Sort::Map(Box::new(k.clone()), Box::new(v.clone())))
}

/// Evaluate [super::ExtOp::MapFlip].
pub fn eval_map_flip(args: &[&Value]) -> Value {
    let map = &args[0].as_map();
    Value::Map(map::Map::new(
        map.key_sort.clone(),
        map.value_sort.clone(),
        map.map.iter().map(|(k, v)| (v.clone(), k.clone())),
    ))
}

/// Type-check [super::ExtOp::MapSelect].
pub fn check_map_select(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [map, k] = ty::count_or(arg_sorts)?;
    let (km, v) = ty::map_or(map, "MapSelect expects map")?;
    ty::eq_or(km, k, "MapSelect key")?;
    Ok(v.clone())
}

/// Evaluate [super::ExtOp::MapSelect].
pub fn eval_map_select(args: &[&Value]) -> Value {
    let map = &args[0].as_map();
    let key = &args[1];
    map.select(key)
}

/// Type-check [super::ExtOp::MapContainsKey].
pub fn check_map_contains_key(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [map, k] = ty::count_or(arg_sorts)?;
    let (km, _) = ty::map_or(map, "MapContainsKey expects map")?;
    ty::eq_or(km, k, "MapContainsKey key")?;
    Ok(Sort::Bool)
}

/// Evaluate [super::ExtOp::MapContainsKey].
pub fn eval_map_contains_key(args: &[&Value]) -> Value {
    let map = &args[0].as_map();
    Value::Bool(map.contains_key(args[1]))
}
