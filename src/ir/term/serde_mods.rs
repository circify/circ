//! Serde functions

/// For term-valued maps
pub mod map {
    use super::super::*;
    use std::hash::Hash;
    /// Serialize a term-value map.
    pub fn serialize<S, K>(map: &FxHashMap<K, Term>, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        K: Hash + Eq + Clone + Serialize,
    {
        let (keys, values): (Vec<K>, Vec<Term>) =
            map.iter().map(|(k, v)| (k.clone(), v.clone())).unzip();
        (keys, term(Op::Tuple, values)).serialize(ser)
    }
    /// Serialize a term-value map.
    pub fn deserialize<'de, D, K>(de: D) -> Result<FxHashMap<K, Term>, D::Error>
    where
        D: Deserializer<'de>,
        K: Hash + Eq + Clone + Deserialize<'de>,
    {
        let (keys, tuple): (Vec<K>, Term) = Deserialize::deserialize(de)?;
        Ok(keys.into_iter().zip(tuple.cs().iter().cloned()).collect())
    }
}
/// For term vectors
pub mod vec {
    use super::super::*;
    /// Serialize a term vector
    #[allow(clippy::ptr_arg)]
    pub fn serialize<S>(vec: &Vec<Term>, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        term(Op::Tuple, vec.clone()).serialize(ser)
    }
    /// Serialize a term vector
    pub fn deserialize<'de, D>(de: D) -> Result<Vec<Term>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let tuple: Term = Deserialize::deserialize(de)?;
        Ok(tuple.cs().to_vec())
    }
}
