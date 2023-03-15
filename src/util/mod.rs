//! Various data structures, etc.

pub mod hc;
pub mod ns;
pub mod once;

#[cfg(test)]
mod hash_test {
    //! This module validates our assumptions about the determinism and non-determinism of
    //! iteration orders for different hash collections.
    use fxhash::{FxHashMap, FxHashSet};
    use std::collections::{HashMap, HashSet};

    #[test]
    fn test_map_det_iter_order() {
        let mut m1: FxHashMap<usize, usize> = Default::default();
        let mut m2: FxHashMap<usize, usize> = Default::default();
        for i in 0..100 {
            m1.insert(i, i);
            m2.insert(i, i);
        }
        let v1: Vec<(usize, usize)> = m1.into_iter().collect();
        let v2: Vec<(usize, usize)> = m2.into_iter().collect();
        assert_eq!(v1, v2);
    }

    #[test]
    fn test_map_non_det_iter_order() {
        let mut m1: HashMap<usize, usize> = HashMap::new();
        let mut m2: HashMap<usize, usize> = HashMap::new();
        for i in 0..100 {
            m1.insert(i, i);
            m2.insert(i, i);
        }
        let v1: Vec<(usize, usize)> = m1.into_iter().collect();
        let v2: Vec<(usize, usize)> = m2.into_iter().collect();
        assert_ne!(v1, v2);
    }

    #[test]
    fn test_set_det_iter_order() {
        let mut m1: FxHashSet<usize> = Default::default();
        let mut m2: FxHashSet<usize> = Default::default();
        for i in 0..100 {
            m1.insert(i);
            m2.insert(i);
        }
        let v1: Vec<usize> = m1.into_iter().collect();
        let v2: Vec<usize> = m2.into_iter().collect();
        assert_eq!(v1, v2);
    }

    #[test]
    fn test_set_non_det_iter_order() {
        let mut m1: HashSet<usize> = HashSet::new();
        let mut m2: HashSet<usize> = HashSet::new();
        for i in 0..100 {
            m1.insert(i);
            m2.insert(i);
        }
        let v1: Vec<usize> = m1.into_iter().collect();
        let v2: Vec<usize> = m2.into_iter().collect();
        assert_ne!(v1, v2);
    }
}
