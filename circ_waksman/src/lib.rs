//! A configuration library for Waksman networks.
//!
//! Such a network applies a permutation to sort an input vector.
//!
//! Reference: "On Arbitrary Waksman Networks and their Vulnerability", by Bruno Beauquier and Eric Darrot.

use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;
use std::collections::VecDeque;

use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
/// A network configuration
pub enum Config {
    /// The trivial configuration for routing 1 flow.
    SingleWire,
    /// Routing multiple flows
    Recursive {
        /// The number of flows `n`.
        n_wires: usize,
        /// `floor(n/2)` booleans `b_i` indicating whether to switch `2i` and `2i+1` initially
        input_configs: Vec<bool>,
        /// the configuration for the subnet applied to the first output of each initial switch
        upper_subnet: Box<Config>,
        /// the configuration for the subnet applied to all other initial switch outputs (and a
        /// possible final input which doesn't get an initial switch)
        lower_subnet: Box<Config>,
        /// `floor((n-1)/2)` booleans indicating whether to switch outputs `2i` and `2i+1`,
        /// post-subnets.
        output_configs: Vec<bool>,
    },
}

pub fn n_switches(n_flows: usize) -> usize {
    // (1) of the reference paper
    (1..=n_flows)
        .map(|i| (i as f64).log2().ceil() as usize)
        .sum()
}

impl Config {
    /// Compute the configuration that routes `inputs` into sorted order.
    pub fn for_sorting<T: Clone + Ord + Hash>(inputs: Vec<T>) -> Config {
        debug_assert_ne!(inputs.len(), 0);
        if inputs.len() == 1 {
            return Config::SingleWire;
        }
        let mut outputs = inputs.clone();
        outputs.sort();
        let output_idxs = HashMap::from_iter(outputs.iter().enumerate().map(|(oi, o)| (o, oi)));
        let input_idxs = HashMap::from_iter(inputs.iter().enumerate().map(|(ii, i)| (i, ii)));
        #[cfg(debug_assertions)]
        {
            debug_assert_eq!(HashSet::from_iter(inputs.iter()).len(), inputs.len());
        }
        // two subnets: l and u
        let n = inputs.len();
        let u_size = n / 2;
        let l_size = n - u_size;
        let n_in_switches = n / 2;
        let n_out_switches = (n - 1) / 2;
        let mut in_l = HashSet::<usize>::default();
        let mut to_place = HashSet::from_iter(0..n);
        // list of forced placements into subnets: [(subnet_idx, output_idx)]
        //    subnet_idx false: l
        //    subnet_idx  true: u
        let mut forced_placements: Vec<(bool, usize)> = vec![(false, n - 1)];
        while !to_place.is_empty() {
            let (subnet_idx, output_i) = forced_placements
                .pop()
                .unwrap_or_else(|| (false, *to_place.iter().next().unwrap()));
            if !to_place.contains(&output_i) {
                debug_assert!(in_l.contains(&output_i) ^ subnet_idx);
            }
            to_place.remove(&output_i);
            if !subnet_idx {
                in_l.insert(output_i);
            }
            if twin(output_i) < n && to_place.contains(&twin(output_i)) {
                forced_placements.push((!subnet_idx, twin(output_i)));
            }
            let input_i = *input_idxs.get(&outputs[output_i]).unwrap();
            if twin(input_i) < n {
                let twin_output_i = *output_idxs.get(&inputs[twin(input_i)]).unwrap();
                if to_place.contains(&twin_output_i) {
                    forced_placements.push((!subnet_idx, twin_output_i));
                }
            }
        }
        assert_eq!(in_l.len(), l_size);
        let in_u = HashSet::from_iter((0..n).filter(|i| !in_l.contains(i)));
        let input_configs = Vec::from_iter(
            (0..n_in_switches).map(|i| in_l.contains(output_idxs.get(&inputs[2 * i]).unwrap())),
        );
        let output_configs = Vec::from_iter((0..n_out_switches).map(|i| in_l.contains(&(2 * i))));
        let l_inputs = Vec::from_iter(
            (0..n)
                .filter(|i| in_l.contains(output_idxs.get(&inputs[*i]).unwrap()))
                .map(|i| inputs[i].clone()),
        );
        let u_inputs = Vec::from_iter(
            (0..n)
                .filter(|i| in_u.contains(output_idxs.get(&inputs[*i]).unwrap()))
                .map(|i| inputs[i].clone()),
        );
        let lower_subnet = Config::for_sorting(l_inputs);
        let upper_subnet = Config::for_sorting(u_inputs);
        let ret = Config::Recursive {
            n_wires: n,
            input_configs,
            output_configs,
            lower_subnet: Box::new(lower_subnet),
            upper_subnet: Box::new(upper_subnet),
        };
        ret
    }

    /// How many flows does this configuration route?
    pub fn n_flows(&self) -> usize {
        match self {
            Config::SingleWire => 1,
            Config::Recursive { n_wires, .. } => *n_wires,
        }
    }

    /// Apply this configuration to `data`. If `check` is true, check that the output is sorted,
    /// and print a message/panic if not.
    pub fn apply<T: Clone + Debug + Ord>(&self, data: Vec<T>, check: bool) -> Vec<T> {
        assert_eq!(data.len(), self.n_flows());
        match self {
            Config::SingleWire => data,
            Config::Recursive {
                n_wires,
                input_configs,
                output_configs,
                upper_subnet,
                lower_subnet,
            } => {
                let data_cp = if check { data.clone() } else { vec![] };
                let mut lower_inputs = Vec::new();
                let mut upper_inputs = Vec::new();
                for i in 0..(n_wires / 2) {
                    let mut first = data[2 * i].clone();
                    let mut second = data[2 * i + 1].clone();
                    if input_configs[i] {
                        std::mem::swap(&mut first, &mut second);
                    }
                    lower_inputs.push(second);
                    upper_inputs.push(first);
                }
                if n_wires % 2 == 1 {
                    lower_inputs.push(data.last().unwrap().clone());
                }
                let mut upper_outputs = upper_subnet.apply(upper_inputs, check);
                let mut lower_outputs = lower_subnet.apply(lower_inputs, check);
                lower_outputs.reverse();
                upper_outputs.reverse();
                let mut outputs = Vec::new();
                for i in 0..((n_wires - 1) / 2) {
                    let mut first = upper_outputs.pop().unwrap();
                    let mut second = lower_outputs.pop().unwrap();
                    if output_configs[i] {
                        std::mem::swap(&mut first, &mut second);
                    }
                    outputs.push(first);
                    outputs.push(second);
                }
                assert!(upper_outputs.len() <= 1);
                assert!(lower_outputs.len() <= 1);
                assert!(!(upper_outputs.len() == 1 && lower_outputs.len() == 0));
                outputs.extend(upper_outputs);
                outputs.extend(lower_outputs);
                if check {
                    for i in 0..(outputs.len() - 1) {
                        if outputs[i] >= outputs[i + 1] {
                            println!("On input {:?}", data_cp);
                            println!("Got ouput {:?}", outputs);
                            println!("Which is not sorted (indices {} {})", i, i + 1);
                            println!("Plan: {:#?}", self);
                            panic!("Config::apply failure");
                        }
                    }
                }
                outputs
            }
        }
    }

    /// Return a list of switch settings.
    pub fn switches(self) -> Vec<bool> {
        let mut out = Vec::new();
        self.switches_into(&mut out);
        out
    }

    fn switches_into(self, into: &mut Vec<bool>) {
        match self {
            Config::SingleWire => {}
            Config::Recursive {
                input_configs,
                upper_subnet,
                lower_subnet,
                output_configs,
                ..
            } => {
                into.extend(input_configs);
                upper_subnet.switches_into(into);
                lower_subnet.switches_into(into);
                into.extend(output_configs);
            }
        }
    }
}

pub fn twin(i: usize) -> usize {
    i ^ 1
}

/// Symbolically apply a Waksman network to the given `data`, using the given `switches` and the
/// given `switch_fn`.
pub fn symbolic_apply<T: Clone, Cond, SwitchFn: FnMut(&T, &T, Cond) -> (T, T)>(
    data: Vec<T>,
    switches: &mut VecDeque<Cond>,
    switch_fn: &mut SwitchFn,
) -> Vec<T> {
    let n = data.len();
    if n == 1 {
        return data;
    }
    let n_input_switches = n / 2;
    let n_output_switches = (n - 1) / 2;
    let upper_size = n / 2;
    let lower_size = n - upper_size;
    let mut upper_inputs = Vec::new();
    let mut lower_inputs = Vec::new();
    for input_pair_i in 0..n_input_switches {
        let top_in = &data[2 * input_pair_i];
        let bot_in = &data[2 * input_pair_i + 1];
        let switch = switches.pop_front().unwrap();
        let (top, bot) = switch_fn(top_in, bot_in, switch);
        upper_inputs.push(top);
        lower_inputs.push(bot);
    }
    if n % 2 == 1 {
        lower_inputs.push(data[n - 1].clone());
    }
    let upper_outputs = symbolic_apply(upper_inputs, switches, switch_fn);
    let lower_outputs = symbolic_apply(lower_inputs, switches, switch_fn);
    let mut outputs = Vec::new();
    for output_pair_i in 0..n_output_switches {
        let top_in = &upper_outputs[output_pair_i];
        let bot_in = &lower_outputs[output_pair_i];
        let switch = switches.pop_front().unwrap();
        let (top, bot) = switch_fn(top_in, bot_in, switch);
        outputs.push(top);
        outputs.push(bot);
    }
    if n % 2 == 0 {
        outputs.push(upper_outputs[upper_size - 1].clone());
    }
    outputs.push(lower_outputs[lower_size - 1].clone());
    outputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use rand::seq::SliceRandom;
    use rand::Rng;
    use rand::SeedableRng;

    fn test_on_data(data: Vec<usize>) {
        let cfg = Config::for_sorting(data.clone());
        cfg.apply(data.clone(), true);
    }

    fn test_all_dense_perms(size: usize) {
        let universe = Vec::from_iter(0..size);
        for data in universe.iter().cloned().permutations(size) {
            test_on_data(data)
        }
    }

    fn test_all_sparse_perms(size: usize) {
        let universe = Vec::from_iter(0..size);
        for data in universe.iter().cloned().permutations(size) {
            test_on_data(data.into_iter().map(|i| 3 * i + 1).collect())
        }
    }

    #[test]
    fn test1_sparse() {
        test_on_data(vec![0]);
        test_on_data(vec![1]);
        test_on_data(vec![17]);
    }

    #[test]
    fn test2_sparse() {
        test_on_data(vec![0, 1]);
        test_on_data(vec![1, 0]);
        test_on_data(vec![1, 2]);
        test_on_data(vec![2, 1]);
        test_on_data(vec![17, 20]);
        test_on_data(vec![20, 10]);
    }

    #[test]
    fn test2_all_dense() {
        test_all_dense_perms(2);
    }

    #[test]
    fn test3_all_dense() {
        test_all_dense_perms(3);
    }

    #[test]
    fn test4_all_dense() {
        test_all_dense_perms(4);
    }

    #[test]
    fn test5_all_dense() {
        test_all_dense_perms(5);
    }

    #[test]
    fn test2_all_sparse() {
        test_all_sparse_perms(2);
    }

    #[test]
    fn test3_all_sparse() {
        test_all_sparse_perms(3);
    }

    #[test]
    fn test4_all_sparse() {
        test_all_sparse_perms(4);
    }

    #[test]
    fn test5_all_sparse() {
        test_all_sparse_perms(5);
    }

    #[test]
    fn test7_all_sparse() {
        test_all_sparse_perms(7);
    }

    #[test]
    fn test3_rev() {
        Config::for_sorting(vec![2, 1, 0]);
    }

    #[test]
    fn test5_id() {
        Config::for_sorting(vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn test5_transpose() {
        Config::for_sorting(vec![1, 0, 2, 3, 4]);
    }

    #[test]
    fn test5_rev() {
        Config::for_sorting(vec![4, 3, 2, 1, 0]);
    }

    #[test]
    fn test5_rev_sparse() {
        Config::for_sorting(vec![19, 14, 10, 1, 0]);
    }

    #[test]
    fn rand_dense_test() {
        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(0);
        let size = 200;
        let iters = 100;
        for _i in 0..iters {
            let mut data = Vec::from_iter(0..size);
            data.shuffle(rng);
            test_on_data(data);
        }
    }

    #[test]
    fn rand_sparse_rand() {
        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(0);
        let size = 200;
        let iters = 100;
        for _i in 0..iters {
            let mut data = Vec::from_iter((0..size).map(|i| 10 * i + rng.gen_range(0..10)));
            data.shuffle(rng);
            test_on_data(data);
        }
    }

    #[test]
    fn rand_sym_apply() {
        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(0);
        let size = 200;
        let iters = 10;
        for _i in 0..iters {
            let mut data = Vec::from_iter((0..size).map(|i| 10 * i + rng.gen_range(0..10)));
            data.shuffle(rng);
            let cfg = Config::for_sorting(data.clone());
            let apply_normal = cfg.apply(data.clone(), false);
            let mut switches = VecDeque::from_iter(cfg.switches().into_iter());
            let apply_sym = symbolic_apply(
                data,
                &mut switches,
                &mut |top: &usize, bot: &usize, cond: bool| {
                    if cond {
                        (*bot, *top)
                    } else {
                        (*top, *bot)
                    }
                },
            );
            assert_eq!(apply_normal, apply_sym);
        }
    }
}
