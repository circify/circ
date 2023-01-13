mod random;
mod tiny;
mod hc_u8 {
    crate::generate_hashcons!(u8);
}

mod bench {

    use rand_chacha::ChaChaRng;

    fn test_rng() -> ChaChaRng {
        ChaChaRng::from_seed([0; 32])
    }

    use crate::hc_u8;

    use rand::{distributions::Distribution, Rng, SeedableRng};
    use rand_distr::Geometric;
    use std::time::{Duration, Instant};

    #[derive(Debug)]
    enum Step<T> {
        New(T, Vec<usize>),
        Dup(usize),
        Del(usize),
    }

    fn sample_steps<T, D, R>(num_steps: usize, d: &D, rng: &mut R, geo_p: f64) -> Vec<Step<T>>
    where
        D: Distribution<T>,
        R: Rng,
    {
        let mut steps = vec![];
        let mut size = 0;
        let arity_dist = Geometric::new(geo_p).unwrap();
        while steps.len() < num_steps {
            match rng.gen_range(0..3) {
                0 => {
                    let t = d.sample(rng);
                    let n_args = if size == 0 {
                        0
                    } else {
                        arity_dist.sample(rng) as usize
                    };
                    let args = (0..n_args).map(|_| rng.gen_range(0..size)).collect();
                    steps.push(Step::New(t, args));
                    size += 1;
                }
                1 => {
                    if size > 0 {
                        steps.push(Step::Dup(rng.gen_range(0..size)));
                        size += 1;
                    }
                }
                2 => {
                    if size > 0 {
                        steps.push(Step::Del(rng.gen_range(0..size)));
                        size -= 1;
                    }
                }
                _ => unreachable!(),
            }
        }
        steps
    }

    fn sample_u8_steps(num_steps: usize) -> Vec<Step<u8>> {
        sample_steps(
            num_steps,
            &rand::distributions::Standard,
            &mut test_rng(),
            0.25,
        )
    }

    struct Times {
        run: Duration,
        gc: Duration,
    }

    fn run_u8_steps(steps: &[Step<u8>]) -> Times {
        let mut mem = vec![];
        let start_run = Instant::now();
        for s in steps {
            match s {
                Step::New(t, args) => {
                    let new_t = hc_u8::create(t, args.iter().map(|i| &mem[*i]));
                    mem.push(new_t);
                }
                Step::Dup(i) => {
                    let prev = &mem[*i];
                    let new_t = hc_u8::create(&prev.op, prev.cs.iter());
                    mem.push(new_t);
                }
                Step::Del(i) => {
                    mem.remove(*i);
                }
            }
        }
        let run = start_run.elapsed();
        let start_gc = Instant::now();
        std::mem::drop(mem);
        hc_u8::gc();
        let gc = start_gc.elapsed();
        Times { run, gc }
    }

    fn bench_test(num_steps: usize) {
        hc_u8::gc();
        assert_eq!(hc_u8::table_size(), 0);
        let steps = sample_u8_steps(num_steps);
        let times = run_u8_steps(&steps);
        hc_u8::gc();
        assert_eq!(hc_u8::table_size(), 0);
        println!("time: {:?}", times.run / num_steps as u32);
        println!("gc  : {:?}", times.gc / num_steps as u32);
    }

    #[test]
    fn bench_100_() {
        bench_test(100)
    }

    #[test]
    fn bench_1000_() {
        bench_test(1000)
    }

    #[test]
    fn bench_10000_() {
        bench_test(10000)
    }

    #[test]
    fn bench_100000_() {
        bench_test(100000)
    }
    #[test]
    fn bench_500000_() {
        bench_test(500000)
    }
}
