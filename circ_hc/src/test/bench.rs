use rand_chacha::ChaChaRng;

fn test_rng() -> ChaChaRng {
    ChaChaRng::from_seed([0; 32])
}

use crate::{Node, Table};

use rand::{distributions::Distribution, Rng, SeedableRng};
use rand_distr::Geometric;
use std::time::{Duration, Instant};

#[derive(Debug)]
enum Step<Op> {
    New(Op, Vec<usize>),
    Dup(usize),
    Del(usize),
}

fn sample_steps<Op, D, R>(num_steps: usize, d: &D, rng: &mut R, geo_p: f64) -> Vec<Step<Op>>
where
    D: Distribution<Op>,
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

fn gc_every_step<T: Table<u8>>(steps: &[Step<u8>]) -> Times {
    T::reserve(steps.len());
    let mut mem = vec![];
    let start_run = Instant::now();
    let mut gc = std::time::Duration::ZERO;
    for s in steps {
        match s {
            Step::New(t, args) => {
                let new_t = T::create_ref(t, args.iter().map(|i| &mem[*i]));
                mem.push(new_t);
            }
            Step::Dup(i) => {
                let prev = &mem[*i];
                let new_t = T::create_ref(prev.op(), prev.cs().iter());
                mem.push(new_t);
            }
            Step::Del(i) => {
                if *i > 0 {
                    mem[*i] = mem[i - 1].clone();
                }
            }
        }
        let start_gc = Instant::now();
        T::gc();
        gc += start_gc.elapsed();
    }
    let run = start_run.elapsed();
    let start_gc = Instant::now();
    std::mem::drop(mem);
    T::gc();
    gc += start_gc.elapsed();
    Times { run, gc }
}

fn gc_at_end<T: Table<u8>>(steps: &[Step<u8>]) -> Times {
    T::reserve(steps.len());
    let mut mem = vec![];
    let start_run = Instant::now();
    for s in steps {
        match s {
            Step::New(t, args) => {
                let new_t = T::create_ref(t, args.iter().map(|i| &mem[*i]));
                mem.push(new_t);
            }
            Step::Dup(i) => {
                let prev = &mem[*i];
                let new_t = T::create_ref(prev.op(), prev.cs().iter());
                mem.push(new_t);
            }
            Step::Del(i) => {
                if *i > 0 {
                    mem[*i] = mem[i - 1].clone();
                }
            }
        }
    }
    let run = start_run.elapsed();
    let start_gc = Instant::now();
    std::mem::drop(mem);
    T::gc();
    let gc = start_gc.elapsed();
    Times { run, gc }
}

pub fn bench_test<T: Table<u8>>(num_steps: usize) {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let steps = sample_u8_steps(num_steps);
    let times = gc_at_end::<T>(&steps);
    T::gc();
    assert_eq!(T::table_size(), 0);
    println!("");
    println!("workload,name,steps,time,gc_time");
    println!(
        "gc_at_end,{},{},{:?},{:?}",
        T::name(),
        num_steps,
        times.run / num_steps as u32,
        times.gc / num_steps as u32
    );
    let times = gc_every_step::<T>(&steps);
    T::gc();
    assert_eq!(T::table_size(), 0);
    println!("");
    println!("workload,name,steps,time,gc_time");
    println!(
        "gc_every_step,{},{},{:?},{:?}",
        T::name(),
        num_steps,
        times.run / num_steps as u32,
        times.gc / num_steps as u32
    );
}
