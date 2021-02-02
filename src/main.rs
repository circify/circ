mod ir;
mod util;

use rand::distributions::Distribution;

fn main() {
    let mut rng = rand::thread_rng();
    for i in 0..100 {
        let t = ir::term::BoolDist(6).sample(&mut rng);
        println!("Term: {:#?}", t)
    }
}
