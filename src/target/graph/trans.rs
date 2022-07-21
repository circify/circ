use crate::ir::term::*;

use crate::target::graph::tp::*;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::SharingMap;
use std::collections::HashMap;


#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_glp(
    fs: &Functions, 
    cm: &str
) -> (Functions, HashMap<String, SharingMap>){
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let c = tp.inline_all(&main.to_string());

    // println!("Terms after inline all.");
    // for t in c.terms_postorder() {
    //     println!("t: {}", t);
    // }

    let cs = c.to_cs();
    let assignment = assign(&cs, cm);
    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}
