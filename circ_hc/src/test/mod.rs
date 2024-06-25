mod bench;
mod gc_hook;
mod qc;
mod tiny;
mod weak;

#[cfg(feature = "raw")]
mod raw {
    mod hc_u8 {
        crate::raw::generate_hashcons!(u8);
    }
    use hc_u8::Table;

    mod tiny {
        #[test]
        pub fn one() {
            super::super::tiny::one::<super::Table>();
        }
        #[test]
        pub fn two() {
            super::super::tiny::two::<super::Table>();
        }
        #[test]
        pub fn dup() {
            super::super::tiny::dup::<super::Table>();
        }
        #[test]
        pub fn min() {
            super::super::tiny::min::<super::Table>();
        }
        #[test]
        pub fn nodrop() {
            super::super::tiny::nodrop::<super::Table>();
        }
    }

    mod qc {
        use quickcheck_macros::quickcheck;
        #[quickcheck]
        pub fn four_nodes(a: u8, b: u8, c: u8, d: u8) {
            super::super::qc::four_nodes::<super::Table>(a, b, c, d);
        }
        #[quickcheck]
        pub fn many_nodes(steps: Vec<(u8, Vec<usize>)>) {
            super::super::qc::many_nodes::<super::Table>(steps);
        }
    }
    mod bench {
        #[test]
        fn ops_100_() {
            super::super::bench::bench_test::<super::Table>(100)
        }
        #[test]
        fn ops_1000_() {
            super::super::bench::bench_test::<super::Table>(1000)
        }
        #[test]
        fn ops_10000_() {
            super::super::bench::bench_test::<super::Table>(10000)
        }
        #[test]
        fn ops_100000_() {
            super::super::bench::bench_test::<super::Table>(100000)
        }
        #[test]
        fn ops_1000000_() {
            super::super::bench::bench_test::<super::Table>(1000000)
        }
    }

    mod weak {
        #[test]
        fn two() {
            super::super::weak::two::<super::Table>();
        }
        #[test]
        fn three() {
            super::super::weak::three::<super::Table>();
        }
    }
}

#[cfg(feature = "hashconsing")]
mod hashconsing {
    mod hc_u8 {
        crate::hashconsing::generate_hashcons!(u8);
    }
    use hc_u8::Table;

    mod tiny {
        #[test]
        pub fn one() {
            super::super::tiny::one::<super::Table>();
        }
        #[test]
        pub fn two() {
            super::super::tiny::two::<super::Table>();
        }
        #[test]
        pub fn dup() {
            super::super::tiny::dup::<super::Table>();
        }
        #[test]
        pub fn min() {
            super::super::tiny::min::<super::Table>();
        }
        #[test]
        pub fn nodrop() {
            super::super::tiny::nodrop::<super::Table>();
        }
    }

    mod qc {
        use quickcheck_macros::quickcheck;
        #[quickcheck]
        pub fn leaf(u: u8) {
            super::super::qc::leaf::<super::Table>(u);
        }
        #[quickcheck]
        pub fn four_nodes(a: u8, b: u8, c: u8, d: u8) {
            super::super::qc::four_nodes::<super::Table>(a, b, c, d);
        }
        #[quickcheck]
        pub fn many_nodes(steps: Vec<(u8, Vec<usize>)>) {
            super::super::qc::many_nodes::<super::Table>(steps);
        }
    }
    mod bench {
        #[test]
        fn ops_100_() {
            super::super::bench::bench_test::<super::Table>(100)
        }
        #[test]
        fn ops_1000_() {
            super::super::bench::bench_test::<super::Table>(1000)
        }
        #[test]
        fn ops_10000_() {
            super::super::bench::bench_test::<super::Table>(10000)
        }
        #[test]
        fn ops_100000_() {
            super::super::bench::bench_test::<super::Table>(100000)
        }
        #[test]
        fn ops_1000000_() {
            super::super::bench::bench_test::<super::Table>(1000000)
        }
    }

    mod weak {
        #[test]
        #[ignore]
        fn two() {
            super::super::weak::two::<super::Table>();
        }
        #[test]
        fn three() {
            super::super::weak::three::<super::Table>();
        }
    }
}

#[cfg(feature = "rc")]
mod rc {
    mod hc_u8 {
        crate::rc::generate_hashcons!(u8);
    }
    use hc_u8::Table;
    //use crate::rc::example_u8::Table;

    mod tiny {
        #[test]
        pub fn one() {
            super::super::tiny::one::<super::Table>();
        }
        #[test]
        pub fn two() {
            super::super::tiny::two::<super::Table>();
        }
        #[test]
        pub fn dup() {
            super::super::tiny::dup::<super::Table>();
        }
        #[test]
        pub fn min() {
            super::super::tiny::min::<super::Table>();
        }
        #[test]
        pub fn nodrop() {
            super::super::tiny::nodrop::<super::Table>();
        }
    }

    mod qc {
        use quickcheck_macros::quickcheck;
        #[quickcheck]
        pub fn leaf(u: u8) {
            super::super::qc::leaf::<super::Table>(u);
        }
        #[quickcheck]
        pub fn four_nodes(a: u8, b: u8, c: u8, d: u8) {
            super::super::qc::four_nodes::<super::Table>(a, b, c, d);
        }
        #[quickcheck]
        pub fn many_nodes(steps: Vec<(u8, Vec<usize>)>) {
            super::super::qc::many_nodes::<super::Table>(steps);
        }
    }

    mod bench {
        #[test]
        fn ops_100_() {
            super::super::bench::bench_test::<super::Table>(100)
        }
        #[test]
        fn ops_1000_() {
            super::super::bench::bench_test::<super::Table>(1000)
        }
        #[test]
        fn ops_10000_() {
            super::super::bench::bench_test::<super::Table>(10000)
        }
        #[test]
        fn ops_100000_() {
            super::super::bench::bench_test::<super::Table>(100000)
        }
        #[test]
        fn ops_1000000_() {
            super::super::bench::bench_test::<super::Table>(1000000)
        }
    }

    mod weak {
        #[test]
        fn two() {
            super::super::weak::two::<super::Table>();
        }
        #[test]
        fn three() {
            super::super::weak::three::<super::Table>();
        }
    }

    mod gc_hook {
        #[test]
        fn two() {
            super::super::gc_hook::two::<super::Table>();
        }
        #[test]
        fn three() {
            super::super::gc_hook::three::<super::Table>();
        }
    }
}
