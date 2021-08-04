//! Mixed ILP backend

#[cfg(test)]
mod test {
    use good_lp::{ProblemVariables, Solution, SolverModel, default_solver, variable, solvers::lp_solvers::SolverTrait};

    #[test]
    fn simple() {
        let mut vars = ProblemVariables::new();
        let a = vars.add(variable().name("a").binary());
        let b = vars.add(variable().name("b").integer().max(10));
        let c = vars.add(variable().name("c").max(10));
        let solution =
            vars
            .maximise(a + b + c)
            .using(default_solver)
            .with(a + b << 30.0)
            .solve().unwrap();
        assert_eq!(solution.value(a), 1.0);
        assert_eq!(solution.value(b), 10.0);
        assert_eq!(solution.value(c), 10.0);
    }

    fn test_solver<S: SolverTrait + Clone>(s: S) {
        let mut vars = ProblemVariables::new();
        let a = vars.add(variable().name("a").binary());
        let b = vars.add(variable().name("b").integer().max(10));
        let c = vars.add(variable().name("c").max(10));
        let solution =
            vars
            .maximise(a + b + c)
            .using(good_lp::solvers::lp_solvers::LpSolver(s))
            .with(a + b << 30.0)
            .solve().unwrap();
        assert_eq!(solution.value(a), 1.0);
        assert_eq!(solution.value(b), 10.0);
        assert_eq!(solution.value(c), 10.0);
    }

    #[test]
    #[ignore]
    fn test_cbc() {
        test_solver(good_lp::solvers::lp_solvers::CbcSolver::new());
    }
    #[test]
    #[ignore]
    fn test_glpk() {
        test_solver(good_lp::solvers::lp_solvers::GlpkSolver::new());
    }
}
