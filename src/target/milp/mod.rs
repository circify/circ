//! Mixed Integer Linear Programming


#[cfg(test)]
mod test {
    ///! Tests the lp-modeller library
    use lp_modeler::dsl::*;
    use lp_modeler::solvers::{SolverTrait, CbcSolver, Status, GlpkSolver};
    use lp_modeler::format::lp_format::LpFileFormat;


    #[test]
    fn simple_real() {

        let x = &LpContinuous::new("x");
        let y = &LpContinuous::new("y");
        let mut prob = LpProblem::new("problem", LpObjective::Maximize);
        prob += x + y;
        prob += x.le(10);
        prob += y.le(10);
        let solver = CbcSolver::new();
        let solution = solver.run(&prob).unwrap();
        assert_eq!(solution.results.get("x").unwrap(), &10.0);
        assert_eq!(solution.results.get("y").unwrap(), &10.0);
        assert_eq!(solution.status, Status::Optimal);

    }

    #[test]
    fn unsat_real() {

        let x = &LpContinuous::new("x");
        let y = &LpContinuous::new("y");
        let mut prob = LpProblem::new("problem", LpObjective::Maximize);
        prob += x + y;
        prob += x.le(10);
        prob += y.le(10);
        prob += (x + y).ge(30);
        let solver = CbcSolver::new();
        let solution = solver.run(&prob).unwrap();
        assert_eq!(solution.status, Status::Infeasible);

    }

    #[test]
    fn all() {
        let x = &LpBinary::new("b");
        let y = &LpInteger::new("y");
        let z = &LpContinuous::new("z");
        let mut prob = LpProblem::new("problem", LpObjective::Maximize);
        prob += x + y + z;
        prob += y.le(10);
        prob += z.le(10);
        prob += x.le(10);
        dbg!(&prob.variables());
        dbg!(&prob);
        println!("{}", prob.to_lp_file_format());
        let solver = CbcSolver::new();
        let solution = solver.run(&prob).unwrap();
        assert_eq!(solution.status, Status::Optimal);
        assert_eq!(solution.results.get("b").unwrap(), &1.0);
        assert_eq!(solution.results.get("y").unwrap(), &10.0);
        assert_eq!(solution.results.get("z").unwrap(), &10.0);
        let solver = GlpkSolver::new();
        let solution = solver.run(&prob).unwrap();
        assert_eq!(solution.status, Status::Optimal);
        assert_eq!(solution.results.get("b").unwrap(), &1.0);
        assert_eq!(solution.results.get("y").unwrap(), &10.0);
        assert_eq!(solution.results.get("z").unwrap(), &10.0);
    }
}
