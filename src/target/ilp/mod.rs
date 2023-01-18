//! Mixed ILP backend

pub mod trans;

use crate::ir::term::*;
use fxhash::FxHashMap as HashMap;
pub(crate) use good_lp::{
    Constraint, Expression, ProblemVariables, ResolutionError, Solution, Solver, SolverModel,
    Variable, VariableDefinition,
};
use log::debug;
use std::fmt::{self, Debug, Formatter};

/// An integer linear program
pub struct Ilp {
    /// Map from names to variables
    pub var_names: HashMap<String, Variable>,
    /// The variables
    variables: ProblemVariables,
    /// The constraints
    constraints: Vec<Constraint>,
    /// The optimization objective (to maximize)
    maximize: Expression,
}

impl Debug for Ilp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ilp")
            .field("var_names", &self.var_names)
            .field("constraints", &self.constraints)
            .field("maximize", &self.maximize)
            .finish_non_exhaustive()
    }
}

impl Default for Ilp {
    fn default() -> Self {
        Self::new()
    }
}

impl Ilp {
    /// Create an empty ILP
    pub fn new() -> Self {
        Self {
            var_names: HashMap::default(),
            variables: ProblemVariables::new(),
            constraints: Vec::new(),
            maximize: Expression::from(0),
        }
    }
    /// Create a new variable. `defn` can specify bounds, etc. See [VariableDefinition], which can
    /// be built using [good_lp::variable()].
    pub fn new_variable(&mut self, defn: VariableDefinition, name: String) -> Variable {
        let defn = defn.name(&name);
        let v = self.variables.add(defn);
        self.var_names.insert(name.clone(), v);
        debug!("Variable: {} -> {:?}", name, v);
        v
    }
    /// Add a constraint.
    pub fn new_constraint(&mut self, c: Constraint) {
        debug!("Constraint: {:?}", c);
        self.constraints.push(c);
    }
    /// Add a constraint.
    pub fn new_constraints(&mut self, c: impl IntoIterator<Item = Constraint>) {
        self.constraints.extend(c);
    }
    /// Get constraints
    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }
    /// Set maximization objective
    pub fn maximize(&mut self, e: Expression) {
        self.maximize = e;
    }
    /// Solve, using `s`.
    pub fn solve<M: SolverModel<Error = ResolutionError>, S: Solver<Model = M>>(
        self,
        s: S,
    ) -> Result<(f64, HashMap<String, f64>), IlpUnsat> {
        let max = self.maximize.clone();
        let mut prob = self.variables.maximise(self.maximize).using(s);
        for c in self.constraints {
            prob = prob.with(c);
        }
        match prob.solve() {
            Ok(s) => Ok((
                s.eval(max),
                self.var_names
                    .into_iter()
                    .map(|(name, v)| (name, s.value(v)))
                    .collect(),
            )),
            Err(ResolutionError::Unbounded) => Err(IlpUnsat::Unbounded),
            Err(ResolutionError::Infeasible) => Err(IlpUnsat::Infeasible),
            Err(e) => panic!("Error in solving: {}", e),
        }
    }
    /// Solve, using the default solver of [good_lp].
    pub fn default_solve(self) -> Result<(f64, HashMap<String, f64>), IlpUnsat> {
        self.solve(good_lp::default_solver)
    }
}

/// Convert an ILP assignment to a bit-vector assignment.
pub fn assignment_to_values(
    assignment: &HashMap<String, f64>,
    inputs: &HashMap<String, Sort>,
) -> HashMap<String, Value> {
    assignment
        .iter()
        .filter_map(|(name, v)| match inputs.get(name) {
            Some(Sort::BitVector(n)) => Some((
                name.clone(),
                Value::BitVector(BitVector::new((v.round() as u64).into(), *n)),
            )),
            Some(s) => unimplemented!(
                "Cannot reconstruct value of sort {} (var {}) from ILP output",
                s,
                name
            ),
            None => None,
        })
        .collect()
}

/// Why the ILP could not be solved
#[derive(Debug)]
pub enum IlpUnsat {
    /// The objective can be arbitrarily maximized
    Unbounded,
    /// No solutions to the constraints
    Infeasible,
}

#[cfg(test)]
mod test {
    use super::*;
    use good_lp::{
        default_solver, solvers::lp_solvers::SolverTrait, variable, ProblemVariables, Solution,
        SolverModel,
    };

    #[test]
    fn simple() {
        let mut vars = ProblemVariables::new();
        let a = vars.add(variable().name("a").binary());
        let b = vars.add(variable().name("b").integer().max(10));
        let c = vars.add(variable().name("c").max(10));
        let solution = vars
            .maximise(a + b + c)
            .using(default_solver)
            .with((a + b) << 30.0)
            .solve()
            .unwrap();
        assert_eq!(solution.value(a), 1.0);
        assert_eq!(solution.value(b), 10.0);
        assert_eq!(solution.value(c), 10.0);
    }

    fn test_solver<S: SolverTrait + Clone>(s: S) {
        let mut vars = ProblemVariables::new();
        let a = vars.add(variable().name("a").binary());
        let b = vars.add(variable().name("b").integer().max(10));
        let c = vars.add(variable().name("c").max(10));
        let solution = vars
            .maximise(a + b + c)
            .using(good_lp::solvers::lp_solvers::LpSolver(s))
            .with((a + b) << 30.0)
            .solve()
            .unwrap();
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

    fn test_solver_our_ilp<M: SolverModel<Error = ResolutionError>, S: Solver<Model = M>>(s: S) {
        let mut vars = Ilp::new();
        let a = vars.new_variable(variable().binary(), "a".into());
        let b = vars.new_variable(variable().integer().max(10), "b".into());
        let c = vars.new_variable(variable().max(10), "c".into());
        vars.maximize(a + b + c);
        vars.new_constraint(a << 5.0);
        vars.new_constraint(b << 5.0);
        vars.new_constraint(c << 2.0);
        let (_max, solution) = vars.solve(s).unwrap();
        assert_eq!(solution.get("a").unwrap(), &1.0);
        assert_eq!(solution.get("b").unwrap(), &5.0);
        assert_eq!(solution.get("c").unwrap(), &2.0);
    }

    #[test]
    fn test_our_ilp_with_default_solver() {
        test_solver_our_ilp(default_solver)
    }
}
