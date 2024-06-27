//! A multi-stage R1CS witness evaluator.

use crate::cfg::cfg_or_default;
use crate::ir::term::*;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use serde::{Deserialize, Serialize};

use log::trace;

use std::time::Duration;

/// A witness computation that proceeds in stages.
///
/// In each stage:
/// * it takes a partial assignment
/// * it returns a vector of field values
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct StagedWitComp {
    vars: HashSet<String>,
    stages: Vec<Stage>,
    steps: Vec<(Op, usize)>,
    step_args: Vec<usize>,
    ouput_steps: Vec<usize>,
    // we don't serialize the cache; it's just used during construction, and terms are expensive to
    // serialize.
    #[serde(skip)]
    term_to_step: TermMap<usize>,
}

/// Specifies a stage.
#[derive(Debug, Serialize, Deserialize)]
pub struct Stage {
    inputs: HashMap<String, Sort>,
    num_outputs: usize,
}

/// Builder interface
impl StagedWitComp {
    /// Add a new stage.
    #[allow(clippy::uninlined_format_args)]
    pub fn add_stage(&mut self, inputs: HashMap<String, Sort>, output_values: Vec<Term>) {
        let stage = Stage {
            inputs,
            num_outputs: output_values.len(),
        };
        for input in stage.inputs.keys() {
            debug_assert!(!self.vars.contains(input), "Duplicate input {}", input);
        }
        self.vars.extend(stage.inputs.keys().cloned());
        self.stages.push(stage);
        let already_have: TermSet = self.term_to_step.keys().cloned().collect();
        for t in PostOrderIter::from_roots_and_skips(output_values.clone(), already_have) {
            self.add_step(t);
        }
        for t in output_values {
            self.ouput_steps.push(*self.term_to_step.get(&t).unwrap());
        }
    }

    fn add_step(&mut self, term: Term) {
        debug_assert!(!self.term_to_step.contains_key(&term));
        let step_idx = self.steps.len();
        if let Op::Var(var) = term.op() {
            debug_assert!(self.vars.contains(&*var.name));
        }
        for child in term.cs() {
            let child_step = self.term_to_step.get(child).unwrap();
            self.step_args.push(*child_step);
        }
        self.steps.push((term.op().clone(), self.step_args.len()));
        self.term_to_step.insert(term, step_idx);
    }

    /// How many stages are there?
    pub fn stage_sizes(&self) -> impl Iterator<Item = usize> + '_ {
        self.stages.iter().map(|s| s.num_outputs)
    }

    /// How many inputs are there for this stage?
    pub fn num_stage_inputs(&self, n: usize) -> usize {
        self.stages[n].inputs.len()
    }
}

/// Evaluator interface
impl StagedWitComp {
    fn step_args(&self, step_idx: usize) -> impl Iterator<Item = usize> + '_ {
        assert!(step_idx < self.steps.len());
        let args_end = self.steps[step_idx].1;
        let args_start = if step_idx == 0 {
            0
        } else {
            self.steps[step_idx - 1].1
        };
        (args_start..args_end).map(move |step_arg_idx| self.step_args[step_arg_idx])
    }
}

/// Evaluates a staged witness computation.
#[derive(Debug)]
pub struct StagedWitCompEvaluator<'a> {
    comp: &'a StagedWitComp,
    variable_values: HashMap<String, Value>,
    step_values: Vec<Value>,
    stages_evaluated: usize,
    outputs_evaluted: usize,
    op_times: HashMap<(Op, Vec<Sort>), (Duration, usize)>,
    time_ops: bool,
}

impl<'a> StagedWitCompEvaluator<'a> {
    /// Create an empty witness computation.
    pub fn new(comp: &'a StagedWitComp) -> Self {
        Self {
            comp,
            variable_values: Default::default(),
            step_values: Default::default(),
            stages_evaluated: Default::default(),
            outputs_evaluted: 0,
            op_times: Default::default(),
            time_ops: cfg_or_default().ir.time_eval_ops,
        }
    }
    /// Have all stages been evaluated?
    pub fn is_done(&self) -> bool {
        self.stages_evaluated == self.comp.stages.len()
    }
    fn eval_step(&mut self) {
        let next_step_idx = self.step_values.len();
        assert!(next_step_idx < self.comp.steps.len());
        let op = &self.comp.steps[next_step_idx].0;
        let step_values = &self.step_values;
        let op_times = &mut self.op_times;
        let args: Vec<&Value> = self
            .comp
            .step_args(next_step_idx)
            .map(|i| &step_values[i])
            .collect();
        let value = if self.time_ops {
            let start = std::time::Instant::now();
            let r = eval_op(op, &args, &self.variable_values);
            let duration = start.elapsed();
            let (ref mut dur, ref mut ct) = op_times
                .entry((op.clone(), args.iter().map(|v| v.sort()).collect()))
                .or_default();
            *dur += duration;
            *ct += 1;
            r
        } else {
            eval_op(op, &args, &self.variable_values)
        };

        trace!(
            "Eval step {}: {} on {:?} -> {}",
            next_step_idx,
            op,
            args,
            value
        );
        self.step_values.push(value);
    }
    /// Evaluate one stage.
    pub fn eval_stage(&mut self, inputs: HashMap<String, Value>) -> Vec<&Value> {
        trace!(
            "Beginning stage {}/{}",
            self.stages_evaluated,
            self.comp.stages.len()
        );
        debug_assert!(self.stages_evaluated < self.comp.stages.len());
        let stage = &self.comp.stages[self.stages_evaluated];
        let num_outputs = stage.num_outputs;
        for (k, v) in &inputs {
            trace!("Input {}: {}", k, v,);
        }
        self.variable_values.extend(inputs);
        if num_outputs > 0 {
            let max_step = (0..num_outputs)
                .map(|i| {
                    let new_output_i = i + self.outputs_evaluted;
                    self.comp.ouput_steps[new_output_i]
                })
                .max()
                .unwrap();
            while self.step_values.len() <= max_step {
                self.eval_step();
            }
        }
        self.outputs_evaluted += num_outputs;
        self.stages_evaluated += 1;
        let mut out = Vec::new();
        for output_step in
            &self.comp.ouput_steps[self.outputs_evaluted - num_outputs..self.outputs_evaluted]
        {
            out.push(&self.step_values[*output_step]);
        }
        out
    }

    /// Prints out operator evaluation times (if self.time_ops is set)
    pub fn print_times(&self) {
        if self.time_ops {
            // (operator, nanos total, counts, nanos/count, arg sorts (or *))
            let mut rows: Vec<(String, usize, usize, f64, String)> = Default::default();
            for ((op, arg_sorts), (time, count)) in &self.op_times {
                let nanos = time.as_nanos() as usize;
                let per = nanos as f64 / *count as f64;
                rows.push((
                    format!("{}", op),
                    nanos,
                    *count,
                    per,
                    format!("{:?}", arg_sorts),
                ));
            }
            rows.sort_by_key(|t| t.1);
            println!("time,op,nanos,counts,nanos_per,arg_sorts");
            for (op, nanos, counts, nanos_per, arg_sorts) in &rows {
                println!("time,{op},{nanos},{counts},{nanos_per},\"{arg_sorts}\"");
            }
        }
    }
}

#[cfg(test)]
mod test {

    use rug::Integer;

    use super::*;
    use circ_fields::FieldT;

    fn mk_inputs(v: Vec<(String, Sort)>) -> HashMap<String, Sort> {
        v.into_iter().collect()
    }

    #[test]
    fn one_const() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn many_const() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);
        comp.add_stage(
            mk_inputs(vec![]),
            vec![pf_lit(field.new_v(1)), pf_lit(field.new_v(4))],
        );
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(6))]);
        comp.add_stage(mk_inputs(vec![]), vec![pf_lit(field.new_v(0))]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[1, 4];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[6];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(Default::default());
        let ex_output: &[usize] = &[0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn vars_one_stage() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![("a".into(), Sort::Bool), ("b".into(), Sort::Field(field.clone()))]),
        vec![
            var("b".into(), Sort::Field(field.clone())),
            term![Op::Ite; var("a".into(), Sort::Bool), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
        ]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(
            vec![
                ("a".into(), Value::Bool(true)),
                ("b".into(), Value::Field(field.new_v(5))),
            ]
            .into_iter()
            .collect(),
        );
        let ex_output: &[usize] = &[5, 1];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }

    #[test]
    fn vars_many_stages() {
        let mut comp = StagedWitComp::default();
        let field = FieldT::from(Integer::from(7));
        comp.add_stage(mk_inputs(vec![("a".into(), Sort::Bool), ("b".into(), Sort::Field(field.clone()))]),
        vec![
            var("b".into(), Sort::Field(field.clone())),
            term![Op::Ite; var("a".into(), Sort::Bool), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
        ]);
        comp.add_stage(mk_inputs(vec![("c".into(), Sort::Field(field.clone()))]),
        vec![
            term![PF_ADD;
               var("b".into(), Sort::Field(field.clone())),
               var("c".into(), Sort::Field(field.clone()))],
            term![Op::Ite; var("a".into(), Sort::Bool), pf_lit(field.new_v(1)), pf_lit(field.new_v(0))],
            term![Op::Ite; var("a".into(), Sort::Bool), pf_lit(field.new_v(0)), pf_lit(field.new_v(1))],
        ]);

        let mut evaluator = StagedWitCompEvaluator::new(&comp);

        let output = evaluator.eval_stage(
            vec![
                ("a".into(), Value::Bool(true)),
                ("b".into(), Value::Field(field.new_v(5))),
            ]
            .into_iter()
            .collect(),
        );
        let ex_output: &[usize] = &[5, 1];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        let output = evaluator.eval_stage(
            vec![("c".into(), Value::Field(field.new_v(3)))]
                .into_iter()
                .collect(),
        );
        let ex_output: &[usize] = &[1, 1, 0];
        assert_eq!(output.len(), ex_output.len());
        for i in 0..ex_output.len() {
            assert_eq!(output[i], &Value::Field(field.new_v(ex_output[i])), "{i}");
        }

        assert!(evaluator.is_done());
    }
}
