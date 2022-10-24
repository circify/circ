use rand_core::RngCore;
use std::ops::{AddAssign, MulAssign};
use std::sync::Arc;

use ff::{Field, PrimeField, PrimeFieldBits};
use group::{prime::PrimeCurveAffine, Curve};
use pairing::Engine;
use rand_chacha::ChaChaRng;
use sha2::{Digest, Sha256};

use super::{ParameterSource, Proof};

use crate::random::RandomCircuit;
use crate::random::RandomConstraintSystem;
use crate::{Circuit, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};

use crate::domain::{EvaluationDomain, Scalar};

use crate::multiexp::{multiexp, DensityTracker, FullDensity};

use crate::multicore::Worker;

fn eval<S: PrimeField>(
    lc: &LinearCombination<S>,
    mut input_density: Option<&mut DensityTracker>,
    mut aux_density: Option<&mut DensityTracker>,
    input_assignment: &[S],
    aux_assignment: &[S],
) -> S {
    let mut acc = S::zero();

    for &(index, coeff) in lc.0.iter() {
        let mut tmp;

        if !coeff.is_zero_vartime() {
            match index {
                Variable(Index::Input(i)) => {
                    tmp = input_assignment[i];
                    if let Some(ref mut v) = input_density {
                        v.inc(i);
                    }
                }
                Variable(Index::Aux(i)) => {
                    tmp = aux_assignment[i];
                    if let Some(ref mut v) = aux_density {
                        v.inc(i);
                    }
                }
            }

            if coeff != S::one() {
                tmp *= coeff;
            }
            acc += tmp;
        }
    }

    acc
}

struct ProvingAssignment<'a, E: Engine, S: PrimeField> {
    // Density of queries
    a_aux_density: DensityTracker,
    b_input_density: DensityTracker,
    b_aux_density: DensityTracker,

    // Evaluations of A, B, C polynomials
    a: Vec<Scalar<S>>,
    b: Vec<Scalar<S>>,
    c: Vec<Scalar<S>>,

    // Assignments of variables
    input_assignment: Vec<S>,
    aux_assignment: Vec<S>,
    nonrand_aux_assignment: Vec<S>,
    rand_aux_assignment: Vec<S>,

    num_nonrandom: usize,
    coin_inds: Vec<usize>,
    coins_done: bool,

    // cached pid value for generating coins
    d: Option<E::G1Affine>,
    get_d: &'a dyn Fn(&Vec<S>, usize) -> E::G1Affine,
}

impl<'a, E: Engine, S: PrimeField> ProvingAssignment<'a, E, S> {
    fn fiat_shamir_coin(&mut self, num: usize) -> S {
        if self.d.is_none() {
            self.d = Some((self.get_d)(
                &self.nonrand_aux_assignment,
                self.num_nonrandom,
            ));
        }

        // don't include coins in the inputs...this doesn't really matter but
        // makes verification easier
        compute_coin::<E, S>(
            &self.input_assignment[..self.input_assignment.len() - self.coin_inds.len()],
            self.d.unwrap(),
            num,
        )
    }
}

pub fn compute_coin<E: Engine, S: PrimeField>(inputs: &[S], pid: E::G1Affine, num: usize) -> S {
    let inputs_bits: Vec<u8> = inputs
        .iter()
        .flat_map(|s| s.to_repr().as_ref().to_vec())
        .collect();

    use group::GroupEncoding;

    println!("coin inputs are: {:?}", inputs);
    let num_bits = num.to_be_bytes();
    // TODO: need to put in Pid in here...
    let sha_input = [&inputs_bits, pid.to_bytes().as_ref(), &num_bits[..]].concat();
    let mut hasher = Sha256::new();
    hasher.update(sha_input);
    let seed = hasher.finalize();
    use rand_core::SeedableRng;
    let mut rng = ChaChaRng::from_seed(seed.try_into().unwrap());
    // TODO: gross
    //let coin =
    //from_u8s(&res).unwrap()
    let res = S::random(&mut rng);
    println!("coin is: {:?}", res);
    res
}

fn from_u8s<F: PrimeField>(arr: &[u8]) -> Option<F> {
    if arr.is_empty() {
        return None;
    }

    if arr.len() == 1 && arr[0] == 0 {
        return Some(F::zero());
    }

    let mut res = F::zero();

    let twofivesix = F::from(256);

    let mut first_digit = true;

    for c in arr {
        if first_digit {
            if *c == 0 {
                return None;
            }

            first_digit = false;
        }

        res.mul_assign(&twofivesix);
        res.add_assign(&F::from(*c as u64));
    }

    Some(res)
}

impl<E: Engine, S: PrimeField> ConstraintSystem<S> for ProvingAssignment<'_, E, S> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let res = f()?;
        let res2 = res.clone();
        self.aux_assignment.push(res);
        self.a_aux_density.add_element();
        self.b_aux_density.add_element();

        if self.coin_inds.is_empty() {
            self.num_nonrandom += 1;
            self.nonrand_aux_assignment.push(res2);
        } else {
            self.coins_done = true;
            self.rand_aux_assignment.push(res2);
        }

        Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.input_assignment.push(f()?);
        self.b_input_density.add_element();

        Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LB: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LC: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.a.push(Scalar(eval(
            &a,
            // Inputs have full density in the A query
            // because there are constraints of the
            // form x * 0 = 0 for each input.
            None,
            Some(&mut self.a_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.b.push(Scalar(eval(
            &b,
            Some(&mut self.b_input_density),
            Some(&mut self.b_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.c.push(Scalar(eval(
            &c,
            // There is no C polynomial query,
            // though there is an (beta)A + (alpha)B + C
            // query for all aux variables.
            // However, that query has full density.
            None,
            None,
            &self.input_assignment,
            &self.aux_assignment,
        )));
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

impl<E: Engine, S: PrimeField> RandomConstraintSystem<S> for ProvingAssignment<'_, E, S> {
    fn alloc_random_coin<A, AR>(&mut self, annotation: A) -> Result<(Variable, S), SynthesisError>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // There is no assingment, so we don't do compute anything...
        // There is no assingment, so we don't do compute anything...
        if self.coins_done {
            return Err(SynthesisError::LateRandomCoin);
        }

        // TODO: compute random coin...
        //let coin =
        //self.input_assignment.push(S::one());
        let coin = self.fiat_shamir_coin(self.coin_inds.len());
        self.input_assignment.push(coin);
        self.coin_inds.push(self.input_assignment.len() - 1);
        self.b_input_density.add_element();

        Ok((
            Variable(Index::Input(self.input_assignment.len() - 1)),
            coin,
        ))
    }
}

pub fn create_random_proof<E, C, R, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    mut rng: &mut R,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    E::Fr: PrimeFieldBits,
    C: RandomCircuit<E::Fr>,
    R: RngCore,
{
    let r = E::Fr::random(&mut rng);
    let s = E::Fr::random(&mut rng);
    let t = E::Fr::random(&mut rng);

    create_proof::<E, C, P>(circuit, params, r, s, t)
}

#[allow(clippy::many_single_char_names)]
pub fn create_proof<E, C, P: ParameterSource<E>>(
    circuit: C,
    mut params: P,
    r: E::Fr,
    s: E::Fr,
    _t: E::Fr,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    E::Fr: PrimeFieldBits,
    C: RandomCircuit<E::Fr>,
{
    let vk = params.get_vk(0)?;
    let j = params.get_j(0).unwrap();

    // TODO: gross....
    let get_pid = |nonrand: &Vec<<E as Engine>::Fr>, numnonrand: usize| {
        let mut g_d = vk.delta_g1 * _t;
        let worker = Worker::new();

        let aux_nonrand_assignment =
            Arc::new(nonrand.into_iter().map(|s| s.into()).collect::<Vec<_>>());

        let j = multiexp(
            &worker,
            j.clone(),
            FullDensity,
            aux_nonrand_assignment.clone(),
        );

        AddAssign::<&E::G1>::add_assign(&mut g_d, &j.wait().unwrap());
        let res: E::G1Affine = g_d.to_affine();
        res
    };

    let mut prover: ProvingAssignment<E, <E as Engine>::Fr> = ProvingAssignment {
        a_aux_density: DensityTracker::new(),
        b_input_density: DensityTracker::new(),
        b_aux_density: DensityTracker::new(),
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![],
        nonrand_aux_assignment: vec![],
        rand_aux_assignment: vec![],

        num_nonrandom: 0,
        coin_inds: vec![],
        coins_done: false,

        d: None,
        get_d: &get_pid,
    };

    prover.alloc_input(|| "", || Ok(E::Fr::one()))?;

    circuit.synthesize(&mut prover)?;

    //let coins = prover
    //    .coin_inds
    //    .iter()
    //    .map(|i| prover.input_assignment[*i])
    //    .collect();
    //println!("Got coins {:?}", coins);

    for i in 0..prover.input_assignment.len() {
        prover.enforce(|| "", |lc| lc + Variable(Index::Input(i)), |lc| lc, |lc| lc);
    }

    let worker = Worker::new();

    let h = {
        let mut a = EvaluationDomain::from_coeffs(prover.a)?;
        let mut b = EvaluationDomain::from_coeffs(prover.b)?;
        let mut c = EvaluationDomain::from_coeffs(prover.c)?;
        a.ifft(&worker);
        a.coset_fft(&worker);
        b.ifft(&worker);
        b.coset_fft(&worker);
        c.ifft(&worker);
        c.coset_fft(&worker);

        a.mul_assign(&worker, &b);
        drop(b);
        a.sub_assign(&worker, &c);
        drop(c);
        a.divide_by_z_on_coset(&worker);
        a.icoset_fft(&worker);
        let mut a = a.into_coeffs();
        let a_len = a.len() - 1;
        a.truncate(a_len);
        // TODO: parallelize if it's even helpful
        let a = Arc::new(a.into_iter().map(|s| s.0.into()).collect::<Vec<_>>());

        multiexp(&worker, params.get_h(a.len())?, FullDensity, a)
    };

    println!("nonrand aux: {:?}", prover.nonrand_aux_assignment);
    println!("rand aux: {:?}", prover.rand_aux_assignment);

    // TODO: parallelize if it's even helpful
    let input_assignment = Arc::new(
        prover
            .input_assignment
            .into_iter()
            .map(|s| s.into())
            .collect::<Vec<_>>(),
    );
    let aux_assignment = Arc::new(
        prover
            .aux_assignment
            .clone()
            .into_iter()
            .map(|s| s.into())
            .collect::<Vec<_>>(),
    );
    let aux_nonrand_assignment = Arc::new(
        prover
            .nonrand_aux_assignment
            .into_iter()
            .map(|s| s.into())
            .collect::<Vec<_>>(),
    );
    let aux_rand_assignment = Arc::new(
        prover
            .rand_aux_assignment
            .into_iter()
            .map(|s| s.into())
            .collect::<Vec<_>>(),
    );

    let j = multiexp(
        &worker,
        params.get_j(prover.num_nonrandom)?,
        FullDensity,
        aux_nonrand_assignment.clone(),
    );

    println!("ok2");
    let l = multiexp(
        &worker,
        params.get_l(aux_assignment.len() - prover.num_nonrandom)?,
        FullDensity,
        aux_rand_assignment.clone(),
    );
    println!("ok3");

    let a_aux_density_total = prover.a_aux_density.get_total_density();

    let (a_inputs_source, a_aux_source) =
        params.get_a(input_assignment.len(), a_aux_density_total)?;

    let a_inputs = multiexp(
        &worker,
        a_inputs_source,
        FullDensity,
        input_assignment.clone(),
    );
    let a_aux = multiexp(
        &worker,
        a_aux_source,
        Arc::new(prover.a_aux_density),
        aux_assignment.clone(),
    );

    let b_input_density = Arc::new(prover.b_input_density);
    let b_input_density_total = b_input_density.get_total_density();
    let b_aux_density = Arc::new(prover.b_aux_density);
    let b_aux_density_total = b_aux_density.get_total_density();

    let (b_g1_inputs_source, b_g1_aux_source) =
        params.get_b_g1(b_input_density_total, b_aux_density_total)?;

    let b_g1_inputs = multiexp(
        &worker,
        b_g1_inputs_source,
        b_input_density.clone(),
        input_assignment.clone(),
    );
    let b_g1_aux = multiexp(
        &worker,
        b_g1_aux_source,
        b_aux_density.clone(),
        aux_assignment.clone(),
    );

    let (b_g2_inputs_source, b_g2_aux_source) =
        params.get_b_g2(b_input_density_total, b_aux_density_total)?;

    let b_g2_inputs = multiexp(
        &worker,
        b_g2_inputs_source,
        b_input_density,
        input_assignment,
    );
    let b_g2_aux = multiexp(&worker, b_g2_aux_source, b_aux_density, aux_assignment);

    if bool::from(vk.delta_g1.is_identity() | vk.delta_g2.is_identity()) {
        // If this element is zero, someone is trying to perform a
        // subversion-CRS attack.
        return Err(SynthesisError::UnexpectedIdentity);
    }

    let mut g_a = vk.delta_g1 * r;
    AddAssign::<&E::G1Affine>::add_assign(&mut g_a, &vk.alpha_g1);
    let mut g_b = vk.delta_g2 * s;
    AddAssign::<&E::G2Affine>::add_assign(&mut g_b, &vk.beta_g2);
    let mut g_c;
    {
        let mut rs = r;
        rs.mul_assign(&s);

        g_c = vk.delta_g1 * rs;
        use std::ops::Neg;
        AddAssign::<&E::G1>::add_assign(&mut g_c, &(vk.deltap_g1.neg() * _t));
        AddAssign::<&E::G1>::add_assign(&mut g_c, &(vk.alpha_g1 * s));
        AddAssign::<&E::G1>::add_assign(&mut g_c, &(vk.beta_g1 * r));
    }
    let mut g_d = vk.delta_g1 * _t;
    let mut a_answer = a_inputs.wait()?;
    AddAssign::<&E::G1>::add_assign(&mut a_answer, &a_aux.wait()?);
    AddAssign::<&E::G1>::add_assign(&mut g_a, &a_answer);
    MulAssign::<E::Fr>::mul_assign(&mut a_answer, s);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &a_answer);

    let mut b1_answer: E::G1 = b_g1_inputs.wait()?;
    AddAssign::<&E::G1>::add_assign(&mut b1_answer, &b_g1_aux.wait()?);
    let mut b2_answer = b_g2_inputs.wait()?;
    AddAssign::<&E::G2>::add_assign(&mut b2_answer, &b_g2_aux.wait()?);

    AddAssign::<&E::G2>::add_assign(&mut g_b, &b2_answer);
    MulAssign::<E::Fr>::mul_assign(&mut b1_answer, r);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &b1_answer);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &h.wait()?);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &l.wait()?);

    AddAssign::<&E::G1>::add_assign(&mut g_d, &j.wait()?);
    //AddAssign::<&E::G1>::add_assign(&mut g_d, &j.wait()?);

    Ok(Proof {
        a: g_a.to_affine(),
        b: g_b.to_affine(),
        c: g_c.to_affine(),
        d: g_d.to_affine(),
        //coins,
    })
}
