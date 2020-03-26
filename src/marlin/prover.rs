use crate::marlin::indexer::{Index, MatrixEncoding, MatrixType};
use crate::marlin::oracles::Oracles;
use crate::multicore::Worker;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::Engine;
use crate::plonk::polynomials::{Coefficients, Polynomial, Values};
use crate::{
    Circuit, ConstraintSystem, Index as VariableIndex, LinearCombination, SynthesisError, Variable,
};
use rand::{Rand, Rng};
use std::collections::HashMap;

pub fn create_proof<'a, E: Engine, C: Circuit<E>, R: Rng>(
    worker: &Worker,
    index: &Index<E>,
    circuit: C,
    rng: &mut R,
) -> Result<Proof<'a, E>, SynthesisError> {
    let mut prover = Prover::new();
    circuit.synthesize(&mut prover)?;
    prover.make_matrix_square();
    prover.prove(worker, index, rng)
}

#[derive(Clone)]
pub struct ProofEvaluations<'a, E: Engine> {
    pub at_beta_one: HashMap<&'a str, E::Fr>,
    pub at_beta_two: HashMap<&'a str, E::Fr>,
    pub at_beta_three: HashMap<&'a str, E::Fr>,
}

#[derive(Clone)]
pub struct Proof<'a, E: Engine> {
    pub evals: ProofEvaluations<'a, E>,
    pub oracles: Oracles<E>,
    pub sigma_two: E::Fr,
    pub sigma_three: E::Fr,
}

pub struct Prover<E: Engine> {
    // Assignments of variables
    pub(crate) input_assignment: Vec<E::Fr>,
    pub(crate) witness_assignment: Vec<E::Fr>,
    pub(crate) num_input_variables: usize,
    pub(crate) num_witness_variables: usize,
    pub(crate) num_constraints: usize,
}
impl<E: Engine> ConstraintSystem<E> for Prover<E> {
    type Root = Self;

    #[inline]
    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.num_witness_variables;
        self.num_witness_variables += 1;

        self.witness_assignment.push(f()?);
        Ok(Variable(VariableIndex::Aux(index)))
    }

    #[inline]
    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.num_input_variables;
        self.num_input_variables += 1;

        self.input_assignment.push(f()?);
        Ok(Variable(VariableIndex::Input(index)))
    }

    #[inline]
    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _: LA, _: LB, _: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        self.num_constraints += 1;
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

impl<E: Engine> Prover<E> {
    pub fn new() -> Self {
        Self {
            input_assignment: vec![E::Fr::one()],
            witness_assignment: Vec::new(),
            num_input_variables: 1usize,
            num_witness_variables: 0usize,
            num_constraints: 0usize,
        }
    }

    pub fn prove<'b, R: Rng>(
        &self,
        worker: &Worker,
        index: &Index<E>,
        _rng: &R,
    ) -> Result<Proof<'b, E>, SynthesisError> {
        let input_variables = self.input_assignment.clone();
        let witness_variables = self.witness_assignment.clone();
        assert_eq!(
            self.num_constraints,
            input_variables.len() + witness_variables.len(),
            "matrix is not square"
        );

        // full assignment z = (x,w) ∊ F^H
        let z: Vec<E::Fr> = [&input_variables[..], &witness_variables[..]].concat();
        let z_a = index.a_index.matrix.linear_combination(&z);
        let z_b = index.b_index.matrix.linear_combination(&z);
        let z_a = Polynomial::from_values(z_a)?.ifft(worker).lde(worker, 2)?;
        let z_b = Polynomial::from_values(z_b)?.ifft(worker).lde(worker, 2)?;

        let mut z_c = z_a.clone();
        z_c.mul_assign(worker, &z_b);
    
        let zm = vec![z_a.clone(), z_b.clone(), z_c.clone()];        

        let z_a_poly = z_a.ifft(worker);
        let z_b_poly = z_b.ifft(worker);
        let z_c_poly = z_c.ifft(worker);

        // x'(X)
        let mut x_evals = Polynomial::from_values(input_variables.clone())?;
        let x_poly = x_evals.ifft(worker);
        let factor = (index.domains.h.size / index.domains.x.size) as usize;
        x_evals = x_poly.lde(worker, factor)?;
        let x_evals_vec = x_evals.into_coeffs();

        // w'(x) = (w(X)-x'(X)) / v_x(C)
        // first part: (w(X)-x'(X))
        let mut w = witness_variables.clone();
        w.extend(vec![
            E::Fr::zero();
            (index.domains.h.size - index.domains.x.size) as usize
                - witness_variables.len()
        ]);
        let w_evals: Vec<_> = (0..(index.domains.h.size as usize))
            .into_iter()
            .map(|i| {
                if i % factor == 0 {
                    E::Fr::zero() // replace x with zero
                } else {
                    let mut tmp = w[i - (i / factor) - 1].clone();
                    tmp.sub_assign(&x_evals_vec[i]);
                    tmp
                }
            })
            .collect();
        // second part: (w(X)-x'(X)) / v_x(X)
        let w_poly = Polynomial::from_values(w_evals)?.ifft(worker);
        let (w_hat_poly, remainder) = w_poly.divide_by_vanishing_poly(index.domains.x)?;
        assert!(remainder.is_zero());

        // Verifier challenges
        let mut oracles = Oracles::new();
        oracles.alpha = E::Fr::from_str("43").expect("must construct a field element");
        oracles.eta_a = E::Fr::from_str("47").expect("must construct a field element");
        oracles.eta_b = E::Fr::from_str("53").expect("must construct a field element");
        oracles.eta_c = E::Fr::from_str("57").expect("must construct a field element");
        oracles.beta_one = E::Fr::from_str("63").expect("must construct a field element");
        oracles.beta_two = E::Fr::from_str("67").expect("must construct a field element");
        oracles.beta_three = E::Fr::from_str("73").expect("must construct a field element");

        // u(⍺, X) = (v(⍺) - v(X)) / (⍺-X)
        let r_alpha_evals = index
            .domains
            .h
            .evaluate_bivariate_polynomial_with_diff_inputs(
                worker,
                &index.elements_of_domain_h,
                oracles.alpha,
            );
        let r_alpha = Polynomial::from_values(r_alpha_evals)?.ifft(worker);

        let (h1, g1) = self.sumcheck_one(
            worker,
            index,
            r_alpha.clone(),
            w_hat_poly.clone(),
            zm,
            &oracles,
            &input_variables,
        )?;

        let (sigma2, h2, g2) = self.sumcheck_two(
            worker, 
            index, 
            r_alpha, 
            &oracles
        )?;

        let (sigma3, h3, g3) = self.sumcheck_three(
            worker, 
            index, 
            &oracles
        )?;

        // After integrating polynomial commitment scheme all these hash-map structure will be replaced with an elegant solution.
        let mut beta_one_evals: HashMap<&str, E::Fr> = HashMap::new();
        beta_one_evals.insert("h1", h1.evaluate_at(worker, oracles.beta_one));
        beta_one_evals.insert("g1", g1.evaluate_at(worker, oracles.beta_one));
        beta_one_evals.insert("w", w_hat_poly.evaluate_at(worker, oracles.beta_one));
        beta_one_evals.insert("za", z_a_poly.evaluate_at(worker, oracles.beta_one));
        beta_one_evals.insert("zb", z_b_poly.evaluate_at(worker, oracles.beta_one));
        beta_one_evals.insert("zc", z_c_poly.evaluate_at(worker, oracles.beta_one));
        let mut beta_two_evals: HashMap<&str, E::Fr> = HashMap::new();
        beta_two_evals.insert("h2", h2.evaluate_at(worker, oracles.beta_two));
        beta_two_evals.insert("g2", g2.evaluate_at(worker, oracles.beta_two));
        let mut beta_three_evals: HashMap<&str, E::Fr> = HashMap::new();
        beta_three_evals.insert("h3", h3.evaluate_at(worker, oracles.beta_three));
        beta_three_evals.insert("g3", g3.evaluate_at(worker, oracles.beta_three));
        beta_three_evals.insert(
            "a_row", index.a_index.row_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "a_col", index.a_index.col_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "a_val",index.a_index.val_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "b_row",index.b_index.row_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "b_col",index.b_index.col_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "b_val",index.b_index.val_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "c_row",index.c_index.row_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "c_col",index.c_index.col_poly.evaluate_at(worker, oracles.beta_three),
        );
        beta_three_evals.insert(
            "c_val",index.c_index.val_poly.evaluate_at(worker, oracles.beta_three),
        );

        let proof_evals = ProofEvaluations {
            at_beta_one: beta_one_evals,
            at_beta_two: beta_two_evals,
            at_beta_three: beta_three_evals,
        };

        let proof = Proof {
            evals: proof_evals,
            oracles,
            sigma_two: sigma2,
            sigma_three: sigma3,
        };
        Ok(proof)
    }

    // q1(X) = s(X) + r(⍺, X)*( ήa*z'A(X) + ήb*z'B(X) + ή*z'C(X) ) - (z'(X)*(ήa*rA(⍺,X) +ήb*rB(⍺,X) + ήc*rC(⍺,x)))
    fn sumcheck_one(
        &self,
        worker: &Worker,
        index: &Index<E>,
        r_alpha: Polynomial<E::Fr, Coefficients>,
        w: Polynomial<E::Fr, Coefficients>,
        zm: Vec<Polynomial<E::Fr, Values>>,
        oracles: &Oracles<E>,
        input_variables: &[E::Fr],
    ) -> Result<
        (
            Polynomial<E::Fr, Coefficients>,
            Polynomial<E::Fr, Coefficients>,
        ),
        SynthesisError,
    > {
        let mut zm = zm.clone();
        zm[0].scale(worker, oracles.eta_a);
        zm[1].scale(worker, oracles.eta_b);
        zm[2].scale(worker, oracles.eta_c);
        let mut sum_zm = zm[0].clone();
        sum_zm.add_assign(worker, &zm[1]);
        sum_zm.add_assign(worker, &zm[2]);
        let mut sum_zm = sum_zm.ifft(worker).lde(worker, 2)?;
        let r_alpha = r_alpha.lde(worker, 4)?;
        sum_zm.mul_assign(worker, &r_alpha);

        // part 2 : z'(X)*( ήa*rA(⍺,X) + ήb*rB(⍺,X) + ήc*rC(⍺,x) )
        let precomputed_bivariate_evaluations_same_inputs = index
            .precomputed_bivariate_poly_with_same_inputs_on_domain_h
            .as_ref();
        let precomputed_evaluations_of_bivariate_poly_with_diff_inputs = index
            .domains
            .h
            .evaluate_bivariate_polynomial_with_diff_inputs(
                worker,
                &index.elements_of_domain_h,
                oracles.alpha,
            );
            
        // rM(⍺,X)
        // formula: u_H(col(κ_2),col(κ_2))*val(κ_2)*r(⍺,row(κ_2))*u_H(row(κ_2),row(κ_2))
        fn compute_r_m_for_matrix<E: Engine>(
            worker: &Worker,
            matrix: MatrixEncoding<E>,
            precomputed_bivariate_evaluations_same_inputs: &[E::Fr],
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs: &[E::Fr],
            domain_h_size: usize,
        ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
            // iterate through domain K; we can use column length as loop size
            let loop_size = matrix.val_evals_on_k.len();
            let val_evals = &matrix.val_evals_on_k;
            // let val_evals = &matrix.val_evals_on_k.clone();
            // Lemma 5.5
            // Initialize for each κ1 ∈ H a variable for rM(α,κ1) that is initially set to 0.
            // Then, for each κ2 ∈ K, compute the term uH (col(κ2), col(κ2))val(κ2)r(α, row(κ2))uH (row(κ2), row(κ2))
            // and add it to the variable for rM (α, col(κ2)).
            // Concurrent threads may write to same slot in array allocated for rM (α, col(κ2)).
            //
            // In order to prevent race-conditions we use 2-D array. Each thread has its own storage that has length of domain size.
            // We split this process into two phases:
            // 1. During computation each thread updates its own storage. 
            // 2. At the end of parallel computation we need to aggregate each slot in each storage of corresponding thread.

            let number_of_chunks = worker.get_num_spawned_threads(domain_h_size);
            let mut chunks_evaluations = vec![vec![E::Fr::zero(); domain_h_size]; number_of_chunks];
            // phase one
            worker.scope(loop_size, |scope, chunk_size| {
                for (chunk_id, ((eval_chunk, col_index_chunk), row_index_chunk)) in
                    chunks_evaluations
                        .chunks_mut(1)
                        .zip(matrix.col_indexes_on_domain_h.chunks(chunk_size))
                        .zip(matrix.row_indexes_on_domain_h.chunks(chunk_size))
                        .enumerate()
                {
                    scope.spawn(move |_| {
                        let chunk_storage = &mut eval_chunk[0];
                        let offset = chunk_id * chunk_size;
                        for (i, (col_index, row_index)) in col_index_chunk
                            .iter()
                            .zip(row_index_chunk.iter())
                            .enumerate()
                        {
                            let evaluation_of_bivariate_on_col_k_2 =
                                precomputed_bivariate_evaluations_same_inputs[*col_index];
                            let evaluation_of_bivariate_on_row_k_2 =
                                precomputed_bivariate_evaluations_same_inputs[*row_index];
                            let evaluation_of_r_alpha_on_domain_h =
                                precomputed_evaluations_of_bivariate_poly_with_diff_inputs
                                    [*row_index];
                            let mut result = val_evals[offset + i].clone();
                            result.mul_assign(&evaluation_of_bivariate_on_col_k_2);
                            result.mul_assign(&evaluation_of_bivariate_on_row_k_2);
                            result.mul_assign(&evaluation_of_r_alpha_on_domain_h);
                            chunk_storage[*col_index].add_assign(&result);
                        }
                    });
                }
            });
            // phase two
            let chunks_evaluations_for_worker = &chunks_evaluations;
            let mut final_evals = vec![E::Fr::zero(); domain_h_size];
            worker.scope(domain_h_size, |scope, chunk_size| {
                for (chunk_id, chunk) in final_evals.chunks_mut(chunk_size).enumerate() {
                    scope.spawn(move |_| {
                        let offset = chunk_id * chunk_size;
                        for (i, chunk_slot) in chunk.iter_mut().enumerate() {
                            for previous_chunk_slot in chunks_evaluations_for_worker {
                                chunk_slot.add_assign(&previous_chunk_slot[offset + i]);
                            }
                        }
                    });
                }
            });

            Polynomial::from_values(final_evals)
        }

        let output_domain_size = index.domains.h.size as usize;
        // r_A(alpha, X) over domain K
        let mut r_a_alpha_over_k = compute_r_m_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::A),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        r_a_alpha_over_k.scale(worker, oracles.eta_a);

        // r_B(alpha, X) over domain K
        let mut r_b_alpha_over_k = compute_r_m_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::B),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        r_b_alpha_over_k.scale(worker, oracles.eta_b);

        // r_X(alpha, X) over domain K
        let mut r_c_alpha_over_k = compute_r_m_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::C),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        r_c_alpha_over_k.scale(worker, oracles.eta_c);

        let mut sum_r_m_alpha_over_k = r_a_alpha_over_k.clone();
        sum_r_m_alpha_over_k.add_assign(worker, &r_b_alpha_over_k);
        sum_r_m_alpha_over_k.add_assign(worker, &r_c_alpha_over_k);
        let mut sum_r_m_alpha_over_k = sum_r_m_alpha_over_k.ifft(worker).lde(worker, 4)?;
        // z(x) = w'(x)*v_x(x) + x(X)
        let mut z = w.mul_by_vanishing_poly(index.domains.x).lde(worker, 2)?;
        let x = Polynomial::from_values(input_variables.to_vec())?;
        // TODO: why computation fails with x.lde() ??
        // let factor = z.size() / x.size();
        // let x = x.ifft(worker).lde(worker, factor)?;
        let mut x = x.ifft(worker);
        x.pad_to_size(z.size())?;
        let x = x.fft(worker);
        z.add_assign(worker, &x);
        // z'(x) * sum_r_m
        sum_r_m_alpha_over_k.mul_assign(&worker, &z);

        let mut q1 = sum_zm.clone();
        q1.sub_assign(worker, &sum_r_m_alpha_over_k);
        let q1 = q1.ifft(worker);

        let (h1, x_g1) = q1.divide_by_vanishing_poly(index.domains.h)?;
        let mut g1_coeffs = x_g1.into_coeffs();
        g1_coeffs.remove(0);
        let g1 = Polynomial::from_coeffs(g1_coeffs)?;

        Ok((h1, g1))
    }
    // q2(X) = r(⍺, X)*(ήa*A(X,β_1) + ήb*B(X,β_1) + ή*C(X,β_1) ))
    fn sumcheck_two(
        &self,
        worker: &Worker,
        index: &Index<E>,
        r_alpha: Polynomial<E::Fr, Coefficients>,
        oracles: &Oracles<E>,
    ) -> Result<
        (
            E::Fr,
            Polynomial<E::Fr, Coefficients>,
            Polynomial<E::Fr, Coefficients>,
        ),
        SynthesisError,
    > {
        let precomputed_bivariate_evaluations_same_inputs = index
            .precomputed_bivariate_poly_with_same_inputs_on_domain_h
            .as_ref();
        let precomputed_evaluations_of_bivariate_poly_with_diff_inputs = index
            .domains
            .h
            .evaluate_bivariate_polynomial_with_diff_inputs(
                worker,
                &index.elements_of_domain_h,
                oracles.beta_one,
            );
        // formula: u_H(row(κ_2),row(κ_2))*u_H(beta_one,col(κ_2))*val(κ_2)
        fn compute_m_beta_one_for_matrix<E: Engine>(
            worker: &Worker,
            matrix: MatrixEncoding<E>,
            precomputed_bivariate_evaluations_same_inputs: &[E::Fr],
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs: &[E::Fr],
            domain_h_size: usize,
        ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
            let loop_size = matrix.val_evals_on_k.len();
            let val_evals = &matrix.val_evals_on_k;

            let number_of_chunks = worker.get_num_spawned_threads(domain_h_size);
            let mut chunks_evaluations = vec![vec![E::Fr::zero(); domain_h_size]; number_of_chunks];

            worker.scope(loop_size, |scope, chunk_size| {
                for (chunk_id, ((eval_chunk, col_index_chunk), row_index_chunk)) in
                    chunks_evaluations
                        .chunks_mut(1)
                        .zip(matrix.col_indexes_on_domain_h.chunks(chunk_size))
                        .zip(matrix.row_indexes_on_domain_h.chunks(chunk_size))
                        .enumerate()
                {
                    scope.spawn(move |_| {
                        let chunk_storage = &mut eval_chunk[0];
                        let offset = chunk_id * chunk_size;
                        for (i, (col_index, row_index)) in col_index_chunk
                            .iter()
                            .zip(row_index_chunk.iter())
                            .enumerate()
                        {
                            let evaluation_of_bivariate_on_row_k_2 =
                                precomputed_bivariate_evaluations_same_inputs[*row_index];
                            let evaluation_of_r_beta_one_on_domain_h =
                                precomputed_evaluations_of_bivariate_poly_with_diff_inputs
                                    [*col_index];
                            let mut result = val_evals[offset + i].clone();
                            result.mul_assign(&evaluation_of_bivariate_on_row_k_2);
                            result.mul_assign(&evaluation_of_r_beta_one_on_domain_h);
                            chunk_storage[*row_index].add_assign(&result);
                        }
                    });
                }
            });
            let chunks_evaluations_for_worker = &chunks_evaluations;
            let mut final_evals = vec![E::Fr::zero(); domain_h_size];
            worker.scope(domain_h_size, |scope, chunk_size| {
                for (chunk_id, chunk) in final_evals.chunks_mut(chunk_size).enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        for (i, chunk_slot) in chunk.iter_mut().enumerate() {
                            for previous_chunk_slot in chunks_evaluations_for_worker {
                                chunk_slot.add_assign(&previous_chunk_slot[start + i]);
                            }
                        }
                    });
                }
            });
            Polynomial::from_values(final_evals)
        }

        let output_domain_size = index.domains.h.size as usize;
        // A(X, beta_one) on domain K
        let mut a_beta_one_over_k = compute_m_beta_one_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::A),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        a_beta_one_over_k.scale(worker, oracles.eta_a);

        // B(X, beta_one) on domain K
        let mut b_beta_one_over_k = compute_m_beta_one_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::B),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        b_beta_one_over_k.scale(worker, oracles.eta_b);

        // C(X, beta_one) on domain K
        let mut c_beta_one_over_k = compute_m_beta_one_for_matrix(
            worker,
            index.get_matrix_encoding(MatrixType::C),
            precomputed_bivariate_evaluations_same_inputs,
            precomputed_evaluations_of_bivariate_poly_with_diff_inputs.as_ref(),
            output_domain_size,
        )?;
        c_beta_one_over_k.scale(worker, oracles.eta_c);

        let mut sum_m_beta_one_over_k = a_beta_one_over_k.clone();
        sum_m_beta_one_over_k.add_assign(worker, &b_beta_one_over_k);
        sum_m_beta_one_over_k.add_assign(worker, &c_beta_one_over_k);
        let mut sum_m_beta_one_over_k = sum_m_beta_one_over_k.ifft(worker).lde(worker, 2)?;

        let r_alpha = r_alpha.lde(worker, 2)?;
        sum_m_beta_one_over_k.mul_assign(worker, &r_alpha);
        let q2 = sum_m_beta_one_over_k.ifft(worker);

        let (h2, x_g2) = q2.divide_by_vanishing_poly(index.domains.h)?;
        let mut g2_coeffs = x_g2.into_coeffs();
        let sigma2 = g2_coeffs[0];
        g2_coeffs.remove(0);
        let g2 = Polynomial::from_coeffs(g2_coeffs)?;
        Ok((sigma2, h2, g2))
    }

    // a(x) - b(x) * f_3(x)
    fn sumcheck_three(
        &self,
        worker: &Worker,
        index: &Index<E>,
        oracles: &Oracles<E>,
    ) -> Result<
        (
            E::Fr,
            Polynomial<E::Fr, Coefficients>,
            Polynomial<E::Fr, Coefficients>,
        ),
        SynthesisError,
    > {
        fn compute_denominator_of_f3_for_matrix<E: Engine>(
            worker: &Worker,
            matrix: MatrixEncoding<E>,
            beta_one: &Polynomial<E::Fr, Values>,
            beta_two: &Polynomial<E::Fr, Values>,
            scale_factor: E::Fr,
        ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
            // evaluations of univariate polynomials on domain K
            let row_evals = matrix.row_poly.fft(worker);
            let col_evals = matrix.col_poly.fft(worker);
            let val_evals = matrix.val_poly.fft(worker);

            // f_3(κ)= (v_h(β_2)*v_h(β_1)*val(κ))/((β_2-row(κ))*(β_1-col(κ)))\
            let mut tmp = beta_two.clone();
            tmp.sub_assign(worker, &row_evals);
            let mut denominator = beta_one.clone();
            denominator.sub_assign(worker, &col_evals);
            denominator.mul_assign(worker, &tmp);
            denominator.batch_inversion(worker)?;
            denominator.mul_assign(worker, &val_evals);
            denominator.scale(worker, scale_factor);
            Ok(denominator)
        }

        let beta_one_evals =
            Polynomial::from_values(vec![oracles.beta_one; index.domains.k.size as usize])?;
        let beta_two_evals =
            Polynomial::from_values(vec![oracles.beta_two; index.domains.k.size as usize])?;

        let evals_a_for_f3 = compute_denominator_of_f3_for_matrix::<E>(
            worker,
            index.get_matrix_encoding(MatrixType::A),
            &beta_one_evals,
            &beta_two_evals,
            oracles.eta_a,
        )?;

        let evals_b_for_f3 = compute_denominator_of_f3_for_matrix::<E>(
            worker,
            index.get_matrix_encoding(MatrixType::B),
            &beta_one_evals,
            &beta_two_evals,
            oracles.eta_b,
        )?;

        let evals_c_for_f3 = compute_denominator_of_f3_for_matrix::<E>(
            worker,
            index.get_matrix_encoding(MatrixType::C),
            &beta_one_evals,
            &beta_two_evals,
            oracles.eta_c,
        )?;

        // f_3(κ)= (v_h(β_2)*v_h(β_1)*val(κ))/((β_2-row(κ))*(β_1-col(κ)))\
        let mut vanishing_of_domain_h_at_beta_one_and_beta_two = index
            .domains
            .h
            .evaluate_vanishing_polynomial_at(oracles.beta_one);
        let vanishing_of_domain_h_at_beta_two = index
            .domains
            .h
            .evaluate_vanishing_polynomial_at(oracles.beta_two);
        vanishing_of_domain_h_at_beta_one_and_beta_two
            .mul_assign(&vanishing_of_domain_h_at_beta_two);

        let mut f3 = evals_a_for_f3.clone();
        f3.add_assign(worker, &evals_b_for_f3);
        f3.add_assign(worker, &evals_c_for_f3);
        f3.scale(worker, vanishing_of_domain_h_at_beta_one_and_beta_two);

        fn compute_evaluations_on_domain_b<E: Engine>(
            worker: &Worker,
            matrix: &MatrixEncoding<E>,
            size_of_domain_b: usize,
        ) -> Result<
            (
                Polynomial<E::Fr, Values>,
                Polynomial<E::Fr, Values>,
                Polynomial<E::Fr, Values>,
            ),
            SynthesisError,
        > {
            // TODO:
            // let factor = (index.domains.b.size / index.domains.k.size) as usize;
            // let tmp = index.a_index.row_poly.clone().lde(worker, factor)?;
            let mut row_evals_on_b = matrix.row_poly.clone();
            row_evals_on_b.pad_to_size(size_of_domain_b)?;
            let row_evals_on_b = row_evals_on_b.fft(worker);

            let mut col_evals_on_b = matrix.col_poly.clone();
            col_evals_on_b.pad_to_size(size_of_domain_b)?;
            let col_evals_on_b = col_evals_on_b.fft(worker);
            let mut val_evals_on_b = matrix.val_poly.clone();
            val_evals_on_b.pad_to_size(size_of_domain_b)?;
            let val_evals_on_b = val_evals_on_b.fft(worker);

            Ok((row_evals_on_b, col_evals_on_b, val_evals_on_b))
        }

        let beta_one_evals =
            Polynomial::from_values(vec![oracles.beta_one; index.domains.b.size as usize])?;
        let beta_two_evals =
            Polynomial::from_values(vec![oracles.beta_two; index.domains.b.size as usize])?;

        let size_of_domain_b = index.domains.b.size as usize;
        let a_evals_on_domain_b =
            compute_evaluations_on_domain_b(worker, &index.a_index, size_of_domain_b)?;
        let b_evals_on_domain_b =
            compute_evaluations_on_domain_b(worker, &index.b_index, size_of_domain_b)?;
        let c_evals_on_domain_b =
            compute_evaluations_on_domain_b(worker, &index.c_index, size_of_domain_b)?;

        // A
        // β_2 - row(x) evals
        let mut a_beta_two_minus_row = beta_two_evals.clone();
        a_beta_two_minus_row.sub_assign(worker, &a_evals_on_domain_b.0);

        // β_1 - col(x) evals
        let mut a_beta_one_minus_col = beta_one_evals.clone();
        a_beta_one_minus_col.sub_assign(worker, &a_evals_on_domain_b.1);
        // B
        // β_2 - row(x) evals
        let mut b_beta_two_minus_row = beta_two_evals.clone();
        b_beta_two_minus_row.sub_assign(worker, &b_evals_on_domain_b.0);

        // β_1 - col(x) evals
        let mut b_beta_one_minus_col = beta_one_evals.clone();
        b_beta_one_minus_col.sub_assign(worker, &b_evals_on_domain_b.1);

        // C
        // β_2 - row(x) evals
        let mut c_beta_two_minus_row = beta_two_evals.clone();
        c_beta_two_minus_row.sub_assign(worker, &c_evals_on_domain_b.0);

        // β_1 - col(x) evals
        let mut c_beta_one_minus_col = beta_one_evals.clone();
        c_beta_one_minus_col.sub_assign(worker, &c_evals_on_domain_b.1);

        // b(x) = π_{A,B,C}{(β_2-row_M(x))*(β_1-col_M(x)))}
        let mut a_beta_one_row_beta_two_col = a_beta_two_minus_row.clone();
        a_beta_one_row_beta_two_col.mul_assign(worker, &a_beta_one_minus_col);
        let mut b_beta_one_row_beta_two_col = b_beta_two_minus_row.clone();
        b_beta_one_row_beta_two_col.mul_assign(worker, &b_beta_one_minus_col);

        let mut c_beta_one_row_beta_two_col = c_beta_two_minus_row.clone();
        c_beta_one_row_beta_two_col.mul_assign(worker, &c_beta_one_minus_col);

        let mut b_x = a_beta_one_row_beta_two_col.clone();
        b_x.mul_assign(worker, &b_beta_one_row_beta_two_col);
        b_x.mul_assign(worker, &c_beta_one_row_beta_two_col);

        // a(x) = Σ_{M∊{A,B,C}}{ ή_M*v_H(β_2)*v_h(β_1)*val_M(κ)* (ᴨ_{N∊{A,B,C}\{M}}((β_2-row_N(l))*(β_1-col_N(l)))}

        // A
        let mut a_part_for_a_x = b_beta_one_row_beta_two_col.clone();
        a_part_for_a_x.mul_assign(worker, &c_beta_one_row_beta_two_col);
        a_part_for_a_x.mul_assign(worker, &a_evals_on_domain_b.2);
        a_part_for_a_x.scale(worker, vanishing_of_domain_h_at_beta_one_and_beta_two);
        a_part_for_a_x.scale(worker, oracles.eta_a);
        // B
        let mut b_part_for_a_x = a_beta_one_row_beta_two_col.clone();
        b_part_for_a_x.mul_assign(worker, &c_beta_one_row_beta_two_col);
        b_part_for_a_x.mul_assign(worker, &b_evals_on_domain_b.2);
        b_part_for_a_x.scale(worker, vanishing_of_domain_h_at_beta_one_and_beta_two);
        b_part_for_a_x.scale(worker, oracles.eta_b);
        // C
        let mut c_part_for_a_x = a_beta_one_row_beta_two_col.clone();
        c_part_for_a_x.mul_assign(worker, &b_beta_one_row_beta_two_col);
        c_part_for_a_x.mul_assign(worker, &c_evals_on_domain_b.2);
        c_part_for_a_x.scale(worker, vanishing_of_domain_h_at_beta_one_and_beta_two);
        c_part_for_a_x.scale(worker, oracles.eta_c);
        let mut a_x = a_part_for_a_x.clone();
        a_x.add_assign(worker, &b_part_for_a_x);
        a_x.add_assign(worker, &c_part_for_a_x);

        // result =  a(x) - f_3(x)*b(x)
        // TODO
        // let factor = (b_x.size() / f3.size()) as usize;
        // let factor = (index.domains.b.size/index.domains.k.size) as usize;
        let mut tmp = f3.clone().ifft(worker);
        tmp.pad_to_size(b_x.size())?;
        let mut tmp = tmp.fft(worker);
        assert!(b_x.size() == a_x.size() && tmp.size() == b_x.size());
        tmp.mul_assign(worker, &b_x);
        let mut result = a_x.clone();
        result.sub_assign(worker, &tmp);

        let (h3, remainder) = result
            .ifft(worker)
            .divide_by_vanishing_poly(index.domains.k)?;
        assert!(remainder.is_zero());

        let mut g3_coeffs = f3.ifft(worker).into_coeffs();
        let sigma3 = g3_coeffs[0];
        g3_coeffs.remove(0);
        let g3 = Polynomial::from_coeffs(g3_coeffs)?;

        Ok((sigma3, h3, g3))
    }

    // r: number of constraints = number of rows
    // c: number of non-zero = number of cols
    // dim = abs(r-c)
    pub fn make_matrix_square(&mut self) {
        let num_variables = self.num_input_variables + self.num_witness_variables; // alloc & alloc_input
        let diff = self.num_constraints as isize - num_variables as isize;
        if diff != 0 {
            self.pad_variables(diff as isize);
        }
        assert_eq!(
            self.num_input_variables + self.num_witness_variables,
            self.num_constraints,
            "padding failed"
        );
    }

    fn pad_variables(&mut self, diff: isize) {
        println!("matrix is not square. padding..");
        if diff < 0 {
            // needs more rows so enforcing
            for i in 0..diff.abs() {
                self.enforce(|| format!("enforcing {}", i), |lc| lc, |lc| lc, |lc| lc);
            }
        } else {
            // needs more inputs sor allocating
            for i in 0..diff.abs() {
                self.alloc(|| format!("padding {}", i), || Ok(E::Fr::one()))
                    .expect("");
            }
        }
    }
}
