use rand::{Rand, Rng};
use std::marker::PhantomData;
use crate::{Circuit, SynthesisError};
use crate::multicore::Worker;
use crate::pairing::Engine;
use crate::pairing::ff::{Field, PrimeField};
use crate::plonk::domains::Domain;
use crate::plonk::polynomials::{PolynomialForm, Polynomial, Coefficients, Values};
use crate::marlin::indexer::Index;
use crate::marlin::oracles::Oracles;
use crate::marlin::prover::Proof;

pub fn verify_proof<E: Engine>(worker: &Worker, index: &Index<E>, proof: &Proof<E>, public_input: &[E::Fr]) -> Result<bool, SynthesisError>{
    Verifier::verify(worker, index, proof, public_input)
}

pub struct Verifier<E: Engine>{
    phantom: PhantomData<E>,
}

impl<E: Engine> Verifier<E>{

    pub fn verify(worker: &Worker, index: &Index<E>, proof: &Proof<E>, public_input: &[E::Fr])-> Result<bool, SynthesisError>{
        let round_one = sumcheck_one(worker, index, proof, public_input)?;        
        let round_two = sumcheck_two(index, proof)?;
        let round_three = sumcheck_three(index, proof)?;
        [round_one, round_two, round_three].iter().enumerate().for_each(|(i,r)| if !r {println!("round {} failed", i+1)});

        Ok(round_one && round_two && round_three)
    }
}   

// s(beta_one) + [r(alpha, beta_one)*(eta_a*z_A(beta_one) + eta_b*z_B(beta_one) + eta_c*z_C(beta_one))] - (sigma_two*|H| * z(beta_one))
// ==
// h1(beta_one)*v_h(beta_one) + (beta_one*g1(beta_one)) + sigma_one 
// sigma_one can be omitted
fn sumcheck_one<E: Engine>(worker: &Worker, index: &Index<E>, proof: &Proof<E>, public_input: &[E::Fr])-> Result<bool, SynthesisError>{
    // lhs: s(beta_one) + [r(alpha, beta_one)*(eta_a*z_A(beta_one) + eta_b*z_B(beta_one) + eta_c*z_C(beta_one))] - (sigma_two*|H| * z(beta_one))
    // s(beta_one) can be omitted
    let mut numerator = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.alpha);
    let v_h_at_beta_one = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.beta_one);
    numerator.sub_assign(&v_h_at_beta_one);

    let mut denominator = proof.oracles.alpha.clone();
    denominator.sub_assign(&proof.oracles.beta_one);
    denominator = denominator.inverse().expect("must has inverse");

    let mut lhs = numerator.clone();
    lhs.mul_assign(&denominator);
    
    // query z evals
    let mut z_a = *proof.evals.at_beta_one.get("za").expect("must contain za"); 
    z_a.mul_assign(&proof.oracles.eta_a);
    let mut z_b = *proof.evals.at_beta_one.get("zb").expect("must contain zb"); 
    z_b.mul_assign(&proof.oracles.eta_b);
    let mut z_c = *proof.evals.at_beta_one.get("zc").expect("must contain zc"); 
    z_c.mul_assign(&proof.oracles.eta_c);
    let mut sum_zm = z_a.clone();
    sum_zm.add_assign(&z_b);
    sum_zm.add_assign(&z_c);
    lhs.mul_assign(&sum_zm);
    
    let mut tmp = proof.sigma_two.clone();
    let h_size = E::Fr::from_str(&index.domains.h.size.to_string()).expect("must construct a field element");
    tmp.mul_assign(&h_size);
    // compute z(beta_one) = w(beta_one)*v_x(beta_one) + x(beta_one)    
    let mut x_evals = vec![E::Fr::one()];
    x_evals.extend_from_slice(public_input);
    let x = Polynomial::from_values(x_evals)?;
    let x_at_beta_one = x.ifft(worker).evaluate_at(worker, proof.oracles.beta_one);    
    let mut z = *proof.evals.at_beta_one.get("w").expect("must contain w");
    let v_x_at_beta_one = index.domains.x.evaluate_vanishing_polynomial_at(proof.oracles.beta_one);
    z.mul_assign(&v_x_at_beta_one);
    z.add_assign(&x_at_beta_one);
    tmp.mul_assign(&z);
    lhs.sub_assign(&tmp);

    // rhs: h1(beta_one)*v_h(beta_one) + (beta_one*g1(beta_one)) + sigma_one 
    let h1 = proof.evals.at_beta_one.get("h1").expect("must contain h1");
    let g1 = proof.evals.at_beta_one.get("g1").expect("must contain g1");

    let mut rhs = h1.clone();
    rhs.mul_assign(&v_h_at_beta_one);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.mul_assign(&g1);
    rhs.add_assign(&tmp);
    Ok(lhs == rhs)
}

// r(alpha, beta_two) * (sigma_three*|K|) 
// ==
// h2(beta_two)*v_h(beta_two) + (beta_two*g2(beta_two)) + sigma_two
fn sumcheck_two<E: Engine>(index: &Index<E>, proof: &Proof<E>)-> Result<bool, SynthesisError>{
    // lhs: (sigma_three*|K|)* r(alpha, beta_two) = (v_h(alpha) - v_h(beta_two)) / (alpha - beta_two)
    let mut numerator = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.alpha);
    let v_h_at_beta_two = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.beta_two);
    numerator.sub_assign(&v_h_at_beta_two);

    let mut denominator = proof.oracles.alpha.clone();
    denominator.sub_assign(&proof.oracles.beta_two);
    denominator = denominator.inverse().expect("must has inverse");
    
    let mut lhs = numerator.clone();
    lhs.mul_assign(&denominator);
    let k_size = E::Fr::from_str(&index.domains.k.size.to_string()).expect("must construct a field element");
    let mut sigma_three = proof.sigma_three.clone();
    sigma_three.mul_assign(&k_size);
    lhs.mul_assign(&sigma_three);

    // rhs: h2(beta_two)*v_h(beta_two) + (beta_two*g2(beta_two)) + sigma_two
    let h2 = proof.evals.at_beta_two.get("h2").expect("must contains h2");
    let g2 = proof.evals.at_beta_two.get("g2").expect("must contains g2");

    let mut rhs = h2.clone();
    rhs.mul_assign(&v_h_at_beta_two);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.mul_assign(&g2);
    rhs.add_assign(&tmp);
    rhs.add_assign(&proof.sigma_two);

    Ok(lhs == rhs)
}

// h3(beta_three) *v_k(beta_three)
// ==
// a(beta_three) - (b(beta_three)*beta_three*g3(beta_three)) + sigma_three
fn sumcheck_three<E: Engine>(index: &Index<E>, proof: &Proof<E>)-> Result<bool, SynthesisError>{
    // lhs
    let v_k_at_beta_three = index.domains.k.evaluate_vanishing_polynomial_at(proof.oracles.beta_three);
    let h3 = proof.evals.at_beta_three.get("h3").expect("must has h3");
    let mut lhs = h3.clone();
    lhs.mul_assign(&v_k_at_beta_three);
    
    // rhs
    // first part : a(x) = Σ_{M∊{A,B,C}}{ ή_M*v_H(β_2)*v_h(β_1)*val_M(κ)* (ᴨ_{N∊{A,B,C}\{M}}((β_2-row_N(l))*(β_1-col_N(l)))}    
    let v_h_at_beta_one = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.beta_one);
    let v_h_at_beta_two = index.domains.h.evaluate_vanishing_polynomial_at(proof.oracles.beta_two);
    // query evaluation of matrix polynomials
    let a_row = proof.evals.at_beta_three.get("a_row").expect("must has a_row");
    let a_col = proof.evals.at_beta_three.get("a_col").expect("must has a_col");
    let a_val = proof.evals.at_beta_three.get("a_val").expect("must has a_val");
    let b_row = proof.evals.at_beta_three.get("b_row").expect("must has b_row");
    let b_col = proof.evals.at_beta_three.get("b_col").expect("must has b_col");
    let b_val = proof.evals.at_beta_three.get("b_val").expect("must has b_val");
    let c_row = proof.evals.at_beta_three.get("c_row").expect("must has c_row");
    let c_col = proof.evals.at_beta_three.get("c_col").expect("must has c_col");
    let c_val = proof.evals.at_beta_three.get("c_val").expect("must has c_val");
    // A part
    let mut a_evals = proof.oracles.eta_a.clone();
    a_evals.mul_assign(&v_h_at_beta_one);
    a_evals.mul_assign(&v_h_at_beta_two);
    a_evals.mul_assign(&a_val);

    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(b_row);
    a_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(b_col);
    a_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(c_row);
    a_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(c_col);
    a_evals.mul_assign(&tmp);
    // B part
    let mut b_evals = proof.oracles.eta_b.clone();
    b_evals.mul_assign(&v_h_at_beta_one);
    b_evals.mul_assign(&v_h_at_beta_two);
    b_evals.mul_assign(&b_val);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(a_row);
    b_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(a_col);
    b_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(c_row);
    b_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(c_col);
    b_evals.mul_assign(&tmp);
    // C part
    let mut c_evals = proof.oracles.eta_c.clone();
    c_evals.mul_assign(&v_h_at_beta_one);
    c_evals.mul_assign(&v_h_at_beta_two);
    c_evals.mul_assign(&c_val);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(a_row);
    c_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(a_col);
    c_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_two.clone();
    tmp.sub_assign(b_row);
    c_evals.mul_assign(&tmp);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(b_col);
    c_evals.mul_assign(&tmp);

    let mut rhs = a_evals.clone();
    rhs.add_assign(&b_evals);
    rhs.add_assign(&c_evals);

    // second part: b(beta_three)*(beta_three*g3(beta_three) + sigma_three)
    // for each matrices
    // b(x) = (beta_two - row(beta_three)) * (beta_one - col(beta_three))
    // A
    let mut a_evals = proof.oracles.beta_two.clone();
    a_evals.sub_assign(a_row);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(a_col);
    a_evals.mul_assign(&tmp);
    // B
    let mut b_evals = proof.oracles.beta_two.clone();
    b_evals.sub_assign(b_row);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(b_col);
    b_evals.mul_assign(&tmp);
    // C
    let mut c_evals = proof.oracles.beta_two.clone();
    c_evals.sub_assign(c_row);
    let mut tmp = proof.oracles.beta_one.clone();
    tmp.sub_assign(c_col);
    c_evals.mul_assign(&tmp);

    let mut tmp = a_evals.clone();
    tmp.mul_assign(&b_evals);
    tmp.mul_assign(&c_evals);

    let g3 = proof.evals.at_beta_three.get("g3").expect("must has g3");
    let mut tmp2 = proof.oracles.beta_three.clone();
    tmp2.mul_assign(g3);
    tmp2.add_assign(&proof.sigma_three);

    tmp.mul_assign(&tmp2);

    rhs.sub_assign(&tmp);

    Ok(lhs == rhs)
}


