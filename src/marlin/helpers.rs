use rand::{Rand, Rng};
use core::cmp::Ordering;
use std::marker::PhantomData;
use crate::multicore::Worker;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::Engine;
use crate::{Circuit, ConstraintSystem, SynthesisError};
pub use crate::plonk::domains::Domain;
pub use crate::plonk::polynomials::{Coefficients, Polynomial, PolynomialForm, Values};
pub use crate::cs::Index;

impl<F: PrimeField> Domain<F> {
    pub fn evaluate_vanishing_polynomial_at(&self, x: F) -> F {
        let mut x = x.pow(&[self.size]);
        x.sub_assign(&F::one());
        x
    }

    pub fn elements(&self, worker: &Worker) -> Vec<F> {
        let domain_size = self.size as usize;
        let mut elements = vec![F::zero(); domain_size];
        let generator = self.generator;
        worker.scope(domain_size, |scope, chunk_size| {
            for (chunk_id, elem_slice) in elements.chunks_mut(chunk_size).enumerate() {
                scope.spawn(move |_| {
                    let start = (chunk_id * chunk_size) as u64;
                    let mut chunk_generator = generator.pow(&[start]);
                    for elem in elem_slice.iter_mut() {
                        *elem = chunk_generator;
                        chunk_generator.mul_assign(&generator);
                    }
                });
            }
        });
        elements
    }

    pub fn get_vanishing_polynomial(&self) -> Result<Polynomial<F, Coefficients>, SynthesisError> {
        let v_size = self.size as usize;
        let mut v_coeff = vec![F::zero(); v_size + 1];
        let mut neg_one = F::one();
        neg_one.negate();
        v_coeff[0] = neg_one;
        v_coeff[v_size] = F::one();
        Polynomial::from_coeffs(v_coeff)
    }

    pub fn evaluate_bivariate_polynomial_with_same_inputs(
        &self,
        worker: &Worker,
        elements_of_domain_h: &[F],
    ) -> Vec<F> {
        let size_as_fe = F::from_str(&self.size.to_string()).unwrap();
        // in order to exploit multicore "size of domain" and "domain elements of h" are wrapped in a polynomial of value form
        let mut domain_size_as_polynomial =
            Polynomial::from_values(vec![size_as_fe; self.size as usize]).unwrap();
        let elements_of_domain_h = Polynomial::from_values(elements_of_domain_h.to_vec()).unwrap();
        domain_size_as_polynomial.mul_assign(worker, &elements_of_domain_h);
        let mut result = domain_size_as_polynomial.into_coeffs();
        result[1..].reverse();
        result
    }

    pub fn evaluate_bivariate_polynomial_with_diff_inputs(
        &self,
        worker: &Worker,
        elements_of_domain_h: &[F],
        x: F,
    ) -> Vec<F> {
        let vanishing_polynomial_evaluated_at_x = self.evaluate_vanishing_polynomial_at(x);
        // in order to exploit multicore "x" and "domain elements of h" are wrapped in a polynomial of value form
        let mut result = Polynomial::from_values(vec![x; self.size as usize]).unwrap();
        let elements_of_domain_h = Polynomial::from_values(elements_of_domain_h.to_vec()).unwrap();
        result.sub_assign(worker, &elements_of_domain_h);
        result.batch_inversion(worker).unwrap(); // TODO: unwrap here or expect?
        result.scale(worker, vanishing_polynomial_evaluated_at_x);

        result.into_coeffs()
    }
}

impl<F: PrimeField, P: PolynomialForm> Polynomial<F, P> {
    pub fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            // assert!(self.as_ref().last().map_or(false, |coeff| !coeff.is_zero()));
            self.as_ref().len() - 1
        }
    }

    pub fn is_zero(&self) -> bool {
        self.as_ref().is_empty() || self.as_ref().iter().all(|coeff| coeff.is_zero())
    }
}

impl<F: PrimeField> Polynomial<F, Coefficients> {
    // this function exist for sumcheck. it will be deprecated after integration of new sumcheck
    pub fn divide_by_vanishing_poly(
        &self,
        domain: Domain<F>,
    ) -> Result<(Polynomial<F, Coefficients>, Polynomial<F, Coefficients>), SynthesisError> {
        let v = domain.get_vanishing_polynomial()?;

        if self.is_zero() {
            println!("poly is zero");
            let zero_poly = Polynomial::<F, Coefficients>::new_for_size(0).unwrap();
            Ok((zero_poly.clone(), zero_poly.clone()))
        } else if v.is_zero() {
            Err(SynthesisError::PolynomialDegreeTooLarge)
        } else if self.degree() < v.degree() {
            println!("degree(nom) < degree(denom)");
            Ok((
                Polynomial::<F, Coefficients>::new_for_size(0).unwrap(),
                self.clone(),
            ))
        } else {
            let mut v_coeffs = v.clone().into_coeffs();
            // trim trailing zeroes
            while let Some(true) = v_coeffs.iter().last().map(|c| c == &F::zero()) {
                v_coeffs.pop();
            }
            // (degree + 1 = size) so q = self.len() -v.len() + 2
            let mut q: Vec<F> = vec![F::zero(); self.as_ref().len() - v_coeffs.len() + 2];
            let largest_coeff_inv = v_coeffs.iter().last().unwrap().inverse().unwrap();
            let mut r_coeffs = self.clone().into_coeffs();
            while !(r_coeffs.is_empty() || r_coeffs.iter().all(|coeff| coeff.is_zero()))
                && r_coeffs.len() >= v_coeffs.len()
            {
                let mut cur_q_coeff = r_coeffs[r_coeffs.len() - 1];
                cur_q_coeff.mul_assign(&largest_coeff_inv);
                let cur_q_deg = r_coeffs.len() - v_coeffs.len(); // TODO
                q[cur_q_deg] = cur_q_coeff;
                v_coeffs.iter().enumerate().for_each(|(i, e)| {
                    let mut tmp = cur_q_coeff.clone();
                    tmp.mul_assign(&e);
                    r_coeffs[cur_q_deg + i].sub_assign(&tmp);
                });
                while let Some(true) = r_coeffs.iter().last().map(|c| c == &F::zero()) {
                    r_coeffs.pop();
                }
            }
            let r = Polynomial::from_coeffs(r_coeffs).unwrap();
            let q_poly = Polynomial::from_coeffs(q).unwrap();

            Ok((q_poly, r))
        }
    }

    pub fn mul_by_vanishing_poly(&self, domain: Domain<F>) -> Polynomial<F, Coefficients> {
        let mut elems = vec![F::zero(); domain.size as usize];
        elems.extend_from_slice(&self.as_ref().clone());
        elems
            .iter_mut()
            .zip(self.as_ref().clone())
            .for_each(|(e, v)| e.sub_assign(&v));
        Self::from_coeffs(elems).unwrap()
    }
}

pub fn rand_poly<E: Engine, R: Rng>(
    degree: usize,
    _rng: &mut R,
) -> Polynomial<E::Fr, Coefficients> {
    let coeffs = (0..=degree)
        .map(|_| {
            E::Fr::from_str("33337829893243287892342388743").unwrap()
            // E::Fr::rand(rng)
        })
        .collect();
    Polynomial::from_coeffs(coeffs).unwrap()
}

impl PartialOrd for Index {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Index {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Index::Input(ref idx1), Index::Input(ref idx2))
            | (Index::Aux(ref idx1), Index::Aux(ref idx2)) => idx1.cmp(idx2),
            (Index::Input(_), Index::Aux(_)) => Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => Ordering::Greater,
        }
    }
}